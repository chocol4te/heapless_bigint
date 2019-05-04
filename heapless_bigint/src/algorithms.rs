use {
    crate::BigUint,
    core::{
        cmp::{
            self,
            Ordering::{self, Equal, Greater, Less},
        },
        iter::repeat,
    },
    heapless::{ArrayLength, Vec},
};

pub fn biguint_shl<N: ArrayLength<u8>>(n: &BigUint<N>, bits: usize) -> BigUint<N> {
    let n_unit = bits / 8;
    let mut data = match n_unit {
        0 => n.data.clone(),
        _ => {
            let mut data = Vec::<u8, N>::new();
            data.extend(repeat(0).take(n_unit));

            let mut ext = n.data.clone();
            while let Some(&0) = ext.last() {
                ext.pop();
            }

            data.extend(ext.iter());

            data
        }
    };

    let n_bits = bits % 8;
    if n_bits > 0 {
        let mut carry = 0;
        for elem in data[n_unit..].iter_mut() {
            let new_carry = *elem >> (8 - n_bits);
            *elem = (*elem << n_bits) | carry;
            carry = new_carry;
        }
        if carry != 0 {
            data.push(carry).unwrap();
        }
    }

    BigUint { data }
}

pub fn biguint_shr<N: ArrayLength<u8>>(n: &mut BigUint<N>, bits: usize) -> BigUint<N> {
    let n_unit = bits / 8;

    if n_unit >= n.data.len() {
        return BigUint::zero();
    }
    let mut data = n.data.clone();
    data.truncate(n.data.len() - n_unit);

    let n_bits = bits % 8;
    if n_bits > 0 {
        let mut borrow = 0;
        for elem in data.iter_mut().rev() {
            let new_borrow = *elem << (8 - n_bits);
            *elem = (*elem >> n_bits) | borrow;
            borrow = new_borrow;
        }
    }

    BigUint { data }
}

pub fn adc(a: u8, b: u8, acc: &mut u16) -> u8 {
    *acc += a as u16;
    *acc += b as u16;
    let lo = *acc as u8;
    *acc >>= 8;
    lo
}

pub fn sbb(a: u8, b: u8, acc: &mut i16) -> u8 {
    *acc += a as i16;
    *acc -= b as i16;
    let lo = *acc as u8;
    *acc >>= 8;
    lo
}

fn div_wide(hi: u8, lo: u8, divisor: u8) -> (u8, u8) {
    debug_assert!(hi < divisor);

    let lhs = lo as u16 | ((hi as u16) << 8);
    let rhs = divisor as u16;
    ((lhs / rhs) as u8, (lhs % rhs) as u8)
}

fn div_rem_digit<N: ArrayLength<u8>>(mut a: BigUint<N>, b: u8) -> (BigUint<N>, u8) {
    let mut rem = 0;

    for d in a.data.iter_mut().rev() {
        let (q, r) = div_wide(rem, *d, b);
        *d = q;
        rem = r;
    }

    (a, rem)
}

fn cmp_slice(a: &[u8], b: &[u8]) -> Ordering {
    //debug_assert!(a.last() != Some(&0));
    //debug_assert!(b.last() != Some(&0));

    let (a_len, b_len) = (a.len(), b.len());
    if a_len < b_len {
        return Less;
    }
    if a_len > b_len {
        return Greater;
    }

    for (&ai, &bi) in a.iter().rev().zip(b.iter().rev()) {
        if ai < bi {
            return Less;
        }
        if ai > bi {
            return Greater;
        }
    }
    return Equal;
}

pub fn div_rem<N: ArrayLength<u8>>(u: &BigUint<N>, d: &BigUint<N>) -> (BigUint<N>, BigUint<N>) {
    if d.is_zero() {
        panic!()
    }
    if u.is_zero() {
        return (BigUint::zero(), BigUint::zero());
    }
    if d.data == [1] {
        return (
            BigUint {
                data: u.data.clone(),
            },
            BigUint::zero(),
        );
    }
    if d.data.len() == 1 {
        let (div, rem) = div_rem_digit(
            BigUint {
                data: u.data.clone(),
            },
            d.data[0],
        );
        return (div, BigUint::from_bytes_be(&[rem]));
    }

    // Required or the q_len calculation below can underflow:
    match u.cmp(d) {
        Less => {
            return (
                BigUint::zero(),
                BigUint {
                    data: u.data.clone(),
                },
            )
        }
        Equal => return (BigUint::from_bytes_be(&[1]), BigUint::zero()),
        Greater => {} // Do nothing
    }

    // This algorithm is from Knuth, TAOCP vol 2 section 4.3, algorithm D:
    //
    // First, normalize the arguments so the highest bit in the highest digit of the divisor is
    // set: the main loop uses the highest digit of the divisor for generating guesses, so we
    // want it to be the largest number we can efficiently divide by.
    //
    let shift = d.data.last().unwrap().leading_zeros() as usize;
    let mut a = u << shift;
    let b = d << shift;

    // The algorithm works by incrementally calculating "guesses", q0, for part of the
    // remainder. Once we have any number q0 such that q0 * b <= a, we can set
    //
    //     q += q0
    //     a -= q0 * b
    //
    // and then iterate until a < b. Then, (q, a) will be our desired quotient and remainder.
    //
    // q0, our guess, is calculated by dividing the last few digits of a by the last digit of b
    // - this should give us a guess that is "close" to the actual quotient, but is possibly
    // greater than the actual quotient. If q0 * b > a, we simply use iterated subtraction
    // until we have a guess such that q0 * b <= a.
    //

    let bn = *b.data.last().unwrap();
    let q_len = a.data.len() - b.data.len() + 1;
    let mut q = BigUint {
        data: {
            let mut data = Vec::<u8, N>::new();
            for _ in 0..q_len {
                data.push(0).unwrap();
            }
            data
        },
    };

    // We reuse the same temporary to avoid hitting the allocator in our inner loop - this is
    // sized to hold a0 (in the common case; if a particular digit of the quotient is zero a0
    // can be bigger).
    //
    let mut tmp = BigUint {
        data: Vec::<u8, N>::new(),
    };

    let b_data = b.data.clone();
    for j in (0..q_len).rev() {
        let b = BigUint {
            data: b_data.clone(),
        };

        /*
         * When calculating our next guess q0, we don't need to consider the digits below j
         * + b.data.len() - 1: we're guessing digit j of the quotient (i.e. q0 << j) from
         * digit bn of the divisor (i.e. bn << (b.data.len() - 1) - so the product of those
         * two numbers will be zero in all digits up to (j + b.data.len() - 1).
         */
        let offset = j + b.data.len() - 1;
        if offset >= a.data.len() {
            continue;
        }

        /* just avoiding a heap allocation: */
        let mut a0 = tmp;
        a0.data.truncate(0);
        a0.data.extend(a.data[offset..].iter().cloned());

        /*
         * q0 << j * big_digit::BITS is our actual quotient estimate - we do the shifts
         * implicitly at the end, when adding and subtracting to a and q. Not only do we
         * save the cost of the shifts, the rest of the arithmetic gets to work with
         * smaller numbers.
         */
        let (mut q0, _) = div_rem_digit(a0, bn);
        let mut prod = &BigUint {
            data: b_data.clone(),
        } * &q0;

        while cmp_slice(&prod.data[..], &a.data[j..]) == Greater {
            let one = BigUint::<N>::from_bytes_be(&[1]);
            q0 = q0 - one;
            prod = prod
                - BigUint {
                    data: b_data.clone(),
                };
        }

        add2(&mut q.data[j..], &q0.data[..]);
        sub2(&mut a.data[j..], &prod.data[..]);
        a.normalize();

        tmp = q0;
    }

    debug_assert!(a < b);

    (q.normalized(), a >> shift)
}

pub fn __add2(a: &mut [u8], b: &[u8]) -> u8 {
    debug_assert!(a.len() >= b.len());

    let mut carry = 0;
    let (a_lo, a_hi) = a.split_at_mut(b.len());

    for (a, b) in a_lo.iter_mut().zip(b) {
        *a = adc(*a, *b, &mut carry);
    }

    if carry != 0 {
        for a in a_hi {
            *a = adc(*a, 0, &mut carry);
            if carry == 0 {
                break;
            }
        }
    }

    carry as u8
}

pub fn add2(a: &mut [u8], b: &[u8]) {
    let carry = __add2(a, b);

    debug_assert!(carry == 0);
}

pub fn sub2(a: &mut [u8], b: &[u8]) {
    let mut borrow = 0;

    let len = cmp::min(a.len(), b.len());
    let (a_lo, a_hi) = a.split_at_mut(len);
    let (b_lo, b_hi) = b.split_at(len);

    for (a, b) in a_lo.iter_mut().zip(b_lo) {
        *a = sbb(*a, *b, &mut borrow);
    }

    if borrow != 0 {
        for a in a_hi {
            *a = sbb(*a, 0, &mut borrow);
            if borrow == 0 {
                break;
            }
        }
    }

    // note: we're _required_ to fail on underflow
    assert!(
        borrow == 0 && b_hi.iter().all(|x| *x == 0),
        "Cannot subtract b from a because b is larger than a."
    );
}

pub fn mul3<N: ArrayLength<u8>>(x: &[u8], y: &[u8]) -> BigUint<N> {
    let mut prod = BigUint {
        data: {
            let mut data = Vec::<u8, N>::new();
            for _ in 0..(x.len() + y.len() + 1) {
                data.push(0).unwrap();
            }
            data
        },
    };

    mac3(&mut prod.data[..], x, y);
    prod.normalized()
}

fn mac3(acc: &mut [u8], b: &[u8], c: &[u8]) {
    let (x, y) = if b.len() < c.len() { (b, c) } else { (c, b) };
    for (i, xi) in x.iter().enumerate() {
        mac_digit(&mut acc[i..], y, *xi);
    }
}

pub fn mac_digit(acc: &mut [u8], b: &[u8], c: u8) {
    if c == 0 {
        return;
    }

    let mut carry = 0;
    let (a_lo, a_hi) = acc.split_at_mut(b.len());

    for (a, &b) in a_lo.iter_mut().zip(b) {
        *a = mac_with_carry(*a, b, c, &mut carry);
    }

    let mut a = a_hi.iter_mut();
    while carry != 0 {
        let a = a.next().expect("carry overflow during multiplication!");
        *a = adc(*a, 0, &mut carry);
    }
}

fn mac_with_carry(a: u8, b: u8, c: u8, acc: &mut u16) -> u8 {
    *acc += a as u16;
    *acc += (b as u16) * (c as u16);
    let lo = *acc as u8;
    *acc >>= 8;
    lo
}
