#![no_std]

#[cfg(test)]
#[macro_use]
extern crate std;

mod algorithms;

use {
    algorithms::*,
    core::{
        cmp::Ordering::{self, Greater, Less},
        ops::{Add, AddAssign, Mul, MulAssign, Rem, RemAssign, Shl, Shr, Sub, SubAssign},
    },
    heapless::{ArrayLength, Vec},
};

#[derive(Debug, Clone)]
pub struct BigUint<N>
where
    N: ArrayLength<u8>,
{
    data: Vec<u8, N>,
}

impl<N: ArrayLength<u8>> PartialEq for BigUint<N> {
    fn eq(&self, other: &BigUint<N>) -> bool {
        self.data.eq(&other.data)
    }
}

impl<N: ArrayLength<u8>> Eq for BigUint<N> {}

impl<N: ArrayLength<u8>> PartialOrd for BigUint<N> {
    fn partial_cmp(&self, other: &BigUint<N>) -> Option<Ordering> {
        if self.data.len() > other.data.len() {
            Some(Greater)
        } else if self.data.len() < other.data.len() {
            Some(Less)
        } else {
            let mut i = self.data.len() - 1;

            while i > 0 {
                if self.data[i] > other.data[i] {
                    return Some(Greater);
                } else if self.data[i] < other.data[i] {
                    return Some(Less);
                } else {
                    i -= 1;
                }
            }

            Some(self.data[0].cmp(&other.data[0]))
        }
    }
}

impl<N: ArrayLength<u8>> Ord for BigUint<N> {
    fn cmp(&self, other: &BigUint<N>) -> Ordering {
        self.partial_cmp(other).expect("partial_cmp is always Some")
    }
}

impl<N: ArrayLength<u8>> BigUint<N> {
    pub fn from_bytes_be(bytes: &[u8]) -> Self {
        let mut data = Vec::<u8, N>::new();

        // Change this to return an error
        assert!(bytes.len() <= data.capacity());

        for i in (0..bytes.len()).rev() {
            data.push(bytes[i]).unwrap();
        }

        for _ in bytes.len()..data.capacity() {
            data.push(0).unwrap();
        }

        Self { data }
    }

    pub fn from_bytes_le(bytes: &[u8]) -> Self {
        let mut data = Vec::<u8, N>::new();

        // Change this to return an error
        assert!(bytes.len() <= data.capacity());

        for i in 0..bytes.len() {
            data.push(bytes[i]).unwrap();
        }

        Self { data }
    }

    pub fn to_bytes_be(mut self) -> Vec<u8, N> {
        self.normalize();
        self.data.reverse();
        self.data
    }

    pub fn to_bytes_le(self) -> Vec<u8, N> {
        self.normalized().data
    }

    pub fn zero() -> Self {
        Self {
            data: {
                let mut data = Vec::<u8, N>::new();
                data.push(0).unwrap();
                data
            },
        }
    }

    pub fn is_zero(&self) -> bool {
        self.data.iter().max() == Some(&0)
    }

    fn normalize(&mut self) {
        while let Some(&0) = self.data.last() {
            if self.data.len() > 1 {
                self.data.pop();
            } else {
                break;
            }
        }
    }

    fn normalized(mut self) -> BigUint<N> {
        self.normalize();
        self
    }
}

impl<'a, N: ArrayLength<u8>> Shl<usize> for &'a BigUint<N> {
    type Output = BigUint<N>;

    fn shl(self, rhs: usize) -> BigUint<N> {
        biguint_shl(self, rhs)
    }
}

impl<N: ArrayLength<u8>> Shr<usize> for BigUint<N> {
    type Output = BigUint<N>;

    fn shr(self, rhs: usize) -> BigUint<N> {
        biguint_shr(self, rhs)
    }
}

impl<N: ArrayLength<u8>> Add for BigUint<N> {
    type Output = BigUint<N>;

    fn add(mut self, other: BigUint<N>) -> BigUint<N> {
        self += other;
        self
    }
}

impl<N: ArrayLength<u8>> AddAssign for BigUint<N> {
    fn add_assign(&mut self, other: BigUint<N>) {
        assert!(self.data.capacity() >= other.data.capacity());

        let mut acc: u16 = 0;

        for i in 0..other.data.len() {
            self.data[i] = adc(self.data[i], other.data[i], &mut acc);
        }

        if acc != 0 {
            panic!("BigUint overflow by {}", acc);
        }
    }
}

impl<N: ArrayLength<u8>> Sub for BigUint<N> {
    type Output = BigUint<N>;

    fn sub(mut self, other: BigUint<N>) -> BigUint<N> {
        self -= other;
        self
    }
}

impl<N: ArrayLength<u8>> SubAssign<BigUint<N>> for BigUint<N> {
    fn sub_assign(&mut self, other: BigUint<N>) {
        assert!(self.data.capacity() >= other.data.capacity());

        let mut acc: i16 = 0;

        for i in 0..other.data.len() {
            self.data[i] = sbb(self.data[i], other.data[i], &mut acc);
        }

        if acc != 0 {
            panic!("BigUint underflow by {}", acc);
        }
    }
}

impl<'a, N: ArrayLength<u8>> Sub<&'a BigUint<N>> for &'a mut BigUint<N> {
    type Output = BigUint<N>;

    fn sub(mut self, other: &'a BigUint<N>) -> BigUint<N> {
        self -= &other;
        BigUint {
            data: self.data.clone(),
        }
    }
}

impl<'a, 'b, N: ArrayLength<u8>> SubAssign<&'a BigUint<N>> for &'b mut BigUint<N> {
    fn sub_assign(&mut self, other: &BigUint<N>) {
        assert!(self.data.capacity() >= other.data.capacity());

        let mut acc: i16 = 0;

        for i in 0..self.data.len() {
            self.data[i] = sbb(self.data[i], other.data[i], &mut acc);
        }

        if acc != 0 {
            panic!("BigUint underflow by {}", acc);
        }
    }
}

impl<N: ArrayLength<u8>> Mul for BigUint<N> {
    type Output = BigUint<N>;

    fn mul(mut self, other: BigUint<N>) -> BigUint<N> {
        self *= &other;
        self
    }
}

impl<'a, 'b, N: ArrayLength<u8>> Mul<&'b BigUint<N>> for &'a BigUint<N> {
    type Output = BigUint<N>;

    fn mul(self, other: &BigUint<N>) -> BigUint<N> {
        // Assume self is larger
        assert!(self.data.capacity() >= other.data.capacity());

        let mut out = Vec::<u8, N>::new();
        for _ in 0..self.data.len() {
            out.push(0).unwrap();
        }

        for (i, xi) in other.data.iter().enumerate() {
            mac_digit(&mut out[i..], &self.data, *xi);
        }

        BigUint { data: out }
    }
}

impl<'a, N: ArrayLength<u8>> MulAssign<&'a BigUint<N>> for BigUint<N> {
    fn mul_assign(&mut self, other: &'a BigUint<N>) {
        *self = &*self * other;
    }
}

impl<'a, 'b, N: ArrayLength<u8>> Rem<&'b BigUint<N>> for &'a BigUint<N> {
    type Output = BigUint<N>;

    #[inline]
    fn rem(self, other: &BigUint<N>) -> BigUint<N> {
        let (_, r) = div_rem(self, other);
        r
    }
}

impl<'a, N: ArrayLength<u8>> RemAssign<&'a BigUint<N>> for BigUint<N> {
    #[inline]
    fn rem_assign(&mut self, other: &BigUint<N>) {
        *self = &*self % other;
    }
}

#[cfg(test)]
mod tests {
    use {crate::*, heapless::consts::*};

    #[test]
    fn from_bytes() {
        let bytes_be = [0xAB, 0xCD, 0xEF];
        let bytes_le = [0xEF, 0xCD, 0xAB];

        assert_eq!(
            BigUint::<U3>::from_bytes_be(&bytes_be),
            BigUint::<U3>::from_bytes_le(&bytes_le)
        )
    }

    #[test]
    fn to_and_from_fixed_len() {
        let a: [u8; 19] = [
            91, 222, 11, 193, 169, 165, 86, 105, 5, 1, 2, 56, 102, 142, 194, 80, 17, 240, 154,
        ];
        assert_eq!(a, &BigUint::<U19>::from_bytes_be(&a).to_bytes_be()[..])
    }

    #[test]
    fn add() {
        assert_eq!(
            BigUint::<U4>::from_bytes_be(&[3, 16, 53]),
            BigUint::<U4>::from_bytes_be(&[2, 249, 113]) + BigUint::<U4>::from_bytes_be(&[22, 196])
        )
    }

    #[test]
    #[should_panic]
    fn add_panic() {
        let _ = BigUint::<U3>::from_bytes_be(&[255, 255, 255]) + BigUint::<U3>::from_bytes_be(&[1]);
    }

    #[test]
    fn sub() {
        assert_eq!(
            BigUint::<U3>::from_bytes_be(&[2, 226, 173]),
            BigUint::<U3>::from_bytes_be(&[2, 249, 113]) - BigUint::<U3>::from_bytes_be(&[22, 196])
        )
    }

    #[test]
    #[should_panic]
    fn sub_panic() {
        let _ =
            BigUint::<U3>::from_bytes_be(&[1, 255, 255]) - BigUint::<U3>::from_bytes_be(&[2, 0, 0]);
    }

    #[test]
    fn mul() {
        assert_eq!(
            BigUint::<U4>::from_bytes_be(&[67, 185, 169, 245]),
            &BigUint::<U4>::from_bytes_be(&[2, 249, 113])
                * &BigUint::<U4>::from_bytes_be(&[22, 197])
        )
    }

    /*
    #[test]
    fn rem() {
        assert_eq!(
            BigUint::<U4>::from_bytes_be(&[10, 12]),
            &BigUint::<U4>::from_bytes_be(&[2, 249, 113])
                % &BigUint::<U4>::from_bytes_be(&[22, 197])
        )
    }
    */
}
