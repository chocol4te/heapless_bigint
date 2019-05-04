use {heapless::consts::*, heapless_bigint, num_bigint, proptest::prelude::*};

proptest! {
    #[test]
    fn to_and_from_bytes(bytes: Vec<u8>) {
        if bytes.len() > 0 {
            if bytes.last() != Some(&0) {
                assert_eq!(
                    bytes.as_slice(),
                    &heapless_bigint::BigUint::<U8192>::from_bytes_le(&bytes).to_bytes_le()[..]
                );
            }

            if bytes.first() != Some(&0) {
                assert_eq!(
                    bytes.as_slice(),
                    &heapless_bigint::BigUint::<U8192>::from_bytes_be(&bytes).to_bytes_be()[..]
                );
            }
        }
    }

    #[test]
    fn add(a: Vec<u8>, b: Vec<u8>) {
        assert_eq!(
            &(heapless_bigint::BigUint::<U8192>::from_bytes_be(&a)
                + heapless_bigint::BigUint::<U8192>::from_bytes_be(&b))
            .to_bytes_be()[..],
            &(num_bigint::BigUint::from_bytes_be(&a) + num_bigint::BigUint::from_bytes_be(&b))
                .to_bytes_be()[..]
        )
    }

    #[test]
    fn sub(a: Vec<u8>, b: Vec<u8>) {
        if a.len() > b.len() {
            assert_eq!(
                &(heapless_bigint::BigUint::<U8192>::from_bytes_be(&a)
                    - heapless_bigint::BigUint::<U8192>::from_bytes_be(&b))
                .to_bytes_be()[..],
                &(num_bigint::BigUint::from_bytes_be(&a) - num_bigint::BigUint::from_bytes_be(&b))
                    .to_bytes_be()[..]
            )
        }
    }

    #[test]
    fn mul(a: Vec<u8>, b: Vec<u8>) {
        assert_eq!(
            &(heapless_bigint::BigUint::<U8192>::from_bytes_be(&a)
                * heapless_bigint::BigUint::<U8192>::from_bytes_be(&b))
            .to_bytes_be()[..],
            &(num_bigint::BigUint::from_bytes_be(&a) * num_bigint::BigUint::from_bytes_be(&b))
                .to_bytes_be()[..]
        )
    }

    #[test]
    fn div(a: Vec<u8>, b: Vec<u8>) {
        if b.len() != 0 && b.first() != Some(&0) {
        assert_eq!(
            &(heapless_bigint::BigUint::<U8192>::from_bytes_be(&a)
                / heapless_bigint::BigUint::<U8192>::from_bytes_be(&b))
            .to_bytes_be()[..],
            &(num_bigint::BigUint::from_bytes_be(&a) / num_bigint::BigUint::from_bytes_be(&b))
                .to_bytes_be()[..]
        )
        }
    }

    #[test]
    fn shift(a: Vec<u8>, bits: usize) {
        if bits < 8 * 16384 {
        assert_eq!(
            &(heapless_bigint::BigUint::<U16384>::from_bytes_be(&a) >> bits).to_bytes_be()[..],
            &(num_bigint::BigUint::from_bytes_be(&a) >> bits).to_bytes_be()[..],
        );

        assert_eq!(
            &(&heapless_bigint::BigUint::<U16384>::from_bytes_be(&a) << bits).to_bytes_be()[..],
            &(num_bigint::BigUint::from_bytes_be(&a) << bits).to_bytes_be()[..],
        );
        }
    }

    #[test]
    fn rem(a: Vec<u8>, b: u8) {
        if b != 0 {
        assert_eq!(
            &(heapless_bigint::BigUint::<U8192>::from_bytes_be(&a)
                / heapless_bigint::BigUint::<U8192>::from_bytes_be(&[b]))
            .to_bytes_be()[..],
            &(num_bigint::BigUint::from_bytes_be(&a) / num_bigint::BigUint::from_bytes_be(&[b]))
                .to_bytes_be()[..]
        )
        }
    }
}
