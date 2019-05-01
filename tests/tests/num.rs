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
        if a.len() > 0 || b.len() > 0 {
            assert_eq!(
                &(heapless_bigint::BigUint::<U8192>::from_bytes_be(&a)
                    + heapless_bigint::BigUint::<U8192>::from_bytes_be(&b))
                .to_bytes_be()[..],
                &(num_bigint::BigUint::from_bytes_be(&a) + num_bigint::BigUint::from_bytes_be(&b))
                    .to_bytes_be()[..]
            )
        }
    }

    #[test]
    fn sub(a: Vec<u8>, b: Vec<u8>) {
        if a.len() > b.len() && b.len() > 0 {
            assert_eq!(
                &(heapless_bigint::BigUint::<U8192>::from_bytes_be(&a)
                    - heapless_bigint::BigUint::<U8192>::from_bytes_be(&b))
                .to_bytes_be()[..],
                &(num_bigint::BigUint::from_bytes_be(&a) - num_bigint::BigUint::from_bytes_be(&b))
                    .to_bytes_be()[..]
            )
        }
    }
}
