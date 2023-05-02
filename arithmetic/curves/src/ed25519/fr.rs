use core::convert::TryInto;
use core::fmt;
use core::ops::{Add, Mul, Neg, Sub};

use ff::PrimeField;
use rand::RngCore;
use serde::{Deserialize, Serialize};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::arithmetic::{adc, mac, macx, sbb};

use pasta_curves::arithmetic::{FieldExt, Group, SqrtRatio};

/// This represents an element of $\mathbb{F}_q$ where
///
/// `r = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed`
///
/// is the scalar field of the ed25519 curve.
// The internal representation of this type is four 64-bit unsigned
// integers in little-endian order. `Fr` values are always in
// Montgomery form; i.e., Fr(a) = aR mod r, with R = 2^256.
#[derive(Clone, Copy, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Fr(pub(crate) [u64; 4]);

/// Constant representing the modulus
/// r = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed
const MODULUS: Fr = Fr([
    0x5812631a5cf5d3ed,
    0x14def9dea2f79cd6,
    0x0000000000000000,
    0x1000000000000000,
]);

/// The modulus as u32 limbs.
#[cfg(not(target_pointer_width = "64"))]
const MODULUS_LIMBS_32: [u32; 8] = [
    0x5cf5_d3ed,
    0x5812_631a,
    0xa2f7_9cd6,
    0x14de_f9de,
    0x0000_0000,
    0x0000_0000,
    0x0000_0000,
    0x1000_0000,
];

///Constant representing the modulus as static str
const MODULUS_STR: &str = "0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed";

/// INV = -(q^{-1} mod 2^64) mod 2^64
const INV: u64 = 0xd2b51da312547e1b;

/// R = 2^256 mod r
/// 0xffffffffffffffffffffffffffffffec6ef5bf4737dcf70d6ec31748d98951d
const R: Fr = Fr([
    0xd6ec31748d98951d,
    0xc6ef5bf4737dcf70,
    0xfffffffffffffffe,
    0x0fffffffffffffff,
]);

/// R^2 = 2^512 mod r
/// 0x399411b7c309a3dceec73d217f5be65d00e1ba768859347a40611e3449c0f01
const R2: Fr = Fr([
    0xa40611e3449c0f01,
    0xd00e1ba768859347,
    0xceec73d217f5be65,
    0x0399411b7c309a3d,
]);

/// R^3 = 2^768 mod r
/// 0xe530b773599cec78065dc6c04ec5b65278324e6aef7f3ec2a9e49687b83a2db
const R3: Fr = Fr([
    0x2a9e49687b83a2db,
    0x278324e6aef7f3ec,
    0x8065dc6c04ec5b65,
    0x0e530b773599cec7,
]);

/// 1 / 2 mod r
const TWO_INV: Fr = Fr::from_raw([
    0x2c09318d2e7ae9f7,
    0x0a6f7cef517bce6b,
    0x0000000000000000,
    0x0800000000000000,
]);

/// sqrt(-1) mod p = 2^((p - 1) / 4) mod p
const SQRT_MINUS_ONE: Fr = Fr::from_raw([
    0xbe8775dfebbe07d4,
    0x0ef0565342ce83fe,
    0x7d3d6d60abc1c27a,
    0x094a7310e07981e7,
]);

const ZETA: Fr = Fr::zero();
const DELTA: Fr = Fr::zero();
const ROOT_OF_UNITY_INV: Fr = Fr::zero();

use crate::{
    field_arithmetic, field_common, field_specific, impl_add_binop_specify_output,
    impl_binops_additive, impl_binops_additive_specify_output, impl_binops_multiplicative,
    impl_binops_multiplicative_mixed, impl_sub_binop_specify_output,
};
impl_binops_additive!(Fr, Fr);
impl_binops_multiplicative!(Fr, Fr);
field_common!(
    Fr,
    MODULUS,
    INV,
    MODULUS_STR,
    TWO_INV,
    ROOT_OF_UNITY_INV,
    DELTA,
    ZETA,
    R,
    R2,
    R3
);
field_arithmetic!(Fr, MODULUS, INV, dense);

impl Fr {
    pub const fn size() -> usize {
        32
    }
}

impl ff::Field for Fr {
    fn random(mut rng: impl RngCore) -> Self {
        Self::from_u512([
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
        ])
    }

    fn zero() -> Self {
        Self::zero()
    }

    fn one() -> Self {
        Self::one()
    }

    fn double(&self) -> Self {
        self.double()
    }

    #[inline(always)]
    fn square(&self) -> Self {
        self.square()
    }

    /// Computes the square root of this element, if it exists.
    fn sqrt(&self) -> CtOption<Self> {
        // Sqrt = a^((p + 3) / 8)
        //        OR
        //      = a^((p + 3) / 8) * sqrt(-1)
        //      = a^((p + 3) / 8) * (2^((p - 1) / 4))
        //        OR
        //        Doesn't exist
        let x1 = self.pow(&[
            0xcb024c634b9eba7e,
            0x029bdf3bd45ef39a,
            0x0000000000000000,
            0x0200000000000000,
        ]);

        let choice1 = x1.square().ct_eq(&self);
        let choice2 = x1.square().ct_eq(&-self);

        let sqrt = Self::conditional_select(&x1, &(x1 * SQRT_MINUS_ONE), choice2);

        CtOption::new(sqrt, choice1 | choice2)
    }

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    fn invert(&self) -> CtOption<Self> {
        let tmp = self.pow_vartime([
            0x5812631a5cf5d3eb,
            0x14def9dea2f79cd6,
            0x0000000000000000,
            0x1000000000000000,
        ]);

        CtOption::new(tmp, !self.ct_eq(&Self::zero()))
    }

    fn pow_vartime<S: AsRef<[u64]>>(&self, exp: S) -> Self {
        let mut res = Self::one();
        let mut found_one = false;
        for e in exp.as_ref().iter().rev() {
            for i in (0..64).rev() {
                if found_one {
                    res = res.square();
                }

                if ((*e >> i) & 1) == 1 {
                    found_one = true;
                    res *= self;
                }
            }
        }
        res
    }
}

impl ff::PrimeField for Fr {
    type Repr = [u8; 32];

    const NUM_BITS: u32 = 256;
    const CAPACITY: u32 = 255;
    const S: u32 = 6;

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let mut tmp = Fr([0, 0, 0, 0]);

        tmp.0[0] = u64::from_le_bytes(repr[0..8].try_into().unwrap());
        tmp.0[1] = u64::from_le_bytes(repr[8..16].try_into().unwrap());
        tmp.0[2] = u64::from_le_bytes(repr[16..24].try_into().unwrap());
        tmp.0[3] = u64::from_le_bytes(repr[24..32].try_into().unwrap());

        // Try to subtract the modulus
        let (_, borrow) = tmp.0[0].overflowing_sub(MODULUS.0[0]);
        let (_, borrow) = sbb(tmp.0[1], MODULUS.0[1], borrow);
        let (_, borrow) = sbb(tmp.0[2], MODULUS.0[2], borrow);
        let (_, borrow) = sbb(tmp.0[3], MODULUS.0[3], borrow);

        // If the element is smaller than MODULUS then the
        // subtraction will underflow, producing a borrow value
        // of 0xffff...ffff. Otherwise, it'll be zero.
        let is_some = (borrow as u8) & 1;

        // Convert to Montgomery form by computing
        // (a.R^0 * R^2) / R = a.R
        tmp *= &R2;

        CtOption::new(tmp, Choice::from(is_some))
    }

    fn to_repr(&self) -> Self::Repr {
        // Turn into canonical form by computing
        // (a.R) / R = a
        let tmp = Fr::montgomery_reduce_short(self.0[0], self.0[1], self.0[2], self.0[3]);

        let mut res = [0; 32];
        res[0..8].copy_from_slice(&tmp.0[0].to_le_bytes());
        res[8..16].copy_from_slice(&tmp.0[1].to_le_bytes());
        res[16..24].copy_from_slice(&tmp.0[2].to_le_bytes());
        res[24..32].copy_from_slice(&tmp.0[3].to_le_bytes());

        res
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.to_repr()[0] & 1)
    }

    fn multiplicative_generator() -> Self {
        unimplemented!();
    }

    fn root_of_unity() -> Self {
        unimplemented!();
    }
}

impl SqrtRatio for Fr {
    const T_MINUS1_OVER2: [u64; 4] = [0, 0, 0, 0];

    fn get_lower_32(&self) -> u32 {
        let tmp = Fr::montgomery_reduce_short(self.0[0], self.0[1], self.0[2], self.0[3]);
        tmp.0[0] as u32
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ff::Field;
    use rand_core::OsRng;

    #[test]
    fn test_sqrt() {
        // NB: TWO_INV is standing in as a "random" field element
        let v = (Fr::TWO_INV).square().sqrt().unwrap();
        assert!(v == Fr::TWO_INV || (-v) == Fr::TWO_INV);

        for _ in 0..10000 {
            let a = Fr::random(OsRng);
            let mut b = a;
            b = b.square();

            let b = b.sqrt().unwrap();
            let mut negb = b;
            negb = negb.neg();

            assert!(a == b || a == negb);
        }
    }

    #[test]
    fn test_invert() {
        let v = Fr::one().double().invert().unwrap();
        assert!(v == Fr::TWO_INV);

        for _ in 0..10000 {
            let a = Fr::random(OsRng);
            let b = a.invert().unwrap().invert().unwrap();

            assert!(a == b);
        }
    }

    #[test]
    fn test_field() {
        crate::tests::field::random_field_tests::<Fr>("ed25519 scalar".to_string());
    }

    #[test]
    fn test_serialization() {
        crate::tests::field::random_serialization_test::<Fr>("ed25519 scalar".to_string());
    }
}
