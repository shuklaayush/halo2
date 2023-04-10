use core::convert::TryInto;
use core::fmt;
use core::ops::{Add, Mul, Neg, Sub};

use ff::PrimeField;
use rand::RngCore;
use serde::{Deserialize, Serialize};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use pasta_curves::arithmetic::{FieldExt, Group, SqrtRatio};

use crate::arithmetic::{adc, mac, macx, sbb};

/// This represents an element of $\mathbb{F}_p$ where
///
/// `p = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed`
///
/// is the base field of the Ed25519 curve.
// The internal representation of this type is four 64-bit unsigned
// integers in little-endian order. `Fp` values are always in
// Montgomery form; i.e., Fp(a) = aR mod p, with R = 2^256.
#[derive(Clone, Copy, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Fp(pub(crate) [u64; 4]);

/// Constant representing the modulus
/// p = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed
const MODULUS: Fp = Fp([
    0xffffffffffffffed,
    0xffffffffffffffff,
    0xffffffffffffffff,
    0x7fffffffffffffff,
]);

/// The modulus as u32 limbs.
#[cfg(not(target_pointer_width = "64"))]
const MODULUS_LIMBS_32: [u32; 8] = [
    0xffff_ffed,
    0xffff_fffe,
    0xffff_ffff,
    0xffff_ffff,
    0xffff_ffff,
    0xffff_ffff,
    0xffff_ffff,
    0x7fff_ffff,
];

/// Constant representing the modolus as static str
const MODULUS_STR: &str = "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed";

/// INV = -(p^{-1} mod 2^64) mod 2^64
const INV: u64 = 0x86bca1af286bca1b;

/// R = 2^256 mod p
/// 0x26
const R: Fp = Fp([0x26, 0, 0, 0]);

/// R^2 = 2^512 mod p
/// 0x5a4
const R2: Fp = Fp([0x5a4, 0, 0, 0]);

/// R^3 = 2^768 mod p
/// 0xd658
const R3: Fp = Fp([0xd658, 0, 0, 0]);

/// 1 / 2 mod p
const TWO_INV: Fp = Fp::from_raw([
    0xfffffffffffffff7,
    0xffffffffffffffff,
    0xffffffffffffffff,
    0x3fffffffffffffff,
]);

/// sqrt(-1) mod p = 2^((p - 1) / 4) mod p
const MINUS_ONE_SQRT: Fp = Fp::from_raw([
    0xc4ee1b274a0ea0b0,
    0x2f431806ad2fe478,
    0x2b4d00993dfbd7a7,
    0x2b8324804fc1df0b,
]);

const ZETA: Fp = Fp::zero();
const DELTA: Fp = Fp::zero();
const ROOT_OF_UNITY_INV: Fp = Fp::zero();

use crate::{
    field_arithmetic, field_common, field_specific, impl_add_binop_specify_output,
    impl_binops_additive, impl_binops_additive_specify_output, impl_binops_multiplicative,
    impl_binops_multiplicative_mixed, impl_sub_binop_specify_output,
};
impl_binops_additive!(Fp, Fp);
impl_binops_multiplicative!(Fp, Fp);
field_common!(
    Fp,
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
field_arithmetic!(Fp, MODULUS, INV, dense);

impl Fp {
    pub const fn size() -> usize {
        32
    }
}

impl ff::Field for Fp {
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
        //      = a^((p + 3) / 8) * (2^((p - 1) / 4))
        let x1 = self.pow(&[
            0xfffffffffffffffe,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0x0fffffffffffffff,
        ]);

        let choice1 = x1.square().ct_eq(&self);
        let choice2 = x1.square().ct_eq(&-self);

        let sqrt = Self::conditional_select(&x1, &(x1 * MINUS_ONE_SQRT), choice2);

        CtOption::new(sqrt, choice1 | choice2)
    }

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    fn invert(&self) -> CtOption<Self> {
        let tmp = self.pow_vartime([
            0xffffffffffffffeb,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0x7fffffffffffffff,
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

impl ff::PrimeField for Fp {
    type Repr = [u8; 32];

    const NUM_BITS: u32 = 256;
    const CAPACITY: u32 = 255;
    const S: u32 = 1;

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let mut tmp = Fp([0, 0, 0, 0]);

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
        let tmp = Fp::montgomery_reduce_short(self.0[0], self.0[1], self.0[2], self.0[3]);

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

impl SqrtRatio for Fp {
    const T_MINUS1_OVER2: [u64; 4] = [0, 0, 0, 0];

    fn get_lower_32(&self) -> u32 {
        let tmp = Fp::montgomery_reduce_short(self.0[0], self.0[1], self.0[2], self.0[3]);
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
        let v = (Fp::TWO_INV).square().sqrt().unwrap();
        assert!(v == Fp::TWO_INV || (-v) == Fp::TWO_INV);

        for _ in 0..10000 {
            let a = Fp::random(OsRng);
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
        let v = Fp::one().double().invert().unwrap();
        assert!(v == Fp::TWO_INV);

        for _ in 0..10000 {
            let a = Fp::random(OsRng);
            let b = a.invert().unwrap().invert().unwrap();

            assert!(a == b);
        }
    }

    #[test]
    fn test_field() {
        crate::tests::field::random_field_tests::<Fp>("ed25519 base".to_string());
    }

    #[test]
    fn test_serialization() {
        crate::tests::field::random_serialization_test::<Fp>("ed25519 base".to_string());
    }
}
