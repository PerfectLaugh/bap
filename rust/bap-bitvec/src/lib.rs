#![forbid(unsafe_code)]

use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};
use serde::{Deserialize, Serialize};
use std::fmt;

/// An arbitrary-width, unsigned bitvector with masked arithmetic.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct BitVec {
    width: u32,
    value: BigUint,
}

impl BitVec {
    pub fn new(width: u32, value: BigUint) -> Self {
        let mask = mask(width);
        Self {
            width,
            value: value & &mask,
        }
    }
    pub fn zero(width: u32) -> Self {
        Self::new(width, BigUint::zero())
    }
    pub fn one(width: u32) -> Self {
        Self::new(width, BigUint::one())
    }
    pub fn ones(width: u32) -> Self {
        Self::new(width, mask(width))
    }
    pub fn from_u64(width: u32, value: u64) -> Self {
        Self::new(width, BigUint::from(value))
    }
    pub fn from_biguint(width: u32, value: BigUint) -> Self {
        Self::new(width, value)
    }
    pub fn width(&self) -> u32 {
        self.width
    }
    pub fn value(&self) -> &BigUint {
        &self.value
    }
    pub fn into_value(self) -> BigUint {
        self.value
    }
    pub fn to_u64(&self) -> Option<u64> {
        self.value.to_u64()
    }
    pub fn is_zero(&self) -> bool {
        self.value.is_zero()
    }
    pub fn is_one(&self) -> bool {
        self.value.is_one()
    }
    pub fn msb(&self) -> bool {
        self.width != 0 && self.value.bit(self.width as u64 - 1)
    }
    pub fn lsb(&self) -> bool {
        self.value.bit(0)
    }
    pub fn bit(&self, index: u32) -> bool {
        index < self.width && self.value.bit(index as u64)
    }
    pub fn succ(&self) -> Self {
        self.add(&Self::one(self.width))
    }
    pub fn pred(&self) -> Self {
        self.sub(&Self::one(self.width))
    }
    pub fn neg(&self) -> Self {
        if self.is_zero() {
            self.clone()
        } else {
            Self::new(self.width, mask(self.width) - &self.value + 1u8)
        }
    }
    pub fn not(&self) -> Self {
        Self::new(self.width, mask(self.width) ^ &self.value)
    }
    pub fn abs(&self) -> Self {
        if self.msb() { self.neg() } else { self.clone() }
    }
    pub fn add(&self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        Self::new(self.width, &self.value + &other.value)
    }
    pub fn sub(&self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        Self::new(
            self.width,
            mask(self.width) + &self.value - &other.value + 1u8,
        )
    }
    pub fn mul(&self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        Self::new(self.width, &self.value * &other.value)
    }
    pub fn and(&self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        Self::new(self.width, &self.value & &other.value)
    }
    pub fn or(&self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        Self::new(self.width, &self.value | &other.value)
    }
    pub fn xor(&self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        Self::new(self.width, &self.value ^ &other.value)
    }
    pub fn shl(&self, amount: &Self) -> Self {
        if amount
            .to_u64()
            .map(|amount| amount as usize)
            .is_none_or(|amount| amount >= self.width as usize)
        {
            Self::zero(self.width)
        } else {
            Self::new(
                self.width,
                &self.value
                    << amount
                        .to_u64()
                        .map(|amount| amount as usize)
                        .expect("shift"),
            )
        }
    }
    pub fn lshr(&self, amount: &Self) -> Self {
        if amount
            .to_u64()
            .map(|amount| amount as usize)
            .is_none_or(|amount| amount >= self.width as usize)
        {
            Self::zero(self.width)
        } else {
            Self::new(
                self.width,
                &self.value
                    >> amount
                        .to_u64()
                        .map(|amount| amount as usize)
                        .expect("shift"),
            )
        }
    }
    pub fn ashr(&self, amount: &Self) -> Self {
        if amount
            .to_u64()
            .map(|amount| amount as usize)
            .is_none_or(|amount| amount >= self.width as usize)
        {
            if self.msb() {
                Self::ones(self.width)
            } else {
                Self::zero(self.width)
            }
        } else {
            let amount = amount
                .to_u64()
                .map(|amount| amount as usize)
                .expect("shift");
            let shifted = &self.value >> amount;
            if !self.msb() {
                Self::new(self.width, shifted)
            } else {
                let fill = mask(self.width) ^ mask(self.width - amount as u32);
                Self::new(self.width, shifted | fill)
            }
        }
    }
    pub fn div(&self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        if other.is_zero() {
            Self::ones(self.width)
        } else {
            Self::new(self.width, &self.value / &other.value)
        }
    }
    pub fn sdiv(&self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        if other.is_zero() {
            return Self::ones(self.width);
        }
        let left = self.signed();
        let right = other.signed();
        let result = if left.sign() == right.sign() {
            left / right
        } else {
            -((left.abs()) / (right.abs()))
        };
        self.from_signed(result)
    }
    pub fn rem(&self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        if other.is_zero() {
            self.clone()
        } else {
            Self::new(self.width, &self.value % &other.value)
        }
    }
    pub fn srem(&self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        if other.is_zero() {
            return self.clone();
        }
        self.from_signed(self.signed() % other.signed())
    }
    pub fn smod(&self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        let rem = self.rem(other);
        if rem.is_zero() {
            return rem;
        }
        match (self.msb(), other.msb()) {
            (false, false) => rem,
            (true, false) => rem.neg().add(other),
            (false, true) => rem.add(other),
            (true, true) => rem.neg(),
        }
    }
    pub fn gcd(&self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        Self::new(self.width, self.value.gcd(&other.value))
    }
    pub fn lcm(&self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        if self.is_zero() || other.is_zero() {
            Self::zero(self.width)
        } else {
            Self::new(
                self.width,
                &self.value / self.value.gcd(&other.value) * &other.value,
            )
        }
    }
    pub fn gcdext(&self, other: &Self) -> (Self, Self, Self) {
        assert_eq!(self.width, other.width);
        let extended =
            BigInt::from(self.value.clone()).extended_gcd(&BigInt::from(other.value.clone()));
        (
            Self::new(self.width, extended.gcd.to_biguint().unwrap_or_default()),
            self.from_signed(extended.x),
            self.from_signed(extended.y),
        )
    }
    pub fn extract(&self, high: u32, low: u32) -> Option<Self> {
        if high < low || high >= self.width {
            return None;
        }
        let width = high - low + 1;
        Some(Self::new(width, &self.value >> low as usize))
    }
    pub fn concat(&self, lower: &Self) -> Self {
        Self::new(
            self.width + lower.width,
            (&self.value << lower.width as usize) | &lower.value,
        )
    }
    pub fn signed(&self) -> BigInt {
        if self.msb() {
            BigInt::from(self.value.clone()) - BigInt::from(BigUint::one() << self.width as usize)
        } else {
            BigInt::from(self.value.clone())
        }
    }
    pub fn from_signed(&self, value: BigInt) -> Self {
        let modulus = BigInt::one() << self.width as usize;
        Self::new(
            self.width,
            value
                .mod_floor(&modulus)
                .to_biguint()
                .expect("a nonnegative residue"),
        )
    }
}

fn mask(width: u32) -> BigUint {
    if width == 0 {
        BigUint::zero()
    } else {
        (BigUint::one() << width as usize) - 1u8
    }
}

impl Ord for BitVec {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.width
            .cmp(&other.width)
            .then_with(|| self.value.cmp(&other.value))
    }
}
impl PartialOrd for BitVec {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl fmt::Display for BitVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let digits = self.value.to_str_radix(16);
        let width = (self.width as usize).div_ceil(4);
        write!(f, "0x{digits:0>width$}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn masks_and_signed_arithmetic() {
        assert_eq!(BitVec::from_u64(4, 0xff).to_u64(), Some(15));
        assert_eq!(BitVec::from_u64(4, 0b1111).signed().to_string(), "-1");
        assert_eq!(BitVec::from_u64(4, 0b1110).signed().to_string(), "-2");
        assert_eq!(BitVec::from_u64(4, 0b1111).neg().to_u64(), Some(1));
        assert_eq!(BitVec::from_u64(4, 0b1110).abs().to_u64(), Some(2));
        assert_eq!(
            BitVec::from_u64(4, 15)
                .add(&BitVec::from_u64(4, 2))
                .to_u64(),
            Some(1)
        );
        assert_eq!(
            BitVec::from_u64(4, 1).sub(&BitVec::from_u64(4, 2)).to_u64(),
            Some(15)
        );
        assert_eq!(
            BitVec::from_u64(4, 7).div(&BitVec::zero(4)).to_u64(),
            Some(15)
        );
        assert_eq!(
            BitVec::from_u64(4, 7)
                .sdiv(&BitVec::from_u64(4, 2))
                .to_u64(),
            Some(3)
        );
    }

    #[test]
    fn signed_modulo_matches_bap() {
        let negative_three = BitVec::from_u64(8, 0xfd);
        let negative_five = BitVec::from_u64(8, 0xfb);
        assert_eq!(
            BitVec::from_u64(8, 5).smod(&negative_three).to_u64(),
            Some(2)
        );
        assert_eq!(
            negative_five.smod(&BitVec::from_u64(8, 3)).to_u64(),
            Some(1)
        );
        assert_eq!(negative_five.smod(&negative_three).to_u64(), Some(5));
        assert_eq!(
            negative_five
                .srem(&BitVec::from_u64(8, 3))
                .signed()
                .to_string(),
            "-2"
        );
    }

    #[test]
    fn shifts_extract_and_concat() {
        let value = BitVec::from_u64(8, 0b1011_0001);
        assert_eq!(
            value.shl(&BitVec::from_u64(8, 2)).to_u64(),
            Some(0b1100_0100)
        );
        assert_eq!(
            value.lshr(&BitVec::from_u64(8, 2)).to_u64(),
            Some(0b0010_1100)
        );
        assert_eq!(
            value.ashr(&BitVec::from_u64(8, 2)).to_u64(),
            Some(0b1110_1100)
        );
        assert_eq!(value.extract(5, 2).unwrap().to_u64(), Some(0b1100));
        assert_eq!(
            BitVec::from_u64(4, 0xa)
                .concat(&BitVec::from_u64(4, 0x5))
                .to_u64(),
            Some(0xa5)
        );
        assert_eq!(
            BitVec::from_u64(4, 0xf)
                .shl(&BitVec::from_u64(4, 4))
                .to_u64(),
            Some(0)
        );
    }

    #[test]
    fn large_widths_and_gcd() {
        let x = BitVec::from_u64(160, 12);
        let y = BitVec::from_u64(160, 18);
        assert_eq!(x.gcd(&y).to_u64(), Some(6));
        assert_eq!(x.lcm(&y).to_u64(), Some(36));
        let (gcd, a, b) = x.gcdext(&y);
        assert_eq!(gcd.to_u64(), Some(6));
        assert_eq!(a.mul(&x).add(&b.mul(&y)).to_u64(), Some(6));
        let high = BitVec::one(160).shl(&BitVec::from_u64(160, 159));
        assert!(high.msb());
    }
}
