#![deny(unsafe_op_in_unsafe_fn)]

use bap_bitvec::BitVec;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, ToPrimitive, Zero};
use ocaml::Pointer;

#[derive(Debug)]
pub struct NativeBitvec(pub BigUint);

ocaml::custom!(NativeBitvec);

type Native = Pointer<NativeBitvec>;
type NativeResult = Result<Native, String>;

trait IntoNative {
    fn into_native(self) -> Native;
}

impl IntoNative for BigUint {
    fn into_native(self) -> Native {
        NativeBitvec(self).into()
    }
}

fn width(value: isize) -> u32 {
    u32::try_from(value).expect("bitvector width must be nonnegative")
}

fn signed(size: u32, value: BigInt) -> Native {
    let modulus = BigInt::one() << size as usize;
    let value = value.mod_floor(&modulus).to_biguint().expect("residue");
    value.into_native()
}

fn unary(value: &NativeBitvec, size: isize, operation: impl FnOnce(&BitVec) -> BitVec) -> Native {
    operation(&BitVec::new(width(size), value.0.clone()))
        .into_value()
        .into_native()
}

fn binary(
    left: &NativeBitvec,
    right: &NativeBitvec,
    size: isize,
    operation: impl FnOnce(&BitVec, &BitVec) -> BitVec,
) -> Native {
    let size = width(size);
    let left = BitVec::new(size, left.0.clone());
    let right = BitVec::new(size, right.0.clone());
    operation(&left, &right).into_value().into_native()
}

fn parse(input: &str, base: u32) -> NativeResult {
    if input.starts_with('-') || input.starts_with('+') {
        return Err("invalid string representation, sign is not expected".into());
    }
    let digits = match base {
        16 => input
            .strip_prefix("0x")
            .or_else(|| input.strip_prefix("0X"))
            .unwrap_or(input),
        8 => input
            .strip_prefix("0o")
            .or_else(|| input.strip_prefix("0O"))
            .unwrap_or(input),
        2 => input
            .strip_prefix("0b")
            .or_else(|| input.strip_prefix("0B"))
            .unwrap_or(input),
        _ => input,
    };
    if digits.is_empty() {
        return Err("empty bitvector representation".into());
    }
    BigUint::parse_bytes(digits.as_bytes(), base)
        .map(NativeBitvec)
        .map(Pointer::from)
        .ok_or_else(|| "invalid bitvector representation".into())
}

#[ocaml::func]
pub fn bitvec_rs_zero() -> Native {
    NativeBitvec(BigUint::zero()).into()
}

#[ocaml::func]
pub fn bitvec_rs_one() -> Native {
    NativeBitvec(BigUint::one()).into()
}

#[ocaml::func]
pub fn bitvec_rs_bool(value: bool) -> Native {
    NativeBitvec(BigUint::from(value)).into()
}

#[ocaml::func]
pub fn bitvec_rs_int(value: isize, size: isize) -> Native {
    signed(width(size), BigInt::from(value))
}

#[ocaml::func]
pub fn bitvec_rs_int32(value: i32, size: isize) -> Native {
    signed(width(size), BigInt::from(value))
}

#[ocaml::func]
pub fn bitvec_rs_int64(value: i64, size: isize) -> Native {
    signed(width(size), BigInt::from(value))
}

#[ocaml::func]
pub fn bitvec_rs_bigint(value: &str, size: isize) -> NativeResult {
    let value = value.parse::<BigInt>().map_err(|error| error.to_string())?;
    Ok(signed(width(size), value))
}

#[ocaml::func]
pub fn bitvec_rs_to_bigint(value: &NativeBitvec) -> String {
    value.0.to_string()
}

#[ocaml::func]
pub fn bitvec_rs_ones(size: isize) -> Native {
    BitVec::ones(width(size)).into_value().into_native()
}

#[ocaml::func]
pub fn bitvec_rs_succ(value: &NativeBitvec, size: isize) -> Native {
    unary(value, size, |value| value.succ())
}

#[ocaml::func]
pub fn bitvec_rs_pred(value: &NativeBitvec, size: isize) -> Native {
    unary(value, size, |value| value.pred())
}

#[ocaml::func]
pub fn bitvec_rs_nsucc(value: &NativeBitvec, amount: isize, size: isize) -> Native {
    let size = width(size);
    signed(size, BigInt::from(value.0.clone()) + amount)
}

#[ocaml::func]
pub fn bitvec_rs_npred(value: &NativeBitvec, amount: isize, size: isize) -> Native {
    let size = width(size);
    signed(size, BigInt::from(value.0.clone()) - amount)
}

#[ocaml::func]
pub fn bitvec_rs_neg(value: &NativeBitvec, size: isize) -> Native {
    unary(value, size, |value| value.neg())
}

#[ocaml::func]
pub fn bitvec_rs_lnot(value: &NativeBitvec, size: isize) -> Native {
    unary(value, size, |value| value.not())
}

#[ocaml::func]
pub fn bitvec_rs_abs(value: &NativeBitvec, size: isize) -> Native {
    unary(value, size, |value| value.abs())
}

#[ocaml::func]
pub fn bitvec_rs_add(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.add(right))
}

#[ocaml::func]
pub fn bitvec_rs_sub(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.sub(right))
}

#[ocaml::func]
pub fn bitvec_rs_mul(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.mul(right))
}

#[ocaml::func]
pub fn bitvec_rs_div(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.div(right))
}

#[ocaml::func]
pub fn bitvec_rs_sdiv(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.sdiv(right))
}

#[ocaml::func]
pub fn bitvec_rs_rem(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.rem(right))
}

#[ocaml::func]
pub fn bitvec_rs_srem(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.srem(right))
}

#[ocaml::func]
pub fn bitvec_rs_smod(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.smod(right))
}

#[ocaml::func]
pub fn bitvec_rs_logand(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.and(right))
}

#[ocaml::func]
pub fn bitvec_rs_logor(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.or(right))
}

#[ocaml::func]
pub fn bitvec_rs_logxor(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.xor(right))
}

#[ocaml::func]
pub fn bitvec_rs_lshift(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.shl(right))
}

#[ocaml::func]
pub fn bitvec_rs_rshift(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.lshr(right))
}

#[ocaml::func]
pub fn bitvec_rs_arshift(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.ashr(right))
}

#[ocaml::func]
pub fn bitvec_rs_gcd(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.gcd(right))
}

#[ocaml::func]
pub fn bitvec_rs_lcm(left: &NativeBitvec, right: &NativeBitvec, size: isize) -> Native {
    binary(left, right, size, |left, right| left.lcm(right))
}

#[ocaml::func]
pub fn bitvec_rs_gcdext(
    left: &NativeBitvec,
    right: &NativeBitvec,
    size: isize,
) -> (Native, Native, Native) {
    let size = width(size);
    let left = BitVec::new(size, left.0.clone());
    let right = BitVec::new(size, right.0.clone());
    let (gcd, x, y) = left.gcdext(&right);
    (
        gcd.into_value().into_native(),
        x.into_value().into_native(),
        y.into_value().into_native(),
    )
}

#[ocaml::func]
pub fn bitvec_rs_nth(value: &NativeBitvec, index: isize) -> Result<bool, String> {
    let index = u64::try_from(index).map_err(|_| "bit index must be nonnegative".to_string())?;
    Ok(value.0.bit(index))
}

#[ocaml::func]
pub fn bitvec_rs_msb(value: &NativeBitvec, size: isize) -> bool {
    BitVec::new(width(size), value.0.clone()).msb()
}

#[ocaml::func]
pub fn bitvec_rs_lsb(value: &NativeBitvec) -> bool {
    value.0.bit(0)
}

#[ocaml::func]
pub fn bitvec_rs_compare(left: &NativeBitvec, right: &NativeBitvec) -> isize {
    match left.0.cmp(&right.0) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

#[ocaml::func]
pub fn bitvec_rs_hash(value: &NativeBitvec) -> isize {
    let mut hash = 0xcbf29ce484222325u64;
    for byte in value.0.to_bytes_le() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    (hash & u64::MAX >> 1) as isize
}

#[ocaml::func]
pub fn bitvec_rs_to_string(value: &NativeBitvec) -> String {
    format!("0x{}", value.0.to_str_radix(16))
}

#[ocaml::func]
pub fn bitvec_rs_of_string(input: &str) -> NativeResult {
    parse(input, 10)
        .or_else(|_| parse(input, 16))
        .or_else(|_| parse(input, 8))
        .or_else(|_| parse(input, 2))
}

#[ocaml::func]
pub fn bitvec_rs_of_string_base(base: isize, input: &str) -> NativeResult {
    let base = u32::try_from(base).map_err(|_| "invalid base".to_string())?;
    if !(2..=16).contains(&base)
        || input.starts_with("0x")
        || input.starts_with("0b")
        || input.starts_with("0o")
    {
        return Err("invalid based bitvector representation".into());
    }
    parse(input, base)
}

#[ocaml::func]
pub fn bitvec_rs_to_binary(value: &NativeBitvec) -> ocaml::bigarray::Array1<u8> {
    let bytes = if value.0.is_zero() {
        Vec::new()
    } else {
        value.0.to_bytes_le()
    };
    // SAFETY: the returned Bigarray owns its copied bytes, so it cannot outlive them.
    unsafe { ocaml::bigarray::Array1::from_slice(bytes) }
}

#[ocaml::func]
pub fn bitvec_rs_of_binary(input: ocaml::bigarray::Array1<u8>) -> NativeResult {
    Ok(NativeBitvec(BigUint::from_bytes_le(input.data())).into())
}

#[ocaml::func]
pub fn bitvec_rs_extract(value: &NativeBitvec, hi: isize, lo: isize) -> NativeResult {
    let hi = width(hi);
    let lo = width(lo);
    let source = BitVec::new(hi.saturating_add(1), value.0.clone());
    source
        .extract(hi, lo)
        .map(BitVec::into_value)
        .map(NativeBitvec)
        .map(Pointer::from)
        .ok_or_else(|| "invalid extraction".into())
}

#[ocaml::func]
pub fn bitvec_rs_append(w1: isize, w2: isize, left: &NativeBitvec, right: &NativeBitvec) -> Native {
    let left = BitVec::new(width(w1), left.0.clone());
    let right = BitVec::new(width(w2), right.0.clone());
    left.concat(&right).into_value().into_native()
}

#[ocaml::func]
pub fn bitvec_rs_fits_int(value: &NativeBitvec, bits: isize) -> bool {
    let bits = width(bits);
    value.0 < BigUint::one() << (bits - 1) as usize
}

#[ocaml::func]
pub fn bitvec_rs_fits_int32(value: &NativeBitvec) -> bool {
    value.0 <= BigUint::from(i32::MAX as u32)
}

#[ocaml::func]
pub fn bitvec_rs_fits_int64(value: &NativeBitvec) -> bool {
    value.0 <= BigUint::from(i64::MAX as u64)
}

#[ocaml::func]
pub fn bitvec_rs_to_int(value: &NativeBitvec, bits: isize) -> Result<isize, String> {
    let bits = width(bits);
    let value = value
        .0
        .to_u64()
        .filter(|_| value.0 <= ((BigUint::one() << bits as usize) - 1u8));
    value
        .map(|value| value as isize)
        .ok_or_else(|| "value does not fit int".into())
}

#[ocaml::func]
pub fn bitvec_rs_to_int32(value: &NativeBitvec) -> Result<i32, String> {
    value
        .0
        .to_u32()
        .map(|value| value as i32)
        .ok_or_else(|| "value does not fit int32".into())
}

#[ocaml::func]
pub fn bitvec_rs_to_int64(value: &NativeBitvec) -> Result<i64, String> {
    value
        .0
        .to_u64()
        .map(|value| value as i64)
        .ok_or_else(|| "value does not fit int64".into())
}
