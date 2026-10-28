use crate::{BinOp, Cast, Def, Endian, Exp, Type, UnOp, Var};
use bap_bitvec::BitVec;
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    Type(String),
    Width { expected: u32, actual: u32 },
    Unknown(String, Type),
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Type(message) => f.write_str(message),
            Self::Width { expected, actual } => write!(f, "expected {expected} bits, got {actual}"),
            Self::Unknown(message, typ) => {
                write!(f, "cannot evaluate unknown {message} of type {typ:?}")
            }
        }
    }
}
impl std::error::Error for Error {}
pub type Result<T, E = Error> = std::result::Result<T, E>;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Memory {
    pub address_width: u32,
    pub cells: BTreeMap<BigUint, u8>,
}
impl Memory {
    pub fn new(address_width: u32) -> Self {
        Self {
            address_width,
            cells: BTreeMap::new(),
        }
    }
    fn address(&self, address: &BigUint, offset: u32) -> BigUint {
        BitVec::new(self.address_width, address + offset).into_value()
    }
    pub fn read(&self, address: &BigUint, size: u32, endian: Endian) -> Result<BitVec> {
        let mut bytes = Vec::with_capacity(size as usize);
        for index in 0..size {
            let byte = self
                .cells
                .get(&self.address(address, index))
                .copied()
                .unwrap_or(0);
            bytes.push(byte);
        }
        if endian == Endian::Big {
            bytes.reverse();
        }
        Ok(BitVec::from_biguint(
            size * 8,
            BigUint::from_bytes_le(&bytes),
        ))
    }
    pub fn write(
        &mut self,
        address: &BigUint,
        value: &BitVec,
        endian: Endian,
        size: u32,
    ) -> Result<()> {
        if size * 8 != value.width() {
            return Err(Error::Width {
                expected: size * 8,
                actual: value.width(),
            });
        }
        let mut bytes = value.value().to_bytes_le();
        bytes.resize(size as usize, 0);
        if endian == Endian::Big {
            bytes.reverse();
        }
        for (index, byte) in bytes.into_iter().enumerate() {
            self.cells.insert(self.address(address, index as u32), byte);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Bits(BitVec),
    Memory(Memory),
}
impl Value {
    pub fn bits(&self) -> Result<&BitVec> {
        match self {
            Self::Bits(value) => Ok(value),
            Self::Memory(_) => Err(Error::Type("expected a bitvector".into())),
        }
    }
    pub fn memory(&self) -> Result<&Memory> {
        match self {
            Self::Memory(memory) => Ok(memory),
            Self::Bits(_) => Err(Error::Type("expected a memory".into())),
        }
    }
    pub fn width(&self) -> u32 {
        match self {
            Self::Bits(value) => value.width(),
            Self::Memory(memory) => memory.address_width,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Evaluator {
    pub vars: BTreeMap<Var, Value>,
    pub memory: Memory,
}
impl Evaluator {
    pub fn new(address_width: u32) -> Self {
        Self {
            vars: BTreeMap::new(),
            memory: Memory::new(address_width),
        }
    }
    pub fn bind(&mut self, var: Var, value: Value) {
        self.vars.insert(var, value);
    }
    pub fn eval_def(&mut self, def: &Def) -> Result<Value> {
        let value = self.eval(&def.rhs)?;
        if let Value::Memory(memory) = &value {
            self.memory = memory.clone();
        }
        self.vars.insert(def.var.clone(), value.clone());
        Ok(value)
    }
    pub fn eval(&mut self, exp: &Exp) -> Result<Value> {
        match exp {
            Exp::Int(value) => Ok(Value::Bits(value.clone())),
            Exp::Var(var) => self
                .vars
                .get(var)
                .cloned()
                .ok_or_else(|| Error::Type(format!("unbound variable {}", var.name))),
            Exp::Load {
                memory,
                address,
                endian,
                size,
            } => {
                let memory = self.eval(memory)?.memory()?.clone();
                let address = self.eval(address)?.bits()?.value().clone();
                memory.read(&address, *size, *endian).map(Value::Bits)
            }
            Exp::Store {
                memory,
                address,
                value,
                endian,
                size,
            } => {
                let mut memory = self.eval(memory)?.memory()?.clone();
                let address = self.eval(address)?.bits()?.value().clone();
                let value = self.eval(value)?.bits()?.clone();
                memory.write(&address, &value, *endian, *size)?;
                Ok(Value::Memory(memory))
            }
            Exp::Bin { op, left, right } => {
                let left = self.eval(left)?.bits()?.clone();
                let right = self.eval(right)?.bits()?.clone();
                self.binary(*op, &left, &right)
            }
            Exp::Un { op, value } => {
                let value = self.eval(value)?.bits()?.clone();
                Ok(Value::Bits(match op {
                    UnOp::Neg => value.neg(),
                    UnOp::Not => value.not(),
                }))
            }
            Exp::Cast { kind, size, value } => {
                let value = self.eval(value)?.bits()?.clone();
                self.cast(*kind, *size, &value)
            }
            Exp::Let { var, value, body } => {
                let value = self.eval(value)?;
                let old = self.vars.insert(var.clone(), value);
                let result = self.eval(body);
                if let Some(old) = old {
                    self.vars.insert(var.clone(), old);
                } else {
                    self.vars.remove(var);
                }
                result
            }
            Exp::Ite { condition, yes, no } => {
                let condition = self.eval(condition)?.bits()?.clone();
                if condition.width() != 1 {
                    return Err(Error::Width {
                        expected: 1,
                        actual: condition.width(),
                    });
                }
                if condition.is_one() {
                    self.eval(yes)
                } else {
                    self.eval(no)
                }
            }
            Exp::Extract { high, low, value } => {
                let value = self.eval(value)?.bits()?.clone();
                let source_width = value.width().max(high.saturating_add(1));
                BitVec::new(source_width, value.into_value())
                    .extract(*high, *low)
                    .map(Value::Bits)
                    .ok_or_else(|| Error::Type("invalid extraction".into()))
            }
            Exp::Concat { left, right } => {
                let left = self.eval(left)?.bits()?.clone();
                let right = self.eval(right)?.bits()?.clone();
                Ok(Value::Bits(left.concat(&right)))
            }
            Exp::Unknown(message, typ) => Err(Error::Unknown(message.clone(), typ.clone())),
        }
    }

    fn binary(&self, op: BinOp, left: &BitVec, right: &BitVec) -> Result<Value> {
        let is_shift = matches!(op, BinOp::LShift | BinOp::RShift | BinOp::AShift);
        let width = left.width().max(right.width());
        let normalized = |value: &BitVec| BitVec::new(width, value.value().clone());
        let (left, right) = if is_shift {
            (left.clone(), right.clone())
        } else {
            (normalized(left), normalized(right))
        };
        let bits = |value| Value::Bits(value);
        Ok(match op {
            BinOp::Add => bits(left.add(&right)),
            BinOp::Sub => bits(left.sub(&right)),
            BinOp::Mul => bits(left.mul(&right)),
            BinOp::Div => bits(left.div(&right)),
            BinOp::SDiv => bits(left.sdiv(&right)),
            BinOp::Rem => bits(left.rem(&right)),
            BinOp::SRem => bits(left.srem(&right)),
            BinOp::Mod => bits(left.smod(&right)),
            BinOp::LShift => bits(left.shl(&right)),
            BinOp::RShift => bits(left.lshr(&right)),
            BinOp::AShift => bits(left.ashr(&right)),
            BinOp::And => bits(left.and(&right)),
            BinOp::Or => bits(left.or(&right)),
            BinOp::Xor => bits(left.xor(&right)),
            BinOp::Eq => bits(BitVec::from_u64(1, u64::from(left == right))),
            BinOp::Neq => bits(BitVec::from_u64(1, u64::from(left != right))),
            BinOp::Lt => bits(BitVec::from_u64(1, u64::from(left < right))),
            BinOp::Le => bits(BitVec::from_u64(1, u64::from(left <= right))),
            BinOp::Gt => bits(BitVec::from_u64(1, u64::from(left > right))),
            BinOp::Ge => bits(BitVec::from_u64(1, u64::from(left >= right))),
            BinOp::SLt => bits(BitVec::from_u64(
                1,
                u64::from(left.signed() < right.signed()),
            )),
            BinOp::SLe => bits(BitVec::from_u64(
                1,
                u64::from(left.signed() <= right.signed()),
            )),
            BinOp::SGt => bits(BitVec::from_u64(
                1,
                u64::from(left.signed() > right.signed()),
            )),
            BinOp::SGe => bits(BitVec::from_u64(
                1,
                u64::from(left.signed() >= right.signed()),
            )),
        })
    }

    fn cast(&self, kind: Cast, size: u32, value: &BitVec) -> Result<Value> {
        if size == 0 {
            return Err(Error::Width {
                expected: 1,
                actual: 0,
            });
        }
        Ok(Value::Bits(match kind {
            Cast::Low => BitVec::new(size, value.value().clone()),
            Cast::High => {
                if size > value.width() {
                    return Err(Error::Width {
                        expected: value.width(),
                        actual: size,
                    });
                }
                value
                    .extract(value.width() - 1, value.width() - size)
                    .expect("validated high cast")
            }
            Cast::Unsigned => BitVec::new(size, value.value().clone()),
            Cast::Signed => {
                if size <= value.width() {
                    BitVec::new(size, value.value().clone())
                } else {
                    let extension = size - value.width();
                    if value.msb() {
                        BitVec::ones(extension).concat(value)
                    } else {
                        BitVec::zero(extension).concat(value)
                    }
                }
            }
        }))
    }
}
