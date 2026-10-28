use crate::{Error, Result};
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::cell::OnceCell;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::rc::Rc;

#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub enum ScalarType {
    Int,
    Str,
    Bool,
    Float,
}
impl ScalarType {
    pub fn name(self) -> &'static str {
        match self {
            Self::Int => "int",
            Self::Str => "str",
            Self::Bool => "bool",
            Self::Float => "float",
        }
    }
    pub fn parse(self, input: &str) -> Result<Scalar> {
        match self {
            Self::Int => parse_int(input).map(Scalar::Int),
            Self::Str => Ok(Scalar::Str(input.into())),
            Self::Bool => match input {
                "true" => Ok(Scalar::Bool(true)),
                "false" => Ok(Scalar::Bool(false)),
                _ => Err(type_error(self, input)),
            },
            Self::Float => match input {
                "infinity" | "+infinity" => Ok(Scalar::Float(f64::INFINITY)),
                "-infinity" => Ok(Scalar::Float(f64::NEG_INFINITY)),
                "nan" => Ok(Scalar::Float(f64::NAN)),
                _ => input
                    .parse()
                    .map(Scalar::Float)
                    .map_err(|_| type_error(self, input)),
            },
        }
    }
    pub fn normalize(self, input: &str) -> Result<Scalar> {
        self.parse(input)
    }
}
fn type_error(kind: ScalarType, input: &str) -> Error {
    Error::Schema(format!("value {input:?} is not a valid {}", kind.name()))
}
fn parse_int(input: &str) -> Result<i64> {
    let cleaned = input.replace('_', "");
    let (negative, digits) = cleaned
        .strip_prefix('-')
        .map_or((false, cleaned.as_str()), |x| (true, x));
    let (radix, digits) = digits
        .strip_prefix("0x")
        .or_else(|| digits.strip_prefix("0X"))
        .map_or((10, digits), |x| (16, x));
    let value = i128::from_str_radix(digits.strip_prefix('+').unwrap_or(digits), radix)
        .map_err(|_| type_error(ScalarType::Int, input))?;
    let value = if negative { -value } else { value };
    i64::try_from(value).map_err(|_| type_error(ScalarType::Int, input))
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Scalar {
    Int(i64),
    Str(String),
    Bool(bool),
    Float(f64),
}
impl Scalar {
    pub fn kind(&self) -> ScalarType {
        match self {
            Self::Int(_) => ScalarType::Int,
            Self::Str(_) => ScalarType::Str,
            Self::Bool(_) => ScalarType::Bool,
            Self::Float(_) => ScalarType::Float,
        }
    }
    pub fn atom(&self) -> String {
        match self {
            Self::Int(x) => x.to_string(),
            Self::Str(x) => x.clone(),
            Self::Bool(x) => x.to_string(),
            Self::Float(x) if x.is_nan() => "nan".into(),
            Self::Float(x) if *x == f64::INFINITY => "infinity".into(),
            Self::Float(x) if *x == f64::NEG_INFINITY => "-infinity".into(),
            Self::Float(x) => x.to_string(),
        }
    }
}
impl PartialEq for Scalar {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Int(x), Self::Int(y)) => x == y,
            (Self::Str(x), Self::Str(y)) => x == y,
            (Self::Bool(x), Self::Bool(y)) => x == y,
            (Self::Float(x), Self::Float(y)) => x.total_cmp(y).is_eq(),
            _ => false,
        }
    }
}
impl Eq for Scalar {}
impl Hash for Scalar {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind().hash(state);
        match self {
            Self::Int(value) => value.hash(state),
            Self::Str(value) => value.hash(state),
            Self::Bool(value) => value.hash(state),
            Self::Float(value) => value.to_bits().hash(state),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub struct FieldSpec {
    pub name: String,
    pub kind: ScalarType,
}

pub struct Field<T> {
    spec: FieldSpec,
    marker: PhantomData<fn() -> T>,
}
impl<T> Clone for Field<T> {
    fn clone(&self) -> Self {
        Self {
            spec: self.spec.clone(),
            marker: PhantomData,
        }
    }
}
impl<T> fmt::Debug for Field<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.spec.fmt(f)
    }
}
impl<T> Field<T> {
    fn new(name: impl Into<String>, kind: ScalarType) -> Self {
        Self {
            spec: FieldSpec {
                name: name.into(),
                kind,
            },
            marker: PhantomData,
        }
    }
    pub fn name(&self) -> &str {
        &self.spec.name
    }
    pub fn kind(&self) -> ScalarType {
        self.spec.kind
    }
    pub fn spec(&self) -> FieldSpec {
        self.spec.clone()
    }
}
impl Field<i64> {
    pub fn int(name: impl Into<String>) -> Self {
        Self::new(name, ScalarType::Int)
    }
}
impl Field<String> {
    pub fn str(name: impl Into<String>) -> Self {
        Self::new(name, ScalarType::Str)
    }
}
impl Field<bool> {
    pub fn bool(name: impl Into<String>) -> Self {
        Self::new(name, ScalarType::Bool)
    }
}
impl Field<f64> {
    pub fn float(name: impl Into<String>) -> Self {
        Self::new(name, ScalarType::Float)
    }
}

#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
pub struct Schema {
    pub(crate) fields: Vec<FieldSpec>,
}
impl Schema {
    pub fn new(fields: Vec<FieldSpec>) -> Self {
        Self { fields }
    }
    pub fn fields(&self) -> &[FieldSpec] {
        &self.fields
    }
    pub fn field<T>(&self, field: &Field<T>) -> Self {
        let mut fields = self.fields.clone();
        fields.push(field.spec());
        Self { fields }
    }
    pub fn position(&self, field: &FieldSpec) -> Option<usize> {
        self.fields.iter().position(|candidate| candidate == field)
    }
}

/// An in-memory row. The scalar values are serialized; typed values are cached.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub(crate) struct Fact {
    pub values: Vec<Scalar>,
    #[serde(skip, default = "OnceCell::new")]
    pub typed: OnceCell<Rc<dyn Any>>,
}
impl Fact {
    pub fn new(values: Vec<Scalar>, typed: Option<Rc<dyn Any>>) -> Self {
        let cell = OnceCell::new();
        if let Some(value) = typed {
            cell.set(value).expect("new typed cell");
        }
        Self {
            values,
            typed: cell,
        }
    }
}
impl PartialEq for Fact {
    fn eq(&self, other: &Self) -> bool {
        self.values == other.values
    }
}
impl Eq for Fact {}

type Encode<T> = Rc<dyn Fn(&T) -> Result<Vec<Scalar>>>;
type Decode<T> = Rc<dyn Fn(&[Scalar]) -> Result<T>>;

pub struct Attribute<T> {
    pub(crate) name: String,
    pub(crate) schema: Schema,
    pub(crate) encode: Encode<T>,
    pub(crate) decode: Decode<T>,
}
impl<T> Clone for Attribute<T> {
    fn clone(&self) -> Self {
        Self {
            name: self.name.clone(),
            schema: self.schema.clone(),
            encode: self.encode.clone(),
            decode: self.decode.clone(),
        }
    }
}
impl<T> fmt::Debug for Attribute<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Attribute")
            .field("name", &self.name)
            .field("schema", &self.schema)
            .finish()
    }
}

impl<T: 'static> Attribute<T> {
    pub fn new(
        name: impl Into<String>,
        schema: Schema,
        encode: impl Fn(&T) -> Result<Vec<Scalar>> + 'static,
        decode: impl Fn(&[Scalar]) -> Result<T> + 'static,
    ) -> Self {
        Self {
            name: name.into(),
            schema,
            encode: Rc::new(encode),
            decode: Rc::new(decode),
        }
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn schema(&self) -> &Schema {
        &self.schema
    }
    pub(crate) fn pack(&self, value: &T) -> Result<Vec<Scalar>> {
        let values = (self.encode)(value)?;
        if values.len() != self.schema.fields.len() {
            return Err(Error::Schema(format!(
                "attribute {} expects {} fields, got {}",
                self.name,
                self.schema.fields.len(),
                values.len()
            )));
        }
        for (field, value) in self.schema.fields.iter().zip(&values) {
            if field.kind != value.kind() {
                return Err(type_error(field.kind, &value.atom()));
            }
        }
        Ok(values)
    }
    pub(crate) fn unpack(&self, values: &[Scalar]) -> Result<T> {
        (self.decode)(values)
    }
}
