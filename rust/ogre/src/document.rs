use crate::schema::{Fact, FieldSpec};
use crate::{Attribute, Error, Result, Scalar, ScalarType, Schema, Sexp};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;
use std::fs;
use std::path::Path;
use std::rc::Rc;

/// An OGRE schema and deduplicated, shared fact rows.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct Document {
    pub(crate) schema: BTreeMap<String, Schema>,
    pub(crate) entries: BTreeMap<String, Vec<Rc<Fact>>>,
}
impl PartialEq for Document {
    fn eq(&self, other: &Self) -> bool {
        self.schema == other.schema
            && self.entries.len() == other.entries.len()
            && self.entries.iter().all(|(name, facts)| {
                other.entries.get(name).is_some_and(|other| {
                    facts.len() == other.len()
                        && facts
                            .iter()
                            .all(|fact| other.iter().any(|old| old.values == fact.values))
                })
            })
    }
}
impl Eq for Document {}

impl Document {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn is_empty(&self) -> bool {
        self.schema.is_empty()
    }
    pub fn declarations(&self) -> usize {
        self.schema.len()
    }
    pub fn definitions(&self) -> usize {
        self.entries.values().map(Vec::len).sum()
    }
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    pub fn declare(&mut self, name: &str, schema: Schema) -> Result<()> {
        if let Some(old) = self.schema.get(name) {
            if old != &schema {
                return Err(Error::Schema(format!(
                    "signature mismatch for {name}: expected {old:?}, got {schema:?}"
                )));
            }
        } else {
            self.schema.insert(name.into(), schema);
        }
        Ok(())
    }

    pub fn schema(&self, name: &str) -> Option<&Schema> {
        self.schema.get(name)
    }

    pub fn insert_scalars(
        &mut self,
        name: &str,
        schema: Schema,
        values: Vec<Scalar>,
    ) -> Result<()> {
        self.declare(name, schema)?;
        self.insert_fact(name, Rc::new(Fact::new(values, None)))
    }

    pub fn values(&self, name: &str) -> Vec<Vec<Scalar>> {
        self.entries
            .get(name)
            .into_iter()
            .flatten()
            .map(|fact| fact.values.clone())
            .collect()
    }

    pub fn insert<T: 'static>(&mut self, attribute: &Attribute<T>, value: T) -> Result<()> {
        let values = attribute.pack(&value)?;
        self.declare(attribute.name(), attribute.schema().clone())?;
        self.insert_fact(
            attribute.name(),
            Rc::new(Fact::new(values, Some(Rc::new(value)))),
        )
    }

    fn insert_fact(&mut self, name: &str, fact: Rc<Fact>) -> Result<()> {
        let schema = self
            .schema
            .get(name)
            .ok_or_else(|| Error::Schema(format!("attribute {name} is not declared")))?;
        validate_values(name, schema, &fact.values)?;
        let entries = self.entries.entry(name.into()).or_default();
        if !entries.iter().any(|old| old.values == fact.values) {
            entries.insert(0, fact);
        }
        Ok(())
    }

    fn validate(&self) -> Result<()> {
        for (name, facts) in &self.entries {
            let schema = self
                .schema
                .get(name)
                .ok_or_else(|| Error::Schema(format!("attribute {name} has no declaration")))?;
            for fact in facts {
                validate_values(name, schema, &fact.values)?;
            }
        }
        Ok(())
    }

    pub fn to_json(&self) -> Result<String> {
        serde_json::to_string_pretty(self).map_err(|error| Error::Schema(error.to_string()))
    }
    pub fn from_json(input: &str) -> Result<Self> {
        let document: Self =
            serde_json::from_str(input).map_err(|error| Error::Schema(error.to_string()))?;
        document.validate()?;
        Ok(document)
    }

    pub fn get<T: 'static>(&self, attribute: &Attribute<T>) -> Result<Vec<T>> {
        if let Some(schema) = self.schema.get(attribute.name())
            && schema != attribute.schema()
        {
            return Err(Error::Schema(format!(
                "query schema differs for {}",
                attribute.name()
            )));
        }
        self.entries
            .get(attribute.name())
            .unwrap_or(&Vec::new())
            .iter()
            .map(|fact| attribute.unpack(&fact.values))
            .collect()
    }
    pub fn request<T: 'static>(&self, attribute: &Attribute<T>) -> Result<Option<T>> {
        self.request_that(attribute, |_| true)
    }
    pub fn request_that<T: 'static>(
        &self,
        attribute: &Attribute<T>,
        predicate: impl Fn(&T) -> bool,
    ) -> Result<Option<T>> {
        let mut values = self.get(attribute)?.into_iter().filter(|x| predicate(x));
        let result = values.next();
        if values.next().is_some() {
            Err(Error::Ambiguous(attribute.name().into()))
        } else {
            Ok(result)
        }
    }
    pub fn require<T: 'static>(&self, attribute: &Attribute<T>) -> Result<T> {
        self.require_that(attribute, |_| true)
    }
    pub fn require_that<T: 'static>(
        &self,
        attribute: &Attribute<T>,
        predicate: impl Fn(&T) -> bool,
    ) -> Result<T> {
        self.request_that(attribute, predicate)?
            .ok_or_else(|| Error::Missing(attribute.name().into()))
    }

    pub fn merge(&self, other: &Self) -> Result<Self> {
        let mut result = self.clone();
        for (name, schema) in &other.schema {
            result.declare(name, schema.clone())?;
        }
        for (name, facts) in &other.entries {
            for fact in facts {
                result.insert_fact(name, fact.clone())?;
            }
        }
        Ok(result)
    }

    pub fn parse(input: &str) -> Result<Self> {
        let mut document = Self::new();
        for expression in Sexp::parse_all(input)? {
            document.parse_entry(&expression)?;
        }
        Ok(document)
    }

    fn parse_entry(&mut self, expression: &Sexp) -> Result<()> {
        let values = expression
            .list()
            .ok_or_else(|| Error::Schema("expected an OGRE list entry".into()))?;
        let name = values
            .first()
            .and_then(Sexp::atom)
            .ok_or_else(|| Error::Schema("expected an attribute name".into()))?;
        if name == "declare" {
            let name = values
                .get(1)
                .and_then(Sexp::atom)
                .ok_or_else(|| Error::Schema("expected a declaration name".into()))?;
            let fields = values[2..]
                .iter()
                .enumerate()
                .map(|(position, declaration)| parse_field(declaration, position))
                .collect::<Result<_>>()?;
            self.declare(name, Schema::new(fields))
        } else {
            let schema = self
                .schema
                .get(name)
                .cloned()
                .ok_or_else(|| Error::Schema(format!("{name} is not declared")))?;
            let mut fields = BTreeMap::new();
            for (position, definition) in values[1..].iter().enumerate() {
                let (field, value) =
                    match definition {
                        Sexp::Atom(value) => {
                            let field = schema
                                .fields
                                .get(position)
                                .ok_or_else(|| Error::Schema(format!("wrong arity for {name}")))?;
                            (field.name.clone(), field.kind.parse(value)?)
                        }
                        Sexp::List(pair) if pair.len() == 2 => {
                            let field = pair[0]
                                .atom()
                                .ok_or_else(|| Error::Schema("expected a field name".into()))?;
                            let value = pair[1]
                                .atom()
                                .ok_or_else(|| Error::Schema("expected a scalar value".into()))?;
                            let spec = schema.fields.iter().find(|x| x.name == field).ok_or_else(
                                || Error::Schema(format!("unknown field {name}.{field}")),
                            )?;
                            (field.into(), spec.kind.parse(value)?)
                        }
                        _ => {
                            return Err(Error::Schema(
                                "expected a positional or named scalar".into(),
                            ));
                        }
                    };
                if fields.insert(field, value).is_some() {
                    return Err(Error::Schema(format!("duplicate field in {name}")));
                }
            }
            let values = schema
                .fields
                .iter()
                .map(|field| {
                    fields.get(&field.name).cloned().ok_or_else(|| {
                        Error::Schema(format!("missing field {name}.{}", field.name))
                    })
                })
                .collect::<Result<_>>()?;
            self.insert_fact(name, Rc::new(Fact::new(values, None)))
        }
    }

    pub fn load(path: impl AsRef<Path>) -> Result<Self> {
        Self::parse(&fs::read_to_string(path)?)
    }
    pub fn save(&self, path: impl AsRef<Path>) -> Result<()> {
        fs::write(path, self.to_string()).map_err(Into::into)
    }

    pub fn to_yaml(&self) -> String {
        let mut result = String::from("scheme:\n");
        for (name, schema) in &self.schema {
            result.push_str(&format!("  {name:?} : {{"));
            for (index, field) in schema.fields.iter().enumerate() {
                if index != 0 {
                    result.push_str(", ");
                }
                result.push_str(&format!("{:?} : {}", field.name, field.kind.name()));
            }
            result.push_str("}\n");
        }
        for (name, facts) in &self.entries {
            result.push_str(&format!("{name:?}:\n"));
            for fact in facts {
                result.push_str("  - ");
                for (field, value) in self.schema[name].fields.iter().zip(&fact.values) {
                    if field.kind == ScalarType::Str {
                        result.push_str(&format!("{:?}: {:?}\n    ", field.name, value.atom()));
                    } else {
                        result.push_str(&format!("{:?}: {}\n    ", field.name, value.atom()));
                    }
                }
                result.truncate(result.len() - 4);
            }
        }
        result
    }
}

fn validate_values(name: &str, schema: &Schema, values: &[Scalar]) -> Result<()> {
    if values.len() != schema.fields.len() {
        return Err(Error::Schema(format!("wrong arity for {name}")));
    }
    for (field, value) in schema.fields.iter().zip(values) {
        if field.kind != value.kind() {
            return Err(Error::Schema(format!(
                "wrong scalar type for {name}.{}",
                field.name
            )));
        }
    }
    Ok(())
}

fn parse_field(expression: &Sexp, position: usize) -> Result<FieldSpec> {
    let (name, kind) = match expression {
        Sexp::Atom(kind) => (position.to_string(), kind.as_str()),
        Sexp::List(pair) if pair.len() == 2 => {
            let name = pair[0]
                .atom()
                .ok_or_else(|| Error::Schema("expected field name".into()))?;
            let kind = pair[1]
                .atom()
                .ok_or_else(|| Error::Schema("expected field type".into()))?;
            if !name.bytes().enumerate().all(|(i, c)| {
                if i == 0 {
                    c.is_ascii_alphabetic()
                } else {
                    c.is_ascii_alphanumeric() || c == b'-'
                }
            }) {
                return Err(Error::Schema(format!("invalid field name {name:?}")));
            }
            (name.into(), kind)
        }
        _ => return Err(Error::Schema("expected a field declaration".into())),
    };
    let kind = match kind {
        "int" => ScalarType::Int,
        "str" => ScalarType::Str,
        "bool" => ScalarType::Bool,
        "float" => ScalarType::Float,
        _ => return Err(Error::Schema(format!("unknown field type {kind}"))),
    };
    Ok(FieldSpec { name, kind })
}

impl fmt::Display for Document {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (name, schema) in &self.schema {
            let mut declaration = vec![Sexp::Atom("declare".into()), Sexp::Atom(name.clone())];
            declaration.extend(schema.fields.iter().map(|field| {
                if field.name.bytes().all(|x| x.is_ascii_digit()) {
                    Sexp::Atom(field.kind.name().into())
                } else {
                    Sexp::List(vec![
                        Sexp::Atom(field.name.clone()),
                        Sexp::Atom(field.kind.name().into()),
                    ])
                }
            }));
            writeln!(f, "{}", Sexp::List(declaration))?;
        }
        for (name, facts) in &self.entries {
            for fact in facts {
                let mut entry = vec![Sexp::Atom(name.clone())];
                entry.extend(fact.values.iter().map(|value| Sexp::Atom(value.atom())));
                writeln!(f, "{}", Sexp::List(entry))?;
            }
        }
        Ok(())
    }
}
