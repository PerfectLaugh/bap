use crate::schema::{Fact, FieldSpec};
use crate::{Attribute, Document, Error, Field, Result, Scalar};
use std::any::Any;
use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Value(Scalar),
    Field(FieldRef),
    Not(Box<Expr>),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
}
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BinaryOp {
    And,
    Or,
    Eq,
    Lt,
    Add,
    Sub,
}

impl std::ops::Add for Expr {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        Self::binary(BinaryOp::Add, self, other)
    }
}
impl std::ops::Sub for Expr {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        Self::binary(BinaryOp::Sub, self, other)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct FieldRef {
    attribute: Option<String>,
    position: Option<usize>,
    field_position: Option<usize>,
    field: FieldSpec,
}

impl Expr {
    pub fn int(value: i64) -> Self {
        Self::Value(Scalar::Int(value))
    }
    pub fn str(value: impl Into<String>) -> Self {
        Self::Value(Scalar::Str(value.into()))
    }
    pub fn float(value: f64) -> Self {
        Self::Value(Scalar::Float(value))
    }
    pub fn bool(value: bool) -> Self {
        Self::Value(Scalar::Bool(value))
    }
    pub fn field<T: 'static>(attribute: &Attribute<T>, field: &Field<impl Sized>) -> Self {
        Self::Field(FieldRef {
            attribute: Some(attribute.name().into()),
            position: None,
            field_position: None,
            field: field.spec(),
        })
    }
    pub fn positional<T>(position: usize, field: &Field<T>) -> Self {
        Self::Field(FieldRef {
            attribute: None,
            position: Some(position),
            field_position: None,
            field: field.spec(),
        })
    }
    pub fn dynamic(attribute: Option<String>, position: Option<usize>, field: FieldSpec) -> Self {
        Self::Field(FieldRef {
            attribute,
            position,
            field_position: None,
            field,
        })
    }
    fn binary(operator: BinaryOp, left: Self, right: Self) -> Self {
        Self::Binary(operator, Box::new(left), Box::new(right)).simplify()
    }
    pub fn and(self, other: Self) -> Self {
        Self::binary(BinaryOp::And, self, other)
    }
    pub fn or(self, other: Self) -> Self {
        Self::binary(BinaryOp::Or, self, other)
    }
    pub fn implies(self, other: Self) -> Self {
        self.not().or(other)
    }
    pub fn eq(self, other: Self) -> Self {
        Self::binary(BinaryOp::Eq, self, other)
    }
    pub fn ne(self, other: Self) -> Self {
        self.eq(other).not()
    }
    pub fn lt(self, other: Self) -> Self {
        Self::binary(BinaryOp::Lt, self, other)
    }
    pub fn gt(self, other: Self) -> Self {
        other.lt(self)
    }
    pub fn le(self, other: Self) -> Self {
        other.lt(self).not()
    }
    pub fn ge(self, other: Self) -> Self {
        self.lt(other).not()
    }
    #[allow(clippy::should_implement_trait)]
    pub fn not(self) -> Self {
        match self {
            Self::Not(value) => *value,
            value => Self::Not(Box::new(value)).simplify(),
        }
    }
    fn simplify(self) -> Self {
        match self {
            Self::Not(value) => match *value {
                Self::Value(Scalar::Bool(value)) => Self::bool(!value),
                Self::Not(value) => value.simplify(),
                value => Self::Not(Box::new(value.simplify())),
            },
            Self::Binary(operator, left, right) => {
                let left = left.simplify();
                let right = right.simplify();
                match (&operator, &left, &right) {
                    (BinaryOp::And, Self::Value(Scalar::Bool(false)), _)
                    | (BinaryOp::And, _, Self::Value(Scalar::Bool(false))) => Self::bool(false),
                    (BinaryOp::And, Self::Value(Scalar::Bool(true)), value)
                    | (BinaryOp::And, value, Self::Value(Scalar::Bool(true))) => value.clone(),
                    (BinaryOp::Or, Self::Value(Scalar::Bool(true)), _)
                    | (BinaryOp::Or, _, Self::Value(Scalar::Bool(true))) => Self::bool(true),
                    (BinaryOp::Or, Self::Value(Scalar::Bool(false)), value)
                    | (BinaryOp::Or, value, Self::Value(Scalar::Bool(false))) => value.clone(),
                    _ => {
                        let expression = Self::Binary(operator, Box::new(left), Box::new(right));
                        if !expression.has_variables()
                            && let Ok(value) = expression.evaluate(&[])
                        {
                            return Self::Value(value);
                        }
                        expression
                    }
                }
            }
            value => value,
        }
    }
    fn has_variables(&self) -> bool {
        match self {
            Self::Field(_) => true,
            Self::Not(value) => value.has_variables(),
            Self::Binary(_, left, right) => left.has_variables() || right.has_variables(),
            Self::Value(_) => false,
        }
    }
    fn resolve(self, selection: &Selection) -> Result<Self> {
        match self {
            Self::Field(reference) => resolve(&reference, selection)?
                .last()
                .cloned()
                .map(Self::Field)
                .ok_or_else(|| {
                    Error::Query(format!("field {} is not selected", reference.field.name))
                }),
            Self::Not(value) => Ok(Self::Not(Box::new(value.resolve(selection)?))),
            Self::Binary(operator, left, right) => Ok(Self::Binary(
                operator,
                Box::new(left.resolve(selection)?),
                Box::new(right.resolve(selection)?),
            )),
            value => Ok(value),
        }
    }
    fn evaluate(&self, row: &[Rc<Fact>]) -> Result<Scalar> {
        match self {
            Self::Value(value) => Ok(value.clone()),
            Self::Field(reference) => {
                let attribute = reference
                    .position
                    .ok_or_else(|| Error::Query("unresolved attribute".into()))?;
                let field = reference
                    .field_position
                    .ok_or_else(|| Error::Query("unresolved field".into()))?;
                row.get(attribute)
                    .and_then(|fact| fact.values.get(field))
                    .cloned()
                    .ok_or_else(|| Error::Query("field position is out of range".into()))
            }
            Self::Not(value) => match value.evaluate(row)? {
                Scalar::Bool(value) => Ok(Scalar::Bool(!value)),
                _ => Err(type_error("not")),
            },
            Self::Binary(BinaryOp::And, left, right) => match left.evaluate(row)? {
                Scalar::Bool(false) => Ok(Scalar::Bool(false)),
                Scalar::Bool(true) => expect_bool(right.evaluate(row)?),
                _ => Err(type_error("and")),
            },
            Self::Binary(BinaryOp::Or, left, right) => match left.evaluate(row)? {
                Scalar::Bool(true) => Ok(Scalar::Bool(true)),
                Scalar::Bool(false) => expect_bool(right.evaluate(row)?),
                _ => Err(type_error("or")),
            },
            Self::Binary(operator, left, right) => {
                let left = left.evaluate(row)?;
                let right = right.evaluate(row)?;
                match operator {
                    BinaryOp::Eq => {
                        if left.kind() != right.kind() {
                            return Err(type_error("equality"));
                        }
                        Ok(Scalar::Bool(left == right))
                    }
                    BinaryOp::Lt => Ok(Scalar::Bool(scalar_less(&left, &right)?)),
                    BinaryOp::Add | BinaryOp::Sub => arithmetic(*operator, left, right),
                    BinaryOp::And | BinaryOp::Or => unreachable!(),
                }
            }
        }
    }
}
fn expect_bool(value: Scalar) -> Result<Scalar> {
    if let Scalar::Bool(_) = value {
        Ok(value)
    } else {
        Err(type_error("boolean operator"))
    }
}
fn type_error(operator: &str) -> Error {
    Error::Query(format!("invalid operand type for {operator}"))
}
fn scalar_less(x: &Scalar, y: &Scalar) -> Result<bool> {
    match (x, y) {
        (Scalar::Int(x), Scalar::Int(y)) => Ok(x < y),
        (Scalar::Str(x), Scalar::Str(y)) => Ok(x < y),
        (Scalar::Float(x), Scalar::Float(y)) => Ok(x.total_cmp(y).is_lt()),
        _ => Err(type_error("comparison")),
    }
}
fn arithmetic(operator: BinaryOp, x: Scalar, y: Scalar) -> Result<Scalar> {
    match (operator, x, y) {
        (BinaryOp::Add, Scalar::Int(x), Scalar::Int(y)) => Ok(Scalar::Int(x.wrapping_add(y))),
        (BinaryOp::Sub, Scalar::Int(x), Scalar::Int(y)) => Ok(Scalar::Int(x.wrapping_sub(y))),
        (BinaryOp::Add, Scalar::Float(x), Scalar::Float(y)) => Ok(Scalar::Float(x + y)),
        (BinaryOp::Sub, Scalar::Float(x), Scalar::Float(y)) => Ok(Scalar::Float(x - y)),
        _ => Err(type_error("arithmetic")),
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Join {
    fields: Vec<FieldRef>,
}
impl Join {
    pub fn new(fields: Vec<FieldRef>) -> Self {
        Self { fields }
    }
    pub fn qualified<T: 'static>(attribute: &Attribute<T>, field: &Field<impl Sized>) -> FieldRef {
        FieldRef {
            attribute: Some(attribute.name().into()),
            position: None,
            field_position: None,
            field: field.spec(),
        }
    }
    pub fn unqualified<T>(field: &Field<T>) -> FieldRef {
        FieldRef {
            attribute: None,
            position: None,
            field_position: None,
            field: field.spec(),
        }
    }
    pub fn positional<T>(position: usize, field: &Field<T>) -> FieldRef {
        FieldRef {
            attribute: None,
            position: Some(position),
            field_position: None,
            field: field.spec(),
        }
    }
    pub fn dynamic(
        attribute: Option<String>,
        position: Option<usize>,
        field: FieldSpec,
    ) -> FieldRef {
        FieldRef {
            attribute,
            position,
            field_position: None,
            field,
        }
    }
}

type Decode = Rc<dyn Fn(&[Scalar]) -> Result<Rc<dyn Any>>>;
pub(crate) struct QueryTable {
    pub name: String,
    pub schema: crate::Schema,
    pub decode: Decode,
}

#[derive(Clone, Default)]
pub struct Selection {
    pub(crate) tables: Vec<Rc<QueryTable>>,
}
impl fmt::Debug for Selection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Selection")
            .field(
                "attributes",
                &self.tables.iter().map(|x| &x.name).collect::<Vec<_>>(),
            )
            .finish()
    }
}
impl Selection {
    pub fn one<T: 'static>(attribute: &Attribute<T>) -> Self {
        Self {
            tables: vec![table(attribute)],
        }
    }
    pub fn and<T: 'static>(mut self, attribute: &Attribute<T>) -> Self {
        self.tables.push(table(attribute));
        self
    }
}
fn table<T: 'static>(attribute: &Attribute<T>) -> Rc<QueryTable> {
    let decoder = attribute.clone();
    Rc::new(QueryTable {
        name: attribute.name().into(),
        schema: attribute.schema().clone(),
        decode: Rc::new(move |values| {
            decoder
                .unpack(values)
                .map(|value| Rc::new(value) as Rc<dyn Any>)
        }),
    })
}

#[derive(Clone, Debug)]
pub struct Query {
    selection: Selection,
    condition: Expr,
    joins: Vec<Join>,
}
impl Query {
    pub fn new(selection: Selection) -> Self {
        Self {
            selection,
            condition: Expr::bool(true),
            joins: Vec::new(),
        }
    }
    pub fn where_expr(mut self, condition: Expr) -> Self {
        self.condition = condition;
        self
    }
    pub fn join(mut self, joins: Vec<Join>) -> Self {
        self.joins = joins;
        self
    }

    pub fn prepare<'a>(&self, document: &'a Document) -> Result<PreparedQuery<'a>> {
        if self.selection.tables.is_empty()
            || self
                .selection
                .tables
                .iter()
                .any(|table| !document.entries.contains_key(&table.name))
        {
            return Ok(PreparedQuery {
                document,
                selection: self.selection.clone(),
                condition: self.condition.clone(),
                indexes: BTreeMap::new(),
                empty: true,
            });
        }
        let mut condition = self.condition.clone().resolve(&self.selection)?;
        let mut keys = BTreeMap::new();
        for join in &self.joins {
            let mut variables = Vec::new();
            for field in &join.fields {
                variables.extend(resolve(field, &self.selection)?);
            }
            if let Some(first) = variables.first().cloned() {
                for variable in &variables[1..] {
                    condition =
                        condition.and(Expr::Field(first.clone()).eq(Expr::Field(variable.clone())));
                }
            }
            for variable in &variables {
                let position = variable.position.expect("resolved position");
                if let Some(earlier) = variables
                    .iter()
                    .find(|other| other.position.expect("resolved") < position)
                {
                    keys.entry(position).or_insert((
                        variable.field_position.expect("resolved field"),
                        earlier.position.expect("resolved attribute"),
                        earlier.field_position.expect("resolved field"),
                    ));
                }
            }
        }
        if self.selection.tables.is_empty()
            || self
                .selection
                .tables
                .iter()
                .any(|table| !document.entries.contains_key(&table.name))
        {
            return Ok(PreparedQuery {
                document,
                selection: self.selection.clone(),
                condition,
                indexes: BTreeMap::new(),
                empty: true,
            });
        }
        let mut indexes = BTreeMap::new();
        for (position, (field, earlier, other)) in keys {
            let table = &self.selection.tables[position];
            let mut buckets: HashMap<Scalar, Vec<Rc<Fact>>> = HashMap::new();
            for fact in &document.entries[&table.name] {
                buckets
                    .entry(fact.values[field].clone())
                    .or_default()
                    .push(fact.clone());
            }
            indexes.insert(
                position,
                JoinIndex {
                    earlier,
                    other,
                    buckets,
                },
            );
        }
        Ok(PreparedQuery {
            document,
            selection: self.selection.clone(),
            condition,
            indexes,
            empty: false,
        })
    }

    pub fn execute(&self, document: &Document) -> Result<Vec<Row>> {
        self.prepare(document)?.execute()
    }
}

#[derive(Debug)]
struct JoinIndex {
    earlier: usize,
    other: usize,
    buckets: HashMap<Scalar, Vec<Rc<Fact>>>,
}

/// A query whose expressions and join indexes are reusable across executions.
#[derive(Debug)]
pub struct PreparedQuery<'a> {
    document: &'a Document,
    selection: Selection,
    condition: Expr,
    indexes: BTreeMap<usize, JoinIndex>,
    empty: bool,
}
impl PreparedQuery<'_> {
    pub fn execute(&self) -> Result<Vec<Row>> {
        let mut result = Vec::new();
        self.for_each(|row| {
            result.push(row.into_owned());
            Ok(())
        })?;
        Ok(result)
    }

    /// Visits matching rows without materializing the cross product or results.
    pub fn for_each(
        &self,
        mut visitor: impl for<'row> FnMut(RowRef<'row>) -> Result<()>,
    ) -> Result<()> {
        if self.empty {
            return Ok(());
        }
        enumerate(self, 0, &mut Vec::new(), &mut visitor)
    }
}

fn resolve(reference: &FieldRef, selection: &Selection) -> Result<Vec<FieldRef>> {
    let matches = |position: usize, table: &Rc<QueryTable>| {
        reference
            .attribute
            .as_ref()
            .is_none_or(|name| name == &table.name)
            && reference
                .position
                .is_none_or(|expected| expected == position)
            && table.schema.position(&reference.field).is_some()
    };
    let mut result = Vec::new();
    for (position, table) in selection.tables.iter().enumerate() {
        if matches(position, table) {
            let mut resolved = reference.clone();
            resolved.position = Some(position);
            resolved.field_position = table.schema.position(&reference.field);
            result.push(resolved);
        }
    }
    if let Some(name) = &reference.attribute
        && !selection.tables.iter().any(|table| table.name == *name)
    {
        return Err(Error::Query(format!("attribute {name} is not selected")));
    }
    if result.is_empty() {
        let schemas = selection
            .tables
            .iter()
            .map(|table| (&table.name, &table.schema.fields))
            .collect::<Vec<_>>();
        return Err(Error::Query(format!(
            "field {} is not selected: {reference:?}; schemas: {schemas:?}",
            reference.field.name
        )));
    }
    Ok(result)
}

fn enumerate<F>(
    query: &PreparedQuery<'_>,
    position: usize,
    prefix: &mut Vec<Rc<Fact>>,
    visitor: &mut F,
) -> Result<()>
where
    F: for<'row> FnMut(RowRef<'row>) -> Result<()>,
{
    let Some(table) = query.selection.tables.get(position) else {
        return if expect_bool(query.condition.evaluate(prefix)?)? == Scalar::Bool(true) {
            visitor(RowRef {
                facts: prefix,
                selection: &query.selection,
            })
        } else {
            Ok(())
        };
    };
    let entries = &query.document.entries[&table.name];
    let candidates = query.indexes.get(&position).map_or_else(
        || entries.as_slice(),
        |index| {
            index
                .buckets
                .get(&prefix[index.earlier].values[index.other])
                .map_or(&[], Vec::as_slice)
        },
    );
    for candidate in candidates {
        prefix.push(candidate.clone());
        enumerate(query, position + 1, prefix, visitor)?;
        prefix.pop();
    }
    Ok(())
}

fn get<'a, T: 'static>(
    facts: &'a [Rc<Fact>],
    selection: &Selection,
    position: usize,
    attribute: &Attribute<T>,
) -> Result<&'a T> {
    let table = selection
        .tables
        .get(position)
        .ok_or_else(|| Error::Query(format!("invalid row position {position}")))?;
    if table.name != attribute.name() || table.schema != *attribute.schema() {
        return Err(Error::Query(
            "attribute decoder does not match the selected column".into(),
        ));
    }
    let fact = &facts[position];
    if fact.typed.get().is_none() {
        let value = (table.decode)(&fact.values)?;
        fact.typed
            .set(value)
            .map_err(|_| Error::Query("typed row cache initialization failed".into()))?;
    }
    fact.typed
        .get()
        .and_then(|value| value.downcast_ref::<T>())
        .ok_or_else(|| Error::Query("attribute type mismatch".into()))
}

/// A collected result row.
#[derive(Clone, Debug)]
pub struct Row {
    facts: Vec<Rc<Fact>>,
    selection: Selection,
}
impl Row {
    pub fn get<T: 'static>(&self, position: usize, attribute: &Attribute<T>) -> Result<&T> {
        get(&self.facts, &self.selection, position, attribute)
    }
    pub fn len(&self) -> usize {
        self.facts.len()
    }
    pub fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }
}

/// A zero-copy result row supplied to [`PreparedQuery::for_each`].
#[derive(Clone, Debug)]
pub struct RowRef<'a> {
    facts: &'a [Rc<Fact>],
    selection: &'a Selection,
}
impl RowRef<'_> {
    fn into_owned(self) -> Row {
        Row {
            facts: self.facts.to_vec(),
            selection: self.selection.clone(),
        }
    }
    pub fn get<T: 'static>(&self, position: usize, attribute: &Attribute<T>) -> Result<&T> {
        get(self.facts, self.selection, position, attribute)
    }
    pub fn len(&self) -> usize {
        self.facts.len()
    }
    pub fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }
}
