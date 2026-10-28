//! OCaml-facing OGRE operations. No manually written unsafe FFI is required.
use ogre::{Document, Expr, FieldSpec, Join, Query, Scalar, ScalarType, Schema, Selection, Sexp};
use std::cell::RefCell;
use std::collections::{BTreeMap, LinkedList};
use std::sync::atomic::{AtomicI64, Ordering};

type QueryRows = LinkedList<LinkedList<LinkedList<(String, String)>>>;

#[ocaml::func]
pub fn ogre_rs_parse(input: &str) -> Result<String, String> {
    Document::parse(input)
        .map(|document| document.to_string())
        .map_err(|error| error.to_string())
}
#[ocaml::func]
pub fn ogre_rs_merge(left: &str, right: &str) -> Result<String, String> {
    let left = Document::parse(left).map_err(|error| error.to_string())?;
    let right = Document::parse(right).map_err(|error| error.to_string())?;
    left.merge(&right)
        .map(|document| document.to_string())
        .map_err(|error| error.to_string())
}
#[ocaml::func]
pub fn ogre_rs_json(input: &str) -> Result<String, String> {
    Document::parse(input)
        .and_then(|document| document.to_json())
        .map_err(|error| error.to_string())
}
#[ocaml::func]
pub fn ogre_rs_yaml(input: &str) -> Result<String, String> {
    Document::parse(input)
        .map(|document| document.to_yaml())
        .map_err(|error| error.to_string())
}

thread_local! {
    static DOCUMENTS: RefCell<BTreeMap<i64, Document>> = const { RefCell::new(BTreeMap::new()) };
}
fn next_id() -> i64 {
    static IDS: AtomicI64 = AtomicI64::new(0);
    IDS.fetch_add(1, Ordering::Relaxed) + 1
}
fn insert(document: Document) -> i64 {
    let id = next_id();
    DOCUMENTS.with(|documents| {
        documents.borrow_mut().insert(id, document);
    });
    id
}
fn with<T>(id: i64, operation: impl FnOnce(&Document) -> Result<T, String>) -> Result<T, String> {
    DOCUMENTS.with(|documents| {
        let documents = documents.borrow();
        let document = documents
            .get(&id)
            .ok_or_else(|| format!("invalid OGRE document handle {id}"))?;
        operation(document)
    })
}
fn update(
    id: i64,
    operation: impl FnOnce(Document) -> Result<Document, String>,
) -> Result<i64, String> {
    DOCUMENTS.with(|documents| {
        let old = documents
            .borrow()
            .get(&id)
            .cloned()
            .ok_or_else(|| format!("invalid OGRE document handle {id}"))?;
        operation(old).map(insert)
    })
}
fn error(error: ogre::Error) -> String {
    error.to_string()
}

#[ocaml::func]
pub fn ogre_rs_doc_empty() -> i64 {
    insert(Document::new())
}
#[ocaml::func]
pub fn ogre_rs_doc_from_string(input: &str) -> Result<i64, String> {
    Document::parse(input).map(insert).map_err(error)
}
#[ocaml::func]
pub fn ogre_rs_doc_to_string(id: i64) -> Result<String, String> {
    with(id, |document| Ok(document.to_string()))
}
#[ocaml::func]
pub fn ogre_rs_doc_yaml(id: i64) -> Result<String, String> {
    with(id, |document| Ok(document.to_yaml()))
}
#[ocaml::func]
pub fn ogre_rs_doc_json(id: i64) -> Result<String, String> {
    with(id, |document| document.to_json().map_err(error))
}
#[ocaml::func]
pub fn ogre_rs_doc_merge(left: i64, right: i64) -> Result<i64, String> {
    let (left, right) = DOCUMENTS.with(|documents| {
        let documents = documents.borrow();
        let left = documents
            .get(&left)
            .cloned()
            .ok_or_else(|| "invalid left document".to_string())?;
        let right = documents
            .get(&right)
            .cloned()
            .ok_or_else(|| "invalid right document".to_string())?;
        Ok::<_, String>((left, right))
    })?;
    left.merge(&right).map(insert).map_err(error)
}
#[ocaml::func]
pub fn ogre_rs_doc_clear(id: i64) -> Result<i64, String> {
    update(id, |mut document| {
        document.clear();
        Ok(document)
    })
}
#[ocaml::func]
pub fn ogre_rs_doc_counts(id: i64) -> Result<(isize, isize), String> {
    with(id, |document| {
        Ok((
            document.declarations() as isize,
            document.definitions() as isize,
        ))
    })
}

fn kind(name: &str) -> Result<ScalarType, String> {
    match name {
        "int" | "Int" => Ok(ScalarType::Int),
        "str" | "Str" => Ok(ScalarType::Str),
        "bool" | "Bool" => Ok(ScalarType::Bool),
        "float" | "Float" => Ok(ScalarType::Float),
        _ => Err(format!("unknown OGRE scalar type {name}")),
    }
}
fn schema(fields: &LinkedList<(String, String)>) -> Result<Schema, String> {
    fields
        .iter()
        .map(|(name, kind_name)| {
            kind(kind_name).map(|kind| FieldSpec {
                name: name.clone(),
                kind,
            })
        })
        .collect::<Result<Vec<_>, _>>()
        .map(Schema::new)
}
#[ocaml::func]
pub fn ogre_rs_doc_declare(
    id: i64,
    name: &str,
    fields: LinkedList<(String, String)>,
) -> Result<i64, String> {
    let schema = schema(&fields)?;
    update(id, |mut document| {
        document.declare(name, schema).map_err(error)?;
        Ok(document)
    })
}

#[ocaml::func]
pub fn ogre_rs_doc_put(
    id: i64,
    name: &str,
    signature: LinkedList<(String, String)>,
    fields: LinkedList<(String, String)>,
) -> Result<i64, String> {
    let schema = schema(&signature)?;
    let provided: BTreeMap<String, String> = fields.into_iter().collect();
    let values = schema
        .fields()
        .iter()
        .map(|field| {
            provided
                .get(&field.name)
                .ok_or_else(|| format!("missing field {name}.{}", field.name))
                .and_then(|value| field.kind.parse(value).map_err(error))
        })
        .collect::<Result<Vec<_>, _>>()?;
    update(id, |mut document| {
        document
            .insert_scalars(name, schema, values)
            .map_err(error)?;
        Ok(document)
    })
}

#[ocaml::func]
pub fn ogre_rs_doc_entries(
    id: i64,
    name: &str,
) -> Result<LinkedList<LinkedList<(String, String)>>, String> {
    with(id, |document| {
        let schema = document.schema(name).cloned().unwrap_or_default();
        Ok(document
            .values(name)
            .into_iter()
            .map(|values| {
                schema
                    .fields()
                    .iter()
                    .zip(values)
                    .map(|(field, value)| (field.name.clone(), value.atom()))
                    .collect()
            })
            .collect())
    })
}

type JoinVar = (Option<String>, i64, String, String);
fn field_ref(
    attribute: Option<String>,
    position: i64,
    name: String,
    kind_name: String,
) -> Result<(Option<String>, Option<usize>, FieldSpec), String> {
    let position = if position < 0 {
        None
    } else {
        Some(position as usize)
    };
    let field = FieldSpec {
        name,
        kind: kind(&kind_name)?,
    };
    Ok((attribute, position, field))
}
fn parse_expr(expression: &Sexp) -> Result<Expr, String> {
    match expression {
        Sexp::Atom(value) if value == "True" => Ok(Expr::bool(true)),
        Sexp::List(values) if values.len() == 2 && values[0].atom() == Some("Int") => {
            let value = values[1]
                .atom()
                .ok_or_else(|| "expected an integer".to_string())?;
            value
                .parse()
                .map(Expr::int)
                .map_err(|_| "invalid integer expression".to_string())
        }
        Sexp::List(values) if values.len() == 2 && values[0].atom() == Some("Str") => values[1]
            .atom()
            .map(Expr::str)
            .ok_or_else(|| "expected a string".to_string()),
        Sexp::List(values) if values.len() == 2 && values[0].atom() == Some("Flt") => {
            let value = values[1]
                .atom()
                .ok_or_else(|| "expected a float".to_string())?;
            ScalarType::Float
                .parse(value)
                .map(Expr::Value)
                .map_err(error)
        }
        Sexp::List(values) if values.len() == 2 && values[0].atom() == Some("Var") => {
            let (attribute, position, field) = parse_column(&values[1])?;
            Ok(Expr::dynamic(attribute, position, field))
        }
        Sexp::List(values) if values.len() == 3 && values[0].atom() == Some("Uop") => {
            if values[1].atom() != Some("Not") {
                return Err("unknown unary operator".into());
            }
            Ok(parse_expr(&values[2])?.not())
        }
        Sexp::List(values) if values.len() == 4 && values[0].atom() == Some("Bop") => {
            let operator = values[1]
                .atom()
                .ok_or_else(|| "expected an operator".to_string())?;
            let left = parse_expr(&values[2])?;
            let right = parse_expr(&values[3])?;
            match operator {
                "And" => Ok(left.and(right)),
                "Or" => Ok(left.or(right)),
                "Eq" => Ok(left.eq(right)),
                "Lt" => Ok(left.lt(right)),
                "Add" => Ok(left + right),
                "Sub" => Ok(left - right),
                _ => Err(format!("unknown binary operator {operator}")),
            }
        }
        _ => Err(format!("unsupported expression {expression}")),
    }
}
fn parse_column(expression: &Sexp) -> Result<(Option<String>, Option<usize>, FieldSpec), String> {
    let fields = expression
        .list()
        .ok_or_else(|| "expected a column".to_string())?;
    let mut attribute = None;
    let mut position = None;
    let mut field = None;
    for entry in fields {
        let pair = entry
            .list()
            .ok_or_else(|| "expected a column field".to_string())?;
        if pair.len() != 2 {
            return Err("invalid column field".into());
        }
        match pair[0].atom() {
            Some("attr") => match &pair[1] {
                Sexp::Atom(value) => position = value.parse().ok(),
                Sexp::List(name) => {
                    if name.len() != 2 {
                        return Err("invalid attribute position".into());
                    }
                    match name[0].atom() {
                        Some("Name") => attribute = name[1].atom().map(str::to_owned),
                        Some("Pos") => {
                            position = name[1].atom().and_then(|value| value.parse().ok())
                        }
                        _ => return Err("invalid attribute reference".into()),
                    }
                }
            },
            Some("field") => {
                let header = pair[1]
                    .list()
                    .ok_or_else(|| "expected a field header".to_string())?;
                let mut name = None;
                let mut kind_name = None;
                for part in header {
                    let pair = part
                        .list()
                        .ok_or_else(|| "expected a field header entry".to_string())?;
                    if pair.len() != 2 {
                        return Err("invalid field header".into());
                    }
                    match pair[0].atom() {
                        Some("fname") => name = pair[1].atom().map(str::to_owned),
                        Some("ftype") => kind_name = pair[1].atom().map(str::to_owned),
                        _ => {}
                    }
                }
                field = Some(FieldSpec {
                    name: name.ok_or_else(|| "missing field name".to_string())?,
                    kind: kind(&kind_name.ok_or_else(|| "missing field type".to_string())?)?,
                });
            }
            _ => {}
        }
    }
    Ok((
        attribute,
        position,
        field.ok_or_else(|| "missing column field".to_string())?,
    ))
}

#[ocaml::func]
pub fn ogre_rs_doc_query(
    id: i64,
    names: LinkedList<String>,
    joins: LinkedList<LinkedList<JoinVar>>,
    where_expression: &str,
) -> Result<QueryRows, String> {
    let expression =
        Sexp::parse(where_expression).map_err(|error| ogre::Error::from(error).to_string())?;
    let condition = parse_expr(&expression)?;
    with(id, |document| {
        let mut selection: Option<Selection> = None;
        for name in &names {
            let schema = document.schema(name).cloned().unwrap_or_default();
            let attribute = ogre::Attribute::new(
                name.clone(),
                schema,
                |values: &Vec<Scalar>| Ok(values.clone()),
                |values| Ok(values.to_vec()),
            );
            selection = Some(match selection {
                None => Selection::one(&attribute),
                Some(selection) => selection.and(&attribute),
            });
        }
        let mut query = Query::new(selection.unwrap_or_default()).where_expr(condition);
        let mut query_joins = Vec::new();
        for class in joins {
            let mut fields = Vec::new();
            for (attribute, position, name, kind_name) in class {
                let (attribute, position, field) = field_ref(attribute, position, name, kind_name)?;
                fields.push(Join::dynamic(attribute, position, field));
            }
            query_joins.push(Join::new(fields));
        }
        query = query.join(query_joins);
        let rows = query.execute(document).map_err(error)?;
        rows.into_iter()
            .map(|row| {
                names
                    .iter()
                    .enumerate()
                    .map(|(position, name)| {
                        let attribute = ogre::Attribute::new(
                            name.clone(),
                            document.schema(name).cloned().unwrap_or_default(),
                            |values: &Vec<Scalar>| Ok(values.clone()),
                            |values| Ok(values.to_vec()),
                        );
                        row.get::<Vec<Scalar>>(position, &attribute)
                            .map(|values| {
                                attribute
                                    .schema()
                                    .fields()
                                    .iter()
                                    .zip(values)
                                    .map(|(field, value)| (field.name.clone(), value.atom()))
                                    .collect()
                            })
                            .map_err(error)
                    })
                    .collect()
            })
            .collect()
    })
}
