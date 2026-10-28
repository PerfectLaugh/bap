#![forbid(unsafe_code)]

//! OGRE: a small, self-describing relational document store.
//!
//! Documents use the same S-expression representation as BAP's OCaml OGRE.

mod document;
mod error;
mod query;
mod schema;

pub use bap_sexp::Sexp;
pub use document::Document;
pub use error::{Error, Result};
pub use query::{Expr, Join, PreparedQuery, Query, Row, RowRef, Selection};
pub use schema::{Attribute, Field, FieldSpec, Scalar, ScalarType, Schema};
