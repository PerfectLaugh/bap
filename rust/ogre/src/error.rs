use std::fmt;

#[derive(Debug)]
#[non_exhaustive]
pub enum Error {
    Parse { offset: usize, message: String },
    Schema(String),
    Query(String),
    Ambiguous(String),
    Missing(String),
    Io(std::io::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse { offset, message } => {
                write!(f, "OGRE parse error at byte {offset}: {message}")
            }
            Self::Schema(message) => write!(f, "OGRE schema error: {message}"),
            Self::Query(message) => write!(f, "OGRE query error: {message}"),
            Self::Ambiguous(message) => write!(f, "ambiguous OGRE attribute: {message}"),
            Self::Missing(message) => write!(f, "missing OGRE attribute: {message}"),
            Self::Io(error) => error.fmt(f),
        }
    }
}
impl std::error::Error for Error {}
impl From<bap_sexp::Error> for Error {
    fn from(error: bap_sexp::Error) -> Self {
        match error {
            bap_sexp::Error::Parse { offset, message } => Self::Parse { offset, message },
        }
    }
}
impl From<std::io::Error> for Error {
    fn from(error: std::io::Error) -> Self {
        Self::Io(error)
    }
}
pub type Result<T, E = Error> = std::result::Result<T, E>;
