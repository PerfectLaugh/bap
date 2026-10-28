#![forbid(unsafe_code)]

use std::fmt;

#[derive(Debug)]
pub enum Error {
    Parse { offset: usize, message: String },
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse { offset, message } => {
                write!(f, "S-expression parse error at byte {offset}: {message}")
            }
        }
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

impl Sexp {
    pub fn parse_all(input: &str) -> Result<Vec<Self>> {
        let mut parser = Parser {
            input: input.as_bytes(),
            position: 0,
        };
        let mut result = Vec::new();
        parser.space();
        while parser.position < parser.input.len() {
            result.push(parser.value()?);
            parser.space();
        }
        Ok(result)
    }

    pub fn parse(input: &str) -> Result<Self> {
        let mut values = Self::parse_all(input)?;
        if values.len() == 1 {
            Ok(values.remove(0))
        } else {
            Err(Error::Parse {
                offset: 0,
                message: "expected exactly one S-expression".into(),
            })
        }
    }

    pub fn atom(&self) -> Option<&str> {
        if let Self::Atom(value) = self {
            Some(value)
        } else {
            None
        }
    }
    pub fn list(&self) -> Option<&[Self]> {
        if let Self::List(values) = self {
            Some(values)
        } else {
            None
        }
    }
}

impl fmt::Display for Sexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Atom(value) => f.write_str(&quote(value)),
            Self::List(values) => {
                f.write_str("(")?;
                for (index, value) in values.iter().enumerate() {
                    if index != 0 {
                        f.write_str(" ")?;
                    }
                    value.fmt(f)?;
                }
                f.write_str(")")
            }
        }
    }
}

fn quote(value: &str) -> String {
    if !value.is_empty()
        && value
            .bytes()
            .all(|x| x.is_ascii_alphanumeric() || b"._-+*/%<>!=?:@#$^&|~[]{}".contains(&x))
    {
        return value.into();
    }
    let mut result = String::from("\"");
    for c in value.chars() {
        match c {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            c if c.is_control() => result.push_str(&format!("\\{:03}", c as u32)),
            c => result.push(c),
        }
    }
    result.push('"');
    result
}

struct Parser<'a> {
    input: &'a [u8],
    position: usize,
}
impl Parser<'_> {
    fn error(&self, message: impl Into<String>) -> Error {
        Error::Parse {
            offset: self.position,
            message: message.into(),
        }
    }
    fn space(&mut self) {
        loop {
            while self
                .input
                .get(self.position)
                .is_some_and(u8::is_ascii_whitespace)
            {
                self.position += 1;
            }
            if self.input.get(self.position) == Some(&b';') {
                while self.input.get(self.position).is_some_and(|x| *x != b'\n') {
                    self.position += 1;
                }
            } else {
                break;
            }
        }
    }
    fn value(&mut self) -> Result<Sexp> {
        self.space();
        match self.input.get(self.position) {
            Some(b'(') => {
                self.position += 1;
                let mut values = Vec::new();
                loop {
                    self.space();
                    if self.input.get(self.position) == Some(&b')') {
                        self.position += 1;
                        return Ok(Sexp::List(values));
                    }
                    if self.position == self.input.len() {
                        return Err(self.error("unclosed list"));
                    }
                    values.push(self.value()?);
                }
            }
            Some(b'"') => self.quoted().map(Sexp::Atom),
            Some(b')') => Err(self.error("unexpected closing parenthesis")),
            Some(_) => self.bare().map(Sexp::Atom),
            None => Err(self.error("expected a value")),
        }
    }
    fn quoted(&mut self) -> Result<String> {
        self.position += 1;
        let mut output = String::new();
        loop {
            let byte = *self
                .input
                .get(self.position)
                .ok_or_else(|| self.error("unclosed quoted atom"))?;
            self.position += 1;
            match byte {
                b'"' => return Ok(output),
                b'\\' => {
                    let escaped = *self
                        .input
                        .get(self.position)
                        .ok_or_else(|| self.error("trailing escape"))?;
                    self.position += 1;
                    match escaped {
                        b'n' => output.push('\n'),
                        b'r' => output.push('\r'),
                        b't' => output.push('\t'),
                        b'x' => {
                            let digits = self
                                .input
                                .get(self.position..self.position + 2)
                                .ok_or_else(|| self.error("short hex escape"))?;
                            let digits = std::str::from_utf8(digits)
                                .map_err(|_| self.error("invalid hex escape"))?;
                            let byte = u8::from_str_radix(digits, 16)
                                .map_err(|_| self.error("invalid hex escape"))?;
                            self.position += 2;
                            output.push(byte as char);
                        }
                        b'0'..=b'9' => {
                            let digits = self
                                .input
                                .get(self.position - 1..self.position + 2)
                                .ok_or_else(|| self.error("short decimal escape"))?;
                            let digits = std::str::from_utf8(digits)
                                .map_err(|_| self.error("invalid decimal escape"))?;
                            let byte: u8 = digits
                                .parse()
                                .map_err(|_| self.error("invalid decimal escape"))?;
                            self.position += 2;
                            output.push(byte as char);
                        }
                        b'\n' => {}
                        other => output.push(other as char),
                    }
                }
                byte if byte.is_ascii() => output.push(byte as char),
                _ => {
                    let remaining = std::str::from_utf8(&self.input[self.position - 1..])
                        .map_err(|_| self.error("invalid UTF-8"))?;
                    let c = remaining.chars().next().expect("nonempty");
                    self.position += c.len_utf8() - 1;
                    output.push(c);
                }
            }
        }
    }
    fn bare(&mut self) -> Result<String> {
        let start = self.position;
        while self
            .input
            .get(self.position)
            .is_some_and(|x| !x.is_ascii_whitespace() && !matches!(x, b'(' | b')' | b';' | b'"'))
        {
            self.position += 1;
        }
        if self.position == start {
            return Err(self.error("expected an atom"));
        }
        String::from_utf8(self.input[start..self.position].to_vec())
            .map_err(|_| self.error("atom is not UTF-8"))
    }
}
