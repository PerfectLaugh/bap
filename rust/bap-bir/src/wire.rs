use crate::{
    Arg, Bil, BinOp, Blk, Cast, Def, Endian, Exp, Jmp, JmpKind, Label, Phi, Stmt, Sub, Type, UnOp,
    Var,
};
use bap_bitvec::BitVec;
use bap_sexp::Sexp;
use num_bigint::BigUint;
use num_traits::Num;
use std::collections::BTreeSet;

pub type Result<T> = std::result::Result<T, String>;

fn list(sexp: &Sexp) -> Result<&[Sexp]> {
    sexp.list()
        .ok_or_else(|| format!("expected a list, got {sexp}"))
}
fn atom(sexp: &Sexp) -> Result<&str> {
    sexp.atom()
        .ok_or_else(|| format!("expected an atom, got {sexp}"))
}
fn uint(sexp: &Sexp) -> Result<u64> {
    atom(sexp)?
        .parse()
        .map_err(|_| format!("expected an integer, got {sexp}"))
}
fn u32_value(sexp: &Sexp) -> Result<u32> {
    u32::try_from(uint(sexp)?).map_err(|_| "integer is out of range".into())
}
fn usize_value(sexp: &Sexp) -> Result<usize> {
    usize::try_from(uint(sexp)?).map_err(|_| "integer is out of range".into())
}
fn tagged<'a>(sexp: &'a Sexp, tag: &str, arity: usize) -> Result<&'a [Sexp]> {
    let values = list(sexp)?;
    if values.len() != arity + 1 || values.first().and_then(Sexp::atom) != Some(tag) {
        return Err(format!(
            "expected ({tag} ...) with arity {arity}, got {sexp}"
        ));
    }
    Ok(&values[1..])
}
fn sexp(values: Vec<Sexp>) -> Sexp {
    Sexp::List(values)
}
fn atom_sexp(value: impl Into<String>) -> Sexp {
    Sexp::Atom(value.into())
}
fn tagged_sexp(tag: &str, values: Vec<Sexp>) -> Sexp {
    let mut result = vec![atom_sexp(tag)];
    result.extend(values);
    sexp(result)
}

pub fn parse_type(input: &Sexp) -> Result<Type> {
    if atom(input) == Ok("unk") {
        return Ok(Type::Unknown);
    }
    if atom(input) == Ok("unit") {
        return Ok(Type::Unit);
    }
    if let Ok(values) = tagged(input, "imm", 1) {
        return Ok(Type::Int(u32_value(&values[0])?));
    }
    let values = tagged(input, "mem", 2)?;
    Ok(Type::Mem {
        address: u32_value(&values[0])?,
        value: u32_value(&values[1])?,
    })
}
fn print_type(typ: &Type) -> Sexp {
    match typ {
        Type::Unknown => atom_sexp("unk"),
        Type::Unit => atom_sexp("unit"),
        Type::Int(width) => tagged_sexp("imm", vec![atom_sexp(width.to_string())]),
        Type::Mem { address, value } => tagged_sexp(
            "mem",
            vec![atom_sexp(address.to_string()), atom_sexp(value.to_string())],
        ),
    }
}

pub fn parse_var(input: &Sexp) -> Result<Var> {
    let values = tagged(input, "var", 4)?;
    Ok(Var {
        name: uint(&values[0])?.to_string(),
        index: match usize_value(&values[1])? {
            0 => None,
            index => Some(index),
        },
        typ: parse_type(&values[2])?,
        is_virtual: match atom(&values[3])? {
            "1" => true,
            "0" => false,
            _ => return Err("invalid virtual flag".into()),
        },
    })
}
pub fn print_var(var: &Var) -> Sexp {
    tagged_sexp(
        "var",
        vec![
            atom_sexp(&var.name),
            atom_sexp(var.index.unwrap_or(0).to_string()),
            print_type(&var.typ),
            atom_sexp(if var.is_virtual { "1" } else { "0" }),
        ],
    )
}

pub fn parse_vars(input: &str) -> Result<BTreeSet<Var>> {
    let sexp = Sexp::parse(input).map_err(|error| error.to_string())?;
    tagged(&sexp, "vars", 1)?
        .first()
        .ok_or_else(|| "missing variables".into())
        .and_then(|values| list(values)?.iter().map(parse_var).collect())
}

pub fn print_vars(vars: &BTreeSet<Var>) -> Sexp {
    tagged_sexp("vars", vec![sexp(vars.iter().map(print_var).collect())])
}

fn parse_endian(input: &Sexp) -> Result<Endian> {
    match atom(input)? {
        "el" => Ok(Endian::Little),
        "be" => Ok(Endian::Big),
        _ => Err("invalid endian".into()),
    }
}
fn print_endian(endian: Endian) -> Sexp {
    atom_sexp(match endian {
        Endian::Little => "el",
        Endian::Big => "be",
    })
}
fn parse_cast(input: &Sexp) -> Result<Cast> {
    match atom(input)? {
        "LOW" => Ok(Cast::Low),
        "HIGH" => Ok(Cast::High),
        "SIGNED" => Ok(Cast::Signed),
        "UNSIGNED" => Ok(Cast::Unsigned),
        _ => Err("invalid cast".into()),
    }
}
fn print_cast(cast: Cast) -> Sexp {
    atom_sexp(match cast {
        Cast::Low => "LOW",
        Cast::High => "HIGH",
        Cast::Signed => "SIGNED",
        Cast::Unsigned => "UNSIGNED",
    })
}
fn parse_unop(input: &Sexp) -> Result<UnOp> {
    match atom(input)? {
        "NEG" => Ok(UnOp::Neg),
        "NOT" => Ok(UnOp::Not),
        _ => Err("invalid unop".into()),
    }
}
fn print_unop(op: UnOp) -> Sexp {
    atom_sexp(if op == UnOp::Neg { "NEG" } else { "NOT" })
}

const BINOPS: &[(BinOp, &str)] = &[
    (BinOp::Add, "PLUS"),
    (BinOp::Sub, "MINUS"),
    (BinOp::Mul, "TIMES"),
    (BinOp::Div, "DIVIDE"),
    (BinOp::SDiv, "SDIVIDE"),
    (BinOp::Rem, "MOD"),
    (BinOp::SRem, "SREM"),
    (BinOp::Mod, "SMOD"),
    (BinOp::LShift, "LSHIFT"),
    (BinOp::RShift, "RSHIFT"),
    (BinOp::AShift, "ARSHIFT"),
    (BinOp::And, "AND"),
    (BinOp::Or, "OR"),
    (BinOp::Xor, "XOR"),
    (BinOp::Eq, "EQ"),
    (BinOp::Neq, "NEQ"),
    (BinOp::Lt, "LT"),
    (BinOp::Le, "LE"),
    (BinOp::Gt, "GT"),
    (BinOp::Ge, "GE"),
    (BinOp::SLt, "SLT"),
    (BinOp::SLe, "SLE"),
    (BinOp::SGt, "SGT"),
    (BinOp::SGe, "SGE"),
];
fn parse_binop(input: &Sexp) -> Result<BinOp> {
    let name = atom(input)?;
    BINOPS
        .iter()
        .find_map(|(op, candidate)| (*candidate == name).then_some(*op))
        .ok_or_else(|| format!("invalid binop {name}"))
}
fn print_binop(op: BinOp) -> Sexp {
    atom_sexp(
        BINOPS
            .iter()
            .find_map(|(candidate, name)| (*candidate == op).then_some(*name))
            .expect("binop name"),
    )
}

pub fn parse_exp(input: &Sexp) -> Result<Exp> {
    if let Ok(values) = tagged(input, "int", 2) {
        let width = u32_value(&values[0])?;
        let value =
            BigUint::from_str_radix(atom(&values[1])?, 16).map_err(|error| error.to_string())?;
        return Ok(Exp::Int(BitVec::new(width, value)));
    }
    if tagged(input, "var", 4).is_ok() {
        return Ok(Exp::Var(parse_var(input)?));
    }
    if let Ok(values) = tagged(input, "load", 4) {
        return Ok(Exp::load(
            parse_exp(&values[0])?,
            parse_exp(&values[1])?,
            parse_endian(&values[2])?,
            u32_value(&values[3])?,
        ));
    }
    if let Ok(values) = tagged(input, "store", 5) {
        return Ok(Exp::store(
            parse_exp(&values[0])?,
            parse_exp(&values[1])?,
            parse_exp(&values[2])?,
            parse_endian(&values[3])?,
            u32_value(&values[4])?,
        ));
    }
    if let Ok(values) = tagged(input, "binop", 3) {
        return Ok(Exp::bin(
            parse_binop(&values[0])?,
            parse_exp(&values[1])?,
            parse_exp(&values[2])?,
        ));
    }
    if let Ok(values) = tagged(input, "unop", 2) {
        return Ok(Exp::un(parse_unop(&values[0])?, parse_exp(&values[1])?));
    }
    if let Ok(values) = tagged(input, "cast", 3) {
        return Ok(Exp::cast(
            parse_cast(&values[0])?,
            u32_value(&values[1])?,
            parse_exp(&values[2])?,
        ));
    }
    if let Ok(values) = tagged(input, "let", 3) {
        return Ok(Exp::Let {
            var: parse_var(&values[0])?,
            value: Box::new(parse_exp(&values[1])?),
            body: Box::new(parse_exp(&values[2])?),
        });
    }
    if let Ok(values) = tagged(input, "ite", 3) {
        return Ok(Exp::ite(
            parse_exp(&values[0])?,
            parse_exp(&values[1])?,
            parse_exp(&values[2])?,
        ));
    }
    if let Ok(values) = tagged(input, "extract", 3) {
        return Ok(Exp::extract(
            u32_value(&values[0])?,
            u32_value(&values[1])?,
            parse_exp(&values[2])?,
        ));
    }
    if let Ok(values) = tagged(input, "concat", 2) {
        return Ok(Exp::concat(parse_exp(&values[0])?, parse_exp(&values[1])?));
    }
    let values = tagged(input, "unknown", 2)?;
    Ok(Exp::Unknown(
        atom(&values[0])?.into(),
        parse_type(&values[1])?,
    ))
}
pub fn print_exp(exp: &Exp) -> Sexp {
    match exp {
        Exp::Int(value) => tagged_sexp(
            "int",
            vec![
                atom_sexp(value.width().to_string()),
                atom_sexp(value.value().to_str_radix(16)),
            ],
        ),
        Exp::Var(var) => print_var(var),
        Exp::Load {
            memory,
            address,
            endian,
            size,
        } => tagged_sexp(
            "load",
            vec![
                print_exp(memory),
                print_exp(address),
                print_endian(*endian),
                atom_sexp(size.to_string()),
            ],
        ),
        Exp::Store {
            memory,
            address,
            value,
            endian,
            size,
        } => tagged_sexp(
            "store",
            vec![
                print_exp(memory),
                print_exp(address),
                print_exp(value),
                print_endian(*endian),
                atom_sexp(size.to_string()),
            ],
        ),
        Exp::Bin { op, left, right } => tagged_sexp(
            "binop",
            vec![print_binop(*op), print_exp(left), print_exp(right)],
        ),
        Exp::Un { op, value } => tagged_sexp("unop", vec![print_unop(*op), print_exp(value)]),
        Exp::Cast { kind, size, value } => tagged_sexp(
            "cast",
            vec![
                print_cast(*kind),
                atom_sexp(size.to_string()),
                print_exp(value),
            ],
        ),
        Exp::Let { var, value, body } => tagged_sexp(
            "let",
            vec![print_var(var), print_exp(value), print_exp(body)],
        ),
        Exp::Ite { condition, yes, no } => tagged_sexp(
            "ite",
            vec![print_exp(condition), print_exp(yes), print_exp(no)],
        ),
        Exp::Extract { high, low, value } => tagged_sexp(
            "extract",
            vec![
                atom_sexp(high.to_string()),
                atom_sexp(low.to_string()),
                print_exp(value),
            ],
        ),
        Exp::Concat { left, right } => {
            tagged_sexp("concat", vec![print_exp(left), print_exp(right)])
        }
        Exp::Unknown(message, typ) => {
            tagged_sexp("unknown", vec![atom_sexp(message), print_type(typ)])
        }
    }
}

pub fn parse_stmt(input: &Sexp) -> Result<Stmt> {
    if let Ok(values) = tagged(input, "move", 2) {
        return Ok(Stmt::Move {
            var: parse_var(&values[0])?,
            value: parse_exp(&values[1])?,
        });
    }
    if let Ok(values) = tagged(input, "jmp", 1) {
        return Ok(Stmt::Jmp(parse_exp(&values[0])?));
    }
    if let Ok(values) = tagged(input, "special", 1) {
        return Ok(Stmt::Special(atom(&values[0])?.into()));
    }
    if let Ok(values) = tagged(input, "while", 2) {
        return Ok(Stmt::While {
            condition: parse_exp(&values[0])?,
            body: parse_stmts(&values[1])?,
        });
    }
    if let Ok(values) = tagged(input, "if", 3) {
        return Ok(Stmt::If {
            condition: parse_exp(&values[0])?,
            yes: parse_stmts(&values[1])?,
            no: parse_stmts(&values[2])?,
        });
    }
    let values = tagged(input, "cpuexn", 1)?;
    Ok(Stmt::CpuExn(u32_value(&values[0])?))
}
fn print_stmt(stmt: &Stmt) -> Sexp {
    match stmt {
        Stmt::Move { var, value } => tagged_sexp("move", vec![print_var(var), print_exp(value)]),
        Stmt::Jmp(target) => tagged_sexp("jmp", vec![print_exp(target)]),
        Stmt::Special(message) => tagged_sexp("special", vec![atom_sexp(message)]),
        Stmt::While { condition, body } => {
            tagged_sexp("while", vec![print_exp(condition), print_stmts(body)])
        }
        Stmt::If { condition, yes, no } => tagged_sexp(
            "if",
            vec![print_exp(condition), print_stmts(yes), print_stmts(no)],
        ),
        Stmt::CpuExn(number) => tagged_sexp("cpuexn", vec![atom_sexp(number.to_string())]),
    }
}
fn parse_stmts(input: &Sexp) -> Result<Bil> {
    list(input)?.iter().map(parse_stmt).collect()
}
fn print_stmts(bil: &Bil) -> Sexp {
    sexp(bil.iter().map(print_stmt).collect())
}

pub fn parse_bil(input: &str) -> Result<Bil> {
    let sexp = Sexp::parse(input).map_err(|error| error.to_string())?;
    tagged(&sexp, "bil", 1).and_then(|values| parse_stmts(&values[0]))
}
pub fn print_bil(bil: &Bil) -> String {
    tagged_sexp("bil", vec![print_stmts(bil)]).to_string()
}

fn parse_def_with_tag(input: &Sexp, tag: &str) -> Result<Def> {
    let values = tagged(input, tag, 3)?;
    Ok(Def {
        tid: uint(&values[0])?,
        var: parse_var(&values[1])?,
        rhs: parse_exp(&values[2])?,
    })
}
fn print_def_with_tag(def: &Def, tag: &str) -> Sexp {
    tagged_sexp(
        tag,
        vec![
            atom_sexp(def.tid.to_string()),
            print_var(&def.var),
            print_exp(&def.rhs),
        ],
    )
}
fn parse_phi(input: &Sexp) -> Result<Phi> {
    let values = tagged(input, "phi", 3)?;
    let values_in = list(&values[2])?
        .iter()
        .map(|value| {
            let pair = list(value)?;
            if pair.len() != 2 {
                return Err("invalid phi input".into());
            }
            Ok((uint(&pair[0])?, parse_exp(&pair[1])?))
        })
        .collect::<Result<_>>()?;
    Ok(Phi {
        tid: uint(&values[0])?,
        var: parse_var(&values[1])?,
        values: values_in,
    })
}
fn print_phi(phi: &Phi) -> Sexp {
    tagged_sexp(
        "phi",
        vec![
            atom_sexp(phi.tid.to_string()),
            print_var(&phi.var),
            sexp(
                phi.values
                    .iter()
                    .map(|(tid, exp)| sexp(vec![atom_sexp(tid.to_string()), print_exp(exp)]))
                    .collect(),
            ),
        ],
    )
}
fn parse_label(input: &Sexp) -> Result<Label> {
    if let Ok(values) = tagged(input, "direct", 1) {
        return Ok(Label::Direct(uint(&values[0])?));
    }
    let values = tagged(input, "indirect", 1)?;
    Ok(Label::Indirect(parse_exp(&values[0])?))
}
fn print_label(label: &Label) -> Sexp {
    match label {
        Label::Direct(tid) => tagged_sexp("direct", vec![atom_sexp(tid.to_string())]),
        Label::Indirect(exp) => tagged_sexp("indirect", vec![print_exp(exp)]),
    }
}
fn parse_optional_label(input: &Sexp) -> Result<Option<Label>> {
    if atom(input) == Ok("none") {
        return Ok(None);
    }
    tagged(input, "some", 1).and_then(|values| parse_label(&values[0]).map(Some))
}
fn print_optional_label(label: &Option<Label>) -> Sexp {
    label.as_ref().map_or_else(
        || atom_sexp("none"),
        |label| tagged_sexp("some", vec![print_label(label)]),
    )
}
fn parse_jmp(input: &Sexp) -> Result<Jmp> {
    let values = tagged(input, "jmp", 3)?;
    let condition = if atom(&values[1]) == Ok("none") {
        None
    } else {
        Some(parse_exp(&tagged(&values[1], "some", 1)?[0])?)
    };
    let kind_values = list(&values[2])?;
    let kind = match kind_values.first().and_then(Sexp::atom) {
        Some("goto") => JmpKind::Goto(parse_label(&kind_values[1])?),
        Some("ret") => JmpKind::Return(parse_label(&kind_values[1])?),
        Some("call") => JmpKind::Call {
            target: parse_label(&kind_values[1])?,
            return_to: parse_optional_label(&kind_values[2])?,
        },
        Some("int") => JmpKind::Interrupt {
            number: u32_value(&kind_values[1])?,
            return_to: uint(&kind_values[2])?,
        },
        _ => return Err("invalid jump kind".into()),
    };
    Ok(Jmp {
        tid: uint(&values[0])?,
        condition,
        kind,
    })
}
fn print_jmp(jmp: &Jmp) -> Sexp {
    let condition = jmp.condition.as_ref().map_or_else(
        || atom_sexp("none"),
        |exp| tagged_sexp("some", vec![print_exp(exp)]),
    );
    let kind = match &jmp.kind {
        JmpKind::Goto(label) => tagged_sexp("goto", vec![print_label(label)]),
        JmpKind::Return(label) => tagged_sexp("ret", vec![print_label(label)]),
        JmpKind::Call { target, return_to } => tagged_sexp(
            "call",
            vec![print_label(target), print_optional_label(return_to)],
        ),
        JmpKind::Interrupt { number, return_to } => tagged_sexp(
            "int",
            vec![
                atom_sexp(number.to_string()),
                atom_sexp(return_to.to_string()),
            ],
        ),
    };
    tagged_sexp("jmp", vec![atom_sexp(jmp.tid.to_string()), condition, kind])
}
fn parse_blk(input: &Sexp) -> Result<Blk> {
    let values = tagged(input, "blk", 4)?;
    Ok(Blk {
        tid: uint(&values[0])?,
        phis: list(&values[1])?
            .iter()
            .map(parse_phi)
            .collect::<Result<_>>()?,
        defs: list(&values[2])?
            .iter()
            .map(|value| parse_def_with_tag(value, "def"))
            .collect::<Result<_>>()?,
        jmps: list(&values[3])?
            .iter()
            .map(parse_jmp)
            .collect::<Result<_>>()?,
    })
}
fn print_blk(blk: &Blk) -> Sexp {
    tagged_sexp(
        "blk",
        vec![
            atom_sexp(blk.tid.to_string()),
            sexp(blk.phis.iter().map(print_phi).collect()),
            sexp(
                blk.defs
                    .iter()
                    .map(|def| print_def_with_tag(def, "def"))
                    .collect(),
            ),
            sexp(blk.jmps.iter().map(print_jmp).collect()),
        ],
    )
}
pub fn parse_sub(input: &str) -> Result<Sub> {
    let sexp = Sexp::parse(input).map_err(|error| error.to_string())?;
    let values = tagged(&sexp, "sub", 4)?;
    Ok(Sub {
        tid: uint(&values[0])?,
        name: atom(&values[1])?.into(),
        args: list(&values[2])?
            .iter()
            .map(|value| parse_def_with_tag(value, "arg"))
            .collect::<Result<Vec<Arg>>>()?,
        blks: list(&values[3])?
            .iter()
            .map(parse_blk)
            .collect::<Result<_>>()?,
    })
}
pub fn print_sub(sub: &Sub) -> String {
    tagged_sexp(
        "sub",
        vec![
            atom_sexp(sub.tid.to_string()),
            atom_sexp(&sub.name),
            sexp(
                sub.args
                    .iter()
                    .map(|arg| print_def_with_tag(arg, "arg"))
                    .collect(),
            ),
            sexp(sub.blks.iter().map(print_blk).collect()),
        ],
    )
    .to_string()
}
