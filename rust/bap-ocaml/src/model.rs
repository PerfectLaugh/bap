use bap_bir as bir;
use bap_bitvec::BitVec;
use num_bigint::BigUint;
use ocaml::bigarray::Array1;
use std::collections::LinkedList;

#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub enum WType {
    Unknown,
    Unit,
    Mem(isize, isize),
    Imm(isize),
}
#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub struct WVar {
    pub id: isize,
    pub index: isize,
    pub typ: WType,
    pub is_virtual: bool,
}
#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub enum WEndian {
    Little,
    Big,
}
#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub enum WCast {
    Low,
    High,
    Signed,
    Unsigned,
}
#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub enum WUnOp {
    Neg,
    Not,
}
#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub enum WBinOp {
    Add,
    Sub,
    Mul,
    Div,
    SDiv,
    Rem,
    SRem,
    Mod,
    LShift,
    RShift,
    AShift,
    And,
    Or,
    Xor,
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    SLt,
    SLe,
    SGt,
    SGe,
}
#[derive(Clone, ocaml::ToValue, ocaml::FromValue)]
pub enum WExp {
    Word(isize, Array1<u8>),
    Var(WVar),
    Load(Box<WExp>, Box<WExp>, WEndian, isize),
    Store(Box<WExp>, Box<WExp>, Box<WExp>, WEndian, isize),
    Bin(WBinOp, Box<WExp>, Box<WExp>),
    Un(WUnOp, Box<WExp>),
    Cast(WCast, isize, Box<WExp>),
    Let(WVar, Box<WExp>, Box<WExp>),
    Ite(Box<WExp>, Box<WExp>, Box<WExp>),
    Extract(isize, isize, Box<WExp>),
    Concat(Box<WExp>, Box<WExp>),
    Unknown(String, WType),
}
impl std::fmt::Debug for WExp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("WExp")
    }
}
#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub enum WStmt {
    Move(WVar, WExp),
    Jmp(WExp),
    Special(String),
    While(WExp, LinkedList<WStmt>),
    If(WExp, LinkedList<WStmt>, LinkedList<WStmt>),
    CpuExn(isize),
}
#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub struct WDef {
    pub tid: isize,
    pub var: WVar,
    pub rhs: WExp,
}
#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub struct WPhi {
    pub tid: isize,
    pub var: WVar,
    pub values: LinkedList<(isize, WExp)>,
}
#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub enum WLabel {
    Direct(isize),
    Indirect(WExp),
}
#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub enum WJmpKind {
    Goto(WLabel),
    Call(WLabel, Option<WLabel>),
    Return(WLabel),
    Interrupt(isize, isize),
}
#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub struct WJmp {
    pub tid: isize,
    pub condition: Option<WExp>,
    pub kind: WJmpKind,
}
#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub struct WBlk {
    pub tid: isize,
    pub phis: LinkedList<WPhi>,
    pub defs: LinkedList<WDef>,
    pub jmps: LinkedList<WJmp>,
}
#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub struct WSub {
    pub tid: isize,
    pub name: String,
    pub args: LinkedList<WDef>,
    pub blks: LinkedList<WBlk>,
}
#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub struct WLive {
    pub tid: isize,
    pub ins: LinkedList<WVar>,
    pub outs: LinkedList<WVar>,
}
#[derive(Clone, Debug, ocaml::ToValue, ocaml::FromValue)]
pub struct WEdge {
    pub src: isize,
    pub dst: isize,
    pub label: isize,
}

fn bytes(value: &BitVec) -> Array1<u8> {
    let bytes = if value.is_zero() {
        Vec::new()
    } else {
        value.value().to_bytes_le()
    };
    // SAFETY: the returned Bigarray owns its copied bytes, so it cannot outlive them.
    unsafe { Array1::from_slice(bytes) }
}
fn u32_value(value: isize) -> u32 {
    value as u32
}
fn usize_value(value: isize) -> usize {
    value as usize
}
fn int(value: u32) -> isize {
    value as isize
}

pub fn typ_from_wire(typ: &WType) -> bir::Type {
    match typ {
        WType::Unknown => bir::Type::Unknown,
        WType::Unit => bir::Type::Unit,
        WType::Mem(address, value) => bir::Type::Mem {
            address: u32_value(*address),
            value: u32_value(*value),
        },
        WType::Imm(width) => bir::Type::Int(u32_value(*width)),
    }
}
pub fn typ_to_wire(typ: &bir::Type) -> WType {
    match typ {
        bir::Type::Unknown => WType::Unknown,
        bir::Type::Unit => WType::Unit,
        bir::Type::Mem { address, value } => WType::Mem(int(*address), int(*value)),
        bir::Type::Int(width) => WType::Imm(int(*width)),
    }
}
pub fn var_from_wire(var: &WVar) -> bir::Var {
    bir::Var {
        name: var.id.to_string(),
        typ: typ_from_wire(&var.typ),
        index: match var.index {
            0 => None,
            index => Some(usize_value(index)),
        },
        is_virtual: var.is_virtual,
    }
}
pub fn var_to_wire(var: &bir::Var) -> WVar {
    WVar {
        id: var.name.parse().expect("wire variable ID"),
        index: var.index.unwrap_or(0) as isize,
        typ: typ_to_wire(&var.typ),
        is_virtual: var.is_virtual,
    }
}

pub fn exp_from_wire(exp: &WExp) -> bir::Exp {
    match exp {
        WExp::Word(width, value) => bir::Exp::Int(BitVec::new(
            u32_value(*width),
            BigUint::from_bytes_le(value.data()),
        )),
        WExp::Var(var) => bir::Exp::Var(var_from_wire(var)),
        WExp::Load(memory, address, endian, size) => bir::Exp::load(
            exp_from_wire(memory),
            exp_from_wire(address),
            endian_from_wire(endian),
            u32_value(*size),
        ),
        WExp::Store(memory, address, value, endian, size) => bir::Exp::store(
            exp_from_wire(memory),
            exp_from_wire(address),
            exp_from_wire(value),
            endian_from_wire(endian),
            u32_value(*size),
        ),
        WExp::Bin(op, left, right) => bir::Exp::bin(
            binop_from_wire(op),
            exp_from_wire(left),
            exp_from_wire(right),
        ),
        WExp::Un(op, value) => bir::Exp::un(unop_from_wire(op), exp_from_wire(value)),
        WExp::Cast(kind, size, value) => {
            bir::Exp::cast(cast_from_wire(kind), u32_value(*size), exp_from_wire(value))
        }
        WExp::Let(var, value, body) => bir::Exp::Let {
            var: var_from_wire(var),
            value: Box::new(exp_from_wire(value)),
            body: Box::new(exp_from_wire(body)),
        },
        WExp::Ite(condition, yes, no) => bir::Exp::ite(
            exp_from_wire(condition),
            exp_from_wire(yes),
            exp_from_wire(no),
        ),
        WExp::Extract(high, low, value) => {
            bir::Exp::extract(u32_value(*high), u32_value(*low), exp_from_wire(value))
        }
        WExp::Concat(left, right) => bir::Exp::concat(exp_from_wire(left), exp_from_wire(right)),
        WExp::Unknown(message, typ) => bir::Exp::Unknown(message.clone(), typ_from_wire(typ)),
    }
}
pub fn exp_to_wire(exp: &bir::Exp) -> WExp {
    match exp {
        bir::Exp::Int(value) => WExp::Word(int(value.width()), bytes(value)),
        bir::Exp::Var(var) => WExp::Var(var_to_wire(var)),
        bir::Exp::Load {
            memory,
            address,
            endian,
            size,
        } => WExp::Load(
            Box::new(exp_to_wire(memory)),
            Box::new(exp_to_wire(address)),
            endian_to_wire(*endian),
            int(*size),
        ),
        bir::Exp::Store {
            memory,
            address,
            value,
            endian,
            size,
        } => WExp::Store(
            Box::new(exp_to_wire(memory)),
            Box::new(exp_to_wire(address)),
            Box::new(exp_to_wire(value)),
            endian_to_wire(*endian),
            int(*size),
        ),
        bir::Exp::Bin { op, left, right } => WExp::Bin(
            binop_to_wire(*op),
            Box::new(exp_to_wire(left)),
            Box::new(exp_to_wire(right)),
        ),
        bir::Exp::Un { op, value } => WExp::Un(unop_to_wire(*op), Box::new(exp_to_wire(value))),
        bir::Exp::Cast { kind, size, value } => WExp::Cast(
            cast_to_wire(*kind),
            int(*size),
            Box::new(exp_to_wire(value)),
        ),
        bir::Exp::Let { var, value, body } => WExp::Let(
            var_to_wire(var),
            Box::new(exp_to_wire(value)),
            Box::new(exp_to_wire(body)),
        ),
        bir::Exp::Ite { condition, yes, no } => WExp::Ite(
            Box::new(exp_to_wire(condition)),
            Box::new(exp_to_wire(yes)),
            Box::new(exp_to_wire(no)),
        ),
        bir::Exp::Extract { high, low, value } => {
            WExp::Extract(int(*high), int(*low), Box::new(exp_to_wire(value)))
        }
        bir::Exp::Concat { left, right } => {
            WExp::Concat(Box::new(exp_to_wire(left)), Box::new(exp_to_wire(right)))
        }
        bir::Exp::Unknown(message, typ) => WExp::Unknown(message.clone(), typ_to_wire(typ)),
    }
}

fn endian_from_wire(endian: &WEndian) -> bir::Endian {
    match endian {
        WEndian::Little => bir::Endian::Little,
        WEndian::Big => bir::Endian::Big,
    }
}
fn endian_to_wire(endian: bir::Endian) -> WEndian {
    match endian {
        bir::Endian::Little => WEndian::Little,
        bir::Endian::Big => WEndian::Big,
    }
}
fn cast_from_wire(cast: &WCast) -> bir::Cast {
    match cast {
        WCast::Low => bir::Cast::Low,
        WCast::High => bir::Cast::High,
        WCast::Signed => bir::Cast::Signed,
        WCast::Unsigned => bir::Cast::Unsigned,
    }
}
fn cast_to_wire(cast: bir::Cast) -> WCast {
    match cast {
        bir::Cast::Low => WCast::Low,
        bir::Cast::High => WCast::High,
        bir::Cast::Signed => WCast::Signed,
        bir::Cast::Unsigned => WCast::Unsigned,
    }
}
fn unop_from_wire(op: &WUnOp) -> bir::UnOp {
    match op {
        WUnOp::Neg => bir::UnOp::Neg,
        WUnOp::Not => bir::UnOp::Not,
    }
}
fn unop_to_wire(op: bir::UnOp) -> WUnOp {
    match op {
        bir::UnOp::Neg => WUnOp::Neg,
        bir::UnOp::Not => WUnOp::Not,
    }
}
fn binop_from_wire(op: &WBinOp) -> bir::BinOp {
    match op {
        WBinOp::Add => bir::BinOp::Add,
        WBinOp::Sub => bir::BinOp::Sub,
        WBinOp::Mul => bir::BinOp::Mul,
        WBinOp::Div => bir::BinOp::Div,
        WBinOp::SDiv => bir::BinOp::SDiv,
        WBinOp::Rem => bir::BinOp::Rem,
        WBinOp::SRem => bir::BinOp::SRem,
        WBinOp::Mod => bir::BinOp::Mod,
        WBinOp::LShift => bir::BinOp::LShift,
        WBinOp::RShift => bir::BinOp::RShift,
        WBinOp::AShift => bir::BinOp::AShift,
        WBinOp::And => bir::BinOp::And,
        WBinOp::Or => bir::BinOp::Or,
        WBinOp::Xor => bir::BinOp::Xor,
        WBinOp::Eq => bir::BinOp::Eq,
        WBinOp::Neq => bir::BinOp::Neq,
        WBinOp::Lt => bir::BinOp::Lt,
        WBinOp::Le => bir::BinOp::Le,
        WBinOp::Gt => bir::BinOp::Gt,
        WBinOp::Ge => bir::BinOp::Ge,
        WBinOp::SLt => bir::BinOp::SLt,
        WBinOp::SLe => bir::BinOp::SLe,
        WBinOp::SGt => bir::BinOp::SGt,
        WBinOp::SGe => bir::BinOp::SGe,
    }
}
fn binop_to_wire(op: bir::BinOp) -> WBinOp {
    match op {
        bir::BinOp::Add => WBinOp::Add,
        bir::BinOp::Sub => WBinOp::Sub,
        bir::BinOp::Mul => WBinOp::Mul,
        bir::BinOp::Div => WBinOp::Div,
        bir::BinOp::SDiv => WBinOp::SDiv,
        bir::BinOp::Rem => WBinOp::Rem,
        bir::BinOp::SRem => WBinOp::SRem,
        bir::BinOp::Mod => WBinOp::Mod,
        bir::BinOp::LShift => WBinOp::LShift,
        bir::BinOp::RShift => WBinOp::RShift,
        bir::BinOp::AShift => WBinOp::AShift,
        bir::BinOp::And => WBinOp::And,
        bir::BinOp::Or => WBinOp::Or,
        bir::BinOp::Xor => WBinOp::Xor,
        bir::BinOp::Eq => WBinOp::Eq,
        bir::BinOp::Neq => WBinOp::Neq,
        bir::BinOp::Lt => WBinOp::Lt,
        bir::BinOp::Le => WBinOp::Le,
        bir::BinOp::Gt => WBinOp::Gt,
        bir::BinOp::Ge => WBinOp::Ge,
        bir::BinOp::SLt => WBinOp::SLt,
        bir::BinOp::SLe => WBinOp::SLe,
        bir::BinOp::SGt => WBinOp::SGt,
        bir::BinOp::SGe => WBinOp::SGe,
    }
}

pub fn stmts_from_wire(stmts: &LinkedList<WStmt>) -> bir::Bil {
    stmts.iter().map(stmt_from_wire).collect()
}
pub fn stmts_to_wire(stmts: &bir::Bil) -> LinkedList<WStmt> {
    stmts.iter().map(stmt_to_wire).collect()
}
fn stmt_from_wire(stmt: &WStmt) -> bir::Stmt {
    match stmt {
        WStmt::Move(var, value) => bir::Stmt::Move {
            var: var_from_wire(var),
            value: exp_from_wire(value),
        },
        WStmt::Jmp(target) => bir::Stmt::Jmp(exp_from_wire(target)),
        WStmt::Special(message) => bir::Stmt::Special(message.clone()),
        WStmt::While(condition, body) => bir::Stmt::While {
            condition: exp_from_wire(condition),
            body: stmts_from_wire(body),
        },
        WStmt::If(condition, yes, no) => bir::Stmt::If {
            condition: exp_from_wire(condition),
            yes: stmts_from_wire(yes),
            no: stmts_from_wire(no),
        },
        WStmt::CpuExn(number) => bir::Stmt::CpuExn(u32_value(*number)),
    }
}
fn stmt_to_wire(stmt: &bir::Stmt) -> WStmt {
    match stmt {
        bir::Stmt::Move { var, value } => WStmt::Move(var_to_wire(var), exp_to_wire(value)),
        bir::Stmt::Jmp(target) => WStmt::Jmp(exp_to_wire(target)),
        bir::Stmt::Special(message) => WStmt::Special(message.clone()),
        bir::Stmt::While { condition, body } => {
            WStmt::While(exp_to_wire(condition), stmts_to_wire(body))
        }
        bir::Stmt::If { condition, yes, no } => WStmt::If(
            exp_to_wire(condition),
            stmts_to_wire(yes),
            stmts_to_wire(no),
        ),
        bir::Stmt::CpuExn(number) => WStmt::CpuExn(int(*number)),
    }
}

fn def_from_wire(def: &WDef) -> bir::Def {
    bir::Def {
        tid: def.tid as u64,
        var: var_from_wire(&def.var),
        rhs: exp_from_wire(&def.rhs),
    }
}
fn def_to_wire(def: &bir::Def) -> WDef {
    WDef {
        tid: def.tid as isize,
        var: var_to_wire(&def.var),
        rhs: exp_to_wire(&def.rhs),
    }
}
fn phi_from_wire(phi: &WPhi) -> bir::Phi {
    bir::Phi {
        tid: phi.tid as u64,
        var: var_from_wire(&phi.var),
        values: phi
            .values
            .iter()
            .map(|(tid, exp)| (*tid as u64, exp_from_wire(exp)))
            .collect(),
    }
}
fn phi_to_wire(phi: &bir::Phi) -> WPhi {
    WPhi {
        tid: phi.tid as isize,
        var: var_to_wire(&phi.var),
        values: phi
            .values
            .iter()
            .map(|(tid, exp)| (*tid as isize, exp_to_wire(exp)))
            .collect(),
    }
}
fn label_from_wire(label: &WLabel) -> bir::Label {
    match label {
        WLabel::Direct(tid) => bir::Label::Direct(*tid as u64),
        WLabel::Indirect(exp) => bir::Label::Indirect(exp_from_wire(exp)),
    }
}
fn label_to_wire(label: &bir::Label) -> WLabel {
    match label {
        bir::Label::Direct(tid) => WLabel::Direct(*tid as isize),
        bir::Label::Indirect(exp) => WLabel::Indirect(exp_to_wire(exp)),
    }
}
fn jmp_from_wire(jmp: &WJmp) -> bir::Jmp {
    let kind = match &jmp.kind {
        WJmpKind::Goto(label) => bir::JmpKind::Goto(label_from_wire(label)),
        WJmpKind::Call(target, return_to) => bir::JmpKind::Call {
            target: label_from_wire(target),
            return_to: return_to.as_ref().map(label_from_wire),
        },
        WJmpKind::Return(label) => bir::JmpKind::Return(label_from_wire(label)),
        WJmpKind::Interrupt(number, return_to) => bir::JmpKind::Interrupt {
            number: u32_value(*number),
            return_to: *return_to as u64,
        },
    };
    bir::Jmp {
        tid: jmp.tid as u64,
        condition: jmp.condition.as_ref().map(exp_from_wire),
        kind,
    }
}
fn jmp_to_wire(jmp: &bir::Jmp) -> WJmp {
    let kind = match &jmp.kind {
        bir::JmpKind::Goto(label) => WJmpKind::Goto(label_to_wire(label)),
        bir::JmpKind::Call { target, return_to } => {
            WJmpKind::Call(label_to_wire(target), return_to.as_ref().map(label_to_wire))
        }
        bir::JmpKind::Return(label) => WJmpKind::Return(label_to_wire(label)),
        bir::JmpKind::Interrupt { number, return_to } => {
            WJmpKind::Interrupt(int(*number), *return_to as isize)
        }
    };
    WJmp {
        tid: jmp.tid as isize,
        condition: jmp.condition.as_ref().map(exp_to_wire),
        kind,
    }
}

pub fn sub_from_wire(sub: &WSub) -> bir::Sub {
    bir::Sub {
        tid: sub.tid as u64,
        name: sub.name.clone(),
        args: sub.args.iter().map(def_from_wire).collect(),
        blks: sub
            .blks
            .iter()
            .map(|blk| bir::Blk {
                tid: blk.tid as u64,
                phis: blk.phis.iter().map(phi_from_wire).collect(),
                defs: blk.defs.iter().map(def_from_wire).collect(),
                jmps: blk.jmps.iter().map(jmp_from_wire).collect(),
            })
            .collect(),
    }
}
pub fn sub_to_wire(sub: &bir::Sub) -> WSub {
    WSub {
        tid: sub.tid as isize,
        name: sub.name.clone(),
        args: sub.args.iter().map(def_to_wire).collect(),
        blks: sub
            .blks
            .iter()
            .map(|blk| WBlk {
                tid: blk.tid as isize,
                phis: blk.phis.iter().map(phi_to_wire).collect(),
                defs: blk.defs.iter().map(def_to_wire).collect(),
                jmps: blk.jmps.iter().map(jmp_to_wire).collect(),
            })
            .collect(),
    }
}
