use bap_bitvec::BitVec;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

pub type Tid = u64;

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
pub enum Type {
    Unit,
    Unknown,
    Mem { address: u32, value: u32 },
    Int(u32),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
pub struct Var {
    pub name: String,
    pub typ: Type,
    pub index: Option<usize>,
    pub is_virtual: bool,
}
impl Var {
    pub fn new(name: impl Into<String>, typ: Type) -> Self {
        Self {
            name: name.into(),
            typ,
            index: None,
            is_virtual: false,
        }
    }
    pub fn new_virtual(name: impl Into<String>, typ: Type) -> Self {
        Self {
            is_virtual: true,
            ..Self::new(name, typ)
        }
    }
    pub fn version(&self, index: usize) -> Self {
        Self {
            index: Some(index),
            ..self.clone()
        }
    }
    pub fn base(&self) -> Self {
        Self {
            index: None,
            ..self.clone()
        }
    }
    pub fn width(&self) -> u32 {
        match self.typ {
            Type::Int(width) | Type::Mem { value: width, .. } => width,
            Type::Unit | Type::Unknown => 0,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum Endian {
    Little,
    Big,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum Cast {
    Low,
    High,
    Signed,
    Unsigned,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum UnOp {
    Neg,
    Not,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum BinOp {
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

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Exp {
    Int(BitVec),
    Var(Var),
    Load {
        memory: Box<Exp>,
        address: Box<Exp>,
        endian: Endian,
        size: u32,
    },
    Store {
        memory: Box<Exp>,
        address: Box<Exp>,
        value: Box<Exp>,
        endian: Endian,
        size: u32,
    },
    Bin {
        op: BinOp,
        left: Box<Exp>,
        right: Box<Exp>,
    },
    Un {
        op: UnOp,
        value: Box<Exp>,
    },
    Cast {
        kind: Cast,
        size: u32,
        value: Box<Exp>,
    },
    Let {
        var: Var,
        value: Box<Exp>,
        body: Box<Exp>,
    },
    Ite {
        condition: Box<Exp>,
        yes: Box<Exp>,
        no: Box<Exp>,
    },
    Extract {
        high: u32,
        low: u32,
        value: Box<Exp>,
    },
    Concat {
        left: Box<Exp>,
        right: Box<Exp>,
    },
    Unknown(String, Type),
}
impl Exp {
    pub fn var(var: Var) -> Self {
        Self::Var(var)
    }
    pub fn int(value: BitVec) -> Self {
        Self::Int(value)
    }
    pub fn bin(op: BinOp, left: Exp, right: Exp) -> Self {
        Self::Bin {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }
    pub fn un(op: UnOp, value: Exp) -> Self {
        Self::Un {
            op,
            value: Box::new(value),
        }
    }
    pub fn cast(kind: Cast, size: u32, value: Exp) -> Self {
        Self::Cast {
            kind,
            size,
            value: Box::new(value),
        }
    }
    pub fn ite(condition: Exp, yes: Exp, no: Exp) -> Self {
        Self::Ite {
            condition: Box::new(condition),
            yes: Box::new(yes),
            no: Box::new(no),
        }
    }
    pub fn load(memory: Exp, address: Exp, endian: Endian, size: u32) -> Self {
        Self::Load {
            memory: Box::new(memory),
            address: Box::new(address),
            endian,
            size,
        }
    }
    pub fn store(memory: Exp, address: Exp, value: Exp, endian: Endian, size: u32) -> Self {
        Self::Store {
            memory: Box::new(memory),
            address: Box::new(address),
            value: Box::new(value),
            endian,
            size,
        }
    }
    pub fn extract(high: u32, low: u32, value: Exp) -> Self {
        Self::Extract {
            high,
            low,
            value: Box::new(value),
        }
    }
    pub fn concat(left: Exp, right: Exp) -> Self {
        Self::Concat {
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    pub fn free_vars(&self) -> BTreeSet<Var> {
        let mut vars = BTreeSet::new();
        self.collect_vars(&mut vars);
        vars
    }
    fn collect_vars(&self, vars: &mut BTreeSet<Var>) {
        match self {
            Self::Var(var) => {
                vars.insert(var.clone());
            }
            Self::Load {
                memory, address, ..
            } => {
                memory.collect_vars(vars);
                address.collect_vars(vars);
            }
            Self::Store {
                memory,
                address,
                value,
                ..
            } => {
                memory.collect_vars(vars);
                address.collect_vars(vars);
                value.collect_vars(vars);
            }
            Self::Bin { left, right, .. } | Self::Concat { left, right } => {
                left.collect_vars(vars);
                right.collect_vars(vars);
            }
            Self::Un { value, .. } | Self::Cast { value, .. } | Self::Extract { value, .. } => {
                value.collect_vars(vars)
            }
            Self::Let { var, value, body } => {
                let mut body_vars = BTreeSet::new();
                body.collect_vars(&mut body_vars);
                body_vars.remove(var);
                vars.extend(body_vars);
                value.collect_vars(vars);
            }
            Self::Ite { condition, yes, no } => {
                condition.collect_vars(vars);
                yes.collect_vars(vars);
                no.collect_vars(vars);
            }
            Self::Int(_) | Self::Unknown(_, _) => {}
        }
    }

    pub fn substitute(&self, replacements: &BTreeMap<Var, Exp>) -> Exp {
        match self {
            Self::Int(_) | Self::Unknown(_, _) => self.clone(),
            Self::Var(var) => replacements
                .get(var)
                .cloned()
                .unwrap_or_else(|| self.clone()),
            Self::Load {
                memory,
                address,
                endian,
                size,
            } => Self::load(
                memory.substitute(replacements),
                address.substitute(replacements),
                *endian,
                *size,
            ),
            Self::Store {
                memory,
                address,
                value,
                endian,
                size,
            } => Self::store(
                memory.substitute(replacements),
                address.substitute(replacements),
                value.substitute(replacements),
                *endian,
                *size,
            ),
            Self::Bin { op, left, right } => Self::bin(
                *op,
                left.substitute(replacements),
                right.substitute(replacements),
            ),
            Self::Un { op, value } => Self::un(*op, value.substitute(replacements)),
            Self::Cast { kind, size, value } => {
                Self::cast(*kind, *size, value.substitute(replacements))
            }
            Self::Let { var, value, body } => {
                let value = value.substitute(replacements);
                let body = if replacements.contains_key(var) {
                    let mut scoped = replacements.clone();
                    scoped.remove(var);
                    body.substitute(&scoped)
                } else {
                    body.substitute(replacements)
                };
                Self::Let {
                    var: var.clone(),
                    value: Box::new(value),
                    body: Box::new(body),
                }
            }
            Self::Ite { condition, yes, no } => Self::ite(
                condition.substitute(replacements),
                yes.substitute(replacements),
                no.substitute(replacements),
            ),
            Self::Extract { high, low, value } => {
                Self::extract(*high, *low, value.substitute(replacements))
            }
            Self::Concat { left, right } => Self::concat(
                left.substitute(replacements),
                right.substitute(replacements),
            ),
        }
    }

    pub fn map(&self, f: &impl Fn(&Exp) -> Exp) -> Exp {
        let mapped = match self {
            Self::Int(_) | Self::Var(_) | Self::Unknown(_, _) => self.clone(),
            Self::Load {
                memory,
                address,
                endian,
                size,
            } => Self::load(memory.map(f), address.map(f), *endian, *size),
            Self::Store {
                memory,
                address,
                value,
                endian,
                size,
            } => Self::store(memory.map(f), address.map(f), value.map(f), *endian, *size),
            Self::Bin { op, left, right } => Self::Bin {
                op: *op,
                left: Box::new(left.map(f)),
                right: Box::new(right.map(f)),
            },
            Self::Un { op, value } => Self::Un {
                op: *op,
                value: Box::new(value.map(f)),
            },
            Self::Cast { kind, size, value } => Self::Cast {
                kind: *kind,
                size: *size,
                value: Box::new(value.map(f)),
            },
            Self::Let { var, value, body } => Self::Let {
                var: var.clone(),
                value: Box::new(value.map(f)),
                body: Box::new(body.map(f)),
            },
            Self::Ite { condition, yes, no } => Self::Ite {
                condition: Box::new(condition.map(f)),
                yes: Box::new(yes.map(f)),
                no: Box::new(no.map(f)),
            },
            Self::Extract { high, low, value } => Self::Extract {
                high: *high,
                low: *low,
                value: Box::new(value.map(f)),
            },
            Self::Concat { left, right } => Self::Concat {
                left: Box::new(left.map(f)),
                right: Box::new(right.map(f)),
            },
        };
        f(&mapped)
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Stmt {
    Move { var: Var, value: Exp },
    Jmp(Exp),
    Special(String),
    While { condition: Exp, body: Bil },
    If { condition: Exp, yes: Bil, no: Bil },
    CpuExn(u32),
}
pub type Bil = Vec<Stmt>;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Label {
    Direct(Tid),
    Indirect(Exp),
}
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum JmpKind {
    Goto(Label),
    Call {
        target: Label,
        return_to: Option<Label>,
    },
    Return(Label),
    Interrupt {
        number: u32,
        return_to: Tid,
    },
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Def {
    pub tid: Tid,
    pub var: Var,
    pub rhs: Exp,
}
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Phi {
    pub tid: Tid,
    pub var: Var,
    pub values: BTreeMap<Tid, Exp>,
}
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Jmp {
    pub tid: Tid,
    pub condition: Option<Exp>,
    pub kind: JmpKind,
}

#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct Blk {
    pub tid: Tid,
    pub phis: Vec<Phi>,
    pub defs: Vec<Def>,
    pub jmps: Vec<Jmp>,
}
impl Jmp {
    pub fn free_vars(&self) -> BTreeSet<Var> {
        let mut vars = self
            .condition
            .iter()
            .flat_map(Exp::free_vars)
            .collect::<BTreeSet<_>>();
        let labels: Vec<&Label> = match &self.kind {
            JmpKind::Goto(label) | JmpKind::Return(label) => vec![label],
            JmpKind::Call { target, return_to } => {
                let mut labels = vec![target];
                labels.extend(return_to.iter());
                labels
            }
            JmpKind::Interrupt { .. } => Vec::new(),
        };
        for label in labels {
            if let Label::Indirect(target) = label {
                vars.extend(target.free_vars());
            }
        }
        vars
    }
}

impl Blk {
    pub fn new(tid: Tid) -> Self {
        Self {
            tid,
            ..Self::default()
        }
    }
    pub fn successors(&self) -> BTreeSet<Tid> {
        self.jmps
            .iter()
            .filter_map(|jmp| match &jmp.kind {
                JmpKind::Goto(Label::Direct(dst)) | JmpKind::Return(Label::Direct(dst)) => {
                    Some(*dst)
                }
                JmpKind::Call {
                    return_to: Some(Label::Direct(dst)),
                    ..
                } => Some(*dst),
                JmpKind::Interrupt { return_to, .. } => Some(*return_to),
                _ => None,
            })
            .collect()
    }
    pub fn free_vars(&self) -> BTreeSet<Var> {
        let mut vars = BTreeSet::new();
        let mut defined = BTreeSet::new();
        for def in &self.defs {
            vars.extend(def.rhs.free_vars().difference(&defined).cloned());
            defined.insert(def.var.clone());
        }
        for phi in &self.phis {
            vars.extend(phi.values.values().flat_map(Exp::free_vars));
        }
        for jmp in &self.jmps {
            vars.extend(jmp.free_vars());
        }
        vars
    }
    pub fn defined_vars(&self) -> BTreeSet<Var> {
        self.phis
            .iter()
            .map(|phi| phi.var.clone())
            .chain(self.defs.iter().map(|def| def.var.clone()))
            .collect()
    }
    pub fn defines(&self, var: &Var) -> bool {
        self.defined_vars().contains(var)
    }
}

pub type Arg = Def;
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Sub {
    pub tid: Tid,
    pub name: String,
    pub args: Vec<Arg>,
    pub blks: Vec<Blk>,
}
impl Sub {
    pub fn new(tid: Tid, name: impl Into<String>) -> Self {
        Self {
            tid,
            name: name.into(),
            args: Vec::new(),
            blks: Vec::new(),
        }
    }
    pub fn blk(&self, tid: Tid) -> Option<&Blk> {
        self.blks.iter().find(|blk| blk.tid == tid)
    }
    pub fn blk_mut(&mut self, tid: Tid) -> Option<&mut Blk> {
        self.blks.iter_mut().find(|blk| blk.tid == tid)
    }
}
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct Program {
    pub subs: Vec<Sub>,
}
impl Program {
    pub fn new(subs: Vec<Sub>) -> Self {
        Self { subs }
    }
    pub fn sub(&self, tid: Tid) -> Option<&Sub> {
        self.subs.iter().find(|sub| sub.tid == tid)
    }
}
