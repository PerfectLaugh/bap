use crate::{Bil, Evaluator, Exp, Stmt, Type, Var};
use bap_bitvec::BitVec;
use std::collections::{BTreeMap, BTreeSet};

pub fn fold_exp(exp: &Exp) -> Exp {
    exp.map(&|exp| {
        let mut evaluator = Evaluator::new(64);
        match evaluator.eval(exp) {
            Ok(value) => value
                .bits()
                .map_or_else(|_| exp.clone(), |bits| Exp::Int(bits.clone())),
            Err(_) => exp.clone(),
        }
    })
}

pub fn fold_bil(bil: &Bil) -> Bil {
    bil.iter().map(fold_stmt).collect()
}

fn fold_stmt(stmt: &Stmt) -> Stmt {
    match stmt {
        Stmt::Move { var, value } => Stmt::Move {
            var: var.clone(),
            value: fold_exp(value),
        },
        Stmt::Jmp(target) => Stmt::Jmp(fold_exp(target)),
        Stmt::Special(_) | Stmt::CpuExn(_) => stmt.clone(),
        Stmt::While { condition, body } => Stmt::While {
            condition: fold_exp(condition),
            body: fold_bil(body),
        },
        Stmt::If { condition, yes, no } => Stmt::If {
            condition: fold_exp(condition),
            yes: fold_bil(yes),
            no: fold_bil(no),
        },
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Const {
    Immediate(BitVec),
    Undefined(String, Type),
    Top,
}
impl Const {
    fn of_exp(exp: &Exp) -> Self {
        match exp {
            Exp::Int(value) => Self::Immediate(value.clone()),
            Exp::Unknown(message, typ) => Self::Undefined(message.clone(), typ.clone()),
            _ => Self::Top,
        }
    }
    fn to_exp(&self) -> Option<Exp> {
        match self {
            Self::Immediate(value) => Some(Exp::Int(value.clone())),
            Self::Undefined(message, typ) => Some(Exp::Unknown(message.clone(), typ.clone())),
            Self::Top => None,
        }
    }
}

type Environment = BTreeMap<Var, Const>;

fn join(left: &Environment, right: &Environment) -> Environment {
    left.keys()
        .chain(right.keys())
        .map(|var| {
            let value = match (left.get(var), right.get(var)) {
                (Some(left), Some(right)) if left == right => left.clone(),
                _ => Const::Top,
            };
            (var.clone(), value)
        })
        .collect()
}

fn eval_var(var: &Var, environment: &Environment) -> Exp {
    environment
        .get(var)
        .and_then(Const::to_exp)
        .unwrap_or_else(|| Exp::Var(var.clone()))
}

fn eval_exp(exp: &Exp, environment: &mut Environment) -> Exp {
    fold_exp(&eval_exp_inner(exp, environment))
}

fn eval_exp_inner(exp: &Exp, environment: &mut Environment) -> Exp {
    match exp {
        Exp::Int(_) | Exp::Unknown(_, _) => exp.clone(),
        Exp::Var(var) => eval_var(var, environment),
        Exp::Load {
            memory,
            address,
            endian,
            size,
        } => Exp::load(
            eval_exp(memory, environment),
            eval_exp(address, environment),
            *endian,
            *size,
        ),
        Exp::Store {
            memory,
            address,
            value,
            endian,
            size,
        } => Exp::store(
            eval_exp(memory, environment),
            eval_exp(address, environment),
            eval_exp(value, environment),
            *endian,
            *size,
        ),
        Exp::Bin { op, left, right } => Exp::bin(
            *op,
            eval_exp(left, environment),
            eval_exp(right, environment),
        ),
        Exp::Un { op, value } => Exp::un(*op, eval_exp(value, environment)),
        Exp::Cast { kind, size, value } => Exp::cast(*kind, *size, eval_exp(value, environment)),
        Exp::Let { var, value, body } => {
            let saved = environment.clone();
            let value = eval_exp(value, environment);
            environment.insert(var.clone(), Const::of_exp(&value));
            let body = eval_exp(body, environment);
            *environment = saved;
            match body {
                Exp::Int(_) | Exp::Unknown(_, _) => body,
                _ => Exp::Let {
                    var: var.clone(),
                    value: Box::new(value),
                    body: Box::new(body),
                },
            }
        }
        Exp::Ite { condition, yes, no } => Exp::ite(
            eval_exp(condition, environment),
            eval_exp(yes, environment),
            eval_exp(no, environment),
        ),
        Exp::Extract { high, low, value } => {
            Exp::extract(*high, *low, eval_exp(value, environment))
        }
        Exp::Concat { left, right } => {
            Exp::concat(eval_exp(left, environment), eval_exp(right, environment))
        }
    }
}

fn has_unconditional_jmps(bil: &Bil) -> bool {
    bil.iter().any(|stmt| matches!(stmt, Stmt::Jmp(_)))
}

fn eval_bil(bil: &Bil, environment: &mut Environment) -> Bil {
    bil.iter()
        .map(|stmt| eval_stmt(stmt, environment))
        .collect()
}

fn eval_stmt(stmt: &Stmt, environment: &mut Environment) -> Stmt {
    match stmt {
        Stmt::Move { var, value } => {
            let value = eval_exp(value, environment);
            environment.insert(var.clone(), Const::of_exp(&value));
            Stmt::Move {
                var: var.clone(),
                value,
            }
        }
        Stmt::Jmp(target) => Stmt::Jmp(eval_exp(target, environment)),
        Stmt::Special(_) | Stmt::CpuExn(_) => stmt.clone(),
        Stmt::If { condition, yes, no } => {
            let saved = environment.clone();
            let condition = eval_exp(condition, environment);
            let yes = eval_bil(yes, environment);
            let yes_environment = environment.clone();
            *environment = saved.clone();
            let no = eval_bil(no, environment);
            let no_environment = environment.clone();
            *environment = match (has_unconditional_jmps(&yes), has_unconditional_jmps(&no)) {
                (false, false) => join(&yes_environment, &no_environment),
                (true, true) => saved,
                (false, true) => yes_environment,
                (true, false) => no_environment,
            };
            Stmt::If { condition, yes, no }
        }
        Stmt::While { condition, body } => {
            let saved = environment.clone();
            for var in defined_vars(body) {
                environment.insert(var, Const::Top);
            }
            let condition = eval_exp(condition, environment);
            let body = eval_bil(body, environment);
            *environment = if has_unconditional_jmps(&body) {
                saved
            } else {
                join(&saved, environment)
            };
            Stmt::While { condition, body }
        }
    }
}

fn defined_vars(bil: &Bil) -> BTreeSet<Var> {
    let mut vars = BTreeSet::new();
    for stmt in bil {
        match stmt {
            Stmt::Move { var, .. } => {
                vars.insert(var.clone());
            }
            Stmt::If { yes, no, .. } => {
                vars.extend(defined_vars(yes));
                vars.extend(defined_vars(no));
            }
            Stmt::While { body, .. } => vars.extend(defined_vars(body)),
            Stmt::Jmp(_) | Stmt::Special(_) | Stmt::CpuExn(_) => {}
        }
    }
    vars
}

pub fn propagate_consts(bil: &Bil) -> Bil {
    eval_bil(bil, &mut Environment::new())
}

fn free_vars(bil: &Bil) -> BTreeSet<Var> {
    let mut free = BTreeSet::new();
    let mut defined = BTreeSet::new();
    for stmt in bil {
        match stmt {
            Stmt::Move { var, value } => {
                free.extend(value.free_vars().difference(&defined).cloned());
                defined.insert(var.clone());
            }
            Stmt::Jmp(target) => free.extend(target.free_vars()),
            Stmt::Special(_) | Stmt::CpuExn(_) => {}
            Stmt::While { condition, body } => {
                free.extend(condition.free_vars());
                free.extend(free_vars(body));
            }
            Stmt::If { condition, yes, no } => {
                free.extend(condition.free_vars());
                free.extend(free_vars(yes));
                free.extend(free_vars(no));
            }
        }
    }
    free
}

fn prune(bil: &Bil, mut live: BTreeSet<Var>) -> (Bil, BTreeSet<Var>) {
    let mut result = Vec::new();
    for stmt in bil.iter().rev() {
        match stmt {
            Stmt::Special(_) | Stmt::CpuExn(_) => result.push(stmt.clone()),
            Stmt::Jmp(target) => {
                live.extend(target.free_vars());
                result.push(stmt.clone());
            }
            Stmt::If { condition, yes, no } => {
                let (yes, yes_live) = prune(yes, live.clone());
                let (no, no_live) = prune(no, live.clone());
                live = yes_live.into_iter().chain(no_live).collect();
                live.extend(condition.free_vars());
                result.push(Stmt::If {
                    condition: condition.clone(),
                    yes,
                    no,
                });
            }
            Stmt::Move { var, value } => {
                if !var.is_virtual || live.contains(var) {
                    live.remove(var);
                    live.extend(value.free_vars());
                    result.push(stmt.clone());
                }
            }
            Stmt::While { condition, body } => {
                live.extend(free_vars(body));
                live.extend(condition.free_vars());
                result.push(stmt.clone());
            }
        }
    }
    result.reverse();
    (result, live)
}

pub fn prune_dead_virtuals(bil: &Bil) -> Bil {
    prune(bil, BTreeSet::new()).0
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BinOp;

    #[test]
    fn propagates_through_structured_bil_and_prunes_virtuals() {
        let x = Var::new_virtual("x", Type::Int(32));
        let y = Var::new_virtual("y", Type::Int(32));
        let bil = vec![
            Stmt::Move {
                var: x.clone(),
                value: Exp::Int(BitVec::from_u64(32, 40)),
            },
            Stmt::Move {
                var: y.clone(),
                value: Exp::bin(BinOp::Add, Exp::Var(x), Exp::Int(BitVec::from_u64(32, 2))),
            },
            Stmt::Jmp(Exp::Var(y)),
        ];
        let propagated = fold_bil(&propagate_consts(&bil));
        assert_eq!(
            propagated[1],
            Stmt::Move {
                var: Var::new_virtual("y", Type::Int(32)),
                value: Exp::Int(BitVec::from_u64(32, 42)),
            }
        );
        assert_eq!(prune_dead_virtuals(&propagated).len(), 1);
        assert_eq!(prune_dead_virtuals(&propagated[..1].to_vec()).len(), 0);
    }
}
