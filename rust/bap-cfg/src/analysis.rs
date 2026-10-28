use crate::Cfg;
use bap_bir::{BinOp, Blk, Exp, Sub, Var};
use bap_bitvec::BitVec;
use std::collections::{BTreeMap, BTreeSet};

pub fn simplify_exp(exp: &Exp) -> Exp {
    exp.map(&|exp| match exp {
        Exp::Ite { condition, yes, no } => {
            let mut evaluator = bap_bir::Evaluator::new(64);
            match evaluator.eval(condition) {
                Ok(value) if value.bits().is_ok_and(|bits| bits.is_one()) => (**yes).clone(),
                Ok(value) if value.bits().is_ok_and(|bits| bits.is_zero()) => (**no).clone(),
                _ => exp.clone(),
            }
        }
        Exp::Bin { op, left, right } => {
            if let (Exp::Int(left_value), Exp::Int(right_value)) = (&**left, &**right) {
                if *op == BinOp::Add && left_value.is_zero() {
                    return (**right).clone();
                }
                if *op == BinOp::Add && right_value.is_zero() {
                    return (**left).clone();
                }
                if *op == BinOp::Sub && right_value.is_zero() {
                    return (**left).clone();
                }
                if *op == BinOp::Mul && left_value.is_one() {
                    return (**right).clone();
                }
                if *op == BinOp::Mul && right_value.is_one() {
                    return (**left).clone();
                }
                if *op == BinOp::Mul && (left_value.is_zero() || right_value.is_zero()) {
                    return Exp::Int(BitVec::zero(left_value.width()));
                }
            }
            let mut evaluator = bap_bir::Evaluator::new(64);
            match evaluator.eval(exp) {
                Ok(value) => value
                    .bits()
                    .map_or_else(|_| exp.clone(), |bits| Exp::Int(bits.clone())),
                Err(_) => exp.clone(),
            }
        }
        Exp::Cast { .. } => {
            let mut evaluator = bap_bir::Evaluator::new(64);
            match evaluator.eval(exp) {
                Ok(value) => value
                    .bits()
                    .map_or_else(|_| exp.clone(), |bits| Exp::Int(bits.clone())),
                Err(_) => exp.clone(),
            }
        }
        _ => exp.clone(),
    })
}

pub fn simplify_block(block: &Blk) -> Blk {
    let mut block = block.clone();
    for def in &mut block.defs {
        def.rhs = simplify_exp(&def.rhs);
    }
    for phi in &mut block.phis {
        for value in phi.values.values_mut() {
            *value = simplify_exp(value);
        }
    }
    for jmp in &mut block.jmps {
        if let Some(condition) = &mut jmp.condition {
            *condition = simplify_exp(condition);
        }
    }
    block
}

pub fn simplify_sub(sub: &Sub) -> Sub {
    let mut sub = sub.clone();
    for block in &mut sub.blks {
        *block = simplify_block(block);
    }
    sub
}

pub fn eliminate_dead_code(cfg: &Cfg) -> Cfg {
    let mut cfg = cfg.clone();
    loop {
        let previous = cfg.clone();
        let (_, outs) = cfg.liveness();
        for block in cfg.blocks.values_mut() {
            let out = &outs[&block.tid];
            block
                .defs
                .retain(|def| out.contains(&def.var) || has_side_effect(&def.rhs));
            block.phis.retain(|phi| out.contains(&phi.var));
        }
        if cfg == previous {
            return cfg;
        }
    }
}

fn has_side_effect(exp: &Exp) -> bool {
    match exp {
        Exp::Store { .. } => true,
        Exp::Load {
            memory, address, ..
        } => has_side_effect(memory) || has_side_effect(address),
        Exp::Bin { left, right, .. } | Exp::Concat { left, right } => {
            has_side_effect(left) || has_side_effect(right)
        }
        Exp::Un { value, .. } | Exp::Cast { value, .. } | Exp::Extract { value, .. } => {
            has_side_effect(value)
        }
        Exp::Let { value, body, .. } => has_side_effect(value) || has_side_effect(body),
        Exp::Ite { condition, yes, no } => {
            has_side_effect(condition) || has_side_effect(yes) || has_side_effect(no)
        }
        Exp::Int(_) | Exp::Var(_) | Exp::Unknown(_, _) => false,
    }
}

pub fn propagate_constants(cfg: &Cfg) -> Cfg {
    let mut cfg = cfg.prune();
    let mut exits = BTreeMap::<bap_bir::Tid, BTreeMap<Var, BitVec>>::new();
    let mut work = cfg.blocks.keys().copied().collect::<Vec<_>>();
    while let Some(tid) = work.pop() {
        let predecessors = cfg.predecessors(tid);
        let mut incoming = predecessors.iter().filter_map(|pred| exits.get(pred));
        let mut environment = incoming.next().cloned().unwrap_or_default();
        for predecessor in incoming {
            environment.retain(|var, value| predecessor.get(var) == Some(value));
        }
        let block = cfg.block_mut(tid).expect("a reachable block");
        for phi in &mut block.phis {
            for value in phi.values.values_mut() {
                *value = simplify_exp(value);
            }
        }
        for def in &mut block.defs {
            let replacements = environment
                .iter()
                .map(|(var, value)| (var.clone(), Exp::Int(value.clone())))
                .collect();
            def.rhs = simplify_exp(&def.rhs.substitute(&replacements));
            if let Exp::Int(value) = &def.rhs {
                environment.insert(def.var.clone(), value.clone());
            } else {
                environment.remove(&def.var);
            }
        }
        let replacements = environment
            .iter()
            .map(|(var, value)| (var.clone(), Exp::Int(value.clone())))
            .collect();
        for jmp in &mut block.jmps {
            if let Some(condition) = &mut jmp.condition {
                *condition = simplify_exp(&condition.substitute(&replacements));
            }
            substitute_jmp_targets(jmp, &replacements);
        }
        if exits.get(&tid) != Some(&environment) {
            exits.insert(tid, environment);
            work.extend(cfg.successors(tid));
        }
    }
    cfg
}

fn substitute_jmp_targets(jmp: &mut bap_bir::Jmp, replacements: &BTreeMap<Var, Exp>) {
    fn label(label: &mut bap_bir::Label, replacements: &BTreeMap<Var, Exp>) {
        if let bap_bir::Label::Indirect(target) = label {
            *target = simplify_exp(&target.substitute(replacements));
        }
    }
    match &mut jmp.kind {
        bap_bir::JmpKind::Goto(target) | bap_bir::JmpKind::Return(target) => {
            label(target, replacements)
        }
        bap_bir::JmpKind::Call { target, return_to } => {
            label(target, replacements);
            if let Some(return_to) = return_to {
                label(return_to, replacements);
            }
        }
        bap_bir::JmpKind::Interrupt { .. } => {}
    }
}

pub fn optimize(sub: &Sub) -> Sub {
    let cfg = Cfg::from_sub(sub).prune();
    let cfg = propagate_constants(&cfg);
    eliminate_dead_code(&cfg).into_sub(sub)
}

pub fn to_ssa(sub: &Sub) -> Sub {
    let actual = sub.blks.iter().map(|blk| blk.tid).collect::<BTreeSet<_>>();
    let order = sub
        .blks
        .iter()
        .enumerate()
        .map(|(index, blk)| (blk.tid, index))
        .collect::<BTreeMap<_, _>>();
    let mut cfg = Cfg::connected(sub);
    let idom = cfg.immediate_dominators();
    let frontier = cfg.dominance_frontier();
    let vars = cfg
        .blocks
        .values()
        .flat_map(|block| {
            block
                .defined_vars()
                .into_iter()
                .chain(block.free_vars())
                .map(|var| var.base())
                .collect::<BTreeSet<_>>()
        })
        .collect::<BTreeSet<_>>();
    for var in vars {
        let definitions = cfg
            .blocks
            .values()
            .filter(|block| block.defines(&var))
            .map(|block| block.tid)
            .collect::<BTreeSet<_>>();
        let mut work = definitions.into_iter().collect::<Vec<_>>();
        let mut inserted = BTreeSet::new();
        while let Some(tid) = work.pop() {
            for join in frontier.get(&tid).into_iter().flatten() {
                if inserted.insert(*join) {
                    let predecessors = cfg.predecessors(*join);
                    if let Some(block) = cfg.block_mut(*join) {
                        let values = predecessors
                            .into_iter()
                            .map(|pred| (pred, Exp::Var(var.clone())))
                            .collect();
                        block.phis.push(bap_bir::Phi {
                            tid: *join,
                            var: var.clone(),
                            values,
                        });
                    }
                    work.push(*join);
                }
            }
        }
    }
    let mut renamer = Renamer::new(idom);
    renamer.rename(cfg.start, &mut cfg);
    let mut sub = cfg.into_sub(sub);
    sub.blks.retain(|blk| actual.contains(&blk.tid));
    sub.blks.sort_by_key(|blk| order[&blk.tid]);
    sub
}

struct Renamer {
    idom: BTreeMap<bap_bir::Tid, bap_bir::Tid>,
    stacks: BTreeMap<Var, Vec<Var>>,
    counters: BTreeMap<Var, usize>,
}
impl Renamer {
    fn new(idom: BTreeMap<bap_bir::Tid, bap_bir::Tid>) -> Self {
        Self {
            idom,
            stacks: BTreeMap::new(),
            counters: BTreeMap::new(),
        }
    }
    fn new_name(&mut self, var: &Var) -> Var {
        let counter = self.counters.entry(var.clone()).or_insert(1);
        let renamed = var.version(*counter);
        *counter += 1;
        self.stacks
            .entry(var.clone())
            .or_default()
            .push(renamed.clone());
        renamed
    }
    fn top(&self, var: &Var) -> Var {
        let base = var.base();
        self.stacks
            .get(&base)
            .and_then(|stack| stack.last())
            .cloned()
            .unwrap_or(base)
    }
    fn replacements(&self) -> BTreeMap<Var, Exp> {
        self.stacks
            .iter()
            .filter_map(|(var, stack)| stack.last().map(|top| (var.clone(), Exp::Var(top.clone()))))
            .collect()
    }
    fn substitute(&self, exp: &Exp) -> Exp {
        exp.substitute(&self.replacements())
    }
    fn pop(&mut self, defined: &[Var]) {
        for var in defined {
            if let Some(stack) = self.stacks.get_mut(var) {
                stack.pop();
            }
        }
    }
    fn rename(&mut self, tid: bap_bir::Tid, cfg: &mut Cfg) {
        let Some(block) = cfg.block_mut(tid) else {
            return;
        };
        let defined = block
            .defined_vars()
            .into_iter()
            .map(|var| var.base())
            .collect::<Vec<_>>();
        for phi in &mut block.phis {
            let var = phi.var.base();
            phi.var = self.new_name(&var);
        }
        for def in &mut block.defs {
            def.rhs = self.substitute(&def.rhs);
            let var = def.var.base();
            def.var = self.new_name(&var);
        }
        let replacements = self.replacements();
        for jmp in &mut block.jmps {
            if let Some(condition) = &mut jmp.condition {
                *condition = condition.substitute(&replacements);
            }
            substitute_jmp_targets(jmp, &replacements);
        }
        let successors = cfg.successors(tid).iter().copied().collect::<Vec<_>>();
        for successor in successors {
            if let Some(block) = cfg.block_mut(successor) {
                for phi in &mut block.phis {
                    if let Some(Exp::Var(var)) = phi.values.get_mut(&tid) {
                        *var = self.top(var);
                    }
                }
            }
        }
        let children = self
            .idom
            .iter()
            .filter(|(_, parent)| **parent == tid)
            .map(|(child, _)| *child)
            .collect::<Vec<_>>();
        for child in children {
            self.rename(child, cfg);
        }
        self.pop(&defined);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bap_bir::{Def, Jmp, JmpKind, Label, Type};

    fn var() -> Var {
        Var::new("x", Type::Int(32))
    }
    fn int(value: u64) -> Exp {
        Exp::Int(BitVec::from_u64(32, value))
    }
    fn def(tid: u64, var: Var, rhs: Exp) -> Def {
        Def { tid, var, rhs }
    }
    fn goto(tid: u64, destination: u64) -> Jmp {
        Jmp {
            tid,
            condition: None,
            kind: JmpKind::Goto(Label::Direct(destination)),
        }
    }
    fn sample() -> Sub {
        let mut sub = Sub::new(1, "sample");
        sub.blks.push(Blk {
            tid: 1,
            defs: vec![def(1, var(), int(1))],
            jmps: vec![goto(1, 2)],
            ..Blk::new(1)
        });
        sub.blks.push(Blk {
            tid: 2,
            defs: vec![def(2, var(), int(2))],
            jmps: vec![goto(2, 3)],
            ..Blk::new(2)
        });
        sub.blks.push(Blk {
            tid: 3,
            defs: vec![def(3, var(), Exp::Var(var()))],
            ..Blk::new(3)
        });
        sub
    }
    fn diamond() -> Sub {
        let mut sub = Sub::new(1, "diamond");
        sub.blks.push(Blk {
            tid: 1,
            defs: vec![def(1, var(), int(0))],
            jmps: vec![goto(1, 2), goto(2, 3)],
            ..Blk::new(1)
        });
        sub.blks.push(Blk {
            tid: 2,
            defs: vec![def(2, var(), int(1))],
            jmps: vec![goto(3, 4)],
            ..Blk::new(2)
        });
        sub.blks.push(Blk {
            tid: 3,
            defs: vec![def(3, var(), int(2))],
            jmps: vec![goto(4, 4)],
            ..Blk::new(3)
        });
        sub.blks.push(Blk {
            tid: 4,
            defs: vec![def(4, Var::new("y", Type::Int(32)), Exp::Var(var()))],
            ..Blk::new(4)
        });
        sub.blks.push(Blk {
            tid: 99,
            defs: vec![def(99, var(), int(7))],
            ..Blk::new(99)
        });
        sub
    }

    #[test]
    fn dominators_liveness_and_pruning() {
        let cfg = Cfg::from_sub(&sample());
        assert!(cfg.reachable().contains(&3));
        assert_eq!(cfg.immediate_dominators().get(&3), Some(&2));
        let (_, outs) = cfg.liveness();
        assert!(!outs[&1].contains(&var()));
        assert!(outs[&2].contains(&var()));
        assert!(!outs[&3].contains(&var()));
    }

    #[test]
    fn constant_propagation_and_iterative_dce() {
        let propagated = propagate_constants(&Cfg::from_sub(&sample()));
        assert_eq!(propagated.block(3).unwrap().defs[0].rhs, int(2));
        let optimized = optimize(&sample());
        assert!(optimized.blks.iter().all(|block| block.defs.is_empty()));
    }

    #[test]
    fn ssa_merges_diamond_edges_and_preserves_disconnected_blocks() {
        let ssa = to_ssa(&diamond());
        assert!(ssa.blk(99).is_some());
        let join = ssa.blk(4).unwrap();
        assert_eq!(join.phis.len(), 1);
        let phi = &join.phis[0];
        let left = phi.values[&2].clone();
        let right = phi.values[&3].clone();
        assert_ne!(left, right);
        assert!(matches!(left, Exp::Var(ref var) if var.index.is_some()));
        assert!(matches!(right, Exp::Var(ref var) if var.index.is_some()));
        assert_eq!(join.defs[0].rhs, Exp::Var(phi.var.clone()));
        let cfg = Cfg::from_sub(&ssa);
        let (_, outs) = cfg.liveness();
        assert_eq!(outs[&2].len(), 1);
        assert!(outs[&2].contains(&cfg.block(2).unwrap().defs[0].var));
        assert_eq!(outs[&3].len(), 1);
        assert!(outs[&3].contains(&cfg.block(3).unwrap().defs[0].var));
    }

    #[test]
    fn calls_only_continue_to_their_return_block() {
        let mut sub = sample();
        sub.blks[0].jmps = vec![Jmp {
            tid: 1,
            condition: None,
            kind: JmpKind::Call {
                target: Label::Direct(99),
                return_to: Some(Label::Direct(2)),
            },
        }];
        let cfg = Cfg::from_sub(&sub);
        assert_eq!(cfg.successors(1), &BTreeSet::from([2]));
    }
}
