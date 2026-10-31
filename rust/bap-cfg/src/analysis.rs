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
    eliminate_dead_code_protected(cfg, &BTreeSet::new())
}

/// Removes definitions and phis whose variable isn't read later. In each block the last otherwise
/// dead assignment to a base variable in `protected` stays, as in `compute_dead` of the optimization
/// plugin, since a variable that may be read outside of the subroutine has to keep its value at the
/// exit of any block.
pub fn eliminate_dead_code_protected(cfg: &Cfg, protected: &BTreeSet<Var>) -> Cfg {
    let mut cfg = cfg.clone();
    loop {
        let previous = cfg.clone();
        let (_, outs) = cfg.liveness();
        for block in cfg.blocks.values_mut() {
            let mut live = outs.get(&block.tid).cloned().unwrap_or_default();
            live.extend(block.jmps.iter().flat_map(|jmp| jmp.free_vars()));
            let mut protected = protected.clone();
            let mut kept = Vec::with_capacity(block.defs.len());
            for def in block.defs.drain(..).rev() {
                let keep = live.contains(&def.var)
                    || has_side_effect(&def.rhs)
                    || protected.remove(&def.var.base());
                if keep {
                    live.remove(&def.var);
                    live.extend(def.rhs.free_vars());
                    kept.push(def);
                }
            }
            kept.reverse();
            block.defs = kept;
            block
                .phis
                .retain(|phi| live.contains(&phi.var) || protected.remove(&phi.var.base()));
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

type ConstEnv = BTreeMap<Var, BitVec>;

fn constant_replacements(environment: &ConstEnv) -> BTreeMap<Var, Exp> {
    environment
        .iter()
        .map(|(var, value)| (var.clone(), Exp::Int(value.clone())))
        .collect()
}

/// Rewrites a block under the constants known at its entry and returns the constants known at its
/// exit. A phi assigns its variable on entry, so an incoming constant for it no longer holds.
fn propagate_block(block: &Blk, environment: &ConstEnv) -> (Blk, ConstEnv) {
    let mut block = block.clone();
    let mut environment = environment.clone();
    for phi in &mut block.phis {
        environment.remove(&phi.var);
        for value in phi.values.values_mut() {
            *value = simplify_exp(value);
        }
    }
    for def in &mut block.defs {
        def.rhs = simplify_exp(&def.rhs.substitute(&constant_replacements(&environment)));
        if let Exp::Int(value) = &def.rhs {
            environment.insert(def.var.clone(), value.clone());
        } else {
            environment.remove(&def.var);
        }
    }
    let replacements = constant_replacements(&environment);
    for jmp in &mut block.jmps {
        if let Some(condition) = &mut jmp.condition {
            *condition = simplify_exp(&condition.substitute(&replacements));
        }
        substitute_jmp_targets(jmp, &replacements);
    }
    (block, environment)
}

/// Constants known on entry: nothing at the start, whose entry state is unconstrained even when it
/// has predecessors, otherwise the join over the predecessors analysed so far.
fn entry_constants(
    cfg: &Cfg,
    exits: &BTreeMap<bap_bir::Tid, ConstEnv>,
    tid: bap_bir::Tid,
) -> ConstEnv {
    if tid == cfg.start {
        return ConstEnv::new();
    }
    let predecessors = cfg.predecessors(tid);
    let mut incoming = predecessors.iter().filter_map(|pred| exits.get(pred));
    let mut environment = incoming.next().cloned().unwrap_or_default();
    for predecessor in incoming {
        environment.retain(|var, value| predecessor.get(var) == Some(value));
    }
    environment
}

/// Rewrites each block once, after the analysis reached a fixpoint, so a constant is used only if it
/// holds on every path into the block. Rewriting during the analysis would keep what an optimistic
/// first visit assumed. If the analysis runs out of steps only constants local to a block are used.
pub fn propagate_constants(cfg: &Cfg) -> Cfg {
    let mut cfg = cfg.prune();
    let variables = cfg
        .blocks
        .values()
        .flat_map(|block| block.defined_vars().into_iter().chain(block.free_vars()))
        .collect::<BTreeSet<_>>()
        .len();
    let edges = cfg.edges.values().map(BTreeSet::len).sum::<usize>();
    let mut steps = (variables + 2) * (cfg.blocks.len() + 2) * (edges + 2);
    let mut exits = BTreeMap::<bap_bir::Tid, ConstEnv>::new();
    let mut work = vec![cfg.start];
    while let Some(tid) = work.pop() {
        if steps == 0 {
            break;
        }
        steps -= 1;
        let Some(block) = cfg.block(tid) else {
            continue;
        };
        let (_, environment) = propagate_block(block, &entry_constants(&cfg, &exits, tid));
        if exits.get(&tid) != Some(&environment) {
            exits.insert(tid, environment);
            work.extend(cfg.successors(tid));
        }
    }
    let solved = cfg.blocks.iter().all(|(tid, block)| {
        let (_, environment) = propagate_block(block, &entry_constants(&cfg, &exits, *tid));
        exits.get(tid) == Some(&environment)
    });
    let rewritten = cfg
        .blocks
        .iter()
        .map(|(tid, block)| {
            let entry = if solved {
                entry_constants(&cfg, &exits, *tid)
            } else {
                ConstEnv::new()
            };
            (*tid, propagate_block(block, &entry).0)
        })
        .collect();
    cfg.blocks = rewritten;
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
    optimize_protected(sub, &BTreeSet::new())
}

/// As [`optimize`], keeping the assignments to `protected`, see [`eliminate_dead_code_protected`].
pub fn optimize_protected(sub: &Sub, protected: &BTreeSet<Var>) -> Sub {
    let cfg = Cfg::from_sub(sub).prune();
    let cfg = propagate_constants(&cfg);
    eliminate_dead_code_protected(&cfg, protected).into_sub(sub)
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
        // one entry per name pushed below, a set would leave stale names for the siblings
        let pushed = block
            .phis
            .iter()
            .map(|phi| phi.var.base())
            .chain(block.defs.iter().map(|def| def.var.base()))
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
        self.pop(&pushed);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{PSEUDO_EXIT, PSEUDO_START};
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

    fn y() -> Var {
        Var::new("y", Type::Int(32))
    }
    fn z() -> Var {
        Var::new("z", Type::Int(32))
    }
    fn blk(tid: u64, defs: Vec<Def>, jmps: Vec<Jmp>) -> Blk {
        Blk {
            tid,
            defs,
            jmps,
            ..Blk::new(tid)
        }
    }
    fn branch(tid: u64, condition: Exp, destination: u64) -> Jmp {
        Jmp {
            condition: Some(condition),
            ..goto(tid, destination)
        }
    }
    fn ret(tid: u64, target: Exp) -> Jmp {
        Jmp {
            tid,
            condition: None,
            kind: JmpKind::Return(Label::Indirect(target)),
        }
    }
    fn sub_of(blks: Vec<Blk>) -> Sub {
        let mut sub = Sub::new(1, "regression");
        sub.blks = blks;
        sub
    }
    fn is_var(exp: &Exp, var: &Var) -> bool {
        matches!(exp, Exp::Var(found) if found == var)
    }

    #[test]
    fn ssa_pops_one_name_per_definition() {
        // blocks 2 and 3 are siblings, block 2 assigns x twice and block 3 reads x
        let sub = sub_of(vec![
            blk(1, vec![], vec![goto(1, 2), goto(2, 3)]),
            blk(
                2,
                vec![def(3, var(), int(1)), def(4, var(), int(2))],
                vec![],
            ),
            blk(3, vec![def(5, y(), Exp::Var(var()))], vec![]),
        ]);
        let ssa = to_ssa(&sub);
        let second = ssa.blk(2).unwrap();
        assert_ne!(second.defs[0].var, second.defs[1].var);
        assert_eq!(ssa.blk(3).unwrap().defs[0].rhs, Exp::Var(var()));
    }

    #[test]
    fn ssa_pops_the_name_of_a_phi_and_a_definition() {
        // the join defines x by a phi and by a definition, and its sibling reads x
        let sub = sub_of(vec![
            blk(
                1,
                vec![def(1, var(), int(0))],
                vec![goto(1, 2), goto(2, 3), goto(3, 5)],
            ),
            blk(2, vec![def(4, var(), int(1))], vec![goto(5, 4)]),
            blk(3, vec![], vec![goto(6, 4)]),
            blk(4, vec![def(7, var(), int(2))], vec![]),
            blk(5, vec![def(8, y(), Exp::Var(var()))], vec![]),
        ]);
        let ssa = to_ssa(&sub);
        assert_eq!(ssa.blk(4).unwrap().phis.len(), 1);
        let entry = ssa.blk(1).unwrap().defs[0].var.clone();
        assert_eq!(ssa.blk(5).unwrap().defs[0].rhs, Exp::Var(entry));
    }

    #[test]
    fn liveness_seed_reaches_predecessors() {
        let sub = sub_of(vec![
            blk(1, vec![], vec![goto(1, 2)]),
            blk(2, vec![def(2, y(), int(1))], vec![goto(3, 3)]),
            blk(3, vec![], vec![]),
        ]);
        let keep = BTreeSet::from([var(), y()]);
        let cfg = Cfg::connected(&sub);
        let (ins, outs) = cfg.liveness_from(PSEUDO_EXIT, keep.clone());
        assert_eq!(ins[&PSEUDO_EXIT], keep);
        assert_eq!(outs[&PSEUDO_EXIT], keep);
        assert_eq!(ins[&3], keep);
        assert_eq!(outs[&2], keep);
        // a definition kills the seed on the way up
        assert_eq!(ins[&2], BTreeSet::from([var()]));
        assert_eq!(ins[&1], BTreeSet::from([var()]));
        assert_eq!(outs[&PSEUDO_START], BTreeSet::from([var()]));
    }

    #[test]
    fn liveness_seed_adds_to_what_the_successors_need() {
        // the seeded block has a successor, whose reads stay live
        let sub = sub_of(vec![
            blk(1, vec![], vec![goto(1, 2)]),
            blk(2, vec![def(2, y(), Exp::Var(z()))], vec![]),
        ]);
        let (ins, outs) = Cfg::from_sub(&sub).liveness_from(1, BTreeSet::from([var()]));
        assert_eq!(outs[&1], BTreeSet::from([var(), z()]));
        assert_eq!(ins[&1], BTreeSet::from([var(), z()]));
    }

    #[test]
    fn dead_code_keeps_a_definition_read_later_in_its_block() {
        let sub = sub_of(vec![
            blk(
                1,
                vec![def(1, var(), Exp::Var(z())), def(2, y(), Exp::Var(var()))],
                vec![goto(3, 2)],
            ),
            blk(2, vec![], vec![ret(4, Exp::Var(y()))]),
        ]);
        let cfg = eliminate_dead_code(&Cfg::from_sub(&sub));
        let vars = cfg.block(1).unwrap().defs.iter().map(|d| d.var.clone());
        assert_eq!(vars.collect::<Vec<_>>(), vec![var(), y()]);
    }

    #[test]
    fn dead_code_keeps_a_definition_read_by_a_jump_of_its_block() {
        let sub = sub_of(vec![blk(
            1,
            vec![def(1, var(), Exp::Var(z()))],
            vec![ret(2, Exp::Var(var()))],
        )]);
        let cfg = eliminate_dead_code(&Cfg::from_sub(&sub));
        assert_eq!(cfg.block(1).unwrap().defs.len(), 1);
    }

    #[test]
    fn dead_code_removes_an_overwritten_definition() {
        let sub = sub_of(vec![blk(
            1,
            vec![def(1, var(), Exp::Var(z())), def(2, var(), Exp::Var(y()))],
            vec![ret(3, Exp::Var(var()))],
        )]);
        let cfg = eliminate_dead_code(&Cfg::from_sub(&sub));
        let defs = &cfg.block(1).unwrap().defs;
        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].tid, 2);
    }

    #[test]
    fn dead_code_accepts_unreachable_blocks() {
        let sub = sub_of(vec![
            blk(1, vec![], vec![]),
            blk(2, vec![def(1, var(), int(1))], vec![]),
        ]);
        assert!(eliminate_dead_code(&Cfg::from_sub(&sub)).block(2).is_some());
    }

    #[test]
    fn dead_code_keeps_the_last_assignment_to_a_protected_variable() {
        let sub = sub_of(vec![blk(
            1,
            vec![
                def(1, var(), int(1)),
                def(2, var(), int(2)),
                def(3, y(), int(3)),
            ],
            vec![],
        )]);
        let cfg = Cfg::from_sub(&sub);
        assert!(eliminate_dead_code(&cfg).block(1).unwrap().defs.is_empty());
        let protected = BTreeSet::from([var()]);
        let kept = eliminate_dead_code_protected(&cfg, &protected);
        let defs = &kept.block(1).unwrap().defs;
        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].tid, 2);
        // the protection is by base variable, as the input of the plugin is in SSA
        let ssa = sub_of(vec![blk(1, vec![def(1, var().version(3), int(1))], vec![])]);
        let kept = eliminate_dead_code_protected(&Cfg::from_sub(&ssa), &protected);
        assert_eq!(kept.block(1).unwrap().defs.len(), 1);
    }

    #[test]
    fn dead_code_keeps_what_a_protected_assignment_reads() {
        let sub = sub_of(vec![blk(
            1,
            vec![def(1, y(), Exp::Var(z())), def(2, var(), Exp::Var(y()))],
            vec![],
        )]);
        let kept = eliminate_dead_code_protected(&Cfg::from_sub(&sub), &BTreeSet::from([var()]));
        assert_eq!(kept.block(1).unwrap().defs.len(), 2);
    }

    #[test]
    fn optimize_protected_keeps_writes_at_the_exit() {
        let sub = sub_of(vec![blk(1, vec![def(1, var(), Exp::Var(z()))], vec![])]);
        assert!(optimize(&sub).blks[0].defs.is_empty());
        let kept = optimize_protected(&sub, &BTreeSet::from([var()]));
        assert_eq!(kept.blks[0].defs.len(), 1);
    }

    #[test]
    fn frontier_contains_the_start_of_a_loop() {
        let sub = sub_of(vec![
            blk(1, vec![], vec![goto(1, 2)]),
            blk(2, vec![], vec![goto(2, 3)]),
            blk(3, vec![], vec![goto(3, 1)]),
        ]);
        let frontier = Cfg::from_sub(&sub).dominance_frontier();
        for tid in [1, 2, 3] {
            assert_eq!(frontier[&tid], BTreeSet::from([1]));
        }
    }

    #[test]
    fn frontier_of_a_diamond_is_unchanged() {
        let frontier = Cfg::from_sub(&diamond()).dominance_frontier();
        assert_eq!(frontier[&2], BTreeSet::from([4]));
        assert_eq!(frontier[&3], BTreeSet::from([4]));
        assert!(!frontier.contains_key(&1));
        assert!(!frontier.contains_key(&4));
    }

    #[test]
    fn ssa_of_a_loop_at_the_entry_is_connected_through_the_pseudo_start() {
        let sub = sub_of(vec![blk(
            1,
            vec![def(1, y(), Exp::Var(var())), def(2, var(), int(1))],
            vec![branch(3, Exp::Var(z()), 1)],
        )]);
        let ssa = to_ssa(&sub);
        // x and y are assigned in the loop, whose header joins the pseudo start and the back edge
        assert_eq!(ssa.blk(1).unwrap().phis.len(), 2);
    }

    #[test]
    fn constants_are_not_folded_from_the_first_iteration_of_a_loop() {
        let sub = sub_of(vec![
            blk(1, vec![def(1, var(), int(1))], vec![goto(2, 2)]),
            blk(
                2,
                vec![def(3, y(), Exp::Var(var())), def(4, var(), int(2))],
                vec![branch(5, Exp::Var(z()), 2), goto(6, 3)],
            ),
            blk(3, vec![], vec![ret(7, Exp::Var(y()))]),
        ]);
        let cfg = propagate_constants(&Cfg::from_sub(&sub));
        assert!(is_var(&cfg.block(2).unwrap().defs[0].rhs, &var()));
    }

    #[test]
    fn constants_stable_around_a_loop_are_folded() {
        let sub = sub_of(vec![
            blk(1, vec![def(1, var(), int(1))], vec![goto(2, 2)]),
            blk(
                2,
                vec![def(3, y(), Exp::Var(var()))],
                vec![branch(4, Exp::Var(z()), 2), goto(5, 3)],
            ),
            blk(3, vec![], vec![]),
        ]);
        let cfg = propagate_constants(&Cfg::from_sub(&sub));
        assert_eq!(cfg.block(2).unwrap().defs[0].rhs, int(1));
    }

    #[test]
    fn constants_are_not_assumed_at_the_entry() {
        // on the first iteration x is whatever the caller passed
        let sub = sub_of(vec![blk(
            1,
            vec![def(1, y(), Exp::Var(var())), def(2, var(), int(1))],
            vec![branch(3, Exp::Var(z()), 1)],
        )]);
        let cfg = propagate_constants(&Cfg::from_sub(&sub));
        assert!(is_var(&cfg.block(1).unwrap().defs[0].rhs, &var()));
    }

    #[test]
    fn a_phi_invalidates_an_incoming_constant() {
        let mut join = blk(2, vec![def(2, y(), Exp::Var(var()))], vec![]);
        join.phis.push(bap_bir::Phi {
            tid: 3,
            var: var(),
            values: BTreeMap::from([(1, Exp::Var(z()))]),
        });
        let sub = sub_of(vec![
            blk(1, vec![def(1, var(), int(1))], vec![goto(4, 2)]),
            join,
        ]);
        let cfg = propagate_constants(&Cfg::from_sub(&sub));
        assert!(is_var(&cfg.block(2).unwrap().defs[0].rhs, &var()));
    }

    #[test]
    fn optimize_keeps_the_entry_first() {
        // the entry has the largest tid, and the first block is what makes it the entry
        let sub = sub_of(vec![
            blk(9, vec![], vec![goto(1, 2)]),
            blk(2, vec![], vec![]),
        ]);
        let tids = optimize(&sub)
            .blks
            .iter()
            .map(|b| b.tid)
            .collect::<Vec<_>>();
        assert_eq!(tids, vec![9, 2]);
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
