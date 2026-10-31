use bap_bir::{Blk, Sub, Tid};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq)]
pub struct Cfg {
    pub start: Tid,
    pub blocks: BTreeMap<Tid, Blk>,
    pub edges: BTreeMap<Tid, BTreeSet<Tid>>,
}
impl Cfg {
    pub fn from_sub(sub: &Sub) -> Self {
        let start = sub.blks.first().map_or(0, |blk| blk.tid);
        let blocks = sub
            .blks
            .iter()
            .map(|blk| (blk.tid, blk.clone()))
            .collect::<BTreeMap<_, _>>();
        let edges = sub
            .blks
            .iter()
            .map(|blk| (blk.tid, blk.successors()))
            .collect();
        Self {
            start,
            blocks,
            edges,
        }
    }
    pub fn connected(sub: &Sub) -> Self {
        let actual = sub.blks.iter().map(|blk| blk.tid).collect::<BTreeSet<_>>();
        let mut cfg = Self::from_sub(sub);
        cfg.start = PSEUDO_START;
        cfg.blocks.insert(PSEUDO_START, Blk::new(PSEUDO_START));
        cfg.blocks.insert(PSEUDO_EXIT, Blk::new(PSEUDO_EXIT));
        cfg.edges.insert(PSEUDO_START, BTreeSet::new());
        cfg.edges.insert(PSEUDO_EXIT, BTreeSet::new());
        for tid in &actual {
            if cfg.predecessors(*tid).is_empty() {
                cfg.edges.entry(PSEUDO_START).or_default().insert(*tid);
            }
            if cfg.successors(*tid).is_empty() {
                cfg.edges.entry(*tid).or_default().insert(PSEUDO_EXIT);
            }
        }
        loop {
            let reachable = cfg.reachable();
            let missing = actual.difference(&reachable).next().copied();
            let Some(tid) = missing else { break };
            cfg.edges.entry(PSEUDO_START).or_default().insert(tid);
        }
        loop {
            let mut reachable = BTreeSet::from([PSEUDO_EXIT]);
            let mut work = vec![PSEUDO_EXIT];
            while let Some(tid) = work.pop() {
                for pred in cfg.predecessors(tid) {
                    if reachable.insert(pred) {
                        work.push(pred);
                    }
                }
            }
            let missing = actual.difference(&reachable).next().copied();
            let Some(tid) = missing else { break };
            cfg.edges.entry(tid).or_default().insert(PSEUDO_EXIT);
        }
        cfg
    }
    /// Keeps the block order of `sub`, whose first block is the entry. Blocks that `sub` doesn't
    /// have follow in tid order.
    pub fn into_sub(self, sub: &Sub) -> Sub {
        let mut blocks = self.blocks;
        let mut blks = sub
            .blks
            .iter()
            .filter_map(|blk| blocks.remove(&blk.tid))
            .collect::<Vec<_>>();
        blks.extend(blocks.into_values());
        Sub {
            blks,
            ..sub.clone()
        }
    }
    pub fn block(&self, tid: Tid) -> Option<&Blk> {
        self.blocks.get(&tid)
    }
    pub fn block_mut(&mut self, tid: Tid) -> Option<&mut Blk> {
        self.blocks.get_mut(&tid)
    }
    pub fn successors(&self, tid: Tid) -> &BTreeSet<Tid> {
        self.edges.get(&tid).unwrap_or(&EMPTY)
    }
    pub fn predecessors(&self, tid: Tid) -> BTreeSet<Tid> {
        self.edges
            .iter()
            .filter(|(_, targets)| targets.contains(&tid))
            .map(|(source, _)| *source)
            .collect()
    }
    pub fn reachable(&self) -> BTreeSet<Tid> {
        let mut seen = BTreeSet::new();
        let mut work = vec![self.start];
        while let Some(tid) = work.pop() {
            if self.blocks.contains_key(&tid) && seen.insert(tid) {
                work.extend(self.successors(tid));
            }
        }
        seen
    }
    pub fn prune(&self) -> Self {
        let reachable = self.reachable();
        Self {
            start: self.start,
            blocks: self
                .blocks
                .iter()
                .filter(|(tid, _)| reachable.contains(tid))
                .map(|(tid, blk)| (*tid, blk.clone()))
                .collect(),
            edges: self
                .edges
                .iter()
                .filter(|(tid, _)| reachable.contains(tid))
                .map(|(tid, targets)| (*tid, targets.intersection(&reachable).copied().collect()))
                .collect(),
        }
    }
    pub fn dominators(&self) -> BTreeMap<Tid, BTreeSet<Tid>> {
        let reachable = self.reachable();
        let mut dom = reachable
            .iter()
            .map(|tid| {
                (
                    *tid,
                    if *tid == self.start {
                        BTreeSet::from([*tid])
                    } else {
                        reachable.clone()
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        loop {
            let mut changed = false;
            for tid in &reachable {
                if *tid == self.start {
                    continue;
                }
                let mut predecessors = self
                    .predecessors(*tid)
                    .into_iter()
                    .filter(|pred| reachable.contains(pred));
                let Some(first) = predecessors.next() else {
                    continue;
                };
                let mut new = dom[&first].clone();
                for pred in predecessors {
                    new = new.intersection(&dom[&pred]).copied().collect();
                }
                new.insert(*tid);
                if new != dom[tid] {
                    dom.insert(*tid, new);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        dom
    }
    pub fn immediate_dominators(&self) -> BTreeMap<Tid, Tid> {
        let dom = self.dominators();
        let mut result = BTreeMap::new();
        for tid in self.reachable() {
            if tid == self.start {
                continue;
            }
            let strict = dom[&tid].iter().filter(|candidate| **candidate != tid);
            if let Some(parent) = strict.max_by_key(|candidate| dom[candidate].len()) {
                result.insert(tid, *parent);
            }
        }
        result
    }
    /// A node without an immediate dominator (the start) has no node to stop at, so the walk from
    /// its predecessors ends after recording the root, as in `Dom_frontier_cooper` of graphlib.
    pub fn dominance_frontier(&self) -> BTreeMap<Tid, BTreeSet<Tid>> {
        let idom = self.immediate_dominators();
        let mut frontier = BTreeMap::<Tid, BTreeSet<Tid>>::new();
        for tid in self.reachable() {
            let stop = idom.get(&tid).copied();
            for pred in self.predecessors(tid) {
                let mut runner = pred;
                while Some(runner) != stop {
                    frontier.entry(runner).or_default().insert(tid);
                    let Some(next) = idom.get(&runner) else { break };
                    runner = *next;
                }
            }
        }
        frontier
    }
    pub fn liveness(
        &self,
    ) -> (
        BTreeMap<Tid, BTreeSet<bap_bir::Var>>,
        BTreeMap<Tid, BTreeSet<bap_bir::Var>>,
    ) {
        self.liveness_impl(None)
    }
    pub fn liveness_from(
        &self,
        exit: Tid,
        initial: BTreeSet<bap_bir::Var>,
    ) -> (
        BTreeMap<Tid, BTreeSet<bap_bir::Var>>,
        BTreeMap<Tid, BTreeSet<bap_bir::Var>>,
    ) {
        self.liveness_impl(Some((exit, initial)))
    }
    fn liveness_impl(
        &self,
        initial: Option<(Tid, BTreeSet<bap_bir::Var>)>,
    ) -> (
        BTreeMap<Tid, BTreeSet<bap_bir::Var>>,
        BTreeMap<Tid, BTreeSet<bap_bir::Var>>,
    ) {
        let reachable = self.reachable();
        let mut ins = reachable
            .iter()
            .map(|tid| (*tid, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        let mut outs = ins.clone();
        if let Some((exit, vars)) = &initial {
            outs.insert(*exit, vars.clone());
        }
        loop {
            let mut changed = false;
            for tid in reachable.iter().rev() {
                let block = &self.blocks[tid];
                let mut out = BTreeSet::new();
                for succ in self
                    .successors(*tid)
                    .iter()
                    .filter(|succ| self.blocks.contains_key(succ))
                {
                    let successor = &self.blocks[succ];
                    let phi_vars = successor
                        .phis
                        .iter()
                        .map(|phi| phi.var.clone())
                        .collect::<BTreeSet<_>>();
                    out.extend(ins[succ].difference(&phi_vars).cloned());
                    for phi in &successor.phis {
                        if let Some(value) = phi.values.get(tid) {
                            out.extend(value.free_vars());
                        }
                    }
                }
                if let Some((_, vars)) = initial.as_ref().filter(|(exit, _)| exit == tid) {
                    out.extend(vars.iter().cloned());
                }
                let mut input = BTreeSet::new();
                let mut defined = BTreeSet::new();
                for def in &block.defs {
                    input.extend(def.rhs.free_vars().difference(&defined).cloned());
                    defined.insert(def.var.clone());
                }
                for jmp in &block.jmps {
                    input.extend(jmp.free_vars());
                }
                input.extend(out.difference(&defined).cloned());
                if ins.get(tid) != Some(&input) || outs.get(tid) != Some(&out) {
                    ins.insert(*tid, input);
                    outs.insert(*tid, out);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        (ins, outs)
    }
}
pub const PSEUDO_START: Tid = u64::MAX;
pub const PSEUDO_EXIT: Tid = u64::MAX - 1;

static EMPTY: BTreeSet<Tid> = BTreeSet::new();
