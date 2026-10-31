import Bap.IR.Syntax
import Bap.Graph.Fast

namespace Bap.IR

structure Cfg where
  start : Tid
  blocks : List Blk := []
  graph : Bap.Graph.Graph Tid
  deriving Repr

def Label.directTarget : Label → Option Tid
  | .direct tid => some tid
  | .indirect _ => none

def Jmp.successors (jmp : Jmp) : List Tid :=
  match jmp.kind with
  | .goto target | .ret target => target.directTarget.toList
  | .call _ returnTo => (returnTo.bind Label.directTarget).toList
  | .interrupt _ returnTo => [returnTo]

def Blk.successors (blk : Blk) : List Tid :=
  blk.jmps.flatMap Jmp.successors |>.eraseDups

def Sub.block (sub : Sub) (tid : Tid) : Option Blk :=
  sub.blks.find? fun blk => blk.tid = tid

def Program.sub (program : Program) (tid : Tid) : Option Sub :=
  program.subs.find? fun sub => sub.tid = tid

def Cfg.fromSub (sub : Sub) : Cfg :=
  {
    start := sub.blks.head?.map Blk.tid |>.getD 0
    blocks := sub.blks
    graph := {
      nodes := sub.blks.map Blk.tid
      edges := sub.blks.flatMap fun blk => blk.successors.map (blk.tid, ·)
    }
  }

def Cfg.block (cfg : Cfg) (tid : Tid) : Option Blk :=
  cfg.blocks.find? fun blk => blk.tid = tid

def Cfg.successors (cfg : Cfg) (tid : Tid) : List Tid := Bap.Graph.successors cfg.graph tid
def Cfg.predecessors (cfg : Cfg) (tid : Tid) : List Tid := Bap.Graph.predecessors cfg.graph tid
def Cfg.reachable (cfg : Cfg) : List Tid := Bap.Graph.reachable cfg.graph cfg.start

private def Cfg.reachableFast (cfg : Cfg) : List Tid := Bap.Graph.Fast.reachable cfg.graph cfg.start

@[csimp] private theorem Cfg.reachable_eq_fast : @Cfg.reachable = @Cfg.reachableFast :=
  funext fun cfg => (Bap.Graph.Fast.reachable_eq cfg.graph cfg.start).symm

def Cfg.prune (cfg : Cfg) : Cfg :=
  let graph := Bap.Graph.prune cfg.graph cfg.start
  { cfg with
    blocks := cfg.blocks.filter fun blk => blk.tid ∈ graph.nodes
    graph := graph
  }

private def Cfg.pruneFast (cfg : Cfg) : Cfg :=
  let keep : Std.HashSet Tid := Std.HashSet.ofList (Bap.Graph.Fast.reachable cfg.graph cfg.start)
  { cfg with
    blocks := cfg.blocks.filter fun blk => keep.contains blk.tid
    graph := {
      nodes := cfg.graph.nodes.filter keep.contains
      edges := cfg.graph.edges.filter fun edge => keep.contains edge.1 && keep.contains edge.2
    }
  }

@[csimp] private theorem Cfg.prune_eq_fast : @Cfg.prune = @Cfg.pruneFast := by
  funext cfg
  have hkeep : ∀ tid, (Std.HashSet.ofList (Bap.Graph.Fast.reachable cfg.graph cfg.start)).contains tid =
      decide (tid ∈ Bap.Graph.reachable cfg.graph cfg.start) := by
    intro tid
    rw [Bap.Graph.Fast.reachable_eq, Bool.eq_iff_iff]
    simp [Std.HashSet.contains_ofList]
  simp only [Cfg.prune, Cfg.pruneFast, Bap.Graph.prune, hkeep]
  congr 1
  · apply List.filter_congr
    intro blk _
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, List.mem_filter, and_iff_right_iff_imp]
    exact fun h => Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ h
  · congr 1
    apply List.filter_congr
    intro node _
    rw [hkeep]

def Cfg.dominators (cfg : Cfg) : List (Tid × List Tid) := Bap.Graph.dominators cfg.graph cfg.start

def Cfg.immediateDominators (cfg : Cfg) : List (Tid × Tid) :=
  Bap.Graph.immediateDominators cfg.graph cfg.start

def Cfg.dominanceFrontier (cfg : Cfg) : List (Tid × List Tid) :=
  Bap.Graph.dominanceFrontier cfg.graph cfg.start

private def Cfg.dominatorsFast (cfg : Cfg) : List (Tid × List Tid) := Bap.Graph.Fast.dominators cfg.graph cfg.start

private def Cfg.immediateDominatorsFast (cfg : Cfg) : List (Tid × Tid) :=
  Bap.Graph.Fast.immediateDominators cfg.graph cfg.start

private def Cfg.dominanceFrontierFast (cfg : Cfg) : List (Tid × List Tid) :=
  Bap.Graph.Fast.dominanceFrontier cfg.graph cfg.start

@[csimp] private theorem Cfg.dominators_eq_fast : @Cfg.dominators = @Cfg.dominatorsFast :=
  funext fun cfg => (Bap.Graph.Fast.dominators_eq cfg.graph cfg.start).symm

@[csimp] private theorem Cfg.immediateDominators_eq_fast : @Cfg.immediateDominators = @Cfg.immediateDominatorsFast :=
  funext fun cfg => (Bap.Graph.Fast.immediateDominators_eq cfg.graph cfg.start).symm

@[csimp] private theorem Cfg.dominanceFrontier_eq_fast : @Cfg.dominanceFrontier = @Cfg.dominanceFrontierFast :=
  funext fun cfg => (Bap.Graph.Fast.dominanceFrontier_eq cfg.graph cfg.start).symm

def Cfg.intoSub (cfg : Cfg) (sub : Sub) : Sub := { sub with blks := cfg.blocks }

def pseudoStart : Tid := 0xffffffffffffffff
def pseudoExit : Tid := 0xfffffffffffffffe

def Cfg.updateBlock (cfg : Cfg) (tid : Tid) (f : Blk → Blk) : Cfg :=
  { cfg with blocks := cfg.blocks.map fun blk => if blk.tid = tid then f blk else blk }

private def reverseGraph (graph : Bap.Graph.Graph Tid) : Bap.Graph.Graph Tid :=
  { graph with edges := graph.edges.map fun edge => (edge.2, edge.1) }

private def connectMissingStarts (actual : List Tid) (cfg : Cfg) : Nat → Cfg
  | 0 => cfg
  | fuel + 1 =>
    let reachable := cfg.reachable
    match actual.find? fun tid => tid ∉ reachable with
    | none => cfg
    | some tid =>
      let cfg := { cfg with graph := { cfg.graph with edges := (pseudoStart, tid) :: cfg.graph.edges } }
      connectMissingStarts actual cfg fuel

private def connectMissingExits (actual : List Tid) (cfg : Cfg) : Nat → Cfg
  | 0 => cfg
  | fuel + 1 =>
    let coReachable := Bap.Graph.reachable (reverseGraph cfg.graph) pseudoExit
    match actual.find? fun tid => tid ∉ coReachable with
    | none => cfg
    | some tid =>
      let cfg := { cfg with graph := { cfg.graph with edges := (tid, pseudoExit) :: cfg.graph.edges } }
      connectMissingExits actual cfg fuel

private def connectMissingStartsFast (actual : List Tid) (cfg : Cfg) : Nat → Cfg
  | 0 => cfg
  | fuel + 1 =>
    let reachable : Std.HashSet Tid := Std.HashSet.ofList (Bap.Graph.Fast.reachable cfg.graph cfg.start)
    match actual.find? fun tid => !reachable.contains tid with
    | none => cfg
    | some tid =>
      let cfg := { cfg with graph := { cfg.graph with edges := (pseudoStart, tid) :: cfg.graph.edges } }
      connectMissingStartsFast actual cfg fuel

private def connectMissingExitsFast (actual : List Tid) (cfg : Cfg) : Nat → Cfg
  | 0 => cfg
  | fuel + 1 =>
    let coReachable : Std.HashSet Tid := Std.HashSet.ofList (Bap.Graph.Fast.reachable (reverseGraph cfg.graph) pseudoExit)
    match actual.find? fun tid => !coReachable.contains tid with
    | none => cfg
    | some tid =>
      let cfg := { cfg with graph := { cfg.graph with edges := (tid, pseudoExit) :: cfg.graph.edges } }
      connectMissingExitsFast actual cfg fuel

private theorem find_not_mem_eq (actual seen : List Tid) :
    (actual.find? fun tid => !(Std.HashSet.ofList seen).contains tid) = actual.find? fun tid => decide (tid ∉ seen) := by
  congr 1
  funext tid
  simp [Std.HashSet.contains_ofList]

@[csimp] private theorem connectMissingStarts_eq_fast : @connectMissingStarts = @connectMissingStartsFast := by
  funext actual cfg fuel
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
    simp only [connectMissingStarts, connectMissingStartsFast, Bap.Graph.Fast.reachable_eq, find_not_mem_eq, ih]
    rfl

@[csimp] private theorem connectMissingExits_eq_fast : @connectMissingExits = @connectMissingExitsFast := by
  funext actual cfg fuel
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
    simp only [connectMissingExits, connectMissingExitsFast, Bap.Graph.Fast.reachable_eq, find_not_mem_eq, ih]
    try rfl

def Cfg.connected (sub : Sub) : Cfg :=
  let base := Cfg.fromSub sub
  let actual := sub.blks.map Blk.tid
  -- Execution enters at the first block, which therefore has an edge from the pseudo start even when
  -- it also has predecessors, or another root could wrongly appear to dominate it.
  let roots := actual.head?.toList ++ actual.filter fun tid => (base.predecessors tid).isEmpty
  let leaves := actual.filter fun tid => (base.successors tid).isEmpty
  let cfg : Cfg := {
    start := pseudoStart
    blocks := ⟨pseudoStart, [], [], []⟩ :: base.blocks ++ [⟨pseudoExit, [], [], []⟩]
    graph := {
      nodes := pseudoStart :: actual ++ [pseudoExit]
      edges := base.graph.edges ++ roots.map (pseudoStart, ·) ++ leaves.map (·, pseudoExit)
    }
  }
  let cfg := connectMissingStarts actual cfg (actual.length + 1)
  connectMissingExits actual cfg (actual.length + 1)

private theorem connectMissingStarts_start (actual : List Tid) (cfg : Cfg) (fuel : Nat) :
    (connectMissingStarts actual cfg fuel).start = cfg.start := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
    simp only [connectMissingStarts]
    split
    · rfl
    · exact ih _

private theorem connectMissingExits_start (actual : List Tid) (cfg : Cfg) (fuel : Nat) :
    (connectMissingExits actual cfg fuel).start = cfg.start := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
    simp only [connectMissingExits]
    split
    · rfl
    · exact ih _

@[simp] theorem connected_start (sub : Sub) : (Cfg.connected sub).start = pseudoStart := by
  simp [Cfg.connected, connectMissingStarts_start, connectMissingExits_start]

end Bap.IR
