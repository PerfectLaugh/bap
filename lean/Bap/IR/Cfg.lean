import Bap.IR.Syntax
import Bap.Graph.Basic

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

def Cfg.prune (cfg : Cfg) : Cfg :=
  let graph := Bap.Graph.prune cfg.graph cfg.start
  { cfg with
    blocks := cfg.blocks.filter fun blk => blk.tid ∈ graph.nodes
    graph := graph
  }

def Cfg.dominators (cfg : Cfg) : List (Tid × List Tid) := Bap.Graph.dominators cfg.graph cfg.start

def Cfg.immediateDominators (cfg : Cfg) : List (Tid × Tid) :=
  Bap.Graph.immediateDominators cfg.graph cfg.start

def Cfg.dominanceFrontier (cfg : Cfg) : List (Tid × List Tid) :=
  Bap.Graph.dominanceFrontier cfg.graph cfg.start

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

def Cfg.connected (sub : Sub) : Cfg :=
  let base := Cfg.fromSub sub
  let actual := sub.blks.map Blk.tid
  let roots := actual.filter fun tid => (base.predecessors tid).isEmpty
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
