import Bap.Core.Assoc

namespace Bap.Graph

structure Graph (α : Type) where
  nodes : List α := []
  edges : List (α × α) := []
  deriving Repr

variable {α : Type}

def successors [DecidableEq α] (graph : Graph α) (node : α) : List α :=
  (graph.edges.filter fun edge => edge.1 = node).map Prod.snd |>.eraseDups

def predecessors [DecidableEq α] (graph : Graph α) (node : α) : List α :=
  (graph.edges.filter fun edge => edge.2 = node).map Prod.fst |>.eraseDups

def intersect [DecidableEq α] (left right : List α) : List α :=
  left.filter fun value => value ∈ right

def subset [DecidableEq α] (left right : List α) : Bool :=
  left.all fun value => value ∈ right

def setEq [DecidableEq α] (left right : List α) : Bool :=
  subset left right && subset right left

private def closureStep [DecidableEq α] (graph : Graph α) (seen : List α) : List α :=
  let discovered := graph.nodes.filter fun node =>
    node ∉ seen ∧ (predecessors graph node).any fun pred => pred ∈ seen
  seen ++ discovered

private def closure [DecidableEq α] (graph : Graph α) : Nat → List α → List α
  | 0, seen => seen
  | fuel + 1, seen =>
    let next := closureStep graph seen
    if next = seen then seen else closure graph fuel next

def reachableFrom [DecidableEq α] (graph : Graph α) (seeds : List α) : List α :=
  closure graph (graph.nodes.length + 1) (seeds.filter fun node => node ∈ graph.nodes).eraseDups

def reachable [DecidableEq α] (graph : Graph α) (start : α) : List α :=
  reachableFrom graph [start]

def prune [DecidableEq α] (graph : Graph α) (start : α) : Graph α :=
  let keep := reachable graph start
  {
    nodes := graph.nodes.filter fun node => node ∈ keep
    edges := graph.edges.filter fun edge => edge.1 ∈ keep ∧ edge.2 ∈ keep
  }

private def initialDominators [DecidableEq α] (graph : Graph α) (start : α) : List (α × List α) :=
  let nodes := reachable graph start
  nodes.map fun node => (node, if node = start then [node] else nodes)

private def dominatorStep [DecidableEq α] (graph : Graph α) (start : α)
    (dominators : List (α × List α)) : List (α × List α) :=
  let nodes := reachable graph start
  dominators.map fun entry =>
    let node := entry.1
    if node = start then
      (node, [start])
    else
      let preds := (predecessors graph node).filter fun pred => pred ∈ nodes
      match preds with
      | [] => entry
      | _ =>
        let sets := preds.filterMap fun pred => Assoc.get pred dominators
        let common := sets.foldl (fun result values => intersect result values) nodes
        (node, node :: common |>.eraseDups)

private def dominatorsAux [DecidableEq α] (graph : Graph α) (start : α) :
    Nat → List (α × List α) → List (α × List α)
  | 0, dominators => dominators
  | fuel + 1, dominators =>
    let next := dominatorStep graph start dominators
    if next = dominators then dominators else dominatorsAux graph start fuel next

def dominators [DecidableEq α] (graph : Graph α) (start : α) : List (α × List α) :=
  let initial := initialDominators graph start
  dominatorsAux graph start (initial.length + 1) initial

def immediateDominators [DecidableEq α] (graph : Graph α) (start : α) : List (α × α) :=
  let dominators := dominators graph start
  dominators.filterMap fun entry =>
    let node := entry.1
    if node = start then
      none
    else
      let strict := entry.2.filter fun candidate => candidate != node
      strict.foldl (fun best candidate =>
        match best with
        | none => some (node, candidate)
        | some (_, current) =>
          let candidateSize := (Assoc.get candidate dominators).getD []
          let currentSize := (Assoc.get current dominators).getD []
          if candidateSize.length > currentSize.length then some (node, candidate) else best) none

/-- Walk up the dominator tree from `runner`. A node without an immediate dominator (the start) has
`stop = none`, and then the walk ends at the root after recording it, as in Cooper et al. -/
private def frontierWalk [DecidableEq α] (graph : Graph α) (idom : List (α × α))
    (stop : Option α) (tid : α) : Nat → α → List (α × α) → List (α × α)
  | 0, _, result => result
  | fuel + 1, runner, result =>
    if some runner = stop then
      result
    else
      let result := (runner, tid) :: result
      match Assoc.get runner idom with
      | some next => frontierWalk graph idom stop tid fuel next result
      | none => result

def dominanceFrontier [DecidableEq α] (graph : Graph α) (start : α) : List (α × List α) :=
  let idom := immediateDominators graph start
  let fuel := graph.nodes.length + 1
  let pairs := (reachable graph start).foldl (init := []) fun result tid =>
    (predecessors graph tid).foldl (fun result pred =>
      frontierWalk graph idom (Assoc.get tid idom) tid fuel pred result) result
  graph.nodes.map fun node => (node, (pairs.filter fun pair => pair.1 = node).map Prod.snd |>.eraseDups)

@[simp] theorem successors_mem [DecidableEq α] (graph : Graph α) (source target : α) :
    target ∈ successors graph source ↔ (source, target) ∈ graph.edges := by
  simp [successors]

theorem reachable_start [DecidableEq α] (graph : Graph α) (start : α) (h : start ∈ graph.nodes) :
    start ∈ reachable graph start := by
  simp [reachable, reachableFrom, h]
  exact closure_invariant (graph := graph) (fuel := graph.nodes.length + 1)
    [start].eraseDups (by simp)
where
  closure_invariant (graph : Graph α) : (fuel : Nat) → (seen : List α) → start ∈ seen →
      start ∈ closure graph fuel seen
    | 0, _, hseen => hseen
    | fuel + 1, seen, hseen => by
      simp only [closure]
      split
      · exact hseen
      · apply closure_invariant
        simp [closureStep, hseen]

end Bap.Graph
