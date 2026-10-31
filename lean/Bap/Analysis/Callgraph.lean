import Bap.Analysis.Xrefs
import Bap.Graph.Fast

namespace Bap.Analysis.Callgraph

structure Callgraph where
  graph : Graph.Graph Nat := {}
  functions : List Image.Symbol := []

def create (index : Xrefs.Index) : Callgraph := {
  graph := {
    nodes := (index.functions.map Image.Symbol.addr ++
      index.xrefs.filterMap fun xref => match xref.kind with
        | .call => some xref.target
        | _ => none).eraseDups
    edges := (index.xrefs.filterMap fun xref =>
      if xref.kind = .call then
        (Xrefs.functionOf index xref.source).map fun caller => (caller.addr, xref.target)
      else
        none) |>.eraseDups
  }
  functions := index.functions
}

def reachable (callgraph : Callgraph) (roots : List Nat) : List Nat :=
  Graph.reachableFrom callgraph.graph roots

private def reachableFast (callgraph : Callgraph) (roots : List Nat) : List Nat :=
  Graph.Fast.reachableFrom callgraph.graph roots

@[csimp] private theorem reachable_eq_fast : @reachable = @reachableFast := by
  funext callgraph roots
  exact (Graph.Fast.reachableFrom_eq callgraph.graph roots).symm

def stronglyConnected (callgraph : Callgraph) : List (List Nat) :=
  let components := callgraph.graph.nodes.foldl (init := (callgraph.graph.nodes, [])) fun current node =>
    if !current.1.contains node then current
    else
      let forward := Graph.reachable callgraph.graph node
      let component := forward.filter fun candidate =>
        (Graph.reachable callgraph.graph candidate).contains node
      (current.1.filter fun candidate => !component.contains candidate, current.2 ++ [component])
  components.2

/-- The edges the other way. -/
private def reverseGraph (graph : Graph.Graph Nat) : Graph.Graph Nat :=
  { graph with edges := graph.edges.map fun edge => (edge.2, edge.1) }

private theorem reaches_trans {g : Graph.Graph Nat} {a b c : Nat} (h1 : Bap.Proofs.Graph.Reaches g [a] b)
    (h2 : Bap.Proofs.Graph.Reaches g [b] c) : Bap.Proofs.Graph.Reaches g [a] c := by
  induction h2 with
  | seed hs _ =>
    rw [List.mem_singleton] at hs
    exact hs ▸ h1
  | step _ he hn ih => exact .step ih he hn

private theorem reaches_reverse {g : Graph.Graph Nat} {a b : Nat} (h : Bap.Proofs.Graph.Reaches g [a] b) :
    Bap.Proofs.Graph.Reaches (reverseGraph g) [b] a := by
  induction h with
  | seed hs hn =>
    rw [List.mem_singleton] at hs
    subst hs
    exact .seed List.mem_cons_self hn
  | @step x y h0 he hn ih =>
    have hedge : (y, x) ∈ (reverseGraph g).edges := List.mem_map.2 ⟨(x, y), he, rfl⟩
    exact reaches_trans (.step (.seed List.mem_cons_self hn) hedge h0.mem_nodes) ih

private theorem reverse_reverse (g : Graph.Graph Nat) : reverseGraph (reverseGraph g) = g := by
  cases g with
  | mk nodes edges =>
    simp only [reverseGraph, List.map_map]
    congr 1
    have : ((fun edge : Nat × Nat => (edge.2, edge.1)) ∘ fun edge : Nat × Nat => (edge.2, edge.1)) = id := by
      funext edge
      rfl
    rw [this, List.map_id]

/-- For nodes of the graph: what reaches a node is what the other way it reaches. -/
private theorem reaches_iff (g : Graph.Graph Nat) (c node : Nat) :
    node ∈ Graph.reachable g c ↔ c ∈ Graph.reachable (reverseGraph g) node := by
  simp only [Graph.reachable, Bap.Proofs.Graph.mem_reachableFrom_iff]
  constructor
  · exact reaches_reverse
  · intro h
    have := reaches_reverse h
    rwa [reverse_reverse] at this

/-- `stronglyConnected`, going over the graph once from each component and once the other way, and not from each node of it. -/
private def stronglyConnectedFast (callgraph : Callgraph) : List (List Nat) :=
  let graph := callgraph.graph
  let backward := reverseGraph graph
  let nodes : Std.HashSet Nat := Std.HashSet.ofList graph.nodes
  let forwardTable := Graph.Fast.successorTable graph
  let backwardTable := Graph.Fast.successorTable backward
  let state := graph.nodes.foldl (init := (({} : Std.HashSet Nat), ([] : List (List Nat)))) fun current node =>
    if current.1.contains node then current
    else
      let reaching : Std.HashSet Nat := Std.HashSet.ofList (Graph.Fast.reachableWith backward backwardTable nodes node)
      let component := (Graph.Fast.reachableWith graph forwardTable nodes node).filter reaching.contains
      (current.1.insertMany component, component :: current.2)
  state.2.reverse

@[csimp] private theorem stronglyConnected_eq_fast : @stronglyConnected = @stronglyConnectedFast := by
  funext callgraph
  simp only [stronglyConnected, stronglyConnectedFast]
  generalize callgraph.graph = graph
  have hfw : Graph.Fast.reachableWith graph (Graph.Fast.successorTable graph) (Std.HashSet.ofList graph.nodes) =
      Graph.reachable graph := funext (Graph.Fast.reachableWith_eq graph)
  have hbw : Graph.Fast.reachableWith (reverseGraph graph) (Graph.Fast.successorTable (reverseGraph graph)) (Std.HashSet.ofList graph.nodes) =
      Graph.reachable (reverseGraph graph) := funext (Graph.Fast.reachableWith_eq (reverseGraph graph))
  simp only [hfw, hbw]
  have key : ∀ (rest : List Nat) (list : List Nat) (comps : List (List Nat)) (set : Std.HashSet Nat) (acc : List (List Nat)),
      (∀ n ∈ rest, n ∈ list ↔ set.contains n = false) → comps = acc.reverse →
      (rest.foldl (init := (list, comps)) fun current node =>
        if !current.1.contains node then current
        else
          let forward := Graph.reachable graph node
          let component := forward.filter fun candidate => (Graph.reachable graph candidate).contains node
          (current.1.filter fun candidate => !component.contains candidate, current.2 ++ [component])).2 =
      (rest.foldl (init := (set, acc)) fun current node =>
        if current.1.contains node then current
        else
          let reaching : Std.HashSet Nat := Std.HashSet.ofList (Graph.reachable (reverseGraph graph) node)
          let component := (Graph.reachable graph node).filter reaching.contains
          (current.1.insertMany component, component :: current.2)).2.reverse := by
    intro rest
    induction rest with
    | nil => intro _ _ _ _ _ h; exact h
    | cons n ns ih =>
      intro list comps set acc hmem hc
      simp only [List.foldl_cons]
      by_cases hset : set.contains n = true
      · have hn : n ∉ list := fun hm => by
          have := (hmem n List.mem_cons_self).1 hm
          rw [hset] at this
          cases this
        have hl : (!list.contains n) = true := by simpa using hn
        simp only [hl, hset, ↓reduceIte]
        exact ih _ _ _ _ (fun m hm => hmem m (List.mem_cons_of_mem _ hm)) hc
      · have hn : n ∈ list := (hmem n List.mem_cons_self).2 (by simpa using hset)
        have hl : ¬ (!list.contains n) = true := by simpa using hn
        have hcomp : ((Graph.reachable graph n).filter fun candidate => (Graph.reachable graph candidate).contains n) =
            (Graph.reachable graph n).filter (Std.HashSet.ofList (Graph.reachable (reverseGraph graph) n)).contains := by
          apply List.filter_congr
          intro c _
          rw [Bool.eq_iff_iff]
          simp only [List.contains_eq_mem, decide_eq_true_eq, Std.HashSet.contains_ofList]
          exact reaches_iff graph c n
        simp only [hl, hset, hcomp]
        apply ih
        · intro m hm
          have hold := hmem m (List.mem_cons_of_mem _ hm)
          simp only [List.mem_filter, hold, Std.HashSet.contains_insertMany_list, Bool.or_eq_false_iff, Bool.not_eq_true',
            List.contains_eq_mem, decide_eq_false_iff_not]
        · simp [hc]
  exact key _ _ _ _ _ (by simp) rfl

/-- `create`, without comparing every pair of what it lists. -/
private def createFast (index : Xrefs.Index) : Callgraph := {
  graph := {
    nodes := Graph.Fast.dedup (index.functions.map Image.Symbol.addr ++
      index.xrefs.filterMap fun xref => match xref.kind with
        | .call => some xref.target
        | _ => none)
    edges := Graph.Fast.dedup (index.xrefs.filterMap fun xref =>
      if xref.kind = .call then
        (Xrefs.functionOf index xref.source).map fun caller => (caller.addr, xref.target)
      else
        none)
  }
  functions := index.functions
}

@[csimp] private theorem create_eq_fast : @create = @createFast := by
  funext index
  simp only [create, createFast, Graph.Fast.dedup_eq]

def recursiveFunctions (callgraph : Callgraph) : List Nat :=
  let components := stronglyConnected callgraph
  callgraph.graph.nodes.filter fun node =>
    components.any (fun component => component.length > 1 && component.contains node) ||
      callgraph.graph.edges.contains (node, node)

/-- `recursiveFunctions`, with what it asks about each node in sets. -/
private def recursiveFunctionsFast (callgraph : Callgraph) : List Nat :=
  let components := stronglyConnected callgraph
  let cyclic : Std.HashSet Nat := components.foldl (init := {}) fun set component =>
    if component.length > 1 then set.insertMany component else set
  let loops : Std.HashSet Nat := callgraph.graph.edges.foldl (init := {}) fun set edge =>
    if edge.1 == edge.2 then set.insert edge.1 else set
  callgraph.graph.nodes.filter fun node => cyclic.contains node || loops.contains node

@[csimp] private theorem recursiveFunctions_eq_fast : @recursiveFunctions = @recursiveFunctionsFast := by
  funext callgraph
  simp only [recursiveFunctions, recursiveFunctionsFast]
  apply List.filter_congr
  intro node _
  have hc : ∀ (l : List (List Nat)) (init : Std.HashSet Nat),
      (l.foldl (init := init) fun set component =>
        if component.length > 1 then set.insertMany component else set).contains node =
      (init.contains node || l.any fun component => component.length > 1 && component.contains node) := by
    intro l
    induction l with
    | nil => simp
    | cons head tail ih =>
      intro init
      simp only [List.foldl_cons, ih, List.any_cons]
      by_cases hlen : head.length > 1
      · simp only [hlen, ↓reduceIte, Std.HashSet.contains_insertMany_list, decide_true, Bool.true_and,
          Bool.or_assoc]
      · simp [hlen]
  have hl : ∀ (l : List (Nat × Nat)) (init : Std.HashSet Nat),
      (l.foldl (init := init) fun set edge => if edge.1 == edge.2 then set.insert edge.1 else set).contains node =
      (init.contains node || l.contains (node, node)) := by
    intro l
    induction l with
    | nil => simp
    | cons head tail ih =>
      intro init
      obtain ⟨a, b⟩ := head
      simp only [List.foldl_cons, ih, List.contains_cons]
      by_cases hab : a = b
      · subst hab
        simp only [beq_self_eq_true, ↓reduceIte, Std.HashSet.contains_insert]
        by_cases hn : node = a
        · subst hn
          simp
        · have : (a == node) = false := by simpa using fun h => hn h.symm
          have h2 : ((node, node) == (a, a)) = false := by simpa using fun h => hn h
          simp [this, h2]
      · have hne : (a == b) = false := by simpa using hab
        have h2 : ((node, node) == (a, b)) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq, Prod.mk.injEq]
          exact fun h => hab (h.1.symm.trans h.2)
        simp [hne, h2]
  rw [hc, hl]
  simp

def render (callgraph : Callgraph) : String :=
  let lines := callgraph.graph.edges.map fun edge =>
    match callgraph.functions.find? (fun symbol => symbol.addr = edge.1),
      callgraph.functions.find? (fun symbol => symbol.addr = edge.2) with
    | some caller, some callee => s!"  {caller.name} -> {callee.name};"
    | _, _ => s!"  fn_{edge.1} -> fn_{edge.2};"
  "digraph callgraph {\n" ++ String.intercalate "\n" lines ++ "\n}"

end Bap.Analysis.Callgraph
