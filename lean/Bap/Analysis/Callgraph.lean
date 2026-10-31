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

/-! ### Components

The components come from the algorithm of Kosaraju, whose correctness isn't what is proved. Its result is checked in time for its size: every edge goes from a
component to itself or a later one, so no path comes back, and all of a component is reached from its first node and reaches it. `components_checked` proves that
what passes is the list of `stronglyConnected`, whichever way it was found, and if it were not to pass that list is what is computed. -/

/-- A depth-first search. A frame is a node and the successors left to go to. -/
private def depthFirst (table : Std.HashMap Nat (List Nat)) :
    Nat → List (Nat × List Nat) → Std.HashSet Nat → Array Nat → Std.HashSet Nat × Array Nat
  | 0, _, visited, order => (visited, order)
  | _ + 1, [], visited, order => (visited, order)
  | fuel + 1, (node, []) :: stack, visited, order => depthFirst table fuel stack visited (order.push node)
  | fuel + 1, (node, next :: rest) :: stack, visited, order =>
    if visited.contains next then depthFirst table fuel ((node, rest) :: stack) visited order
    else depthFirst table fuel ((next, table.getD next []) :: (node, rest) :: stack) (visited.insert next) order

/-- All that `work` leads to in `table` that has no label gets `label`. -/
private def spread (table : Std.HashMap Nat (List Nat)) (label : Nat) :
    Nat → List Nat → Std.HashMap Nat Nat → Std.HashMap Nat Nat
  | 0, _, labels => labels
  | _ + 1, [], labels => labels
  | fuel + 1, node :: work, labels =>
    if labels.contains node then spread table label fuel work labels
    else spread table label fuel (table.getD node [] ++ work) (labels.insert node label)

/-- Kosaraju's numbering: the components in the order of the graph, an edge going to the same number or a higher one. -/
private def kosaraju (graph : Graph.Graph Nat) : Std.HashMap Nat Nat :=
  let fuel := 2 * (graph.nodes.length + graph.edges.length) + 2
  let forward := Graph.Fast.successorTable graph
  let backward := Graph.Fast.successorTable (reverseGraph graph)
  let (_, order) := graph.nodes.foldl (init := (({} : Std.HashSet Nat), (#[] : Array Nat))) fun state node =>
    if state.1.contains node then state
    else depthFirst forward fuel [(node, forward.getD node [])] (state.1.insert node) state.2
  (order.foldr (init := (({} : Std.HashMap Nat Nat), 0)) fun node state =>
    if state.1.contains node then state else (spread backward state.2 fuel [node] state.1, state.2 + 1)).1

/-- Every edge between nodes goes to the same number or a higher one. -/
private def ordered (graph : Graph.Graph Nat) (labels : Std.HashMap Nat Nat) : Bool :=
  let nodes : Std.HashSet Nat := Std.HashSet.ofList graph.nodes
  graph.edges.all fun edge => !nodes.contains edge.1 || !nodes.contains edge.2 || labels.getD edge.1 0 ≤ labels.getD edge.2 0

/-- The edges in each component. -/
private def edgesOf (labels : Std.HashMap Nat Nat) (edges : List (Nat × Nat)) : Std.HashMap Nat (List (Nat × Nat)) :=
  edges.foldr (init := {}) fun edge table =>
    let label := labels.getD edge.1 0
    if label = labels.getD edge.2 0 then table.insert label (edge :: table.getD label []) else table

private theorem mem_edgesOf (labels : Std.HashMap Nat Nat) (edges : List (Nat × Nat)) (label u v : Nat) :
    (u, v) ∈ (edgesOf labels edges).getD label [] ↔ (u, v) ∈ edges ∧ labels.getD u 0 = label ∧ labels.getD v 0 = label := by
  induction edges with
  | nil => simp [edgesOf]
  | cons head rest ih =>
    simp only [edgesOf, List.foldr_cons] at ih ⊢
    obtain ⟨a, b⟩ := head
    simp only [List.mem_cons, Prod.mk.injEq]
    split
    · next hs =>
      simp only [Std.HashMap.getD_insert]
      by_cases hl : labels.getD a 0 = label
      · subst hl
        simp only [beq_self_eq_true, ↓reduceIte, List.mem_cons, Prod.mk.injEq, ih]
        constructor
        · rintro (⟨rfl, rfl⟩ | ⟨hm, h1, h2⟩)
          · exact ⟨.inl ⟨rfl, rfl⟩, rfl, hs.symm⟩
          · exact ⟨.inr hm, h1, h2⟩
        · rintro ⟨⟨rfl, rfl⟩ | hm, h1, h2⟩
          · exact .inl ⟨rfl, rfl⟩
          · exact .inr ⟨hm, h1, h2⟩
      · have hb : (labels.getD a 0 == label) = false := by simpa using hl
        simp only [hb, Bool.false_eq_true, ↓reduceIte, ih]
        constructor
        · rintro ⟨hm, h1, h2⟩
          exact ⟨.inr hm, h1, h2⟩
        · rintro ⟨⟨rfl, rfl⟩ | hm, h1, h2⟩
          · exact (hl h1).elim
          · exact ⟨hm, h1, h2⟩
    · next hs =>
      rw [ih]
      constructor
      · rintro ⟨hm, h1, h2⟩
        exact ⟨.inr hm, h1, h2⟩
      · rintro ⟨⟨rfl, rfl⟩ | hm, h1, h2⟩
        · exact (hs (h1.trans h2.symm)).elim
        · exact ⟨hm, h1, h2⟩

/-- A component, from its first node: what `reachable` finds of it, which is checked to be all of the nodes with its number, each of which leads back. -/
private def componentOf (labels : Std.HashMap Nat Nat) (groups : Std.HashMap Nat (List Nat)) (edges : Std.HashMap Nat (List (Nat × Nat)))
    (fuel node : Nat) : Option (List Nat) :=
  let label := labels.getD node 0
  let sub : Graph.Graph Nat := { nodes := groups.getD label [], edges := edges.getD label [] }
  let forward := Graph.Fast.reachableFuel sub fuel node
  let there : Std.HashSet Nat := Std.HashSet.ofList forward
  let back : Std.HashSet Nat := Std.HashSet.ofList (Graph.Fast.reachableFuel (reverseGraph sub) fuel node)
  if sub.nodes.all fun other => there.contains other && back.contains other then some forward else none

private def componentsFrom (labels : Std.HashMap Nat Nat) (groups : Std.HashMap Nat (List Nat)) (edges : Std.HashMap Nat (List (Nat × Nat)))
    (fuel : Nat) : List Nat → Std.HashSet Nat → List (List Nat) → Option (List (List Nat))
  | [], _, done => some done.reverse
  | node :: rest, visited, done =>
    let label := labels.getD node 0
    if visited.contains label then componentsFrom labels groups edges fuel rest visited done
    else
      match componentOf labels groups edges fuel node with
      | some component => componentsFrom labels groups edges fuel rest (visited.insert label) (component :: done)
      | none => none

private def componentsChecked (graph : Graph.Graph Nat) (labels : Std.HashMap Nat Nat) : Option (List (List Nat)) :=
  if ordered graph labels then
    componentsFrom labels (Graph.Fast.groupBy (graph.nodes.map fun node => (labels.getD node 0, node))) (edgesOf labels graph.edges)
      (graph.nodes.length + 1) graph.nodes {} []
  else none

/-- `stronglyConnected`, in the time of a search of the graph and of each component. -/
private def stronglyConnectedFast (callgraph : Callgraph) : List (List Nat) :=
  (componentsChecked callgraph.graph (kosaraju callgraph.graph)).getD (stronglyConnected callgraph)

private theorem reaches_label {graph : Graph.Graph Nat} {labels : Std.HashMap Nat Nat} (hordered : ordered graph labels = true)
    {start x : Nat} (h : Bap.Proofs.Graph.Reaches graph [start] x) : labels.getD start 0 ≤ labels.getD x 0 := by
  induction h with
  | seed hs _ =>
    rw [List.mem_singleton] at hs
    subst hs
    exact Nat.le_refl _
  | @step y z hy he hn ih =>
    simp only [ordered, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hordered
    have hedge := hordered (y, z) he
    simp only [Std.HashSet.contains_ofList, List.contains_eq_mem, decide_eq_false_iff_not] at hedge
    rcases hedge with (h1 | h2) | h3
    · exact (h1 hy.mem_nodes).elim
    · exact (h2 hn).elim
    · exact Nat.le_trans ih h3

private theorem reaches_mono {graph sub : Graph.Graph Nat} (hn : ∀ x ∈ sub.nodes, x ∈ graph.nodes) (he : ∀ e ∈ sub.edges, e ∈ graph.edges)
    {seeds : List Nat} {x : Nat} (h : Bap.Proofs.Graph.Reaches sub seeds x) : Bap.Proofs.Graph.Reaches graph seeds x := by
  induction h with
  | seed hs hx => exact .seed hs (hn _ hx)
  | step _ hedge hx ih => exact .step ih (he _ hedge) (hn _ hx)

/-- What a component passes the check for is what `stronglyConnected` has at that node, and it says which nodes it has. -/
private theorem componentOf_spec {graph : Graph.Graph Nat} {labels : Std.HashMap Nat Nat} (hordered : ordered graph labels = true) {node : Nat}
    (hnode : node ∈ graph.nodes) {component : List Nat}
    (h : componentOf labels (Graph.Fast.groupBy (graph.nodes.map fun node => (labels.getD node 0, node))) (edgesOf labels graph.edges)
      (graph.nodes.length + 1) node = some component) :
    component = (Graph.reachable graph node).filter (fun candidate => (Graph.reachable graph candidate).contains node) ∧
      ∀ other ∈ graph.nodes, other ∈ component ↔ labels.getD other 0 = labels.getD node 0 := by
  generalize hL : labels.getD node 0 = label at h
  have hgroup : (Graph.Fast.groupBy (graph.nodes.map fun node => (labels.getD node 0, node))).getD label [] =
      graph.nodes.filter fun other => labels.getD other 0 = label := by
    rw [Graph.Fast.groupBy_getD, List.filter_map, List.map_map]
    simp [Function.comp_def]
  simp only [componentOf, hL, hgroup] at h
  generalize hsub : ({ nodes := graph.nodes.filter fun other => labels.getD other 0 = label, edges := (edgesOf labels graph.edges).getD label [] } : Graph.Graph Nat) = sub at h
  have hsn : sub.nodes = graph.nodes.filter fun other => labels.getD other 0 = label := by rw [← hsub]
  have hse : ∀ u v, (u, v) ∈ sub.edges ↔ (u, v) ∈ graph.edges ∧ labels.getD u 0 = label ∧ labels.getD v 0 = label := by
    intro u v
    rw [← hsub]
    exact mem_edgesOf labels graph.edges label u v
  split at h
  next hall =>
    simp only [Option.some.injEq] at h
    subst h
    simp only [List.all_eq_true, Bool.and_eq_true, Std.HashSet.contains_ofList, List.contains_eq_mem, decide_eq_true_eq] at hall
    have hin : node ∈ sub.nodes := by
      rw [hsn]
      simp [hnode, hL]
    have hrev : node ∈ (reverseGraph sub).nodes := hin
    have hrestrict := Graph.Fast.reachable_restrict graph sub (fun other => labels.getD other 0 = label) node hnode (by simp [hL]) hsn
      (fun u v => by rw [hse]; simp) (fun y x hy he hx hix => by
        have h1 : label ≤ labels.getD y 0 := hL ▸ reaches_label hordered hy
        have h2 := reaches_label hordered (.step (.seed (List.mem_cons_self) hy.mem_nodes) he hx : Bap.Proofs.Graph.Reaches graph [y] x)
        simp only [decide_eq_true_eq] at hix ⊢
        omega)
    have hback : ∀ other, other ∈ graph.nodes → labels.getD other 0 = label → Bap.Proofs.Graph.Reaches graph [other] node := by
      intro other ho hl
      have hos : other ∈ sub.nodes := by
        rw [hsn]
        simp [ho, hl]
      have hb := Graph.Fast.mem_reachableFuel hrev (hall other (hsn ▸ hos)).2
      have hr := reaches_reverse hb
      rw [reverse_reverse] at hr
      refine reaches_mono ?_ ?_ hr
      · intro x hx
        rw [hsn] at hx
        exact (List.mem_filter.1 hx).1
      · rintro ⟨u, v⟩ he
        exact ((hse u v).1 he).1
    constructor
    · rw [hrestrict]
      apply List.filter_congr
      intro c hc
      have hcr := (Bap.Proofs.Graph.mem_reachableFrom_iff graph [node] c).1 hc
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, List.contains_eq_mem, Graph.reachable, Bap.Proofs.Graph.mem_reachableFrom_iff]
      constructor
      · intro hl
        exact hback c hcr.mem_nodes hl
      · intro hr
        have h1 := reaches_label hordered hcr
        have h2 := reaches_label hordered hr
        omega
    · intro other ho
      constructor
      · intro hm
        have := Graph.Fast.mem_reachableFuel hin hm
        have hmn := this.mem_nodes
        rw [hsn] at hmn
        simpa using (List.mem_filter.1 hmn).2
      · intro hl
        have hos : other ∈ sub.nodes := by
          rw [hsn]
          simp [ho, hl]
        exact (hall other (hsn ▸ hos)).1
  next => cases h

/-- **Whatever numbering passes the check, the list is that of `stronglyConnected`.** -/
private theorem components_checked {graph : Graph.Graph Nat} {labels : Std.HashMap Nat Nat} {result : List (List Nat)}
    (h : componentsChecked graph labels = some result) :
    (graph.nodes.foldl (init := (graph.nodes, [])) fun current node =>
      if !current.1.contains node then current
      else
        let forward := Graph.reachable graph node
        let component := forward.filter fun candidate => (Graph.reachable graph candidate).contains node
        (current.1.filter fun candidate => !component.contains candidate, current.2 ++ [component])).2 = result := by
  simp only [componentsChecked] at h
  split at h
  next hordered =>
    have key : ∀ (rest list : List Nat) (comps : List (List Nat)) (visited : Std.HashSet Nat) (done : List (List Nat)),
        (∀ node ∈ rest, node ∈ graph.nodes) → (∀ node ∈ rest, node ∈ list ↔ visited.contains (labels.getD node 0) = false) → comps = done.reverse →
        componentsFrom labels (Graph.Fast.groupBy (graph.nodes.map fun node => (labels.getD node 0, node))) (edgesOf labels graph.edges)
          (graph.nodes.length + 1) rest visited done = some result →
        (rest.foldl (init := (list, comps)) fun current node =>
          if !current.1.contains node then current
          else
            let forward := Graph.reachable graph node
            let component := forward.filter fun candidate => (Graph.reachable graph candidate).contains node
            (current.1.filter fun candidate => !component.contains candidate, current.2 ++ [component])).2 = result := by
      intro rest
      induction rest with
      | nil =>
        intro list comps visited done _ _ hc hf
        simp only [componentsFrom, Option.some.injEq] at hf
        simpa [hc] using hf
      | cons node nodes ih =>
        intro list comps visited done hnodes hmem hc hf
        simp only [List.foldl_cons]
        simp only [componentsFrom] at hf
        by_cases hv : visited.contains (labels.getD node 0) = true
        · have hn : node ∉ list := fun hm => by
            have := (hmem node List.mem_cons_self).1 hm
            rw [hv] at this
            cases this
          have hl : (!list.contains node) = true := by simpa using hn
          simp only [hv, ↓reduceIte] at hf
          simp only [hl, ↓reduceIte]
          exact ih _ _ _ _ (fun m hm => hnodes m (List.mem_cons_of_mem _ hm)) (fun m hm => hmem m (List.mem_cons_of_mem _ hm)) hc hf
        · have hn : node ∈ list := (hmem node List.mem_cons_self).2 (by simpa using hv)
          have hl : ¬ (!list.contains node) = true := by simpa using hn
          simp only [hv, Bool.false_eq_true, ↓reduceIte] at hf
          split at hf
          · next component hcomp =>
            obtain ⟨hspec, hwho⟩ := componentOf_spec hordered (hnodes node List.mem_cons_self) hcomp
            simp only [hl, ← hspec]
            refine ih _ _ _ _ (fun m hm => hnodes m (List.mem_cons_of_mem _ hm)) ?_ (by simp [hc]) hf
            intro m hm
            have hold := hmem m (List.mem_cons_of_mem _ hm)
            have hwm := hwho m (hnodes m (List.mem_cons_of_mem _ hm))
            simp only [List.mem_filter, hold, Std.HashSet.contains_insert, Bool.or_eq_false_iff, Bool.not_eq_true',
              List.contains_eq_mem, decide_eq_false_iff_not, hwm, beq_eq_false_iff_ne]
            constructor
            · rintro ⟨h1, h2⟩
              exact ⟨fun he => h2 he.symm, h1⟩
            · rintro ⟨h1, h2⟩
              exact ⟨h2, fun he => h1 he.symm⟩
          · cases hf
    exact key _ _ _ _ _ (fun _ h => h) (by simp) rfl h
  next => cases h

@[csimp] private theorem stronglyConnected_eq_fast : @stronglyConnected = @stronglyConnectedFast := by
  funext callgraph
  simp only [stronglyConnectedFast]
  cases h : componentsChecked callgraph.graph (kosaraju callgraph.graph) with
  | none => rfl
  | some result =>
    simp only [Option.getD_some]
    exact components_checked h

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

/-- `render`, with the functions by address in a table. -/
private def renderFast (callgraph : Callgraph) : String :=
  let named := Graph.Fast.assocTable (callgraph.functions.map fun symbol => (symbol.addr, symbol))
  let lines := callgraph.graph.edges.map fun edge =>
    match named.get? edge.1, named.get? edge.2 with
    | some caller, some callee => s!"  {caller.name} -> {callee.name};"
    | _, _ => s!"  fn_{edge.1} -> fn_{edge.2};"
  "digraph callgraph {\n" ++ String.intercalate "\n" lines ++ "\n}"

private theorem find_named (functions : List Image.Symbol) (address : Nat) :
    functions.find? (fun symbol => symbol.addr = address) =
      (Graph.Fast.assocTable (functions.map fun symbol => (symbol.addr, symbol))).get? address := by
  rw [Graph.Fast.assocTable_get]
  induction functions with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.find?_cons, List.map_cons, Assoc.get, List.lookup_cons] at ih ⊢
    by_cases h : head.addr = address
    · simp [h]
    · have hb : (address == head.addr) = false := by simpa using fun he : address = head.addr => h he.symm
      simp [h, hb, ih]

@[csimp] private theorem render_eq_fast : @render = @renderFast := by
  funext callgraph
  simp only [render, renderFast, find_named]

end Bap.Analysis.Callgraph
