import Bap.Graph.Facts
import Std.Data.HashMap
import Std.Data.HashSet

/-! Faster algorithms for graphs over `Nat`, proved to give the very lists of the definitions in
`Bap.Graph.Basic`, which stay the specification: `Bap.IR.Cfg` makes the compiler use these. -/

namespace Bap.Graph.Fast

open Std

local macro "closure" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.Graph.Basic) 0 ++ `Bap.Graph.closure)
local macro "closureStep" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.Graph.Basic) 0 ++ `Bap.Graph.closureStep)
local macro "frontierWalk" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.Graph.Basic) 0 ++ `Bap.Graph.frontierWalk)
local macro "unfold_closureStep" : tactic =>
  `(tactic| simp only [$(Lean.mkIdent (.num (`_private ++ `Bap.Graph.Basic) 0 ++ `Bap.Graph.closureStep)):ident])
local macro "unfold_reachLoop_closure" : tactic =>
  `(tactic| simp only [$(Lean.mkIdent `reachLoop):ident, $(Lean.mkIdent (.num (`_private ++ `Bap.Graph.Basic) 0 ++ `Bap.Graph.closure)):ident])
local macro "unfold_walk_frontierWalk" : tactic =>
  `(tactic| simp only [$(Lean.mkIdent `walk):ident, $(Lean.mkIdent (.num (`_private ++ `Bap.Graph.Basic) 0 ++ `Bap.Graph.frontierWalk)):ident, $(Lean.mkIdent `assocTable_get):ident])

/-! ### Tables -/

/-- Looks up as `Assoc.get` does on the list. -/
def assocTable {β : Type} (entries : List (Nat × β)) : HashMap Nat β :=
  entries.foldr (fun entry table => table.insert entry.1 entry.2) {}

theorem assocTable_get {β : Type} (entries : List (Nat × β)) (key : Nat) :
    (assocTable entries).get? key = Assoc.get key entries := by
  induction entries with
  | nil => simp [assocTable, Assoc.get]
  | cons head tail ih =>
    simp only [assocTable, List.foldr_cons, HashMap.get?_eq_getElem?, HashMap.getElem?_insert] at ih ⊢
    obtain ⟨k, v⟩ := head
    by_cases hk : k = key
    · subst hk
      simp [Assoc.get]
    · have h1 : (k == key) = false := by simpa using hk
      have h2 : (key == k) = false := by simpa using fun e : key = k => hk e.symm
      simp only [h1, Bool.false_eq_true, ite_false, ih]
      simp [Assoc.get, List.lookup, h2]

/-- All the targets of each source of `pairs`, in order. -/
def groupBy (pairs : List (Nat × Nat)) : HashMap Nat (List Nat) :=
  pairs.foldr (fun pair table => table.insert pair.1 (pair.2 :: table.getD pair.1 [])) {}

theorem groupBy_getD (pairs : List (Nat × Nat)) (key : Nat) :
    (groupBy pairs).getD key [] = (pairs.filter fun pair => pair.1 = key).map Prod.snd := by
  induction pairs with
  | nil => simp [groupBy]
  | cons head tail ih =>
    simp only [groupBy, List.foldr_cons, HashMap.getD_insert] at ih ⊢
    obtain ⟨k, v⟩ := head
    by_cases hk : k = key
    · subst hk
      simp [ih]
    · have h1 : (k == key) = false := by simpa using hk
      simp [h1, ih, hk]

/-- `List.eraseDups` of what `seen` doesn't hold. -/
def dedupFrom {α : Type} [BEq α] [Hashable α] (seen : HashSet α) : List α → List α
  | [] => []
  | x :: xs => if seen.contains x then dedupFrom seen xs else x :: dedupFrom (seen.insert x) xs

theorem dedupFrom_eq {α : Type} [BEq α] [Hashable α] [LawfulBEq α] (seen : HashSet α) (l : List α) :
    dedupFrom seen l = (l.filter fun x => !seen.contains x).eraseDups := by
  induction l generalizing seen with
  | nil => rfl
  | cons x xs ih =>
    simp only [dedupFrom, List.filter_cons]
    by_cases hx : seen.contains x = true
    · simp [hx, ih]
    · simp only [hx, ite_false, Bool.false_eq_true, Bool.not_false, ite_true]
      rw [List.eraseDups_cons, ih, List.filter_filter]
      congr 2
      apply List.filter_congr
      intro y _
      simp only [HashSet.contains_insert]
      by_cases hy : y = x
      · subst hy
        simp [hx]
      · have h1 : (x == y) = false := by simpa using fun e : x = y => hy e.symm
        have h2 : (y == x) = false := by simpa using hy
        simp [h1, h2]

/-- `List.eraseDups`, in near-linear time. -/
def dedup {α : Type} [BEq α] [Hashable α] (l : List α) : List α := dedupFrom {} l

theorem dedup_eq {α : Type} [BEq α] [Hashable α] [LawfulBEq α] (l : List α) : dedup l = l.eraseDups := by
  rw [dedup, dedupFrom_eq]
  congr 1
  apply List.filter_eq_self.2
  simp

/-- `predecessors`, from a table of them. -/
def predecessorTable (graph : Graph Nat) : HashMap Nat (List Nat) :=
  groupBy (graph.edges.map fun edge => (edge.2, edge.1))

theorem predecessors_eq (graph : Graph Nat) (node : Nat) :
    dedup ((predecessorTable graph).getD node []) = predecessors graph node := by
  rw [dedup_eq, predecessorTable, groupBy_getD, predecessors, List.filter_map, List.map_map]
  rfl

/-- `successors`, from a table of them. -/
def successorTable (graph : Graph Nat) : HashMap Nat (List Nat) := groupBy graph.edges

theorem successors_eq (graph : Graph Nat) (node : Nat) :
    dedup ((successorTable graph).getD node []) = successors graph node := by
  rw [dedup_eq, successorTable, groupBy_getD, successors]

/-! ### Reachability -/

/-- A step of `closure`: `hits` holds the successors of what is `seen`, and `waiting` what isn't seen yet. -/
private def reachLoop (graph : Graph Nat) (table : HashMap Nat (List Nat)) :
    Nat → List Nat → List Nat → HashSet Nat → List Nat
  | 0, seen, _, _ => seen
  | fuel + 1, seen, waiting, hits =>
    match waiting.filter hits.contains with
    | [] => seen
    | discovered =>
      let hits' := discovered.foldl (fun hits node => hits.insertMany (table.getD node [])) hits
      reachLoop graph table fuel (seen ++ discovered) (waiting.filter fun node => !hits.contains node) hits'

private theorem mem_insertAll (table : HashMap Nat (List Nat)) (found : List Nat) (hits : HashSet Nat) (x : Nat) :
    (found.foldl (fun hits node => hits.insertMany (table.getD node [])) hits).contains x = true ↔
      hits.contains x = true ∨ ∃ node ∈ found, x ∈ table.getD node [] := by
  induction found generalizing hits with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons]
    rw [ih, HashSet.contains_insertMany_list]
    simp only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]
    grind

private theorem mem_successorTable (graph : Graph Nat) (a b : Nat) :
    b ∈ (successorTable graph).getD a [] ↔ (a, b) ∈ graph.edges := by
  rw [successorTable, groupBy_getD]
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨u, v⟩, ⟨he, rfl⟩, rfl⟩
    exact he
  · intro h
    exact ⟨(a, b), ⟨h, rfl⟩, rfl⟩

private theorem reachLoop_eq (graph : Graph Nat) (fuel : Nat) (seen waiting : List Nat) (hits : HashSet Nat)
    (hw : waiting = graph.nodes.filter fun node => node ∉ seen)
    (hh : ∀ x, hits.contains x = true ↔ ∃ y ∈ seen, (y, x) ∈ graph.edges) :
    reachLoop graph (successorTable graph) fuel seen waiting hits = closure graph fuel seen := by
  induction fuel generalizing seen waiting hits with
  | zero => rfl
  | succ fuel ih =>
    have hstep : closureStep graph seen = seen ++ waiting.filter hits.contains := by
      unfold_closureStep
      congr 1
      rw [hw, List.filter_filter]
      apply List.filter_congr
      intro x _
      have := hh x
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Bool.and_eq_true, List.any_eq_true, Bap.Proofs.Graph.mem_predecessors, and_comm (b := x ∉ seen)]
      constructor
      · rintro ⟨hx, y, he, hy⟩
        exact ⟨hx, this.2 ⟨y, by simpa using hy, he⟩⟩
      · rintro ⟨hx, hc⟩
        obtain ⟨y, hy, he⟩ := this.1 hc
        exact ⟨hx, y, he, by simpa using hy⟩
    unfold_reachLoop_closure
    rw [hstep]
    split
    · rename_i hnil
      simp [hnil]
    · rename_i discovered hne
      have hne' : ¬ (seen ++ waiting.filter hits.contains = seen) := by
        intro he
        apply hne
        simpa using he
      simp only [hne', ite_false]
      apply ih
      · rw [hw, List.filter_filter]
        apply List.filter_congr
        intro x hx
        by_cases hs : x ∈ seen
        · simp [hs]
        · have hmem : x ∈ waiting := by
            rw [hw]
            exact List.mem_filter.2 ⟨hx, by simpa using hs⟩
          have hd : x ∈ waiting.filter hits.contains ↔ hits.contains x = true := by simp [List.mem_filter, hmem]
          cases hc : hits.contains x <;> simp [hs, hc, hx]
      · intro x
        rw [mem_insertAll, hh x]
        simp only [mem_successorTable, List.mem_append]
        constructor
        · rintro (⟨y, hy, he⟩ | ⟨y, hy, he⟩)
          · exact ⟨y, .inl hy, he⟩
          · exact ⟨y, .inr hy, he⟩
        · rintro ⟨y, hy | hy, he⟩
          · exact .inl ⟨y, hy, he⟩
          · exact .inr ⟨y, hy, he⟩

/-- `reachableFrom`. -/
def reachableFrom (graph : Graph Nat) (seeds : List Nat) : List Nat :=
  let nodes : HashSet Nat := HashSet.ofList graph.nodes
  let start := dedup (seeds.filter nodes.contains)
  let table := successorTable graph
  let started : HashSet Nat := HashSet.ofList start
  let hits := start.foldl (fun hits node => hits.insertMany (table.getD node [])) ({} : HashSet Nat)
  reachLoop graph table (graph.nodes.length + 1) start (graph.nodes.filter fun node => !started.contains node) hits

theorem reachableFrom_eq (graph : Graph Nat) (seeds : List Nat) :
    reachableFrom graph seeds = Bap.Graph.reachableFrom graph seeds := by
  have hstart : dedup (seeds.filter (HashSet.ofList graph.nodes).contains) = (seeds.filter fun node => node ∈ graph.nodes).eraseDups := by
    rw [dedup_eq]
    congr 1
    apply List.filter_congr
    intro x _
    simp [HashSet.contains_ofList]
  simp only [reachableFrom, Bap.Graph.reachableFrom]
  rw [hstart]
  apply reachLoop_eq
  · apply List.filter_congr
    intro x _
    simp [HashSet.contains_ofList]
  · intro x
    rw [mem_insertAll]
    simp [mem_successorTable]

/-- `reachable`. -/
def reachable (graph : Graph Nat) (start : Nat) : List Nat := reachableFrom graph [start]

theorem reachable_eq (graph : Graph Nat) (start : Nat) : reachable graph start = Bap.Graph.reachable graph start :=
  reachableFrom_eq graph [start]

/-- `reachable`, for many starts in a graph, with what doesn't change between them already in tables. -/
def reachableWith (graph : Graph Nat) (table : HashMap Nat (List Nat)) (nodes : HashSet Nat) (start : Nat) : List Nat :=
  let begin := dedup ([start].filter nodes.contains)
  let started : HashSet Nat := HashSet.ofList begin
  let hits := begin.foldl (fun hits node => hits.insertMany (table.getD node [])) ({} : HashSet Nat)
  reachLoop graph table (graph.nodes.length + 1) begin (graph.nodes.filter fun node => !started.contains node) hits

theorem reachableWith_eq (graph : Graph Nat) (start : Nat) :
    reachableWith graph (successorTable graph) (HashSet.ofList graph.nodes) start = Bap.Graph.reachable graph start :=
  reachable_eq graph start

/-! ### Dominators -/

private abbrev Sorted (l : List Nat) : Prop := l.Pairwise (· < ·)

/-- The intersection of two ascending lists. -/
private def inter : List Nat → List Nat → List Nat
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs =>
    if a < b then inter as (b :: bs)
    else if b < a then inter (a :: as) bs
    else a :: inter as bs
termination_by left right => left.length + right.length

private theorem mem_inter_left {a b : List Nat} {x : Nat} (h : x ∈ inter a b) : x ∈ a ∧ x ∈ b := by
  induction a, b using inter.induct with
  | case1 => simp [inter] at h
  | case2 => simp [inter] at h
  | case3 a as b bs hlt ih =>
    simp only [inter, hlt, ite_true] at h
    obtain ⟨h1, h2⟩ := ih h
    exact ⟨List.mem_cons_of_mem _ h1, h2⟩
  | case4 a as b bs hlt hgt ih =>
    simp only [inter, hlt, ite_false, hgt, ite_true] at h
    obtain ⟨h1, h2⟩ := ih h
    exact ⟨h1, List.mem_cons_of_mem _ h2⟩
  | case5 a as b bs hlt hgt ih =>
    simp only [inter, hlt, ite_false, hgt, List.mem_cons] at h
    have hab : a = b := by omega
    subst hab
    rcases h with rfl | h
    · simp
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

private theorem inter_sorted {a b : List Nat} (ha : Sorted a) : Sorted (inter a b) := by
  induction a, b using inter.induct with
  | case1 => simp [inter]
  | case2 => simp [inter]
  | case3 a as b bs hlt ih =>
    simp only [inter, hlt, ite_true]
    exact ih (List.pairwise_cons.1 ha).2
  | case4 a as b bs hlt hgt ih =>
    simp only [inter, hlt, ite_false, hgt, ite_true]
    exact ih ha
  | case5 a as b bs hlt hgt ih =>
    simp only [inter, hlt, ite_false, hgt]
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 ha
    exact List.pairwise_cons.2 ⟨fun y hy => h1 y (mem_inter_left hy).1, ih h2⟩

private theorem mem_inter_right {a b : List Nat} {x : Nat} (ha : Sorted a) (hb : Sorted b) (hxa : x ∈ a) (hxb : x ∈ b) :
    x ∈ inter a b := by
  induction a, b using inter.induct with
  | case1 => simp at hxa
  | case2 => simp at hxb
  | case3 a as b bs hlt ih =>
    simp only [inter, hlt, ite_true]
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 ha
    obtain ⟨h3, _⟩ := List.pairwise_cons.1 hb
    refine ih h2 hb ?_ hxb
    rcases List.mem_cons.1 hxa with rfl | h
    · rcases List.mem_cons.1 hxb with rfl | h'
      · omega
      · have := h3 _ h'
        omega
    · exact h
  | case4 a as b bs hlt hgt ih =>
    simp only [inter, hlt, ite_false, hgt, ite_true]
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 hb
    obtain ⟨h3, _⟩ := List.pairwise_cons.1 ha
    refine ih ha h2 hxa ?_
    rcases List.mem_cons.1 hxb with rfl | h
    · rcases List.mem_cons.1 hxa with rfl | h'
      · omega
      · have := h3 _ h'
        omega
    · exact h
  | case5 a as b bs hlt hgt ih =>
    simp only [inter, hlt, ite_false, hgt, List.mem_cons]
    have hab : a = b := by omega
    subst hab
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 ha
    obtain ⟨_, h4⟩ := List.pairwise_cons.1 hb
    rcases List.mem_cons.1 hxa with rfl | h
    · exact .inl rfl
    · rcases List.mem_cons.1 hxb with rfl | h'
      · exact .inl rfl
      · exact .inr (ih h2 h4 h h')

private def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | a :: as => if x < a then x :: a :: as else if a < x then a :: insertSorted x as else a :: as

private theorem mem_insertSorted (x y : Nat) (l : List Nat) : y ∈ insertSorted x l ↔ y = x ∨ y ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons a as ih =>
    simp only [insertSorted]
    split
    · simp
    · split
      · simp only [List.mem_cons, ih]
        grind
      · have : x = a := by omega
        subst this
        simp

private theorem insertSorted_sorted (x : Nat) {l : List Nat} (h : Sorted l) : Sorted (insertSorted x l) := by
  induction l with
  | nil => simp [insertSorted]
  | cons a as ih =>
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    simp only [insertSorted]
    split
    · rename_i hlt
      refine List.pairwise_cons.2 ⟨fun y hy => ?_, h⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hlt
      · have := h1 y hy
        omega
    · split
      · rename_i _ hgt
        refine List.pairwise_cons.2 ⟨fun y hy => ?_, ih h2⟩
        rcases (mem_insertSorted _ _ _).1 hy with rfl | hy
        · exact hgt
        · exact h1 y hy
      · exact h

/-- The positions of a list, from `index` on. -/
private def posTable : Nat → List Nat → HashMap Nat Nat → HashMap Nat Nat
  | _, [], table => table
  | index, x :: xs, table => posTable (index + 1) xs (table.insert x index)

private theorem posTable_get {index : Nat} {l : List Nat} {table : HashMap Nat Nat} {y : Nat} (hy : y ∉ l) :
    (posTable index l table).get? y = table.get? y := by
  induction l generalizing index table with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at hy
    simp only [posTable]
    rw [ih hy.2]
    simp only [HashMap.get?_eq_getElem?, HashMap.getElem?_insert]
    have : (x == y) = false := by simpa using fun e : x = y => hy.1 e.symm
    simp [this]

/-- Where an element is in a list without repeats. -/
private theorem posTable_at {l : List Nat} (hl : l.Nodup) (index : Nat) (table : HashMap Nat Nat) (k : Nat) (hk : k < l.length) :
    (posTable index l table).getD l[k] 0 = index + k := by
  induction l generalizing index table k with
  | nil => simp at hk
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.1 hl
    simp only [posTable]
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero, HashMap.getD_eq_getD_getElem?]
      have := posTable_get (index := index + 1) (table := table.insert x index) hx
      simp only [HashMap.get?_eq_getElem?] at this
      rw [this]
      simp
    | succ k =>
      simp only [List.getElem_cons_succ]
      rw [ih hxs (index + 1) _ k (by simpa using hk)]
      omega

/-- Reads the elements of `l`, whose positions start at `index`, at the ascending positions of `row`. -/
private def select : Nat → List Nat → List Nat → List Nat
  | _, [], _ => []
  | _, _, [] => []
  | index, x :: xs, r :: rs =>
    if index = r then x :: select (index + 1) xs rs else select (index + 1) xs (r :: rs)

private theorem select_eq (pos : Nat → Nat) {l : List Nat} {index : Nat} {row : List Nat} (hrow : Sorted row)
    (hge : ∀ r ∈ row, index ≤ r) (hpos : ∀ (k : Nat) (hk : k < l.length), pos l[k] = index + k) :
    select index l row = l.filter fun x => decide (pos x ∈ row) := by
  induction l generalizing index row with
  | nil => simp [select]
  | cons x xs ih =>
    have hx : pos x = index := hpos 0 (by simp)
    have hrest : ∀ (k : Nat) (hk : k < xs.length), pos xs[k] = index + 1 + k := by
      intro k hk
      have := hpos (k + 1) (by simpa using hk)
      simp only [List.getElem_cons_succ] at this
      omega
    have hxs : ∀ y ∈ xs, index < pos y := by
      intro y hy
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hy
      have := hrest k hk
      omega
    cases row with
    | nil =>
      simp only [select, List.not_mem_nil, decide_false]
      rw [List.filter_cons]
      simp
    | cons r rs =>
      obtain ⟨h1, h2⟩ := List.pairwise_cons.1 hrow
      have hr := hge r List.mem_cons_self
      simp only [select, List.filter_cons, hx]
      by_cases he : index = r
      · subst he
        simp only [↓reduceIte, List.mem_cons, true_or, decide_true]
        rw [ih h2 (fun y hy => h1 y hy) hrest]
        congr 1
        apply List.filter_congr
        intro y hy
        have := hxs y hy
        have hne : pos y ≠ index := by omega
        simp [hne]
      · have hgt : index < r := by omega
        have hni : index ∉ r :: rs := by
          intro hm
          rcases List.mem_cons.1 hm with h | h
          · exact he h
          · have := h1 _ h
            omega
        simp only [he, ↓reduceIte, hni, decide_false, Bool.false_eq_true]
        exact ih hrow (fun y hy => by
          rcases List.mem_cons.1 hy with rfl | h
          · exact hgt
          · have := h1 _ h
            omega) hrest

/-- `select` of `elements` from the start, reading each position of the row and not all the others. -/
private def pick (elements : Array Nat) (row : List Nat) : List Nat := row.filterMap fun r => elements[r]?

private theorem filterMap_congr_mem {α β : Type} {f g : α → Option β} {l : List α} (h : ∀ x ∈ l, f x = g x) :
    l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filterMap_cons, h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

private theorem select_eq_filterMap (l : List Nat) {index : Nat} {row : List Nat} (hrow : Sorted row) (hge : ∀ r ∈ row, index ≤ r) :
    select index l row = row.filterMap fun r => l[r - index]? := by
  induction l generalizing index row with
  | nil =>
    simp only [select]
    induction row with
    | nil => rfl
    | cons r rs _ => simp
  | cons x xs ih =>
    cases row with
    | nil => rfl
    | cons r rs =>
      have hr := hge r List.mem_cons_self
      simp only [select]
      obtain ⟨hlt, hrs⟩ := List.pairwise_cons.1 hrow
      split
      · rename_i he
        subst he
        rw [ih hrs fun y hy => hlt y hy]
        simp only [List.filterMap_cons, Nat.sub_self, List.getElem?_cons_zero]
        congr 1
        apply filterMap_congr_mem
        intro y hy
        have := hlt y hy
        have hs : y - index = (y - (index + 1)) + 1 := by omega
        rw [hs, List.getElem?_cons_succ]
      · rename_i hne
        have hall : ∀ y ∈ r :: rs, index + 1 ≤ y := by
          intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · omega
          · have := hlt y hy
            omega
        rw [ih hrow hall]
        apply filterMap_congr_mem
        intro y hy
        have := hall y hy
        have hs : y - index = (y - (index + 1)) + 1 := by omega
        rw [hs, List.getElem?_cons_succ]

private theorem pick_eq (l : List Nat) {row : List Nat} (hrow : Sorted row) : pick l.toArray row = select 0 l row := by
  rw [select_eq_filterMap l hrow (fun _ _ => Nat.zero_le _)]
  simp [pick]

/-- The dominators a block has from its predecessors so far: the ones not known yet don't restrict it. -/
private def meet (table : HashMap Nat (List Nat)) (preds : List Nat) : Option (List Nat) :=
  match preds.filterMap table.get? with
  | [] => none
  | first :: rest => some (rest.foldl inter first)

/-- A pass of dominator sets over the nodes, each from the latest sets of its predecessors. -/
private def domPass (pos : HashMap Nat Nat) (preds : HashMap Nat (List Nat)) (start : Nat) (nodes : List Nat)
    (table : HashMap Nat (List Nat)) : HashMap Nat (List Nat) × Bool :=
  nodes.foldl (init := (table, false)) fun state node =>
    if node = start then state
    else
      match meet state.1 (preds.getD node []) with
      | none => state
      | some common =>
        let row := insertSorted (pos.getD node 0) common
        if state.1.get? node = some row then state else (state.1.insert node row, true)

private def domLoop (pos : HashMap Nat Nat) (preds : HashMap Nat (List Nat)) (start : Nat) (nodes : List Nat) :
    Nat → HashMap Nat (List Nat) → HashMap Nat (List Nat)
  | 0, table => table
  | fuel + 1, table =>
    let (next, changed) := domPass pos preds start nodes table
    if changed then domLoop pos preds start nodes fuel next else next

/-- The sets are a fixpoint, with every predecessor taken into account. -/
private def domCheck (pos : HashMap Nat Nat) (preds : HashMap Nat (List Nat)) (start : Nat) (nodes : List Nat)
    (table : HashMap Nat (List Nat)) : Bool :=
  let member : HashSet Nat := HashSet.ofList nodes
  nodes.all fun node =>
    if node = start then table.get? node == some [pos.getD node 0]
    else
      (preds.getD node []).all (fun pred => !member.contains pred || table.contains pred) &&
      match meet table (preds.getD node []) with
      | none => false
      | some common => table.get? node == some (insertSorted (pos.getD node 0) common)

/-- The dominator sets, from nothing known but the start. -/
private def domTable (pos : HashMap Nat Nat) (preds : HashMap Nat (List Nat)) (start : Nat) (nodes : List Nat) :
    HashMap Nat (List Nat) :=
  domLoop pos preds start nodes (nodes.length + 2)
    (if nodes.contains start then HashMap.insert {} start [pos.getD start 0] else {})

/-- `dominators`. Sets of positions in `reachable`, ascending, make the rows in that order. -/
def dominators (graph : Graph Nat) (start : Nat) : List (Nat × List Nat) :=
  let nodes := reachable graph start
  let unique := dedup nodes
  let pos := posTable 0 unique {}
  let preds := predecessorTable graph
  let table := domTable pos preds start unique
  let elements := unique.toArray
  if domCheck pos preds start unique table then
    nodes.map fun node =>
      (node, if node = start then [start] else
        node :: (pick elements ((table.get? node).getD [])).filter (· != node))
  else
    Bap.Graph.dominators graph start

section DomProofs

variable {graph : Graph Nat} {start : Nat}

private theorem mem_predecessorTable (a b : Nat) : a ∈ (predecessorTable graph).getD b [] ↔ (a, b) ∈ graph.edges := by
  rw [predecessorTable, groupBy_getD]
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨⟨⟨u, v⟩, he, rfl⟩, rfl⟩, rfl⟩
    exact he
  · intro h
    exact ⟨(b, a), ⟨⟨(a, b), h, rfl⟩, rfl⟩, rfl⟩

private theorem mem_foldl_inter_left {rest : List (List Nat)} {first : List Nat} {x : Nat}
    (h : x ∈ rest.foldl inter first) : x ∈ first ∧ ∀ v ∈ rest, x ∈ v := by
  induction rest generalizing first with
  | nil => simpa using h
  | cons v vs ih =>
    obtain ⟨h1, h2⟩ := ih h
    obtain ⟨h3, h4⟩ := mem_inter_left h1
    exact ⟨h3, fun w hw => by
      rcases List.mem_cons.1 hw with rfl | hw
      · exact h4
      · exact h2 w hw⟩

private theorem foldl_inter_right {rest : List (List Nat)} {first : List Nat} {x : Nat} (hs : Sorted first)
    (hall : ∀ v ∈ rest, Sorted v) (h1 : x ∈ first) (h2 : ∀ v ∈ rest, x ∈ v) :
    x ∈ rest.foldl inter first ∧ Sorted (rest.foldl inter first) := by
  induction rest generalizing first with
  | nil => exact ⟨h1, hs⟩
  | cons v vs ih =>
    exact ih (inter_sorted hs) (fun w hw => hall w (List.mem_cons_of_mem _ hw))
      (mem_inter_right hs (hall v List.mem_cons_self) h1 (h2 v List.mem_cons_self))
      (fun w hw => h2 w (List.mem_cons_of_mem _ hw))

private theorem foldl_inter_sorted {rest : List (List Nat)} {first : List Nat} (hs : Sorted first) :
    Sorted (rest.foldl inter first) := by
  induction rest generalizing first with
  | nil => exact hs
  | cons v vs ih => exact ih (inter_sorted hs)

/-- What holds of the sets all along: each is ascending, and has every true dominator. -/
private def Holds (graph : Graph Nat) (start : Nat) (pos : Nat → Nat) (table : HashMap Nat (List Nat)) : Prop :=
  ∀ n row, table.get? n = some row → n ∈ Bap.Graph.reachable graph start ∧ Sorted row ∧
    ∀ d, Bap.Proofs.Graph.Dom graph start n d → pos d ∈ row

private theorem holds_meet {pos : Nat → Nat} {table : HashMap Nat (List Nat)} (h : Holds graph start pos table)
    {n : Nat} (hnn : n ∈ graph.nodes) {common : List Nat} (hm : meet table ((predecessorTable graph).getD n []) = some common) :
    Sorted common ∧ ∀ d, d ≠ n → Bap.Proofs.Graph.Dom graph start n d → pos d ∈ common := by
  simp only [meet] at hm
  split at hm
  · cases hm
  · rename_i first rest he
    cases hm
    have hmem : ∀ v, v ∈ first :: rest → ∃ a, a ∈ (predecessorTable graph).getD n [] ∧ table.get? a = some v := by
      intro v hv
      rw [← he] at hv
      obtain ⟨a, ha, hget⟩ := List.mem_filterMap.1 hv
      exact ⟨a, ha, hget⟩
    have hsorted : ∀ v, v ∈ first :: rest → Sorted v := by
      intro v hv
      obtain ⟨a, _, hget⟩ := hmem v hv
      exact (h a v hget).2.1
    refine ⟨foldl_inter_sorted (hsorted first List.mem_cons_self), fun d hdn hdom => ?_⟩
    have hin : ∀ v, v ∈ first :: rest → pos d ∈ v := by
      intro v hv
      obtain ⟨a, ha, hget⟩ := hmem v hv
      obtain ⟨hreach, _, hc⟩ := h a v hget
      refine hc d fun q hq => ?_
      have he := (mem_predecessorTable a n).1 ha
      rcases List.mem_cons.1 (hdom _ (.cons hq he hnn)) with h' | h'
      · exact absurd h' hdn
      · exact h'
    exact (foldl_inter_right (hsorted first List.mem_cons_self) (fun v hv => hsorted v (List.mem_cons_of_mem _ hv))
      (hin first List.mem_cons_self) (fun v hv => hin v (List.mem_cons_of_mem _ hv))).1

private theorem domPass_holds (pos : HashMap Nat Nat) {nodes : List Nat} {table : HashMap Nat (List Nat)}
    (hnodes : ∀ n ∈ nodes, n ∈ Bap.Graph.reachable graph start)
    (h : Holds graph start (pos.getD · 0) table) :
    Holds graph start (pos.getD · 0) (domPass pos (predecessorTable graph) start nodes table).1 := by
  have key : ∀ (l : List Nat) (state : HashMap Nat (List Nat) × Bool), (∀ n ∈ l, n ∈ Bap.Graph.reachable graph start) →
      Holds graph start (pos.getD · 0) state.1 →
      Holds graph start (pos.getD · 0) (l.foldl (fun state node =>
        if node = start then state
        else
          match meet state.1 ((predecessorTable graph).getD node []) with
          | none => state
          | some common =>
            let row := insertSorted (pos.getD node 0) common
            if state.1.get? node = some row then state else (state.1.insert node row, true)) state).1 := by
    intro l
    induction l with
    | nil => intro state _ hs; exact hs
    | cons node rest ih =>
      intro state hl hs
      simp only [List.foldl_cons]
      apply ih _ fun n hn => hl n (List.mem_cons_of_mem _ hn)
      have hreach := hl node List.mem_cons_self
      split
      · exact hs
      · rename_i hne
        split
        · exact hs
        · rename_i common hm
          split
          · exact hs
          · intro n row hget
            simp only [HashMap.get?_eq_getElem?, HashMap.getElem?_insert] at hget
            split at hget
            · rename_i heq
              have hnn : node = n := by simpa using heq
              subst hnn
              cases hget
              obtain ⟨hsorted, hdoms⟩ := holds_meet hs (Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ hreach) hm
              refine ⟨hreach, insertSorted_sorted _ hsorted, fun d hdom => ?_⟩
              rw [mem_insertSorted]
              by_cases hd : d = node
              · exact .inl (by rw [hd])
              · exact .inr (hdoms d hd hdom)
            · exact hs n row hget
  exact key nodes (table, false) hnodes h

private theorem domLoop_holds (pos : HashMap Nat Nat) {nodes : List Nat}
    (hnodes : ∀ n ∈ nodes, n ∈ Bap.Graph.reachable graph start) (fuel : Nat) {table : HashMap Nat (List Nat)}
    (h : Holds graph start (pos.getD · 0) table) :
    Holds graph start (pos.getD · 0) (domLoop pos (predecessorTable graph) start nodes fuel table) := by
  induction fuel generalizing table with
  | zero => exact h
  | succ fuel ih =>
    simp only [domLoop]
    have hp := domPass_holds pos hnodes h
    cases hr : domPass pos (predecessorTable graph) start nodes table with
    | mk next changed =>
      rw [hr] at hp
      cases changed with
      | true => exact ih hp
      | false => exact hp

private theorem mem_meet {table : HashMap Nat (List Nat)} {preds : List Nat} {common : List Nat} {x : Nat}
    (hm : meet table preds = some common) (hx : x ∈ common) {a : Nat} {v : List Nat} (ha : a ∈ preds)
    (hv : table.get? a = some v) : x ∈ v := by
  simp only [meet] at hm
  split at hm
  · cases hm
  · rename_i first rest he
    cases hm
    have hmem : v ∈ first :: rest := by
      rw [← he]
      exact List.mem_filterMap.2 ⟨a, ha, hv⟩
    obtain ⟨h1, h2⟩ := mem_foldl_inter_left hx
    rcases List.mem_cons.1 hmem with rfl | h
    · exact h1
    · exact h2 v h

/-- What a set that checks out has is a true dominator. -/
private theorem domCheck_sound {posT : HashMap Nat Nat} {nodes : List Nat} {table : HashMap Nat (List Nat)}
    (hnodes : ∀ n, n ∈ nodes ↔ n ∈ Bap.Graph.reachable graph start)
    (hinj : ∀ x ∈ nodes, ∀ y ∈ nodes, posT.getD x 0 = posT.getD y 0 → x = y)
    (hc : domCheck posT (predecessorTable graph) start nodes table = true) :
    ∀ {n : Nat} {p : List Nat}, Bap.Proofs.Graph.Walk graph start n p → ∀ row d, table.get? n = some row → d ∈ nodes →
      posT.getD d 0 ∈ row → d ∈ p := by
  intro n p hw
  have hcheck := List.all_eq_true.1 hc
  have hatStart : ∀ {row d}, start ∈ nodes → table.get? start = some row → d ∈ nodes → posT.getD d 0 ∈ row → d = start := by
    intro row d hs hget hd hmem
    have hst := hcheck start hs
    simp only [↓reduceIte, beq_iff_eq, hget, Option.some.injEq] at hst
    subst hst
    exact hinj d hd start hs (by simpa using hmem)
  induction hw with
  | nil hs =>
    intro row d hget hd hmem
    have hsr : start ∈ nodes := (hnodes _).2 ((Bap.Proofs.Graph.mem_reachable_iff_walk start).2 ⟨_, .nil hs⟩)
    simp [hatStart hsr hget hd hmem]
  | @cons a b q w he hbn ih =>
    intro row d hget hd hmem
    have hbr : b ∈ nodes := (hnodes _).2 ((Bap.Proofs.Graph.mem_reachable_iff_walk b).2 ⟨_, .cons w he hbn⟩)
    have har : a ∈ nodes := (hnodes _).2 ((Bap.Proofs.Graph.mem_reachable_iff_walk a).2 ⟨_, w⟩)
    by_cases hb : b = start
    · subst hb
      rw [hatStart hbr hget hd hmem]
      exact List.mem_cons_self
    · have hchk := hcheck b hbr
      simp only [hb, ↓reduceIte, Bool.and_eq_true, List.all_eq_true] at hchk
      obtain ⟨hall, hmatch⟩ := hchk
      have hpred := (mem_predecessorTable a b).2 he
      have hcontains : table.contains a = true := by
        have := hall a hpred
        simpa [har] using this
      obtain ⟨v, hv⟩ : ∃ v, table.get? a = some v := by
        rw [HashMap.contains_eq_isSome_getElem?] at hcontains
        exact Option.isSome_iff_exists.1 hcontains
      split at hmatch
      · cases hmatch
      · rename_i common hm
        simp only [hget, beq_iff_eq, Option.some.injEq] at hmatch
        subst hmatch
        rcases (mem_insertSorted _ _ _).1 hmem with heq | hin
        · rw [hinj d hd b hbr heq]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih v d hv hd (mem_meet hm hin hpred hv))

open Classical in
theorem dominators_eq (graph : Graph Nat) (start : Nat) :
    dominators graph start = Bap.Graph.dominators graph start := by
  unfold dominators
  dsimp only
  split
  · rename_i hc
    rw [Bap.Proofs.Graph.dominators_rows]
    simp only [reachable_eq, dedup_eq] at hc ⊢
    apply List.map_congr_left
    intro node hnode
    congr 1
    by_cases hns : node = start
    · simp [hns]
    · simp only [hns, ite_false]
      refine congrArg (node :: ·) ?_
      generalize hu : (Bap.Graph.reachable graph start).eraseDups = unique at *
      have hund : unique.Nodup := by
        rw [← hu]
        exact Bap.Proofs.Graph.nodup_eraseDups _
      have hunodes : ∀ n, n ∈ unique ↔ n ∈ Bap.Graph.reachable graph start := by
        intro n
        rw [← hu, List.mem_eraseDups]
      generalize hp : posTable 0 unique {} = posT at *
      have hposAt : ∀ (k : Nat) (hk : k < unique.length), posT.getD unique[k] 0 = k := by
        intro k hk
        have := posTable_at hund 0 {} k hk
        rw [hp] at this
        simpa using this
      have hinj : ∀ x ∈ unique, ∀ y ∈ unique, posT.getD x 0 = posT.getD y 0 → x = y := by
        intro x hx y hy he
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
        rw [hposAt, hposAt] at he
        subst he
        rfl
      have hinitial : Holds graph start (posT.getD · 0)
          (if unique.contains start then HashMap.insert {} start [posT.getD start 0] else {}) := by
        split
        · rename_i hcon
          intro n row hget
          simp only [HashMap.get?_eq_getElem?, HashMap.getElem?_insert] at hget
          split at hget
          · rename_i heq
            have : start = n := by simpa using heq
            subst this
            cases hget
            have hsr : start ∈ Bap.Graph.reachable graph start := (hunodes _).1 (by simpa using hcon)
            refine ⟨hsr, by simp, fun d hdom => ?_⟩
            have hsn : start ∈ graph.nodes := Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ hsr
            have := hdom _ (.nil hsn)
            simp only [List.mem_singleton] at this
            simp [this]
          · simp at hget
        · intro n row hget
          simp at hget
      have hholds := domLoop_holds posT (nodes := unique) (fun n hn => (hunodes n).1 hn) (unique.length + 2) hinitial
      rw [show domLoop posT (predecessorTable graph) start unique (unique.length + 2)
        (if unique.contains start then HashMap.insert {} start [posT.getD start 0] else {}) =
        domTable posT (predecessorTable graph) start unique from rfl] at hholds
      generalize domTable posT (predecessorTable graph) start unique = table at *
      have hnodeu : node ∈ unique := (hunodes node).2 hnode
      obtain ⟨row, hrow⟩ : ∃ row, table.get? node = some row := by
        have hchk := List.all_eq_true.1 hc node hnodeu
        simp only [hns, ↓reduceIte, Bool.and_eq_true] at hchk
        have hm := hchk.2
        split at hm
        · cases hm
        · exact ⟨_, by simpa using hm⟩
      obtain ⟨hreach, hsorted, hcomplete⟩ := hholds node row hrow
      simp only [hrow, Option.getD_some]
      rw [pick_eq _ hsorted, select_eq (posT.getD · 0) hsorted (fun _ _ => Nat.zero_le _) (fun k hk => by simpa using hposAt k hk), List.filter_filter]
      apply List.filter_congr
      intro d hd
      by_cases hdn : d = node
      · subst hdn
        simp
      · rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        have hne : (d != node) = true := by simpa using hdn
        constructor
        · rintro ⟨_, hm⟩
          exact ⟨fun p hp => domCheck_sound hunodes hinj hc hp row d hrow hd hm, hdn⟩
        · rintro ⟨hdom, _⟩
          exact ⟨hne, hcomplete d hdom⟩
  · rfl

/-! ### Immediate dominators and the dominance frontier -/

/-! Immediate dominators as Cooper, Harvey and Kennedy find them: an iteration from what is known of the start, each node taking what its predecessors have in common. Their
tree has what the nodes have in common as ancestors, and a walk up from two nodes finds it, but a change of a parent changes the sets of all that hang under it, for
which the iteration is not known to stay above the dominators on all graphs (the equations have more than one solution). So a node here has its set, and the sets share their
tails, each with a number: the same walk stops where two sets have the same tail, and a pass that changes nothing takes as long as the edges do. -/

/-- A set of positions, largest first, whose tails are shared. -/
inductive Row where
  | nil
  | cons (id element : Nat) (tail : Row)

namespace Row

def id : Row → Nat
  | nil => 0
  | cons id _ _ => id

def elements : Row → List Nat
  | nil => []
  | cons _ element tail => element :: elements tail

/-- Whether a number is above all of the row. -/
def under (element : Nat) : Row → Bool
  | nil => true
  | cons _ first _ => first < element

/-- What two rows have in common, and the next number to give. It stops at a tail they share, and makes a row only of what they don't. -/
def meet : Row → Row → Nat → Nat × Row
  | nil, _, next => (next, nil)
  | _, nil, next => (next, nil)
  | cons ia ea ta, cons ib eb tb, next =>
    if ia = ib then (next, cons ia ea ta)
    else if ea = eb then
      match meet ta tb next with
      | (next, tail) =>
        if tail.id = ta.id then (next, cons ia ea ta)
        else if tail.id = tb.id then (next, cons ib eb tb)
        else (next + 1, cons next ea tail)
    else if ea > eb then meet ta (cons ib eb tb) next
    else meet (cons ia ea ta) tb next
termination_by a b => sizeOf a + sizeOf b

end Row

/-- What the defined predecessors have in common. -/
private def rowMeet (table : HashMap Nat Row) (preds : List Nat) (next : Nat) : Option (Nat × Row) :=
  match preds.filterMap table.get? with
  | [] => none
  | first :: rest => some (rest.foldl (fun state row => Row.meet state.2 row state.1) (next, first))

private def rowStep (pos : HashMap Nat Nat) (preds : HashMap Nat (List Nat)) (start : Nat)
    (state : HashMap Nat Row × Nat × Bool) (node : Nat) : HashMap Nat Row × Nat × Bool :=
  if node = start then state
  else
    match rowMeet state.1 (preds.getD node []) state.2.1 with
    | none => state
    | some (next, common) =>
      let element := pos.getD node 0
      if common.under element then
        match state.1.get? node with
        | some (.cons _ old tail) =>
          if old = element ∧ tail.id = common.id then (state.1, next, state.2.2)
          else (state.1.insert node (.cons next element common), next + 1, true)
        | _ => (state.1.insert node (.cons next element common), next + 1, true)
      else (state.1, next, state.2.2)

private def rowPass (pos : HashMap Nat Nat) (preds : HashMap Nat (List Nat)) (start : Nat) (nodes : List Nat)
    (table : HashMap Nat Row) (next : Nat) : HashMap Nat Row × Nat × Bool :=
  nodes.foldl (rowStep pos preds start) (table, next, false)

private def rowLoop (pos : HashMap Nat Nat) (preds : HashMap Nat (List Nat)) (start : Nat) (nodes : List Nat) :
    Nat → HashMap Nat Row → Nat → HashMap Nat Row × Nat
  | 0, table, next => (table, next)
  | fuel + 1, table, next =>
    match rowPass pos preds start nodes table next with
    | (table, next, true) => rowLoop pos preds start nodes fuel table next
    | (table, next, false) => (table, next)

/-- The rows are a fixpoint, with every predecessor taken into account. -/
private def rowCheck (pos : HashMap Nat Nat) (preds : HashMap Nat (List Nat)) (start : Nat) (member : HashSet Nat) (table : HashMap Nat Row) :
    List Nat → Nat → Bool
  | [], _ => true
  | node :: rest, next =>
    if node = start then
      (match table.get? node with
        | some (.cons _ element .nil) => element = pos.getD node 0
        | _ => false) &&
      rowCheck pos preds start member table rest next
    else
      (preds.getD node []).all (fun pred => !member.contains pred || table.contains pred) &&
      match rowMeet table (preds.getD node []) next with
      | none => false
      | some (next, common) =>
        (match table.get? node with
          | some (.cons _ element tail) => element = pos.getD node 0 && tail.id = common.id
          | _ => false) &&
        rowCheck pos preds start member table rest next

/-- The immediate dominator of a node: the largest of its strict dominators, whose row is all the others. -/
private def rowIdom (table : HashMap Nat Row) (elements : Array Nat) (node : Nat) : Option Nat :=
  match table.get? node with
  | some (.cons _ _ (.cons id element _)) =>
    match elements[element]? with
    | some parent =>
      match table.get? parent with
      | some row => if row.id = id then some parent else none
      | none => none
    | none => none
  | _ => none

/-- `immediateDominators`, with the sizes of the rows in a table. What `rowImmediateDominators` can't show correct comes here. -/
private def slowImmediateDominators (graph : Graph Nat) (start : Nat) : List (Nat × Nat) :=
  let rows := dominators graph start
  let sizes := assocTable (rows.map fun entry => (entry.1, entry.2.length))
  rows.filterMap fun entry =>
    let node := entry.1
    if node = start then
      none
    else
      let strict := entry.2.filter fun candidate => @bne Nat instBEqOfDecidableEq candidate node
      strict.foldl (fun best candidate =>
        match best with
        | none => some (node, candidate)
        | some (_, current) =>
          if sizes.getD candidate 0 > sizes.getD current 0 then some (node, candidate) else best) none

private theorem sizes_getD (rows : List (Nat × List Nat)) (key : Nat) :
    (assocTable (rows.map fun entry => (entry.1, entry.2.length))).getD key 0 = ((Assoc.get key rows).getD []).length := by
  have hlook : Assoc.get key (rows.map fun entry => (entry.1, entry.2.length)) = (Assoc.get key rows).map List.length := by
    induction rows with
    | nil => rfl
    | cons head tail ih =>
      obtain ⟨k, v⟩ := head
      simp only [Assoc.get, List.map_cons, List.lookup_cons] at ih ⊢
      by_cases hk : key = k
      · simp [hk]
      · have : (key == k) = false := by simpa using hk
        simp [this, ih]
  have hget := assocTable_get (rows.map fun entry => (entry.1, entry.2.length)) key
  rw [hlook] at hget
  simp only [HashMap.get?_eq_getElem?] at hget
  rw [HashMap.getD_eq_getD_getElem?, hget]
  cases Assoc.get key rows <;> rfl

private theorem slowImmediateDominators_eq (graph : Graph Nat) (start : Nat) :
    slowImmediateDominators graph start = Bap.Graph.immediateDominators graph start := by
  simp only [slowImmediateDominators, Bap.Graph.immediateDominators, dominators_eq, sizes_getD]
  apply congrArg (fun f => List.filterMap f (Bap.Graph.dominators graph start))
  funext entry
  split
  · rfl
  · congr 1
    funext best candidate
    cases best with
    | none => rfl
    | some pair =>
      obtain ⟨a, c⟩ := pair
      rfl

/-- `immediateDominators` from the rows. -/
def immediateDominators (graph : Graph Nat) (start : Nat) : List (Nat × Nat) :=
  let nodes := reachable graph start
  let unique := dedup nodes
  let pos := posTable 0 unique {}
  let preds := predecessorTable graph
  let initial : HashMap Nat Row := if unique.contains start then HashMap.insert {} start (.cons 1 (pos.getD start 0) .nil) else {}
  let (table, next) := rowLoop pos preds start unique (unique.length + 2) initial 2
  let elements := unique.toArray
  if rowCheck pos preds start (HashSet.ofList unique) table unique next &&
      unique.all (fun node => node == start || (rowIdom table elements node).isSome) then
    nodes.filterMap fun node => if node = start then none else (rowIdom table elements node).map (node, ·)
  else
    slowImmediateDominators graph start

/-! #### The rows are what they say -/

/-- A row whose numbers a table of all rows has, largest element first. -/
private def Row.Valid (f : Nat → Option Row) : Row → Prop
  | .nil => True
  | .cons id element tail => id ≠ 0 ∧ f id = some (.cons id element tail) ∧ (∀ x ∈ tail.elements, x < element) ∧ Row.Valid f tail

private theorem Row.Valid.mono {f g : Nat → Option Row} (hfg : ∀ k r, f k = some r → g k = some r) : ∀ {r : Row}, Row.Valid f r → Row.Valid g r
  | .nil, _ => trivial
  | .cons _ _ _, ⟨h0, h1, h2, h3⟩ => ⟨h0, hfg _ _ h1, h2, Row.Valid.mono hfg h3⟩

/-- Rows with the same number are the same. -/
private theorem Row.Valid.same {f : Nat → Option Row} {a b : Row} (ha : Row.Valid f a) (hb : Row.Valid f b) (h : a.id = b.id) : a = b := by
  cases a with
  | nil =>
    cases b with
    | nil => rfl
    | cons ib eb tb => exact absurd h.symm hb.1
  | cons ia ea ta =>
    cases b with
    | nil => exact absurd h ha.1
    | cons ib eb tb =>
      have h' : ia = ib := h
      subst h'
      have := ha.2.1.symm.trans hb.2.1
      exact Option.some.inj this

private def Fresh (f : Nat → Option Row) (next : Nat) : Prop := next ≠ 0 ∧ ∀ k, next ≤ k → f k = none

private theorem Fresh.extend {f : Nat → Option Row} {next : Nat} (hf : Fresh f next) (row : Row) :
    let g : Nat → Option Row := fun k => if k = next then some row else f k
    (∀ k r, f k = some r → g k = some r) ∧ Fresh g (next + 1) := by
  intro g
  refine ⟨fun k r h => ?_, by omega, fun k hk => ?_⟩
  · have hne : k ≠ next := by
      intro he
      rw [he, hf.2 next (Nat.le_refl _)] at h
      cases h
    simp [g, hne, h]
  · have hne : k ≠ next := by omega
    simp only [g, hne, ↓reduceIte]
    exact hf.2 k (by omega)

private theorem meet_spec (a : Row) : ∀ (b : Row) (next : Nat) (f : Nat → Option Row), Row.Valid f a → Row.Valid f b → Fresh f next →
    ∃ g, (∀ k r, f k = some r → g k = some r) ∧ Fresh g (Row.meet a b next).1 ∧ Row.Valid g (Row.meet a b next).2 ∧
      ∀ x, x ∈ (Row.meet a b next).2.elements ↔ x ∈ a.elements ∧ x ∈ b.elements := by
  induction a with
  | nil =>
    intro b next f _ _ hfresh
    refine ⟨f, fun _ _ h => h, ?_, ?_, ?_⟩ <;> simp [Row.meet, Row.Valid, Row.elements, hfresh]
  | cons ia ea ta iha =>
    intro b
    induction b with
    | nil =>
      intro next f _ _ hfresh
      refine ⟨f, fun _ _ h => h, ?_, ?_, ?_⟩ <;> simp [Row.meet, Row.Valid, Row.elements, hfresh]
    | cons ib eb tb ihb =>
      intro next f hva hvb hfresh
      rw [Row.meet]
      by_cases hs : ia = ib
      · simp only [hs, ↓reduceIte]
        subst hs
        have heq : Row.cons ia ea ta = Row.cons ia eb tb := Row.Valid.same hva hvb rfl
        refine ⟨f, fun _ _ h => h, hfresh, hva, fun x => ?_⟩
        rw [← heq]
        simp
      · simp only [hs, ↓reduceIte]
        by_cases he : ea = eb
        · subst he
          simp only [↓reduceIte]
          obtain ⟨g, hfg, hf, hv, hmem⟩ := iha tb next f hva.2.2.2 hvb.2.2.2 hfresh
          generalize Row.meet ta tb next = result at hf hv hmem ⊢
          obtain ⟨next', tail⟩ := result
          simp only at hf hv hmem ⊢
          have hmemTop (x : Nat) : (x = ea ∨ x ∈ tail.elements) ↔ (x = ea ∨ x ∈ ta.elements) ∧ (x = ea ∨ x ∈ tb.elements) := by
            rw [hmem]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact ⟨Or.inl h, Or.inl h⟩
              · exact ⟨Or.inr h1, Or.inr h2⟩
            · rintro ⟨h1 | h1, h2 | h2⟩
              · exact Or.inl h1
              · exact Or.inl h1
              · exact Or.inl h2
              · exact Or.inr ⟨h1, h2⟩
          by_cases h1 : tail.id = ta.id
          · simp only [h1, ↓reduceIte]
            have hsame := Row.Valid.same hv (Row.Valid.mono hfg hva.2.2.2) h1
            subst hsame
            refine ⟨g, hfg, hf, Row.Valid.mono hfg hva, fun x => ?_⟩
            have := hmemTop x
            simpa [Row.elements] using this
          · simp only [h1, ↓reduceIte]
            by_cases h2 : tail.id = tb.id
            · simp only [h2, ↓reduceIte]
              have hsame := Row.Valid.same hv (Row.Valid.mono hfg hvb.2.2.2) h2
              subst hsame
              refine ⟨g, hfg, hf, Row.Valid.mono hfg hvb, fun x => ?_⟩
              have := hmemTop x
              simpa [Row.elements] using this
            · simp only [h2, ↓reduceIte]
              obtain ⟨hext, hfresh'⟩ := hf.extend (.cons next' ea tail)
              refine ⟨_, fun k r h => hext k r (hfg k r h), hfresh', ⟨hf.1, by simp, ?_, Row.Valid.mono hext hv⟩, fun x => ?_⟩
              · intro x hx
                exact hva.2.2.1 x ((hmem x).1 hx).1
              · have := hmemTop x
                simpa [Row.elements] using this
        · simp only [he, ↓reduceIte]
          by_cases hgt : ea > eb
          · simp only [hgt, ↓reduceIte]
            obtain ⟨g, hfg, hf, hv, hmem⟩ := iha (.cons ib eb tb) next f hva.2.2.2 hvb hfresh
            refine ⟨g, hfg, hf, hv, fun x => ?_⟩
            rw [hmem]
            simp only [Row.elements, List.mem_cons]
            constructor
            · rintro ⟨h1, h2⟩
              exact ⟨Or.inr h1, h2⟩
            · rintro ⟨h1 | h1, h2 | h2⟩
              · omega
              · have := hvb.2.2.1 x h2
                omega
              · exact ⟨h1, Or.inl h2⟩
              · exact ⟨h1, Or.inr h2⟩
          · simp only [hgt, ↓reduceIte]
            obtain ⟨g, hfg, hf, hv, hmem⟩ := ihb next f hva hvb.2.2.2 hfresh
            refine ⟨g, hfg, hf, hv, fun x => ?_⟩
            rw [hmem]
            simp only [Row.elements, List.mem_cons]
            constructor
            · rintro ⟨h1, h2⟩
              exact ⟨h1, Or.inr h2⟩
            · rintro ⟨h1 | h1, h2 | h2⟩
              · omega
              · exact ⟨Or.inl h1, h2⟩
              · have := hva.2.2.1 x h1
                omega
              · exact ⟨Or.inr h1, h2⟩

/-- A table of rows, all of them numbered, none from `next` on. -/
private def RowInv (graph : Graph Nat) (start : Nat) (pos : Nat → Nat) (f : Nat → Option Row) (next : Nat) (table : HashMap Nat Row) : Prop :=
  Fresh f next ∧ ∀ n row, table.get? n = some row → n ∈ Bap.Graph.reachable graph start ∧ Row.Valid f row ∧
    ∀ d, Bap.Proofs.Graph.Dom graph start n d → pos d ∈ row.elements

private theorem RowInv.mono {pos : Nat → Nat} {f g : Nat → Option Row} {next next' : Nat} {table : HashMap Nat Row}
    (h : RowInv graph start pos f next table) (hfg : ∀ k r, f k = some r → g k = some r) (hf : Fresh g next') :
    RowInv graph start pos g next' table :=
  ⟨hf, fun n row hget => ⟨(h.2 n row hget).1, Row.Valid.mono hfg (h.2 n row hget).2.1, (h.2 n row hget).2.2⟩⟩

private theorem foldl_meet_spec {f : Nat → Option Row} (rest : List Row) (next : Nat) (first : Row) (hf : Fresh f next) (hv : Row.Valid f first)
    (hrest : ∀ r ∈ rest, Row.Valid f r) :
    ∃ g, (∀ k r, f k = some r → g k = some r) ∧ Fresh g (rest.foldl (fun state row => Row.meet state.2 row state.1) (next, first)).1 ∧
      Row.Valid g (rest.foldl (fun state row => Row.meet state.2 row state.1) (next, first)).2 ∧
      ∀ x, x ∈ (rest.foldl (fun state row => Row.meet state.2 row state.1) (next, first)).2.elements ↔ x ∈ first.elements ∧ ∀ r ∈ rest, x ∈ r.elements := by
  induction rest generalizing next first f with
  | nil =>
    refine ⟨f, fun _ _ h => h, hf, hv, fun x => ?_⟩
    simp
  | cons head tail ih =>
    simp only [List.foldl_cons]
    obtain ⟨g, hfg, hfresh, hvg, hmem⟩ := meet_spec first head next f hv (hrest head List.mem_cons_self) hf
    obtain ⟨g', hfg', hfresh', hvg', hmem'⟩ := ih _ _ hfresh hvg fun r hr => Row.Valid.mono hfg (hrest r (List.mem_cons_of_mem _ hr))
    refine ⟨g', fun k r h => hfg' k r (hfg k r h), hfresh', hvg', fun x => ?_⟩
    rw [hmem', hmem]
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩

private theorem rowMeet_spec {pos : Nat → Nat} {f : Nat → Option Row} {next next' : Nat} {table : HashMap Nat Row} {preds : List Nat} {common : Row}
    (h : RowInv graph start pos f next table) (hm : rowMeet table preds next = some (next', common)) :
    ∃ g, (∀ k r, f k = some r → g k = some r) ∧ Fresh g next' ∧ Row.Valid g common ∧
      ∀ x, x ∈ common.elements ↔ ∀ r ∈ preds.filterMap table.get?, x ∈ r.elements := by
  simp only [rowMeet] at hm
  split at hm
  · cases hm
  · rename_i first rest he
    injection hm with hm
    have hvalid : ∀ r ∈ first :: rest, Row.Valid f r := by
      intro r hr
      rw [← he] at hr
      obtain ⟨a, _, hget⟩ := List.mem_filterMap.1 hr
      exact (h.2 a r hget).2.1
    obtain ⟨g, hfg, hf, hv, hmem⟩ := foldl_meet_spec rest next first h.1 (hvalid first List.mem_cons_self)
      (fun r hr => hvalid r (List.mem_cons_of_mem _ hr))
    rw [hm] at hf hv hmem
    refine ⟨g, hfg, hf, hv, fun x => ?_⟩
    rw [he, hmem]
    simp

/-- What the predecessors have in common has all that dominates the node, but for itself. -/
private theorem rowMeet_complete {pos : Nat → Nat} {f : Nat → Option Row} {next : Nat} {table : HashMap Nat Row} {n : Nat} {x : Nat}
    (h : RowInv graph start pos f next table) (hnn : n ∈ graph.nodes) {d : Nat} (hx : x = pos d) (hdn : d ≠ n) (hdom : Bap.Proofs.Graph.Dom graph start n d)
    {r : Row} (hr : r ∈ ((predecessorTable graph).getD n []).filterMap table.get?) : x ∈ r.elements := by
  obtain ⟨a, ha, hget⟩ := List.mem_filterMap.1 hr
  obtain ⟨_, _, hc⟩ := h.2 a r hget
  rw [hx]
  refine hc d fun q hq => ?_
  have he := (mem_predecessorTable a n).1 ha
  rcases List.mem_cons.1 (hdom _ (.cons hq he hnn)) with h' | h'
  · exact absurd h' hdn
  · exact h'

private theorem rowStep_inv (pos : HashMap Nat Nat) {node : Nat} (hnr : node ∈ Bap.Graph.reachable graph start) {state : HashMap Nat Row × Nat × Bool} {f : Nat → Option Row}
    (h : RowInv graph start (pos.getD · 0) f state.2.1 state.1) :
    ∃ g, RowInv graph start (pos.getD · 0) g (rowStep pos (predecessorTable graph) start state node).2.1 (rowStep pos (predecessorTable graph) start state node).1 := by
  have hnn : node ∈ graph.nodes := Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ hnr
  obtain ⟨table, next, changed⟩ := state
  simp only at h
  unfold rowStep
  simp only
  split
  · exact ⟨f, h⟩
  · split
    · exact ⟨f, h⟩
    · rename_i next' common hm
      obtain ⟨g, hfg, hf, hv, hmem⟩ := rowMeet_spec h hm
      have hstay : RowInv graph start (pos.getD · 0) g next' table := h.mono hfg hf
      have hinsert : Row.under (pos.getD node 0) common = true →
          ∃ g', RowInv graph start (pos.getD · 0) g' (next' + 1) (table.insert node (.cons next' (pos.getD node 0) common)) := by
        intro hu
        obtain ⟨hext, hfresh'⟩ := hf.extend (.cons next' (pos.getD node 0) common)
        have hunder : ∀ x ∈ common.elements, x < pos.getD node 0 := by
          intro x hx
          cases common with
          | nil => cases hx
          | cons i first tail =>
            have h1 : first < pos.getD node 0 := by simpa [Row.under] using hu
            rcases List.mem_cons.1 hx with rfl | hx
            · exact h1
            · have := hv.2.2.1 x hx
              omega
        refine ⟨_, hfresh', fun n row hget => ?_⟩
        simp only [HashMap.get?_eq_getElem?, HashMap.getElem?_insert] at hget
        split at hget
        · rename_i heq
          have hnode : node = n := by simpa using heq
          subst hnode
          injection hget with hget
          subst hget
          refine ⟨hnr, ⟨hf.1, by simp, hunder, Row.Valid.mono hext hv⟩, fun d hd => ?_⟩
          by_cases hdn : d = node
          · subst hdn
            simp [Row.elements]
          · refine List.mem_cons_of_mem _ ((hmem _).2 fun r hr => ?_)
            exact rowMeet_complete h hnn rfl hdn hd hr
        · obtain ⟨h1, h2, h3⟩ := h.2 n row (by simpa using hget)
          exact ⟨h1, Row.Valid.mono (fun k r hk => hext k r (hfg k r hk)) h2, h3⟩
      split
      · rename_i hu
        split
        · split
          · exact ⟨g, hstay⟩
          · exact hinsert hu
        · exact hinsert hu
      · exact ⟨g, hstay⟩

private theorem rowPass_inv (pos : HashMap Nat Nat) {nodes : List Nat} {table : HashMap Nat Row} {next : Nat} {f : Nat → Option Row}
    (hnodes : ∀ n ∈ nodes, n ∈ Bap.Graph.reachable graph start) (h : RowInv graph start (pos.getD · 0) f next table) :
    ∃ g, RowInv graph start (pos.getD · 0) g (rowPass pos (predecessorTable graph) start nodes table next).2.1 (rowPass pos (predecessorTable graph) start nodes table next).1 := by
  unfold rowPass
  generalize hs : (table, next, false) = state
  have h0 : RowInv graph start (pos.getD · 0) f state.2.1 state.1 := by subst hs; exact h
  clear hs h
  induction nodes generalizing state f with
  | nil => exact ⟨f, h0⟩
  | cons node rest ih =>
    obtain ⟨g, hg⟩ := rowStep_inv pos (hnodes node List.mem_cons_self) h0
    exact ih (fun n hn => hnodes n (List.mem_cons_of_mem _ hn)) _ hg

private theorem rowLoop_inv (pos : HashMap Nat Nat) {nodes : List Nat} (hnodes : ∀ n ∈ nodes, n ∈ Bap.Graph.reachable graph start) (fuel : Nat)
    {table : HashMap Nat Row} {next : Nat} {f : Nat → Option Row} (h : RowInv graph start (pos.getD · 0) f next table) :
    ∃ g, RowInv graph start (pos.getD · 0) g (rowLoop pos (predecessorTable graph) start nodes fuel table next).2 (rowLoop pos (predecessorTable graph) start nodes fuel table next).1 := by
  induction fuel generalizing table next f with
  | zero => exact ⟨f, h⟩
  | succ fuel ih =>
    obtain ⟨g, hg⟩ := rowPass_inv pos hnodes h
    simp only [rowLoop]
    generalize rowPass pos (predecessorTable graph) start nodes table next = result at hg
    obtain ⟨table', next', changed⟩ := result
    cases changed with
    | true => exact ih hg
    | false => exact ⟨g, hg⟩

/-- What `rowCheck` says of each node, whichever numbers its walk gives out. -/
private theorem rowCheck_spec {pos : Nat → Nat} (posT : HashMap Nat Nat) (hpos : pos = (posT.getD · 0)) {member : HashSet Nat} {table : HashMap Nat Row} {nodes : List Nat} {next : Nat} {f : Nat → Option Row}
    (h : RowInv graph start pos f next table) (hc : rowCheck posT (predecessorTable graph) start member table nodes next = true) :
    ∀ node ∈ nodes,
      (node = start → ∃ id, table.get? node = some (.cons id (pos node) .nil)) ∧
      (node ≠ start → (∀ a ∈ (predecessorTable graph).getD node [], member.contains a = true → table.contains a = true) ∧
        ∃ id tail, table.get? node = some (.cons id (pos node) tail) ∧
          ∀ a ∈ (predecessorTable graph).getD node [], ∀ v, table.get? a = some v → ∀ x ∈ tail.elements, x ∈ v.elements) := by
  subst hpos
  induction nodes generalizing next f with
  | nil => simp
  | cons node rest ih =>
    intro n hn
    rw [rowCheck] at hc
    split at hc
    · rename_i hns
      rw [Bool.and_eq_true] at hc
      obtain ⟨h1, h2⟩ := hc
      rcases List.mem_cons.1 hn with rfl | hn
      · refine ⟨fun _ => ?_, fun hne => absurd hns hne⟩
        split at h1
        · rename_i id element hget
          have : element = posT.getD n 0 := by simpa using h1
          subst this
          exact ⟨id, hget⟩
        · cases h1
      · exact ih h2 h n hn
    · rename_i hns
      rw [Bool.and_eq_true] at hc
      obtain ⟨hall, hc⟩ := hc
      split at hc
      · cases hc
      · rename_i next' common hm
        rw [Bool.and_eq_true] at hc
        obtain ⟨h1, h2⟩ := hc
        obtain ⟨g, hfg, hf, hv, hmem⟩ := rowMeet_spec h hm
        rcases List.mem_cons.1 hn with rfl | hn
        · refine ⟨fun he => absurd he hns, fun _ => ⟨?_, ?_⟩⟩
          · intro a ha hma
            have := List.all_eq_true.1 hall a ha
            simpa [hma] using this
          · split at h1
            · rename_i id element tail hget
              have hh := h1
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
              obtain ⟨he, hid⟩ := hh
              subst he
              refine ⟨id, tail, hget, fun a ha v hgetA x hx => ?_⟩
              have hvt : Row.Valid g tail := by
                have := (h.2 n _ hget).2.1
                exact Row.Valid.mono hfg this.2.2.2
              have hsame := Row.Valid.same hvt hv hid
              subst hsame
              exact (hmem x).1 hx v (List.mem_filterMap.2 ⟨a, ha, hgetA⟩)
            · cases h1
        · exact ih h2 (h.mono hfg hf) n hn

/-- What a row that checks out has is a true dominator. -/
private theorem rowCheck_sound {posT : HashMap Nat Nat} {nodes : List Nat} {table : HashMap Nat Row} {next : Nat} {f : Nat → Option Row}
    (hnodes : ∀ n, n ∈ nodes ↔ n ∈ Bap.Graph.reachable graph start)
    (hinj : ∀ x ∈ nodes, ∀ y ∈ nodes, posT.getD x 0 = posT.getD y 0 → x = y)
    (h : RowInv graph start (posT.getD · 0) f next table)
    (hc : rowCheck posT (predecessorTable graph) start (HashSet.ofList nodes) table nodes next = true) :
    ∀ {n : Nat} {p : List Nat}, Bap.Proofs.Graph.Walk graph start n p → ∀ row d, table.get? n = some row → d ∈ nodes →
      posT.getD d 0 ∈ row.elements → d ∈ p := by
  intro n p hw
  have hspec := rowCheck_spec posT rfl h hc
  have hatStart : ∀ {row d}, start ∈ nodes → table.get? start = some row → d ∈ nodes → posT.getD d 0 ∈ row.elements → d = start := by
    intro row d hs hget hd hmem
    obtain ⟨id, hid⟩ := (hspec start hs).1 rfl
    rw [hget] at hid
    injection hid with hid
    subst hid
    exact hinj d hd start hs (by simpa [Row.elements] using hmem)
  induction hw with
  | nil hs =>
    intro row d hget hd hmem
    have hsr : start ∈ nodes := (hnodes _).2 ((Bap.Proofs.Graph.mem_reachable_iff_walk start).2 ⟨_, .nil hs⟩)
    simp [hatStart hsr hget hd hmem]
  | @cons a b q w he hbn ih =>
    intro row d hget hd hmem
    have hbr : b ∈ nodes := (hnodes _).2 ((Bap.Proofs.Graph.mem_reachable_iff_walk b).2 ⟨_, .cons w he hbn⟩)
    have har : a ∈ nodes := (hnodes _).2 ((Bap.Proofs.Graph.mem_reachable_iff_walk a).2 ⟨_, w⟩)
    by_cases hb : b = start
    · subst hb
      rw [hatStart hbr hget hd hmem]
      exact List.mem_cons_self
    · obtain ⟨hall, id, tail, hrow, hcommon⟩ := (hspec b hbr).2 hb
      have hpred := (mem_predecessorTable a b).2 he
      have hcontains : table.contains a = true := hall a hpred (by simpa using har)
      obtain ⟨v, hv⟩ : ∃ v, table.get? a = some v := by
        rw [HashMap.contains_eq_isSome_getElem?] at hcontains
        exact Option.isSome_iff_exists.1 hcontains
      rw [hget] at hrow
      injection hrow with hrow
      subst hrow
      rcases List.mem_cons.1 hmem with heq | hin
      · rw [hinj d hd b hbr heq]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih v d hv hd (hcommon a hpred v hv _ hin))

/-- **The rows give the immediate dominators**, when they check out, and otherwise the slow way does. -/
theorem immediateDominators_eq (graph : Graph Nat) (start : Nat) :
    immediateDominators graph start = Bap.Graph.immediateDominators graph start := by
  unfold immediateDominators
  dsimp only
  simp only [reachable_eq, dedup_eq]
  generalize hu : (Bap.Graph.reachable graph start).eraseDups = unique
  have hund : unique.Nodup := by
    rw [← hu]
    exact Bap.Proofs.Graph.nodup_eraseDups _
  have hunodes : ∀ n, n ∈ unique ↔ n ∈ Bap.Graph.reachable graph start := by
    intro n
    rw [← hu, List.mem_eraseDups]
  generalize hp : posTable 0 unique {} = posT
  have hposAt : ∀ (k : Nat) (hk : k < unique.length), posT.getD unique[k] 0 = k := by
    intro k hk
    have := posTable_at hund 0 {} k hk
    rw [hp] at this
    simpa using this
  have hinj : ∀ x ∈ unique, ∀ y ∈ unique, posT.getD x 0 = posT.getD y 0 → x = y := by
    intro x hx y hy he
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
    rw [hposAt, hposAt] at he
    subst he
    rfl
  have hfresh0 : Fresh (fun k => if k = 1 then some (Row.cons 1 (posT.getD start 0) .nil) else none) 2 :=
    ⟨by omega, fun k hk => by
      have : k ≠ 1 := by omega
      simp [this]⟩
  have hinitial : RowInv graph start (posT.getD · 0) (fun k => if k = 1 then some (Row.cons 1 (posT.getD start 0) .nil) else none) 2
      (if unique.contains start then HashMap.insert {} start (.cons 1 (posT.getD start 0) .nil) else {}) := by
    refine ⟨hfresh0, ?_⟩
    split
    · rename_i hcon
      intro n row hget
      simp only [HashMap.get?_eq_getElem?, HashMap.getElem?_insert] at hget
      split at hget
      · rename_i heq
        have : start = n := by simpa using heq
        subst this
        cases hget
        have hsr : start ∈ Bap.Graph.reachable graph start := (hunodes _).1 (by simpa using hcon)
        refine ⟨hsr, ⟨by omega, by simp, by simp [Row.elements], trivial⟩, fun d hdom => ?_⟩
        have hsn : start ∈ graph.nodes := Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ hsr
        have := hdom _ (.nil hsn)
        simp only [List.mem_singleton] at this
        simp [this, Row.elements]
      · simp at hget
    · intro n row hget
      simp at hget
  obtain ⟨g, hg⟩ := rowLoop_inv posT (nodes := unique) (fun n hn => (hunodes n).1 hn) (unique.length + 2) hinitial
  generalize rowLoop posT (predecessorTable graph) start unique (unique.length + 2) (if unique.contains start then HashMap.insert {} start (.cons 1 (posT.getD start 0) .nil) else {}) 2 = result at hg ⊢
  obtain ⟨table, next⟩ := result
  simp only at hg ⊢
  split
  · rename_i hc
    rw [Bool.and_eq_true] at hc
    obtain ⟨hcheck, hall⟩ := hc
    have hsound := @rowCheck_sound graph start posT unique table next g hunodes hinj hg hcheck
    -- each node has what `immediateDominators_of` wants
    have hnode : ∀ n ∈ Bap.Graph.reachable graph start, n ≠ start → ∃ i, rowIdom table unique.toArray n = some i ∧ i ≠ n ∧
        Bap.Proofs.Graph.Dom graph start n i ∧ ∀ c, c ≠ n → Bap.Proofs.Graph.Dom graph start n c → Bap.Proofs.Graph.Dom graph start i c := by
      intro n hn hns
      have hnu := (hunodes n).2 hn
      have hsome := List.all_eq_true.1 hall n hnu
      have hisome : (rowIdom table unique.toArray n).isSome = true := by
        simpa [hns] using hsome
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hisome
      refine ⟨i, hi, ?_⟩
      unfold rowIdom at hi
      split at hi
      · rename_i idn en id el rest hrow
        split at hi
        · rename_i parent hel
          split at hi
          · rename_i row hparent
            split at hi
            · rename_i hrid
              injection hi with hi
              subst hi
              obtain ⟨_, hvn, hcomplete⟩ := hg.2 n _ hrow
              obtain ⟨hir, hvi, _⟩ := hg.2 parent row hparent
              have hsame : row = Row.cons id el rest := Row.Valid.same hvi hvn.2.2.2 hrid
              subst hsame
              have hlt : el < en := hvn.2.2.1 el List.mem_cons_self
              have hpa : posT.getD parent 0 = el := by
                have hel' : unique[el]? = some parent := by simpa using hel
                obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.1 hel'
                rw [← he]
                exact hposAt el hk
              have hpu : parent ∈ unique := (hunodes _).2 hir
              have hen : en = posT.getD n 0 := by
                obtain ⟨_, _, tail, hr, _⟩ := (rowCheck_spec posT rfl hg hcheck n hnu).2 hns
                rw [hrow] at hr
                injection hr with hr
                injection hr
              refine ⟨?_, ?_, ?_⟩
              · intro heq
                subst heq
                omega
              · intro p hw
                refine hsound hw _ parent hrow hpu ?_
                rw [hpa]
                exact List.mem_cons_of_mem _ List.mem_cons_self
              · intro c hcn hdom p hw
                have hcr : c ∈ unique := by
                  obtain ⟨q, hq⟩ := (Bap.Proofs.Graph.mem_reachable_iff_walk n).1 hn
                  exact (hunodes _).2 (hq.subset_reachable (hdom q hq))
                have hin := hcomplete c hdom
                rcases List.mem_cons.1 hin with he | hin
                · exact absurd (hinj c hcr n hnu (he.trans hen)) hcn
                · exact hsound hw _ c hparent hcr hin
            · cases hi
          · cases hi
        · cases hi
      · cases hi
    have heq := Bap.Proofs.Graph.immediateDominators_of (g := graph) (s := start) (fun n => (rowIdom table unique.toArray n).getD 0) (fun n hn hns => by
      obtain ⟨i, hi, h1, h2, h3⟩ := hnode n hn hns
      simpa [hi] using ⟨h1, h2, h3⟩)
    rw [heq]
    apply filterMap_congr_mem
    intro n hn
    by_cases hns : n = start
    · simp [hns]
    · obtain ⟨i, hi, _⟩ := hnode n hn hns
      simp [hns, hi]
  · exact slowImmediateDominators_eq graph start

private def walk (table : HashMap Nat Nat) (stop : Option Nat) (tid : Nat) :
    Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, result => result
  | fuel + 1, runner, result =>
    if some runner = stop then
      result
    else
      let result := (runner, tid) :: result
      match table.get? runner with
      | some next => walk table stop tid fuel next result
      | none => result

private theorem walk_eq (graph : Graph Nat) (idom : List (Nat × Nat)) (stop : Option Nat) (tid fuel runner : Nat)
    (result : List (Nat × Nat)) :
    walk (assocTable idom) stop tid fuel runner result = frontierWalk graph idom stop tid fuel runner result := by
  induction fuel generalizing runner result with
  | zero => rfl
  | succ fuel ih =>
    unfold_walk_frontierWalk
    split
    · rfl
    · split <;> simp_all

/-- `dominanceFrontier`, with its lookups in tables. -/
def dominanceFrontier (graph : Graph Nat) (start : Nat) : List (Nat × List Nat) :=
  let table := assocTable (immediateDominators graph start)
  let preds := predecessorTable graph
  let fuel := graph.nodes.length + 1
  let pairs := (reachable graph start).foldl (init := []) fun result tid =>
    (dedup (preds.getD tid [])).foldl (fun result pred => walk table (table.get? tid) tid fuel pred result) result
  let grouped := groupBy pairs
  graph.nodes.map fun node => (node, dedup (grouped.getD node []))

theorem dominanceFrontier_eq (graph : Graph Nat) (start : Nat) :
    dominanceFrontier graph start = Bap.Graph.dominanceFrontier graph start := by
  simp only [dominanceFrontier, Bap.Graph.dominanceFrontier, immediateDominators_eq, reachable_eq, predecessors_eq,
    walk_eq graph, assocTable_get]
  simp only [dedup_eq, groupBy_getD]

end DomProofs

end Bap.Graph.Fast
