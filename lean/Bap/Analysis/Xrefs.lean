import Bap.Project.Basic
import Bap.Bil.Eval

namespace Bap.Analysis.Xrefs

inductive Kind where
  | call | jump | load | store
  deriving DecidableEq, Repr

structure Xref where
  source : Nat
  target : Nat
  kind : Kind
  deriving DecidableEq, Repr

/-- The functions sorted by address, and those of an address in the order they were listed, for binary search. `reach` is,
for each one, where the functions with a size up to it end at most: below an address that all of them end at or before,
only a function without a size can still contain it. -/
structure FunctionTable where
  symbols : Array Image.Symbol
  reach : Array Nat

/-- Whether a function isn't after another. -/
def addrLe (left right : Image.Symbol) : Bool := left.addr ≤ right.addr

/-- Where a function ends, as far as its size says. -/
def sizedEnd (symbol : Image.Symbol) : Nat := if symbol.size = 0 then 0 else symbol.addr + symbol.size

namespace FunctionTable

def ofList (functions : List Image.Symbol) : FunctionTable :=
  let sorted := functions.mergeSort addrLe
  let state := sorted.foldl (init := (0, (#[] : Array Nat))) fun state symbol =>
    let most := max state.1 (sizedEnd symbol)
    (most, state.2.push most)
  { symbols := sorted.toArray, reach := state.2 }

end FunctionTable

structure Index where
  xrefs : List Xref := []
  functions : List Image.Symbol := []
  /-- The table of the functions, if anything asks for it. -/
  table : Thunk FunctionTable := Thunk.mk fun _ => FunctionTable.ofList functions
  table_eq : table.get = FunctionTable.ofList functions := by exact rfl

private def constant (exp : Bil.Exp) : Option Nat :=
  match Bil.evalExp [] exp with
  | .ok value => (Bap.Value.asBits value).toOption.map fun value => value.2.toNat
  | .error _ => none

private def memoryRefs (source : Nat) : Bil.Exp → List Xref
  | .load memory address _ _ =>
    (constant address).toList.map (⟨source, ·, .load⟩) ++ memoryRefs source memory ++ memoryRefs source address
  | .store memory address value _ _ =>
    (constant address).toList.map (⟨source, ·, .store⟩) ++
      memoryRefs source memory ++ memoryRefs source address ++ memoryRefs source value
  | .bin _ left right => memoryRefs source left ++ memoryRefs source right
  | .un _ value => memoryRefs source value
  | .cast _ _ value => memoryRefs source value
  | .letIn _ value body => memoryRefs source value ++ memoryRefs source body
  | .ite condition yes no => memoryRefs source condition ++ memoryRefs source yes ++ memoryRefs source no
  | .extract _ _ value => memoryRefs source value
  | .concat left right => memoryRefs source left ++ memoryRefs source right
  | _ => []

private def stmtRefs (insn : Disasm.Insn) : Bil.Stmt → List Xref
  | .move _ value => memoryRefs insn.address value
  | .jmp target =>
    (constant target).toList.map (⟨insn.address, ·, if insn.flow = .call then .call else .jump⟩) ++
      memoryRefs insn.address target
  | .while condition body =>
    memoryRefs insn.address condition ++ body.flatMap (stmtRefs insn)
  | .ifElse condition yes no =>
    memoryRefs insn.address condition ++ yes.flatMap (stmtRefs insn) ++ no.flatMap (stmtRefs insn)
  | _ => []

private def insnRefs (insn : Disasm.Insn) : List Xref :=
  insn.bil.flatMap (stmtRefs insn)

def create (project : Project.Project) : Index := {
  xrefs := project.disasm.map (fun disasm => disasm.instructions.flatMap insnRefs) |>.getD []
  functions := project.image.map (fun image => image.symbols.filter Image.Symbol.isFunction) |>.getD []
}

/-- The name of a function without a symbol, as upstream has it. -/
def subroutineName (address : Nat) : String :=
  "sub_" ++ String.ofList (Nat.toDigits 16 address)

/-- The addresses of the instructions of a project. -/
private def instructionAddresses (project : Project.Project) : Std.HashSet Nat :=
  (project.disasm.map fun disasm => disasm.instructions.foldl (fun set insn => set.insert insn.address) {}).getD {}

/-- The functions of a project, whatever its symbols say: its function symbols with instructions, which leaves out the
ones it imports, and a function for each start of the scan and each called instruction without a symbol, as `sub_`. -/
def discoveredFunctions (project : Project.Project) (index : Index) : List Image.Symbol :=
  let addresses := instructionAddresses project
  let named := index.functions.filter fun symbol => addresses.contains symbol.addr
  let starts := (project.image.map Project.Project.roots).getD []
  let called := index.xrefs.filterMap fun xref => if xref.kind = .call then some xref.target else none
  let state := (starts ++ called).foldl
    (init := (named.foldl (fun set symbol => set.insert symbol.addr) ({} : Std.HashSet Nat), ([] : List Image.Symbol)))
    fun state address =>
      if state.1.contains address || !addresses.contains address then state
      else (state.1.insert address, ⟨subroutineName address, address, 0, true, false⟩ :: state.2)
  named ++ state.2.reverse

/-- The index of a project, with the functions it was found to have and not only the ones its symbols tell. -/
def discover (project : Project.Project) : Index :=
  let index := create project
  let functions := discoveredFunctions project index
  { index with functions, table := Thunk.mk fun _ => FunctionTable.ofList functions, table_eq := rfl }

def functionAt (index : Index) (address : Nat) : Option Image.Symbol :=
  index.functions.find? fun symbol => symbol.addr = address

/-- The highest function start at or below `address`. -/
private def nearestStart (index : Index) (address : Nat) : Option Nat :=
  index.functions.foldl (init := none) fun best symbol =>
    if symbol.addr ≤ address && best.all (· ≤ symbol.addr) then some symbol.addr else best

/-- Whether `address` lies in `symbol`: within its size if known, else before the next function. -/
private def spans (symbol : Image.Symbol) (nearest : Option Nat) (address : Nat) : Bool :=
  symbol.addr ≤ address &&
    if symbol.size = 0 then nearest = some symbol.addr else address < symbol.addr + symbol.size

def functionOf (index : Index) (address : Nat) : Option Image.Symbol :=
  let nearest := nearestStart index address
  index.functions.foldl (init := none) fun best symbol =>
    if spans symbol nearest address && best.all (·.addr ≤ symbol.addr) then some symbol else best

namespace FunctionTable

/-- The number of the sorted functions at or below `address`, from the range where it can be. -/
def countUpTo (table : FunctionTable) (address : Nat) : Nat → Nat → Nat → Nat
  | 0, low, _ => low
  | fuel + 1, low, high =>
    if low < high then
      let middle := (low + high) / 2
      match table.symbols[middle]? with
      | some symbol =>
        if symbol.addr ≤ address then countUpTo table address fuel (middle + 1) high
        else countUpTo table address fuel low middle
      | none => low
    else low

/-- The last of the first `count` functions that spans `address`. Below a function that isn't at `nearest` and all before
which end at or before `address`, none can. -/
def lastSpanning (table : FunctionTable) (nearest : Option Nat) (address : Nat) : Nat → Option Image.Symbol
  | 0 => none
  | count + 1 =>
    match table.symbols[count]? with
    | none => none
    | some symbol =>
      if spans symbol nearest address then some symbol
      else if nearest != some symbol.addr && (table.reach[count]?.getD 0) ≤ address then none
      else lastSpanning table nearest address count

/-- The start of the last of the first `count` functions. -/
def startBefore (table : FunctionTable) : Nat → Option Nat
  | 0 => none
  | count + 1 => table.symbols[count]?.map (·.addr)

end FunctionTable

/-! `functionOf` and `nearestStart` by binary search, in the table of the index. -/

private def pickStep (sp : Image.Symbol → Bool) (best : Option Image.Symbol) (symbol : Image.Symbol) : Option Image.Symbol :=
  if sp symbol && best.all (·.addr ≤ symbol.addr) then some symbol else best

private theorem pick_filter (sp : Image.Symbol → Bool) (l : List Image.Symbol) (init : Option Image.Symbol) :
    l.foldl (pickStep sp) init = (l.filter sp).foldl (pickStep sp) init := by
  induction l generalizing init with
  | nil => rfl
  | cons head tail ih =>
    cases hs : sp head with
    | true => simp only [List.foldl_cons, List.filter_cons, hs, ↓reduceIte, ih]
    | false =>
      have : pickStep sp init head = init := by simp [pickStep, hs]
      simp only [List.foldl_cons, List.filter_cons, hs, Bool.false_eq_true, ↓reduceIte, this, ih]

/-- What the fold on a list that all spans comes to: a last one of the highest address. -/
private theorem pick_top (sp : Image.Symbol → Bool) (l : List Image.Symbol) (hall : ∀ x ∈ l, sp x = true) (hne : l ≠ []) :
    ∃ r, l.foldl (pickStep sp) none = some r ∧ r ∈ l ∧ (∀ x ∈ l, x.addr ≤ r.addr) ∧
      (l.filter (·.addr == r.addr)).getLast? = some r := by
  have key : ∀ m : List Image.Symbol, (∀ x ∈ m.reverse, sp x = true) → m ≠ [] →
      ∃ r, m.reverse.foldl (pickStep sp) none = some r ∧ r ∈ m.reverse ∧ (∀ x ∈ m.reverse, x.addr ≤ r.addr) ∧
        (m.reverse.filter (·.addr == r.addr)).getLast? = some r := by
    intro m
    induction m with
    | nil => exact fun _ hne => absurd rfl hne
    | cons x m ih =>
      intro hall _
      rw [List.reverse_cons] at hall ⊢
      have hx : sp x = true := hall x (by simp)
      by_cases hl : m = []
      · subst hl
        exact ⟨x, by simp [pickStep, hx], by simp, by simp, by simp⟩
      · obtain ⟨r, h1, h2, h3, h4⟩ := ih (fun y hy => hall y (List.mem_append_left _ hy)) hl
        rw [List.foldl_append, h1]
        by_cases hle : r.addr ≤ x.addr
        · have hstep : pickStep sp (some r) x = some x := by simp [pickStep, hx, hle]
          refine ⟨x, by simp [hstep], by simp, ?_, ?_⟩
          · intro y hy
            rcases List.mem_append.1 hy with hy | hy
            · exact Nat.le_trans (h3 y hy) hle
            · simp only [List.mem_singleton] at hy
              subst hy
              exact Nat.le_refl _
          · simp [List.filter_append]
        · have hstep : pickStep sp (some r) x = some r := by simp [pickStep, hle]
          refine ⟨r, by simp [hstep], List.mem_append_left _ h2, ?_, ?_⟩
          · intro y hy
            rcases List.mem_append.1 hy with hy | hy
            · exact h3 y hy
            · simp only [List.mem_singleton] at hy
              subst hy
              omega
          · have hne' : (x.addr == r.addr) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]
              omega
            simpa [List.filter_append, hne'] using h4
  have := key l.reverse (by simpa using hall) (by simpa using hne)
  simpa using this

private theorem addrLe_trans (a b c : Image.Symbol) (h1 : addrLe a b = true) (h2 : addrLe b c = true) : addrLe a c = true := by
  simp only [addrLe, decide_eq_true_eq] at *
  omega

private theorem addrLe_total (a b : Image.Symbol) : (addrLe a b || addrLe b a) = true := by
  simp only [addrLe, Bool.or_eq_true, decide_eq_true_eq]
  omega

private theorem sorted_pairwise (functions : List Image.Symbol) :
    (functions.mergeSort addrLe).Pairwise fun a b => a.addr ≤ b.addr := by
  have := List.pairwise_mergeSort (le := addrLe) addrLe_trans addrLe_total functions
  simpa [addrLe] using this

/-- The fold on the functions finds the last that spans in their stable sort. -/
private theorem pick_eq_sorted (sp : Image.Symbol → Bool) (l : List Image.Symbol) :
    l.foldl (pickStep sp) none = ((l.mergeSort addrLe).filter sp).getLast? := by
  have hperm : (l.mergeSort addrLe).filter sp |>.Perm (l.filter sp) := (List.mergeSort_perm l addrLe).filter sp
  rw [pick_filter]
  cases hf : l.filter sp with
  | nil =>
    rw [hf] at hperm
    rw [hperm.eq_nil]
    rfl
  | cons head tail =>
    have hne : l.filter sp ≠ [] := by simp [hf]
    obtain ⟨r, h1, h2, h3, h4⟩ := pick_top sp (l.filter sp) (fun x hx => (List.mem_filter.1 hx).2) hne
    rw [← hf, h1]
    -- the last of the sorted ones
    have hne' : (l.mergeSort addrLe).filter sp ≠ [] := fun h => hne (by simpa [h] using hperm.symm)
    obtain ⟨pre, last, heq⟩ : ∃ pre last, (l.mergeSort addrLe).filter sp = pre ++ [last] :=
      ⟨_, _, (List.dropLast_concat_getLast hne').symm⟩
    have hpair : ((l.mergeSort addrLe).filter sp).Pairwise fun a b => a.addr ≤ b.addr :=
      (sorted_pairwise l).filter sp
    rw [heq] at hpair
    have hlast : ∀ x ∈ pre, x.addr ≤ last.addr := fun x hx =>
      (List.pairwise_append.1 hpair).2.2 x hx last (by simp)
    have hlastmem : last ∈ l.filter sp := hperm.subset (by rw [heq]; simp)
    have hrmem : r ∈ pre ++ [last] := by
      rw [← heq]
      exact hperm.symm.subset h2
    have haddr : r.addr = last.addr := by
      have h1 := h3 last hlastmem
      have h2 : r.addr ≤ last.addr := by
        rcases List.mem_append.1 hrmem with h | h
        · exact hlast r h
        · simp only [List.mem_singleton] at h
          rw [h]
          exact Nat.le_refl _
      omega
    -- the block of the highest address is the same in both
    let Q : Image.Symbol → Bool := fun x => sp x && x.addr == r.addr
    have hX : (l.filter sp).filter (·.addr == r.addr) = l.filter Q := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro x _
      simp only [Q, Bool.and_comm]
    have hY : ((l.mergeSort addrLe).filter sp).filter (·.addr == r.addr) = (l.mergeSort addrLe).filter Q := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro x _
      simp only [Q, Bool.and_comm]
    have hblockPair : (l.filter Q).Pairwise fun a b => addrLe a b = true := by
      have all : ∀ (m : List Image.Symbol), (∀ x ∈ m, x.addr = r.addr) → m.Pairwise fun a b => addrLe a b = true := by
        intro m
        induction m with
        | nil => exact fun _ => .nil
        | cons head tail ih =>
          intro hm
          refine .cons (fun b hb => ?_) (ih fun x hx => hm x (List.mem_cons_of_mem _ hx))
          have h1 := hm head List.mem_cons_self
          have h2 := hm b (List.mem_cons_of_mem _ hb)
          simp only [addrLe, decide_eq_true_eq]
          omega
      refine all _ fun x hx => ?_
      have := (List.mem_filter.1 hx).2
      simp only [Q, Bool.and_eq_true, beq_iff_eq] at this
      exact this.2
    have hsub : List.Sublist (l.filter Q) ((l.mergeSort addrLe).filter Q) := by
      have := List.sublist_mergeSort (le := addrLe) (xs := l) addrLe_trans addrLe_total hblockPair (List.filter_sublist)
      have h2 := this.filter Q
      rwa [List.filter_filter, show (fun x => Q x && Q x) = Q by funext x; simp] at h2
    have hsame : l.filter Q = (l.mergeSort addrLe).filter Q :=
      hsub.eq_of_length (((List.mergeSort_perm l addrLe).filter Q).length_eq.symm)
    have hend : (((l.mergeSort addrLe).filter sp).filter (·.addr == r.addr)).getLast? = some last := by
      rw [heq, List.filter_append]
      simp [haddr]
    rw [hX, hsame, ← hY, hend] at h4
    rw [heq]
    simpa using h4.symm

/-- Reaching on the list. -/
private def reachFrom : Nat → List Image.Symbol → List Nat
  | _, [] => []
  | most, symbol :: rest => max most (sizedEnd symbol) :: reachFrom (max most (sizedEnd symbol)) rest

private theorem reach_toList (rest : List Image.Symbol) (most : Nat) (reach : Array Nat) :
    (rest.foldl (init := (most, reach)) fun state symbol =>
      let most := max state.1 (sizedEnd symbol)
      (most, state.2.push most)).2.toList = reach.toList ++ reachFrom most rest := by
  induction rest generalizing most reach with
  | nil => simp [reachFrom]
  | cons head tail ih =>
    simp only [List.foldl_cons, reachFrom]
    rw [ih]
    simp

private theorem reachFrom_length (rest : List Image.Symbol) (most : Nat) : (reachFrom most rest).length = rest.length := by
  induction rest generalizing most with
  | nil => rfl
  | cons head tail ih => simp [reachFrom, ih]

private theorem reachFrom_ge_most (rest : List Image.Symbol) (most i r : Nat) (h : (reachFrom most rest)[i]? = some r) :
    most ≤ r := by
  induction rest generalizing most i with
  | nil => simp [reachFrom] at h
  | cons head tail ih =>
    cases i with
    | zero =>
      simp only [reachFrom, List.getElem?_cons_zero, Option.some.injEq] at h
      omega
    | succ i =>
      have := ih _ i (by simpa [reachFrom] using h)
      omega

private theorem reachFrom_ge (rest : List Image.Symbol) (most i j r : Nat) (symbol : Image.Symbol) (hji : j ≤ i)
    (hj : rest[j]? = some symbol) (hr : (reachFrom most rest)[i]? = some r) : sizedEnd symbol ≤ r := by
  induction rest generalizing most i j with
  | nil => simp at hj
  | cons head tail ih =>
    cases j with
    | zero =>
      have he : head = symbol := by simpa using hj
      subst he
      have := reachFrom_ge_most (head :: tail) most i r hr
      cases i with
      | zero =>
        simp only [reachFrom, List.getElem?_cons_zero, Option.some.injEq] at hr
        omega
      | succ i =>
        have := reachFrom_ge_most tail _ i r (by simpa [reachFrom] using hr)
        omega
    | succ j =>
      cases i with
      | zero => omega
      | succ i => exact ih _ i j (by omega) (by simpa using hj) (by simpa [reachFrom] using hr)

private theorem symbols_get (functions : List Image.Symbol) (i : Nat) :
    (FunctionTable.ofList functions).symbols[i]? = (functions.mergeSort addrLe)[i]? := by
  simp [FunctionTable.ofList]

private theorem reach_get (functions : List Image.Symbol) (i : Nat) :
    (FunctionTable.ofList functions).reach[i]? = (reachFrom 0 (functions.mergeSort addrLe))[i]? := by
  have h := reach_toList (functions.mergeSort addrLe) 0 #[]
  simp only [List.nil_append] at h
  have : (FunctionTable.ofList functions).reach = (reachFrom 0 (functions.mergeSort addrLe)).toArray := by
    apply Array.ext'
    simpa [FunctionTable.ofList] using h
  rw [this]
  simp

/-- What binary search finds. -/
private theorem countUpTo_spec (functions : List Image.Symbol) (address : Nat) (fuel low high : Nat)
    (hs : high ≤ (functions.mergeSort addrLe).length) (hf : high - low ≤ fuel)
    (hlow : ∀ j, j < low → ∀ x, (functions.mergeSort addrLe)[j]? = some x → x.addr ≤ address)
    (hhigh : ∀ j, high ≤ j → ∀ x, (functions.mergeSort addrLe)[j]? = some x → address < x.addr)
    (hle : low ≤ high) :
    let n := FunctionTable.countUpTo (FunctionTable.ofList functions) address fuel low high
    n ≤ (functions.mergeSort addrLe).length ∧
      (∀ j, j < n → ∀ x, (functions.mergeSort addrLe)[j]? = some x → x.addr ≤ address) ∧
      ∀ j, n ≤ j → ∀ x, (functions.mergeSort addrLe)[j]? = some x → address < x.addr := by
  induction fuel generalizing low high with
  | zero =>
    have : low = high := by omega
    subst this
    exact ⟨hs, hlow, hhigh⟩
  | succ fuel ih =>
    simp only [FunctionTable.countUpTo]
    split
    · rename_i hlt
      have hmid : (low + high) / 2 < (functions.mergeSort addrLe).length := by omega
      rw [symbols_get, List.getElem?_eq_getElem hmid]
      simp only
      have hsym := List.getElem?_eq_getElem hmid
      generalize hx : (functions.mergeSort addrLe)[(low + high) / 2] = sym at *
      have hpair := sorted_pairwise functions
      have sorted : ∀ (i j : Nat) (x y : Image.Symbol), i ≤ j → (functions.mergeSort addrLe)[i]? = some x →
          (functions.mergeSort addrLe)[j]? = some y → x.addr ≤ y.addr := by
        intro i j x y hij hi hj
        rcases Nat.lt_or_eq_of_le hij with h | h
        · obtain ⟨hi1, hi2⟩ := List.getElem?_eq_some_iff.1 hi
          obtain ⟨hj1, hj2⟩ := List.getElem?_eq_some_iff.1 hj
          have := List.pairwise_iff_getElem.1 hpair i j hi1 hj1 h
          simpa [hi2, hj2] using this
        · subst h
          rw [hi] at hj
          cases hj
          exact Nat.le_refl _
      split
      · rename_i haddr
        refine ih ((low + high) / 2 + 1) high hs (by omega) ?_ hhigh (by omega)
        intro j hj x hx'
        exact Nat.le_trans (sorted j _ x sym (by omega) hx' hsym) haddr
      · rename_i haddr
        refine ih low ((low + high) / 2) (by omega) (by omega) hlow ?_ (by omega)
        intro j hj x hx'
        have := sorted _ j sym x hj hsym hx'
        omega
    · rename_i hnlt
      have : low = high := by omega
      subst this
      exact ⟨hs, hlow, hhigh⟩

/-- What the walk down from the `count`th function finds. -/
private theorem lastSpanning_eq (functions : List Image.Symbol) (nearest : Option Nat) (address count : Nat)
    (hc : count ≤ (functions.mergeSort addrLe).length)
    (hup : ∀ j, j < count → ∀ x, (functions.mergeSort addrLe)[j]? = some x → x.addr ≤ address)
    (hnear : ∀ x ∈ functions.mergeSort addrLe, x.addr ≤ address → ∃ m, nearest = some m ∧ x.addr ≤ m) :
    FunctionTable.lastSpanning (FunctionTable.ofList functions) nearest address count =
      (((functions.mergeSort addrLe).take count).filter fun symbol => spans symbol nearest address).getLast? := by
  induction count with
  | zero => simp [FunctionTable.lastSpanning]
  | succ count ih =>
    have hlt : count < (functions.mergeSort addrLe).length := by omega
    have htake : (functions.mergeSort addrLe).take (count + 1) =
        (functions.mergeSort addrLe).take count ++ [(functions.mergeSort addrLe)[count]] :=
      List.take_succ_eq_append_getElem hlt
    have hget := List.getElem?_eq_getElem hlt
    rw [FunctionTable.lastSpanning, symbols_get, hget, htake]
    generalize hs : (functions.mergeSort addrLe)[count] = symbol at *
    simp only [List.filter_append, List.filter_cons, List.filter_nil]
    have ih' := ih (by omega) (fun j hj x hx => hup j (by omega) x hx)
    split
    · simp_all
    · rename_i hsp
      simp only [List.append_nil]
      split
      · rename_i hstop
        have ⟨hnearN, hreach⟩ : nearest ≠ some symbol.addr ∧ (FunctionTable.ofList functions).reach[count]?.getD 0 ≤ address := by
          simpa using hstop
        have hnone : ((functions.mergeSort addrLe).take count).filter (fun symbol => spans symbol nearest address) = [] := by
          rw [List.filter_eq_nil_iff]
          intro y hy
          obtain ⟨j, hj, hjy⟩ := List.mem_take_iff_getElem.1 hy
          have hjlt : j < count := by omega
          have hjlen : j < (functions.mergeSort addrLe).length := by omega
          have hjget : (functions.mergeSort addrLe)[j]? = some y := by
            rw [List.getElem?_eq_getElem hjlen, hjy]
          have hup' := hup count (by omega) symbol hget
          obtain ⟨m, hm1, hm2⟩ := hnear symbol (hs ▸ List.getElem_mem hlt) hup'
          have hsorted : y.addr ≤ symbol.addr := by
            have := List.pairwise_iff_getElem.1 (sorted_pairwise functions) j count hjlen hlt hjlt
            simpa [hjy, hs] using this
          have hreach' : ∃ r, (reachFrom 0 (functions.mergeSort addrLe))[count]? = some r ∧ r ≤ address := by
            have hlen : count < (reachFrom 0 (functions.mergeSort addrLe)).length := by
              rw [reachFrom_length]
              exact hlt
            refine ⟨_, List.getElem?_eq_getElem hlen, ?_⟩
            rw [reach_get, List.getElem?_eq_getElem hlen] at hreach
            simpa using hreach
          obtain ⟨r, hr1, hr2⟩ := hreach'
          have hend := reachFrom_ge _ 0 count j r y (by omega) hjget hr1
          intro hspan
          simp only [spans, Bool.and_eq_true, decide_eq_true_eq] at hspan
          obtain ⟨_, hspan⟩ := hspan
          by_cases hzero : y.size = 0
          · simp only [hzero, ↓reduceIte, decide_eq_true_eq] at hspan
            rw [hspan] at hm1
            have hmy : y.addr = m := by simpa using hm1
            have heq : symbol.addr = y.addr := by omega
            exact hnearN (by rw [hspan, heq])
          · simp only [hzero, ↓reduceIte, decide_eq_true_eq] at hspan
            simp only [sizedEnd, hzero, ↓reduceIte] at hend
            omega
        rw [hnone]
        rfl
      · exact ih'

/-- What binary search finds in the whole table. -/
private theorem count_spec (functions : List Image.Symbol) (address : Nat) :
    let n := FunctionTable.countUpTo (FunctionTable.ofList functions) address (FunctionTable.ofList functions).symbols.size 0
      (FunctionTable.ofList functions).symbols.size
    n ≤ (functions.mergeSort addrLe).length ∧
      (∀ j, j < n → ∀ x, (functions.mergeSort addrLe)[j]? = some x → x.addr ≤ address) ∧
      ∀ j, n ≤ j → ∀ x, (functions.mergeSort addrLe)[j]? = some x → address < x.addr := by
  have hsize : (FunctionTable.ofList functions).symbols.size = (functions.mergeSort addrLe).length := by
    simp [FunctionTable.ofList]
  intro n
  refine countUpTo_spec functions address _ 0 _ (Nat.le_of_eq hsize) (by omega) (by simp) ?_ (by omega)
  intro j hj x hx
  have : (functions.mergeSort addrLe).length ≤ j := by omega
  simp [List.getElem?_eq_none this] at hx

private theorem nearStep_map (address : Nat) (l : List Image.Symbol) (init : Option Image.Symbol) :
    (l.foldl (pickStep fun symbol => decide (symbol.addr ≤ address)) init).map (·.addr) =
      l.foldl (fun (best : Option Nat) symbol =>
        if symbol.addr ≤ address && best.all (· ≤ symbol.addr) then some symbol.addr else best) (init.map (·.addr)) := by
  induction l generalizing init with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    cases init with
    | none => simp only [pickStep, Option.all_none, Option.map_none]; split <;> simp_all
    | some best => simp only [pickStep, Option.all_some, Option.map_some]; split <;> simp_all

/-- The sorted functions up to an address are the first `count`. -/
private theorem filter_up_to (functions : List Image.Symbol) (address count : Nat) (sp : Image.Symbol → Bool)
    (hsp : ∀ x, sp x = true → x.addr ≤ address)
    (hhigh : ∀ j, count ≤ j → ∀ x, (functions.mergeSort addrLe)[j]? = some x → address < x.addr) :
    (functions.mergeSort addrLe).filter sp = ((functions.mergeSort addrLe).take count).filter sp := by
  conv => lhs; rw [← List.take_append_drop count (functions.mergeSort addrLe)]
  rw [List.filter_append]
  have : ((functions.mergeSort addrLe).drop count).filter sp = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx hspx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
    rw [List.getElem?_drop] at hi
    have := hhigh (count + i) (by omega) x hi
    have := hsp x hspx
    omega
  rw [this, List.append_nil]

private theorem nearestStart_table (index : Index) (address : Nat) :
    nearestStart index address = (FunctionTable.ofList index.functions).startBefore
      (FunctionTable.countUpTo (FunctionTable.ofList index.functions) address (FunctionTable.ofList index.functions).symbols.size 0
        (FunctionTable.ofList index.functions).symbols.size) := by
  obtain ⟨hn, hlow, hhigh⟩ := count_spec index.functions address
  have hmap := nearStep_map address index.functions none
  rw [pick_eq_sorted, filter_up_to index.functions address _ _ (by simp) hhigh,
    List.filter_eq_self.2 (fun x hx => ?_)] at hmap
  · simp only [nearestStart]
    rw [Option.map_none] at hmap
    rw [← hmap]
    revert hn
    generalize FunctionTable.countUpTo (FunctionTable.ofList index.functions) address (FunctionTable.ofList index.functions).symbols.size 0
      (FunctionTable.ofList index.functions).symbols.size = n
    intro hn
    cases n with
    | zero => simp [FunctionTable.startBefore]
    | succ m =>
      have hlt : m < (index.functions.mergeSort addrLe).length := by omega
      rw [FunctionTable.startBefore, symbols_get, List.take_succ_eq_append_getElem hlt, List.getElem?_eq_getElem hlt]
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.map_some]
  · obtain ⟨j, hj, hjx⟩ := List.mem_take_iff_getElem.1 hx
    have hjlen : j < (index.functions.mergeSort addrLe).length := by omega
    have := hlow j (by omega) x (by rw [List.getElem?_eq_getElem hjlen, hjx])
    simpa using this

private theorem functionOf_table (index : Index) (address : Nat) :
    functionOf index address =
      let count := FunctionTable.countUpTo (FunctionTable.ofList index.functions) address (FunctionTable.ofList index.functions).symbols.size 0
        (FunctionTable.ofList index.functions).symbols.size
      FunctionTable.lastSpanning (FunctionTable.ofList index.functions)
        ((FunctionTable.ofList index.functions).startBefore count) address count := by
  obtain ⟨hn, hlow, hhigh⟩ := count_spec index.functions address
  have hnear := nearestStart_table index address
  simp only [functionOf]
  rw [hnear]
  generalize FunctionTable.countUpTo (FunctionTable.ofList index.functions) address (FunctionTable.ofList index.functions).symbols.size 0
    (FunctionTable.ofList index.functions).symbols.size = count at hn hlow hhigh ⊢
  generalize hnearest : (FunctionTable.ofList index.functions).startBefore count = nearest
  have hpick := pick_eq_sorted (fun symbol => spans symbol nearest address) index.functions
  have hsp : ∀ x, (fun symbol => spans symbol nearest address) x = true → x.addr ≤ address := by
    intro x hx
    simp only [spans, Bool.and_eq_true, decide_eq_true_eq] at hx
    exact hx.1
  rw [filter_up_to index.functions address count _ hsp hhigh] at hpick
  rw [lastSpanning_eq index.functions nearest address count hn hlow ?_]
  · exact hpick
  · intro x hx hle
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
    have hjn : j < count := by
      refine Nat.lt_of_not_le fun hge => ?_
      have := hhigh j hge x hj
      omega
    cases hcount : count with
    | zero => omega
    | succ m =>
      have hlt : m < (index.functions.mergeSort addrLe).length := by omega
      rw [hcount, FunctionTable.startBefore, symbols_get, List.getElem?_eq_getElem hlt] at hnearest
      refine ⟨_, hnearest.symm, ?_⟩
      have hjlt : j < (index.functions.mergeSort addrLe).length := by omega
      have hxj : (index.functions.mergeSort addrLe)[j] = x := by
        have := List.getElem?_eq_getElem hjlt
        rw [hj] at this
        exact (Option.some.inj this).symm
      rcases Nat.lt_or_eq_of_le (show j ≤ m by omega) with h | h
      · have := List.pairwise_iff_getElem.1 (sorted_pairwise index.functions) j m hjlt hlt h
        simpa [hxj] using this
      · subst h
        rw [hxj]
        exact Nat.le_refl _

private def functionOfFast (index : Index) (address : Nat) : Option Image.Symbol :=
  let table := index.table.get
  let count := table.countUpTo address table.symbols.size 0 table.symbols.size
  table.lastSpanning (table.startBefore count) address count

private def nearestStartFast (index : Index) (address : Nat) : Option Nat :=
  let table := index.table.get
  table.startBefore (table.countUpTo address table.symbols.size 0 table.symbols.size)

@[csimp] private theorem functionOf_eq_fast : @functionOf = @functionOfFast := by
  funext index address
  rw [functionOf_table]
  simp only [functionOfFast, index.table_eq]

@[csimp] private theorem nearestStart_eq_fast : @nearestStart = @nearestStartFast := by
  funext index address
  rw [nearestStart_table]
  simp only [nearestStartFast, index.table_eq]

/-- Whether `symbol` owns `address`. Aliases of a function own the same instructions. -/
def owns (index : Index) (symbol : Image.Symbol) (address : Nat) : Bool :=
  spans symbol (nearestStart index address) address &&
    (functionOf index address).any (·.addr == symbol.addr)

def functions (index : Index) : List String := index.functions.map Image.Symbol.name

def references (index : Index) (kind : Kind) (target : Nat) : List Xref :=
  index.xrefs.filter fun xref => xref.kind = kind && xref.target = target

def callers (index : Index) (target : Nat) : List Xref := references index .call target

def callees (index : Index) (function : String) : List Xref :=
  index.xrefs.filter fun xref =>
    xref.kind = .call && index.functions.any fun symbol =>
      symbol.name = function && owns index symbol xref.source

end Bap.Analysis.Xrefs
