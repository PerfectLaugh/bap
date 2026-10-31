import Lean.Elab.Tactic.Basic
import Bap.Disasm.Linear
import Bap.Disasm.Recursive
import Std.Data.HashSet.Lemmas

namespace Bap.Proofs.Disasm

open Bap.Disasm

open Lean Elab Term in
/-- Names a private constant of another module: `priv% Module Full.Name`. -/
local elab "priv% " mod:ident n:ident : term => do
  return mkConst (mkPrivateNameCore mod.getId n.getId)

open Lean Elab Tactic in
/-- Rewrites with the unfolding equation of a private definition of another module. -/
local elab "prw " mod:ident n:ident : tactic => do
  evalTactic (← `(tactic| rw [$(mkIdent (mkPrivateNameCore mod.getId (n.getId ++ `eq_def))):ident]))

private abbrev fastSweepAux : Disassembler → ByteArray → Nat → Nat → Nat → Array Insn → Array String →
    IO (Array Insn × Array String) :=
  priv% Bap.Disasm.Linear Bap.Disasm.Linear.sweepAux
private abbrev fastDecodeSlot : Disassembler → ByteArray → Nat → Recursive.ScanState → IO Recursive.ScanState :=
  priv% Bap.Disasm.Recursive Bap.Disasm.Recursive.decodeSlot
private abbrev fastScanAux : Disassembler → ByteArray → Nat → List Nat → Recursive.ScanState →
    IO Recursive.ScanState :=
  priv% Bap.Disasm.Recursive Bap.Disasm.Recursive.scanAux
private abbrev fastSweepRange : Disassembler → ByteArray → Nat → Nat → Nat → Nat → Nat → Recursive.Walk → Recursive.ScanState →
    IO (Recursive.Walk × Recursive.ScanState) :=
  priv% Bap.Disasm.Recursive Bap.Disasm.Recursive.sweepRange
private abbrev fastBuild : Std.HashSet Nat → List Insn → List Block → List Insn → List Block :=
  priv% Bap.Disasm.Basic Bap.Disasm.buildBlocks

/-- A step of the insertion sort, which sorts as `sortedInstructions` does. -/
def insertInsn (insn : Insn) : List Insn → List Insn
  | [] => [insn]
  | head :: tail =>
    if insn.address ≤ head.address then insn :: head :: tail else head :: insertInsn insn tail

/-! ## The disassemblers as specifications on lists

The disassemblers keep what they find in arrays and sets. What they compute is what these definitions on lists do, which
the theorems of this file are about, by `sweep_eq`, `scan_eq` and `blocks_eq`. -/

def sweepAux (disassembler : Disassembler) (data : ByteArray) (entry : Nat) :
    Nat → Nat → List Insn → List String → IO (List Insn × List String)
  | 0, _, instructions, errors => pure (instructions, errors)
  | fuel + 1, offset, instructions, errors =>
    if offset ≥ data.size then
      pure (instructions, errors)
    else do
      match ← disassembler.decode (entry + offset) data with
      | .error error => pure (instructions, errors ++ [error])
      | .ok insn =>
        if insn.size = 0 then
          pure (instructions, errors ++ ["decoder produced a zero-sized instruction"])
        else
          sweepAux disassembler data entry fuel (offset + insn.size) (instructions ++ [insn]) errors

def decodeSlot (disassembler : Disassembler) (data : ByteArray) (slot : Nat)
    (instructions : List Insn) (errors : List String) : IO (List Insn × List String) := do
  match ← disassembler.decode slot data with
  | .error error => pure (instructions, errors ++ [error])
  | .ok insn =>
    if insn.address != slot || insn.size = 0 then
      pure (instructions, errors ++ ["decoder returned an inconsistent instruction"])
    else
      pure (Recursive.addInsn insn instructions, errors)

def scanAux (disassembler : Disassembler) (data : ByteArray) :
    Nat → List Nat → List Nat → List Insn → List (Nat × Nat) → List String →
      IO (List Insn × List (Nat × Nat) × List String)
  | 0, work, visited, instructions, edges, errors =>
    if work.all (· ∈ visited) then
      pure (instructions, edges, errors)
    else
      pure (instructions, edges, errors ++ [Recursive.outOfFuel])
  | fuel + 1, work, visited, instructions, edges, errors =>
    match work.dropWhile (· ∈ visited) with
    | [] => pure (instructions, edges, errors)
    | address :: work => do
      match ← disassembler.decode address data with
      | .error error =>
        scanAux disassembler data fuel work (address :: visited) instructions edges (errors ++ [error])
      | .ok insn =>
        if insn.address != address || insn.size = 0 then
          scanAux disassembler data fuel work (address :: visited) instructions edges
            (errors ++ ["decoder returned an inconsistent instruction"])
        else
          let instructions := Recursive.addInsn insn instructions
          let edges := edges ++ Recursive.flowEdges disassembler insn
          let work := Recursive.nextAddresses disassembler insn ++ work
          if disassembler.hasDelaySlot insn then
            let (instructions, errors) ← decodeSlot disassembler data insn.next instructions errors
            scanAux disassembler data fuel work (address :: visited) instructions edges errors
          else
            scanAux disassembler data fuel work (address :: visited) instructions edges errors

theorem io_pure_bind {α β} (a : α) (f : α → IO β) : (pure a >>= f : IO β) = f a := rfl

theorem io_bind_assoc {α β γ} (m : IO α) (f : α → IO β) (g : β → IO γ) :
    (m >>= f) >>= g = m >>= fun x => f x >>= g := by
  funext s
  show EST.bind (EST.bind m f) g s = EST.bind m (fun x => EST.bind (f x) g) s
  simp only [EST.bind]
  cases m s <;> rfl

private theorem fast_sweep (d : Disassembler) (data : ByteArray) (entry : Nat) (fuel offset : Nat)
    (instructions : Array Insn) (errors : Array String) :
    fastSweepAux d data entry fuel offset instructions errors >>= (fun out => pure (out.1.toList, out.2.toList)) =
      sweepAux d data entry fuel offset instructions.toList errors.toList := by
  induction fuel generalizing offset instructions errors with
  | zero => rfl
  | succ fuel ih =>
    dsimp only [fastSweepAux] at ih ⊢
    prw Bap.Disasm.Linear Bap.Disasm.Linear.sweepAux
    simp only [sweepAux]
    split
    · simp only [io_pure_bind]
    · simp only [io_bind_assoc]
      refine congrArg _ (funext fun r => ?_)
      cases r with
      | error e => simp only [io_pure_bind, Array.toList_push]
      | ok insn =>
        simp only
        split
        · simp only [io_pure_bind, Array.toList_push]
        · rw [ih, Array.toList_push]

/-- The linear sweep computes what its specification on lists does. -/
theorem sweep_eq (d : Disassembler) (data : ByteArray) (entry : Nat) :
    Linear.sweep d data entry = (sweepAux d data entry (data.size + 1) 0 [] [] >>= fun out =>
      pure { entry := entry, instructions := out.1, errors := out.2 }) := by
  have := fast_sweep d data entry (data.size + 1) 0 #[] #[]
  rw [show sweepAux d data entry (data.size + 1) 0 [] [] = _ from this.symm, io_bind_assoc]
  rfl

/-- The state of the fast scan represents these lists. -/
structure Represents (state : Recursive.ScanState) (visited : List Nat) (instructions : List Insn)
    (edges : List (Nat × Nat)) (errors : List String) : Prop where
  visited_iff : ∀ a, state.visited.contains a = decide (a ∈ visited)
  addresses_iff : ∀ a, state.addresses.contains a = instructions.any (·.address == a)
  instructions : state.instructions.toList = instructions
  edges : state.edges.toList = edges
  errors : state.errors.toList = errors

private theorem Represents.add {s v is es errs} (h : Represents s v is es errs) (insn : Insn) :
    Represents (s.add insn) v (Recursive.addInsn insn is) es errs := by
  unfold Recursive.ScanState.add Recursive.addInsn
  by_cases hc : s.addresses.contains insn.address = true
  · have hany := hc
    rw [h.addresses_iff] at hany
    simp only [hc, hany, ite_true]
    exact h
  · have hany : ¬ is.any (·.address == insn.address) = true := by
      rw [← h.addresses_iff]; exact hc
    simp only [hc, hany, Bool.false_eq_true, ite_false]
    refine ⟨h.visited_iff, ?_, ?_, h.edges, h.errors⟩
    · intro a
      simp only [Std.HashSet.contains_insert, h.addresses_iff, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
      rw [Bool.or_comm]
    · simp [h.instructions]

private theorem Represents.visit {s v is es errs} (h : Represents s v is es errs) (a : Nat) :
    Represents (s.visit a) (a :: v) is es errs := by
  refine ⟨?_, h.addresses_iff, h.instructions, h.edges, h.errors⟩
  intro x
  simp only [Recursive.ScanState.visit, Std.HashSet.contains_insert, h.visited_iff, List.mem_cons]
  by_cases hx : x = a
  · simp [hx]
  · have : ¬ a = x := fun e => hx e.symm
    simp [hx, this]

private theorem Represents.error {s v is es errs} (h : Represents s v is es errs) (m : String) :
    Represents (s.error m) v is es (errs ++ [m]) :=
  ⟨h.visited_iff, h.addresses_iff, h.instructions, h.edges, by simp [Recursive.ScanState.error, h.errors]⟩

private def project (s : Recursive.ScanState) : List Insn × List (Nat × Nat) × List String :=
  (s.instructions.toList, s.edges.toList, s.errors.toList)

private theorem fast_slot (d : Disassembler) (data : ByteArray) (slot : Nat) (s v is es errs)
    (h : Represents s v is es errs) {γ} (kf : Recursive.ScanState → IO γ)
    (ks : List Insn × List String → IO γ)
    (hk : ∀ s' is' errs', Represents s' v is' es errs' → kf s' = ks (is', errs')) :
    fastDecodeSlot d data slot s >>= kf = decodeSlot d data slot is errs >>= ks := by
  dsimp only [fastDecodeSlot]
  prw Bap.Disasm.Recursive Bap.Disasm.Recursive.decodeSlot
  simp only [decodeSlot, io_bind_assoc]
  refine congrArg _ (funext fun r => ?_)
  cases r with
  | error e => simpa only [io_pure_bind] using hk _ _ _ (h.error e)
  | ok insn =>
    simp only
    split
    · simpa only [io_pure_bind] using hk _ _ _ (h.error _)
    · simpa only [io_pure_bind] using hk _ _ _ (h.add insn)

private theorem fast_scan (d : Disassembler) (data : ByteArray) (fuel : Nat) (work : List Nat)
    (s v is es errs) (h : Represents s v is es errs) :
    fastScanAux d data fuel work s >>= (fun out => pure (project out)) = scanAux d data fuel work v is es errs := by
  have hpred (s : Recursive.ScanState) (v) (is es errs) (h : Represents s v is es errs) :
      (fun x => s.visited.contains x) = fun x => decide (x ∈ v) := funext h.visited_iff
  induction fuel generalizing work s v is es errs with
  | zero =>
    dsimp only [fastScanAux]
    prw Bap.Disasm.Recursive Bap.Disasm.Recursive.scanAux
    simp only [scanAux]
    have hall : (work.all fun x => s.visited.contains x) = work.all fun x => decide (x ∈ v) := by
      rw [hpred s v is es errs h]
    rw [hall]
    split
    · simp only [io_pure_bind, project, h.instructions, h.edges, h.errors]
    · simp only [io_pure_bind, project, Recursive.ScanState.error, Array.toList_push, h.instructions, h.edges, h.errors]
  | succ fuel ih =>
    dsimp only [fastScanAux] at ih ⊢
    prw Bap.Disasm.Recursive Bap.Disasm.Recursive.scanAux
    simp only [scanAux]
    have hdrop : work.dropWhile (fun x => s.visited.contains x) = work.dropWhile fun x => decide (x ∈ v) := by
      rw [hpred s v is es errs h]
    rw [hdrop]
    cases List.dropWhile (fun x => decide (x ∈ v)) work with
    | nil => simp only [io_pure_bind, project, h.instructions, h.edges, h.errors]
    | cons address rest =>
      simp only [io_bind_assoc]
      refine congrArg _ (funext fun r => ?_)
      cases r with
      | error e => exact ih _ _ _ _ _ _ ((h.visit address).error e)
      | ok insn =>
        simp only
        split
        · exact ih _ _ _ _ _ _ ((h.visit address).error _)
        · have hadded := (h.visit address).add insn
          have hstate : Represents
              { (s.visit address).add insn with edges := ((s.visit address).add insn).edges ++ (Recursive.flowEdges d insn).toArray }
              (address :: v) (Recursive.addInsn insn is) (es ++ Recursive.flowEdges d insn) errs :=
            ⟨hadded.visited_iff, hadded.addresses_iff, hadded.instructions, by simp [hadded.edges], hadded.errors⟩
          split
          · simp only [io_bind_assoc]
            exact fast_slot d data insn.next _ _ _ _ _ hstate _ _ fun s' is' errs' hs => ih _ _ _ _ _ _ hs
          · exact ih _ _ _ _ _ _ hstate

/-- The recursive scan computes what its specification on lists does. -/
theorem scan_eq (d : Disassembler) (data : ByteArray) (bytes entry : Nat) (roots : List Nat) :
    Recursive.scanRoots d data bytes entry roots =
      (scanAux d data (4 * bytes + roots.length + 1) roots [] [] [] [] >>= fun out =>
        pure { entry := entry, instructions := out.1, edges := out.2.1, errors := out.2.2 }) := by
  have hempty : Represents {} [] [] [] [] := by
    refine ⟨?_, ?_, rfl, rfl, rfl⟩ <;> simp
  rw [← fast_scan d data _ roots _ _ _ _ _ hempty, io_bind_assoc]
  rfl

/-- The scan from one root. -/
theorem scan_eq_scanRoots (d : Disassembler) (data : ByteArray) (entry : Nat) :
    Recursive.scan d data entry = Recursive.scanRoots d data data.size entry [entry] := rfl

/-! ## Successors -/

theorem mem_successors_iff (insn : Insn) (address : Nat) :
    address ∈ insn.successors ↔
      ((insn.flow = .normal ∨ insn.flow = .call ∨ insn.flow = .conditionalJump) ∧
          address = insn.next) ∨
        ((insn.flow = .jump ∨ insn.flow = .conditionalJump) ∧ insn.target = some address) := by
  cases insn with
  | mk a s asm flow target bil =>
    cases flow <;> cases target <;> simp [Insn.successors, Option.toList, eq_comm]

theorem successors_eq_nil_iff (insn : Insn) :
    insn.successors = [] ↔
      insn.flow = .indirectJump ∨ insn.flow = .ret ∨ insn.flow = .barrier ∨
        (insn.flow = .jump ∧ insn.target = none) := by
  cases insn with
  | mk a s asm flow target bil =>
    cases flow <;> cases target <;> simp [Insn.successors, Option.toList]

theorem successors_length_le_two (insn : Insn) : insn.successors.length ≤ 2 := by
  cases insn with
  | mk a s asm flow target bil =>
    cases flow <;> cases target <;> simp [Insn.successors, Option.toList]

/-- Falling through is possible exactly for non-branching flows and conditional branches. -/
theorem next_mem_successors_of_falls_through (insn : Insn)
    (h : insn.flow = .normal ∨ insn.flow = .call ∨ insn.flow = .conditionalJump) :
    insn.next ∈ insn.successors :=
  (mem_successors_iff insn _).2 (.inl ⟨h, rfl⟩)

/-- Successors do not depend on the assembly text or the lifted semantics. -/
theorem successors_frame (insn : Insn) (asm : String) (bil : Bil.Program) :
    { insn with asm := asm, bil := bil }.successors = insn.successors := rfl

/-- A forward-progress fact: fall-through of a sized instruction is a later address. -/
theorem lt_next_of_size_pos (insn : Insn) (h : insn.size ≠ 0) : insn.address < insn.next := by
  simp only [Insn.next]; omega

/-- Successors exist past the instruction itself exactly when control can fall through. -/
theorem next_mem_successors_of_fallsThrough (insn : Insn) (h : insn.fallsThrough = true) :
    insn.next ∈ insn.successors := by
  refine (mem_successors_iff _ _).2 (.inl ⟨?_, rfl⟩)
  unfold Insn.fallsThrough at h
  cases hf : insn.flow <;> simp_all

/-! ## Sorting -/

theorem insertInsn_perm (insn : Insn) (list : List Insn) :
    (insertInsn insn list).Perm (insn :: list) := by
  induction list with
  | nil => exact .refl _
  | cons head tail ih =>
    show (if insn.address ≤ head.address then insn :: head :: tail
      else head :: insertInsn insn tail).Perm _
    split
    · exact .refl _
    · exact (ih.cons head).trans (.swap _ _ _)

private abbrev SortedAddr (list : List Insn) : Prop :=
  list.Pairwise fun a b => a.address ≤ b.address

theorem insertInsn_sorted (insn : Insn) (list : List Insn) (h : SortedAddr list) :
    SortedAddr (insertInsn insn list) := by
  induction list with
  | nil => exact List.pairwise_singleton _ _
  | cons head tail ih =>
    show SortedAddr (if insn.address ≤ head.address then insn :: head :: tail
      else head :: insertInsn insn tail)
    have ⟨hh, ht⟩ := List.pairwise_cons.1 h
    split
    · rename_i hle
      refine List.pairwise_cons.2 ⟨?_, h⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hle
      · exact Nat.le_trans hle (hh x hx)
    · rename_i hle
      refine List.pairwise_cons.2 ⟨?_, ih ht⟩
      intro x hx
      rcases List.mem_cons.1 ((insertInsn_perm insn tail).mem_iff.1 hx) with rfl | hx
      · omega
      · exact hh x hx

private theorem foldl_insert_perm (input acc : List Insn) :
    (input.foldl (fun result insn => insertInsn insn result) acc).Perm (input ++ acc) := by
  induction input generalizing acc with
  | nil => exact .refl _
  | cons head tail ih =>
    exact (ih _).trans ((insertInsn_perm head acc).append_left tail |>.trans
      List.perm_middle)

private theorem foldl_insert_sorted (input acc : List Insn) (h : SortedAddr acc) :
    SortedAddr (input.foldl (fun result insn => insertInsn insn result) acc) := by
  induction input generalizing acc with
  | nil => exact h
  | cons head tail ih => exact ih _ (insertInsn_sorted head acc h)

/-- The insertion sort is as good a specification of the order. -/
theorem foldl_insert_spec (input : List Insn) :
    (input.foldl (fun result insn => insertInsn insn result) []).Perm input ∧
      SortedAddr (input.foldl (fun result insn => insertInsn insn result) []) := by
  have := foldl_insert_perm input []
  rw [List.append_nil] at this
  exact ⟨this, foldl_insert_sorted _ _ List.Pairwise.nil⟩

theorem sortedInstructions_perm (disasm : Bap.Disasm.Disasm) :
    (sortedInstructions disasm).Perm disasm.instructions :=
  List.mergeSort_perm _ _

theorem sortedInstructions_sorted (disasm : Bap.Disasm.Disasm) :
    (sortedInstructions disasm).Pairwise fun a b => a.address ≤ b.address := by
  have := List.pairwise_mergeSort (l := disasm.instructions) (le := fun left right => decide (left.address ≤ right.address))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
  exact this.imp (by simp)

/-- With distinct addresses the sorted listing is strictly ascending. -/
theorem sortedInstructions_strict (disasm : Bap.Disasm.Disasm)
    (h : (disasm.instructions.map Insn.address).Nodup) :
    (sortedInstructions disasm).Pairwise fun a b => a.address < b.address := by
  have hn : ((sortedInstructions disasm).map Insn.address).Nodup :=
    ((sortedInstructions_perm disasm).map _).nodup_iff.2 h
  have hp := List.pairwise_map.1 hn
  exact (sortedInstructions_sorted disasm).imp₂ (fun _ _ hle hne => Nat.lt_of_le_of_ne hle hne) hp

/-! ## Basic blocks -/

/-- The block-leader addresses computed by `Disasm.blocks`. -/
def leaders (disasm : Bap.Disasm.Disasm) : List Nat :=
  disasm.entry :: (sortedInstructions disasm).flatMap fun insn =>
    match insn.flow with
    | .normal => insn.target.toList
    | _ => insn.next :: insn.target.toList

/-- What `Disasm.blocks` builds, on lists. -/
def build (leaders : List Nat) (current : List Insn) (blocks : List Block) : List Insn → List Block
  | [] =>
    match current with
    | [] => blocks
    | head :: _ => blocks ++ [⟨head.address, current⟩]
  | insn :: rest =>
    if insn.address ∈ leaders && !current.isEmpty then
      match current with
      | [] => build leaders [insn] blocks rest
      | head :: _ => build leaders [insn] (blocks ++ [⟨head.address, current⟩]) rest
    else
      build leaders (current ++ [insn]) blocks rest

/-- `buildBlocks` of the reversed block and the reversed list of blocks is `build`. -/
private theorem fast_build (set : Std.HashSet Nat) (ls : List Nat) (hset : ∀ a, set.contains a = decide (a ∈ ls))
    (input current : List Insn) (blocks : List Block) :
    (fastBuild set current.reverse blocks.reverse input).reverse = build ls current blocks input := by
  induction input generalizing current blocks with
  | nil =>
    dsimp only [fastBuild]
    prw Bap.Disasm.Basic Bap.Disasm.buildBlocks
    cases current with
    | nil => simp [build]
    | cons head tail => simp [build]
  | cons insn rest ih =>
    dsimp only [fastBuild] at ih ⊢
    prw Bap.Disasm.Basic Bap.Disasm.buildBlocks
    simp only [hset, build]
    by_cases hl : insn.address ∈ ls
    · cases current with
      | nil =>
        have := ih [insn] blocks
        simpa [hl] using this
      | cons head tail =>
        have := ih [insn] (blocks ++ [⟨head.address, head :: tail⟩])
        simpa [hl] using this
    · have := ih (current ++ [insn]) blocks
      simpa [hl] using this

theorem blocks_eq (disasm : Bap.Disasm.Disasm) :
    disasm.blocks = build (leaders disasm) [] [] (sortedInstructions disasm) := by
  have hfold : ∀ (ls : List Nat) (set : Std.HashSet Nat) (a : Nat),
      (ls.foldl (fun set address => set.insert address) set).contains a = (set.contains a || decide (a ∈ ls)) := by
    intro ls
    induction ls with
    | nil => intro set a; simp
    | cons x xs ih =>
      intro set a
      rw [List.foldl_cons, ih, Std.HashSet.contains_insert]
      by_cases hx : a = x
      · simp [hx]
      · have : (x == a) = false := by simp; exact fun e => hx e.symm
        simp [hx, this]
  exact fast_build _ (leaders disasm) (fun a => (hfold (leaders disasm) {} a).trans (by simp)) _ [] []

/-- Shape of a finished block: non-empty, labelled by its head, no leader past the head. -/
def BlockOk (ls : List Nat) (block : Block) : Prop :=
  ∃ head tail, block.instructions = head :: tail ∧ block.start = head.address ∧
    ∀ insn ∈ tail, insn.address ∉ ls

private theorem build_spec (ls : List Nat) (current : List Insn) (blocks : List Block)
    (rest : List Insn)
    (hb : ∀ b ∈ blocks, BlockOk ls b)
    (hl : ∀ b ∈ blocks.tail, b.start ∈ ls)
    (hc : ∀ insn ∈ current.tail, insn.address ∉ ls)
    (he : current = [] → blocks = [])
    (hh : blocks ≠ [] → ∀ head ∈ current.head?, head.address ∈ ls) :
    let out := build ls current blocks rest
    out.flatMap Block.instructions = blocks.flatMap Block.instructions ++ current ++ rest ∧
      (∀ b ∈ out, BlockOk ls b) ∧ ∀ b ∈ out.tail, b.start ∈ ls := by
  induction rest generalizing current blocks with
  | nil =>
    cases current with
    | nil =>
      simp only [build]
      exact ⟨by simp, hb, hl⟩
    | cons head tail =>
      simp only [build]
      refine ⟨by simp, ?_, ?_⟩
      · intro b hbm
        rcases List.mem_append.1 hbm with hbm | hbm
        · exact hb b hbm
        · rcases List.mem_singleton.1 hbm with rfl
          exact ⟨head, tail, rfl, rfl, by simpa using hc⟩
      · intro b hbm
        cases blocks with
        | nil => simp at hbm
        | cons b0 bs =>
          simp only [List.cons_append, List.tail_cons] at hbm hl
          rcases List.mem_append.1 hbm with hbm | hbm
          · exact hl b hbm
          · rcases List.mem_singleton.1 hbm with rfl
            exact hh (by simp) head (by simp)
  | cons insn rest ih =>
    simp only [build]
    by_cases hleader : insn.address ∈ ls
    · cases current with
      | nil =>
        have hne : blocks = [] := he rfl
        subst hne
        simp only [List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]
        have := ih [insn] [] (by simp) (by simp) (by simp) (by simp) (by simp)
        simpa using this
      | cons head tail =>
        have hif : (decide (insn.address ∈ ls) && !(head :: tail).isEmpty) = true := by
          simp [hleader]
        rw [ite_eq_left hif]
        have := ih [insn] (blocks ++ [⟨head.address, head :: tail⟩])
          (by
            intro b hbm
            rcases List.mem_append.1 hbm with hbm | hbm
            · exact hb b hbm
            · rcases List.mem_singleton.1 hbm with rfl
              exact ⟨head, tail, rfl, rfl, by simpa using hc⟩)
          (by
            intro b hbm
            cases blocks with
            | nil => simp at hbm
            | cons b0 bs =>
              simp only [List.cons_append, List.tail_cons] at hbm hl
              rcases List.mem_append.1 hbm with hbm | hbm
              · exact hl b hbm
              · rcases List.mem_singleton.1 hbm with rfl
                exact hh (by simp) head (by simp))
          (by simp) (by simp) (by simpa using hleader)
        simpa using this
    · have hif : (decide (insn.address ∈ ls) && !current.isEmpty) = false := by simp [hleader]
      rw [ite_eq_right (by simp [hif])]
      have := ih (current ++ [insn]) blocks hb hl
        (by
          intro x hx
          cases current with
          | nil => simp at hx
          | cons head tail =>
            simp only [List.cons_append, List.tail_cons] at hx
            rcases List.mem_append.1 hx with hx | hx
            · exact hc x (by simpa using hx)
            · rcases List.mem_singleton.1 hx with rfl
              exact hleader)
        (by simp)
        (by
          intro hne x hx
          cases current with
          | nil => exact absurd (he rfl) hne
          | cons head tail =>
            exact hh hne x (by simpa using hx))
      simpa using this

/-- Blocks partition the sorted instruction listing: nothing is lost, duplicated or reordered. -/
theorem blocks_flatten (disasm : Bap.Disasm.Disasm) :
    disasm.blocks.flatMap Block.instructions = sortedInstructions disasm := by
  have := (build_spec (leaders disasm) [] [] (sortedInstructions disasm)
    (by simp) (by simp) (by simp) (by simp) (by simp)).1
  simpa [blocks_eq] using this

theorem blocks_wellFormed (disasm : Bap.Disasm.Disasm) :
    ∀ b ∈ disasm.blocks, BlockOk (leaders disasm) b :=
  blocks_eq disasm ▸ (build_spec (leaders disasm) [] [] (sortedInstructions disasm)
    (by simp) (by simp) (by simp) (by simp) (by simp)).2.1

/-- Every block but the first begins at a leader. -/
theorem blocks_tail_start_leader (disasm : Bap.Disasm.Disasm) :
    ∀ b ∈ disasm.blocks.tail, b.start ∈ leaders disasm :=
  blocks_eq disasm ▸ (build_spec (leaders disasm) [] [] (sortedInstructions disasm)
    (by simp) (by simp) (by simp) (by simp) (by simp)).2.2

theorem target_mem_leaders (disasm : Bap.Disasm.Disasm) (insn : Insn)
    (hi : insn ∈ disasm.instructions) (target : Nat) (ht : insn.target = some target) :
    target ∈ leaders disasm := by
  refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨insn, ?_, ?_⟩)
  · exact (sortedInstructions_perm disasm).mem_iff.2 hi
  · cases insn.flow <;> simp [ht]

theorem next_mem_leaders_of_not_normal (disasm : Bap.Disasm.Disasm) (insn : Insn)
    (hi : insn ∈ disasm.instructions) (hf : insn.flow ≠ .normal) :
    insn.next ∈ leaders disasm := by
  refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨insn, ?_, ?_⟩)
  · exact (sortedInstructions_perm disasm).mem_iff.2 hi
  · cases h : insn.flow <;> simp_all

/-- No recorded branch target lands inside a block, past its head. -/
theorem no_target_inside_block (disasm : Bap.Disasm.Disasm) (block : Block)
    (hb : block ∈ disasm.blocks) (inner : Insn) (hinner : inner ∈ block.instructions.tail)
    (insn : Insn) (hi : insn ∈ disasm.instructions) :
    insn.target ≠ some inner.address := by
  intro ht
  have ⟨head, tail, hshape, _, hnot⟩ := blocks_wellFormed disasm block hb
  rw [hshape] at hinner
  exact hnot inner hinner (target_mem_leaders disasm insn hi _ ht)

/-- Control can only fall from one instruction to its layout successor inside a block when the
former is not a control-flow instruction. -/
theorem block_fallthrough_normal (disasm : Bap.Disasm.Disasm) (block : Block)
    (hb : block ∈ disasm.blocks) (inner : Insn) (hinner : inner ∈ block.instructions.tail)
    (insn : Insn) (hi : insn ∈ disasm.instructions) (hnext : insn.next = inner.address) :
    insn.flow = .normal := by
  have ⟨head, tail, hshape, _, hnot⟩ := blocks_wellFormed disasm block hb
  rw [hshape] at hinner
  exact Decidable.byContradiction fun hf =>
    hnot inner hinner (hnext ▸ next_mem_leaders_of_not_normal disasm insn hi hf)

theorem blocks_nil_iff (disasm : Bap.Disasm.Disasm) :
    disasm.blocks = [] ↔ disasm.instructions = [] := by
  constructor
  · intro h
    have hf := blocks_flatten disasm
    rw [h] at hf
    exact List.Perm.eq_nil ((sortedInstructions_perm disasm).symm.trans (by rw [← hf]; exact .refl _))
  · intro h
    have hp := sortedInstructions_perm disasm
    rw [h] at hp
    have hs := hp.eq_nil
    simp [blocks_eq, hs, build]

/-! ## A partial-correctness logic for `IO` -/

/-- `P` holds of every value `m` can return, in any world. Throwing satisfies it vacuously. -/
def Holds {α} (m : IO α) (P : α → Prop) : Prop :=
  ∀ s r s', m s = EST.Out.ok r s' → P r

/-- `m` always returns normally. -/
def NoThrow {α} (m : IO α) : Prop := ∀ s, ∃ r s', m s = EST.Out.ok r s'

/-- `r` is a possible outcome of `m`. -/
def Returns {α} (m : IO α) (r : α) : Prop := ∃ s s', m s = EST.Out.ok r s'

theorem Holds.pure {α} {P : α → Prop} {a : α} (h : P a) : Holds (pure a : IO α) P := by
  intro s r s' he
  cases he
  exact h

theorem bind_ok {α β} {m : IO α} {f : α → IO β} {s a s1} (h : m s = EST.Out.ok a s1) :
    (m >>= f) s = f a s1 := by
  show EST.bind m f s = _
  unfold EST.bind
  rw [h]

theorem bind_error {α β} {m : IO α} {f : α → IO β} {s e s1} (h : m s = EST.Out.error e s1) :
    (m >>= f) s = EST.Out.error e s1 := by
  show EST.bind m f s = _
  unfold EST.bind
  rw [h]

theorem Holds.bind {α β} {m : IO α} {f : α → IO β} {Q : α → Prop} {P : β → Prop}
    (hm : Holds m Q) (hf : ∀ a, Q a → Returns m a → Holds (f a) P) : Holds (m >>= f) P := by
  intro s r s' he
  cases hms : m s with
  | ok a s1 =>
    rw [bind_ok hms] at he
    exact hf a (hm s a s1 hms) ⟨s, s1, hms⟩ s1 r s' he
  | error e s1 =>
    rw [bind_error hms] at he
    cases he

theorem NoThrow.pure {α} (a : α) : NoThrow (pure a : IO α) := fun s => ⟨a, s, rfl⟩

theorem NoThrow.bind {α β} {m : IO α} {f : α → IO β} (hm : NoThrow m)
    (hf : ∀ a, Returns m a → NoThrow (f a)) : NoThrow (m >>= f) := by
  intro s
  have ⟨a, s1, ha⟩ := hm s
  have ⟨b, s2, hb⟩ := hf a ⟨s, s1, ha⟩ s1
  refine ⟨b, s2, ?_⟩
  rw [bind_ok ha]
  exact hb

theorem Holds.true {α} (m : IO α) : Holds m fun _ => True := fun _ _ _ _ => trivial

/-! ## Linear sweep -/

/-- A decoder result for an address. -/
abbrev Gives (d : Disassembler) (data : ByteArray) (address : Nat) (r : Except String Insn) : Prop :=
  Returns (d.decode address data) r

/-- The big-step trace of the linear sweep from a byte offset. -/
inductive LinearRun (d : Disassembler) (data : ByteArray) (entry : Nat) :
    Nat → List Insn → Option String → Prop
  | finished (offset) : data.size ≤ offset → LinearRun d data entry offset [] none
  | failed (offset error) : offset < data.size → Gives d data (entry + offset) (.error error) →
      LinearRun d data entry offset [] (some error)
  | empty (offset insn) : offset < data.size → Gives d data (entry + offset) (.ok insn) →
      insn.size = 0 →
      LinearRun d data entry offset [] (some "decoder produced a zero-sized instruction")
  | step (offset insn rest outcome) : offset < data.size →
      Gives d data (entry + offset) (.ok insn) → insn.size ≠ 0 →
      LinearRun d data entry (offset + insn.size) rest outcome →
      LinearRun d data entry offset (insn :: rest) outcome

private theorem sweepAux_zero (d data entry offset instructions errors) :
    sweepAux d data entry 0 offset instructions errors = pure (instructions, errors) := rfl

private theorem sweepAux_succ (d : Disassembler) (data entry fuel offset instructions errors) :
    sweepAux d data entry (fuel + 1) offset instructions errors =
      if offset ≥ data.size then pure (instructions, errors) else
      d.decode (entry + offset) data >>= fun r => match r with
        | .error error => pure (instructions, errors ++ [error])
        | .ok insn =>
          if insn.size = 0 then
            pure (instructions, errors ++ ["decoder produced a zero-sized instruction"])
          else
            sweepAux d data entry fuel (offset + insn.size) (instructions ++ [insn]) errors := rfl

private theorem sweepAux_spec (d : Disassembler) (data entry fuel offset instructions errors)
    (hfuel : data.size + 1 ≤ offset + fuel) :
    Holds (sweepAux d data entry fuel offset instructions errors) fun out =>
      ∃ rest outcome, out = (instructions ++ rest, errors ++ outcome.toList) ∧
        LinearRun d data entry offset rest outcome := by
  induction fuel generalizing offset instructions with
  | zero =>
    rw [sweepAux_zero]
    exact Holds.pure ⟨[], none, by simp, .finished _ (by omega)⟩
  | succ fuel ih =>
    rw [sweepAux_succ]
    split
    · exact Holds.pure ⟨[], none, by simp, .finished _ (by omega)⟩
    · rename_i hin
      refine Holds.bind (Holds.true _) fun r _ hr => ?_
      cases r with
      | error error =>
        exact Holds.pure ⟨[], some error, by simp, .failed _ _ (by omega) hr⟩
      | ok insn =>
        simp only
        split
        · rename_i hz
          exact Holds.pure ⟨[], some _, by simp, .empty _ insn (by omega) hr hz⟩
        · rename_i hz
          intro s out s' he
          have ⟨rest, outcome, heq, hrun⟩ :=
            ih (offset + insn.size) (instructions ++ [insn]) (by omega) s out s' he
          exact ⟨insn :: rest, outcome, by simpa using heq, .step _ _ _ _ (by omega) hr hz hrun⟩

/-- Soundness of the linear sweep: any returned disassembly is a complete trace from offset 0. -/
theorem sweep_run (d : Disassembler) (data : ByteArray) (entry : Nat) :
    Holds (Linear.sweep d data entry) fun result =>
      ∃ outcome, result.entry = entry ∧ result.edges = [] ∧ result.errors = outcome.toList ∧
        LinearRun d data entry 0 result.instructions outcome := by
  rw [sweep_eq]
  refine Holds.bind (Q := fun out => ∃ rest outcome, out = ([] ++ rest, [] ++ outcome.toList) ∧
    LinearRun d data entry 0 rest outcome) (sweepAux_spec d data entry _ 0 [] [] (by omega)) ?_
  rintro ⟨is, es⟩ ⟨rest, outcome, heq, hrun⟩ _
  simp only [List.nil_append, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact Holds.pure ⟨outcome, rfl, rfl, rfl, hrun⟩

/-- Linear sweep stops at the first failure: it reports at most one error. -/
theorem sweep_errors_length_le_one (d : Disassembler) (data : ByteArray) (entry : Nat) :
    Holds (Linear.sweep d data entry) fun result => result.errors.length ≤ 1 := by
  intro s r s' he
  have ⟨outcome, _, _, herr, _⟩ := sweep_run d data entry s r s' he
  cases outcome <;> simp_all

/-- Decoder behaves as promised at every address: an instruction labelled with the query. -/
def Consistent (d : Disassembler) (data : ByteArray) : Prop :=
  ∀ address insn, Gives d data address (.ok insn) → insn.address = address

section
variable {d : Disassembler} {data : ByteArray} {entry : Nat}

theorem LinearRun.query_in_range {offset is outcome} (h : LinearRun d data entry offset is outcome) :
    ∀ insn ∈ is, ∃ o, offset ≤ o ∧ o < data.size ∧ Gives d data (entry + o) (.ok insn) ∧
      insn.size ≠ 0 := by
  induction h with
  | finished | failed | empty => simp
  | step offset insn rest outcome hlt hg hz _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨offset, Nat.le_refl _, hlt, hg, hz⟩
    · have ⟨o, ho, h1, h2, h3⟩ := ih x hx
      exact ⟨o, by omega, h1, h2, h3⟩

theorem LinearRun.length_le {offset is outcome} (h : LinearRun d data entry offset is outcome) :
    is.length ≤ data.size - offset := by
  induction h with
  | finished | failed | empty => simp
  | step offset insn rest outcome hlt hg hz _ ih =>
    simp only [List.length_cons]; omega

/-- Each instruction ends where the following one begins. -/
def Contiguous : List Insn → Prop
  | a :: b :: rest => a.next = b.address ∧ Contiguous (b :: rest)
  | _ => True

/-- The instructions of a run are contiguous, in order, and start at the run's offset. -/
theorem LinearRun.contiguous (hc : Consistent d data) {offset is outcome}
    (h : LinearRun d data entry offset is outcome) :
    (∀ head ∈ is.head?, head.address = entry + offset) ∧
      Contiguous is := by
  induction h with
  | finished | failed | empty => simp [Contiguous]
  | step offset insn rest outcome hlt hg hz hrun ih =>
    have haddr := hc _ _ hg
    refine ⟨by simpa using haddr, ?_⟩
    cases rest with
    | nil => simp [Contiguous]
    | cons b rest' =>
      refine ⟨?_, ih.2⟩
      have := ih.1 b (by simp)
      simp only [Insn.next]
      omega

/-- All addresses are inside `[entry + offset, entry + size)`. -/
theorem LinearRun.address_in_range (hc : Consistent d data) {offset is outcome}
    (h : LinearRun d data entry offset is outcome) :
    ∀ insn ∈ is, entry + offset ≤ insn.address ∧ insn.address < entry + data.size := by
  intro insn hi
  have ⟨o, h1, h2, h3, _⟩ := h.query_in_range insn hi
  have := hc _ _ h3
  omega

/-- Without a decode failure, each byte from the offset to the end is covered by some instruction;
a successful run therefore has no gaps. -/
theorem LinearRun.covers (hc : Consistent d data) {offset is}
    (h : LinearRun d data entry offset is none) :
    ∀ byte, offset ≤ byte → byte < data.size →
      ∃ insn ∈ is, insn.address ≤ entry + byte ∧ entry + byte < insn.next := by
  generalize ho : (none : Option String) = outcome at h
  induction h with
  | finished offset hle => intro b h1 h2; omega
  | failed => cases ho
  | empty => cases ho
  | step offset insn rest outcome hlt hg hz hrun ih =>
    intro byte h1 h2
    have haddr := hc _ _ hg
    by_cases hb : byte < offset + insn.size
    · exact ⟨insn, by simp, by omega, by simp only [Insn.next]; omega⟩
    · have ⟨x, hx, hx1, hx2⟩ := ih ho byte (by omega) h2
      exact ⟨x, List.mem_cons_of_mem _ hx, hx1, hx2⟩

/-- The instructions of a run occupy strictly ascending, non-overlapping address ranges. -/
theorem LinearRun.non_overlapping (hc : Consistent d data) {offset is outcome}
    (h : LinearRun d data entry offset is outcome) :
    is.Pairwise fun a b => a.next ≤ b.address := by
  induction h with
  | finished | failed | empty => simp
  | step offset insn rest outcome hlt hg hz hrun ih =>
    refine List.pairwise_cons.2 ⟨?_, ih⟩
    intro x hx
    have ⟨o, h1, _, h3, _⟩ := hrun.query_in_range x hx
    have h4 := hc _ _ h3
    have h5 := hc _ _ hg
    simp only [Insn.next]
    omega

end

/-- Coverage for the top-level sweep. If a consistent decoder never fails, then every byte of the
input lies in exactly one decoded instruction. -/
theorem sweep_exact_cover (d : Disassembler) (data : ByteArray) (entry : Nat)
    (hc : Consistent d data) :
    Holds (Linear.sweep d data entry) fun result => result.errors = [] →
      ∀ byte, byte < data.size →
        ∃ insn ∈ result.instructions, (insn.address ≤ entry + byte ∧ entry + byte < insn.next) ∧
          ∀ other ∈ result.instructions, other.address ≤ entry + byte → entry + byte < other.next →
            other.address = insn.address := by
  intro s r s' he herr byte hb
  have ⟨outcome, _, _, herrs, hrun⟩ := sweep_run d data entry s r s' he
  have hnone : outcome = none := by
    cases outcome <;> simp_all
  subst hnone
  have ⟨x, hx, h1, h2⟩ := hrun.covers hc byte (Nat.zero_le _) hb
  refine ⟨x, hx, ⟨h1, h2⟩, ?_⟩
  intro other ho h3 h4
  have hp := hrun.non_overlapping hc
  refine Decidable.byContradiction fun hne => ?_
  have hsep : x.next ≤ other.address ∨ other.next ≤ x.address := by
    have key : ∀ (l : List Insn), l.Pairwise (fun a b => a.next ≤ b.address) →
        ∀ a ∈ l, ∀ b ∈ l, a.address ≠ b.address → a.next ≤ b.address ∨ b.next ≤ a.address := by
      intro l hl
      induction l with
      | nil => simp
      | cons h t ih =>
        have ⟨hh, ht⟩ := List.pairwise_cons.1 hl
        intro a ha b hb hab
        rcases List.mem_cons.1 ha with rfl | ha'
        · rcases List.mem_cons.1 hb with rfl | hb'
          · exact absurd rfl hab
          · exact .inl (hh b hb')
        · rcases List.mem_cons.1 hb with rfl | hb'
          · exact .inr (hh a ha')
          · exact ih ht a ha' b hb' hab
    exact key _ hp x hx other ho (Ne.symm hne)
  omega

/-- Fuel bound in `sweep` is never the reason to stop, and the decoder is queried only within the
input: each instruction is the answer to a query at an in-range address. -/
theorem sweep_queries_in_range (d : Disassembler) (data : ByteArray) (entry : Nat) :
    Holds (Linear.sweep d data entry) fun result =>
      result.instructions.length ≤ data.size ∧ ∀ insn ∈ result.instructions,
        insn.size ≠ 0 ∧ ∃ o, o < data.size ∧ Gives d data (entry + o) (.ok insn) := by
  intro s r s' he
  have ⟨_, _, _, _, hrun⟩ := sweep_run d data entry s r s' he
  refine ⟨by simpa using hrun.length_le, ?_⟩
  intro insn hi
  have ⟨o, _, h2, h3, h4⟩ := hrun.query_in_range insn hi
  exact ⟨h4, o, h2, h3⟩

private theorem sweepAux_noThrow (d : Disassembler) (data : ByteArray) (entry : Nat)
    (hd : ∀ address, NoThrow (d.decode address data)) (fuel offset instructions errors) :
    NoThrow (sweepAux d data entry fuel offset instructions errors) := by
  induction fuel generalizing offset instructions with
  | zero => rw [sweepAux_zero]; exact NoThrow.pure _
  | succ fuel ih =>
    rw [sweepAux_succ]
    split
    · exact NoThrow.pure _
    · refine NoThrow.bind (hd _) fun r _ => ?_
      cases r with
      | error => exact NoThrow.pure _
      | ok insn =>
        simp only
        split
        · exact NoThrow.pure _
        · exact ih _ _

/-- Termination: for a decoder that does not throw, the sweep always returns. -/
theorem sweep_noThrow (d : Disassembler) (data : ByteArray) (entry : Nat)
    (hd : ∀ address, NoThrow (d.decode address data)) : NoThrow (Linear.sweep d data entry) :=
  sweep_eq d data entry ▸ NoThrow.bind (sweepAux_noThrow d data entry hd _ _ _ _) fun _ _ => NoThrow.pure _

/-! ## Recursive scan -/

private theorem scanAux_zero_done (d data work visited instructions edges errors)
    (h : ∀ a ∈ work, a ∈ visited) :
    scanAux d data 0 work visited instructions edges errors =
      pure (instructions, edges, errors) := by
  have hall : (work.all fun x => decide (x ∈ visited)) = true := by simpa using h
  show (if (work.all fun x => decide (x ∈ visited)) = true then _ else _) = _
  rw [ite_eq_left hall]

private theorem scanAux_zero_left (d data work visited instructions edges errors)
    (h : ¬∀ a ∈ work, a ∈ visited) :
    scanAux d data 0 work visited instructions edges errors =
      pure (instructions, edges, errors ++ [Recursive.outOfFuel]) := by
  have hall : ¬(work.all fun x => decide (x ∈ visited)) = true := by simpa using h
  show (if (work.all fun x => decide (x ∈ visited)) = true then _ else _) = _
  rw [ite_eq_right hall]

private theorem scanAux_succ_nil (d : Disassembler) (data fuel work visited instructions edges errors)
    (h : work.dropWhile (fun x => decide (x ∈ visited)) = []) :
    scanAux d data (fuel + 1) work visited instructions edges errors =
      pure (instructions, edges, errors) := by
  rw [scanAux]
  simp only [h]

private theorem scanAux_succ_cons (d : Disassembler) (data fuel work visited instructions edges
    errors address rest) (h : work.dropWhile (fun x => decide (x ∈ visited)) = address :: rest) :
    scanAux d data (fuel + 1) work visited instructions edges errors =
      d.decode address data >>= fun r => match r with
        | .error error =>
          scanAux d data fuel rest (address :: visited) instructions edges (errors ++ [error])
        | .ok insn =>
          if (insn.address != address || decide (insn.size = 0)) = true then
            scanAux d data fuel rest (address :: visited) instructions edges
              (errors ++ ["decoder returned an inconsistent instruction"])
          else if d.hasDelaySlot insn = true then
            decodeSlot d data insn.next (Recursive.addInsn insn instructions) errors >>= fun out =>
              scanAux d data fuel ((Recursive.nextAddresses d insn) ++ rest) (address :: visited) out.1
                (edges ++ Recursive.flowEdges d insn) out.2
          else
            scanAux d data fuel ((Recursive.nextAddresses d insn) ++ rest) (address :: visited)
              (Recursive.addInsn insn instructions) (edges ++ Recursive.flowEdges d insn) errors := by
  rw [scanAux]
  simp only [h]

private theorem decodeSlot_eq (d : Disassembler) (data slot is errs) :
    decodeSlot d data slot is errs =
      d.decode slot data >>= fun r => match r with
        | .error error => pure (is, errs ++ [error])
        | .ok insn =>
          if (insn.address != slot || decide (insn.size = 0)) = true then
            pure (is, errs ++ ["decoder returned an inconsistent instruction"])
          else
            pure (Recursive.addInsn insn is, errs) := rfl

/-! ### Instruction lists -/

theorem addInsn_nodup (insn : Insn) (is : List Insn) (h : (is.map Insn.address).Nodup) :
    ((Recursive.addInsn insn is).map Insn.address).Nodup := by
  unfold Recursive.addInsn
  split
  · exact h
  · rename_i hany
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.2 ⟨h, by simp, ?_⟩
    intro x hx y hy
    rcases List.mem_map.1 hx with ⟨i, hi, rfl⟩
    have hy' : y = insn.address := by simpa using hy
    subst hy'
    intro heq
    exact hany (List.any_eq_true.2 ⟨i, hi, by simpa using heq⟩)

theorem mem_addInsn_of_mem (insn x : Insn) (is : List Insn) (h : x ∈ is) :
    x ∈ Recursive.addInsn insn is := by
  unfold Recursive.addInsn
  split
  · exact h
  · exact List.mem_append_left _ h

theorem mem_addInsn (insn x : Insn) (is : List Insn) (h : x ∈ Recursive.addInsn insn is) :
    x ∈ is ∨ x = insn := by
  unfold Recursive.addInsn at h
  split at h
  · exact .inl h
  · simpa using h

/-- When instructions are determined by their addresses, the listing holds the added one. -/
theorem self_mem_addInsn (insn : Insn) (is : List Insn)
    (h : ∀ x ∈ is, x.address = insn.address → x = insn) : insn ∈ Recursive.addInsn insn is := by
  unfold Recursive.addInsn
  split
  · rename_i hany
    have ⟨x, hx, he⟩ := List.any_eq_true.1 hany
    have := h x hx (by simpa using he)
    exact this ▸ hx
  · simp

theorem addInsn_length (insn : Insn) (is : List Insn) :
    (Recursive.addInsn insn is).length ≤ is.length + 1 := by
  unfold Recursive.addInsn
  split <;> simp

/-- Reachability along a set of recovered CFG edges. -/
inductive EdgeReach (edges : List (Nat × Nat)) (roots : List Nat) : Nat → Prop
  | root {a} : a ∈ roots → EdgeReach edges roots a
  | step {a b} : EdgeReach edges roots a → (a, b) ∈ edges → EdgeReach edges roots b

theorem EdgeReach.mono {e e' : List (Nat × Nat)} {roots a} (hsub : ∀ x ∈ e, x ∈ e')
    (h : EdgeReach e roots a) : EdgeReach e' roots a := by
  induction h with
  | root hr => exact .root hr
  | step _ he ih => exact .step ih (hsub _ he)

theorem EdgeReach.mono_roots {e : List (Nat × Nat)} {roots roots' : List Nat} {a} (hsub : ∀ x ∈ roots, x ∈ roots')
    (h : EdgeReach e roots a) : EdgeReach e roots' a := by
  induction h with
  | root hr => exact .root (hsub _ hr)
  | step _ he ih => exact .step ih he

/-! ### Edges and delay slots -/

/-- The edges of an instruction without a delay slot leave it for its successors. -/
theorem mem_flowEdges_plain (d : Disassembler) (insn : Insn) (h : d.hasDelaySlot insn = false)
    (hc : Recursive.isAnnulledCall d insn = false) (a b : Nat) :
    (a, b) ∈ Recursive.flowEdges d insn ↔ a = insn.address ∧ b ∈ insn.successors := by
  simp only [Recursive.flowEdges, h, hc, Bool.false_eq_true, ite_false, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx, rfl, rfl⟩
    exact ⟨rfl, hx⟩
  · rintro ⟨rfl, hx⟩
    exact ⟨b, hx, rfl, rfl⟩

theorem flowAddresses_plain (d : Disassembler) (insn : Insn) (h : d.hasDelaySlot insn = false)
    (hc : Recursive.isAnnulledCall d insn = false) :
    Recursive.flowAddresses d insn = insn.successors := by
  simp [Recursive.flowAddresses, Recursive.isDelayedConditional, h, hc]

/-- A call that annuls its slot, as a MIPS `BLTZALL`: into the slot, if it is taken, and over it, if it isn't. -/
theorem flowEdges_annulled_call (d : Disassembler) (insn : Insn) (h : Recursive.isAnnulledCall d insn = true) :
    Recursive.flowEdges d insn = [(insn.address, insn.next), (insn.address, insn.next + insn.size)] := by
  have hd : d.hasDelaySlot insn = false := by
    simp only [Recursive.isAnnulledCall, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1
  simp [Recursive.flowEdges, Recursive.pastSlot, h, hd]

/-- A scan goes on from such a call at the slot and past it, and the slot has its own edge past itself. -/
theorem flowAddresses_annulled_call (d : Disassembler) (insn : Insn) (h : Recursive.isAnnulledCall d insn = true) :
    Recursive.flowAddresses d insn = [insn.next, insn.next + insn.size] := by
  have hc : Recursive.isDelayedConditional d insn = false := by
    simp only [Recursive.isAnnulledCall, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [Recursive.isDelayedConditional, h.1.1]
  simp [Recursive.flowAddresses, Recursive.pastSlot, hc, h]

/-- Control can fall through an instruction without a slot of its own to the next instruction. -/
theorem next_mem_flowAddresses (d : Disassembler) (insn : Insn) (h : d.hasDelaySlot insn = false)
    (hft : insn.fallsThrough = true) : insn.next ∈ Recursive.flowAddresses d insn := by
  cases hc : Recursive.isAnnulledCall d insn with
  | false =>
    rw [flowAddresses_plain d insn h hc]
    exact next_mem_successors_of_fallsThrough insn hft
  | true =>
    rw [flowAddresses_annulled_call d insn hc]
    simp

/-- An unconditional delayed transfer enters its slot, and only the slot goes on to the successors of the branch.
So the slot has no fall-through edge of its own, unless the scan also reaches it another way. -/
theorem mem_flowEdges_delayed (d : Disassembler) (insn : Insn) (h : d.hasDelaySlot insn = true)
    (hc : insn.flow ≠ .conditionalJump) (a b : Nat) : (a, b) ∈ Recursive.flowEdges d insn ↔
      (a = insn.address ∧ b = insn.next) ∨ (a = insn.next ∧ b ∈ insn.successors) := by
  have hd : Recursive.isDelayedConditional d insn = false := by
    simp [Recursive.isDelayedConditional, hc]
  simp only [Recursive.flowEdges, h, hd, ite_true, Bool.false_eq_true, ite_false, List.mem_cons, List.mem_map,
    Prod.mk.injEq]
  constructor
  · rintro (h | ⟨x, hx, rfl, rfl⟩)
    · exact .inl h
    · exact .inr ⟨rfl, hx⟩
  · rintro (h | ⟨rfl, hx⟩)
    · exact .inl h
    · exact .inr ⟨b, hx, rfl, rfl⟩

/-- A conditional branch with a delay slot runs it whichever way it goes, and the slot decides: on to the target or
past itself. The branch has no edge of its own to either. -/
theorem mem_flowEdges_delayed_conditional (d : Disassembler) (insn : Insn) (h : d.hasDelaySlot insn = true)
    (hc : insn.flow = .conditionalJump) (ha : d.annulsSlot insn = false) (a b : Nat) :
    (a, b) ∈ Recursive.flowEdges d insn ↔
      (a = insn.address ∧ b = insn.next) ∨ (a = insn.next ∧ b = Recursive.pastSlot insn) ∨
        (a = insn.next ∧ b ∈ insn.target.toList) := by
  cases ht : insn.target <;>
    simp [Recursive.flowEdges, Recursive.isDelayedConditional, h, hc, ha, ht]

/-- A branch that annuls its slot goes through it only to the target; not taken, it skips the slot. The slot has no
edge past itself, and that is the exact flow of a MIPS `BEQL`. -/
theorem mem_flowEdges_annulled (d : Disassembler) (insn : Insn) (h : d.hasDelaySlot insn = true)
    (hc : insn.flow = .conditionalJump) (ha : d.annulsSlot insn = true) (a b : Nat) :
    (a, b) ∈ Recursive.flowEdges d insn ↔
      (a = insn.address ∧ b = insn.next) ∨ (a = insn.address ∧ b = Recursive.pastSlot insn) ∨
        (a = insn.next ∧ b ∈ insn.target.toList) := by
  cases ht : insn.target <;>
    simp [Recursive.flowEdges, Recursive.isDelayedConditional, h, hc, ha, ht]

/-- `BEQL` with a target: exactly the edge into the slot, the one over it, and the one from the slot to the target. -/
theorem flowEdges_annulled_exact (d : Disassembler) (insn : Insn) (target : Nat) (h : d.hasDelaySlot insn = true)
    (hc : insn.flow = .conditionalJump) (ha : d.annulsSlot insn = true) (ht : insn.target = some target) :
    Recursive.flowEdges d insn =
      [(insn.address, insn.next), (insn.address, insn.next + insn.size), (insn.next, target)] := by
  simp [Recursive.flowEdges, Recursive.isDelayedConditional, Recursive.pastSlot, h, hc, ha, ht]

/-- `BEQ` with a target: exactly the edge into the slot and its two ways out. -/
theorem flowEdges_delayed_conditional_exact (d : Disassembler) (insn : Insn) (target : Nat)
    (h : d.hasDelaySlot insn = true) (hc : insn.flow = .conditionalJump) (ha : d.annulsSlot insn = false)
    (ht : insn.target = some target) :
    Recursive.flowEdges d insn =
      [(insn.address, insn.next), (insn.next, insn.next + insn.size), (insn.next, target)] := by
  simp [Recursive.flowEdges, Recursive.isDelayedConditional, Recursive.pastSlot, h, hc, ha, ht]

/-- A delayed conditional branch goes on past its slot or to its target, and never scans its slot as a fall-through. -/
theorem flowAddresses_delayed_conditional (d : Disassembler) (insn : Insn) (h : d.hasDelaySlot insn = true)
    (hc : insn.flow = .conditionalJump) :
    Recursive.flowAddresses d insn = Recursive.pastSlot insn :: insn.target.toList := by
  simp [Recursive.flowAddresses, Recursive.isDelayedConditional, h, hc]

theorem flowAddresses_delayed (d : Disassembler) (insn : Insn) (h : d.hasDelaySlot insn = true)
    (hc : insn.flow ≠ .conditionalJump) :
    Recursive.flowAddresses d insn = insn.successors := by
  simp [Recursive.flowAddresses, Recursive.isDelayedConditional, Recursive.isAnnulledCall, hc, h]

theorem flowAddresses_length_le_two (d : Disassembler) (insn : Insn) :
    (Recursive.flowAddresses d insn).length ≤ 2 := by
  unfold Recursive.flowAddresses
  split
  · cases insn.target <;> simp
  · split
    · simp
    · exact successors_length_le_two insn

/-- Every place control goes on to from an instruction is reached along its edges, from the instruction. -/
private theorem flowAddresses_reached {es : List (Nat × Nat)} {roots : List Nat} (d : Disassembler) (insn : Insn)
    (hra : EdgeReach es roots insn.address) (hflow : ∀ e ∈ Recursive.flowEdges d insn, e ∈ es)
    (b : Nat) (hb : b ∈ Recursive.flowAddresses d insn) : EdgeReach es roots b := by
  cases hdelay : d.hasDelaySlot insn with
  | false =>
    cases hannul : Recursive.isAnnulledCall d insn with
    | false =>
      rw [flowAddresses_plain d insn hdelay hannul] at hb
      exact .step hra (hflow _ ((mem_flowEdges_plain d insn hdelay hannul _ _).2 ⟨rfl, hb⟩))
    | true =>
      rw [flowAddresses_annulled_call d insn hannul] at hb
      rw [flowEdges_annulled_call d insn hannul] at hflow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact .step hra (hflow _ (by simp))
      · exact .step hra (hflow _ (by simp))
  | true =>
    by_cases hc : insn.flow = .conditionalJump
    · rw [flowAddresses_delayed_conditional d insn hdelay hc] at hb
      cases han : d.annulsSlot insn with
      | false =>
        have mem := mem_flowEdges_delayed_conditional d insn hdelay hc han
        have slot : EdgeReach es roots insn.next := .step hra (hflow _ ((mem _ _).2 (.inl ⟨rfl, rfl⟩)))
        rcases List.mem_cons.1 hb with rfl | hb
        · exact .step slot (hflow _ ((mem _ _).2 (.inr (.inl ⟨rfl, rfl⟩))))
        · exact .step slot (hflow _ ((mem _ _).2 (.inr (.inr ⟨rfl, hb⟩))))
      | true =>
        have mem := mem_flowEdges_annulled d insn hdelay hc han
        rcases List.mem_cons.1 hb with rfl | hb
        · exact .step hra (hflow _ ((mem _ _).2 (.inr (.inl ⟨rfl, rfl⟩))))
        · exact .step (.step hra (hflow _ ((mem _ _).2 (.inl ⟨rfl, rfl⟩))))
            (hflow _ ((mem _ _).2 (.inr (.inr ⟨rfl, hb⟩))))
    · rw [flowAddresses_delayed d insn hdelay hc] at hb
      have mem := mem_flowEdges_delayed d insn hdelay hc
      exact .step (.step hra (hflow _ ((mem _ _).2 (.inl ⟨rfl, rfl⟩))))
        (hflow _ ((mem _ _).2 (.inr ⟨rfl, hb⟩)))

/-- Where a scan goes on from an instruction is at most three addresses: where control goes on, and what it calls. -/
theorem nextAddresses_length_le_three (d : Disassembler) (insn : Insn) :
    (Recursive.nextAddresses d insn).length ≤ 3 := by
  have h := flowAddresses_length_le_two d insn
  have : (Recursive.callTarget insn).length ≤ 1 := by
    unfold Recursive.callTarget
    split
    · cases insn.target <;> simp
    · simp
  simp only [Recursive.nextAddresses, List.length_append]
  omega

/-- Control going on from an instruction is a place a scan goes on to. -/
theorem next_mem_nextAddresses (d : Disassembler) (insn : Insn) (h : d.hasDelaySlot insn = false)
    (hft : insn.fallsThrough = true) : insn.next ∈ Recursive.nextAddresses d insn :=
  List.mem_append_left _ (next_mem_flowAddresses d insn h hft)

/-- The subroutine of a direct call is a place a scan goes on to. -/
theorem call_mem_nextAddresses (d : Disassembler) (insn : Insn) (target : Nat) (h : insn.flow = .call)
    (ht : insn.target = some target) : target ∈ Recursive.nextAddresses d insn := by
  refine List.mem_append_right _ ?_
  simp [Recursive.callTarget, h, ht]

/-- Every place a scan goes on to from an instruction is reached along its edges or its call, from the instruction. -/
private theorem nextAddresses_reached {es : List (Nat × Nat)} {roots : List Nat} (d : Disassembler) (insn : Insn)
    (hra : EdgeReach es roots insn.address) (hflow : ∀ e ∈ Recursive.flowEdges d insn, e ∈ es)
    (hcall : ∀ e ∈ Recursive.callEdges insn, e ∈ es)
    (b : Nat) (hb : b ∈ Recursive.nextAddresses d insn) : EdgeReach es roots b := by
  rcases List.mem_append.1 hb with hb | hb
  · exact flowAddresses_reached d insn hra hflow b hb
  · exact .step hra (hcall _ (List.mem_map.2 ⟨b, hb, rfl⟩))

/-- The edge into the slot of any delayed instruction. -/
private theorem slot_edge (d : Disassembler) (insn : Insn) (h : d.hasDelaySlot insn = true) :
    (insn.address, insn.next) ∈ Recursive.flowEdges d insn := by
  simp only [Recursive.flowEdges, h, ite_true]
  split
  · split <;> simp
  · simp

/-- `J` with a delay slot: the branch goes to the slot and the slot to the target, nothing else. -/
theorem flowEdges_delayed_jump (d : Disassembler) (insn : Insn) (target : Nat)
    (h : d.hasDelaySlot insn = true) (hf : insn.flow = .jump) (ht : insn.target = some target) :
    Recursive.flowEdges d insn = [(insn.address, insn.next), (insn.next, target)] := by
  simp [Recursive.flowEdges, Recursive.isDelayedConditional, h, Insn.successors, hf, ht]

private theorem dropWhile_nil_all (work visited : List Nat)
    (h : work.dropWhile (fun x => decide (x ∈ visited)) = []) : ∀ a ∈ work, a ∈ visited := by
  intro a ha
  induction work with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.dropWhile_cons] at h
    split at h
    · rename_i hx
      rcases List.mem_cons.1 ha with rfl | ha'
      · simpa using hx
      · exact ih h ha'
    · cases h

private theorem dropWhile_cons_spec (work visited : List Nat) (a : Nat) (rest : List Nat)
    (h : work.dropWhile (fun x => decide (x ∈ visited)) = a :: rest) :
    a ∉ visited ∧ a ∈ work ∧ (∀ x ∈ rest, x ∈ work) ∧ ∀ x ∈ work, x ∈ visited ∨ x = a ∨ x ∈ rest := by
  induction work with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.dropWhile_cons] at h
    split at h
    · rename_i hy
      have ⟨h1, h2, h3, h4⟩ := ih h
      refine ⟨h1, List.mem_cons_of_mem _ h2, fun x hx => List.mem_cons_of_mem _ (h3 x hx), ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact .inl (by simpa using hy)
      · exact h4 x hx'
    · rename_i hy
      rcases List.cons.inj h with ⟨rfl, rfl⟩
      refine ⟨by simpa using hy, by simp, fun x hx => List.mem_cons_of_mem _ hx, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact .inr (.inl rfl)
      · exact .inr (.inr hx')

/-- That an edge is of an answer of the decoder. -/
def EdgeOf (d : Disassembler) (data : ByteArray) (of : Insn → List (Nat × Nat)) (e : Nat × Nat) : Prop :=
  ∃ insn, insn.size ≠ 0 ∧ Gives d data insn.address (.ok insn) ∧ e ∈ of insn

/-- What holds of a finished recursive scan. Its instructions are reached from its roots along its edges and calls, and
the calls are the ones of answers of the decoder, like the edges. -/
structure ScanOk (d : Disassembler) (data : ByteArray) (roots : List Nat)
    (is : List Insn) (es : List (Nat × Nat)) : Prop where
  nodup : (is.map Insn.address).Nodup
  decoded : ∀ insn ∈ is, insn.size ≠ 0 ∧ Gives d data insn.address (.ok insn)
  edges : ∀ e ∈ es, EdgeOf d data (Recursive.flowEdges d) e
  reach : ∃ calls : List (Nat × Nat), (∀ e ∈ calls, EdgeOf d data Recursive.callEdges e) ∧
    ∀ insn ∈ is, EdgeReach (es ++ calls) roots insn.address

private structure ScanInv (d : Disassembler) (data : ByteArray) (roots : List Nat) (work : List Nat)
    (is : List Insn) (es calls : List (Nat × Nat)) : Prop where
  nodup : (is.map Insn.address).Nodup
  decoded : ∀ insn ∈ is, insn.size ≠ 0 ∧ Gives d data insn.address (.ok insn)
  edges : ∀ e ∈ es, EdgeOf d data (Recursive.flowEdges d) e
  callsOk : ∀ e ∈ calls, EdgeOf d data Recursive.callEdges e
  reach : ∀ insn ∈ is, EdgeReach (es ++ calls) roots insn.address
  reachWork : ∀ a ∈ work, EdgeReach (es ++ calls) roots a

private theorem decodeSlot_noThrow (d : Disassembler) (data : ByteArray)
    (hd : ∀ address, NoThrow (d.decode address data)) (slot is errs) :
    NoThrow (decodeSlot d data slot is errs) := by
  rw [decodeSlot_eq]
  refine NoThrow.bind (hd _) fun r _ => ?_
  cases r with
  | error => exact NoThrow.pure _
  | ok insn =>
    simp only
    split <;> exact NoThrow.pure _

private theorem decodeSlot_spec (d : Disassembler) (data : ByteArray) (slot : Nat) (is : List Insn)
    (errs : List String) :
    Holds (decodeSlot d data slot is errs) fun out =>
      (∀ x ∈ is, x ∈ out.1) ∧ (∀ e ∈ errs, e ∈ out.2) ∧
        (∀ x ∈ out.1, x ∈ is ∨ (x.address = slot ∧ x.size ≠ 0 ∧ Gives d data slot (.ok x))) ∧
        ((is.map Insn.address).Nodup → (out.1.map Insn.address).Nodup) ∧
        out.1.length + out.2.length ≤ is.length + errs.length + 1 := by
  rw [decodeSlot_eq]
  refine Holds.bind (Holds.true _) fun r _ hr => ?_
  cases r with
  | error error =>
    exact Holds.pure ⟨fun _ h => h, fun e he => List.mem_append_left _ he, fun x hx => .inl hx,
      id, by simp <;> omega⟩
  | ok insn =>
    simp only
    split
    · exact Holds.pure ⟨fun _ h => h, fun e he => List.mem_append_left _ he, fun x hx => .inl hx,
        id, by simp <;> omega⟩
    · rename_i hgood
      have hg : insn.address = slot ∧ ¬insn.size = 0 := by simpa using hgood
      refine Holds.pure ⟨fun x hx => mem_addInsn_of_mem _ _ _ hx, fun _ h => h, ?_, addInsn_nodup _ _, ?_⟩
      · intro x hx
        rcases mem_addInsn _ _ _ hx with h | rfl
        · exact .inl h
        · exact .inr ⟨hg.1, hg.2, hr⟩
      · have := addInsn_length insn is
        show (Recursive.addInsn insn is).length + errs.length ≤ _
        omega

private theorem scanAux_spec (d : Disassembler) (data : ByteArray) (roots : List Nat) (fuel : Nat)
    (work visited : List Nat) (is : List Insn) (es calls : List (Nat × Nat)) (errs : List String)
    (hinv : ScanInv d data roots work is es calls) :
    Holds (scanAux d data fuel work visited is es errs) fun out =>
      ScanOk d data roots out.1 out.2.1 ∧
        out.1.length + out.2.2.length ≤ is.length + errs.length + 2 * fuel + 1 := by
  have finish : ScanOk d data roots is es := ⟨hinv.nodup, hinv.decoded, hinv.edges, calls, hinv.callsOk, hinv.reach⟩
  induction fuel generalizing work visited is es calls errs with
  | zero =>
    by_cases hdone : ∀ a ∈ work, a ∈ visited
    · rw [scanAux_zero_done _ _ _ _ _ _ _ hdone]
      exact Holds.pure ⟨finish, by simp <;> omega⟩
    · rw [scanAux_zero_left _ _ _ _ _ _ _ hdone]
      exact Holds.pure ⟨finish, by simp <;> omega⟩
  | succ fuel ih =>
    cases hd : work.dropWhile (fun x => decide (x ∈ visited)) with
    | nil =>
      rw [scanAux_succ_nil _ _ _ _ _ _ _ _ hd]
      exact Holds.pure ⟨finish, by simp <;> omega⟩
    | cons address rest =>
      have ⟨_, hmem, hsub, _⟩ := dropWhile_cons_spec _ _ _ _ hd
      have hra : EdgeReach (es ++ calls) roots address := hinv.reachWork _ hmem
      have hrw : ∀ a ∈ rest, EdgeReach (es ++ calls) roots a := fun a ha => hinv.reachWork a (hsub a ha)
      rw [scanAux_succ_cons _ _ _ _ _ _ _ _ _ _ hd]
      have skip : ∀ errs', errs'.length = errs.length + 1 →
          Holds (scanAux d data fuel rest (address :: visited) is es errs') fun out =>
            ScanOk d data roots out.1 out.2.1 ∧
              out.1.length + out.2.2.length ≤ is.length + errs.length + 2 * (fuel + 1) + 1 := by
        intro errs' hl s out s' he
        have ⟨h1, h2⟩ := ih rest (address :: visited) is es calls errs'
          ⟨hinv.nodup, hinv.decoded, hinv.edges, hinv.callsOk, hinv.reach, hrw⟩ finish s out s' he
        exact ⟨h1, by omega⟩
      refine Holds.bind (Holds.true _) fun r _ hr => ?_
      cases r with
      | error error => exact skip _ (by simp)
      | ok insn =>
        simp only
        split
        · exact skip _ (by simp)
        · rename_i hgood
          have hg : insn.address = address ∧ ¬insn.size = 0 := by simpa using hgood
          have haddr := hg.1
          have hsize : insn.size ≠ 0 := hg.2
          have hr' : Gives d data insn.address (.ok insn) := haddr ▸ hr
          let es' := es ++ Recursive.flowEdges d insn
          let calls' := calls ++ Recursive.callEdges insn
          have hsub' : ∀ x ∈ es ++ calls, x ∈ es' ++ calls' := by
            intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact List.mem_append_left _ (List.mem_append_left _ hx)
            · exact List.mem_append_right _ (List.mem_append_left _ hx)
          have hflow : ∀ e ∈ Recursive.flowEdges d insn, e ∈ es' ++ calls' :=
            fun x hx => List.mem_append_left _ (List.mem_append_right _ hx)
          have hcall : ∀ e ∈ Recursive.callEdges insn, e ∈ es' ++ calls' :=
            fun x hx => List.mem_append_right _ (List.mem_append_right _ hx)
          have hra' : EdgeReach (es' ++ calls') roots address := hra.mono hsub'
          have hedges : ∀ e ∈ es', EdgeOf d data (Recursive.flowEdges d) e := by
            intro e he
            rcases List.mem_append.1 he with he | he
            · exact hinv.edges e he
            · exact ⟨insn, hsize, hr', he⟩
          have hcalls : ∀ e ∈ calls', EdgeOf d data Recursive.callEdges e := by
            intro e he
            rcases List.mem_append.1 he with he | he
            · exact hinv.callsOk e he
            · exact ⟨insn, hsize, hr', he⟩
          have hwork : ∀ a ∈ (Recursive.nextAddresses d insn) ++ rest, EdgeReach (es' ++ calls') roots a := by
            intro b hb
            rcases List.mem_append.1 hb with hb | hb
            · exact nextAddresses_reached d insn (haddr.symm ▸ hra') hflow hcall b hb
            · exact (hrw b hb).mono hsub'
          have hadded : ∀ x ∈ Recursive.addInsn insn is, EdgeReach (es' ++ calls') roots x.address := by
            intro x hx
            rcases mem_addInsn _ _ _ hx with h | rfl
            · exact (hinv.reach x h).mono hsub'
            · rw [haddr]
              exact hra'
          have hdec : ∀ x ∈ Recursive.addInsn insn is, x.size ≠ 0 ∧ Gives d data x.address (.ok x) := by
            intro x hx
            rcases mem_addInsn _ _ _ hx with h | rfl
            · exact hinv.decoded x h
            · exact ⟨hsize, hr'⟩
          have hlen := addInsn_length insn is
          split
          · rename_i hdelay
            refine Holds.bind (decodeSlot_spec d data insn.next _ errs) fun out hout _ => ?_
            obtain ⟨_, _, hmem', hnd, hcount⟩ := hout
            intro s result s' he
            have hinv' : ScanInv d data roots ((Recursive.nextAddresses d insn) ++ rest) out.1 es' calls' :=
              { nodup := hnd (addInsn_nodup _ _ hinv.nodup)
                decoded := by
                  intro x hx
                  rcases hmem' x hx with h | ⟨h1, h2, h3⟩
                  · exact hdec x h
                  · exact ⟨h2, h1 ▸ h3⟩
                edges := hedges
                callsOk := hcalls
                reach := by
                  intro x hx
                  rcases hmem' x hx with h | ⟨h1, _, _⟩
                  · exact hadded x h
                  · rw [h1]
                    exact .step hra' (haddr ▸ hflow _ (slot_edge d insn hdelay))
                reachWork := hwork }
            have ⟨h1, h2⟩ := ih ((Recursive.nextAddresses d insn) ++ rest) (address :: visited) out.1 es' calls' out.2
              hinv' ⟨hinv'.nodup, hinv'.decoded, hinv'.edges, calls', hinv'.callsOk, hinv'.reach⟩ s result s' he
            exact ⟨h1, by omega⟩
          · intro s result s' he
            have hinv' : ScanInv d data roots ((Recursive.nextAddresses d insn) ++ rest) (Recursive.addInsn insn is) es' calls' :=
              { nodup := addInsn_nodup _ _ hinv.nodup
                decoded := hdec
                edges := hedges
                callsOk := hcalls
                reach := hadded
                reachWork := hwork }
            have ⟨h1, h2⟩ := ih ((Recursive.nextAddresses d insn) ++ rest) (address :: visited)
              (Recursive.addInsn insn is) es' calls' errs
              hinv' ⟨hinv'.nodup, hinv'.decoded, hinv'.edges, calls', hinv'.callsOk, hinv'.reach⟩ s result s' he
            exact ⟨h1, by omega⟩

/-- Soundness of the recursive scan for an arbitrary (even effectful) decoder: instruction addresses
are unique, each instruction is a decoder answer at its own address and has non-zero size, each
edge and each call comes from a decoded instruction, and everything is reachable from the roots. -/
theorem scan_sound (d : Disassembler) (data : ByteArray) (bytes entry : Nat) (roots : List Nat) :
    Holds (Recursive.scanRoots d data bytes entry roots) fun result =>
      result.entry = entry ∧ ScanOk d data roots result.instructions result.edges ∧
        result.instructions.length + result.errors.length ≤ 2 * (4 * bytes + roots.length + 1) + 1 := by
  rw [scan_eq]
  refine Holds.bind (Q := fun out => ScanOk d data roots out.1 out.2.1 ∧
      out.1.length + out.2.2.length ≤ [].length + [].length + 2 * (4 * bytes + roots.length + 1) + 1)
    (scanAux_spec d data roots _ roots [] [] [] [] []
      { nodup := by simp, decoded := by simp, edges := by simp, callsOk := by simp, reach := by simp
        reachWork := fun _ ha => .root ha }) ?_
  rintro ⟨is, es, errs⟩ ⟨h1, h2⟩ _
  refine Holds.pure ⟨rfl, h1, ?_⟩
  simp only [List.length_nil] at h2
  show is.length + errs.length ≤ _
  omega

private theorem scanAux_noThrow (d : Disassembler) (data : ByteArray)
    (hd : ∀ address, NoThrow (d.decode address data)) (fuel work visited is es errs) :
    NoThrow (scanAux d data fuel work visited is es errs) := by
  induction fuel generalizing work visited is es errs with
  | zero =>
    by_cases hdone : ∀ a ∈ work, a ∈ visited
    · rw [scanAux_zero_done _ _ _ _ _ _ _ hdone]; exact NoThrow.pure _
    · rw [scanAux_zero_left _ _ _ _ _ _ _ hdone]; exact NoThrow.pure _
  | succ fuel ih =>
    cases hdrop : work.dropWhile (fun x => decide (x ∈ visited)) with
    | nil => rw [scanAux_succ_nil _ _ _ _ _ _ _ _ hdrop]; exact NoThrow.pure _
    | cons address rest =>
      rw [scanAux_succ_cons _ _ _ _ _ _ _ _ _ _ hdrop]
      refine NoThrow.bind (hd _) fun r _ => ?_
      cases r with
      | error => exact ih _ _ _ _ _
      | ok insn =>
        simp only
        split
        · exact ih _ _ _ _ _
        · split
          · exact NoThrow.bind (decodeSlot_noThrow d data hd _ _ _) fun _ _ => ih _ _ _ _ _
          · exact ih _ _ _ _ _

/-- Termination of the scan for a decoder that does not throw. -/
theorem scan_noThrow (d : Disassembler) (data : ByteArray) (bytes entry : Nat) (roots : List Nat)
    (hd : ∀ address, NoThrow (d.decode address data)) : NoThrow (Recursive.scanRoots d data bytes entry roots) :=
  scan_eq d data bytes entry roots ▸ NoThrow.bind (scanAux_noThrow d data hd _ _ _ _ _ _) fun _ _ => NoThrow.pure _

/-! ### Completeness -/

/-- `insn` is the well-formed decoding the scan accepts at `address`. -/
def Valid (f : Nat → Except String Insn) (address : Nat) (insn : Insn) : Prop :=
  f address = .ok insn ∧ insn.address = address ∧ insn.size ≠ 0

/-- Reachability under a deterministic decoder. -/
inductive Reach (d : Disassembler) (f : Nat → Except String Insn) (roots : List Nat) : Nat → Prop
  | root {a} : a ∈ roots → Reach d f roots a
  | step {a b insn} : Reach d f roots a → Valid f a insn → b ∈ Recursive.nextAddresses d insn → Reach d f roots b

/-- A delay slot is accounted for: its instruction is listed or its decode error is reported. -/
def SlotCovered (f : Nat → Except String Insn) (is : List Insn) (errs : List String) (slot : Nat) :
    Prop :=
  (∀ insn, Valid f slot insn → insn ∈ is) ∧ ∀ error, f slot = .error error → error ∈ errs

/-- An address is accounted for: its instruction is listed with its edges and its delay slot, or its
decode error is reported. -/
def Accounted (d : Disassembler) (f : Nat → Except String Insn) (is : List Insn)
    (es : List (Nat × Nat)) (errs : List String) (address : Nat) : Prop :=
  (∀ insn, Valid f address insn → insn ∈ is ∧ (∀ e ∈ Recursive.flowEdges d insn, e ∈ es) ∧
    (d.hasDelaySlot insn = true → SlotCovered f is errs insn.next)) ∧
    ∀ error, f address = .error error → error ∈ errs

private theorem Accounted.mono {d : Disassembler} {f : Nat → Except String Insn} {is is' : List Insn}
    {es es' : List (Nat × Nat)} {errs errs' : List String} {a : Nat}
    (his : ∀ x ∈ is, x ∈ is') (hes : ∀ x ∈ es, x ∈ es') (herr : ∀ x ∈ errs, x ∈ errs')
    (h : Accounted d f is es errs a) : Accounted d f is' es' errs' a := by
  refine ⟨fun i hi => ?_, fun e he => herr _ (h.2 e he)⟩
  have ⟨h1, h2, h3⟩ := h.1 i hi
  refine ⟨his _ h1, fun x hx => hes _ (h2 x hx), fun hd => ?_⟩
  have ⟨h4, h5⟩ := h3 hd
  exact ⟨fun s hs => his _ (h4 s hs), fun e he => herr _ (h5 e he)⟩

private theorem countP_mono' (p q : Nat → Bool) (h : ∀ x, q x = true → p x = true) (S : List Nat) :
    S.countP q ≤ S.countP p := by
  induction S with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons]
    have := h x
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

private theorem countP_lt' (p q : Nat → Bool) (h : ∀ x, q x = true → p x = true) (S : List Nat)
    (a : Nat) (ha : a ∈ S) (hp : p a = true) (hq : q a = false) :
    S.countP q + 1 ≤ S.countP p := by
  induction S with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.countP_cons]
    rcases List.mem_cons.1 ha with rfl | hmem
    · have := countP_mono' p q h xs
      simp only [hp, hq]
      simp
      omega
    · have := ih hmem
      have := h x
      cases hpx : p x <;> cases hqx : q x <;> simp_all <;> omega

private theorem countP_cons_lt (S visited : List Nat) (a : Nat) (ha : a ∈ S) (hv : a ∉ visited) :
    S.countP (fun x => decide (x ∉ a :: visited)) + 1 ≤ S.countP (fun x => decide (x ∉ visited)) := by
  refine countP_lt' _ _ ?_ S a ha (by simpa using hv) (by simp)
  intro x hx
  have hx' : x ∉ a :: visited := by simpa using hx
  simpa using fun h => hx' (List.mem_cons_of_mem _ h)

private abbrev Closure (d : Disassembler) (f : Nat → Except String Insn) (is : List Insn)
    (es : List (Nat × Nat)) (errs : List String) (visited work : List Nat) : Prop :=
  ∀ a ∈ visited, Accounted d f is es errs a ∧
    ∀ insn, Valid f a insn → ∀ b ∈ (Recursive.nextAddresses d insn), b ∈ visited ∨ b ∈ work

/-- A scan that visited all it had to: the visited addresses contain the initial ones and are closed
under successors, and each of them is accounted for in the output. -/
private def Finished (d : Disassembler) (f : Nat → Except String Insn) (work visited : List Nat)
    (out : List Insn × List (Nat × Nat) × List String) : Prop :=
  ∃ visited', (∀ a ∈ visited, a ∈ visited') ∧ (∀ a ∈ work, a ∈ visited') ∧
    Closure d f out.1 out.2.1 out.2.2 visited' []

private theorem finished_of_all {d : Disassembler} {f : Nat → Except String Insn}
    {work visited : List Nat} {is : List Insn} {es : List (Nat × Nat)} {errs : List String}
    (h : ∀ a ∈ work, a ∈ visited) (hinv : Closure d f is es errs visited work) :
    Finished d f work visited (is, es, errs) := by
  refine ⟨visited, fun _ hx => hx, h, fun a ha => ⟨(hinv a ha).1, fun i hi b hb => .inl ?_⟩⟩
  rcases (hinv a ha).2 i hi b hb with hx | hx
  · exact hx
  · exact h b hx

private theorem countP_pos_of_unvisited (S visited : List Nat) (a : Nat) (ha : a ∈ S)
    (hv : a ∉ visited) : 0 < S.countP (fun x => decide (x ∉ visited)) :=
  List.countP_pos_iff.2 ⟨a, ha, by simpa using hv⟩

private theorem decodeSlot_covers (d : Disassembler) (data : ByteArray)
    (f : Nat → Except String Insn) (hf : ∀ a r, Gives d data a r → r = f a) (slot : Nat)
    (is : List Insn) (errs : List String) (hv : ∀ x ∈ is, Valid f x.address x) :
    Holds (decodeSlot d data slot is errs) fun out =>
      (∀ x ∈ is, x ∈ out.1) ∧ (∀ e ∈ errs, e ∈ out.2) ∧ (∀ x ∈ out.1, Valid f x.address x) ∧
        SlotCovered f out.1 out.2 slot := by
  rw [decodeSlot_eq]
  refine Holds.bind (Holds.true _) fun r _ hr => ?_
  have hfa := hf slot r hr
  cases r with
  | error error =>
    refine Holds.pure ⟨fun _ h => h, fun e he => List.mem_append_left _ he, hv, ?_, ?_⟩
    · intro i hi
      have h := hi.1
      rw [← hfa] at h
      cases h
    · intro e he
      rw [← hfa] at he
      cases he
      simp
  | ok insn =>
    have huniq : ∀ i, f slot = .ok i → insn = i := by
      intro i hi
      rw [← hfa] at hi
      cases hi
      rfl
    simp only
    split
    · rename_i hbad
      refine Holds.pure ⟨fun _ h => h, fun e he => List.mem_append_left _ he, hv, ?_, ?_⟩
      · intro i hi
        have hii := huniq i hi.1
        subst hii
        simp [hi.2.1, hi.2.2] at hbad
      · intro e he
        rw [← hfa] at he
        cases he
    · rename_i hgood
      have hg : insn.address = slot ∧ ¬insn.size = 0 := by simpa using hgood
      have hvalid : Valid f slot insn := ⟨hfa.symm, hg.1, hg.2⟩
      refine Holds.pure ⟨fun x hx => mem_addInsn_of_mem _ _ _ hx, fun _ h => h, ?_, ?_, ?_⟩
      · intro x hx
        rcases mem_addInsn _ _ _ hx with h | rfl
        · exact hv x h
        · exact hg.1 ▸ hvalid
      · intro i hi
        have hii := huniq i hi.1
        subst hii
        refine self_mem_addInsn _ _ fun x hx he => ?_
        have hxv := hv x hx
        have h1 := hxv.1
        rw [he, hg.1, ← hfa] at h1
        cases h1
        rfl
      · intro e he
        rw [← hfa] at he
        cases he

private theorem scanAux_complete (d : Disassembler) (data : ByteArray)
    (f : Nat → Except String Insn) (hf : ∀ a r, Gives d data a r → r = f a) (S : List Nat)
    (hS : ∀ a ∈ S, ∀ insn, Valid f a insn → ∀ b ∈ (Recursive.nextAddresses d insn), b ∈ S ∨ S = [])
    (fuel : Nat) (work visited : List Nat) (is : List Insn) (es : List (Nat × Nat))
    (errs : List String) (hwork : S ≠ [] → ∀ a ∈ work, a ∈ S)
    (hvalid : ∀ x ∈ is, Valid f x.address x)
    (hinv : Closure d f is es errs visited work) :
    Holds (scanAux d data fuel work visited is es errs) fun out =>
      (S ≠ [] → S.countP (fun x => decide (x ∉ visited)) ≤ fuel → Finished d f work visited out) ∧
        (Recursive.outOfFuel ∈ out.2.2 ∨ Finished d f work visited out) := by
  induction fuel generalizing work visited is es errs with
  | zero =>
    by_cases hdone : ∀ a ∈ work, a ∈ visited
    · rw [scanAux_zero_done _ _ _ _ _ _ _ hdone]
      exact Holds.pure ⟨fun _ _ => finished_of_all hdone hinv, .inr (finished_of_all hdone hinv)⟩
    · rw [scanAux_zero_left _ _ _ _ _ _ _ hdone]
      refine Holds.pure ⟨fun hne hc => ?_, .inl (by simp)⟩
      refine absurd hdone fun hn => hn ?_
      intro a ha
      refine Decidable.byContradiction fun hv => ?_
      have := countP_pos_of_unvisited S visited a (hwork hne a ha) hv
      omega
  | succ fuel ih =>
    cases hd : work.dropWhile (fun x => decide (x ∈ visited)) with
    | nil =>
      have hdone := dropWhile_nil_all _ _ hd
      rw [scanAux_succ_nil _ _ _ _ _ _ _ _ hd]
      exact Holds.pure ⟨fun _ _ => finished_of_all hdone hinv, .inr (finished_of_all hdone hinv)⟩
    | cons a rest =>
      have ⟨hnew, hmem, hsub, hcover⟩ := dropWhile_cons_spec _ _ _ _ hd
      have hrestS : S ≠ [] → ∀ x ∈ rest, x ∈ S := fun hne x hx => hwork hne x (hsub x hx)
      have hcount : S ≠ [] → S.countP (fun x => decide (x ∉ a :: visited)) + 1 ≤
          S.countP (fun x => decide (x ∉ visited)) :=
        fun hne => countP_cons_lt S visited a (hwork hne a hmem) hnew
      -- how the conclusion for the rest of the work gives the conclusion for this step
      have lift : ∀ rest' (out : List Insn × List (Nat × Nat) × List String),
          (∀ x ∈ rest, x ∈ rest') →
          ((S ≠ [] → S.countP (fun x => decide (x ∉ a :: visited)) ≤ fuel →
              Finished d f rest' (a :: visited) out) ∧
            (Recursive.outOfFuel ∈ out.2.2 ∨ Finished d f rest' (a :: visited) out)) →
          (S ≠ [] → S.countP (fun x => decide (x ∉ visited)) ≤ fuel + 1 →
              Finished d f work visited out) ∧
            (Recursive.outOfFuel ∈ out.2.2 ∨ Finished d f work visited out) := by
        intro rest' out hrest ⟨h1, h2⟩
        have conv : Finished d f rest' (a :: visited) out → Finished d f work visited out := by
          rintro ⟨v, hv, hw, hc⟩
          refine ⟨v, fun x hx => hv x (List.mem_cons_of_mem _ hx), ?_, hc⟩
          intro x hx
          rcases hcover x hx with h | rfl | h
          · exact hv x (List.mem_cons_of_mem _ h)
          · exact hv x (by simp)
          · exact hw x (hrest x h)
        refine ⟨fun hne hc => conv (h1 hne ?_), h2.imp id conv⟩
        have := hcount hne
        omega
      have keep : ∀ {is' : List Insn} {es' : List (Nat × Nat)} {errs' : List String}
          {rest' : List Nat},
          (∀ x ∈ is, x ∈ is') → (∀ x ∈ es, x ∈ es') → (∀ e ∈ errs, e ∈ errs') →
          (∀ x ∈ rest, x ∈ rest') → ∀ x ∈ visited, Accounted d f is' es' errs' x ∧
            ∀ i, Valid f x i → ∀ b ∈ (Recursive.nextAddresses d i), b ∈ a :: visited ∨ b ∈ rest' := by
        intro is' es' errs' rest' h1 h1' h2 h3 x hx
        refine ⟨(hinv x hx).1.mono h1 h1' h2, fun i hi b hb => ?_⟩
        rcases (hinv x hx).2 i hi b hb with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · rcases hcover b h with h' | rfl | h'
          · exact .inl (List.mem_cons_of_mem _ h')
          · exact .inl (by simp)
          · exact .inr (h3 b h')
      rw [scanAux_succ_cons _ _ _ _ _ _ _ _ _ _ hd]
      have skip : ∀ errs', (∀ e ∈ errs, e ∈ errs') → (∀ i, Valid f a i → False) →
          (∀ e, f a = .error e → e ∈ errs') →
          Holds (scanAux d data fuel rest (a :: visited) is es errs') fun out =>
            (S ≠ [] → S.countP (fun x => decide (x ∉ visited)) ≤ fuel + 1 →
                Finished d f work visited out) ∧
              (Recursive.outOfFuel ∈ out.2.2 ∨ Finished d f work visited out) := by
        intro errs' hsub' hnv herr s out s' he
        refine lift rest out (fun _ h => h)
          (ih rest (a :: visited) is es errs' hrestS hvalid ?_ s out s' he)
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact ⟨⟨fun i hi => (hnv i hi).elim, herr⟩, fun i hi => (hnv i hi).elim⟩
        · exact keep (fun _ h => h) (fun _ h => h) hsub' (fun _ h => h) x hx'
      refine Holds.bind (Holds.true _) fun r _ hr => ?_
      have hfa := hf a r hr
      cases r with
      | error error =>
        refine skip _ (fun e he => List.mem_append_left _ he) ?_ ?_
        · intro i hi
          have h := hi.1
          rw [← hfa] at h
          cases h
        · intro e he
          rw [← hfa] at he
          cases he
          simp
      | ok insn =>
        have huniq : ∀ i, f a = .ok i → insn = i := by
          intro i hi
          rw [← hfa] at hi
          cases hi
          rfl
        simp only
        split
        · rename_i hbad
          refine skip _ (fun e he => List.mem_append_left _ he) ?_ ?_
          · intro i hi
            have hii := huniq i hi.1
            subst hii
            simp [hi.2.1, hi.2.2] at hbad
          · intro e he
            rw [← hfa] at he
            cases he
        · rename_i hgood
          have hg : insn.address = a ∧ ¬insn.size = 0 := by simpa using hgood
          have hvi : Valid f a insn := ⟨hfa.symm, hg.1, hg.2⟩
          have hself : insn ∈ Recursive.addInsn insn is := by
            refine self_mem_addInsn _ _ fun x hx he => ?_
            have h1 := (hvalid x hx).1
            rw [he, hg.1, ← hfa] at h1
            cases h1
            rfl
          have hvalid' : ∀ x ∈ Recursive.addInsn insn is, Valid f x.address x := by
            intro x hx
            rcases mem_addInsn _ _ _ hx with h | rfl
            · exact hvalid x h
            · exact hg.1 ▸ hvi
          let es' := es ++ Recursive.flowEdges d insn
          have hwork' : S ≠ [] → ∀ x ∈ (Recursive.nextAddresses d insn) ++ rest, x ∈ S := by
            intro hne x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact (hS a (hwork hne a hmem) insn hvi x hx).resolve_right hne
            · exact hrestS hne x hx
          -- the closure after this step, whatever the slot added
          have closure : ∀ (is' : List Insn) (errs' : List String),
              (∀ x ∈ Recursive.addInsn insn is, x ∈ is') → (∀ e ∈ errs, e ∈ errs') →
              (d.hasDelaySlot insn = true → SlotCovered f is' errs' insn.next) →
              Closure d f is' es' errs' (a :: visited) ((Recursive.nextAddresses d insn) ++ rest) := by
            intro is' errs' h1 h2 h3 x hx
            rcases List.mem_cons.1 hx with rfl | hx'
            · refine ⟨⟨?_, ?_⟩, ?_⟩
              · intro i hi
                have hii := huniq i hi.1
                subst hii
                exact ⟨h1 _ hself, fun e he => List.mem_append_right _ he, h3⟩
              · intro e he
                rw [← hfa] at he
                cases he
              · intro i hi b hb
                have hii := huniq i hi.1
                subst hii
                exact .inr (List.mem_append_left _ hb)
            · exact keep (fun y hy => h1 y (mem_addInsn_of_mem _ _ _ hy))
                (fun _ h => List.mem_append_left _ h) h2
                (fun _ h => List.mem_append_right _ h) x hx'
          split
          · refine Holds.bind (decodeSlot_covers d data f hf insn.next _ errs hvalid') fun out hout _ => ?_
            obtain ⟨h1, h2, h3, h4⟩ := hout
            intro s result s' he
            exact lift ((Recursive.nextAddresses d insn) ++ rest) result (fun _ h => List.mem_append_right _ h)
              (ih ((Recursive.nextAddresses d insn) ++ rest) (a :: visited) out.1 es' out.2 hwork' h3
                (closure _ _ h1 h2 fun _ => h4) s result s' he)
          · rename_i hdelay
            intro s result s' he
            exact lift ((Recursive.nextAddresses d insn) ++ rest) result (fun _ h => List.mem_append_right _ h)
              (ih ((Recursive.nextAddresses d insn) ++ rest) (a :: visited) _ es' errs hwork' hvalid'
                (closure _ _ (fun _ h => h) (fun _ h => h) fun h => absurd h hdelay) s result s' he)

private theorem finished_reach {d : Disassembler} {f : Nat → Except String Insn} {roots : List Nat}
    {is : List Insn} {es : List (Nat × Nat)} {errs : List String} {v : List Nat}
    (hw : ∀ a ∈ roots, a ∈ v) (hc : Closure d f is es errs v []) (a : Nat)
    (ha : Reach d f roots a) : a ∈ v := by
  induction ha with
  | root hr => exact hw _ hr
  | step _ hv hb ih =>
    rcases (hc _ ih).2 _ hv _ hb with h | h
    · exact h
    · simp at h

/-- Nothing is lost silently. For a deterministic decoder, a finished scan accounts for every
address reachable from the roots, with its edges and delay slot; the only other outcome is the
out-of-fuel error. -/
theorem scan_no_silent_loss (d : Disassembler) (data : ByteArray) (bytes entry : Nat) (roots : List Nat)
    (f : Nat → Except String Insn) (hf : ∀ a r, Gives d data a r → r = f a) :
    Holds (Recursive.scanRoots d data bytes entry roots) fun result =>
      Recursive.outOfFuel ∈ result.errors ∨
        ∀ a, Reach d f roots a → Accounted d f result.instructions result.edges result.errors a := by
  rw [scan_eq]
  refine Holds.bind (scanAux_complete d data f hf [] (by simp) _ roots [] [] [] []
    (by simp) (by simp) (fun _ h => by cases h)) ?_
  rintro ⟨is, es, errs⟩ ⟨_, h⟩ _
  refine Holds.pure ?_
  rcases h with h | ⟨v, _, hw, hc⟩
  · exact .inl h
  · exact .inr fun a ha => (hc a (finished_reach hw hc a ha)).1

private theorem reach_nil {d : Disassembler} {f : Nat → Except String Insn} {a : Nat} (h : Reach d f [] a) : False := by
  induction h with
  | root hr => cases hr
  | step _ _ _ ih => exact ih

/-- A scan of the addresses in a list `S` is complete if `S` fits its fuel. -/
private theorem scanAux_complete_of_closed (d : Disassembler) (data : ByteArray) (fuel : Nat) (roots : List Nat)
    (f : Nat → Except String Insn) (hf : ∀ a r, Gives d data a r → r = f a) (S : List Nat)
    (hroots : ∀ r ∈ roots, r ∈ S)
    (hS : ∀ a ∈ S, ∀ insn, Valid f a insn → ∀ b ∈ (Recursive.nextAddresses d insn), b ∈ S)
    (hfuel : S.length ≤ fuel) :
    Holds (scanAux d data fuel roots [] [] [] []) fun out =>
      ∀ a, Reach d f roots a → Accounted d f out.1 out.2.1 out.2.2 a := by
  by_cases hne : S = []
  · have hr : roots = [] := List.eq_nil_iff_forall_not_mem.2 fun r hmem => by
      simpa [hne] using hroots r hmem
    subst hr
    exact fun _ _ _ _ a ha => (reach_nil (a := a) ha).elim
  · have hcount : S.countP (fun x => decide (x ∉ ([] : List Nat))) ≤ S.length := List.countP_le_length
    intro st out st' he a ha
    have ⟨h, _⟩ := scanAux_complete d data f hf S (fun a ha i hi b hb => .inl (hS a ha i hi b hb))
      fuel roots [] [] [] [] (fun _ a ha => hroots a ha) (by simp) (fun _ h => by cases h) st out st' he
    obtain ⟨v, _, hw, hc⟩ := h hne (by omega)
    exact (hc a (finished_reach hw hc a ha)).1

/-- Completeness. For a deterministic decoder, if the reachable addresses lie in a list `S` that
fits the fuel of `4 * bytes + roots.length + 1`, each reachable address is accounted for. Addresses that are
reached again cost nothing. -/
theorem scan_complete (d : Disassembler) (data : ByteArray) (bytes entry : Nat) (roots : List Nat)
    (f : Nat → Except String Insn) (hf : ∀ a r, Gives d data a r → r = f a) (S : List Nat)
    (hroots : ∀ r ∈ roots, r ∈ S)
    (hS : ∀ a ∈ S, ∀ insn, Valid f a insn → ∀ b ∈ (Recursive.nextAddresses d insn), b ∈ S)
    (hfuel : S.length ≤ 4 * bytes + roots.length + 1) :
    Holds (Recursive.scanRoots d data bytes entry roots) fun result =>
      ∀ a, Reach d f roots a → Accounted d f result.instructions result.edges result.errors a := by
  rw [scan_eq]
  refine Holds.bind (scanAux_complete_of_closed d data _ roots f hf S hroots hS hfuel) ?_
  rintro ⟨is, es, errs⟩ h _
  exact Holds.pure h

/-- The addresses of `R` and all they go on to, with the roots, are closed if nothing else decodes, and at most
four for each one of `R`. -/
private theorem closed_of_range (d : Disassembler) (roots R : List Nat) (f : Nat → Except String Insn)
    (hrange : ∀ a insn, Valid f a insn → a ∈ R) :
    ∃ S : List Nat, (∀ r ∈ roots, r ∈ S) ∧
      (∀ a ∈ S, ∀ insn, Valid f a insn → ∀ b ∈ (Recursive.nextAddresses d insn), b ∈ S) ∧
      S.length ≤ 4 * R.length + roots.length := by
  let successorsOf (a : Nat) : List Nat :=
    match f a with
    | .ok insn => (Recursive.nextAddresses d insn)
    | .error _ => []
  have hsucc : ∀ a, (successorsOf a).length ≤ 3 := by
    intro a
    show (match f a with
      | .ok insn => (Recursive.nextAddresses d insn)
      | .error _ => []).length ≤ 3
    split
    · exact nextAddresses_length_le_three d _
    · simp
  have hflat : ∀ l : List Nat, (l.flatMap successorsOf).length ≤ 3 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      have := hsucc x
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  refine ⟨roots ++ (R ++ R.flatMap successorsOf), fun r hr => List.mem_append_left _ hr, ?_, ?_⟩
  · intro a _ insn hv b hb
    refine List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨a, hrange a insn hv, ?_⟩))
    show b ∈ (match f a with
      | .ok insn => (Recursive.nextAddresses d insn)
      | .error _ => [])
    rw [hv.1]
    exact hb
  · have := hflat R
    simp only [List.length_append]
    omega

/-- The built-in fuel always suffices when the decoder only accepts addresses of a list as long as the
number of bytes, which is what the real decoders do on loaded regions: the scan is then complete,
without any assumption about how the code branches. -/
theorem scan_complete_of_range (d : Disassembler) (data : ByteArray) (bytes entry : Nat) (roots R : List Nat)
    (f : Nat → Except String Insn) (hf : ∀ a r, Gives d data a r → r = f a)
    (hR : R.length ≤ bytes) (hrange : ∀ a insn, Valid f a insn → a ∈ R) :
    Holds (Recursive.scanRoots d data bytes entry roots) fun result =>
      ∀ a, Reach d f roots a → Accounted d f result.instructions result.edges result.errors a := by
  have ⟨S, h1, h2, h3⟩ := closed_of_range d roots R f hrange
  exact scan_complete d data bytes entry roots f hf S h1 h2 (by omega)

/-- The scan of one region, whose addresses are `data.size` many. -/
theorem scan_complete_of_in_range (d : Disassembler) (data : ByteArray) (entry base : Nat)
    (f : Nat → Except String Insn) (hf : ∀ a r, Gives d data a r → r = f a)
    (hrange : ∀ a insn, Valid f a insn → base ≤ a ∧ a < base + data.size) :
    Holds (Recursive.scan d data entry) fun result =>
      ∀ a, Reach d f [entry] a → Accounted d f result.instructions result.edges result.errors a := by
  refine scan_complete_of_range d data data.size entry [entry] ((List.range data.size).map (base + ·)) f hf (by simp) ?_
  intro a insn hv
  have ⟨h1, h2⟩ := hrange a insn hv
  exact List.mem_map.2 ⟨a - base, List.mem_range.2 (by omega), by omega⟩

/-- The delay slot of each reachable delayed branch is covered, by the scan of the slot or, for the
branches that can continue past the slot, by falling through to it. -/
theorem scan_covers_delay_slots (d : Disassembler) (data : ByteArray) (entry base : Nat)
    (f : Nat → Except String Insn) (hf : ∀ a r, Gives d data a r → r = f a)
    (hrange : ∀ a insn, Valid f a insn → base ≤ a ∧ a < base + data.size) :
    Holds (Recursive.scan d data entry) fun result =>
      ∀ a insn, Reach d f [entry] a → Valid f a insn →
        (d.hasDelaySlot insn = true ∨ insn.fallsThrough = true) →
        SlotCovered f result.instructions result.errors insn.next := by
  intro s result s' he a insn ha hv hor
  have hall := scan_complete_of_in_range d data entry base f hf hrange s result s' he
  by_cases hd : d.hasDelaySlot insn = true
  · exact ((hall a ha).1 insn hv).2.2 hd
  · have hft := hor.resolve_left hd
    have hnext := hall _ (Reach.step ha hv (next_mem_nextAddresses d insn (by simpa using hd) hft))
    exact ⟨fun i hi => ((hnext).1 i hi).1, hnext.2⟩

/-! ### The scan with a linear sweep -/

theorem Holds.and {α} {m : IO α} {P Q : α → Prop} (hp : Holds m P) (hq : Holds m Q) : Holds m fun a => P a ∧ Q a :=
  fun s r s' he => ⟨hp s r s' he, hq s r s' he⟩

/-- What holds of the output of the specification holds of the output of the fast scan. -/
private theorem fast_holds {d : Disassembler} {data : ByteArray} {fuel : Nat} {work : List Nat}
    {s : Recursive.ScanState} {v is es errs} (h : Represents s v is es errs)
    {Q : List Insn × List (Nat × Nat) × List String → Prop} (hq : Holds (scanAux d data fuel work v is es errs) Q) :
    Holds (fastScanAux d data fuel work s) fun out => Q (project out) := by
  intro st r st' he
  have : (fastScanAux d data fuel work s >>= fun out => pure (project out)) st = EST.Out.ok (project r) st' := by
    rw [bind_ok he]
    rfl
  rw [fast_scan d data fuel work s v is es errs h] at this
  exact hq st _ st' this

/-- A state that represents its own lists. -/
private def SelfRepresents (s : Recursive.ScanState) : Prop :=
  ∃ v, Represents s v s.instructions.toList s.edges.toList s.errors.toList

private theorem SelfRepresents.of {s : Recursive.ScanState} {v is es errs} (h : Represents s v is es errs) : SelfRepresents s := by
  refine ⟨v, ?_⟩
  rw [h.instructions, h.edges, h.errors]
  exact h

private theorem fast_slot_consistent (d : Disassembler) (data : ByteArray) (slot : Nat) (s v is es errs)
    (h : Represents s v is es errs) :
    Holds (fastDecodeSlot d data slot s) fun out => ∃ is' errs', Represents out v is' es errs' := by
  dsimp only [fastDecodeSlot]
  prw Bap.Disasm.Recursive Bap.Disasm.Recursive.decodeSlot
  refine Holds.bind (Holds.true _) fun r _ _ => ?_
  cases r with
  | error e => exact Holds.pure ⟨_, _, h.error e⟩
  | ok insn =>
    simp only
    split
    · exact Holds.pure ⟨_, _, h.error _⟩
    · exact Holds.pure ⟨_, _, h.add insn⟩

private theorem fast_scan_consistent (d : Disassembler) (data : ByteArray) (fuel : Nat) (work : List Nat)
    (s v is es errs) (h : Represents s v is es errs) :
    Holds (fastScanAux d data fuel work s) SelfRepresents := by
  induction fuel generalizing work s v is es errs with
  | zero =>
    dsimp only [fastScanAux]
    prw Bap.Disasm.Recursive Bap.Disasm.Recursive.scanAux
    dsimp only
    split
    · exact Holds.pure (SelfRepresents.of h)
    · exact Holds.pure (SelfRepresents.of (h.error _))
  | succ fuel ih =>
    dsimp only [fastScanAux] at ih ⊢
    prw Bap.Disasm.Recursive Bap.Disasm.Recursive.scanAux
    dsimp only
    split
    · exact Holds.pure (SelfRepresents.of h)
    · rename_i address rest _
      refine Holds.bind (Holds.true _) fun r _ _ => ?_
      cases r with
      | error e => exact ih _ _ _ _ _ _ ((h.visit address).error e)
      | ok insn =>
        simp only
        split
        · exact ih _ _ _ _ _ _ ((h.visit address).error _)
        · have hadded := (h.visit address).add insn
          have hstate : Represents
              { (s.visit address).add insn with edges := ((s.visit address).add insn).edges ++ (Recursive.flowEdges d insn).toArray }
              (address :: v) (Recursive.addInsn insn is) (es ++ Recursive.flowEdges d insn) errs :=
            ⟨hadded.visited_iff, hadded.addresses_iff, hadded.instructions, by simp [hadded.edges], hadded.errors⟩
          split
          · refine Holds.bind (fast_slot_consistent d data insn.next _ _ _ _ _ hstate) fun out ho _ => ?_
            obtain ⟨is', errs', hs⟩ := ho
            exact ih _ _ _ _ _ _ hs
          · exact ih _ _ _ _ _ _ hstate

/-- A scan keeps what it found. -/
private theorem scanAux_mono (d : Disassembler) (data : ByteArray) (fuel : Nat) (work visited : List Nat)
    (is : List Insn) (es : List (Nat × Nat)) (errs : List String) :
    Holds (scanAux d data fuel work visited is es errs) fun out => (∀ x ∈ is, x ∈ out.1) ∧ ∀ x ∈ es, x ∈ out.2.1 := by
  induction fuel generalizing work visited is es errs with
  | zero =>
    by_cases hdone : ∀ a ∈ work, a ∈ visited
    · rw [scanAux_zero_done _ _ _ _ _ _ _ hdone]
      exact Holds.pure ⟨fun _ h => h, fun _ h => h⟩
    · rw [scanAux_zero_left _ _ _ _ _ _ _ hdone]
      exact Holds.pure ⟨fun _ h => h, fun _ h => h⟩
  | succ fuel ih =>
    cases hd : work.dropWhile (fun x => decide (x ∈ visited)) with
    | nil =>
      rw [scanAux_succ_nil _ _ _ _ _ _ _ _ hd]
      exact Holds.pure ⟨fun _ h => h, fun _ h => h⟩
    | cons address rest =>
      rw [scanAux_succ_cons _ _ _ _ _ _ _ _ _ _ hd]
      refine Holds.bind (Holds.true _) fun r _ _ => ?_
      cases r with
      | error error => exact ih _ _ _ _ _
      | ok insn =>
        simp only
        split
        · exact ih _ _ _ _ _
        · split
          · refine Holds.bind (decodeSlot_spec d data insn.next _ errs) fun out hout _ => ?_
            intro st result st' he
            have ⟨h1, h2⟩ := ih _ _ _ _ _ st result st' he
            exact ⟨fun x hx => h1 x (hout.1 x (mem_addInsn_of_mem _ _ _ hx)),
              fun x hx => h2 x (List.mem_append_left _ hx)⟩
          · intro st result st' he
            have ⟨h1, h2⟩ := ih _ _ _ _ _ st result st' he
            exact ⟨fun x hx => h1 x (mem_addInsn_of_mem _ _ _ hx), fun x hx => h2 x (List.mem_append_left _ hx)⟩

/-- A scan from one more root keeps what holds of a finished scan. -/
private theorem scanAux_more (d : Disassembler) (data : ByteArray) (roots : List Nat) (a fuel : Nat) (visited : List Nat)
    (is : List Insn) (es : List (Nat × Nat)) (errs : List String) (h : ScanOk d data roots is es) :
    Holds (scanAux d data fuel [a] visited is es errs) fun out => ScanOk d data (a :: roots) out.1 out.2.1 := by
  obtain ⟨hn, hd, he, calls, hc, hr⟩ := h
  have hinv : ScanInv d data (a :: roots) [a] is es calls :=
    ⟨hn, hd, he, hc, fun x hx => (hr x hx).mono_roots fun _ hm => List.mem_cons_of_mem _ hm, fun x hx => by
      rw [List.mem_singleton.1 hx]
      exact .root List.mem_cons_self⟩
  intro st out st' hout
  exact (scanAux_spec d data (a :: roots) fuel [a] visited is es calls errs hinv st out st' hout).1

/-- What holds along a sweep from a state `base`, from the roots of a scan and some more. -/
private structure SweepInv (d : Disassembler) (data : ByteArray) (roots : List Nat) (base s : Recursive.ScanState) : Prop where
  consistent : SelfRepresents s
  ok : ∃ extra, ScanOk d data (extra ++ roots) s.instructions.toList s.edges.toList
  keeps : ∀ x ∈ base.instructions.toList, x ∈ s.instructions.toList
  keepsEdges : ∀ x ∈ base.edges.toList, x ∈ s.edges.toList

private theorem fast_sweep_step (d : Disassembler) (data : ByteArray) (roots : List Nat) (fuel a : Nat)
    (base s : Recursive.ScanState) (h : SweepInv d data roots base s) :
    Holds (fastScanAux d data fuel [a] s) (SweepInv d data roots base) := by
  obtain ⟨⟨v, hrep⟩, ⟨extra, hok⟩, hk, hke⟩ := h
  have h1 := fast_scan_consistent d data fuel [a] s v _ _ _ hrep
  have h2 := fast_holds hrep (scanAux_more d data (extra ++ roots) a fuel v _ _ s.errors.toList hok)
  have h3 := fast_holds hrep (scanAux_mono d data fuel [a] v s.instructions.toList s.edges.toList s.errors.toList)
  intro st out st' he
  exact ⟨h1 st out st' he, ⟨a :: extra, h2 st out st' he⟩,
    fun x hx => (h3 st out st' he).1 x (hk x hx), fun x hx => (h3 st out st' he).2 x (hke x hx)⟩

private theorem fast_sweep_range (d : Disassembler) (data : ByteArray) (roots : List Nat) (fuel alignment limit steps address : Nat)
    (walk : Recursive.Walk) (base s : Recursive.ScanState) (h : SweepInv d data roots base s) :
    Holds (fastSweepRange d data fuel alignment limit steps address walk s) fun out => SweepInv d data roots base out.2 := by
  induction steps generalizing address walk s with
  | zero =>
    dsimp only [fastSweepRange]
    prw Bap.Disasm.Recursive Bap.Disasm.Recursive.sweepRange
    dsimp only
    exact Holds.pure h
  | succ steps ih =>
    dsimp only [fastSweepRange] at ih ⊢
    prw Bap.Disasm.Recursive Bap.Disasm.Recursive.sweepRange
    dsimp only
    split
    · exact Holds.pure h
    · split
      · exact ih _ _ _ h
      · split
        · exact ih _ _ _ h
        · exact Holds.bind (fast_sweep_step d data roots fuel address base s h) fun out ho _ => ih _ _ _ ho

private theorem fast_sweep_ranges (d : Disassembler) (data : ByteArray) (roots : List Nat) (fuel alignment : Nat)
    (ranges : List (Nat × Nat)) (walk : Recursive.Walk) (base s : Recursive.ScanState) (h : SweepInv d data roots base s) :
    Holds (ranges.foldlM (init := (walk, s)) fun (state : Recursive.Walk × Recursive.ScanState) range =>
        fastSweepRange d data fuel alignment range.2 (2 * (range.2 - range.1) + 1) range.1 state.1 state.2)
      fun out => SweepInv d data roots base out.2 := by
  induction ranges generalizing walk s with
  | nil => exact Holds.pure h
  | cons range rest ih =>
    simp only [List.foldlM_cons]
    exact Holds.bind (fast_sweep_range d data roots fuel alignment _ _ _ walk base s h) fun out ho _ => ih out.1 out.2 ho

private theorem scanRegions_stage (d : Disassembler) (bytes : Nat) (roots : List Nat) :
    Holds (fastScanAux d ByteArray.empty (4 * bytes + roots.length + 1) roots {})
      fun s => SweepInv d ByteArray.empty roots s s := by
  have hempty : Represents {} [] [] [] [] := by
    refine ⟨?_, ?_, rfl, rfl, rfl⟩ <;> simp
  have h1 := fast_scan_consistent d ByteArray.empty (4 * bytes + roots.length + 1) roots _ _ _ _ _ hempty
  have h2 := fast_holds hempty (scanAux_spec d ByteArray.empty roots (4 * bytes + roots.length + 1) roots [] [] [] [] []
    { nodup := by simp, decoded := by simp, edges := by simp, callsOk := by simp, reach := by simp
      reachWork := fun _ ha => .root ha })
  intro st out st' he
  exact ⟨h1 st out st' he, ⟨[], (h2 st out st' he).1⟩, fun _ h => h, fun _ h => h⟩

private theorem scanRegions_unfold (d : Disassembler) (bytes entry : Nat) (roots : List Nat) (alignment : Nat)
    (ranges : List (Nat × Nat)) :
    Recursive.scanRegions d bytes entry roots alignment ranges =
      (fastScanAux d ByteArray.empty (4 * bytes + roots.length + 1) roots {} >>= fun first =>
        (ranges.foldlM (init := (({} : Recursive.Walk), first)) fun (state : Recursive.Walk × Recursive.ScanState) range =>
          fastSweepRange d ByteArray.empty (4 * bytes + roots.length + 1) alignment range.2 (2 * (range.2 - range.1) + 1)
            range.1 state.1 state.2) >>= fun out =>
        pure { entry := entry, instructions := out.2.instructions.toList, edges := out.2.edges.toList,
               errors := first.errors.toList }) := rfl

/-- Soundness of the scan with a linear sweep. What holds of a scan holds of it, from its roots and the addresses the
sweep went on from, and it has no other errors than the ones of the scan from the roots. -/
theorem scanRegions_sound (d : Disassembler) (bytes entry : Nat) (roots : List Nat) (alignment : Nat)
    (ranges : List (Nat × Nat)) :
    Holds (Recursive.scanRegions d bytes entry roots alignment ranges) fun result =>
      result.entry = entry ∧ ∃ extra, ScanOk d ByteArray.empty (extra ++ roots) result.instructions result.edges := by
  rw [scanRegions_unfold]
  refine Holds.bind (scanRegions_stage d bytes roots) fun first hfirst _ => ?_
  refine Holds.bind (fast_sweep_ranges d _ roots _ alignment ranges {} first first hfirst) fun out ho _ => ?_
  exact Holds.pure ⟨rfl, ho.ok⟩

/-- Completeness of the scan with a linear sweep: the sweep adds to the scan from the roots and takes nothing back. -/
theorem scanRegions_complete (d : Disassembler) (bytes entry : Nat) (roots R : List Nat) (alignment : Nat)
    (ranges : List (Nat × Nat)) (f : Nat → Except String Insn) (hf : ∀ a r, Gives d ByteArray.empty a r → r = f a)
    (hR : R.length ≤ bytes) (hrange : ∀ a insn, Valid f a insn → a ∈ R) :
    Holds (Recursive.scanRegions d bytes entry roots alignment ranges) fun result =>
      ∀ a, Reach d f roots a → Accounted d f result.instructions result.edges result.errors a := by
  rw [scanRegions_unfold]
  have ⟨S, h1, h2, h3⟩ := closed_of_range d roots R f hrange
  have hempty : Represents {} [] [] [] [] := by
    refine ⟨?_, ?_, rfl, rfl, rfl⟩ <;> simp
  have hc := fast_holds hempty (scanAux_complete_of_closed d ByteArray.empty (4 * bytes + roots.length + 1) roots f hf S h1 h2
    (by omega))
  refine Holds.bind (Holds.and (scanRegions_stage d bytes roots) hc) fun first hfirst _ => ?_
  refine Holds.bind (fast_sweep_ranges d _ roots _ alignment ranges {} first first hfirst.1) fun out ho _ => ?_
  exact Holds.pure fun a ha => Accounted.mono ho.keeps ho.keepsEdges (fun _ h => h) (hfirst.2 a ha)

/-- The addresses the decoder of several regions has an instruction at are in the regions. -/
theorem ofRegions_in_regions (base : Disassembler) (regions : List (Bap.Image.MemRegion × Disassembler)) (data : ByteArray)
    (address : Nat) (insn : Insn) (h : Gives (Disassembler.ofRegions base regions) data address (.ok insn)) :
    ∃ entry ∈ regions, entry.1.contains address = true := by
  obtain ⟨st, st', he⟩ := h
  simp only [Disassembler.ofRegions] at he
  cases hfind : regions.find? (·.1.contains address) with
  | none =>
    rw [hfind] at he
    cases he
  | some entry =>
    exact ⟨entry, List.mem_of_find?_eq_some hfind, by simpa using List.find?_some hfind⟩

/-- The addresses in regions, which are as many as their bytes. -/
private theorem regions_addresses (regions : List (Bap.Image.MemRegion × Disassembler)) :
    ∃ R : List Nat, R.length = (regions.map (·.1.size)).sum ∧
      ∀ a, (∃ entry ∈ regions, entry.1.contains a = true) → a ∈ R := by
  induction regions with
  | nil => exact ⟨[], rfl, fun _ h => by simp at h⟩
  | cons head tail ih =>
    obtain ⟨R, h1, h2⟩ := ih
    refine ⟨(List.range head.1.size).map (head.1.addr + ·) ++ R, by simp [h1], ?_⟩
    rintro a ⟨entry, hm, hc⟩
    rcases List.mem_cons.1 hm with he | hm
    · subst he
      simp only [Bap.Image.MemRegion.contains, Bap.Image.MemRegion.maxAddr, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hl, hu⟩ := hc
      have hlt : a - entry.1.addr < entry.1.size := by
        simp only [Bap.Image.MemRegion.size] at hu ⊢
        have := of_decide_eq_true hu
        omega
      refine List.mem_append_left _ (List.mem_map.2 ⟨a - entry.1.addr, List.mem_range.2 hlt, ?_⟩)
      show entry.1.addr + (a - entry.1.addr) = a
      omega
    · exact List.mem_append_right _ (h2 a ⟨entry, hm, hc⟩)

/-- The scan of several regions is complete, however the code branches: each address reached from the roots is
accounted for, since their bytes give enough fuel. -/
theorem scanRegions_complete_of_regions (base : Disassembler) (regions : List (Bap.Image.MemRegion × Disassembler))
    (entry : Nat) (roots : List Nat) (alignment : Nat) (ranges : List (Nat × Nat)) (f : Nat → Except String Insn)
    (hf : ∀ a r, Gives (Disassembler.ofRegions base regions) ByteArray.empty a r → r = f a)
    (hrange : ∀ a insn, Valid f a insn → ∃ entry ∈ regions, entry.1.contains a = true) :
    Holds (Recursive.scanRegions (Disassembler.ofRegions base regions) (regions.map (·.1.size)).sum entry roots alignment ranges)
      fun result => ∀ a, Reach (Disassembler.ofRegions base regions) f roots a →
        Accounted (Disassembler.ofRegions base regions) f result.instructions result.edges result.errors a := by
  have ⟨R, h1, h2⟩ := regions_addresses regions
  exact scanRegions_complete _ _ entry roots R alignment ranges f hf (Nat.le_of_eq h1) fun a insn hv => h2 a (hrange a insn hv)

end Bap.Proofs.Disasm
