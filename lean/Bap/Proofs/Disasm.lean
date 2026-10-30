import Lean.Elab.Tactic.Basic
import Bap.Disasm.Linear
import Bap.Disasm.Recursive

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

private abbrev insertInsn : Insn → List Insn → List Insn :=
  priv% Bap.Disasm.Basic Bap.Disasm.insertInsn

private abbrev sweepAux : Disassembler → ByteArray → Nat → Nat → Nat → List Insn → List String →
    IO (List Insn × List String) :=
  priv% Bap.Disasm.Linear Bap.Disasm.Linear.sweepAux

private abbrev scanAux : Disassembler → ByteArray → Nat → List Nat → List Nat → List Insn →
    List (Nat × Nat) → List String → IO (List Insn × List (Nat × Nat) × List String) :=
  priv% Bap.Disasm.Recursive Bap.Disasm.Recursive.scanAux

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

theorem sortedInstructions_perm (disasm : Bap.Disasm.Disasm) :
    (sortedInstructions disasm).Perm disasm.instructions := by
  have := foldl_insert_perm disasm.instructions []
  rw [List.append_nil] at this
  exact this

theorem sortedInstructions_sorted (disasm : Bap.Disasm.Disasm) :
    (sortedInstructions disasm).Pairwise fun a b => a.address ≤ b.address :=
  foldl_insert_sorted _ _ List.Pairwise.nil

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

theorem blocks_eq (disasm : Bap.Disasm.Disasm) :
    disasm.blocks = Bap.Disasm.Disasm.blocks.build (leaders disasm) [] [] (sortedInstructions disasm) :=
  rfl

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
    let out := Bap.Disasm.Disasm.blocks.build ls current blocks rest
    out.flatMap Block.instructions = blocks.flatMap Block.instructions ++ current ++ rest ∧
      (∀ b ∈ out, BlockOk ls b) ∧ ∀ b ∈ out.tail, b.start ∈ ls := by
  induction rest generalizing current blocks with
  | nil =>
    cases current with
    | nil =>
      simp only [Bap.Disasm.Disasm.blocks.build]
      exact ⟨by simp, hb, hl⟩
    | cons head tail =>
      simp only [Bap.Disasm.Disasm.blocks.build]
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
    simp only [Bap.Disasm.Disasm.blocks.build]
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
  (build_spec (leaders disasm) [] [] (sortedInstructions disasm)
    (by simp) (by simp) (by simp) (by simp) (by simp)).2.1

/-- Every block but the first begins at a leader. -/
theorem blocks_tail_start_leader (disasm : Bap.Disasm.Disasm) :
    ∀ b ∈ disasm.blocks.tail, b.start ∈ leaders disasm :=
  (build_spec (leaders disasm) [] [] (sortedInstructions disasm)
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
    simp [blocks_eq, hs, Bap.Disasm.Disasm.blocks.build]

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
  NoThrow.bind (sweepAux_noThrow d data entry hd _ _ _ _) fun _ _ => NoThrow.pure _

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
  dsimp only [scanAux]
  prw Bap.Disasm.Recursive Bap.Disasm.Recursive.scanAux
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
          else
            scanAux d data fuel (insn.successors ++ rest) (address :: visited)
              (instructions ++ [insn]) (edges ++ insn.successors.map (address, ·)) errors := by
  dsimp only [scanAux]
  prw Bap.Disasm.Recursive Bap.Disasm.Recursive.scanAux
  simp only [h]
  rfl

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

/-- Reachability along a set of recovered CFG edges. -/
inductive EdgeReach (edges : List (Nat × Nat)) (entry : Nat) : Nat → Prop
  | entry : EdgeReach edges entry entry
  | step {a b} : EdgeReach edges entry a → (a, b) ∈ edges → EdgeReach edges entry b

theorem EdgeReach.mono {e e' : List (Nat × Nat)} {entry a} (hsub : ∀ x ∈ e, x ∈ e')
    (h : EdgeReach e entry a) : EdgeReach e' entry a := by
  induction h with
  | entry => exact .entry
  | step _ he ih => exact .step ih (hsub _ he)

/-- What holds of a finished recursive scan. -/
structure ScanOk (d : Disassembler) (data : ByteArray) (entry : Nat)
    (is : List Insn) (es : List (Nat × Nat)) : Prop where
  nodup : (is.map Insn.address).Nodup
  decoded : ∀ insn ∈ is, insn.size ≠ 0 ∧ Gives d data insn.address (.ok insn)
  edges : ∀ a b, (a, b) ∈ es ↔ ∃ insn ∈ is, insn.address = a ∧ b ∈ insn.successors
  reach : ∀ insn ∈ is, EdgeReach es entry insn.address

private structure ScanInv (d : Disassembler) (data : ByteArray) (entry : Nat) (work visited : List Nat)
    (is : List Insn) (es : List (Nat × Nat)) : Prop where
  ok : ScanOk d data entry is es
  seen : ∀ insn ∈ is, insn.address ∈ visited
  reachWork : ∀ a ∈ work, EdgeReach es entry a
  reachVisited : ∀ a ∈ visited, EdgeReach es entry a

private theorem scanAux_spec (d : Disassembler) (data : ByteArray) (entry fuel : Nat)
    (work visited : List Nat) (is : List Insn) (es : List (Nat × Nat)) (errs : List String)
    (hinv : ScanInv d data entry work visited is es) :
    Holds (scanAux d data fuel work visited is es errs) fun out =>
      ScanOk d data entry out.1 out.2.1 ∧
        out.1.length + out.2.2.length ≤ is.length + errs.length + fuel + 1 := by
  induction fuel generalizing work visited is es errs with
  | zero =>
    by_cases hdone : ∀ a ∈ work, a ∈ visited
    · rw [scanAux_zero_done _ _ _ _ _ _ _ hdone]
      exact Holds.pure ⟨hinv.ok, by simp <;> omega⟩
    · rw [scanAux_zero_left _ _ _ _ _ _ _ hdone]
      exact Holds.pure ⟨hinv.ok, by simp <;> omega⟩
  | succ fuel ih =>
    cases hd : work.dropWhile (fun x => decide (x ∈ visited)) with
    | nil =>
      rw [scanAux_succ_nil _ _ _ _ _ _ _ _ hd]
      exact Holds.pure ⟨hinv.ok, by simp <;> omega⟩
    | cons address rest =>
      have ⟨hnew, hmem, hsub, _⟩ := dropWhile_cons_spec _ _ _ _ hd
      have hra : EdgeReach es entry address := hinv.reachWork _ hmem
      have hrw : ∀ a ∈ rest, EdgeReach es entry a := fun a ha => hinv.reachWork a (hsub a ha)
      rw [scanAux_succ_cons _ _ _ _ _ _ _ _ _ _ hd]
      have skip : ∀ errs', errs'.length = errs.length + 1 →
          Holds (scanAux d data fuel rest (address :: visited) is es errs') fun out =>
            ScanOk d data entry out.1 out.2.1 ∧
              out.1.length + out.2.2.length ≤ is.length + errs.length + (fuel + 1) + 1 := by
        intro errs' hl s out s' he
        have ⟨h1, h2⟩ := ih rest (address :: visited) is es errs'
          ⟨hinv.ok, fun x hx => List.mem_cons_of_mem _ (hinv.seen x hx), hrw, by
            intro a ha
            rcases List.mem_cons.1 ha with rfl | ha
            · exact hra
            · exact hinv.reachVisited a ha⟩ s out s' he
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
          have hsub' : ∀ x ∈ es, x ∈ es ++ insn.successors.map (address, ·) :=
            fun x hx => List.mem_append_left _ hx
          intro s out s' he
          have ⟨h1, h2⟩ := ih (insn.successors ++ rest) (address :: visited) (is ++ [insn])
            (es ++ insn.successors.map (address, ·)) errs
            { ok :=
                { nodup := by
                    simp only [List.map_append, List.map_cons, List.map_nil]
                    refine List.nodup_append.2 ⟨hinv.ok.nodup, by simp, ?_⟩
                    intro x hx y hy
                    rcases List.mem_map.1 hx with ⟨i, hi, rfl⟩
                    have hy' : y = address := by simpa [haddr] using hy
                    subst hy'
                    intro heq
                    exact hnew (heq ▸ hinv.seen i hi)
                  decoded := by
                    intro x hx
                    rcases List.mem_append.1 hx with hx | hx
                    · exact hinv.ok.decoded x hx
                    · rcases List.mem_singleton.1 hx with rfl
                      exact ⟨hsize, haddr ▸ hr⟩
                  edges := by
                    intro a b
                    simp only [List.mem_append, List.mem_map, List.mem_singleton, Prod.mk.injEq]
                    rw [hinv.ok.edges]
                    constructor
                    · rintro (⟨i, hi, h3, h4⟩ | ⟨b', h3, rfl, rfl⟩)
                      · exact ⟨i, .inl hi, h3, h4⟩
                      · exact ⟨insn, .inr rfl, haddr, h3⟩
                    · rintro ⟨i, hi | rfl, h3, h4⟩
                      · exact .inl ⟨i, hi, h3, h4⟩
                      · exact .inr ⟨b, h4, by omega, rfl⟩
                  reach := by
                    intro x hx
                    rcases List.mem_append.1 hx with hx | hx
                    · exact (hinv.ok.reach x hx).mono hsub'
                    · rcases List.mem_singleton.1 hx with rfl
                      rw [haddr]
                      exact hra.mono hsub' }
              seen := by
                intro x hx
                rcases List.mem_append.1 hx with hx | hx
                · exact List.mem_cons_of_mem _ (hinv.seen x hx)
                · rcases List.mem_singleton.1 hx with rfl
                  simp [haddr]
              reachWork := by
                intro a ha
                rcases List.mem_append.1 ha with ha | ha
                · exact .step (hra.mono hsub')
                    (List.mem_append_right _ (List.mem_map.2 ⟨a, ha, rfl⟩))
                · exact (hrw a ha).mono hsub'
              reachVisited := by
                intro a ha
                rcases List.mem_cons.1 ha with rfl | ha
                · exact hra.mono hsub'
                · exact (hinv.reachVisited a ha).mono hsub' } s out s' he
          simp only [List.length_append, List.length_cons, List.length_nil] at h2
          exact ⟨h1, by omega⟩

/-- Soundness of the recursive scan for an arbitrary (even effectful) decoder: instruction addresses
are unique, each instruction is a decoder answer at its own address and has non-zero size, the
edge list is exactly the successors of the instructions, and everything is reachable from entry. -/
theorem scan_sound (d : Disassembler) (data : ByteArray) (entry : Nat) :
    Holds (Recursive.scan d data entry) fun result =>
      result.entry = entry ∧ ScanOk d data entry result.instructions result.edges ∧
        result.instructions.length + result.errors.length ≤ 3 * data.size + 2 := by
  refine Holds.bind (Q := fun out => ScanOk d data entry out.1 out.2.1 ∧
      out.1.length + out.2.2.length ≤ [].length + [].length + (3 * data.size + 1) + 1)
    (scanAux_spec d data entry _ [entry] [] [] [] []
      { ok := { nodup := by simp, decoded := by simp, edges := by simp, reach := by simp }
        seen := by simp
        reachWork := by
          intro a ha
          rcases List.mem_singleton.1 ha with rfl
          exact .entry
        reachVisited := by simp }) ?_
  rintro ⟨is, es, errs⟩ ⟨h1, h2⟩ _
  exact Holds.pure ⟨rfl, h1, by simpa using h2⟩

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
        · exact ih _ _ _ _ _

/-- Termination of the scan for a decoder that does not throw. -/
theorem scan_noThrow (d : Disassembler) (data : ByteArray) (entry : Nat)
    (hd : ∀ address, NoThrow (d.decode address data)) : NoThrow (Recursive.scan d data entry) :=
  NoThrow.bind (scanAux_noThrow d data hd _ _ _ _ _ _) fun _ _ => NoThrow.pure _

/-! ### Completeness -/

/-- `insn` is the well-formed decoding the scan accepts at `address`. -/
def Valid (f : Nat → Except String Insn) (address : Nat) (insn : Insn) : Prop :=
  f address = .ok insn ∧ insn.address = address ∧ insn.size ≠ 0

/-- Reachability under a deterministic decoder. -/
inductive Reach (f : Nat → Except String Insn) (entry : Nat) : Nat → Prop
  | entry : Reach f entry entry
  | step {a b insn} : Reach f entry a → Valid f a insn → b ∈ insn.successors → Reach f entry b

private def Handled (f : Nat → Except String Insn) (is : List Insn) (errs : List String)
    (address : Nat) : Prop :=
  (∀ insn, Valid f address insn → insn ∈ is) ∧ (∀ error, f address = .error error → error ∈ errs)

private theorem Handled.mono {f : Nat → Except String Insn} {is is' : List Insn}
    {errs errs' : List String} {a : Nat}
    (his : ∀ x ∈ is, x ∈ is') (herr : ∀ x ∈ errs, x ∈ errs') (h : Handled f is errs a) :
    Handled f is' errs' a :=
  ⟨fun i hi => his _ (h.1 i hi), fun e he => herr _ (h.2 e he)⟩

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

private abbrev Closure (f : Nat → Except String Insn) (is : List Insn) (errs : List String)
    (visited work : List Nat) : Prop :=
  ∀ a ∈ visited, Handled f is errs a ∧
    ∀ insn, Valid f a insn → ∀ b ∈ insn.successors, b ∈ visited ∨ b ∈ work

/-- A scan that visited all it had to: the visited addresses contain the initial ones and are closed
under successors, and each of them is accounted for in the output. -/
private def Finished (f : Nat → Except String Insn) (work visited : List Nat)
    (out : List Insn × List (Nat × Nat) × List String) : Prop :=
  ∃ visited', (∀ a ∈ visited, a ∈ visited') ∧ (∀ a ∈ work, a ∈ visited') ∧
    Closure f out.1 out.2.2 visited' []

private theorem finished_of_all {f : Nat → Except String Insn} {work visited : List Nat}
    {is : List Insn} {es : List (Nat × Nat)} {errs : List String} (h : ∀ a ∈ work, a ∈ visited)
    (hinv : Closure f is errs visited work) : Finished f work visited (is, es, errs) := by
  refine ⟨visited, fun _ hx => hx, h, fun a ha => ⟨(hinv a ha).1, fun i hi b hb => .inl ?_⟩⟩
  rcases (hinv a ha).2 i hi b hb with hx | hx
  · exact hx
  · exact h b hx

private theorem countP_pos_of_unvisited (S visited : List Nat) (a : Nat) (ha : a ∈ S)
    (hv : a ∉ visited) : 0 < S.countP (fun x => decide (x ∉ visited)) :=
  List.countP_pos_iff.2 ⟨a, ha, by simpa using hv⟩

private theorem scanAux_complete (d : Disassembler) (data : ByteArray)
    (f : Nat → Except String Insn) (hf : ∀ a r, Gives d data a r → r = f a) (S : List Nat)
    (hS : ∀ a ∈ S, ∀ insn, Valid f a insn → ∀ b ∈ insn.successors, b ∈ S ∨ S = [])
    (fuel : Nat) (work visited : List Nat) (is : List Insn) (es : List (Nat × Nat))
    (errs : List String) (hwork : S ≠ [] → ∀ a ∈ work, a ∈ S)
    (hinv : Closure f is errs visited work) :
    Holds (scanAux d data fuel work visited is es errs) fun out =>
      (S ≠ [] → S.countP (fun x => decide (x ∉ visited)) ≤ fuel → Finished f work visited out) ∧
        (Recursive.outOfFuel ∈ out.2.2 ∨ Finished f work visited out) := by
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
              Finished f rest' (a :: visited) out) ∧
            (Recursive.outOfFuel ∈ out.2.2 ∨ Finished f rest' (a :: visited) out)) →
          (S ≠ [] → S.countP (fun x => decide (x ∉ visited)) ≤ fuel + 1 →
              Finished f work visited out) ∧
            (Recursive.outOfFuel ∈ out.2.2 ∨ Finished f work visited out) := by
        intro rest' out hrest ⟨h1, h2⟩
        have conv : Finished f rest' (a :: visited) out → Finished f work visited out := by
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
      have keep : ∀ {is' : List Insn} {errs' : List String} {rest' : List Nat},
          (∀ x ∈ is, x ∈ is') → (∀ e ∈ errs, e ∈ errs') →
          (∀ x ∈ rest, x ∈ rest') → ∀ x ∈ visited, Handled f is' errs' x ∧
            ∀ i, Valid f x i → ∀ b ∈ i.successors, b ∈ a :: visited ∨ b ∈ rest' := by
        intro is' errs' rest' h1 h2 h3 x hx
        refine ⟨(hinv x hx).1.mono h1 h2, fun i hi b hb => ?_⟩
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
                Finished f work visited out) ∧
              (Recursive.outOfFuel ∈ out.2.2 ∨ Finished f work visited out) := by
        intro errs' hsub' hnv herr s out s' he
        refine lift rest out (fun _ h => h) (ih rest (a :: visited) is es errs' hrestS ?_ s out s' he)
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact ⟨⟨fun i hi => (hnv i hi).elim, herr⟩, fun i hi => (hnv i hi).elim⟩
        · exact keep (fun _ h => h) hsub' (fun _ h => h) x hx'
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
            subst_vars
            have hii := huniq i hi.1
            subst hii
            simp [hi.2.1, hi.2.2] at hbad
          · intro e he
            rw [← hfa] at he
            cases he
        · rename_i hgood
          have hg : insn.address = a ∧ ¬insn.size = 0 := by simpa using hgood
          have hvalid : Valid f a insn := ⟨hfa.symm, hg.1, hg.2⟩
          intro s out s' he
          refine lift (insn.successors ++ rest) out (fun _ h => List.mem_append_right _ h)
            (ih (insn.successors ++ rest) (a :: visited) (is ++ [insn])
              (es ++ insn.successors.map (a, ·)) errs ?_ ?_ s out s' he)
          · intro hne x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact (hS a (hwork hne a hmem) insn hvalid x hx).resolve_right hne
            · exact hrestS hne x hx
          · intro x hx
            rcases List.mem_cons.1 hx with rfl | hx'
            · refine ⟨⟨?_, ?_⟩, ?_⟩
              · intro i hi
                have hii := huniq i hi.1
                subst hii
                simp
              · intro e he
                rw [← hfa] at he
                cases he
              · intro i hi b hb
                have hii := huniq i hi.1
                subst hii
                exact .inr (List.mem_append_left _ hb)
            · exact keep (fun _ h => List.mem_append_left _ h) (fun _ h => h)
                (fun _ h => List.mem_append_right _ h) x hx'

private theorem finished_reach {f : Nat → Except String Insn} {entry : Nat} {is : List Insn}
    {errs : List String} {v : List Nat}
    (hw : ∀ a ∈ [entry], a ∈ v) (hc : Closure f is errs v []) (a : Nat) (ha : Reach f entry a) : a ∈ v := by
  induction ha with
  | entry => exact hw _ (by simp)
  | step _ hv hb ih =>
    rcases (hc _ ih).2 _ hv _ hb with h | h
    · exact h
    · simp at h

/-- Nothing is lost silently. For a deterministic decoder, a finished scan accounts for every
address reachable from the entry: its well-formed instruction is in the output or its decode error
is reported; the only other outcome is the out-of-fuel error. -/
theorem scan_no_silent_loss (d : Disassembler) (data : ByteArray) (entry : Nat)
    (f : Nat → Except String Insn) (hf : ∀ a r, Gives d data a r → r = f a) :
    Holds (Recursive.scan d data entry) fun result =>
      Recursive.outOfFuel ∈ result.errors ∨
        ∀ a, Reach f entry a →
          (∀ insn, Valid f a insn → insn ∈ result.instructions) ∧
            ∀ error, f a = .error error → error ∈ result.errors := by
  refine Holds.bind (scanAux_complete d data f hf [] (by simp) _ [entry] [] [] [] []
    (by simp) (fun _ h => by cases h)) ?_
  rintro ⟨is, es, errs⟩ ⟨_, h⟩ _
  refine Holds.pure ?_
  rcases h with h | ⟨v, _, hw, hc⟩
  · exact .inl h
  · exact .inr fun a ha => (hc a (finished_reach hw hc a ha)).1

/-- Completeness. For a deterministic decoder, if the reachable addresses lie in a list `S` that
fits the fuel of `3 * data.size + 1`, each reachable address is accounted for. Unlike the earlier
bound, addresses that are reached again cost nothing. -/
theorem scan_complete (d : Disassembler) (data : ByteArray) (entry : Nat)
    (f : Nat → Except String Insn) (hf : ∀ a r, Gives d data a r → r = f a) (S : List Nat)
    (hentry : entry ∈ S)
    (hS : ∀ a ∈ S, ∀ insn, Valid f a insn → ∀ b ∈ insn.successors, b ∈ S)
    (hfuel : S.length ≤ 3 * data.size + 1) :
    Holds (Recursive.scan d data entry) fun result =>
      ∀ a, Reach f entry a →
        (∀ insn, Valid f a insn → insn ∈ result.instructions) ∧
          ∀ error, f a = .error error → error ∈ result.errors := by
  have hne : S ≠ [] := fun h => by simp [h] at hentry
  have hcount : S.countP (fun x => decide (x ∉ ([] : List Nat))) ≤ S.length := List.countP_le_length
  refine Holds.bind (scanAux_complete d data f hf S (fun a ha i hi b hb => .inl (hS a ha i hi b hb))
    _ [entry] [] [] [] [] (fun _ a ha => by simpa [List.mem_singleton.1 ha] using hentry)
    (fun _ h => by cases h)) ?_
  rintro ⟨is, es, errs⟩ ⟨h, _⟩ _
  obtain ⟨v, _, hw, hc⟩ := h hne (by omega)
  exact Holds.pure fun a ha => (hc a (finished_reach hw hc a ha)).1

/-- The built-in fuel always suffices when the decoder only accepts addresses of a range as large
as the input, which is what the real decoders do on a loaded region: the scan is then complete,
without any assumption about how the code branches. -/
theorem scan_complete_of_in_range (d : Disassembler) (data : ByteArray) (entry base : Nat)
    (f : Nat → Except String Insn) (hf : ∀ a r, Gives d data a r → r = f a)
    (hrange : ∀ a insn, Valid f a insn → base ≤ a ∧ a < base + data.size) :
    Holds (Recursive.scan d data entry) fun result =>
      ∀ a, Reach f entry a →
        (∀ insn, Valid f a insn → insn ∈ result.instructions) ∧
          ∀ error, f a = .error error → error ∈ result.errors := by
  let region := (List.range data.size).map (base + ·)
  let successorsOf (a : Nat) : List Nat :=
    match f a with
    | .ok insn => insn.successors
    | .error _ => []
  let S := entry :: (region ++ region.flatMap successorsOf)
  have hsucc : ∀ a, (successorsOf a).length ≤ 2 := by
    intro a
    show (match f a with
      | .ok insn => insn.successors
      | .error _ => []).length ≤ 2
    split
    · exact successors_length_le_two _
    · simp
  have hflat : ∀ l : List Nat, (l.flatMap successorsOf).length ≤ 2 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      have := hsucc x
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  have hregion : region.length = data.size := by simp [region]
  refine scan_complete d data entry f hf S (by simp [S]) ?_ ?_
  · intro a _ insn hv b hb
    have ⟨h1, h2⟩ := hrange a insn hv
    have har : a ∈ region := List.mem_map.2 ⟨a - base, List.mem_range.2 (by omega), by omega⟩
    refine List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨a, har, ?_⟩))
    show b ∈ (match f a with
      | .ok insn => insn.successors
      | .error _ => [])
    rw [hv.1]
    exact hb
  · have := hflat region
    simp only [S, List.length_cons, List.length_append]
    omega

end Bap.Proofs.Disasm
