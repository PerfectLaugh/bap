import Lean
import Bap.Primus.Lifted
import Bap.Proofs.Emu
import Bap.Proofs.Primus

open Lean Elab Command in
/-- Bring private declarations of module `mod`, namespace `ns`, into scope by short name. -/
local elab "open_private " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

set_option linter.unusedSimpArgs false

namespace Bap.Proofs.Jit

open Bap.Jit

/-! `Bap.Jit` is an FFI boundary: `compile`, the runners and the persistent-memory API are `@[extern]`
opaques, so their machine behaviour cannot be unfolded. What is provable is the Lean wrapper layer
(below) and the contract of the lowering side that produces `Jit.Op` and classifies `Jit.BinOp`. -/

/-! ### Wrappers around the native runner -/

section Wrappers

/-- `runWithMemoryObserved` installs no code observer. -/
theorem runWithMemoryObserved_eq (program : Program) (state addresses : Array UInt64) (values : Array UInt8)
    (observer : Option MemoryObserver) :
    runWithMemoryObserved program state addresses values observer =
      runWithMemoryObservedCode program state addresses values observer none := rfl

/-- `runWithMemory` installs no observers at all. -/
theorem runWithMemory_eq (program : Program) (state addresses : Array UInt64) (values : Array UInt8) :
    runWithMemory program state addresses values =
      runWithMemoryObservedCode program state addresses values none none := rfl

theorem runWithPersistentMemory_eq (program : Program) (state : Array UInt64) (memory : Bap.Jit.Memory)
    (observer : Option MemoryObserver) :
    runWithPersistentMemory program state memory observer =
      runWithPersistentMemoryObservedCode program state memory observer none := rfl

/-- `run` on any world: it starts from an empty memory image, drops the returned image, and threads the
world and native errors through unchanged. -/
theorem run_result (program : Program) (state : Array UInt64) (world : Void IO.RealWorld) :
    run program state world =
      match runWithMemoryObservedCode program state #[] #[] none none world with
      | .ok (next, slots, _, _) after => .ok (next, slots) after
      | .error error after => .error error after := by
  have key : ∀ (action : IO (Nat × Array UInt64 × Array UInt64 × Array UInt8))
      (f : Nat × Array UInt64 × Array UInt64 × Array UInt8 → IO (Nat × Array UInt64)),
      (action >>= f) world = (match action world with
        | .ok value after => f value after
        | .error error after => .error error after) := by
    intro action f
    show EST.bind action f world = _
    simp only [EST.bind]
    cases action world <;> rfl
  show (runWithMemoryObservedCode program state #[] #[] none none >>= fun result => pure (result.1, result.2.1)) world = _
  rw [key]
  cases runWithMemoryObservedCode program state #[] #[] none none world with
  | ok value after => rfl
  | error error after => rfl

/-- `run` fails exactly when the native runner fails, with the same error. -/
theorem run_error_iff (program : Program) (state : Array UInt64) (world after : Void IO.RealWorld) (error : IO.Error) :
    run program state world = .error error after ↔
      runWithMemoryObservedCode program state #[] #[] none none world = .error error after := by
  rw [run_result]
  cases runWithMemoryObservedCode program state #[] #[] none none world with
  | ok value later => simp
  | error error later => simp

end Wrappers

/-! ### Operator classification -/

section Operators

open Bap.Primus.Lifted
open_private Bap.Primus.Lifted Bap.Primus.Lifted binaryOp isComparison isSigned

/-- Reference semantics a native `BinOp` must implement on full-width slots; comparisons yield 0 or 1. -/
def BinOp.denote : BinOp → BitVec 64 → BitVec 64 → Nat
  | .add, l, r => (l.toNat + r.toNat) % 2 ^ 64
  | .sub, l, r => (l - r).toNat
  | .mul, l, r => (l.toNat * r.toNat) % 2 ^ 64
  | .and, l, r => (l &&& r).toNat
  | .or, l, r => (l ||| r).toNat
  | .xor, l, r => (l ^^^ r).toNat
  | .lshift, l, r => (l <<< r.toNat).toNat
  | .rshift, l, r => l.toNat >>> r.toNat
  | .eq, l, r => if l = r then 1 else 0
  | .neq, l, r => if l = r then 0 else 1
  | .lt, l, r => if l.toNat < r.toNat then 1 else 0
  | .le, l, r => if l.toNat ≤ r.toNat then 1 else 0
  | .gt, l, r => if r.toNat < l.toNat then 1 else 0
  | .ge, l, r => if r.toNat ≤ l.toNat then 1 else 0
  | .udiv, l, r => if r = 0 then 2 ^ 64 - 1 else l.toNat / r.toNat
  | .urem, l, r => if r = 0 then l.toNat else l.toNat % r.toNat
  | .sdiv, l, r => (l.smtSDiv r).toNat
  | .srem, l, r => if r = 0 then l.toNat else (l.srem r).toNat
  | .slt, l, r => if l.toInt < r.toInt then 1 else 0
  | .sle, l, r => if l.toInt ≤ r.toInt then 1 else 0
  | .sgt, l, r => if r.toInt < l.toInt then 1 else 0
  | .sge, l, r => if r.toInt ≤ l.toInt then 1 else 0

/-- Lowering soundness at the operator level: every BIL operator the JIT accepts maps to a native
operator whose reference semantics equals the interpreter's `evalBin` on 64-bit operands. -/
theorem binaryOp_sound {op : Bil.BinOp} {native : BinOp} (h : binaryOp op = some native) (l r : BitVec 64) :
    ∃ (width : Nat) (value : BitVec width), Bil.evalBin op ⟨64, l⟩ ⟨64, r⟩ = .ok (.bits value) ∧
      value.toNat = BinOp.denote native l r := by
  cases op <;> simp only [binaryOp, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    refine ⟨_, _, rfl, ?_⟩ <;> simp only [BinOp.denote]
  all_goals try simp [Word.udiv, Word.urem, Word.sdiv, Word.srem, Word.shl, Word.lshr, Word.eq, Word.neq, Word.lt,
    Word.le, Word.slt, Word.sle, Word.bool, Word.ones]
  case div => by_cases h : r = 0#64 <;> simp only [h, ↓reduceIte] <;> first | rfl | simp
  case rem => by_cases h : r = 0#64 <;> simp only [h, ↓reduceIte] <;> first | rfl | simp
  case srem => by_cases h : r = 0#64 <;> simp only [h, ↓reduceIte] <;> first | rfl | simp
  case lshift => rfl
  case rshift => rfl
  case eq =>
    by_cases h : l = r
    · simp [h]
    · have hb : (l == r) = false := by simpa using h
      simp [h, hb]
  case neq =>
    by_cases h : l = r
    · simp [h]
    · have hb : (l != r) = true := by simpa using h
      simp [h, hb]
  case lt => by_cases h : l.toNat < r.toNat <;> simp [BitVec.lt_def, h]
  case le => by_cases h : l.toNat ≤ r.toNat <;> simp [BitVec.le_def, h]
  case gt => by_cases h : r.toNat < l.toNat <;> simp [BitVec.lt_def, h]
  case ge => by_cases h : r.toNat ≤ l.toNat <;> simp [BitVec.le_def, h]
  case slt => by_cases h : l.toInt < r.toInt <;> simp [BitVec.slt, h]
  case sle => by_cases h : l.toInt ≤ r.toInt <;> simp [BitVec.sle, h]
  case sgt => by_cases h : r.toInt < l.toInt <;> simp [BitVec.slt, h]
  case sge => by_cases h : r.toInt ≤ l.toInt <;> simp [BitVec.sle, h]

/-- Exactly `smod` and `ashift` have no direct native operator and force interpretation or special lowering. -/
theorem binaryOp_none_iff (op : Bil.BinOp) : binaryOp op = none ↔ op = .smod ∨ op = .ashift := by
  cases op <;> simp [binaryOp]

theorem binaryOp_injective {left right : Bil.BinOp} {native : BinOp}
    (hl : binaryOp left = some native) (hr : binaryOp right = some native) : left = right := by
  cases left <;> cases right <;> simp [binaryOp] at hl hr <;> subst hl <;> first | rfl | cases hr

theorem binaryOp_surjective : ∀ native : BinOp, ∃ op, binaryOp op = some native
  | .add => ⟨.add, rfl⟩
  | .sub => ⟨.sub, rfl⟩
  | .mul => ⟨.mul, rfl⟩
  | .and => ⟨.and, rfl⟩
  | .or => ⟨.or, rfl⟩
  | .xor => ⟨.xor, rfl⟩
  | .lshift => ⟨.lshift, rfl⟩
  | .rshift => ⟨.rshift, rfl⟩
  | .eq => ⟨.eq, rfl⟩
  | .neq => ⟨.neq, rfl⟩
  | .lt => ⟨.lt, rfl⟩
  | .le => ⟨.le, rfl⟩
  | .gt => ⟨.gt, rfl⟩
  | .ge => ⟨.ge, rfl⟩
  | .udiv => ⟨.div, rfl⟩
  | .urem => ⟨.rem, rfl⟩
  | .sdiv => ⟨.sdiv, rfl⟩
  | .srem => ⟨.srem, rfl⟩
  | .slt => ⟨.slt, rfl⟩
  | .sle => ⟨.sle, rfl⟩
  | .sgt => ⟨.sgt, rfl⟩
  | .sge => ⟨.sge, rfl⟩

/-- Native comparisons are 0/1-valued; that is why they are narrowed differently in lowering. -/
theorem denote_comparison_boolean (native : BinOp) (h : isComparison native = true) (l r : BitVec 64) :
    BinOp.denote native l r ≤ 1 := by
  cases native <;> simp [isComparison] at h <;> simp only [BinOp.denote] <;> split <;> omega

/-- Signedness: an operator is signed iff its native semantics depends on sign extension. -/
theorem isSigned_iff (native : BinOp) :
    isSigned native = true ↔ native = .sdiv ∨ native = .srem ∨ native = .slt ∨ native = .sle ∨
      native = .sgt ∨ native = .sge := by
  cases native <;> simp [isSigned]

end Operators

/-! ### Emission protocol -/

section Emission

open Bap.Primus.Lifted
open_private Bap.Primus.Lifted Bap.Primus.Lifted Lowering Lowering.ops Lowering.effectSlot Lowering.nextSlot
  Lowering.checkpoints Lowering.outputs temporary setEffect jumpConstant jumpSlot codeSite signExtend graphEdgeOps

/-- Effect code 1 means "jump taken": a native jump always sets the effect slot first. -/
theorem jumpConstant_ops (lowering : Lowering) (target : UInt64) :
    Lowering.ops (jumpConstant lowering target) =
      Lowering.ops lowering ++ [.set (setEffect lowering 1).2 1] ++ [.jump target] := by
  cases h : Lowering.effectSlot lowering <;> simp [jumpConstant, setEffect, h, temporary, Lowering.ops]

theorem jumpSlot_ops (lowering : Lowering) (target : Nat) :
    Lowering.ops (jumpSlot lowering target) =
      Lowering.ops lowering ++ [.set (setEffect lowering 1).2 1] ++ [.jumpSlot target] := by
  cases h : Lowering.effectSlot lowering <;> simp [jumpSlot, setEffect, h, temporary, Lowering.ops]

/-- The jump effect slot is the one `nativeResult` later reads back. -/
theorem jumpConstant_effect (lowering : Lowering) (target : UInt64) :
    Lowering.effectSlot (jumpConstant lowering target) = some (setEffect lowering 1).2 := by
  cases h : Lowering.effectSlot lowering <;> simp [jumpConstant, setEffect, h, temporary, Lowering.effectSlot]

/-- Code sites clear the effect, publish the pc to the observer, and checkpoint the outputs. -/
theorem codeSite_ops (lowering : Lowering) (pc : Nat) :
    Lowering.ops (codeSite lowering pc) =
      Lowering.ops lowering ++ [.set (setEffect lowering 0).2 0] ++ [.code (setEffect lowering 0).2 (UInt64.ofNat pc)] := by
  cases h : Lowering.effectSlot lowering <;> simp [codeSite, setEffect, h, temporary, Lowering.ops]

theorem codeSite_checkpoint (lowering : Lowering) (pc : Nat) :
    Lowering.checkpoints (codeSite lowering pc) =
      Lowering.checkpoints lowering ++ [(pc, Lowering.outputs lowering)] := by
  cases h : Lowering.effectSlot lowering <;> simp [codeSite, setEffect, h, temporary, Lowering.checkpoints, Lowering.outputs]

/-- Sign extension writes to a fresh temporary and never clobbers its source slot. -/
theorem signExtend_fresh (lowering : Lowering) (width source : Nat) :
    (signExtend lowering width source).2 = Lowering.nextSlot lowering ∧
      Lowering.ops (signExtend lowering width source).1 =
        Lowering.ops lowering ++ [.signExtend width (Lowering.nextSlot lowering) source] := by
  simp [signExtend, temporary, Lowering.ops]

/-- Edges leaving the compiled range exit through the jump protocol rather than a goto. -/
theorem graphEdgeOps_external (lowering : Lowering) (labels : List (Nat × Nat)) (edges : List (Nat × Nat))
    (source target : Nat) (he : edges.contains (source, target) = false) :
    ∃ ops, graphEdgeOps lowering labels edges source target = some ops ∧ ops.getLast? = some (.jump (UInt64.ofNat target)) := by
  simp only [graphEdgeOps, he, Bool.false_eq_true, ↓reduceIte]
  refine ⟨_, rfl, ?_⟩
  cases h : Lowering.effectSlot lowering <;> simp [jumpConstant, setEffect, h, temporary, Lowering.ops]

end Emission

/-! ### The persistent memory contract

Obligations 7 to 9 of the trusted base in `Bap.Jit`, on a model, with what the Lean side does with them. -/

section Contract

open Bap.Emu
open Proofs.Core.MemoryLaws
open_private Bap.Emu Bap.Emu persistentRegionData

/-- A `Jit.Memory`, by obligation 7: a total map from addresses to bytes. -/
abbrev NativeMemory := Nat → UInt8

/-- `writeMemory`: pairs, in order. -/
def NativeMemory.write (memory : NativeMemory) (cells : List (Nat × UInt8)) : NativeMemory :=
  cells.foldl (init := memory) fun memory cell address => if address = cell.1 then cell.2 else memory address

/-- `createMemory`: pairs on nothing. -/
def NativeMemory.create (cells : List (Nat × UInt8)) : NativeMemory := NativeMemory.write (fun _ => 0) cells

theorem NativeMemory.write_nil (memory : NativeMemory) : memory.write [] = memory := rfl

private theorem write_other (cells : List (Nat × UInt8)) (memory : NativeMemory) (address : Nat)
    (h : ∀ cell ∈ cells, cell.1 ≠ address) : memory.write cells address = memory address := by
  induction cells generalizing memory with
  | nil => rfl
  | cons head tail ih =>
    simp only [NativeMemory.write, List.foldl_cons]
    have := ih (fun address => if address = head.1 then head.2 else memory address)
      (fun c hc => h c (List.mem_cons_of_mem _ hc))
    simp only [NativeMemory.write] at this
    rw [this]
    have hne : address ≠ head.1 := fun he => h head (List.mem_cons_self ..) he.symm
    simp [hne]

private theorem write_distinct (cells : List (Nat × UInt8)) (memory : NativeMemory) (cell : Nat × UInt8)
    (hm : cell ∈ cells) (hnd : (cells.map Prod.fst).Nodup) : memory.write cells cell.1 = cell.2 := by
  induction cells generalizing memory with
  | nil => cases hm
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    obtain ⟨hhead, htail⟩ := hnd
    simp only [NativeMemory.write, List.foldl_cons]
    rcases List.mem_cons.1 hm with rfl | hm'
    · have := write_other tail (fun address => if address = cell.1 then cell.2 else memory address) cell.1
        (fun c hc he => hhead c hc he)
      simp only [NativeMemory.write] at this
      rw [this]
      simp
    · exact ih _ hm' htail

/-- `nativeFromState` on the model: a native memory made from the cells of a memory reads what it reads. -/
theorem create_cells_reads {width : Nat} {memory : Bap.Memory width} (h : Bap.Proofs.Emu.PagesWF memory)
    (hnd : ((Bap.Memory.cells memory).map fun cell => cell.1.toNat).Nodup) (address : BitVec width) :
    NativeMemory.create ((Bap.Memory.cells memory).map fun cell => (cell.1.toNat, cell.2)) address.toNat =
      Bap.Memory.readByte memory address := by
  have hmap : (((Bap.Memory.cells memory).map fun cell => (cell.1.toNat, cell.2)).map Prod.fst) =
      (Bap.Memory.cells memory).map fun cell => cell.1.toNat := by
    simp [List.map_map, Function.comp_def]
  cases hb : decide (Bap.Memory.readByte memory address = 0) with
  | true =>
    have hzero : Bap.Memory.readByte memory address = 0 := by simpa using hb
    rw [hzero]
    apply write_other
    intro cell hc he
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hc
    have hmem := (Bap.Proofs.Emu.mem_cells_iff h c.1 c.2).1 hc'
    have heq : c.1 = address := BitVec.eq_of_toNat_eq he
    rw [heq, hzero] at hmem
    exact hmem.1 hmem.2.symm
  | false =>
    have hnz : Bap.Memory.readByte memory address ≠ 0 := by simpa using hb
    have hcell := (Bap.Proofs.Emu.mem_cells_iff h address _).2 ⟨hnz, rfl⟩
    exact write_distinct _ _ (address.toNat, Bap.Memory.readByte memory address)
      (List.mem_map.2 ⟨_, hcell, rfl⟩) (hmap ▸ hnd)

/-- `regionsFromNative` on the model: with a dump as obligation 8 says, a region gets the bytes of native
memory, at each offset. -/
theorem region_bytes_of_dump (native : NativeMemory) (cells : List (Nat × UInt8)) (address size : Nat)
    (hsorted : cells.Pairwise fun a b => a.1 < b.1)
    (hdump : ∀ a, native a = Bap.Proofs.Emu.cellAt cells a) {index : Nat} (h : index < size) :
    (persistentRegionData cells address size #[])[index]? = some (native (address + index)) := by
  rw [hdump]
  exact Bap.Proofs.Emu.persistentRegionData_bytes cells address size hsorted h

/-- A clone is a copy: by obligation 9 each of them changes on its own. -/
theorem clone_isolated (parent : NativeMemory) (childWrites parentWrites : List (Nat × UInt8)) (address : Nat)
    (hc : ∀ cell ∈ childWrites, cell.1 ≠ address) (hp : ∀ cell ∈ parentWrites, cell.1 ≠ address) :
    (parent.write parentWrites) address = parent address ∧ (parent.write childWrites) address = parent address :=
  ⟨write_other _ _ _ hp, write_other _ _ _ hc⟩

private def writeRange {width : Nat} (native : Nat → UInt8) (memory : Bap.Memory width) (start : Nat) : Nat → Bap.Memory width
  | 0 => memory
  | n + 1 => Bap.Memory.writeByte (writeRange native memory start n) (BitVec.ofNat width (start + n)) (native (start + n))

private theorem writeRange_spec {width : Nat} (native : Nat → UInt8) (memory : Bap.Memory width) (h : PagesSized memory)
    (start n : Nat) (hn : start + n ≤ 2 ^ width) (address : Nat) (ha : address < 2 ^ width) :
    PagesSized (writeRange native memory start n) ∧
      (start ≤ address → address < start + n →
        Bap.Memory.readByte (writeRange native memory start n) (BitVec.ofNat width address) = native address) ∧
      (¬ (start ≤ address ∧ address < start + n) →
        Bap.Memory.readByte (writeRange native memory start n) (BitVec.ofNat width address) =
          Bap.Memory.readByte memory (BitVec.ofNat width address)) := by
  induction n with
  | zero => exact ⟨h, fun _ _ => by omega, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    refine ⟨writeByte_pagesSized h1 _ _, fun hl hu => ?_, fun hn' => ?_⟩
    · simp only [writeRange]
      by_cases he : address = start + n
      · subst he
        exact readByte_writeByte_same h1 _ _
      · have hne : BitVec.ofNat width address ≠ BitVec.ofNat width (start + n) := by
          intro heq
          have := congrArg BitVec.toNat heq
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show start + n < 2 ^ width by omega)] at this
          omega
        rw [readByte_writeByte_other _ hne]
        exact h2 hl (by omega)
    · simp only [writeRange]
      have hne : BitVec.ofNat width address ≠ BitVec.ofNat width (start + n) := by
        intro heq
        have := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show start + n < 2 ^ width by omega)] at this
        omega
      rw [readByte_writeByte_other _ hne]
      exact h3 (by omega)

private theorem foldl_range_eq {width : Nat} (native : Nat → UInt8) (memory : Bap.Memory width) (start n : Nat) :
    (List.range n).foldl (init := memory) (fun memory offset =>
      Bap.Memory.writeByte memory (BitVec.ofNat width (start + offset)) (native (start + offset))) =
      writeRange native memory start n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; rfl

/-- `applyJournalM` on a pure read, as a fold. -/
private def journalFold {width : Nat} (native : Nat → UInt8) (memory : Bap.Memory width) (journal : List (Nat × Nat)) :
    Bap.Memory width :=
  journal.foldl (init := memory) fun memory write => writeRange native memory write.1 write.2

private theorem journalFold_spec {width : Nat} (native : Nat → UInt8) (journal : List (Nat × Nat)) (memory : Bap.Memory width)
    (h : PagesSized memory) (hwidth : ∀ write ∈ journal, write.1 + write.2 ≤ 2 ^ width) (address : Nat)
    (ha : address < 2 ^ width) :
    ((∃ write ∈ journal, write.1 ≤ address ∧ address < write.1 + write.2) →
        Bap.Memory.readByte (journalFold native memory journal) (BitVec.ofNat width address) = native address) ∧
      ((∀ write ∈ journal, ¬ (write.1 ≤ address ∧ address < write.1 + write.2)) →
        Bap.Memory.readByte (journalFold native memory journal) (BitVec.ofNat width address) =
          Bap.Memory.readByte memory (BitVec.ofNat width address)) := by
  induction journal generalizing memory with
  | nil =>
    refine ⟨?_, fun _ => rfl⟩
    rintro ⟨write, hm, _⟩
    cases hm
  | cons head tail ih =>
    have hspec := writeRange_spec native memory h head.1 head.2 (hwidth head (List.mem_cons_self ..)) address ha
    obtain ⟨h1, h2⟩ := ih (writeRange native memory head.1 head.2) hspec.1 (fun w hw => hwidth w (List.mem_cons_of_mem _ hw))
    show (_ → Bap.Memory.readByte (journalFold native (writeRange native memory head.1 head.2) tail) _ = _) ∧
      (_ → Bap.Memory.readByte (journalFold native (writeRange native memory head.1 head.2) tail) _ = _)
    refine ⟨?_, fun hall => ?_⟩
    · rintro ⟨write, hm, hl, hu⟩
      by_cases htail : ∃ w ∈ tail, w.1 ≤ address ∧ address < w.1 + w.2
      · exact h1 htail
      · have hall : ∀ w ∈ tail, ¬ (w.1 ≤ address ∧ address < w.1 + w.2) := fun w hw hc => htail ⟨w, hw, hc⟩
        rw [h2 hall]
        rcases List.mem_cons.1 hm with rfl | hm'
        · exact hspec.2.1 hl hu
        · exact absurd ⟨hl, hu⟩ (hall write hm')
    · rw [h2 fun w hw => hall w (List.mem_cons_of_mem _ hw)]
      exact hspec.2.2 (hall head (List.mem_cons_self ..))

private theorem applyJournal_fold {width : Nat} (native : Nat → UInt8) (memory : Bap.Memory width) (journal : List (Nat × Nat)) :
    applyJournalM (m := Id) (fun address => pure (native address)) memory journal = journalFold native memory journal := by
  simp only [applyJournalM, journalFold]
  induction journal generalizing memory with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.foldlM_cons, List.foldl_cons]
    have hinner : ∀ (n : Nat) (m : Bap.Memory width),
        (List.range n).foldlM (m := Id) (init := m) (fun memory offset =>
          pure (Bap.Memory.writeByte memory (BitVec.ofNat width (head.1 + offset)) (native (head.1 + offset)))) =
        (pure (writeRange native m head.1 n) : Id _) := by
      intro n m
      rw [← foldl_range_eq, List.foldl_eq_foldlM]
      rfl
    have hi := hinner head.2 memory
    have key := congrArg (fun start => List.foldlM (m := Id) (fun memory write =>
      List.foldlM (m := Id) (fun memory offset => do
        let byte ← pure (native (write.fst + offset))
        pure (Bap.Memory.writeByte memory (BitVec.ofNat width (write.fst + offset)) byte))
      memory (List.range write.snd)) start tail) hi
    exact key.trans (ih _)

/-- The journal of a parallel round on the model: `applyJournalM` gives the memory value the bytes of native
memory at the written ranges, and leaves everything else, which is why the rollback of a later round is exact. -/
theorem applyJournal_spec {width : Nat} (native : Nat → UInt8) (journal : List (Nat × Nat)) (memory : Bap.Memory width)
    (h : PagesSized memory) (hwidth : ∀ write ∈ journal, write.1 + write.2 ≤ 2 ^ width) (address : Nat)
    (ha : address < 2 ^ width) :
    let updated := applyJournalM (m := Id) (fun address => pure (native address)) memory journal
    ((∃ write ∈ journal, write.1 ≤ address ∧ address < write.1 + write.2) →
        Bap.Memory.readByte updated (BitVec.ofNat width address) = native address) ∧
      ((∀ write ∈ journal, ¬ (write.1 ≤ address ∧ address < write.1 + write.2)) →
        Bap.Memory.readByte updated (BitVec.ofNat width address) =
          Bap.Memory.readByte memory (BitVec.ofNat width address)) := by
  simp only [applyJournal_fold]
  exact journalFold_spec native journal memory h hwidth address ha

end Contract


/-! ### Memory on the machine

`memLoad` and `memStore` against `Memory.read` and `Memory.write`. A memory narrower than 64 bits is modelled by a
machine whose `view` wraps with its address space; see `Bap.Proofs.Primus.Machine` for what that has to do with
native code. -/

section MemoryOps

open Bap.Proofs.Primus
open Proofs.Core.MemoryLaws
open_private Bap.Core.Memory Bap.Memory byteAt

/-- `view` wraps at the end of an address space of `width` bits. -/
def ViewOf (machine : Machine) (width : Nat) : Prop :=
  ∀ address, machine.view address = BitVec.ofNat 64 (address.toNat % 2 ^ width)

/-- The memory of the machine holds a memory, in the addresses that the address space has. -/
def WindowOf (memory : Word64 → UInt8) {width : Nat} (cells : Bap.Memory width) : Prop :=
  ∀ address : BitVec width, memory (address.setWidth 64) = Bap.Memory.readByte cells address

private theorem pow_le_64 {width : Nat} (hw : width ≤ 64) : 2 ^ width ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw

/-- An address and an offset, seen through the view, are the address of the sum in the address space. -/
theorem view_add {machine : Machine} {width : Nat} (hv : ViewOf machine width) (hw : width ≤ 64) (address : BitVec width)
    (offset : Nat) (ho : offset < 2 ^ 64) :
    machine.view (address.setWidth 64 + BitVec.ofNat 64 offset) = (address + BitVec.ofNat width offset).setWidth 64 := by
  rw [hv]
  apply BitVec.eq_of_toNat_eq
  have hdvd : 2 ^ width ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hw
  have hlt : (address + BitVec.ofNat width offset).toNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (BitVec.isLt _) (pow_le_64 hw)
  have haddr : address.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le address.isLt (pow_le_64 hw)
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ hdvd]
  rw [Nat.mod_eq_of_lt haddr, Nat.mod_eq_of_lt ho]
  simp only [Nat.add_mod_mod]

/-- The strong agreement that loads use, from a window and a view that wraps. -/
theorem memoryAgrees_of_window {machine : Machine} {width : Nat} {cells : Bap.Memory width} (hv : ViewOf machine width)
    (hw : width ≤ 64) (hc : WindowOf machine.memory cells) (address : BitVec width) (offset : Nat) (ho : offset < 8) :
    machine.memory (machine.view (address.setWidth 64 + BitVec.ofNat 64 offset)) =
      Bap.Memory.readByte cells (address + BitVec.ofNat width offset) := by
  rw [view_add hv hw address offset (by omega), hc]

private theorem foldl_congr_mem {α β : Type} {f g : β → α → β} {items : List α} {init : β}
    (h : ∀ result item, item ∈ items → f result item = g result item) : items.foldl f init = items.foldl g init := by
  induction items generalizing init with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.foldl_cons]
    rw [h _ _ List.mem_cons_self]
    exact ih fun result item hitem => h result item (List.mem_cons_of_mem _ hitem)

/-- A view does nothing when the address is in the address space. On a machine with the identity for its view, that
is native code, an access at an address where all bytes are in the address space loads the same. -/
theorem denoteLoad_view {memory : Word64 → UInt8} {view : Word64 → Word64} {base : Word64} {size : Nat} {big : Bool}
    (h : ∀ index, index < size → view (base + BitVec.ofNat 64 index) = base + BitVec.ofNat 64 index) :
    denoteLoad (fun address => memory (view address)) base size big = denoteLoad memory base size big := by
  unfold denoteLoad
  apply foldl_congr_mem
  intro result index hindex
  simp only [h index (List.mem_range.1 hindex)]

/-- And it stores the same. -/
theorem denoteStore_view {memory : Word64 → UInt8} {view : Word64 → Word64} {base value : Word64} {size : Nat} {big : Bool}
    (h : ∀ index, index < size → view (base + BitVec.ofNat 64 index) = base + BitVec.ofNat 64 index) :
    denoteStore memory view base value size big = denoteStore memory id base value size big := by
  unfold denoteStore
  apply foldl_congr_mem
  intro result index hindex
  funext address
  simp only [h index (List.mem_range.1 hindex), id]

/-- The view that wraps does nothing to an access that does not pass the end of the space. -/
theorem wrap_in_range {width : Nat} {base : Word64} {size index : Nat} (hin : base.toNat + size ≤ 2 ^ width)
    (hindex : index < size) (hw : width ≤ 64) :
    BitVec.ofNat 64 ((base + BitVec.ofNat 64 index).toNat % 2 ^ width) = base + BitVec.ofNat 64 index := by
  have h1 : base.toNat + index < 2 ^ width := by omega
  have h2 := pow_le_64 hw
  have hi : index < 2 ^ 64 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega : base.toNat + index < 2 ^ 64), Nat.mod_eq_of_lt h1,
    Nat.mod_eq_of_lt (by omega)]

private def storedByte (value : Word64) (size index : Nat) (big : Bool) : UInt8 :=
  UInt8.ofNat ((value >>> ((if big then size - 1 - index else index) * 8)).toNat % 256)

private def storeUpTo (memory : Word64 → UInt8) (view : Word64 → Word64) (base value : Word64) (size : Nat) (big : Bool) :
    Nat → Word64 → UInt8
  | 0 => memory
  | n + 1 => fun address =>
    if address = view (base + BitVec.ofNat 64 n) then storedByte value size n big
    else storeUpTo memory view base value size big n address

private theorem foldl_store (memory : Word64 → UInt8) (view : Word64 → Word64) (base value : Word64) (size : Nat) (big : Bool)
    (n : Nat) :
    (List.range n).foldl (fun memory index address =>
      if address = view (base + BitVec.ofNat 64 index) then
        UInt8.ofNat ((value >>> ((if big then size - 1 - index else index) * 8)).toNat % 256)
      else memory address) memory = storeUpTo memory view base value size big n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; rfl

theorem denoteStore_eq (memory : Word64 → UInt8) (view : Word64 → Word64) (base value : Word64) (size : Nat) (big : Bool) :
    denoteStore memory view base value size big = storeUpTo memory view base value size big size := by
  unfold denoteStore
  exact foldl_store _ _ _ _ _ _ _

private theorem storeUpTo_other {memory : Word64 → UInt8} {view : Word64 → Word64} {base value : Word64} {size : Nat} {big : Bool}
    {n : Nat} {address : Word64} (h : ∀ k, k < n → address ≠ view (base + BitVec.ofNat 64 k)) :
    storeUpTo memory view base value size big n address = memory address := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [storeUpTo, h n (by omega), ↓reduceIte]
    exact ih fun k hk => h k (by omega)

/-- An address that one index of a store goes to, and no later one, has its byte. -/
private theorem storeUpTo_at {memory : Word64 → UInt8} {view : Word64 → Word64} {base value : Word64} {size : Nat} {big : Bool}
    {n j : Nat} (hj : j < n) (hne : ∀ k, j < k → k < n → view (base + BitVec.ofNat 64 j) ≠ view (base + BitVec.ofNat 64 k)) :
    storeUpTo memory view base value size big n (view (base + BitVec.ofNat 64 j)) = storedByte value size j big := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hjn : j = n
    · subst hjn
      simp [storeUpTo]
    · simp only [storeUpTo]
      rw [ite_cond_eq_false _ _ (eq_false (hne n (by omega) (by omega)))]
      exact ih (by omega) fun k h1 h2 => hne k h1 (by omega)

private theorem byteAt_stored {w : Nat} {v : Word64} {value : BitVec w} (hv : v.toNat = value.toNat) (shift : Nat) :
    UInt8.ofNat ((v >>> (shift * 8)).toNat % 256) = byteAt value.toNat shift := by
  simp only [byteAt, BitVec.toNat_ushiftRight, hv, Nat.mul_comm shift 8]

/-- `memStore` is `Memory.write`: after it, the window of the machine holds what `Memory.write` makes of the memory, in
either byte order, also across the end of the address space. -/
theorem memStore_correct {machine : Machine} {width size : Nat} {cells updated : Bap.Memory width} {address : BitVec width}
    {valueWidth : Nat} {value : BitVec valueWidth} {endian : Endian} {base stored : Word64} (hs : PagesSized cells)
    (hview : ViewOf machine width) (hw : width ≤ 64) (hwin : WindowOf machine.memory cells)
    (hsize : size ≤ 2 ^ width) (hbase : base = address.setWidth 64) (hstored : stored.toNat = value.toNat)
    (hwrite : Bap.Memory.write cells address value endian size = .ok updated) :
    WindowOf (denoteStore machine.memory machine.view base stored size (endian == .big)) updated := by
  have hvw : size * 8 = valueWidth := by
    by_cases hne : size * 8 = valueWidth
    · exact hne
    · rw [write_error_of_ne value endian hne] at hwrite
      simp at hwrite
  rw [write_eq hvw endian] at hwrite
  simp only [Except.ok.injEq] at hwrite
  subst hwrite
  subst hbase
  intro target
  rw [denoteStore_eq]
  have hdata : (ByteArray.mk (image value endian size).toArray).size = size := by
    show (image value endian size).toArray.size = size
    simp [image]
  have hlt2 : size < 2 ^ 64 + 1 := by have := pow_le_64 hw; omega
  by_cases hin : ∃ j, j < size ∧ target = address + BitVec.ofNat width j
  · obtain ⟨j0, hj0, htarget⟩ := hin
    -- the offsets are distinct, so that exactly one of them goes to the target
    have hoff : ∀ k, k < size → k < 2 ^ 64 := fun k hk => by have := pow_le_64 hw; omega
    have hview' : ∀ k, k < size → machine.view (address.setWidth 64 + BitVec.ofNat 64 k) =
        (address + BitVec.ofNat width k).setWidth 64 := fun k hk => view_add hview hw address k (hoff k hk)
    have hsetw : ∀ x y : BitVec width, x.setWidth 64 = y.setWidth 64 → x = y := by
      intro x y he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_setWidth] at this
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (pow_le_64 hw)),
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le y.isLt (pow_le_64 hw))] at this
      exact BitVec.eq_of_toNat_eq this
    have hdistinct : ∀ k, j0 < k → k < size → machine.view (address.setWidth 64 + BitVec.ofNat 64 j0) ≠
        machine.view (address.setWidth 64 + BitVec.ofNat 64 k) := by
      intro k h1 h2 he
      rw [hview' j0 hj0, hview' k h2] at he
      have he := congrArg BitVec.toNat (hsetw _ _ he)
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod] at he
      have hkj : k - j0 < 2 ^ width := by omega
      have hdvd : 2 ^ width ∣ k - j0 := by
        have h3 : (address.toNat + j0) % 2 ^ width = (address.toNat + k) % 2 ^ width := he
        have := Nat.sub_mod_eq_zero_of_mod_eq h3.symm
        have h4 : address.toNat + k - (address.toNat + j0) = k - j0 := by omega
        rw [h4] at this
        exact Nat.dvd_of_mod_eq_zero this
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    have hat := storeUpTo_at (memory := machine.memory) (value := stored) (size := size) (big := endian == .big) hj0 hdistinct
    rw [hview' j0 hj0, ← htarget] at hat
    rw [hat, readByte_writeRegion_inside hs _ _ (by rw [hdata]; exact hsize) (j := j0) (by rw [hdata]; exact hj0) target
      (by rw [htarget, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod])]
    show _ = (ByteArray.mk (image value endian size).toArray)[j0]!
    have hget : (ByteArray.mk (image value endian size).toArray)[j0]! = (image value endian size)[j0]! := by
      have hlen : j0 < (image value endian size).length := by simp [image, hj0]
      show (ByteArray.mk (image value endian size).toArray)[j0]! = _
      rw [getElem!_pos (ByteArray.mk _) j0 (by rw [hdata]; exact hj0), getElem!_pos _ j0 hlen]
      rfl
    rw [hget, getElem!_pos _ j0 (by simp [image, hj0])]
    simp only [image, List.getElem_map, List.getElem_range, storedByte]
    cases endian <;> simp only [reduceCtorEq, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] <;>
      first
        | exact byteAt_stored hstored _
        | (simp; exact byteAt_stored hstored _)
  · have hother : ∀ k, k < size → target.setWidth 64 ≠ machine.view (address.setWidth 64 + BitVec.ofNat 64 k) := by
      intro k hk he
      rw [view_add hview hw address k (by have := pow_le_64 hw; omega)] at he
      apply hin
      refine ⟨k, hk, ?_⟩
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_setWidth] at this
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le target.isLt (pow_le_64 hw)),
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (pow_le_64 hw))] at this
      exact BitVec.eq_of_toNat_eq this
    rw [storeUpTo_other hother, hwin, readByte_writeRegion_outside hs]
    intro j hj he
    apply hin
    rw [hdata] at hj
    refine ⟨j, hj, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [← he, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod]

end MemoryOps

/-! ### Statements on the machine

`Run` is a run of a program of operations, with its labels and branches: what `bap_jit.cpp` makes of them, by
obligation 1 of `Bap.Jit`. `lowerStatements_correct` says that the operations of a lowered program, from a machine that
holds the environment, end the way `Bil.execProgram` ends, or in the one way the interpreter does not have, a loop
that runs out of its budget of iterations. -/

section Statements

open Bap.Primus.Lifted Bap.Proofs.Primus
open Proofs.Core.MemoryLaws
open_private Bap.Primus.Lifted Bap.Primus.Lifted Lowering Lowering.ops Lowering.layout Lowering.nextSlot Lowering.memory
  Lowering.effectSlot Lowering.nextLabel Lowering.next Lowering.written Lowering.outputs Lowering.inputs Operand Operand.slot
  Operand.width lowerExp lowerMove lowerStmt lowerStatements setEffect temporary jumpConstant jumpSlot immediate useMemory
  useMemoryAt writeVar slot widthOf wrapSafe recordWrite addressOf readVar readsMemory
open_private Bap.Bil.Eval Bap.Bil expectMemory
open_private Bap.Proofs.Primus Bap.Proofs.Primus obind pairwise_same lookup_bind_same lookup_bind_other writeVar_inv
  slot_fields asBits_ok bind_ok SameButInputs SameButInputs.layout

/-- The operations after a label. -/
def afterLabel : List Op → Nat → Option (List Op)
  | [], _ => none
  | .label l :: rest, id => if l = id then some rest else afterLabel rest id
  | _ :: rest, id => afterLabel rest id

def labelsOf (ops : List Op) : List Nat :=
  ops.filterMap fun op =>
    match op with
    | .label l => some l
    | _ => none

@[simp] theorem labelsOf_nil : labelsOf [] = [] := rfl
@[simp] theorem labelsOf_append (a b : List Op) : labelsOf (a ++ b) = labelsOf a ++ labelsOf b := by
  simp [labelsOf, List.filterMap_append]
@[simp] theorem labelsOf_label (id : Nat) (rest : List Op) : labelsOf (.label id :: rest) = id :: labelsOf rest := rfl
private theorem labelsOf_other {op : Op} (h : ∀ l, op ≠ .label l) (rest : List Op) : labelsOf (op :: rest) = labelsOf rest := by
  cases op <;> first | rfl | exact absurd rfl (h _)

/-- With the labels of a program distinct, a label goes to what follows it. -/
theorem afterLabel_split {ops rest : List Op} {id : Nat} (before : List Op) (h : ops = before ++ .label id :: rest)
    (hn : (labelsOf ops).Nodup) : afterLabel ops id = some rest := by
  subst h
  induction before with
  | nil => simp [afterLabel]
  | cons head tail ih =>
    rw [List.cons_append]
    cases head with
    | label l =>
      rw [List.cons_append, labelsOf_label] at hn
      obtain ⟨hmem, hrest⟩ := List.nodup_cons.1 hn
      have hne : l ≠ id := by
        intro he
        subst he
        exact hmem (by simp)
      simp only [afterLabel, hne, ↓reduceIte]
      exact ih hrest
    | _ =>
      all_goals
        simp only [afterLabel]
        apply ih
        rw [List.cons_append, labelsOf_other (by intro l; simp)] at hn
        exact hn

/-- A configuration of a run: the operations to go, and the machine. -/
abbrev Cfg := List Op × Machine

/-- What runs after one step. A run ends at a `jump` or a `jumpSlot`. A code site does not occur in statements. -/
def nextCfg (program : List Op) : Cfg → Option Cfg
  | ([], _) => none
  | (op :: rest, machine) =>
    match op with
    | .goto id => (afterLabel program id).map fun target => (target, machine)
    | .branch condition yes no =>
      (afterLabel program (if machine.slots condition ≠ 0 then yes else no)).map fun target => (target, machine)
    | .jump _ | .jumpSlot _ | .code .. => none
    | _ => some (rest, Bap.Proofs.Primus.step machine op)

/-- A run, which `nextCfg` makes deterministic. -/
inductive Run (program : List Op) : Cfg → Cfg → Prop
  | refl (cfg : Cfg) : Run program cfg cfg
  | step {first second last : Cfg} : nextCfg program first = some second → Run program second last → Run program first last

theorem Run.trans {program : List Op} {a b c : Cfg} (h1 : Run program a b) (h2 : Run program b c) : Run program a c := by
  induction h1 with
  | refl => exact h2
  | step hn _ ih => exact .step hn (ih h2)

/-- The operations that go on with the next one. -/
def isLinear : Op → Bool
  | .goto _ | .branch .. | .jump _ | .jumpSlot _ | .code .. => false
  | _ => true

theorem Run.linear {program : List Op} {op : Op} (h : isLinear op = true) (rest : List Op) (machine : Machine) :
    Run program (op :: rest, machine) (rest, Bap.Proofs.Primus.step machine op) := by
  refine .step ?_ (.refl _)
  cases op <;> first | rfl | (simp [isLinear] at h)

theorem Run.ops {program new : List Op} (h : ∀ op ∈ new, isLinear op = true) (tail : List Op) (machine : Machine) :
    Run program (new ++ tail, machine) (tail, runOps machine new) := by
  induction new generalizing machine with
  | nil => exact .refl _
  | cons op rest ih =>
    exact (Run.linear (h op List.mem_cons_self) _ _).trans (ih (fun o ho => h o (List.mem_cons_of_mem _ ho)) _)

private theorem linear_of_expression {op : Op} (h : isExpressionOp op = true) : isLinear op = true := by
  cases op <;> first | rfl | (simp [isExpressionOp] at h)

theorem Run.goto {program target tail : List Op} {id : Nat} (h : afterLabel program id = some target) (machine : Machine) :
    Run program (.goto id :: tail, machine) (target, machine) :=
  .step (by simp [nextCfg, h]) (.refl _)

theorem Run.branch {program target tail : List Op} {condition yes no : Nat} {machine : Machine}
    (h : afterLabel program (if machine.slots condition ≠ 0 then yes else no) = some target) :
    Run program (.branch condition yes no :: tail, machine) (target, machine) :=
  .step (by simp only [nextCfg, h, Option.map_some]) (.refl _)

/-- The memory that the machine holds. -/
def MemoryInv (machine : Machine) (width : Nat) (cells : Bap.Memory width) : Prop :=
  PagesSized cells ∧ width ≤ 64 ∧ 8 ≤ 2 ^ width ∧ ViewOf machine width ∧ WindowOf machine.memory cells

/-- The machine holds the environment, for the variables of a lowering. -/
structure Agrees (env : Bil.Env) (machine : Machine) (global : Lowering) : Prop where
  slots : SlotsAgree env machine (Lowering.layout global)
  memory : ∀ var, Lowering.memory global = some var → ∀ (width : Nat) (cells : Bap.Memory width),
    Bil.lookup env var = .ok (.memory cells) → MemoryInv machine width cells

/-- A lowering on the way to a global one. -/
structure Sub (lowering global : Lowering) : Prop where
  mono : ∀ b ∈ Lowering.layout lowering, b ∈ Lowering.layout global
  later : ∀ b ∈ Lowering.layout global, b ∈ Lowering.layout lowering ∨ Lowering.nextSlot lowering ≤ b.2
  memory : ∀ var, Lowering.memory lowering = some var → Lowering.memory global = some var

theorem Sub.refl (lowering : Lowering) : Sub lowering lowering :=
  ⟨fun _ h => h, fun _ h => Or.inl h, fun _ h => h⟩

/-- What lowering a statement does to the lowering state. -/
structure Appended (first second : Lowering) (new : List Op) : Prop where
  ops : Lowering.ops second = Lowering.ops first ++ new
  next : Lowering.nextSlot first ≤ Lowering.nextSlot second
  mono : ∀ b ∈ Lowering.layout first, b ∈ Lowering.layout second
  later : ∀ b ∈ Lowering.layout second, b ∈ Lowering.layout first ∨ Lowering.nextSlot first ≤ b.2
  wf : LayoutWF second
  memory : ∀ var, Lowering.memory first = some var → Lowering.memory second = some var
  label : Lowering.nextLabel first ≤ Lowering.nextLabel second
  labels : (labelsOf new).Nodup
  labelRange : ∀ l ∈ labelsOf new, Lowering.nextLabel first ≤ l ∧ l < Lowering.nextLabel second
  effect : Lowering.effectSlot second = Lowering.effectSlot first

theorem Appended.refl {lowering : Lowering} (wf : LayoutWF lowering) : Appended lowering lowering [] where
  ops := by simp
  next := Nat.le_refl _
  mono := fun _ h => h
  later := fun _ h => Or.inl h
  wf := wf
  memory := fun _ h => h
  label := Nat.le_refl _
  labels := by simp
  labelRange := by simp
  effect := rfl

theorem Appended.trans {a b c : Lowering} {x y : List Op} (h1 : Appended a b x) (h2 : Appended b c y) : Appended a c (x ++ y) where
  ops := by rw [h2.ops, h1.ops, List.append_assoc]
  next := Nat.le_trans h1.next h2.next
  mono := fun _ h => h2.mono _ (h1.mono _ h)
  later := fun b hb => by
    rcases h2.later b hb with h | h
    · rcases h1.later b h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · exact Or.inr (Nat.le_trans h1.next h)
  wf := h2.wf
  memory := fun _ h => h2.memory _ (h1.memory _ h)
  label := Nat.le_trans h1.label h2.label
  labels := by
    rw [labelsOf_append]
    refine List.nodup_append.2 ⟨h1.labels, h2.labels, ?_⟩
    intro p hp q hq he
    subst he
    have := (h1.labelRange p hp).2
    have := (h2.labelRange p hq).1
    omega
  labelRange := by
    intro l hl
    rw [labelsOf_append] at hl
    rcases List.mem_append.1 hl with h | h
    · have := h1.labelRange l h
      have := h2.label
      omega
    · have := h2.labelRange l h
      have := h1.label
      omega
  effect := by rw [h2.effect, h1.effect]

private theorem labelsOf_expression {new : List Op} (h : ∀ op ∈ new, isExpressionOp op = true) : labelsOf new = [] := by
  induction new with
  | nil => rfl
  | cons op rest ih =>
    have hop := h op List.mem_cons_self
    have hrest := ih fun o ho => h o (List.mem_cons_of_mem _ ho)
    cases op <;> first | (exfalso; simpa [isExpressionOp] using hop) | (rw [labelsOf_other (by intro l; simp)]; exact hrest)

theorem _root_.Bap.Proofs.Primus.Extends.appended {first second : Lowering} {new : List Op} (h : Extends first second new) (wf : LayoutWF first) :
    Appended first second new where
  ops := h.ops
  next := h.next
  mono := by
    obtain ⟨extra, he, _⟩ := h.extra
    intro b hb
    rw [he]
    exact List.mem_append_left _ hb
  later := by
    obtain ⟨extra, he, hx⟩ := h.extra
    intro b hb
    rw [he] at hb
    rcases List.mem_append.1 hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr (hx _ hb).1
  wf := h.wf wf
  memory := h.memory
  label := by rw [h.nextLabel]; exact Nat.le_refl _
  labels := by rw [labelsOf_expression h.pure]; simp
  labelRange := by rw [labelsOf_expression h.pure]; simp
  effect := h.effect

theorem Sub.before {first second global : Lowering} {new : List Op} (hs : Sub second global) (ha : Appended first second new) :
    Sub first global where
  mono := fun b hb => hs.mono b (ha.mono b hb)
  later := fun b hb => by
    rcases hs.later b hb with h | h
    · exact ha.later b h
    · exact Or.inr (Nat.le_trans ha.next h)
  memory := fun v hv => hs.memory v (ha.memory v hv)

/-- Slots that a part of a run does not write. -/
def Frames (low high : Nat) (global : Lowering) (first second : Machine) : Prop :=
  second.view = first.view ∧ ∀ slot, (slot < low ∨ high ≤ slot) → (∀ var, (var, slot) ∉ Lowering.layout global) →
    second.slots slot = first.slots slot

theorem Frames.refl (low high : Nat) (global : Lowering) (machine : Machine) : Frames low high global machine machine :=
  ⟨rfl, fun _ _ _ => rfl⟩

theorem Frames.trans {low high : Nat} {global : Lowering} {a b c : Machine} (h1 : Frames low high global a b)
    (h2 : Frames low high global b c) : Frames low high global a c :=
  ⟨h2.1.trans h1.1, fun slot hs hv => (h2.2 slot hs hv).trans (h1.2 slot hs hv)⟩

theorem Frames.weaken {low high low' high' : Nat} {global : Lowering} {a b : Machine} (h : Frames low high global a b)
    (hl : low' ≤ low) (hh : high ≤ high') : Frames low' high' global a b :=
  ⟨h.1, fun slot hs hv => h.2 slot (by omega) hv⟩

/-- A run that ends in a jump. -/
def Returns (program : List Op) (cfg : Cfg) (value : Word64) (machine : Machine) : Prop :=
  ∃ rest, (∃ target : UInt64, Run program cfg (.jump target :: rest, machine) ∧ value = target.toBitVec) ∨
    (∃ slot, Run program cfg (.jumpSlot slot :: rest, machine) ∧ value = machine.slots slot)

/-- A run that a loop ended, out of iterations. -/
def Exhausts (program : List Op) (cfg : Cfg) (effect : Nat) : Prop :=
  ∃ target rest machine, Run program cfg (.jump target :: rest, machine) ∧ machine.slots effect = 2

/-- How a run of the operations of a statement ends, given what the interpreter says about it. -/
def Outcome (first second global : Lowering) (program : List Op) (cfg : Cfg) (tail : List Op) (effect : Nat)
    (terminated : Bool) (result : Bil.State × Bil.Effect) : Prop :=
  Exhausts program cfg effect ∨
    match result.2 with
    | .normal => terminated = false ∧ ∃ machine, Run program cfg (tail, machine) ∧ Agrees result.1.env machine global ∧
        Frames (Lowering.nextSlot first) (Lowering.nextSlot second) global cfg.2 machine
    | .jump target => ∃ value machine, Returns program cfg value machine ∧ Holds value target ∧
        machine.slots effect = 1 ∧ Agrees result.1.env machine global
    | _ => False

/-- What a run of a statement needs of where it runs. -/
structure Context (first second global : Lowering) (new : List Op) (program tail : List Op) (effect : Nat) : Prop where
  effectSlot : Lowering.effectSlot first = some effect
  effectLow : effect < Lowering.nextSlot first
  effectFree : ∀ var, (var, effect) ∉ Lowering.layout global
  wfGlobal : LayoutWF global
  sub : Sub second global
  split : ∃ pre, program = pre ++ new ++ tail
  distinct : (labelsOf program).Nodup

/-- A lowered statement, with the executions of it. -/
def LowerOK (first second : Lowering) (new : List Op) (terminated : Bool) (exec : Nat → Bil.State → Except String (Bil.State × Bil.Effect)) :
    Prop :=
  ∀ (fuel : Nat) (state : Bil.State) (result : Bil.State × Bil.Effect) (global : Lowering) (program tail : List Op) (effect : Nat)
    (machine : Machine), Context first second global new program tail effect → Agrees state.env machine global →
    exec fuel state = .ok result → Outcome first second global program (new ++ tail, machine) tail effect terminated result

/-! Inversions and frames. -/

private theorem exec_move {fuel : Nat} {state : Bil.State} {var : Bap.Var} {value : Bil.Exp} {result : Bil.State × Bil.Effect}
    (h : Bil.execStmt fuel state (.move var value) = .ok result) :
    ∃ v, Bil.evalExp state.env value = .ok v ∧ result = ({ env := Bil.bind state.env var v }, .normal) := by
  cases fuel with
  | zero => simp [Bil.execStmt] at h
  | succ fuel =>
    simp only [Bil.execStmt, Bil.execExp] at h
    obtain ⟨v, h1, h2⟩ := bind_ok h
    simp only [Except.ok.injEq] at h2
    exact ⟨v, h1, h2.symm⟩

private theorem exec_jmp {fuel : Nat} {state : Bil.State} {target : Bil.Exp} {result : Bil.State × Bil.Effect}
    (h : Bil.execStmt fuel state (.jmp target) = .ok result) :
    ∃ (width : Nat) (bits : BitVec width), Bil.evalExp state.env target = .ok (.bits bits) ∧
      result = (state, .jump bits) := by
  cases fuel with
  | zero => simp [Bil.execStmt] at h
  | succ fuel =>
    simp only [Bil.execStmt, Bil.execExp] at h
    obtain ⟨v, h1, h2⟩ := bind_ok h
    obtain ⟨r, h3, h4⟩ := bind_ok h2
    simp only [Except.ok.injEq] at h4
    exact ⟨r.1, r.2, by rw [h1, asBits_ok h3], h4.symm⟩

/-- A condition, as a slot holds it. -/
private theorem holds_condition {slot : Word64} {condition : BitVec 1} (h : Holds slot condition) :
    (slot ≠ 0) ↔ condition = 1 := by
  have hlt := condition.isLt
  have h : slot.toNat = condition.toNat := h
  constructor
  · intro hne
    apply BitVec.eq_of_toNat_eq
    have : slot.toNat ≠ 0 := fun he => hne (BitVec.eq_of_toNat_eq (by simpa using he))
    rw [show (1 : BitVec 1).toNat = 1 from rfl]
    omega
  · intro he hs
    subst he
    subst hs
    simp at h

private theorem exec_ifElse {fuel : Nat} {state : Bil.State} {condition : Bil.Exp} {yes no : Bil.Program}
    {result : Bil.State × Bil.Effect} (h : Bil.execStmt fuel state (.ifElse condition yes no) = .ok result) :
    ∃ (fuel' : Nat) (bit : BitVec 1), Bil.evalExp state.env condition = .ok (.bits bit) ∧
      Bil.execProgram fuel' state (if bit = 1 then yes else no) = .ok result := by
  cases fuel with
  | zero => simp [Bil.execStmt] at h
  | succ fuel =>
    simp only [Bil.execStmt, Bil.execExp] at h
    obtain ⟨v, h1, h2⟩ := bind_ok h
    obtain ⟨⟨width, bit⟩, h3, h4⟩ := bind_ok h2
    simp only at h4
    split at h4
    · next hw =>
      subst hw
      exact ⟨fuel, bit, by rw [h1, asBits_ok h3], h4⟩
    · simp at h4

private theorem exec_while {fuel : Nat} {state : Bil.State} {condition : Bil.Exp} {body : Bil.Program}
    {result : Bil.State × Bil.Effect} (h : Bil.execStmt (fuel + 1) state (.while condition body) = .ok result) :
    ∃ bit : BitVec 1, Bil.evalExp state.env condition = .ok (.bits bit) ∧
      if bit = 1 then
        ∃ inner, Bil.execProgram fuel state body = .ok inner ∧
          match inner.2 with
          | .normal => Bil.execStmt fuel inner.1 (.while condition body) = .ok result
          | other => result = (inner.1, other)
      else result = (state, .normal) := by
  simp only [Bil.execStmt, Bil.execExp] at h
  obtain ⟨v, h1, h2⟩ := bind_ok h
  obtain ⟨⟨width, bit⟩, h3, h4⟩ := bind_ok h2
  simp only at h4
  split at h4
  · next hw =>
    subst hw
    refine ⟨bit, by rw [h1, asBits_ok h3], ?_⟩
    simp only at h4
    split at h4
    · next hb =>
      obtain ⟨⟨next, effect⟩, h5, h6⟩ := bind_ok h4
      rw [if_pos hb]
      refine ⟨(next, effect), h5, ?_⟩
      cases effect <;> simp_all
    · next hb =>
      rw [if_neg hb]
      simpa using h4.symm
  · simp at h4

private theorem exec_cons {fuel : Nat} {state : Bil.State} {stmt : Bil.Stmt} {rest : Bil.Program}
    {result : Bil.State × Bil.Effect} (h : Bil.execProgram fuel state (stmt :: rest) = .ok result) :
    ∃ (fuel' : Nat) (first : Bil.State × Bil.Effect), Bil.execStmt fuel' state stmt = .ok first ∧
      match first.2 with
      | .normal => Bil.execProgram fuel' first.1 rest = .ok result
      | other => result = (first.1, other) := by
  cases fuel with
  | zero => simp [Bil.execProgram] at h
  | succ fuel =>
    simp only [Bil.execProgram] at h
    obtain ⟨⟨next, effect⟩, h1, h2⟩ := bind_ok h
    refine ⟨fuel, (next, effect), h1, ?_⟩
    cases effect <;> simp_all

private theorem exec_nil {fuel : Nat} {state : Bil.State} {result : Bil.State × Bil.Effect}
    (h : Bil.execProgram fuel state [] = .ok result) : result = (state, .normal) := by
  cases fuel with
  | zero => simp [Bil.execProgram] at h
  | succ fuel =>
    simp only [Bil.execProgram, Except.ok.injEq] at h
    exact h.symm

theorem Agrees.memoryAgrees {env : Bil.Env} {machine : Machine} {global lowering : Lowering} (h : Agrees env machine global)
    (hs : Sub lowering global) : MemoryAgrees env machine lowering := by
  intro var hv width cells hl address offset ho
  obtain ⟨_, hw, _, hview, hwin⟩ := h.memory var (hs.memory var hv) width cells hl
  exact memoryAgrees_of_window hview hw hwin address offset ho

/-- Operations of an expression write temporaries. -/
theorem Agrees.after {env : Bil.Env} {machine : Machine} {global first second : Lowering} {new : List Op}
    (h : Agrees env machine global) (he : Extends first second new) (hs : Sub second global) :
    Agrees env (runOps machine new) global where
  slots := h.slots.after he hs.later
  memory := by
    intro var hv width cells hl
    obtain ⟨h1, h2, h3, hview, hwin⟩ := h.memory var hv width cells hl
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · intro address
      rw [runOps_view]
      exact hview address
    · rw [WindowOf, runOps_memory he.pure]
      exact hwin

theorem _root_.Bap.Proofs.Primus.Extends.frames {first second global : Lowering} {new : List Op} (he : Extends first second new) (hs : Sub second global)
    (machine : Machine) : Frames (Lowering.nextSlot first) (Lowering.nextSlot second) global machine (runOps machine new) := by
  refine ⟨runOps_view _ _, ?_⟩
  intro slot hslot _
  apply he.frame
  rcases hslot with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- The slot of an operand with a value is not a slot that its operations leave alone and that holds anything else,
so that it is not the effect slot, which they do not write and which belongs to no variable. -/
theorem operand_ne_effect {first second : Lowering} {new : List Op} {operand : Operand} {exp : Bil.Exp} {env : Bil.Env}
    {machine : Machine} {width : Nat} {bits : BitVec width} {effect : Nat}
    (he : Extends first second new)
    (hval : ∀ (env : Bil.Env) (machine : Machine), SlotsAgree env machine (Lowering.layout second) → MemoryAgrees env machine second →
      ∀ (width : Nat) (bits : BitVec width), Bil.evalExp env exp = .ok (.bits bits) →
        Operand.width operand = width ∧ Holds ((runOps machine new).slots (Operand.slot operand)) bits)
    (hs : SlotsAgree env machine (Lowering.layout second)) (hm : MemoryAgrees env machine second)
    (hev : Bil.evalExp env exp = .ok (.bits bits)) (hlow : effect < Lowering.nextSlot first)
    (hfree : ∀ var, (var, effect) ∉ Lowering.layout second) : Operand.slot operand ≠ effect := by
  intro heq
  subst heq
  have h1 := (hval env machine hs hm width bits hev).2
  let other : Machine := { machine with slots := fun slot => if slot = Operand.slot operand then machine.slots slot + 1 else machine.slots slot }
  have hsOther : SlotsAgree env other (Lowering.layout second) := by
    intro binding hb value hl
    obtain ⟨w, x, a, b, c⟩ := hs binding hb value hl
    refine ⟨w, x, a, b, ?_⟩
    have hne : binding.2 ≠ Operand.slot operand := by
      intro he'
      apply hfree binding.1
      have : binding = (binding.1, Operand.slot operand) := Prod.ext rfl he'
      rw [← this]
      exact hb
    show Holds (if binding.2 = Operand.slot operand then _ else _) x
    rw [if_neg hne]
    exact c
  have hmOther : MemoryAgrees env other second := by
    intro var hv w cells hl address offset ho
    exact hm var hv w cells hl address offset ho
  have h2 := (hval env other hsOther hmOther width bits hev).2
  have f1 := he.frame machine (Or.inl hlow)
  have f2 := he.frame other (Or.inl hlow)
  have h1 : ((runOps machine new).slots (Operand.slot operand)).toNat = bits.toNat := h1
  have h2 : ((runOps other new).slots (Operand.slot operand)).toNat = bits.toNat := h2
  rw [f1] at h1
  rw [f2] at h2
  have h3 : other.slots (Operand.slot operand) = machine.slots (Operand.slot operand) + 1 := by simp [other]
  rw [h3, BitVec.toNat_add] at h2
  have hlt := (machine.slots (Operand.slot operand)).isLt
  rw [← h1, show (1 : Word64).toNat = 1 from rfl] at h2
  have : (machine.slots (Operand.slot operand)).toNat + 1 < 2 ^ 64 ∨ (machine.slots (Operand.slot operand)).toNat + 1 = 2 ^ 64 := by omega
  rcases this with h | h
  · rw [Nat.mod_eq_of_lt h] at h2
    omega
  · rw [h, Nat.mod_self] at h2
    omega

private theorem evalBin_bits {op : Bil.BinOp} {left right : Σ width, BitVec width} {value : Bap.Value}
    (h : Bil.evalBin op left right = .ok value) : ∃ (width : Nat) (bits : BitVec width), value = .bits bits := by
  obtain ⟨wl, l⟩ := left
  obtain ⟨wr, r⟩ := right
  simp only [Bil.evalBin] at h
  split at h
  · cases op <;> simp only [Except.ok.injEq] at h <;> exact ⟨_, _, h.symm⟩
  · simp at h

/-- A lowered expression has bits for a value, if the variables of the lowering have. -/
theorem lowered_value_bits (exp : Bil.Exp) : ∀ {first second : Lowering} {operand : Operand}, LayoutWF first →
    lowerExp first exp = some (second, operand) → ∀ (env : Bil.Env) (machine : Machine),
    SlotsAgree env machine (Lowering.layout second) → ∀ value, Bil.evalExp env exp = .ok value →
    ∃ (width : Nat) (bits : BitVec width), value = .bits bits := by
  induction exp with
  | int value =>
    intro first second operand wf h env machine hs v hev
    simp only [Bil.evalExp, Except.ok.injEq] at hev
    exact ⟨_, _, hev.symm⟩
  | var var =>
    intro first second operand wf h env machine hs v hev
    rw [lowerExp] at h
    obtain ⟨width, hw, h⟩ := obind h
    obtain ⟨⟨result, index⟩, hrv, h⟩ := obind h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hindex, hsame⟩ := readVar_inv hrv
    subst hindex
    have hmem : (var, (slot first var).2) ∈ Lowering.layout result := by
      have hl := hsame.layout
      first
        | (rw [← hl]; exact slot_mem_layout first var)
        | (rw [hl]; exact slot_mem_layout first var)
    obtain ⟨w, x, hv, _, _⟩ := hs _ hmem v (by simpa [Bil.evalExp] using hev)
    exact ⟨w, x, hv⟩
  | load memory address endian size _ _ =>
    intro first second operand wf h env machine hs v hev
    obtain ⟨_, _, _, _, _, hv⟩ := evalExp_load_inv hev
    exact ⟨_, _, hv⟩
  | store memory address value endian size _ _ _ =>
    intro first second operand wf h
    rw [lowerExp] at h
    · simp at h
    all_goals (intros; simp_all)
  | bin op left right _ _ =>
    intro first second operand wf h env machine hs v hev
    obtain ⟨_, _, _, _, _, _, hb⟩ := evalExp_bin_inv hev
    exact evalBin_bits hb
  | un op value _ =>
    intro first second operand wf h env machine hs v hev
    obtain ⟨_, _, _, hv⟩ := evalExp_un_inv hev
    cases op <;> exact ⟨_, _, hv⟩
  | cast kind target value _ =>
    intro first second operand wf h env machine hs v hev
    obtain ⟨_, _, _, hv⟩ := evalExp_cast_inv hev
    cases kind
    case high =>
      obtain ⟨_, _, hv⟩ := hv
      exact ⟨_, _, hv⟩
    all_goals exact ⟨_, _, hv⟩
  | letIn var value body _ _ =>
    intro first second operand wf h
    rw [lowerExp] at h
    · simp at h
    all_goals (intros; simp_all)
  | ite condition yes no _ ihy ihn =>
    intro first second operand wf h env machine hs v hev
    obtain ⟨bit, _, hb⟩ := evalExp_ite_inv hev
    rw [lowerExp] at h
    have hpure : (readsMemory yes || readsMemory no) = false := by
      by_cases hc : (readsMemory yes || readsMemory no) = true
      · simp [hc] at h
      · simpa using hc
    simp only [hpure, Bool.false_eq_true, ite_false, pure_bind] at h
    obtain ⟨⟨l1, o1⟩, h1, h⟩ := obind h
    obtain ⟨⟨l2, o2⟩, h2, h⟩ := obind h
    obtain ⟨⟨l3, o3⟩, h3, h⟩ := obind h
    obtain ⟨_, he1, _⟩ := lowerExp_correct condition wf h1
    have wf1 := he1.wf wf
    obtain ⟨_, he2, _⟩ := lowerExp_correct yes wf1 h2
    have wf2 := he2.wf wf1
    obtain ⟨_, he3, _⟩ := lowerExp_correct no wf2 h3
    have hlayout : Lowering.layout second = Lowering.layout l3 := by
      split at h
      · simp at h
      · simp only [temporary, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
    rw [hlayout] at hs
    have m2 := (he2.appended wf1).mono
    have m3 := (he3.appended wf2).mono
    split at hb
    · exact ihy wf1 h2 env machine (hs.mono fun b hb => m3 b hb) v hb
    · exact ihn wf2 h3 env machine hs v hb
  | extract high low value _ =>
    intro first second operand wf h env machine hs v hev
    obtain ⟨_, _, _, _, _, hv⟩ := evalExp_extract_inv hev
    exact ⟨_, _, hv⟩
  | concat left right _ _ =>
    intro first second operand wf h
    rw [lowerExp] at h
    · simp at h
    all_goals (intros; simp_all)
  | unknown message typ =>
    intro first second operand wf h
    rw [lowerExp] at h
    · simp at h
    all_goals (intros; simp_all)

private theorem MemoryInv.write {machine : Machine} {width : Nat} {cells : Bap.Memory width} (h : MemoryInv machine width cells)
    (slot : Nat) (value : Word64) : MemoryInv (machine.write slot value) width cells := h

private theorem writeVar_fields {first second : Lowering} {var : Bap.Var} {index : Nat} (h : writeVar first var = some (second, index)) :
    Lowering.nextLabel second = Lowering.nextLabel first ∧ Lowering.effectSlot second = Lowering.effectSlot first := by
  cases hw : widthOf var with
  | none => simp [writeVar, hw] at h
  | some width =>
    simp only [writeVar, hw, Option.bind_eq_bind, bind, pure, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := slot_fields first var
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨f5, f6⟩

/-- A move to a register. -/
theorem lowerMove_register_ok {first second : Lowering} {dst : Bap.Var} {value : Bil.Exp} {width : Nat} (wf : LayoutWF first)
    (hw : widthOf dst = some width) (h : lowerMove first dst value = some second) :
    ∃ new, Appended first second new ∧ LowerOK first second new false (fun fuel state => Bil.execStmt fuel state (.move dst value)) := by
  have htyp := (widthOf_some_iff dst width).1 hw
  rw [lowerMove] at h
  · obtain ⟨width', hw', h⟩ := obind h
    rw [hw] at hw'
    simp only [Option.some.injEq] at hw'
    subst hw'
    obtain ⟨⟨mid, operand⟩, h1, h⟩ := obind h
    obtain ⟨newE, he, hslot, h0, h64, hval⟩ := lowerExp_correct value wf h1
    have wfm := he.wf wf
    have hwidth : Operand.width operand = width := by
      by_cases hc : Operand.width operand = width
      · exact hc
      · simp [hc] at h
    simp only [hwidth, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨⟨after, index⟩, h2, h⟩ := obind h
    simp only [pure, Option.some.injEq] at h
    have fOps : Lowering.ops second = Lowering.ops after ++ [.move index (Operand.slot operand)] := by rw [← h]
    have fNext : Lowering.nextSlot second = Lowering.nextSlot after := by rw [← h]
    have fLayout : Lowering.layout second = Lowering.layout after := by rw [← h]
    have fMemory : Lowering.memory second = Lowering.memory after := by rw [← h]
    have fLabel : Lowering.nextLabel second = Lowering.nextLabel after := by rw [← h]
    have fEffect : Lowering.effectSlot second = Lowering.effectSlot after := by rw [← h]
    obtain ⟨hindex, hops, hnext, hlayout, hmemory⟩ := writeVar_inv h2
    obtain ⟨hlabel, heffect⟩ := writeVar_fields h2
    subst hindex
    have hext := slot_extends wfm dst
    have hwfs := slot_preserves_wf wfm dst
    have hdstMem : (dst, (slot mid dst).2) ∈ Lowering.layout (slot mid dst).1 := slot_mem_layout mid dst
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := slot_fields mid dst
    have a1 := he.appended wf
    have a2 : Appended mid second [.move (slot mid dst).2 (Operand.slot operand)] := {
      ops := by rw [fOps, hops]
      next := by rw [fNext, hnext]; exact hext.next
      mono := fun b hb => by rw [fLayout, hlayout]; exact slot_layout_mono mid dst b hb
      later := fun b hb => by
        rw [fLayout, hlayout] at hb
        exact (hext.appended wfm).later b hb
      wf := ⟨fun b hb => by
          rw [fNext, hnext]
          rw [fLayout, hlayout] at hb
          exact hwfs.bound b hb,
        by rw [fLayout, hlayout]; exact hwfs.slotsDistinct, by rw [fLayout, hlayout]; exact hwfs.varsDistinct⟩
      memory := fun v hv => by rw [fMemory, hmemory]; exact hv
      label := by rw [fLabel, hlabel]; exact Nat.le_refl _
      labels := by simp [labelsOf]
      labelRange := by simp [labelsOf]
      effect := by rw [fEffect, heffect] }
    refine ⟨newE ++ [.move (slot mid dst).2 (Operand.slot operand)], a1.trans a2, ?_⟩
    intro fuel state result global program tail effect machine ctx hag hex
    obtain ⟨v, hev, rfl⟩ := exec_move hex
    have hsubMid := ctx.sub.before a2
    have hsMid : SlotsAgree state.env machine (Lowering.layout mid) := hag.slots.mono hsubMid.mono
    obtain ⟨w, bits, rfl⟩ := lowered_value_bits value wf h1 state.env machine hsMid v hev
    obtain ⟨hwa, hvalue⟩ := hval state.env machine hsMid (hag.memoryAgrees hsubMid) w bits hev
    have hww : w = width := by rw [← hwa, hwidth]
    subst hww
    refine Or.inr ⟨rfl, runOps machine (newE ++ [.move (slot mid dst).2 (Operand.slot operand)]), ?_, ?_, ?_⟩
    · exact (Run.ops (new := newE ++ [.move (slot mid dst).2 (Operand.slot operand)]) (by
        intro op hop
        rcases List.mem_append.1 hop with hop | hop
        · exact linear_of_expression (he.pure op hop)
        · simp only [List.mem_singleton] at hop
          subst hop
          rfl) tail machine)
    · have hafter := hag.after he hsubMid
      have hdstG : (dst, (slot mid dst).2) ∈ Lowering.layout global := ctx.sub.mono _ (by
        rw [fLayout, hlayout]
        exact hdstMem)
      rw [runOps_append]
      simp only [runOps_cons, runOps_nil, Bap.Proofs.Primus.step]
      refine ⟨?_, ?_⟩
      · intro binding hb val hlookup
        by_cases hbd : binding.1 = dst
        · have hsame : binding = (dst, (slot mid dst).2) := pairwise_same ctx.wfGlobal.varsDistinct hb hdstG hbd
          subst hsame
          rw [lookup_bind_same] at hlookup
          simp only [Except.ok.injEq] at hlookup
          subst hlookup
          refine ⟨w, bits, rfl, hw, ?_⟩
          simp only [Machine.write_slots, ↓reduceIte]
          exact hvalue
        · rw [lookup_bind_other hbd] at hlookup
          obtain ⟨w', x, hv, hwb, hholds⟩ := hafter.slots _ hb _ hlookup
          refine ⟨w', x, hv, hwb, ?_⟩
          have hne : binding.2 ≠ (slot mid dst).2 := by
            intro e
            exact hbd (congrArg Prod.fst (pairwise_same ctx.wfGlobal.slotsDistinct hb hdstG e))
          simp only [Machine.write_slots, hne, ↓reduceIte]
          exact hholds
      · intro var hv w' cells hl
        have hne : var ≠ dst := by
          intro he'
          subst he'
          rw [lookup_bind_same] at hl
          simp at hl
        rw [lookup_bind_other hne] at hl
        exact MemoryInv.write (hafter.memory var hv w' cells hl) _ _
    · have hf := he.frames hsubMid machine
      rw [runOps_append]
      simp only [runOps_cons, runOps_nil, Bap.Proofs.Primus.step]
      refine ⟨hf.1, ?_⟩
      intro slot' hslot' hfree
      have hdstG : (dst, (slot mid dst).2) ∈ Lowering.layout global := ctx.sub.mono _ (by
        rw [fLayout, hlayout]
        exact hdstMem)
      have hne : slot' ≠ (slot mid dst).2 := fun e => hfree dst (e ▸ hdstG)
      simp only [Machine.write_slots, hne, ↓reduceIte]
      refine hf.2 slot' ?_ hfree
      rcases hslot' with h' | h'
      · exact Or.inl h'
      · refine Or.inr (Nat.le_trans a2.next h')
  all_goals (intros; simp_all)

private theorem evalExp_store_inv {env : Bil.Env} {memory address stored : Bil.Exp} {endian : Endian} {size : Nat}
    {value : Bap.Value} (h : Bil.evalExp env (.store memory address stored endian size) = .ok value) :
    ∃ (width : Nat) (cells updated : Bap.Memory width) (bits : BitVec width) (valueWidth : Nat) (data : BitVec valueWidth),
      Bil.evalExp env memory = .ok (.memory cells) ∧ Bil.evalExp env address = .ok (.bits bits) ∧
      Bil.evalExp env stored = .ok (.bits data) ∧ Bap.Memory.write cells bits data endian size = .ok updated ∧
      value = .memory updated := by
  rw [Bil.evalExp] at h
  obtain ⟨v, h1, h2⟩ := bind_ok h
  obtain ⟨m, h3, h4⟩ := bind_ok h2
  obtain ⟨w, cells⟩ := m
  obtain ⟨v', h5, h6⟩ := bind_ok h4
  obtain ⟨a, h7, h8⟩ := bind_ok h6
  obtain ⟨aw, bits⟩ := a
  obtain ⟨d, h9, h10⟩ := bind_ok h8
  obtain ⟨d', h11, h12⟩ := bind_ok h10
  obtain ⟨dw, data⟩ := d'
  simp only at h12
  split at h12
  · next hw =>
    subst hw
    obtain ⟨u, h13, h14⟩ := bind_ok h12
    simp only [Except.ok.injEq] at h14
    cases v <;> simp only [expectMemory, reduceCtorEq, Except.ok.injEq] at h3
    cases h3
    exact ⟨_, _, u, bits, dw, data, h1, by rw [h5, asBits_ok h7], by rw [h9, asBits_ok h11], h13, h14.symm⟩
  · simp at h12

private theorem useMemoryAt_fields {first second : Lowering} {var : Bap.Var} {size : Nat} (h : useMemoryAt first var size = some second) :
    Lowering.memory second = some var ∧ wrapSafe first var size = true := by
  have h0 := useMemoryAt_some h
  refine ⟨useMemory_some h0, ?_⟩
  unfold useMemoryAt at h
  split at h
  · assumption
  · simp at h

/-- A store to the memory of the block: `memStore` does what `Memory.write` does. -/
theorem lowerMove_store_ok {first second : Lowering} {dst : Bap.Var} {memory address stored : Bil.Exp} {endian : Endian} {size a c : Nat}
    (wf : LayoutWF first) (hty : dst.typ = .mem a c) (h : lowerMove first dst (.store memory address stored endian size) = some second) :
    ∃ new, Appended first second new ∧
      LowerOK first second new false (fun fuel state => Bil.execStmt fuel state (.move dst (.store memory address stored endian size))) := by
  unfold lowerMove at h
  rw [hty] at h
  dsimp only at h
  have hmv : memory = .var dst := by
    cases memory
    case var v =>
      by_cases hc : v = dst
      · rw [hc]
      · have hb : (v == dst) = false := by simpa using hc
        simp [hb] at h
    all_goals simp at h
  subst hmv
  simp only [beq_self_eq_true, ↓reduceIte] at h
  obtain ⟨var, hvar, h⟩ := obind h
  simp only [Option.some.injEq] at hvar
  subst hvar
  obtain ⟨l0, h0, h⟩ := obind h
  obtain ⟨hmem0, _⟩ := useMemoryAt_fields h0
  have he0 := useMemory_extends (useMemoryAt_some h0)
  have wf0 := he0.wf wf
  obtain ⟨⟨l1, o1⟩, h1, h⟩ := obind h
  obtain ⟨newA, heA, hsA, _, h64A, hvalA⟩ := lowerExp_correct address wf0 h1
  have wf1 := heA.wf wf0
  dsimp only at h
  obtain ⟨⟨l2, o2⟩, h2, h⟩ := obind h
  dsimp only at h
  obtain ⟨newS, heS, hsS, _, h64S, hvalS⟩ := lowerExp_correct stored wf1 h2
  have wf2 := heS.wf wf1
  have hchecks : (decide (size = 0) || decide (size > 8) || Operand.width o2 != size * 8 || !addressOf dst (Operand.width o1)) = false := by
    by_cases hc : (decide (size = 0) || decide (size > 8) || Operand.width o2 != size * 8 || !addressOf dst (Operand.width o1)) = false
    · exact hc
    · simp only [Bool.not_eq_false] at hc
      simp [hc] at h
  simp only [hchecks, Bool.false_eq_true, ↓reduceIte, pure, Option.some.injEq] at h
  have fOps : Lowering.ops second = Lowering.ops l2 ++ [.memStore (Operand.slot o1) (Operand.slot o2) size (endian == .big)] := by rw [← h]
  have fNext : Lowering.nextSlot second = Lowering.nextSlot l2 := by rw [← h]
  have fLayout : Lowering.layout second = Lowering.layout l2 := by rw [← h]
  have fMemory : Lowering.memory second = Lowering.memory l2 := by rw [← h]
  have fLabel : Lowering.nextLabel second = Lowering.nextLabel l2 := by rw [← h]
  have fEffect : Lowering.effectSlot second = Lowering.effectSlot l2 := by rw [← h]
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, bne_eq_false_iff_eq, Bool.not_eq_false'] at hchecks
  obtain ⟨⟨⟨_, hsize8⟩, hsw⟩, _⟩ := hchecks
  have a3 : Appended l2 second [.memStore (Operand.slot o1) (Operand.slot o2) size (endian == .big)] := {
    ops := fOps
    next := by rw [fNext]; exact Nat.le_refl _
    mono := fun b hb => by rw [fLayout]; exact hb
    later := fun b hb => by rw [fLayout] at hb; exact Or.inl hb
    wf := ⟨fun b hb => by rw [fNext]; rw [fLayout] at hb; exact wf2.bound b hb,
      by rw [fLayout]; exact wf2.slotsDistinct, by rw [fLayout]; exact wf2.varsDistinct⟩
    memory := fun v hv => by rw [fMemory]; exact hv
    label := by rw [fLabel]; exact Nat.le_refl _
    labels := by simp [labelsOf]
    labelRange := by simp [labelsOf]
    effect := fEffect }
  have a0 := he0.appended wf
  have aA := heA.appended wf0
  have aS := heS.appended wf1
  refine ⟨[] ++ newA ++ newS ++ [.memStore (Operand.slot o1) (Operand.slot o2) size (endian == .big)],
    ((a0.trans aA).trans aS).trans a3, ?_⟩
  intro fuel state result global program tail effect machine ctx hag hex
  obtain ⟨v, hev, rfl⟩ := exec_move hex
  obtain ⟨width, cells, updated, addressBits, valueWidth, data, hcells, haddress, hstored, hwrite, rfl⟩ := evalExp_store_inv hev
  have hsub2 := ctx.sub.before a3
  have hsub1 := hsub2.before aS
  have hlookup : Bil.lookup state.env dst = .ok (.memory cells) := by simpa [Bil.evalExp] using hcells
  -- the address and the value
  have hsA' : SlotsAgree state.env machine (Lowering.layout l1) := hag.slots.mono hsub1.mono
  obtain ⟨hwa, hholdsA⟩ := hvalA state.env machine hsA' (hag.memoryAgrees hsub1) width addressBits haddress
  have hag1 := hag.after heA hsub1
  have hsS' : SlotsAgree state.env (runOps machine newA) (Lowering.layout l2) := hag1.slots.mono hsub2.mono
  obtain ⟨hwS, hholdsS⟩ := hvalS state.env (runOps machine newA) hsS' (hag1.memoryAgrees hsub2) valueWidth data hstored
  have hag2 := hag1.after heS hsub2
  have hmemVar : Lowering.memory global = some dst := ctx.sub.memory dst (by
    rw [fMemory]
    exact aS.memory dst (aA.memory dst hmem0))
  obtain ⟨hp, hw, hbig, hview, hwin⟩ := hag2.memory dst hmemVar width cells hlookup
  let before := runOps (runOps machine newA) newS
  have hbase : before.slots (Operand.slot o1) = addressBits.setWidth 64 := by
    have hf : before.slots (Operand.slot o1) = (runOps machine newA).slots (Operand.slot o1) :=
      heS.frame _ (Or.inl hsA)
    rw [hf]
    apply BitVec.eq_of_toNat_eq
    have hh : ((runOps machine newA).slots (Operand.slot o1)).toNat = addressBits.toNat := hholdsA
    rw [hh, BitVec.toNat_setWidth]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le addressBits.isLt (Nat.pow_le_pow_right (by decide) hw))).symm
  have hdata : (before.slots (Operand.slot o2)).toNat = data.toNat := hholdsS
  have hupdated := memStore_correct (machine := before) hp hview hw hwin (by omega) hbase hdata hwrite
  have hps := write_pagesSized hp hwrite
  refine Or.inr ⟨rfl, runOps machine ([] ++ newA ++ newS ++ [.memStore (Operand.slot o1) (Operand.slot o2) size (endian == .big)]),
    ?_, ?_, ?_⟩
  · rw [List.nil_append]
    exact Run.ops (by
      intro op hop
      rcases List.mem_append.1 hop with hop | hop
      · rcases List.mem_append.1 hop with hop | hop
        · exact linear_of_expression (heA.pure op hop)
        · exact linear_of_expression (heS.pure op hop)
      · simp only [List.mem_singleton] at hop
        subst hop
        rfl) tail machine
  · rw [List.nil_append, runOps_append, runOps_append]
    simp only [runOps_cons, runOps_nil]
    refine ⟨?_, ?_⟩
    · intro binding hb val hl
      have hne : binding.1 ≠ dst := by
        intro he'
        obtain ⟨_, _, hbits, _, _⟩ := hag.slots binding hb (.memory cells) (he' ▸ hlookup)
        simp at hbits
      rw [lookup_bind_other hne] at hl
      exact hag2.slots binding hb val hl
    · intro var' hv w' cells' hl
      have hsame : var' = dst := by
        rw [hmemVar] at hv
        simpa using hv.symm
      subst hsame
      rw [lookup_bind_same] at hl
      simp only [Except.ok.injEq, Bap.Value.memory.injEq] at hl
      obtain ⟨rfl, hc⟩ := hl
      have hc := eq_of_heq hc
      subst hc
      exact ⟨hps, hw, hbig, hview, hupdated⟩
  · have f1 := heA.frames hsub1 machine
    have f2 := heS.frames hsub2 (runOps machine newA)
    rw [List.nil_append, runOps_append, runOps_append]
    simp only [runOps_cons, runOps_nil]
    have hlow1 := he0.next
    have hhigh : Lowering.nextSlot l2 ≤ Lowering.nextSlot second := a3.next
    refine ⟨?_, ?_⟩
    · show (runOps (runOps machine newA) newS).view = machine.view
      rw [runOps_view, runOps_view]
    · intro slot' hslot' hfree
      show (runOps (runOps machine newA) newS).slots slot' = _
      rw [f2.2 slot' (by
        rcases hslot' with h' | h'
        · exact Or.inl (by have := heA.next; omega)
        · exact Or.inr (by omega)) hfree]
      exact f1.2 slot' (by
        rcases hslot' with h' | h'
        · exact Or.inl (by omega)
        · exact Or.inr (by have := heS.next; omega)) hfree

/-! The control flow of statements. -/

theorem Agrees.write_free {env : Bil.Env} {machine : Machine} {global : Lowering} (h : Agrees env machine global) {slot : Nat}
    (hf : ∀ var, (var, slot) ∉ Lowering.layout global) (value : Word64) : Agrees env (machine.write slot value) global where
  slots := by
    intro binding hb val hl
    obtain ⟨w, x, a, b, c⟩ := h.slots binding hb val hl
    refine ⟨w, x, a, b, ?_⟩
    have hne : binding.2 ≠ slot := by
      intro he
      apply hf binding.1
      rw [← he]
      exact hb
    simp only [Holds, Machine.write_slots, hne, ↓reduceIte]
    exact c
  memory := fun var hv w cells hl => MemoryInv.write (h.memory var hv w cells hl) _ _

theorem Exhausts.prepend {program : List Op} {a b : Cfg} {effect : Nat} (hr : Run program a b) (h : Exhausts program b effect) :
    Exhausts program a effect := by
  obtain ⟨t, rest, m, h1, h2⟩ := h
  exact ⟨t, rest, m, hr.trans h1, h2⟩

theorem Returns.prepend {program : List Op} {a b : Cfg} {value : Word64} {machine : Machine} (hr : Run program a b)
    (h : Returns program b value machine) : Returns program a value machine := by
  obtain ⟨rest, h | h⟩ := h
  · obtain ⟨t, h1, h2⟩ := h
    exact ⟨rest, Or.inl ⟨t, hr.trans h1, h2⟩⟩
  · obtain ⟨s, h1, h2⟩ := h
    exact ⟨rest, Or.inr ⟨s, hr.trans h1, h2⟩⟩

/-- A lowering with operations added, and labels reserved, by hand. -/
structure Pushed (first second : Lowering) (new : List Op) (labels : Nat) (slots : Nat := 0) : Prop where
  ops : Lowering.ops second = Lowering.ops first ++ new
  layout : Lowering.layout second = Lowering.layout first
  next : Lowering.nextSlot second = Lowering.nextSlot first + slots
  memory : Lowering.memory second = Lowering.memory first
  effect : Lowering.effectSlot second = Lowering.effectSlot first
  label : Lowering.nextLabel second = Lowering.nextLabel first + labels

theorem Pushed.wf {first second : Lowering} {new : List Op} {labels slots : Nat} (h : Pushed first second new labels slots)
    (wf : LayoutWF first) : LayoutWF second :=
  ⟨fun b hb => by rw [h.next]; rw [h.layout] at hb; have := wf.bound b hb; omega,
    by rw [h.layout]; exact wf.slotsDistinct, by rw [h.layout]; exact wf.varsDistinct⟩

/-- What lowering does to the lowering state, with where its labels are left out. -/
structure Grows (first second : Lowering) (new : List Op) : Prop where
  ops : Lowering.ops second = Lowering.ops first ++ new
  next : Lowering.nextSlot first ≤ Lowering.nextSlot second
  mono : ∀ b ∈ Lowering.layout first, b ∈ Lowering.layout second
  later : ∀ b ∈ Lowering.layout second, b ∈ Lowering.layout first ∨ Lowering.nextSlot first ≤ b.2
  wf : LayoutWF second
  memory : ∀ var, Lowering.memory first = some var → Lowering.memory second = some var
  label : Lowering.nextLabel first ≤ Lowering.nextLabel second
  effect : Lowering.effectSlot second = Lowering.effectSlot first

theorem Grows.trans {a b c : Lowering} {x y : List Op} (h1 : Grows a b x) (h2 : Grows b c y) : Grows a c (x ++ y) where
  ops := by rw [h2.ops, h1.ops, List.append_assoc]
  next := Nat.le_trans h1.next h2.next
  mono := fun _ h => h2.mono _ (h1.mono _ h)
  later := fun b hb => by
    rcases h2.later b hb with h | h
    · rcases h1.later b h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · exact Or.inr (Nat.le_trans h1.next h)
  wf := h2.wf
  memory := fun _ h => h2.memory _ (h1.memory _ h)
  label := Nat.le_trans h1.label h2.label
  effect := by rw [h2.effect, h1.effect]

theorem Appended.grows {a b : Lowering} {x : List Op} (h : Appended a b x) : Grows a b x :=
  ⟨h.ops, h.next, h.mono, h.later, h.wf, h.memory, h.label, h.effect⟩

theorem Pushed.grows {first second : Lowering} {new : List Op} {labels slots : Nat} (h : Pushed first second new labels slots)
    (wf : LayoutWF first) : Grows first second new where
  ops := h.ops
  next := by rw [h.next]; omega
  mono := fun b hb => by rw [h.layout]; exact hb
  later := fun b hb => by rw [h.layout] at hb; exact Or.inl hb
  wf := h.wf wf
  memory := fun v hv => by rw [h.memory]; exact hv
  label := by rw [h.label]; omega
  effect := h.effect

theorem Sub.before' {first second global : Lowering} {new : List Op} (hs : Sub second global) (ha : Grows first second new) :
    Sub first global where
  mono := fun b hb => hs.mono b (ha.mono b hb)
  later := fun b hb => by
    rcases hs.later b hb with h | h
    · exact ha.later b h
    · exact Or.inr (Nat.le_trans ha.next h)
  memory := fun v hv => hs.memory v (ha.memory v hv)

/-- `setEffect` of a lowering with an effect slot. -/
theorem setEffect_pushed {lowering : Lowering} {slot : Nat} (h : Lowering.effectSlot lowering = some slot) (value : UInt64) :
    (setEffect lowering value).2 = slot ∧ Pushed lowering (setEffect lowering value).1 [.set slot value] 0 := by
  constructor
  · simp [setEffect, h]
  · simp only [setEffect, h]
    exact ⟨rfl, rfl, rfl, rfl, h.symm, rfl⟩

private def StmtOK (stmt : Bil.Stmt) : Prop :=
  ∀ (first second : Lowering) (terminated : Bool) (effect : Nat), LayoutWF first → Lowering.effectSlot first = some effect →
    effect < Lowering.nextSlot first → lowerStmt first stmt = some (second, terminated) →
    ∃ new, Appended first second new ∧ LowerOK first second new terminated (fun fuel state => Bil.execStmt fuel state stmt)

private def ProgramOK (program : Bil.Program) : Prop :=
  ∀ (first second : Lowering) (terminated : Bool) (effect : Nat), LayoutWF first → Lowering.effectSlot first = some effect →
    effect < Lowering.nextSlot first → lowerStatements first program = some (second, terminated) →
    ∃ new, Appended first second new ∧ LowerOK first second new terminated (fun fuel state => Bil.execProgram fuel state program)

private theorem move_ok (dst : Bap.Var) (value : Bil.Exp) : StmtOK (.move dst value) := by
  intro first second terminated effect wf _ _ h
  rw [lowerStmt] at h
  obtain ⟨lowering, hm, h⟩ := obind h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  cases hty : dst.typ
  case mem a c =>
    cases value
    case store memory address stored endian size => exact lowerMove_store_ok wf hty hm
    all_goals
      unfold lowerMove at hm
      rw [hty] at hm
      simp [widthOf, hty] at hm
  all_goals
    have hwidth : ∃ width, widthOf dst = some width := by
      cases hw : widthOf dst with
      | some width => exact ⟨width, rfl⟩
      | none =>
        exfalso
        unfold lowerMove at hm
        rw [hty] at hm
        simp [hw] at hm
    obtain ⟨width, hw⟩ := hwidth
    exact lowerMove_register_ok wf hw hm

private theorem jmp_constant_ok {width : Nat} (target : BitVec width) : StmtOK (.jmp (.int target)) := by
  intro first second terminated effect wf heff hlow h
  rw [lowerStmt] at h
  split at h
  · next hw =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨he, hp⟩ := setEffect_pushed heff (1 : UInt64)
    have hops : Lowering.ops (jumpConstant first (immediate target)) =
        Lowering.ops first ++ [.set effect 1, .jump (immediate target)] := by
      simp only [jumpConstant]
      show Lowering.ops (setEffect first 1).1 ++ _ = _
      rw [hp.ops, List.append_assoc]
      rfl
    have g : Grows first (setEffect first 1).1 [.set effect 1] := hp.grows wf
    have happ : Appended first (jumpConstant first (immediate target)) [.set effect 1, .jump (immediate target)] :=
      { ops := hops
        next := g.next
        mono := g.mono
        later := g.later
        wf := ⟨g.wf.bound, g.wf.slotsDistinct, g.wf.varsDistinct⟩
        memory := g.memory
        label := g.label
        labels := by simp [labelsOf]
        labelRange := by simp [labelsOf]
        effect := g.effect }
    refine ⟨_, happ, ?_⟩
    intro fuel state result global program tail effect' machine ctx hag hex
    obtain ⟨w, bits, hev, rfl⟩ := exec_jmp hex
    have heq : effect' = effect := by
      have := ctx.effectSlot
      rw [heff] at this
      simpa using this.symm
    subst heq
    simp only [Bil.evalExp, Except.ok.injEq, Bap.Value.bits.injEq] at hev
    obtain ⟨rfl, hb⟩ := hev
    have hb := eq_of_heq hb
    subst hb
    refine Or.inr ⟨(immediate target : UInt64).toBitVec, machine.write effect' (1 : UInt64).toBitVec, ?_, ?_, ?_, ?_⟩
    · exact ⟨tail, Or.inl ⟨immediate target, Run.linear (op := .set effect' 1) rfl _ _, rfl⟩⟩
    · show (immediate target).toBitVec.toNat = target.toNat
      simp only [immediate, UInt64.toBitVec_ofNat, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le target.isLt (Nat.pow_le_pow_right (by decide) hw))
    · simp only [Machine.write_slots, ↓reduceIte]
      rfl
    · exact hag.write_free ctx.effectFree _
  · simp at h

private theorem jmp_slot_ok (target : Bil.Exp) (hnot : ∀ (width : Nat) (value : BitVec width), target ≠ .int value) :
    StmtOK (.jmp target) := by
  intro first second terminated effect wf heff hlow h
  rw [lowerStmt] at h
  · obtain ⟨⟨mid, operand⟩, h1, h⟩ := obind h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨newE, he, hslot, _, h64, hval⟩ := lowerExp_correct target wf h1
    have a1 := he.appended wf
    have heffm : Lowering.effectSlot mid = some effect := by rw [a1.effect]; exact heff
    obtain ⟨hs, hp⟩ := setEffect_pushed heffm (1 : UInt64)
    have g : Grows mid (setEffect mid 1).1 [.set effect 1] := hp.grows a1.wf
    have hops : Lowering.ops (jumpSlot mid (Operand.slot operand)) =
        Lowering.ops mid ++ [.set effect 1, .jumpSlot (Operand.slot operand)] := by
      simp only [jumpSlot]
      show Lowering.ops (setEffect mid 1).1 ++ _ = _
      rw [hp.ops, List.append_assoc]
      rfl
    have a2 : Appended mid (jumpSlot mid (Operand.slot operand)) [.set effect 1, .jumpSlot (Operand.slot operand)] :=
      { ops := hops
        next := g.next
        mono := g.mono
        later := g.later
        wf := ⟨g.wf.bound, g.wf.slotsDistinct, g.wf.varsDistinct⟩
        memory := g.memory
        label := g.label
        labels := by simp [labelsOf]
        labelRange := by simp [labelsOf]
        effect := g.effect }
    refine ⟨_, a1.trans a2, ?_⟩
    intro fuel state result global program tail effect' machine ctx hag hex
    obtain ⟨w, bits, hev, rfl⟩ := exec_jmp hex
    have heq : effect' = effect := by
      have := ctx.effectSlot
      rw [heff] at this
      simpa using this.symm
    subst heq
    have hsub := ctx.sub.before a2
    have hsm : SlotsAgree state.env machine (Lowering.layout mid) := hag.slots.mono hsub.mono
    have hmm := hag.memoryAgrees hsub
    obtain ⟨_, hvalue⟩ := hval state.env machine hsm hmm w bits hev
    have hne : Operand.slot operand ≠ effect' :=
      operand_ne_effect he hval hsm hmm hev hlow fun var hv => ctx.effectFree var (hsub.mono _ hv)
    have hafter := hag.after he hsub
    refine Or.inr ⟨((runOps machine newE).write effect' (1 : UInt64).toBitVec).slots (Operand.slot operand),
      (runOps machine newE).write effect' (1 : UInt64).toBitVec, ?_, ?_, ?_, ?_⟩
    · refine ⟨tail, Or.inr ⟨Operand.slot operand, ?_, rfl⟩⟩
      rw [List.append_assoc]
      exact (Run.ops (fun op hop => linear_of_expression (he.pure op hop)) _ machine).trans
        (Run.linear (op := .set effect' 1) rfl _ _)
    · show Holds (if Operand.slot operand = effect' then _ else _) bits
      rw [if_neg hne]
      exact hvalue
    · simp only [Machine.write_slots, ↓reduceIte]
      rfl
    · exact hafter.write_free ctx.effectFree _
  · intro width value he
    exact hnot width value he

private theorem jmp_ok (target : Bil.Exp) : StmtOK (.jmp target) := by
  cases target
  case int value => exact jmp_constant_ok value
  all_goals exact jmp_slot_ok _ (by intro width value he; simp at he)

private theorem special_ok (message : String) : StmtOK (.special message) := by
  intro first second terminated effect wf _ _ h
  rw [lowerStmt] at h
  · simp at h
  all_goals (intros; simp_all)

private theorem cpuExn_ok (number : Nat) : StmtOK (.cpuExn number) := by
  intro first second terminated effect wf _ _ h
  rw [lowerStmt] at h
  · simp at h
  all_goals (intros; simp_all)

private theorem program_nil_ok : ProgramOK [] := by
  intro first second terminated effect wf _ _ h
  rw [lowerStatements] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨[], Appended.refl wf, ?_⟩
  intro fuel state result global program tail effect' machine ctx hag hex
  have := exec_nil hex
  subst this
  exact Or.inr ⟨rfl, machine, .refl _, hag, Frames.refl _ _ _ _⟩

private theorem program_cons_ok {stmt : Bil.Stmt} {rest : Bil.Program} (hs : StmtOK stmt) (hr : ProgramOK rest) :
    ProgramOK (stmt :: rest) := by
  intro first second terminated effect wf heff hlow h
  rw [lowerStatements] at h
  obtain ⟨⟨mid, stopped⟩, h1, h⟩ := obind h
  obtain ⟨newS, a1, ok1⟩ := hs first mid stopped effect wf heff hlow h1
  cases stopped with
  | true =>
    simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨newS, a1, ?_⟩
    intro fuel state result global program tail effect' machine ctx hag hex
    obtain ⟨fuel', ⟨st, eff⟩, h2, h3⟩ := exec_cons hex
    rcases ok1 fuel' state (st, eff) global program tail effect' machine ctx hag h2 with hx | hn
    · exact Or.inl hx
    · cases eff with
      | normal => simp at hn
      | jump target =>
        simp only at h3
        subst h3
        exact Or.inr hn
      | special message => exact absurd hn (by simp)
      | cpuExn number => exact absurd hn (by simp)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have heff2 : Lowering.effectSlot mid = some effect := by rw [a1.effect]; exact heff
    obtain ⟨newR, a2, ok2⟩ := hr mid second terminated effect a1.wf heff2 (Nat.lt_of_lt_of_le hlow a1.next) h
    refine ⟨newS ++ newR, a1.trans a2, ?_⟩
    intro fuel state result global program tail effect' machine ctx hag hex
    obtain ⟨fuel', ⟨st, eff⟩, h2, h3⟩ := exec_cons hex
    obtain ⟨pre, hsplit⟩ := ctx.split
    have ctx1 : Context first mid global newS program (newR ++ tail) effect' := {
      effectSlot := ctx.effectSlot
      effectLow := ctx.effectLow
      effectFree := ctx.effectFree
      wfGlobal := ctx.wfGlobal
      sub := ctx.sub.before a2
      split := ⟨pre, by rw [hsplit]; simp⟩
      distinct := ctx.distinct }
    have hcfg : (newS ++ newR) ++ tail = newS ++ (newR ++ tail) := by simp
    rw [show Outcome first second global program ((newS ++ newR) ++ tail, machine) tail effect' terminated result =
      Outcome first second global program (newS ++ (newR ++ tail), machine) tail effect' terminated result by rw [hcfg]]
    rcases ok1 fuel' state (st, eff) global program (newR ++ tail) effect' machine ctx1 hag h2 with hx | hn
    · exact Or.inl hx
    · cases eff with
      | normal =>
        obtain ⟨_, m1, hrun, hag1, hf1⟩ := hn
        simp only at h3
        have ctx2 : Context mid second global newR program tail effect' := {
          effectSlot := by rw [a1.effect]; exact ctx.effectSlot
          effectLow := Nat.lt_of_lt_of_le ctx.effectLow a1.next
          effectFree := ctx.effectFree
          wfGlobal := ctx.wfGlobal
          sub := ctx.sub
          split := ⟨pre ++ newS, by rw [hsplit]; simp⟩
          distinct := ctx.distinct }
        rcases ok2 fuel' st result global program tail effect' m1 ctx2 hag1 h3 with hx | hn2
        · exact Or.inl (Exhausts.prepend hrun hx)
        · refine Or.inr ?_
          obtain ⟨st2, eff2⟩ := result
          cases eff2 with
          | normal =>
            obtain ⟨ht, m2, hrun2, hag2, hf2⟩ := hn2
            refine ⟨ht, m2, hrun.trans hrun2, hag2, ?_⟩
            exact (hf1.weaken (Nat.le_refl _) a2.next).trans (hf2.weaken a1.next (Nat.le_refl _))
          | jump target =>
            obtain ⟨value, m2, hret, hheld, hone, hag2⟩ := hn2
            exact ⟨value, m2, Returns.prepend hrun hret, hheld, hone, hag2⟩
          | special message => exact absurd hn2 (by simp)
          | cpuExn number => exact absurd hn2 (by simp)
      | jump target =>
        simp only at h3
        subst h3
        exact Or.inr hn
      | special message => exact absurd hn (by simp)
      | cpuExn number => exact absurd hn (by simp)

/-- The core of a conditional, with the lowerings on the way abstract. -/
private theorem ifElse_core {first mid l0 yesEnd l1 noEnd second : Lowering} {condition : Bil.Exp} {yes no : Bil.Program}
    {operand : Operand} {yesDone noDone : Bool} {effect : Nat} (hyesOK : ProgramOK yes) (hnoOK : ProgramOK no)
    (wf : LayoutWF first) (heff : Lowering.effectSlot first = some effect) (hlow : effect < Lowering.nextSlot first)
    (h1 : lowerExp first condition = some (mid, operand)) (hw : Operand.width operand = 1)
    (p0 : Pushed mid l0 [.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1),
      .label (Lowering.nextLabel mid)] 3)
    (hyes : lowerStatements l0 yes = some (yesEnd, yesDone))
    (p1 : Pushed yesEnd l1 ((if yesDone then [] else [.goto (Lowering.nextLabel mid + 2)]) ++ [.label (Lowering.nextLabel mid + 1)]) 0)
    (hno : lowerStatements l1 no = some (noEnd, noDone))
    (p2 : Pushed noEnd second ((if noDone then [] else [.goto (Lowering.nextLabel mid + 2)]) ++
      (if yesDone && noDone then [] else [.label (Lowering.nextLabel mid + 2)])) 0) :
    ∃ new, Appended first second new ∧
      LowerOK first second new (yesDone && noDone) (fun fuel state => Bil.execStmt fuel state (.ifElse condition yes no)) := by
  obtain ⟨newC, he, _, _, _, hval⟩ := lowerExp_correct condition wf h1
  have aC := he.appended wf
  have wfm := aC.wf
  have heffm : Lowering.effectSlot mid = some effect := by rw [aC.effect]; exact heff
  have g0 := p0.grows wfm
  have heff0 : Lowering.effectSlot l0 = some effect := by rw [g0.effect]; exact heffm
  have hlow0 : effect < Lowering.nextSlot l0 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlow aC.next) g0.next
  obtain ⟨newY, aY, okY⟩ := hyesOK l0 yesEnd yesDone effect g0.wf heff0 hlow0 hyes
  have g1 := p1.grows aY.wf
  have heff1 : Lowering.effectSlot l1 = some effect := by rw [g1.effect, aY.effect]; exact heff0
  have hlow1 : effect < Lowering.nextSlot l1 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlow0 aY.next) g1.next
  obtain ⟨newN, aN, okN⟩ := hnoOK l1 noEnd noDone effect g1.wf heff1 hlow1 hno
  have g2 := p2.grows aN.wf
  have y := Lowering.nextLabel mid
  let gotoY : List Op := if yesDone then [] else [.goto (Lowering.nextLabel mid + 2)]
  let gotoN : List Op := if noDone then [] else [.goto (Lowering.nextLabel mid + 2)]
  let labelD : List Op := if yesDone && noDone then [] else [.label (Lowering.nextLabel mid + 2)]
  have hgy : labelsOf gotoY = [] := by simp only [gotoY]; split <;> rfl
  have hgn : labelsOf gotoN = [] := by simp only [gotoN]; split <;> rfl
  have gAll := (((aC.grows.trans g0).trans aY.grows).trans g1).trans (aN.grows.trans g2)
  have hl0 : Lowering.nextLabel l0 = Lowering.nextLabel mid + 3 := p0.label
  have hmidLabel : Lowering.nextLabel first ≤ Lowering.nextLabel mid := aC.label
  let new : List Op := newC ++ [.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1),
      .label (Lowering.nextLabel mid)] ++ newY ++ (gotoY ++ [.label (Lowering.nextLabel mid + 1)]) ++ (newN ++ (gotoN ++ labelD))
  have hlabelsNew : labelsOf new = Lowering.nextLabel mid :: (labelsOf newY ++ (Lowering.nextLabel mid + 1) :: (labelsOf newN ++ labelsOf labelD)) := by
    simp only [new, labelsOf_append, labelsOf_expression he.pure, hgy, hgn]
    simp [labelsOf]
  have hrangeY := aY.labelRange
  have hrangeN := aN.labelRange
  have hl1 : Lowering.nextLabel l1 = Lowering.nextLabel yesEnd := by rw [p1.label]; rfl
  have hend : Lowering.nextLabel second = Lowering.nextLabel noEnd := by rw [p2.label]; rfl
  have hD : ∀ l ∈ labelsOf labelD, l = Lowering.nextLabel mid + 2 := by
    simp only [labelD]
    split <;> simp [labelsOf]
  have hsplitL : ∀ l, l ∈ labelsOf new → Lowering.nextLabel first ≤ l ∧ l < Lowering.nextLabel second := by
    intro l hl
    rw [hlabelsNew] at hl
    have a1 := aY.label
    have a2 := aN.label
    simp only [List.mem_cons, List.mem_append] at hl
    rcases hl with rfl | hl | rfl | hl | hl
    · omega
    · have := hrangeY l hl
      omega
    · omega
    · have := hrangeN l hl
      omega
    · have := hD l hl
      omega
  have happ : Appended first second new := {
    ops := by
      rw [gAll.ops]
    next := gAll.next
    mono := gAll.mono
    later := gAll.later
    wf := gAll.wf
    memory := gAll.memory
    label := gAll.label
    labels := by
      rw [hlabelsNew]
      have a1 := aY.label
      refine List.nodup_cons.2 ⟨?_, ?_⟩
      · simp only [List.mem_append, List.mem_cons, not_or]
        refine ⟨fun hm => ?_, by omega, fun hm => ?_, fun hm => ?_⟩
        · have := hrangeY _ hm
          omega
        · have := hrangeN _ hm
          omega
        · have := hD _ hm
          omega
      · refine List.nodup_append.2 ⟨aY.labels, List.nodup_cons.2 ⟨?_, List.nodup_append.2 ⟨aN.labels, ?_, ?_⟩⟩, ?_⟩
        · simp only [List.mem_append, not_or]
          exact ⟨fun hm => by have := hrangeN _ hm; omega, fun hm => by have := hD _ hm; omega⟩
        · simp only [labelD]
          split <;> simp [labelsOf]
        · intro p hp q hq he
          subst he
          have := hrangeN p hp
          have := hD p hq
          omega
        · intro p hp q hq he
          subst he
          have := hrangeY p hp
          simp only [List.mem_cons, List.mem_append] at hq
          rcases hq with rfl | hq | hq
          · omega
          · have := hrangeN p hq
            omega
          · have := hD p hq
            omega
    labelRange := hsplitL
    effect := gAll.effect }
  refine ⟨new, happ, ?_⟩
  intro fuel state result global program tail effect' machine ctx hag hex
  have heq : effect' = effect := by
    have := ctx.effectSlot
    rw [heff] at this
    simpa using this.symm
  subst heq
  obtain ⟨fuel', bit, hev, hexec⟩ := exec_ifElse hex
  obtain ⟨pre, hsplit⟩ := ctx.split
  have subEnd := ctx.sub.before' g2
  have subL1 := subEnd.before' aN.grows
  have subY := subL1.before' g1
  have subL0 := subY.before' aY.grows
  have subMid := subL0.before' g0
  have hsm : SlotsAgree state.env machine (Lowering.layout mid) := hag.slots.mono subMid.mono
  obtain ⟨_, hvalue⟩ := hval state.env machine hsm (hag.memoryAgrees subMid) 1 bit hev
  have hag1 := hag.after he subMid
  have hf0 := he.frames subMid machine
  let m1 := runOps machine newC
  let rest : List Op := newY ++ (gotoY ++ [.label (Lowering.nextLabel mid + 1)]) ++ (newN ++ (gotoN ++ labelD)) ++ tail
  have hnew : new ++ tail = newC ++ (.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1) ::
      .label (Lowering.nextLabel mid) :: rest) := by
    simp [new, rest, List.append_assoc]
  have hrun0 : Run program (new ++ tail, machine)
      (.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1) ::
        .label (Lowering.nextLabel mid) :: rest, m1) := by
    rw [hnew]
    exact Run.ops (fun op hop => linear_of_expression (he.pure op hop)) _ machine
  have hprog : program = (pre ++ newC ++ [.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1)]) ++
      .label (Lowering.nextLabel mid) :: rest := by
    rw [hsplit]
    simp [new, rest, List.append_assoc]
  have hafterY := afterLabel_split _ hprog ctx.distinct
  have hprogN : program = (pre ++ newC ++ [.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1),
      .label (Lowering.nextLabel mid)] ++ newY ++ gotoY) ++ .label (Lowering.nextLabel mid + 1) :: (newN ++ (gotoN ++ labelD) ++ tail) := by
    rw [hsplit]
    simp [new, List.append_assoc]
  have hafterN := afterLabel_split _ hprogN ctx.distinct
  have hdone : ∀ hc : (yesDone && noDone) = false, program = (pre ++ newC ++ [.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1),
      .label (Lowering.nextLabel mid)] ++ newY ++ gotoY ++ [.label (Lowering.nextLabel mid + 1)] ++ newN ++ gotoN) ++
      .label (Lowering.nextLabel mid + 2) :: tail := by
    intro hc
    rw [hsplit]
    simp [new, labelD, hc, List.append_assoc]
  have hflow : ∀ {a b c : Nat}, a < b → b ≤ c → a < c := fun h1 h2 => Nat.lt_of_lt_of_le h1 h2
  by_cases hbit : bit = 1
  · -- the branch that was taken
    rw [if_pos hbit] at hexec
    have hne : m1.slots (Operand.slot operand) ≠ 0 := (holds_condition hvalue).2 hbit
    have hbranch : Run program (.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1) ::
        .label (Lowering.nextLabel mid) :: rest, m1) (rest, m1) :=
      Run.branch (by rw [if_pos hne]; exact hafterY)
    have ctxY : Context l0 yesEnd global newY program ((gotoY ++ [.label (Lowering.nextLabel mid + 1)]) ++ (newN ++ (gotoN ++ labelD)) ++ tail) effect' := {
      effectSlot := heff0
      effectLow := hlow0
      effectFree := ctx.effectFree
      wfGlobal := ctx.wfGlobal
      sub := subY
      split := ⟨pre ++ newC ++ [.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1),
        .label (Lowering.nextLabel mid)], by rw [hsplit]; simp [new, List.append_assoc]⟩
      distinct := ctx.distinct }
    have hprefix := hrun0.trans hbranch
    have hrestEq : rest = newY ++ ((gotoY ++ [.label (Lowering.nextLabel mid + 1)]) ++ (newN ++ (gotoN ++ labelD)) ++ tail) := by
      simp [rest, List.append_assoc]
    rcases okY fuel' state result global program _ effect' m1 ctxY hag1 hexec with hx | hn
    · refine Or.inl (Exhausts.prepend hprefix ?_)
      rw [hrestEq]
      exact hx
    · refine Or.inr ?_
      obtain ⟨st, eff⟩ := result
      cases eff with
      | normal =>
        obtain ⟨hy, m2, hrun, hag2, hf⟩ := hn
        subst hy
        refine ⟨by simp, m2, ?_, hag2, ?_⟩
        · refine hprefix.trans ?_
          rw [hrestEq]
          refine hrun.trans ?_
          have hc : (false && noDone) = false := rfl
          have hgo : gotoY = [.goto (Lowering.nextLabel mid + 2)] := by simp [gotoY]
          rw [hgo]
          exact Run.goto (afterLabel_split _ (hdone hc) ctx.distinct) _
        · have hg := g0.next
          have hn1 := aC.next
          have hs0 := aY.next
          have hs1 := g1.next
          have hs2 := aN.next
          have hs3 := g2.next
          exact (hf0.weaken (Nat.le_refl _) (by omega)).trans (hf.weaken (by omega) (by omega))
      | jump target =>
        obtain ⟨value, m2, hret, hheld, hone, hag2⟩ := hn
        refine ⟨value, m2, Returns.prepend hprefix ?_, hheld, hone, hag2⟩
        rw [hrestEq]
        exact hret
      | special message => exact absurd hn (by simp)
      | cpuExn number => exact absurd hn (by simp)
  · rw [if_neg hbit] at hexec
    have hzero : m1.slots (Operand.slot operand) = 0 := by
      by_cases hz : m1.slots (Operand.slot operand) = 0
      · exact hz
      · exact absurd ((holds_condition hvalue).1 hz) hbit
    have hbranch : Run program (.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1) ::
        .label (Lowering.nextLabel mid) :: rest, m1) (newN ++ (gotoN ++ labelD) ++ tail, m1) :=
      Run.branch (by
        rw [if_neg (by simpa using hzero)]
        exact hafterN)
    have ctxN : Context l1 noEnd global newN program ((gotoN ++ labelD) ++ tail) effect' := {
      effectSlot := heff1
      effectLow := hlow1
      effectFree := ctx.effectFree
      wfGlobal := ctx.wfGlobal
      sub := subEnd
      split := ⟨pre ++ newC ++ [.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1),
        .label (Lowering.nextLabel mid)] ++ newY ++ (gotoY ++ [.label (Lowering.nextLabel mid + 1)]), by
          rw [hsplit]; simp [new, List.append_assoc]⟩
      distinct := ctx.distinct }
    have hprefix := hrun0.trans hbranch
    have hrestEq : newN ++ (gotoN ++ labelD) ++ tail = newN ++ ((gotoN ++ labelD) ++ tail) := by simp [List.append_assoc]
    rcases okN fuel' state result global program _ effect' m1 ctxN hag1 hexec with hx | hn
    · refine Or.inl (Exhausts.prepend hprefix ?_)
      rw [hrestEq]
      exact hx
    · refine Or.inr ?_
      obtain ⟨st, eff⟩ := result
      cases eff with
      | normal =>
        obtain ⟨hy, m2, hrun, hag2, hf⟩ := hn
        subst hy
        refine ⟨by simp, m2, ?_, hag2, ?_⟩
        · refine hprefix.trans ?_
          rw [hrestEq]
          refine hrun.trans ?_
          have hc : (yesDone && false) = false := by simp
          have hgo : gotoN = [.goto (Lowering.nextLabel mid + 2)] := by simp [gotoN]
          have hprogD := hdone hc
          rw [hgo]
          exact Run.goto (afterLabel_split _ hprogD ctx.distinct) _
        · have hg := g0.next
          have hn1 := aC.next
          have hs1 := g1.next
          have hs0 := aY.next
          have hs2 := aN.next
          have hs3 := g2.next
          exact (hf0.weaken (Nat.le_refl _) (by omega)).trans (hf.weaken (by omega) (by omega))
      | jump target =>
        obtain ⟨value, m2, hret, hheld, hone, hag2⟩ := hn
        refine ⟨value, m2, Returns.prepend hprefix ?_, hheld, hone, hag2⟩
        rw [hrestEq]
        exact hret
      | special message => exact absurd hn (by simp)
      | cpuExn number => exact absurd hn (by simp)

/-- The core of a loop, with the lowerings on the way abstract. -/
private theorem while_core {first l3 mid l4 bodyEnd l5 l6 second : Lowering} {condition : Bil.Exp} {body : Bil.Program}
    {operand : Operand} {bodyDone : Bool} {effect : Nat} {exit : UInt64} (hbodyOK : ProgramOK body)
    (wf : LayoutWF first) (heff : Lowering.effectSlot first = some effect) (hlow : effect < Lowering.nextSlot first)
    (p0 : Pushed first l3 [.set (Lowering.nextSlot first) 0, .goto (Lowering.nextLabel first), .label (Lowering.nextLabel first),
        .add (Lowering.nextSlot first) (Lowering.nextSlot first) 1,
        .set (Lowering.nextSlot first + 1) 100000,
        .bin .ge (Lowering.nextSlot first + 2) (Lowering.nextSlot first) (Lowering.nextSlot first + 1),
        .branch (Lowering.nextSlot first + 2) (Lowering.nextLabel first + 4) (Lowering.nextLabel first + 1),
        .label (Lowering.nextLabel first + 1)] 5 3)
    (h1 : lowerExp l3 condition = some (mid, operand)) (hw : Operand.width operand = 1)
    (p1 : Pushed mid l4 [.branch (Operand.slot operand) (Lowering.nextLabel first + 2) (Lowering.nextLabel first + 3),
      .label (Lowering.nextLabel first + 2)] 0)
    (hbody : lowerStatements l4 body = some (bodyEnd, bodyDone))
    (p2 : Pushed bodyEnd l5 ((if bodyDone then [] else [.goto (Lowering.nextLabel first)]) ++ [.label (Lowering.nextLabel first + 4)]) 0)
    (p3 : Lowering.effectSlot l5 = some effect → Pushed l5 l6 [.set effect 2] 0)
    (p4 : Pushed l6 second [.jump exit, .label (Lowering.nextLabel first + 3)] 0) :
    ∃ new, Appended first second new ∧
      LowerOK first second new false (fun fuel state => Bil.execStmt fuel state (.while condition body)) := by
  generalize hc : Lowering.nextSlot first = c at p0
  generalize hl : Lowering.nextLabel first = l at p0 p1 p2 p4
  have g0 := p0.grows wf
  have hnext0 : Lowering.nextSlot l3 = c + 3 := by rw [p0.next, hc]
  have hlabel0 : Lowering.nextLabel l3 = l + 5 := by rw [p0.label, hl]
  obtain ⟨newC, he, _, _, _, hval⟩ := lowerExp_correct condition g0.wf h1
  have aC := he.appended g0.wf
  have g1 := p1.grows aC.wf
  have heff4 : Lowering.effectSlot l4 = some effect := by rw [g1.effect, aC.effect, g0.effect]; exact heff
  have hlow4 : effect < Lowering.nextSlot l4 :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlow g0.next) aC.next) g1.next
  obtain ⟨newB, aB, okB⟩ := hbodyOK l4 bodyEnd bodyDone effect g1.wf heff4 hlow4 hbody
  have g2 := p2.grows aB.wf
  have heff5 : Lowering.effectSlot l5 = some effect := by rw [g2.effect, aB.effect]; exact heff4
  have p3 := p3 heff5
  have g3 := p3.grows g2.wf
  have g4 := p4.grows g3.wf
  have hlabel4 : Lowering.nextLabel l4 = l + 5 := by rw [p1.label, ← he.nextLabel.symm, hlabel0]
  let goBack : List Op := if bodyDone then [] else [.goto l]
  have hgoBack : labelsOf goBack = [] := by simp only [goBack]; split <;> rfl
  let head : List Op := [.add c c 1, .set (c + 1) 100000, .bin .ge (c + 2) c (c + 1), .branch (c + 2) (l + 4) (l + 1), .label (l + 1)]
  let new : List Op := [.set c 0, .goto l, .label l] ++ head ++ newC ++
    [.branch (Operand.slot operand) (l + 2) (l + 3), .label (l + 2)] ++ newB ++ (goBack ++ [.label (l + 4)]) ++
    [.set effect 2] ++ [.jump exit, .label (l + 3)]
  have gAll := (((g0.trans aC.grows).trans g1).trans aB.grows).trans (g2.trans (g3.trans g4))
  have hlabelsNew : labelsOf new = l :: (l + 1) :: (l + 2) :: (labelsOf newB ++ (l + 4) :: (l + 3) :: []) := by
    simp only [new, head, labelsOf_append, labelsOf_expression he.pure, hgoBack]
    simp [labelsOf]
  have hrangeB := aB.labelRange
  have hbodyLabel : Lowering.nextLabel l4 ≤ Lowering.nextLabel bodyEnd := aB.label
  have hend : Lowering.nextLabel second = Lowering.nextLabel bodyEnd := by
    rw [p4.label, p3.label, p2.label]
    rfl
  have happ : Appended first second new := {
    ops := by
      rw [gAll.ops]
      simp [new, head, goBack, List.append_assoc]
    next := gAll.next
    mono := gAll.mono
    later := gAll.later
    wf := gAll.wf
    memory := gAll.memory
    label := gAll.label
    labels := by
      rw [hlabelsNew]
      have hout : ∀ x, x < l + 5 → x ∉ labelsOf newB := fun x hx hm => by
        have := hrangeB x hm
        omega
      simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or]
      refine ⟨⟨by omega, by omega, hout _ (by omega), by omega, by omega, by simp⟩,
        ⟨by omega, hout _ (by omega), by omega, by omega, by simp⟩, ⟨hout _ (by omega), by omega, by omega, by simp⟩, ?_⟩
      refine List.nodup_append.2 ⟨aB.labels, by simp, ?_⟩
      intro p hp q hq he
      subst he
      have := hrangeB p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      omega
    labelRange := by
      intro x hx
      rw [hlabelsNew] at hx
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | hx | rfl | rfl
      all_goals first
        | (have := hrangeB x hx; omega)
        | omega
    effect := gAll.effect }
  refine ⟨new, happ, ?_⟩
  intro fuel state result global program tail effect' machine ctx hag hex
  have heq : effect' = effect := by
    have := ctx.effectSlot
    rw [heff] at this
    simpa using this.symm
  subst heq
  obtain ⟨pre, hsplit⟩ := ctx.split
  have subL6 := ctx.sub.before' g4
  have subL5 := subL6.before' g3
  have subEnd := subL5.before' g2
  have subL4 := subEnd.before' aB.grows
  have subMid := subL4.before' g1
  have subL3 := subMid.before' aC.grows
  have sub0 := subL3.before' g0
  -- the slots of the loop belong to no variable
  have hfree : ∀ slot, c ≤ slot → slot < c + 3 → ∀ var, (var, slot) ∉ Lowering.layout global := by
    intro slot h1 h2 var hm
    rcases subL3.later _ hm with hb | hb
    · have hb' : (var, slot) ∈ Lowering.layout first := by rw [p0.layout] at hb; exact hb
      have := wf.bound _ hb'
      simp only at this
      omega
    · simp only at hb
      omega
  let afterBody : List Op := (goBack ++ [.label (l + 4)]) ++ [.set effect' 2] ++ [.jump exit, .label (l + 3)] ++ tail
  let loop : List Op := head ++ newC ++ [.branch (Operand.slot operand) (l + 2) (l + 3), .label (l + 2)] ++ newB ++ afterBody
  have hprogLoop : program = (pre ++ [.set c 0, .goto l]) ++ .label l :: loop := by
    rw [hsplit]
    simp [new, loop, afterBody, List.append_assoc]
  have hafterLoop := afterLabel_split _ hprogLoop ctx.distinct
  have hprogExh : program = (pre ++ [.set c 0, .goto l, .label l] ++ head ++ newC ++
      [.branch (Operand.slot operand) (l + 2) (l + 3), .label (l + 2)] ++ newB ++ goBack) ++ .label (l + 4) ::
      ([.set effect' 2, .jump exit, .label (l + 3)] ++ tail) := by
    rw [hsplit]
    simp [new, List.append_assoc]
  have hafterExh := afterLabel_split _ hprogExh ctx.distinct
  have hprogCheck : program = (pre ++ [.set c 0, .goto l, .label l, .add c c 1, .set (c + 1) 100000, .bin .ge (c + 2) c (c + 1),
      .branch (c + 2) (l + 4) (l + 1)]) ++ .label (l + 1) :: (newC ++ [.branch (Operand.slot operand) (l + 2) (l + 3), .label (l + 2)] ++ newB ++ afterBody) := by
    rw [hsplit]
    simp [new, head, afterBody, List.append_assoc]
  have hafterCheck := afterLabel_split _ hprogCheck ctx.distinct
  have hprogBody : program = (pre ++ [.set c 0, .goto l, .label l] ++ head ++ newC ++ [.branch (Operand.slot operand) (l + 2) (l + 3)]) ++
      .label (l + 2) :: (newB ++ afterBody) := by
    rw [hsplit]
    simp [new, head, afterBody, List.append_assoc]
  have hafterBody := afterLabel_split _ hprogBody ctx.distinct
  have hprogDone : program = (pre ++ [.set c 0, .goto l, .label l] ++ head ++ newC ++
      [.branch (Operand.slot operand) (l + 2) (l + 3), .label (l + 2)] ++ newB ++ (goBack ++ [.label (l + 4)]) ++ [.set effect' 2, .jump exit]) ++
      .label (l + 3) :: tail := by
    rw [hsplit]
    simp [new, List.append_assoc]
  have hafterDone := afterLabel_split _ hprogDone ctx.distinct
  have hfnext : Lowering.nextSlot first ≤ Lowering.nextSlot second := gAll.next
  have hc3 : c + 3 ≤ Lowering.nextSlot second := by
    have h1 := aC.next
    have h2 := g1.next
    have h3 := aB.next
    have h4 := g2.next
    have h5 := g3.next
    have h6 := g4.next
    omega
  have hEndNext : Lowering.nextSlot bodyEnd ≤ Lowering.nextSlot second := by
    have h4 := g2.next
    have h5 := g3.next
    have h6 := g4.next
    omega
  have hmidNext : Lowering.nextSlot mid ≤ Lowering.nextSlot l4 := g1.next
  have hmid3 : c + 3 ≤ Lowering.nextSlot mid := by
    have := aC.next
    omega
  -- one iteration and the ones after it
  have key : ∀ (fuel : Nat) (state : Bil.State) (result : Bil.State × Bil.Effect) (machine : Machine),
      Agrees state.env machine global → Bil.execStmt fuel state (.while condition body) = .ok result →
      Outcome first second global program (loop, machine) tail effect' false result := by
    intro fuel
    induction fuel with
    | zero =>
      intro state result machine _ hex
      simp [Bil.execStmt] at hex
    | succ fuel ih =>
      intro state result machine hag hex
      obtain ⟨bit, hev, hbranch⟩ := exec_while hex
      let m0 := runOps machine [.add c c 1, .set (c + 1) 100000, .bin .ge (c + 2) c (c + 1)]
      have hrun0 : Run program (loop, machine) (.branch (c + 2) (l + 4) (l + 1) :: .label (l + 1) ::
          (newC ++ [.branch (Operand.slot operand) (l + 2) (l + 3), .label (l + 2)] ++ newB ++ afterBody), m0) := by
        have hloop : loop = [.add c c 1, .set (c + 1) 100000, .bin .ge (c + 2) c (c + 1)] ++
            (.branch (c + 2) (l + 4) (l + 1) :: .label (l + 1) ::
              (newC ++ [.branch (Operand.slot operand) (l + 2) (l + 3), .label (l + 2)] ++ newB ++ afterBody)) := by
          simp [loop, head, List.append_assoc]
        rw [hloop]
        exact Run.ops (by intro op hop; simp at hop; rcases hop with rfl | rfl | rfl <;> rfl) _ machine
      have hag0 : Agrees state.env m0 global :=
        ((hag.write_free (hfree c (by omega) (by omega)) _).write_free (hfree (c + 1) (by omega) (by omega)) _).write_free
          (hfree (c + 2) (by omega) (by omega)) _
      have hf0 : Frames (Lowering.nextSlot first) (Lowering.nextSlot second) global machine m0 := by
        refine ⟨rfl, ?_⟩
        intro slot hslot _
        have hne : slot ≠ c ∧ slot ≠ c + 1 ∧ slot ≠ c + 2 := by omega
        simp [m0, runOps_cons, runOps_nil, Bap.Proofs.Primus.step, Machine.write_slots, hne.1, hne.2.1, hne.2.2]
      by_cases hlimit : m0.slots (c + 2) ≠ 0
      · -- out of iterations
        refine Or.inl ⟨exit, .label (l + 3) :: tail, m0.write effect' (2 : UInt64).toBitVec, ?_, ?_⟩
        · refine hrun0.trans (.step ?_ (Run.linear (op := .set effect' 2) rfl _ _))
          simp only [nextCfg, if_pos hlimit, hafterExh]
          rfl
        · simp only [Machine.write_slots, ↓reduceIte]
          rfl
      · have hzero : m0.slots (c + 2) = 0 := by simpa using hlimit
        have hrun1 : Run program (loop, machine) (newC ++ [.branch (Operand.slot operand) (l + 2) (l + 3), .label (l + 2)] ++ newB ++ afterBody, m0) := by
          refine hrun0.trans (.step ?_ (.refl _))
          simp only [nextCfg, if_neg hlimit, hafterCheck]
          rfl
        have hsm : SlotsAgree state.env m0 (Lowering.layout mid) := hag0.slots.mono subMid.mono
        obtain ⟨_, hvalue⟩ := hval state.env m0 hsm (hag0.memoryAgrees subMid) 1 bit hev
        have hag1 := hag0.after he subMid
        have hf1 := he.frames subMid m0
        let m1 := runOps m0 newC
        have hrun2 : Run program (loop, machine) (.branch (Operand.slot operand) (l + 2) (l + 3) :: .label (l + 2) :: (newB ++ afterBody), m1) := by
          refine hrun1.trans ?_
          have heq : newC ++ [.branch (Operand.slot operand) (l + 2) (l + 3), .label (l + 2)] ++ newB ++ afterBody =
              newC ++ (.branch (Operand.slot operand) (l + 2) (l + 3) :: .label (l + 2) :: (newB ++ afterBody)) := by
            simp [List.append_assoc]
          rw [heq]
          exact Run.ops (fun op hop => linear_of_expression (he.pure op hop)) _ m0
        have hfm1 : Frames (Lowering.nextSlot first) (Lowering.nextSlot second) global machine m1 := by
          refine hf0.trans (hf1.weaken ?_ ?_)
          · have := g0.next; exact this
          · have h3 := g1.next
            have h4 := aB.next
            omega
        by_cases hbit : bit = 1
        · rw [if_pos hbit] at hbranch
          obtain ⟨inner, hbodyExec, hinner⟩ := hbranch
          have hne : m1.slots (Operand.slot operand) ≠ 0 := (holds_condition hvalue).2 hbit
          have hrun3 : Run program (loop, machine) (newB ++ afterBody, m1) := by
            refine hrun2.trans (.step ?_ (.refl _))
            simp only [nextCfg, if_pos hne, hafterBody]
            rfl
          have ctxB : Context l4 bodyEnd global newB program afterBody effect' := {
            effectSlot := heff4
            effectLow := hlow4
            effectFree := ctx.effectFree
            wfGlobal := ctx.wfGlobal
            sub := subEnd
            split := ⟨pre ++ [.set c 0, .goto l, .label l] ++ head ++ newC ++ [.branch (Operand.slot operand) (l + 2) (l + 3), .label (l + 2)], by
              rw [hsplit]; simp [new, afterBody, List.append_assoc]⟩
            distinct := ctx.distinct }
          rcases okB fuel state inner global program afterBody effect' m1 ctxB hag1 hbodyExec with hx | hn
          · exact Or.inl (Exhausts.prepend hrun3 hx)
          · obtain ⟨st, eff⟩ := inner
            cases eff with
            | normal =>
              obtain ⟨hb, m2, hrun, hag2, hf⟩ := hn
              subst hb
              simp only at hinner
              have hrun4 : Run program (loop, machine) (loop, m2) := by
                refine hrun3.trans (hrun.trans ?_)
                have hgo : goBack = [.goto l] := by simp [goBack]
                simp only [afterBody, hgo]
                exact Run.goto hafterLoop _
              rcases ih st result m2 hag2 hinner with hx | hn2
              · exact Or.inl (Exhausts.prepend hrun4 hx)
              · refine Or.inr ?_
                obtain ⟨st', eff'⟩ := result
                have hfm2 : Frames (Lowering.nextSlot first) (Lowering.nextSlot second) global machine m2 :=
                  hfm1.trans (hf.weaken (by
                    have h1 := g0.next
                    have h2 := aC.next
                    have h3 := g1.next
                    omega) hEndNext)
                cases eff' with
                | normal =>
                  obtain ⟨ht, m3, hrun5, hag3, hf3⟩ := hn2
                  exact ⟨ht, m3, hrun4.trans hrun5, hag3, hfm2.trans hf3⟩
                | jump target =>
                  obtain ⟨value, m3, hret, hheld, hone, hag3⟩ := hn2
                  exact ⟨value, m3, Returns.prepend hrun4 hret, hheld, hone, hag3⟩
                | special message => exact absurd hn2 (by simp)
                | cpuExn number => exact absurd hn2 (by simp)
            | jump target =>
              simp only at hinner
              subst hinner
              obtain ⟨value, m3, hret, hheld, hone, hag3⟩ := hn
              exact Or.inr ⟨value, m3, Returns.prepend hrun3 hret, hheld, hone, hag3⟩
            | special message => exact absurd hn (by simp)
            | cpuExn number => exact absurd hn (by simp)
        · rw [if_neg hbit] at hbranch
          subst hbranch
          have hzero1 : m1.slots (Operand.slot operand) = 0 := by
            by_cases hz : m1.slots (Operand.slot operand) = 0
            · exact hz
            · exact absurd ((holds_condition hvalue).1 hz) hbit
          refine Or.inr ⟨rfl, m1, ?_, hag1, hfm1⟩
          refine hrun2.trans (.step ?_ (.refl _))
          have hnz : ¬ (m1.slots (Operand.slot operand) ≠ 0) := by simpa using hzero1
          simp only [nextCfg, if_neg hnz, hafterDone]
          rfl
  -- the way into the loop
  have hstart : Run program (new ++ tail, machine) (loop, machine.write c (0 : UInt64).toBitVec) := by
    have hnew : new ++ tail = .set c 0 :: .goto l :: .label l :: loop := by
      simp [new, loop, afterBody, head, List.append_assoc]
    rw [hnew]
    exact (Run.linear (op := .set c 0) rfl _ _).trans (Run.goto hafterLoop _)
  have hag' := hag.write_free (hfree c (by omega) (by omega)) (0 : UInt64).toBitVec
  have hfs : Frames (Lowering.nextSlot first) (Lowering.nextSlot second) global machine (machine.write c (0 : UInt64).toBitVec) := by
    refine ⟨rfl, ?_⟩
    intro slot hslot _
    have hne : slot ≠ c := by omega
    simp [Machine.write_slots, hne]
  rcases key fuel state result _ hag' hex with hx | hn
  · exact Or.inl (Exhausts.prepend hstart hx)
  · refine Or.inr ?_
    obtain ⟨st, eff⟩ := result
    cases eff with
    | normal =>
      obtain ⟨ht, m3, hrun5, hag3, hf3⟩ := hn
      exact ⟨ht, m3, hstart.trans hrun5, hag3, hfs.trans hf3⟩
    | jump target =>
      obtain ⟨value, m3, hret, hheld, hone, hag3⟩ := hn
      exact ⟨value, m3, Returns.prepend hstart hret, hheld, hone, hag3⟩
    | special message => exact absurd hn (by simp)
    | cpuExn number => exact absurd hn (by simp)

private theorem ifElse_ok {condition : Bil.Exp} {yes no : Bil.Program} (hy : ProgramOK yes) (hn : ProgramOK no) :
    StmtOK (.ifElse condition yes no) := by
  intro first second terminated effect wf heff hlow h
  rw [lowerStmt] at h
  obtain ⟨⟨mid, operand⟩, h1, h⟩ := obind h
  have hw : Operand.width operand = 1 := by
    by_cases hc : Operand.width operand = 1
    · exact hc
    · simp [hc] at h
  simp only [hw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨⟨yesEnd, yesDone⟩, hyes, h⟩ := obind h
  obtain ⟨⟨noEnd, noDone⟩, hno, h⟩ := obind h
  split at h
  · simp at h
  · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ifElse_core hy hn wf heff hlow h1 hw ?_ hyes ?_ hno ?_
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨List.append_assoc _ _ _, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨List.append_assoc _ _ _, rfl, rfl, rfl, rfl, rfl⟩

private theorem while_ok {condition : Bil.Exp} {body : Bil.Program} (hb : ProgramOK body) : StmtOK (.while condition body) := by
  intro first second terminated effect wf heff hlow h
  rw [lowerStmt] at h
  simp only [temporary] at h
  obtain ⟨⟨mid, operand⟩, h1, h⟩ := obind h
  have hw : Operand.width operand = 1 := by
    by_cases hc : Operand.width operand = 1
    · exact hc
    · simp [hc] at h
  simp only [hw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨⟨bodyEnd, bodyDone⟩, hbody, h⟩ := obind h
  split at h
  · simp at h
  · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine while_core hb wf heff hlow ?_ h1 hw ?_ hbody ?_ (fun he => (setEffect_pushed he 2).2) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨List.append_assoc _ _ _, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨List.append_assoc _ _ _, rfl, rfl, rfl, rfl, rfl⟩

/-- Every statement and program that lowers is correct, by the structure of the program. -/
private theorem lowered_all : (∀ stmt, StmtOK stmt) ∧ (∀ program, ProgramOK program) := by
  have key : ∀ stmt, StmtOK stmt := fun stmt =>
    @Bil.Stmt.rec StmtOK ProgramOK move_ok jmp_ok special_ok (fun _ _ hb => while_ok hb) (fun _ _ _ hy hn => ifElse_ok hy hn)
      cpuExn_ok program_nil_ok (fun _ _ hs hr => program_cons_ok hs hr) stmt
  have keyP : ∀ program, ProgramOK program := fun program =>
    @Bil.Stmt.rec_1 StmtOK ProgramOK move_ok jmp_ok special_ok (fun _ _ hb => while_ok hb) (fun _ _ _ hy hn => ifElse_ok hy hn)
      cpuExn_ok program_nil_ok (fun _ _ hs hr => program_cons_ok hs hr) program
  exact ⟨key, keyP⟩

/-- A lowered statement. -/
theorem lowerStmt_correct {first second : Lowering} {stmt : Bil.Stmt} {terminated : Bool} {effect : Nat} (wf : LayoutWF first)
    (heff : Lowering.effectSlot first = some effect) (hlow : effect < Lowering.nextSlot first)
    (h : lowerStmt first stmt = some (second, terminated)) :
    ∃ new, Appended first second new ∧
      LowerOK first second new terminated (fun fuel state => Bil.execStmt fuel state stmt) :=
  lowered_all.1 stmt first second terminated effect wf heff hlow h

/-- The operations of a lowered program, from a machine that holds the environment, end the way the interpreter ends on
that program. It runs off its end with the machine holding the environment of the interpreter, or returns the target of
its jump with 1 in the effect slot and likewise. The one other way to end is a loop that uses up its 100000 iterations,
with 2 in the effect slot, which the runner turns into an error. -/
theorem lowerStatements_correct {first second : Lowering} {program : Bil.Program} {terminated : Bool} {effect : Nat}
    (wf : LayoutWF first) (heff : Lowering.effectSlot first = some effect) (hlow : effect < Lowering.nextSlot first)
    (h : lowerStatements first program = some (second, terminated)) :
    ∃ new, Appended first second new ∧
      LowerOK first second new terminated (fun fuel state => Bil.execProgram fuel state program) :=
  lowered_all.2 program first second terminated effect wf heff hlow h

/-- The whole of it: from a first lowering with no operations and an effect slot that no variable has, a machine that
holds the environment, and any fuel with which the interpreter has an outcome. -/
theorem lowerStatements_run {first second : Lowering} {program : Bil.Program} {terminated : Bool} {effect : Nat}
    (wf : LayoutWF first) (hops : Lowering.ops first = []) (heff : Lowering.effectSlot first = some effect)
    (hlow : effect < Lowering.nextSlot first) (hfree : ∀ var, (var, effect) ∉ Lowering.layout second)
    (h : lowerStatements first program = some (second, terminated)) (fuel : Nat) (state : Bil.State)
    (result : Bil.State × Bil.Effect) (machine : Machine) (hag : Agrees state.env machine second)
    (hex : Bil.execProgram fuel state program = .ok result) :
    Outcome first second second (Lowering.ops second ++ []) (Lowering.ops second ++ [], machine) [] effect terminated result := by
  obtain ⟨new, a, ok⟩ := lowerStatements_correct wf heff hlow h
  have hnew : Lowering.ops second = new := by rw [a.ops, hops]; simp
  have ctx : Context first second second new (Lowering.ops second ++ []) [] effect := {
    effectSlot := heff
    effectLow := hlow
    effectFree := hfree
    wfGlobal := a.wf
    sub := Sub.refl second
    split := ⟨[], by rw [hnew]; simp⟩
    distinct := by rw [hnew]; simpa using a.labels }
  have := ok fuel state result second _ [] effect machine ctx hag hex
  rw [hnew] at this ⊢
  exact this

end Statements

/-! ### Native accesses, the address space and the graph -/

section Accesses

open Bap.Primus.Lifted Bap.Proofs.Primus Bap.Emu
open_private Bap.Primus.Lifted Bap.Primus.Lifted Lowering Lowering.wrapFaults Lowering.memory wrapSafe useMemoryAt lowerExp lowerMove
  useMemory blockExit directEdges closedTarget closedTarget.closed BlockExit laterWrites

/-- Without an observer that rejects them, an access on a memory narrower than 64 bits that lowers has one byte, which
cannot pass the end of the address space. So native code and the machine whose view wraps have the same access. -/
theorem wrapSafe_narrow {lowering : Lowering} {var : Bap.Var} {size width c : Nat} (h : wrapSafe lowering var size = true)
    (ht : var.typ = .mem width c) (hw : width < 64) (hf : Lowering.wrapFaults lowering = false) : size = 1 := by
  simp only [wrapSafe, ht] at h
  have : ¬ 64 ≤ width := by omega
  simp_all

/-- The one byte is at the address itself. -/
theorem single_byte_in_range {width : Nat} (address : BitVec width) (hw : width ≤ 64) :
    (address.setWidth 64).toNat + 1 ≤ 2 ^ width := by
  have h1 := address.isLt
  have h2 : 2 ^ width ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  omega

/-- An access that passes the end of an address space is rejected, when no region goes past that end: the emulator's
observer faults before native code touches anything. So in the emulator a multi-byte access at the end of a narrow
address space faults, in native code as in the interpreter. -/
theorem accessFault_past_end {regions : List Region} {width address size : Nat} {write : Bool}
    (hspace : ∀ region ∈ regions, region.address + region.data.size ≤ 2 ^ width) (hpast : 2 ^ width < address + size)
    (hsize : 0 < size) : (accessFault regions write address size).isSome = true := by
  have hslow : (accessFaultSlow regions write address size).isSome = true := by
    let offset := if address ≤ 2 ^ width then 2 ^ width - address else 0
    have hoffset : offset < size := by
      simp only [offset]
      split <;> omega
    have hnone : lookupRegion regions (address + offset) = none := by
      apply List.find?_eq_none.2
      intro region hr hc
      have hb := hspace region hr
      simp only [Region.contains, Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [offset] at hc
      split at hc <;> omega
    unfold accessFaultSlow
    rw [List.find?_isSome]
    refine ⟨offset, List.mem_range.2 hoffset, ?_⟩
    simp [hnone]
  unfold accessFault
  split
  · next region hl =>
    split
    · next hallowed =>
      exfalso
      have hr : region ∈ regions := List.mem_of_find?_eq_some hl
      have hb := hspace region hr
      simp only [accessAllowed, Bool.and_eq_true, decide_eq_true_eq] at hallowed
      omega
    · exact hslow
  · exact hslow

/-! The way into and out of native code. -/

open_private Bap.Primus.Lifted Bap.Primus.Lifted Lowering.layout Lowering.inputs Lowering.outputs Lowering.flags Lowering.nextSlot
  Lowering.ops Lowering.effectSlot Lowering.nextLabel Operand encodeState syncState syncUpdates reachedOutputs slotBits withoutBindings
  immediate widthOf sameBytes definitelyWritten flagOutputs enterBlock freshLabel codeSite setEffect jumpConstant
  closedTarget.closed
open_private Bap.Proofs.Primus Bap.Proofs.Primus asBits_ok bind_ok

/-- A slot, read back with the width of its variable, is what it holds. -/
theorem slotBits_holds {width : Nat} {slot : UInt64} {bits : BitVec width} (h : Holds slot.toBitVec bits) :
    slotBits width slot = bits := by
  have h : slot.toBitVec.toNat = bits.toNat := h
  unfold slotBits
  split
  · next hw =>
    subst hw
    exact BitVec.eq_of_toNat_eq h
  · apply BitVec.eq_of_toNat_eq
    have hn : slot.toNat = bits.toNat := h
    simp only [BitVec.toNat_ofNat, hn]
    exact Nat.mod_eq_of_lt bits.isLt

private theorem encode_fold (env : Bil.Env) (inputs : List Bap.Var) (layout : List (Bap.Var × Nat)) (init result : Array UInt64)
    (hb : ∀ b ∈ layout, b.2 < init.size) (hd : layout.Pairwise fun left right => left.2 ≠ right.2)
    (h : layout.foldlM (init := init) (fun slots binding => do
      let var := binding.1
      match Bil.lookup env var with
      | .ok value =>
        let ⟨width, value⟩ ← Value.asBits value
        match widthOf var with
        | some expected =>
          if width == expected then .ok (slots.set! binding.2 (immediate value))
          else .error s!"variable {var.name} has width {width}, expected {expected}"
        | none => .error s!"unsupported variable {var.name}"
      | .error error =>
        if inputs.contains var then .error error else .ok slots) = .ok result) :
    result.size = init.size ∧ (∀ b ∈ layout, ∀ value, Bil.lookup env b.1 = .ok value →
      ∃ (width : Nat) (bits : BitVec width), value = .bits bits ∧ widthOf b.1 = some width ∧
        Holds (result.getD b.2 0).toBitVec bits) ∧
      ∀ index, (∀ b ∈ layout, b.2 ≠ index) → result.getD index 0 = init.getD index 0 := by
  induction layout generalizing init with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, by simp, fun _ _ => rfl⟩
  | cons head rest ih =>
    obtain ⟨hne, hrest⟩ := List.pairwise_cons.1 hd
    simp only [List.foldlM_cons] at h
    obtain ⟨mid, h1, h2⟩ := bind_ok h
    have hsame : ∃ value, mid = init ∧ (∀ v, Bil.lookup env head.1 = .ok v → False) ∨
        (Bil.lookup env head.1 = .ok value ∧ ∃ (width : Nat) (bits : BitVec width), value = .bits bits ∧ widthOf head.1 = some width ∧
          mid = init.set! head.2 (immediate bits)) := by
      cases hl : Bil.lookup env head.1 with
      | error e =>
        refine ⟨.undefined, Or.inl ⟨?_, by simp⟩⟩
        simp only [hl] at h1
        split at h1
        · simp at h1
        · simpa using h1.symm
      | ok value =>
        refine ⟨value, Or.inr ⟨rfl, ?_⟩⟩
        simp only [hl] at h1
        obtain ⟨⟨width, bits⟩, h3, h4⟩ := bind_ok h1
        simp only at h4
        split at h4
        · next expected hw =>
          split at h4
          · next hweq =>
            have hweq := eq_of_beq hweq
            subst hweq
            simp only [Except.ok.injEq] at h4
            exact ⟨width, bits, asBits_ok h3, hw, h4.symm⟩
          · simp at h4
        · simp at h4
    have hsize : mid.size = init.size := by
      obtain ⟨_, ⟨rfl, _⟩ | ⟨_, _, _, _, _, rfl⟩⟩ := hsame
      · rfl
      · simp
    obtain ⟨r1, r2, r3⟩ := ih mid (fun b hmem => by rw [hsize]; exact hb b (List.mem_cons_of_mem _ hmem)) hrest h2
    refine ⟨by rw [r1, hsize], ?_, ?_⟩
    · intro b hmem value hl
      rcases List.mem_cons.1 hmem with rfl | hmem
      · obtain ⟨_, ⟨_, hn⟩ | ⟨hl', w, bits, hv, hw, hm⟩⟩ := hsame
        · exact (hn value hl).elim
        · rw [hl] at hl'
          simp only [Except.ok.injEq] at hl'
          subst hl'
          refine ⟨w, bits, hv, hw, ?_⟩
          rw [r3 _ fun x hx => (hne x hx).symm, hm]
          have hbound := hb b List.mem_cons_self
          have hget : (init.set! b.2 (immediate bits)).getD b.2 0 = immediate bits := by
            simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, hbound]
          rw [hget]
          have hle := ((widthOf_some_iff _ _).1 hw).2.2
          show (immediate bits).toBitVec.toNat = bits.toNat
          simp only [immediate, UInt64.toBitVec_ofNat, BitVec.toNat_ofNat]
          exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le bits.isLt (Nat.pow_le_pow_right (by decide) hle))
      · exact r2 b hmem value hl
    · intro index hi
      rw [r3 index fun b hm => hi b (List.mem_cons_of_mem _ hm)]
      obtain ⟨_, ⟨rfl, _⟩ | ⟨_, _, _, _, _, rfl⟩⟩ := hsame
      · rfl
      · have hne' : head.2 ≠ index := hi head List.mem_cons_self
        simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hne']

/-- `encodeState` makes a machine that holds the environment: each variable with a value has it in its slot. -/
theorem encodeState_holds {lowering : Lowering} {env : Bil.Env} {slots : Array UInt64} (wf : LayoutWF lowering)
    (h : encodeState lowering env = .ok slots) (binding : Bap.Var × Nat) (hb : binding ∈ Lowering.layout lowering) (value : Bap.Value)
    (hl : Bil.lookup env binding.1 = .ok value) :
    ∃ (width : Nat) (bits : BitVec width), value = .bits bits ∧ widthOf binding.1 = some width ∧
      Holds (slots.getD binding.2 0).toBitVec bits :=
  (encode_fold env (Lowering.inputs lowering) (Lowering.layout lowering) _ slots
    (fun b hm => by simpa using wf.bound b hm) wf.slotsDistinct h).2.1 binding hb value hl

/-- `syncState` writes back the value of an output that the run reached, when the output has one slot. -/
theorem syncState_output {lowering : Lowering} {state : Bil.State} {slots : Array UInt64} {var : Bap.Var} {slot width : Nat}
    (hm : (var, slot) ∈ reachedOutputs lowering slots) (hw : widthOf var = some width)
    (hu : ∀ other, (var, other) ∈ reachedOutputs lowering slots → other = slot) :
    Bil.lookup (syncState lowering state slots).env var = .ok (.bits (slotBits width (slots.getD slot 0))) := by
  have key : (syncUpdates (reachedOutputs lowering slots) slots).find? (fun binding => binding.1 == var) =
      some (var, .bits (slotBits width (slots.getD slot 0))) := by
    generalize reachedOutputs lowering slots = outputs at hm hu
    induction outputs with
    | nil => simp at hm
    | cons head rest ih =>
      obtain ⟨hv, hs⟩ := head
      by_cases he : hv = var
      · subst he
        have hslot : hs = slot := hu hs List.mem_cons_self
        subst hslot
        simp [syncUpdates, hw]
      · have hm' : (var, slot) ∈ rest := by
          rcases List.mem_cons.1 hm with he' | hm'
          · simp only [Prod.mk.injEq] at he'
            exact absurd he'.1.symm he
          · exact hm'
        have hi := ih hm' fun other ho => hu other (List.mem_cons_of_mem _ ho)
        have hb : (hv == var) = false := by simpa using he
        simp only [syncUpdates, List.foldr_cons] at hi ⊢
        cases hwv : widthOf hv with
        | none => simpa [hwv] using hi
        | some w =>
          simp only [hwv, List.find?_cons, hb]
          exact hi
  simp only [syncState, Bil.lookup, List.find?_append, key]
  rfl

/-- An output whose flag says that the run did not reach a write of it is not written back. -/
theorem reachedOutputs_unflagged {lowering : Lowering} {slots : Array UInt64} {output : Bap.Var × Nat} {flag : Nat × Nat}
    (hf : (Lowering.flags lowering).find? (fun flag => flag.1 == output.2) = some flag) (hz : slots.getD flag.2 0 = 0)
 : output ∉ reachedOutputs lowering slots := by
  have hne : (Lowering.flags lowering).isEmpty = false := by
    cases hfl : Lowering.flags lowering with
    | nil => rw [hfl] at hf; simp at hf
    | cons _ _ => rfl
  simp only [reachedOutputs, hne, Bool.false_eq_true, ↓reduceIte, List.mem_filter, not_and]
  intro _
  simp [hf, hz]

/-- The seed of a range is where nothing is written yet. -/
theorem definitelyWritten_seed (seed : Nat) (blocks : List Block) (edges : List (Nat × Nat)) (writes : Block → List Bap.Var) :
    definitelyWritten seed blocks edges writes seed = [] := by
  unfold definitelyWritten
  cases hl : blocks.length with
  | zero =>
    have : blocks = [] := List.eq_nil_of_length_eq_zero hl
    subst this
    simp
  | succ n =>
    rw [List.range_succ, List.foldl_append]
    simp

/-- A cached block is found by its bytes: `sameBytes` is equality of them. -/
theorem sameBytes_eq {left right : ByteArray} (h : sameBytes left right = true) : left = right := by
  simp only [sameBytes, Bool.and_eq_true, beq_iff_eq, Nat.all_eq_finRange_all, List.all_eq_true] at h
  obtain ⟨hs, ha⟩ := h
  cases left with
  | mk l =>
    cases right with
    | mk r =>
      have hs' : l.size = r.size := hs
      congr 1
      apply Array.ext hs'
      intro i h1 h2
      have := ha ⟨i, h1⟩ (List.mem_finRange _)
      simpa [ByteArray.get!, h1, h2, hs'] using this

theorem peekByte_eq {width : Nat} (memory : Bap.Memory width) (address : Nat) (h : address < 2 ^ width) :
    peekByte memory address = Bap.Memory.readByte memory (BitVec.ofNat width address) := by
  simp only [peekByte, Bap.Memory.readByte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  rfl

/-- A closed target is the same value in every environment. -/
private theorem closed_evalExp (exp : Bil.Exp) (env : Bil.Env) (h : closedTarget.closed exp = true) :
    Bil.evalExp env exp = Bil.evalExp [] exp := by
  induction exp with
  | int value => rfl
  | bin op left right ihl ihr =>
    simp only [closedTarget.closed, Bool.and_eq_true] at h
    rw [Bil.evalExp, Bil.evalExp, ihl h.1, ihr h.2]
  | un op value ih =>
    simp only [closedTarget.closed] at h
    rw [Bil.evalExp, Bil.evalExp, ih h]
  | cast kind width value ih =>
    simp only [closedTarget.closed] at h
    rw [Bil.evalExp, Bil.evalExp, ih h]
  | _ => simp [closedTarget.closed] at h

/-- A target that a range goes to directly is where the interpreter jumps, in whatever environment it runs. This is what
makes a pc-relative branch an edge of the graph. -/
theorem closedTarget_sound {target : Bil.Exp} {address : Nat} (h : closedTarget target = some address) (env : Bil.Env) :
    ∃ (width : Nat) (value : BitVec width), Bil.evalExp env target = .ok (.bits value) ∧ width ≤ 64 ∧ value.toNat = address := by
  unfold closedTarget at h
  split at h
  · next hc =>
    split at h
    · next width value he =>
      split at h
      · next hw =>
        simp only [Option.some.injEq] at h
        exact ⟨width, value, by rw [closed_evalExp _ _ hc, he], hw, h⟩
      · simp at h
    · simp at h
  · simp at h

/-- The way into a block of a range over an edge starts with the check of the budget, and leaving with no budget left
sets the effect of a jump to the block, whose hooks are the next step's to fire. -/
theorem enterBlock_starts {lowering : Lowering} {effect : Nat} (budget observed address : Nat) (guarded : Bool)
    (h : Lowering.effectSlot lowering = some effect) :
    ∃ rest, Lowering.ops (enterBlock lowering budget observed address guarded) = Lowering.ops lowering ++
      [.branch budget (Lowering.nextLabel lowering) (Lowering.nextLabel lowering + 1), .label (Lowering.nextLabel lowering + 1),
        .set effect 1, .jump (UInt64.ofNat address), .label (Lowering.nextLabel lowering)] ++ rest := by
  simp only [enterBlock, freshLabel, jumpConstant, setEffect, h]
  split <;> simp [codeSite, setEffect, List.append_assoc]

end Accesses

end Bap.Proofs.Jit
