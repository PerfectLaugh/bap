import Lean
import Bap.Primus.Lifted
import Bap.Proofs.Emu
import Bap.Proofs.Primus
import Bap.Proofs.JitProgress

open Lean Elab Command in
/-- Bring private declarations of module `mod`, namespace `ns`, into scope by short name. -/
local elab "open_private " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }


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
  cases h : Lowering.effectSlot lowering <;> simp [jumpConstant, setEffect, h, temporary]

theorem jumpSlot_ops (lowering : Lowering) (target : Nat) :
    Lowering.ops (jumpSlot lowering target) =
      Lowering.ops lowering ++ [.set (setEffect lowering 1).2 1] ++ [.jumpSlot target] := by
  cases h : Lowering.effectSlot lowering <;> simp [jumpSlot, setEffect, h, temporary]

/-- The jump effect slot is the one `nativeResult` later reads back. -/
theorem jumpConstant_effect (lowering : Lowering) (target : UInt64) :
    Lowering.effectSlot (jumpConstant lowering target) = some (setEffect lowering 1).2 := by
  cases h : Lowering.effectSlot lowering <;> simp [jumpConstant, setEffect, h, temporary]

/-- Code sites clear the effect, publish the pc to the observer, and checkpoint the outputs. -/
theorem codeSite_ops (lowering : Lowering) (pc : Nat) :
    Lowering.ops (codeSite lowering pc) =
      Lowering.ops lowering ++ [.set (setEffect lowering 0).2 0] ++ [.code (setEffect lowering 0).2 (UInt64.ofNat pc)] := by
  cases h : Lowering.effectSlot lowering <;> simp [codeSite, setEffect, h, temporary]

theorem codeSite_checkpoint (lowering : Lowering) (pc : Nat) :
    Lowering.checkpoints (codeSite lowering pc) =
      Lowering.checkpoints lowering ++ [(pc, Lowering.outputs lowering)] := by
  cases h : Lowering.effectSlot lowering <;> simp [codeSite, setEffect, h, temporary]

/-- Sign extension writes to a fresh temporary and never clobbers its source slot. -/
theorem signExtend_fresh (lowering : Lowering) (width source : Nat) :
    (signExtend lowering width source).2 = Lowering.nextSlot lowering ∧
      Lowering.ops (signExtend lowering width source).1 =
        Lowering.ops lowering ++ [.signExtend width (Lowering.nextSlot lowering) source] := by
  simp [signExtend, temporary]

/-- Edges leaving the compiled range exit through the jump protocol rather than a goto. -/
theorem graphEdgeOps_external (lowering : Lowering) (labels : List (Nat × Nat)) (edges : List (Nat × Nat))
    (source target : Nat) (he : edges.contains (source, target) = false) :
    ∃ ops, graphEdgeOps lowering labels edges source target = some ops ∧ ops.getLast? = some (.jump (UInt64.ofNat target)) := by
  simp only [graphEdgeOps, he, Bool.false_eq_true, ↓reduceIte]
  refine ⟨_, rfl, ?_⟩
  cases h : Lowering.effectSlot lowering <;> simp [jumpConstant, setEffect, temporary]

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
      rw [ite_eq_right_of_eq_false _ _ (eq_false (hne n (by omega) (by omega)))]
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
    cases endian <;> simp only [beq_self_eq_true, ↓reduceIte] <;>
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
open_private Bap.Proofs.Primus Bap.Proofs.Primus flag obind pairwise_same lookup_bind_same lookup_bind_other writeVar_inv
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
  /-- What is not what the run started from was moved to, or is the memory. -/
  changed : ∀ var, Bil.lookup env var ≠ Bil.lookup machine.origin var →
    Lowering.memory global = some var ∨ ∃ slot, (var, slot) ∈ Lowering.layout global ∧ machine.moved slot = true
  /-- What was moved to has a value. -/
  bound : ∀ binding ∈ Lowering.layout global, machine.moved binding.2 = true → ∃ value, Bil.lookup env binding.1 = .ok value

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
    cases op <;> first | (exfalso; simp [isExpressionOp] at hop; done) | (rw [labelsOf_other (by intro l; simp)]; exact hrest)

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

/-- The iterations that a loop of native code has, which is the fuel that the interpreter gets (`Bil.runObserved`). -/
def loopLimit : Nat := 100000

/-- A run that a loop ended, out of iterations. -/
def Exhausts (program : List Op) (cfg : Cfg) (effect : Nat) : Prop :=
  ∃ target rest machine, Run program cfg (.jump target :: rest, machine) ∧ machine.slots effect = 2

/-- Like `Frames`, for a run that left, which set the effect. -/
def FramesOut (effect low high : Nat) (global : Lowering) (first second : Machine) : Prop :=
  second.view = first.view ∧ ∀ slot, slot ≠ effect → (slot < low ∨ high ≤ slot) → (∀ var, (var, slot) ∉ Lowering.layout global) →
    second.slots slot = first.slots slot

theorem Frames.thenOut {effect low high : Nat} {global : Lowering} {a b c : Machine} (h1 : Frames low high global a b)
    (h2 : FramesOut effect low high global b c) : FramesOut effect low high global a c :=
  ⟨h2.1.trans h1.1, fun slot he hs hv => (h2.2 slot he hs hv).trans (h1.2 slot hs hv)⟩

theorem FramesOut.weaken {effect low high low' high' : Nat} {global : Lowering} {a b : Machine} (h : FramesOut effect low high global a b)
    (hl : low' ≤ low) (hh : high ≤ high') : FramesOut effect low' high' global a b :=
  ⟨h.1, fun slot he hs hv => h.2 slot he (by omega) hv⟩

/-- How a run of the operations of a statement ends, given what the interpreter says about it. `limit` is what must hold
of the fuel of the interpreter for a loop to run out of iterations before the interpreter ran out of fuel. -/
def Outcome (limit : Prop) (first second global : Lowering) (program : List Op) (cfg : Cfg) (tail : List Op) (effect : Nat)
    (terminated : Bool) (result : Bil.State × Bil.Effect) : Prop :=
  (limit ∧ Exhausts program cfg effect) ∨
    match result.2 with
    | .normal => terminated = false ∧ ∃ machine, Run program cfg (tail, machine) ∧ Agrees result.1.env machine global ∧
        Frames (Lowering.nextSlot first) (Lowering.nextSlot second) global cfg.2 machine
    | .jump target => ∃ value machine, Returns program cfg value machine ∧ Holds value target ∧
        machine.slots effect = 1 ∧ Agrees result.1.env machine global ∧
        FramesOut effect (Lowering.nextSlot first) (Lowering.nextSlot second) global cfg.2 machine
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

/-- A lowered statement, with the executions of it. A loop only runs out of iterations with `cap` fuel at least. -/
def LowerOK (cap : Nat) (first second : Lowering) (new : List Op) (terminated : Bool) (exec : Nat → Bil.State → Except String (Bil.State × Bil.Effect)) :
    Prop :=
  ∀ (fuel : Nat) (state : Bil.State) (result : Bil.State × Bil.Effect) (global : Lowering) (program tail : List Op) (effect : Nat)
    (machine : Machine), Context first second global new program tail effect → Agrees state.env machine global →
    exec fuel state = .ok result → Outcome (cap ≤ fuel) first second global program (new ++ tail, machine) tail effect terminated result

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
    ∃ (fuel' : Nat) (bit : BitVec 1), fuel = fuel' + 1 ∧ Bil.evalExp state.env condition = .ok (.bits bit) ∧
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
      exact ⟨fuel, bit, rfl, by rw [h1, asBits_ok h3], h4⟩
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
      rw [ite_eq_left hb]
      refine ⟨(next, effect), h5, ?_⟩
      cases effect <;> simp_all
    · next hb =>
      rw [ite_eq_right hb]
      simpa using h4.symm
  · simp at h4

private theorem exec_cons {fuel : Nat} {state : Bil.State} {stmt : Bil.Stmt} {rest : Bil.Program}
    {result : Bil.State × Bil.Effect} (h : Bil.execProgram fuel state (stmt :: rest) = .ok result) :
    ∃ (fuel' : Nat) (first : Bil.State × Bil.Effect), fuel = fuel' + 1 ∧ Bil.execStmt fuel' state stmt = .ok first ∧
      match first.2 with
      | .normal => Bil.execProgram fuel' first.1 rest = .ok result
      | other => result = (first.1, other) := by
  cases fuel with
  | zero => simp [Bil.execProgram] at h
  | succ fuel =>
    simp only [Bil.execProgram] at h
    obtain ⟨⟨next, effect⟩, h1, h2⟩ := bind_ok h
    refine ⟨fuel, (next, effect), rfl, h1, ?_⟩
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
  changed := by
    intro var hne
    rw [runOps_origin] at hne
    rcases h.changed var hne with hm | ⟨slot, hm, hmoved⟩
    · exact Or.inl hm
    · exact Or.inr ⟨slot, hm, runOps_moved_mono _ hmoved⟩
  bound := by
    intro binding hb hmoved
    rcases runOps_moved_new hmoved with hm | ⟨op, hop, hd⟩
    · exact h.bound binding hb hm
    · obtain ⟨_, hlt, hfree⟩ := he.writes op hop _ hd
      rcases hs.later binding hb with hl | hl
      · exact absurd hl (hfree binding.1)
      · omega

theorem _root_.Bap.Proofs.Primus.Extends.frames {first second global : Lowering} {new : List Op} (he : Extends first second new) (_hs : Sub second global)
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
    rw [ite_eq_right hne]
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
    simp only [Option.some.injEq, Prod.mk.injEq] at h
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
    simp only [hpure, Bool.false_eq_true, ite_false] at h
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
      · simp only [temporary, Option.some.injEq, Prod.mk.injEq] at h
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
    simp only [writeVar, hw, bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := slot_fields first var
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨f5, f6⟩

/-- A move to a register. -/
theorem lowerMove_register_ok {first second : Lowering} {dst : Bap.Var} {value : Bil.Exp} {width : Nat} (wf : LayoutWF first)
    (hw : widthOf dst = some width) (h : lowerMove first dst value = some second) :
    ∃ new, Appended first second new ∧ LowerOK loopLimit first second new false (fun fuel state => Bil.execStmt fuel state (.move dst value)) := by
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
    simp only [Option.some.injEq] at h
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
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro binding hb val hlookup
        by_cases hbd : binding.1 = dst
        · have hsame : binding = (dst, (slot mid dst).2) := pairwise_same ctx.wfGlobal.varsDistinct hb hdstG hbd
          subst hsame
          rw [lookup_bind_same] at hlookup
          simp only [Except.ok.injEq] at hlookup
          subst hlookup
          refine ⟨w, bits, rfl, hw, ?_⟩
          simp only [Machine.markMove_slots, ↓reduceIte]
          exact hvalue
        · rw [lookup_bind_other hbd] at hlookup
          obtain ⟨w', x, hv, hwb, hholds⟩ := hafter.slots _ hb _ hlookup
          refine ⟨w', x, hv, hwb, ?_⟩
          have hne : binding.2 ≠ (slot mid dst).2 := by
            intro e
            exact hbd (congrArg Prod.fst (pairwise_same ctx.wfGlobal.slotsDistinct hb hdstG e))
          simp only [Machine.markMove_slots, hne, ↓reduceIte]
          exact hholds
      · intro var hv w' cells hl
        have hne : var ≠ dst := by
          intro he'
          subst he'
          rw [lookup_bind_same] at hl
          simp at hl
        rw [lookup_bind_other hne] at hl
        exact hafter.memory var hv w' cells hl
      · intro var hne
        by_cases hvd : var = dst
        · rw [hvd]
          exact Or.inr ⟨(slot mid dst).2, hdstG, by simp [Machine.markMove]⟩
        · rw [lookup_bind_other hvd] at hne
          rcases hafter.changed var hne with hm | ⟨s, hm, hmoved⟩
          · exact Or.inl hm
          · exact Or.inr ⟨s, hm, by simp [Machine.markMove, hmoved]⟩
      · intro binding hb hmoved
        by_cases hbd : binding.1 = dst
        · rw [hbd, lookup_bind_same]
          exact ⟨_, rfl⟩
        · rw [lookup_bind_other hbd]
          simp only [Machine.markMove, Bool.or_eq_true, beq_iff_eq] at hmoved
          rcases hmoved with he' | hmoved
          · exact absurd (congrArg Prod.fst (pairwise_same ctx.wfGlobal.slotsDistinct hb hdstG he')) hbd
          · exact hafter.bound binding hb hmoved
    · have hf := he.frames hsubMid machine
      rw [runOps_append]
      simp only [runOps_cons, runOps_nil, Bap.Proofs.Primus.step]
      refine ⟨hf.1, ?_⟩
      intro slot' hslot' hfree
      have hdstG : (dst, (slot mid dst).2) ∈ Lowering.layout global := ctx.sub.mono _ (by
        rw [fLayout, hlayout]
        exact hdstMem)
      have hne : slot' ≠ (slot mid dst).2 := fun e => hfree dst (e ▸ hdstG)
      simp only [Machine.markMove_slots, hne, ↓reduceIte]
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
      LowerOK loopLimit first second new false (fun fuel state => Bil.execStmt fuel state (.move dst (.store memory address stored endian size))) := by
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
  simp only [hchecks, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
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
    refine ⟨?_, ?_, ?_, ?_⟩
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
    · intro var hne
      by_cases hvd : var = dst
      · subst hvd
        exact Or.inl hmemVar
      · rw [lookup_bind_other hvd] at hne
        exact hag2.changed var hne
    · intro binding hb hmoved
      have hne : binding.1 ≠ dst := by
        intro he'
        obtain ⟨_, _, hbits, _, _⟩ := hag.slots binding hb (.memory cells) (he' ▸ hlookup)
        simp at hbits
      rw [lookup_bind_other hne]
      exact hag2.bound binding hb hmoved
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
  changed := h.changed
  bound := h.bound

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
    ∃ new, Appended first second new ∧ LowerOK loopLimit first second new terminated (fun fuel state => Bil.execStmt fuel state stmt)

private def ProgramOK (program : Bil.Program) : Prop :=
  ∀ (first second : Lowering) (terminated : Bool) (effect : Nat), LayoutWF first → Lowering.effectSlot first = some effect →
    effect < Lowering.nextSlot first → lowerStatements first program = some (second, terminated) →
    ∃ new, Appended first second new ∧ LowerOK (loopLimit + 1) first second new terminated (fun fuel state => Bil.execProgram fuel state program)

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
    refine Or.inr ⟨(immediate target : UInt64).toBitVec, machine.write effect' (1 : UInt64).toBitVec, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨tail, Or.inl ⟨immediate target, Run.linear (op := .set effect' 1) rfl _ _, rfl⟩⟩
    · show (immediate target).toBitVec.toNat = target.toNat
      simp only [immediate]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le target.isLt (Nat.pow_le_pow_right (by decide) hw))
    · simp only [Machine.write_slots, ↓reduceIte]
      rfl
    · exact hag.write_free ctx.effectFree _
    · exact ⟨rfl, fun slot he _ _ => by simp [Machine.write_slots, he]⟩
  · simp at h

private theorem jmp_slot_ok (target : Bil.Exp) (hnot : ∀ (width : Nat) (value : BitVec width), target ≠ .int value) :
    StmtOK (.jmp target) := by
  intro first second terminated effect wf heff hlow h
  rw [lowerStmt] at h
  · obtain ⟨⟨mid, operand⟩, h1, h⟩ := obind h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
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
      (runOps machine newE).write effect' (1 : UInt64).toBitVec, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨tail, Or.inr ⟨Operand.slot operand, ?_, rfl⟩⟩
      rw [List.append_assoc]
      exact (Run.ops (fun op hop => linear_of_expression (he.pure op hop)) _ machine).trans
        (Run.linear (op := .set effect' 1) rfl _ _)
    · show Holds (if Operand.slot operand = effect' then _ else _) bits
      rw [ite_eq_right hne]
      exact hvalue
    · simp only [Machine.write_slots, ↓reduceIte]
      rfl
    · exact hafter.write_free ctx.effectFree _
    · have hfm := he.frames hsub machine
      have hg2 : Lowering.nextSlot mid ≤ Lowering.nextSlot (jumpSlot mid (Operand.slot operand)) := a2.next
      refine ⟨hfm.1, fun slot hne hs hfree => ?_⟩
      simp only [Machine.write_slots, hne, ↓reduceIte]
      exact hfm.2 slot (by omega) hfree
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
    obtain ⟨fuel', ⟨st, eff⟩, hfuel, h2, h3⟩ := exec_cons hex
    rcases ok1 fuel' state (st, eff) global program tail effect' machine ctx hag h2 with hx | hn
    · exact Or.inl ⟨by omega, hx.2⟩
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
    obtain ⟨fuel', ⟨st, eff⟩, hfuel, h2, h3⟩ := exec_cons hex
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
    rw [show Outcome (loopLimit + 1 ≤ fuel) first second global program ((newS ++ newR) ++ tail, machine) tail effect' terminated result =
      Outcome (loopLimit + 1 ≤ fuel) first second global program (newS ++ (newR ++ tail), machine) tail effect' terminated result by rw [hcfg]]
    rcases ok1 fuel' state (st, eff) global program (newR ++ tail) effect' machine ctx1 hag h2 with hx | hn
    · exact Or.inl ⟨by omega, hx.2⟩
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
        · exact Or.inl ⟨by omega, Exhausts.prepend hrun hx.2⟩
        · refine Or.inr ?_
          obtain ⟨st2, eff2⟩ := result
          cases eff2 with
          | normal =>
            obtain ⟨ht, m2, hrun2, hag2, hf2⟩ := hn2
            refine ⟨ht, m2, hrun.trans hrun2, hag2, ?_⟩
            exact (hf1.weaken (Nat.le_refl _) a2.next).trans (hf2.weaken a1.next (Nat.le_refl _))
          | jump target =>
            obtain ⟨value, m2, hret, hheld, hone, hag2, hf2⟩ := hn2
            exact ⟨value, m2, Returns.prepend hrun hret, hheld, hone, hag2,
              (hf1.weaken (Nat.le_refl _) a2.next).thenOut (hf2.weaken a1.next (Nat.le_refl _))⟩
          | special message => exact absurd hn2 (by simp)
          | cpuExn number => exact absurd hn2 (by simp)
      | jump target =>
        simp only at h3
        subst h3
        obtain ⟨value, m2, hret, hheld, hone, hag2, hf2⟩ := hn
        exact Or.inr ⟨value, m2, hret, hheld, hone, hag2, hf2.weaken (Nat.le_refl _) a2.next⟩
      | special message => exact absurd hn (by simp)
      | cpuExn number => exact absurd hn (by simp)

/-- The core of a conditional, with the lowerings on the way abstract. -/
private theorem ifElse_core {first mid l0 yesEnd l1 noEnd second : Lowering} {condition : Bil.Exp} {yes no : Bil.Program}
    {operand : Operand} {yesDone noDone : Bool} {effect : Nat} (hyesOK : ProgramOK yes) (hnoOK : ProgramOK no)
    (wf : LayoutWF first) (heff : Lowering.effectSlot first = some effect) (hlow : effect < Lowering.nextSlot first)
    (h1 : lowerExp first condition = some (mid, operand)) (_hw : Operand.width operand = 1)
    (p0 : Pushed mid l0 [.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1),
      .label (Lowering.nextLabel mid)] 3)
    (hyes : lowerStatements l0 yes = some (yesEnd, yesDone))
    (p1 : Pushed yesEnd l1 ((if yesDone then [] else [.goto (Lowering.nextLabel mid + 2)]) ++ [.label (Lowering.nextLabel mid + 1)]) 0)
    (hno : lowerStatements l1 no = some (noEnd, noDone))
    (p2 : Pushed noEnd second ((if noDone then [] else [.goto (Lowering.nextLabel mid + 2)]) ++
      (if yesDone && noDone then [] else [.label (Lowering.nextLabel mid + 2)])) 0) :
    ∃ new, Appended first second new ∧
      LowerOK loopLimit first second new (yesDone && noDone) (fun fuel state => Bil.execStmt fuel state (.ifElse condition yes no)) := by
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
  obtain ⟨fuel', bit, hfuel, hev, hexec⟩ := exec_ifElse hex
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
    rw [ite_eq_left hbit] at hexec
    have hne : m1.slots (Operand.slot operand) ≠ 0 := (holds_condition hvalue).2 hbit
    have hbranch : Run program (.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1) ::
        .label (Lowering.nextLabel mid) :: rest, m1) (rest, m1) :=
      Run.branch (by rw [ite_eq_left hne]; exact hafterY)
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
    · refine Or.inl ⟨by omega, Exhausts.prepend hprefix ?_⟩
      rw [hrestEq]
      exact hx.2
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
        obtain ⟨value, m2, hret, hheld, hone, hag2, hf⟩ := hn
        refine ⟨value, m2, Returns.prepend hprefix ?_, hheld, hone, hag2, ?_⟩
        · rw [hrestEq]
          exact hret
        · have hg := g0.next
          have hn1 := aC.next
          have hs1 := g1.next
          have hs0 := aY.next
          have hs2 := aN.next
          have hs3 := g2.next
          exact (hf0.weaken (Nat.le_refl _) (by omega)).thenOut (hf.weaken (by omega) (by omega))
      | special message => exact absurd hn (by simp)
      | cpuExn number => exact absurd hn (by simp)
  · rw [ite_eq_right hbit] at hexec
    have hzero : m1.slots (Operand.slot operand) = 0 := by
      by_cases hz : m1.slots (Operand.slot operand) = 0
      · exact hz
      · exact absurd ((holds_condition hvalue).1 hz) hbit
    have hbranch : Run program (.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1) ::
        .label (Lowering.nextLabel mid) :: rest, m1) (newN ++ (gotoN ++ labelD) ++ tail, m1) :=
      Run.branch (by
        rw [ite_eq_right (by simpa using hzero)]
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
    · refine Or.inl ⟨by omega, Exhausts.prepend hprefix ?_⟩
      rw [hrestEq]
      exact hx.2
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
        obtain ⟨value, m2, hret, hheld, hone, hag2, hf⟩ := hn
        refine ⟨value, m2, Returns.prepend hprefix ?_, hheld, hone, hag2, ?_⟩
        · rw [hrestEq]
          exact hret
        · have hg := g0.next
          have hn1 := aC.next
          have hs1 := g1.next
          have hs0 := aY.next
          have hs2 := aN.next
          have hs3 := g2.next
          exact (hf0.weaken (Nat.le_refl _) (by omega)).thenOut (hf.weaken (by omega) (by omega))
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
    (h1 : lowerExp l3 condition = some (mid, operand)) (_hw : Operand.width operand = 1)
    (p1 : Pushed mid l4 [.branch (Operand.slot operand) (Lowering.nextLabel first + 2) (Lowering.nextLabel first + 3),
      .label (Lowering.nextLabel first + 2)] 0)
    (hbody : lowerStatements l4 body = some (bodyEnd, bodyDone))
    (p2 : Pushed bodyEnd l5 ((if bodyDone then [] else [.goto (Lowering.nextLabel first)]) ++ [.label (Lowering.nextLabel first + 4)]) 0)
    (p3 : Lowering.effectSlot l5 = some effect → Pushed l5 l6 [.set effect 2] 0)
    (p4 : Pushed l6 second [.jump exit, .label (Lowering.nextLabel first + 3)] 0) :
    ∃ new, Appended first second new ∧
      LowerOK loopLimit first second new false (fun fuel state => Bil.execStmt fuel state (.while condition body)) := by
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
      (machine.slots c).toNat < loopLimit → Agrees state.env machine global → Bil.execStmt fuel state (.while condition body) = .ok result →
      Outcome (loopLimit ≤ fuel + (machine.slots c).toNat) first second global program (loop, machine) tail effect' false result := by
    intro fuel
    induction fuel with
    | zero =>
      intro state result machine _ _ hex
      simp [Bil.execStmt] at hex
    | succ fuel ih =>
      intro state result machine hcount hag hex
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
      have hm0count : (m0.slots c).toNat = (machine.slots c).toNat + 1 ∧ (m0.slots (c + 2) ≠ 0 → loopLimit ≤ (machine.slots c).toNat + 1) ∧
          (m0.slots (c + 2) = 0 → (machine.slots c).toNat + 1 < loopLimit) := by
        have hsum : (machine.slots c + (1 : UInt64).toBitVec).toNat = (machine.slots c).toNat + 1 := by
          have h1 : (1 : UInt64).toBitVec.toNat = 1 := by decide
          rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt]
          have : (machine.slots c).toNat < 100000 := hcount
          omega
        simp only [m0, runOps_cons, runOps_nil, Bap.Proofs.Primus.step, Machine.write_slots, denoteBin]
        simp only [loopLimit] at hcount
        have hmod : ((machine.slots c).toNat + 1) % 18446744073709551616 = (machine.slots c).toNat + 1 := Nat.mod_eq_of_lt (by omega)
        simp [loopLimit, hmod]
        by_cases hk : 100000 ≤ (machine.slots c).toNat + 1
        · simp [flag]
          omega
        · simp [flag]
          omega
      by_cases hlimit : m0.slots (c + 2) ≠ 0
      · -- out of iterations
        refine Or.inl ⟨?_, exit, .label (l + 3) :: tail, m0.write effect' (2 : UInt64).toBitVec, ?_, ?_⟩
        · have := hm0count.2.1 hlimit
          omega
        · refine hrun0.trans (.step ?_ (Run.linear (op := .set effect' 2) rfl _ _))
          simp only [nextCfg, ite_eq_left hlimit, hafterExh]
          rfl
        · simp only [Machine.write_slots, ↓reduceIte]
          rfl
      · have hzero : m0.slots (c + 2) = 0 := by simpa using hlimit
        have hrun1 : Run program (loop, machine) (newC ++ [.branch (Operand.slot operand) (l + 2) (l + 3), .label (l + 2)] ++ newB ++ afterBody, m0) := by
          refine hrun0.trans (.step ?_ (.refl _))
          simp only [nextCfg, ite_eq_right hlimit, hafterCheck]
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
        · rw [ite_eq_left hbit] at hbranch
          obtain ⟨inner, hbodyExec, hinner⟩ := hbranch
          have hne : m1.slots (Operand.slot operand) ≠ 0 := (holds_condition hvalue).2 hbit
          have hrun3 : Run program (loop, machine) (newB ++ afterBody, m1) := by
            refine hrun2.trans (.step ?_ (.refl _))
            simp only [nextCfg, ite_eq_left hne, hafterBody]
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
          · exact Or.inl ⟨by have := hx.1; omega, Exhausts.prepend hrun3 hx.2⟩
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
              have hcm : (m2.slots c).toNat = (machine.slots c).toNat + 1 := by
                have hc1 := hf1.2 c (Or.inl (by rw [hnext0]; omega)) (hfree c (by omega) (by omega))
                have hc2 := hf.2 c (Or.inl (by have h1 := aC.next; have h2 := g1.next; rw [hnext0] at h1; omega)) (hfree c (by omega) (by omega))
                rw [hc2, hc1]
                exact hm0count.1
              have hcountNext : (m2.slots c).toNat < loopLimit := by
                have := hm0count.2.2 hzero
                omega
              rcases ih st result m2 hcountNext hag2 hinner with hx | hn2
              · exact Or.inl ⟨by have := hx.1; omega, Exhausts.prepend hrun4 hx.2⟩
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
                  obtain ⟨value, m3, hret, hheld, hone, hag3, hf3⟩ := hn2
                  exact ⟨value, m3, Returns.prepend hrun4 hret, hheld, hone, hag3, hfm2.thenOut hf3⟩
                | special message => exact absurd hn2 (by simp)
                | cpuExn number => exact absurd hn2 (by simp)
            | jump target =>
              simp only at hinner
              subst hinner
              obtain ⟨value, m3, hret, hheld, hone, hag3, hf3⟩ := hn
              exact Or.inr ⟨value, m3, Returns.prepend hrun3 hret, hheld, hone, hag3, hfm1.thenOut (hf3.weaken (by
                have h1 := g0.next
                have h2 := aC.next
                have h3 := g1.next
                omega) hEndNext)⟩
            | special message => exact absurd hn (by simp)
            | cpuExn number => exact absurd hn (by simp)
        · rw [ite_eq_right hbit] at hbranch
          subst hbranch
          have hzero1 : m1.slots (Operand.slot operand) = 0 := by
            by_cases hz : m1.slots (Operand.slot operand) = 0
            · exact hz
            · exact absurd ((holds_condition hvalue).1 hz) hbit
          refine Or.inr ⟨rfl, m1, ?_, hag1, hfm1⟩
          refine hrun2.trans (.step ?_ (.refl _))
          have hnz : ¬ (m1.slots (Operand.slot operand) ≠ 0) := by simpa using hzero1
          simp only [nextCfg, ite_eq_right hnz, hafterDone]
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
  rcases key fuel state result (machine.write c (0 : UInt64).toBitVec) (by simp [Machine.write_slots, loopLimit]) hag' hex with hx | hn
  · exact Or.inl ⟨by simpa [Machine.write_slots] using hx.1, Exhausts.prepend hstart hx.2⟩
  · refine Or.inr ?_
    obtain ⟨st, eff⟩ := result
    cases eff with
    | normal =>
      obtain ⟨ht, m3, hrun5, hag3, hf3⟩ := hn
      exact ⟨ht, m3, hstart.trans hrun5, hag3, hfs.trans hf3⟩
    | jump target =>
      obtain ⟨value, m3, hret, hheld, hone, hag3, hf3⟩ := hn
      exact ⟨value, m3, Returns.prepend hstart hret, hheld, hone, hag3, hfs.thenOut hf3⟩
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
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
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
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
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
      LowerOK loopLimit first second new terminated (fun fuel state => Bil.execStmt fuel state stmt) :=
  lowered_all.1 stmt first second terminated effect wf heff hlow h

/-- The operations of a lowered program, from a machine that holds the environment, end the way the interpreter ends on
that program. It runs off its end with the machine holding the environment of the interpreter, or returns the target of
its jump with 1 in the effect slot and likewise. The one other way to end is a loop that uses up its 100000 iterations,
with 2 in the effect slot, which the runner turns into an error, and only an interpreter with more fuel than that has a result then. -/
theorem lowerStatements_correct {first second : Lowering} {program : Bil.Program} {terminated : Bool} {effect : Nat}
    (wf : LayoutWF first) (heff : Lowering.effectSlot first = some effect) (hlow : effect < Lowering.nextSlot first)
    (h : lowerStatements first program = some (second, terminated)) :
    ∃ new, Appended first second new ∧
      LowerOK (loopLimit + 1) first second new terminated (fun fuel state => Bil.execProgram fuel state program) :=
  lowered_all.2 program first second terminated effect wf heff hlow h

/-- The whole of it: from a first lowering with no operations and an effect slot that no variable has, a machine that
holds the environment, and any fuel with which the interpreter has an outcome. -/
theorem lowerStatements_run {first second : Lowering} {program : Bil.Program} {terminated : Bool} {effect : Nat}
    (wf : LayoutWF first) (hops : Lowering.ops first = []) (heff : Lowering.effectSlot first = some effect)
    (hlow : effect < Lowering.nextSlot first) (hfree : ∀ var, (var, effect) ∉ Lowering.layout second)
    (h : lowerStatements first program = some (second, terminated)) (fuel : Nat) (state : Bil.State)
    (result : Bil.State × Bil.Effect) (machine : Machine) (hag : Agrees state.env machine second)
    (hex : Bil.execProgram fuel state program = .ok result) :
    Outcome (loopLimit + 1 ≤ fuel) first second second (Lowering.ops second ++ []) (Lowering.ops second ++ [], machine) [] effect terminated result := by
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
          simp only [immediate]
          exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le bits.isLt (Nat.pow_le_pow_right (by decide) hle))
      · exact r2 b hmem value hl
    · intro index hi
      rw [r3 index fun b hm => hi b (List.mem_cons_of_mem _ hm)]
      obtain ⟨_, ⟨rfl, _⟩ | ⟨_, _, _, _, _, rfl⟩⟩ := hsame
      · rfl
      · have hne' : head.2 ≠ index := hi head List.mem_cons_self
        simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, hne']

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
          simp only [List.find?_cons, hb]
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

/-! ### Whole ranges -/

section Graph
open Bap.Primus.Lifted Bap.Proofs.Primus Bap.Emu
open_private Bap.Primus.Lifted Bap.Primus.Lifted Lowering Lowering.ops Lowering.layout Lowering.nextSlot Lowering.memory
  Lowering.effectSlot Lowering.nextLabel Lowering.next Lowering.written Lowering.outputs Lowering.inputs Lowering.flags
  Lowering.checkpoints Lowering.budget Lowering.observed Lowering.wrapFaults Lowering.push Lowering.withWritten
  Operand Operand.slot Operand.width lowerExp lowerStatements setEffect temporary jumpConstant immediate widthOf
  blockExit BlockExit BlockExit.direct BlockExit.branch BlockExit.other BlockExit.fall closedTarget graphEdgeOps freshLabel enterBlock codeSite GraphPlan GraphPlan.seed GraphPlan.labels GraphPlan.edges
  GraphPlan.budget GraphPlan.observed GraphPlan.chained GraphPlan.definite GraphPlan.guarded lowerEntry lowerExit lowerBlock lowerBlocks lowerGraph
  lowerGraphChecked leadingMoves opSlots opLabels flagOutputs encodeState syncState syncUpdates reachedOutputs slotBits withoutBindings atCodeStop
  definitelyWritten writtenAt flagged flagSlots withControl graphInitial graphPlan chainedCount nativeOutcome
open_private Bap.Proofs.Primus Bap.Proofs.Primus obind pairwise_same lookup_bind_same lookup_bind_other bind_ok asBits_ok

/-- What runs after one step, where a code site goes on unless its observer stops the run. -/
def nextCfgAt (stops : Nat → Bool) (program : List Op) (cfg : Cfg) : Option Cfg :=
  match cfg with
  | (.code _ pc :: rest, machine) => if stops pc.toNat then none else some (rest, machine)
  | _ => nextCfg program cfg

/-- A run through code sites, which `nextCfgAt` makes deterministic as well. -/
inductive RunAt (stops : Nat → Bool) (program : List Op) : Cfg → Cfg → Prop
  | refl (cfg : Cfg) : RunAt stops program cfg cfg
  | step {first second last : Cfg} : nextCfgAt stops program first = some second → RunAt stops program second last →
      RunAt stops program first last

theorem RunAt.trans {stops : Nat → Bool} {program : List Op} {a b c : Cfg} (h1 : RunAt stops program a b)
    (h2 : RunAt stops program b c) : RunAt stops program a c := by
  induction h1 with
  | refl => exact h2
  | step hn _ ih => exact .step hn (ih h2)

theorem nextCfgAt_of_next {stops : Nat → Bool} {program : List Op} {a b : Cfg} (h : nextCfg program a = some b) :
    nextCfgAt stops program a = some b := by
  obtain ⟨ops, machine⟩ := a
  cases ops with
  | nil => simp [nextCfg] at h
  | cons op rest =>
    cases op
    case code => simp [nextCfg] at h
    all_goals exact h

theorem Run.toAt {stops : Nat → Bool} {program : List Op} {a b : Cfg} (h : Run program a b) : RunAt stops program a b := by
  induction h with
  | refl => exact .refl _
  | step hn _ ih => exact .step (nextCfgAt_of_next hn) ih

/-- A run that a loop ended, out of iterations. -/
def ExhaustsAt (stops : Nat → Bool) (program : List Op) (cfg : Cfg) (effect : Nat) : Prop :=
  ∃ target rest machine, RunAt stops program cfg (.jump target :: rest, machine) ∧ machine.slots effect = 2

theorem ExhaustsAt.prepend {stops : Nat → Bool} {program : List Op} {a b : Cfg} {effect : Nat} (hr : RunAt stops program a b)
    (h : ExhaustsAt stops program b effect) : ExhaustsAt stops program a effect := by
  obtain ⟨t, rest, m, h1, h2⟩ := h
  exact ⟨t, rest, m, hr.trans h1, h2⟩

theorem Exhausts.toAt {stops : Nat → Bool} {program : List Op} {cfg : Cfg} {effect : Nat} (h : Exhausts program cfg effect) :
    ExhaustsAt stops program cfg effect := by
  obtain ⟨t, rest, m, h1, h2⟩ := h
  exact ⟨t, rest, m, h1.toAt, h2⟩

/-- Where a run returns to the dispatcher, with `pc` and the machine it leaves: at a jump, or at a code site whose observer
stopped it, which then has 3 in the effect slot it names. -/
def EndsAt (stops : Nat → Bool) (program : List Op) (cfg : Cfg) (pc : Nat) (machine : Machine) : Prop :=
  (∃ rest target, RunAt stops program cfg (.jump target :: rest, machine) ∧ target.toNat = pc) ∨
  (∃ rest slot, RunAt stops program cfg (.jumpSlot slot :: rest, machine) ∧ (machine.slots slot).toNat = pc) ∨
  (∃ rest effect target before, RunAt stops program cfg (.code effect target :: rest, before) ∧ stops target.toNat = true ∧
    machine = before.write effect (3 : UInt64).toBitVec ∧ target.toNat = pc)

theorem EndsAt.prepend {stops : Nat → Bool} {program : List Op} {a b : Cfg} {pc : Nat} {machine : Machine}
    (hr : RunAt stops program a b) (h : EndsAt stops program b pc machine) : EndsAt stops program a pc machine := by
  rcases h with ⟨rest, t, h1, h2⟩ | ⟨rest, s, h1, h2⟩ | ⟨rest, e, t, b', h1, h2, h3, h4⟩
  · exact Or.inl ⟨rest, t, hr.trans h1, h2⟩
  · exact Or.inr (Or.inl ⟨rest, s, hr.trans h1, h2⟩)
  · exact Or.inr (Or.inr ⟨rest, e, t, b', hr.trans h1, h2, h3, h4⟩)

/-- A run that returned is at its end: no step follows, so that the run from a configuration is the one run. -/
theorem nextCfgAt_jump (stops : Nat → Bool) (program : List Op) (target : UInt64) (rest : List Op) (machine : Machine) :
    nextCfgAt stops program (.jump target :: rest, machine) = none := rfl

theorem nextCfgAt_jumpSlot (stops : Nat → Bool) (program : List Op) (slot : Nat) (rest : List Op) (machine : Machine) :
    nextCfgAt stops program (.jumpSlot slot :: rest, machine) = none := rfl

theorem nextCfgAt_stop {stops : Nat → Bool} (program : List Op) {effect : Nat} {target : UInt64} (rest : List Op) (machine : Machine)
    (h : stops target.toNat = true) : nextCfgAt stops program (.code effect target :: rest, machine) = none := by
  simp [nextCfgAt, h]

/-- Two runs from one configuration to configurations where nothing follows are the same run. -/
theorem RunAt.unique {stops : Nat → Bool} {program : List Op} {a b c : Cfg} (h1 : RunAt stops program a b)
    (h2 : RunAt stops program a c) (hb : nextCfgAt stops program b = none) (hc : nextCfgAt stops program c = none) : b = c := by
  induction h1 with
  | refl =>
    cases h2 with
    | refl => rfl
    | step hn _ => rw [hb] at hn; simp at hn
  | step hn _ ih =>
    cases h2 with
    | refl => rw [hc] at hn; simp at hn
    | step hn' hr =>
      rw [hn] at hn'
      simp only [Option.some.injEq] at hn'
      subst hn'
      exact ih hr hb

/-! What one instruction at a time does. -/

/-- Where the interpreter goes on after a block, which is what `runInterpreted` returns. -/
def nextPc (block : Block) : Bil.Effect → Nat
  | .jump target => target.toNat
  | _ => block.next

def blockAt (blocks : List Block) (pc : Nat) : Option Block :=
  blocks.find? fun block => block.address == pc

/-- One block in the interpreter. -/
def stepBlock (blocks : List Block) (fuel : Nat) (cfg : Bil.State × Nat) : Except String (Bil.State × Nat) :=
  match blockAt blocks cfg.2 with
  | none => .error "no block"
  | some block =>
    match Bil.execProgram fuel cfg.1 block.program with
    | .error error => .error error
    | .ok result => .ok (result.1, nextPc block result.2)

/-- `count` blocks in the interpreter, one at a time. -/
def stepBlocks (blocks : List Block) (fuel : Nat) : Nat → Bil.State × Nat → Except String (Bil.State × Nat)
  | 0, cfg => .ok cfg
  | count + 1, cfg =>
    match stepBlock blocks fuel cfg with
    | .error error => .error error
    | .ok next => stepBlocks blocks fuel count next

private theorem exec_single {fuel : Nat} {state : Bil.State} {stmt : Bil.Stmt} {result : Bil.State × Bil.Effect}
    (h : Bil.execProgram fuel state [stmt] = .ok result) : ∃ fuel', Bil.execStmt fuel' state stmt = .ok result := by
  obtain ⟨fuel', ⟨st, eff⟩, _, h1, h2⟩ := exec_cons h
  refine ⟨fuel', ?_⟩
  cases eff with
  | normal =>
    have := exec_nil h2
    rw [this]
    exact h1
  | jump t => simp only at h2; rw [h2]; exact h1
  | special t => simp only at h2; rw [h2]; exact h1
  | cpuExn t => simp only at h2; rw [h2]; exact h1

/-- A program with its last statement apart. -/
private theorem exec_snoc (xs : Bil.Program) (y : Bil.Stmt) {fuel : Nat} {state : Bil.State} {result : Bil.State × Bil.Effect}
    (h : Bil.execProgram fuel state (xs ++ [y]) = .ok result) :
    ∃ first : Bil.State × Bil.Effect, Bil.execProgram fuel state xs = .ok first ∧
      match first.2 with
      | .normal => ∃ fuel', Bil.execStmt fuel' first.1 y = .ok result
      | _ => result = first := by
  induction xs generalizing fuel state with
  | nil =>
    cases fuel with
    | zero => simp [Bil.execProgram] at h
    | succ fuel =>
      exact ⟨(state, .normal), by simp [Bil.execProgram], exec_single h⟩
  | cons x rest ih =>
    cases fuel with
    | zero => simp [Bil.execProgram] at h
    | succ fuel =>
      simp only [List.cons_append, Bil.execProgram] at h
      obtain ⟨⟨st, eff⟩, h1, h2⟩ := bind_ok h
      simp only at h2
      cases eff with
      | normal =>
        obtain ⟨first, h3, h4⟩ := ih h2
        refine ⟨first, ?_, h4⟩
        simp only [Bil.execProgram, h1]
        exact h3
      | jump t =>
        simp only [Except.ok.injEq] at h2
        subst h2
        exact ⟨_, by simp only [Bil.execProgram, h1]; rfl, rfl⟩
      | special t =>
        simp only [Except.ok.injEq] at h2
        subst h2
        exact ⟨_, by simp only [Bil.execProgram, h1]; rfl, rfl⟩
      | cpuExn t =>
        simp only [Except.ok.injEq] at h2
        subst h2
        exact ⟨_, by simp only [Bil.execProgram, h1]; rfl, rfl⟩

/-- A bound variable stays bound. -/
private theorem exec_stays_bound (var : Bap.Var) : ∀ fuel : Nat,
    (∀ (state : Bil.State) (stmt : Bil.Stmt) (result : Bil.State × Bil.Effect), Bil.execStmt fuel state stmt = .ok result →
      (∃ value, Bil.lookup state.env var = .ok value) → ∃ value, Bil.lookup result.1.env var = .ok value) ∧
    (∀ (state : Bil.State) (program : Bil.Program) (result : Bil.State × Bil.Effect), Bil.execProgram fuel state program = .ok result →
      (∃ value, Bil.lookup state.env var = .ok value) → ∃ value, Bil.lookup result.1.env var = .ok value) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun _ _ _ h => ?_, fun _ _ _ h => ?_⟩ <;> simp [Bil.execStmt, Bil.execProgram] at h
  | succ fuel ih =>
    obtain ⟨ihS, ihP⟩ := ih
    refine ⟨?_, ?_⟩
    · intro state stmt result h hb
      cases stmt with
      | move dst value =>
        obtain ⟨v, _, rfl⟩ := exec_move h
        by_cases hd : var = dst
        · subst hd
          exact ⟨_, lookup_bind_same _ _ _⟩
        · simpa only [lookup_bind_other hd] using hb
      | jmp target =>
        obtain ⟨_, _, _, rfl⟩ := exec_jmp h
        exact hb
      | special message =>
        simp only [Bil.execStmt, Except.ok.injEq] at h
        subst h
        exact hb
      | cpuExn number =>
        simp only [Bil.execStmt, Except.ok.injEq] at h
        subst h
        exact hb
      | ifElse condition yes no =>
        simp only [Bil.execStmt, Bil.execExp] at h
        obtain ⟨v, _, h⟩ := bind_ok h
        obtain ⟨⟨w, bits⟩, _, h⟩ := bind_ok h
        simp only at h
        split at h
        · exact ihP _ _ _ h hb
        · simp at h
      | «while» condition body =>
        simp only [Bil.execStmt, Bil.execExp] at h
        obtain ⟨v, _, h⟩ := bind_ok h
        obtain ⟨⟨w, bits⟩, _, h⟩ := bind_ok h
        simp only at h
        split at h
        · split at h
          · obtain ⟨⟨st, eff⟩, h1, h2⟩ := bind_ok h
            have hb1 := ihP _ _ _ h1 hb
            simp only at h2
            cases eff with
            | normal => exact ihS _ _ _ h2 hb1
            | jump t => simp only [Except.ok.injEq] at h2; subst h2; exact hb1
            | special t => simp only [Except.ok.injEq] at h2; subst h2; exact hb1
            | cpuExn t => simp only [Except.ok.injEq] at h2; subst h2; exact hb1
          · simp only [Except.ok.injEq] at h
            subst h
            exact hb
        · simp at h
    · intro state program result h hb
      cases program with
      | nil =>
        simp only [Bil.execProgram, Except.ok.injEq] at h
        subst h
        exact hb
      | cons stmt rest =>
        simp only [Bil.execProgram] at h
        obtain ⟨⟨st, eff⟩, h1, h2⟩ := bind_ok h
        have hb1 := ihS _ _ _ h1 hb
        simp only at h2
        cases eff with
        | normal => exact ihP _ _ _ h2 hb1
        | jump t => simp only [Except.ok.injEq] at h2; subst h2; exact hb1
        | special t => simp only [Except.ok.injEq] at h2; subst h2; exact hb1
        | cpuExn t => simp only [Except.ok.injEq] at h2; subst h2; exact hb1

/-- What a program moves to first has a value at every end of it. -/
theorem leadingMoves_bound {var : Bap.Var} (program : Bil.Program) (hm : var ∈ leadingMoves program) {fuel : Nat} {state : Bil.State}
    {result : Bil.State × Bil.Effect} (h : Bil.execProgram fuel state program = .ok result) :
    ∃ value, Bil.lookup result.1.env var = .ok value := by
  induction program generalizing fuel state with
  | nil => simp [leadingMoves] at hm
  | cons stmt rest ih =>
    cases stmt with
    | move dst value =>
      simp only [leadingMoves, List.mem_cons] at hm
      obtain ⟨fuel', ⟨st, eff⟩, _, h1, h2⟩ := exec_cons h
      obtain ⟨v, _, he⟩ := exec_move h1
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only at h2
      rcases hm with rfl | hm
      · exact (exec_stays_bound var fuel').2 _ _ _ h2 ⟨_, lookup_bind_same _ _ _⟩
      · exact ih hm h2
    | _ => simp [leadingMoves] at hm

theorem stepBlocks_stays_bound {blocks : List Block} {fuel : Nat} {var : Bap.Var} (count : Nat) {cfg result : Bil.State × Nat}
    (h : stepBlocks blocks fuel count cfg = .ok result) (hb : ∃ value, Bil.lookup cfg.1.env var = .ok value) :
    ∃ value, Bil.lookup result.1.env var = .ok value := by
  induction count generalizing cfg with
  | zero =>
    simp only [stepBlocks, Except.ok.injEq] at h
    subst h
    exact hb
  | succ count ih =>
    simp only [stepBlocks] at h
    split at h
    · simp at h
    · next next' hs =>
      refine ih h ?_
      simp only [stepBlock] at hs
      split at hs
      · simp at hs
      · split at hs
        · simp at hs
        · next result' he =>
          simp only [Except.ok.injEq] at hs
          subst hs
          exact (exec_stays_bound var fuel).2 _ _ _ he hb

/-- Where a jump goes. -/
def nextPcOf : Bil.Effect → Option Nat
  | .jump target => some target.toNat
  | _ => none

/-! How a block ends in a range. -/

/-- An edge of the graph to `target`, whose block has `label`. -/
def EdgeTo (plan : GraphPlan) (source target label : Nat) : Prop :=
  (source, target) ∈ GraphPlan.edges plan ∧
    ∃ address, (GraphPlan.labels plan).find? (fun (address, _) => address = target) = some (address, label)

/-- How a run of a block in a range ends, given what the interpreter says about the block. -/
def BlockOutcome (limit : Prop) (stops : Nat → Bool) (plan : GraphPlan) (low high : Nat) (global : Lowering) (program : List Op) (cfg : Cfg)
    (effect : Nat) (address : Nat) (block : Block) (result : Bil.State × Bil.Effect) : Prop :=
  (limit ∧ ExhaustsAt stops program cfg effect) ∨
    (∃ machine, EndsAt stops program cfg (nextPc block result.2) machine ∧ Agrees result.1.env machine global ∧
      FramesOut effect low high global cfg.2 machine ∧ (machine.slots effect = 0 ∨ machine.slots effect = 1)) ∨
    (∃ machine label rest, RunAt stops program cfg (.goto label :: rest, machine) ∧ EdgeTo plan address (nextPc block result.2) label ∧
      Agrees result.1.env machine global ∧ Frames low high global cfg.2 machine)

/-- What a part of a program needs of where it runs. -/
structure Place (first second global : Lowering) (new program tail : List Op) (effect : Nat) : Prop where
  effectFree : ∀ var, (var, effect) ∉ Lowering.layout global
  wfGlobal : LayoutWF global
  sub : Sub second global
  split : ∃ pre, program = pre ++ new ++ tail
  distinct : (labelsOf program).Nodup

private theorem one_toBitVec_ne : (1 : UInt64).toBitVec ≠ (0 : Word64) := by decide

/-- The operations of an edge either go to the label of its target or leave for it. -/
private theorem graphEdgeOps_sim {lowering : Lowering} {plan : GraphPlan} {source target effect : Nat} {ops : List Op}
    (heff : Lowering.effectSlot lowering = some effect)
    (h : graphEdgeOps lowering (GraphPlan.labels plan) (GraphPlan.edges plan) source target = some ops) :
    (∃ label, ops = [.goto label] ∧ EdgeTo plan source target label) ∨ ops = [.set effect 1, .jump (UInt64.ofNat target)] := by
  unfold graphEdgeOps at h
  split at h
  · next he =>
    split at h
    · next address label hf =>
      simp only [Option.some.injEq] at h
      exact Or.inl ⟨label, h.symm, by simpa using he, address, hf⟩
    · simp at h
  · simp only [Option.some.injEq] at h
    refine Or.inr ?_
    rw [← h]
    simp [jumpConstant, setEffect, heff]

/-- The jump to a closed target. -/
private theorem exec_closed {fuel : Nat} {state : Bil.State} {exp : Bil.Exp} {target : Nat} {result : Bil.State × Bil.Effect}
    (hc : closedTarget exp = some target) (h : Bil.execStmt fuel state (.jmp exp) = .ok result) :
    result.1 = state ∧ nextPcOf result.2 = some target := by
  obtain ⟨w, bits, hev, rfl⟩ := exec_jmp h
  obtain ⟨w', value, hev', _, hv⟩ := closedTarget_sound hc state.env
  rw [hev] at hev'
  simp only [Except.ok.injEq, Bap.Value.bits.injEq] at hev'
  obtain ⟨rfl, hb⟩ := hev'
  have hb := eq_of_heq hb
  subst hb
  exact ⟨rfl, by simp [nextPcOf, hv]⟩

theorem Returns.endsAt {stops : Nat → Bool} {program : List Op} {cfg : Cfg} {value : Word64} {machine : Machine}
    (h : Returns program cfg value machine) : EndsAt stops program cfg value.toNat machine := by
  obtain ⟨rest, ⟨t, h1, h2⟩ | ⟨s, h1, h2⟩⟩ := h
  · exact Or.inl ⟨rest, t, h1.toAt, by rw [h2]; rfl⟩
  · exact Or.inr (Or.inl ⟨rest, s, h1.toAt, by rw [h2]⟩)

private theorem Place.context {first second mid global : Lowering} {new newS more program tail : List Op} {effect : Nat}
    (place : Place first second global new program tail effect) (heff : Lowering.effectSlot first = some effect)
    (hlow : effect < Lowering.nextSlot first) (hsub : Sub mid global) (hnew : new = newS ++ more) :
    Context first mid global newS program (more ++ tail) effect := by
  obtain ⟨pre, hsplit⟩ := place.split
  exact {
    effectSlot := heff
    effectLow := hlow
    effectFree := place.effectFree
    wfGlobal := place.wfGlobal
    sub := hsub
    split := ⟨pre, by rw [hsplit, hnew]; simp [List.append_assoc]⟩
    distinct := place.distinct }

/-- The end of a block over an edge. -/
private theorem edge_finish {limit : Prop} {stops : Nat → Bool} {plan : GraphPlan} {lowering : Lowering} {low high : Nat} {global : Lowering}
    {program rest ops : List Op} {cfg : Cfg} {effect source target : Nat} {block : Block} {result : Bil.State × Bil.Effect} {m : Machine}
    (heff : Lowering.effectSlot lowering = some effect) (hfree : ∀ var, (var, effect) ∉ Lowering.layout global)
    (hgo : graphEdgeOps lowering (GraphPlan.labels plan) (GraphPlan.edges plan) source target = some ops) (hlt : target < 2 ^ 64)
    (hpc : nextPc block result.2 = target) (hrun : RunAt stops program cfg (ops ++ rest, m)) (hag : Agrees result.1.env m global)
    (hf : Frames low high global cfg.2 m) :
    BlockOutcome limit stops plan low high global program cfg effect source block result := by
  rcases graphEdgeOps_sim heff hgo with ⟨label, rfl, he⟩ | rfl
  · exact Or.inr (Or.inr ⟨m, label, rest, hrun, by rw [hpc]; exact he, hag, hf⟩)
  · refine Or.inr (Or.inl ⟨m.write effect (1 : UInt64).toBitVec, ?_, hag.write_free hfree _, ?_, Or.inr ?_⟩)
    · rw [hpc]
      refine Or.inl ⟨rest, UInt64.ofNat target, hrun.trans ((Run.linear (op := .set effect 1) rfl _ _).toAt), ?_⟩
      simp only [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt hlt
    · exact Frames.thenOut hf ⟨rfl, fun slot he _ _ => by simp [Machine.write_slots, he]⟩
    · simp only [Machine.write_slots, ↓reduceIte]
      rfl

/-- The end of a block that leaves with the effect it has. -/
private theorem fall_finish {limit : Prop} {stops : Nat → Bool} {plan : GraphPlan} {low high : Nat} {global : Lowering}
    {program rest : List Op} {cfg : Cfg} {effect source target : Nat} {block : Block} {result : Bil.State × Bil.Effect} {m : Machine}
    (hlt : target < 2 ^ 64) (hpc : nextPc block result.2 = target)
    (hrun : RunAt stops program cfg (.jump (UInt64.ofNat target) :: rest, m)) (hag : Agrees result.1.env m global)
    (hf : Frames low high global cfg.2 m) (hzero : m.slots effect = 0) :
    BlockOutcome limit stops plan low high global program cfg effect source block result := by
  refine Or.inr (Or.inl ⟨m, ?_, hag, ?_, Or.inl hzero⟩)
  · rw [hpc]
    refine Or.inl ⟨rest, UInt64.ofNat target, hrun, ?_⟩
    simp only [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt hlt
  · exact ⟨hf.1, fun slot _ hs hv => hf.2 slot hs hv⟩

/-- A jump out of the statements of a block. -/
private theorem inner_jump {limit : Prop} {stops : Nat → Bool} {plan : GraphPlan} {low high low' high' : Nat} {global : Lowering}
    {program : List Op} {cfg : Cfg} {effect source : Nat} {block : Block} {state : Bil.State} {width : Nat} {target : BitVec width}
    (hl : low ≤ low') (hh : high' ≤ high)
    (h : ∃ value machine, Returns program cfg value machine ∧ Holds value target ∧ machine.slots effect = 1 ∧
      Agrees state.env machine global ∧ FramesOut effect low' high' global cfg.2 machine) :
    BlockOutcome limit stops plan low high global program cfg effect source block (state, .jump target) := by
  obtain ⟨value, machine, hret, hheld, hone, hag, hf⟩ := h
  refine Or.inr (Or.inl ⟨machine, ?_, hag, hf.weaken hl hh, Or.inr hone⟩)
  have : value.toNat = target.toNat := hheld
  simp only [nextPc]
  rw [← this]
  exact hret.endsAt

private theorem closed_lt {target : Bil.Exp} {address : Nat} (h : closedTarget target = some address) : address < 2 ^ 64 := by
  obtain ⟨w, value, _, hw, hv⟩ := closedTarget_sound h []
  rw [← hv]
  exact Nat.lt_of_lt_of_le value.isLt (Nat.pow_le_pow_right (by decide) hw)

private theorem Pushed.ops_only {lowering : Lowering} (more : List Op) (mk : Lowering)
    (h1 : Lowering.ops mk = Lowering.ops lowering ++ more) (h2 : Lowering.layout mk = Lowering.layout lowering)
    (h3 : Lowering.nextSlot mk = Lowering.nextSlot lowering) (h4 : Lowering.memory mk = Lowering.memory lowering)
    (h5 : Lowering.effectSlot mk = Lowering.effectSlot lowering) (h6 : Lowering.nextLabel mk = Lowering.nextLabel lowering) :
    Pushed lowering mk more 0 0 := ⟨h1, h2, h3, h4, h5, h6⟩

private theorem nextPc_of_jump {block : Block} {eff : Bil.Effect} {target : Nat} (h : nextPcOf eff = some target) :
    nextPc block eff = target := by
  cases eff with
  | jump t => simpa [nextPcOf, nextPc] using h
  | normal => simp [nextPcOf] at h
  | special t => simp [nextPcOf] at h
  | cpuExn t => simp [nextPcOf] at h

/-- A block whose last statement jumps, with what comes before it lowered. -/
private theorem lowerExit_direct {plan : GraphPlan} {first second : Lowering} {block : Block} {target effect : Nat}
    (wf : LayoutWF first) (heff : Lowering.effectSlot first = some effect) (hlow : effect < Lowering.nextSlot first)
    (he : blockExit block = BlockExit.direct target)
    {lowered : Lowering} {ops : List Op}
    (h1 : lowerStatements first block.program.dropLast = some (lowered, false))
    (hgo : graphEdgeOps lowered (GraphPlan.labels plan) (GraphPlan.edges plan) block.address target = some ops)
    (p : Pushed lowered second ops 0 0) :
    ∃ new, Grows first second new ∧ ∀ (stops : Nat → Bool) (global : Lowering) (program tail : List Op), Place first second global new program tail effect →
      ∀ (fuel : Nat) (state : Bil.State) (result : Bil.State × Bil.Effect) (machine : Machine), Agrees state.env machine global →
      machine.slots effect = 0 → Bil.execProgram fuel state block.program = .ok result →
      BlockOutcome (loopLimit + 1 ≤ fuel) stops plan (Lowering.nextSlot first) (Lowering.nextSlot second) global program (new ++ tail, machine) effect block.address block result := by
  obtain ⟨newS, aS, okS⟩ := lowerStatements_correct wf heff hlow h1
  have gp := p.grows aS.wf
  refine ⟨newS ++ ops, aS.grows.trans gp, ?_⟩
  intro stops global program tail place fuel state result machine hag _ hex
  obtain ⟨exp, hprog, hc⟩ := blockExit_direct he
  rw [hprog] at hex
  obtain ⟨⟨s1, e1⟩, hfirst, hrest⟩ := exec_snoc _ _ hex
  have ctx := place.context heff hlow (place.sub.before' gp) rfl
  have hlts := gp.next
  have heffL : Lowering.effectSlot lowered = some effect := by rw [aS.effect]; exact heff
  rcases okS fuel state (s1, e1) global program (ops ++ tail) effect machine ctx hag hfirst with hx | hn
  · exact Or.inl ⟨hx.1, by rw [List.append_assoc]; exact hx.2.toAt⟩
  · cases e1 with
    | normal =>
      obtain ⟨_, m1, hrun, hag1, hf1⟩ := hn
      simp only at hrest
      obtain ⟨fuel', hj⟩ := hrest
      obtain ⟨hs, hpc⟩ := exec_closed hc hj
      obtain ⟨st, eff⟩ := result
      simp only at hs
      subst hs
      have hpc' : nextPc block eff = target := nextPc_of_jump hpc
      rw [List.append_assoc]
      exact edge_finish (rest := tail) heffL place.effectFree hgo (closed_lt hc) hpc' hrun.toAt hag1
        (hf1.weaken (Nat.le_refl _) hlts)
    | jump t =>
      simp only at hrest
      subst hrest
      rw [List.append_assoc]
      exact inner_jump (Nat.le_refl _) hlts hn
    | special t => exact absurd hn (by simp)
    | cpuExn t => exact absurd hn (by simp)

/-- A block whose last statement is a branch, with what comes before it lowered. -/
private theorem lowerExit_branch {plan : GraphPlan} {first second : Lowering} {block : Block} {condition : Bil.Exp} {yes no : Nat}
    {falls : Bool} {effect : Nat} (wf : LayoutWF first) (heff : Lowering.effectSlot first = some effect)
    (hlow : effect < Lowering.nextSlot first) (he : blockExit block = BlockExit.branch condition yes no falls) (hnextLt : block.next < 2 ^ 64)
    {lowered mid after yesLowering noLowering : Lowering} {operand : Operand} {yesOps noOps : List Op}
    (h1 : lowerStatements first block.program.dropLast = some (lowered, false))
    (h2 : lowerExp lowered condition = some (mid, operand))
    (hyes : graphEdgeOps yesLowering (GraphPlan.labels plan) (GraphPlan.edges plan) block.address yes = some yesOps)
    (hno : (noOps = [.jump (UInt64.ofNat no)] ∧ falls = true) ∨
      graphEdgeOps noLowering (GraphPlan.labels plan) (GraphPlan.edges plan) block.address no = some noOps)
    (hyesEff : Lowering.effectSlot yesLowering = some effect) (hnoEff : Lowering.effectSlot noLowering = some effect)
    (p : Pushed mid after ([.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1),
        .label (Lowering.nextLabel mid)] ++ yesOps ++ [.label (Lowering.nextLabel mid + 1)]) 2 0)
    (q : Pushed after second noOps 0 0) :
    ∃ new, Grows first second new ∧ ∀ (stops : Nat → Bool) (global : Lowering) (program tail : List Op), Place first second global new program tail effect →
      ∀ (fuel : Nat) (state : Bil.State) (result : Bil.State × Bil.Effect) (machine : Machine), Agrees state.env machine global →
      machine.slots effect = 0 → Bil.execProgram fuel state block.program = .ok result →
      BlockOutcome (loopLimit + 1 ≤ fuel) stops plan (Lowering.nextSlot first) (Lowering.nextSlot second) global program (new ++ tail, machine) effect block.address block result := by
  obtain ⟨newS, aS, okS⟩ := lowerStatements_correct wf heff hlow h1
  obtain ⟨newC, heC, _, _, _, hval⟩ := lowerExp_correct condition aS.wf h2
  have aC := heC.appended aS.wf
  have gp := p.grows aC.wf
  have gq := q.grows gp.wf
  let yl := Lowering.nextLabel mid
  let nl := Lowering.nextLabel mid + 1
  let tailOps : List Op := [.branch (Operand.slot operand) yl nl, .label yl] ++ yesOps ++ [.label nl] ++ noOps
  refine ⟨newS ++ (newC ++ tailOps), aS.grows.trans (aC.grows.trans (by
    have := gp.trans gq
    simpa [tailOps, yl, nl, List.append_assoc] using this)), ?_⟩
  intro stops global program tail place fuel state result machine hag hzero hex
  obtain ⟨yesExp, hcy, hshape⟩ := blockExit_branch he
  have subMid := (place.sub.before' gq).before' gp
  have subL := subMid.before' aC.grows
  have hnxC := aC.next
  have hnxP := gp.next
  have hnxQ := gq.next
  have ctx := place.context (newS := newS) (more := newC ++ tailOps) heff hlow subL rfl
  obtain ⟨pre, hsplit⟩ := place.split
  have hcont : ∀ (s1 : Bil.State) (m1 : Machine) (result' : Bil.State × Bil.Effect) (bit : BitVec 1),
      RunAt stops program ((newS ++ (newC ++ tailOps)) ++ tail, machine) ((newC ++ tailOps) ++ tail, m1) →
      Agrees s1.env m1 global → Frames (Lowering.nextSlot first) (Lowering.nextSlot lowered) global machine m1 → m1.slots effect = 0 →
      Bil.evalExp s1.env condition = .ok (.bits bit) → result'.1 = s1 →
      (bit = 1 → nextPc block result'.2 = yes) → (bit ≠ 1 → nextPc block result'.2 = no) →
      BlockOutcome (loopLimit + 1 ≤ fuel) stops plan (Lowering.nextSlot first) (Lowering.nextSlot second) global program
        ((newS ++ (newC ++ tailOps)) ++ tail, machine) effect block.address block result' := by
    intro s1 m1 result' bit hrun hag1 hf1 hz1 hev hst hy hn
    have hsm : SlotsAgree s1.env m1 (Lowering.layout mid) := hag1.slots.mono subMid.mono
    obtain ⟨_, hvalue⟩ := hval s1.env m1 hsm (hag1.memoryAgrees subMid) 1 bit hev
    have hag2 := hag1.after heC subMid
    have hf2 := heC.frames subMid m1
    have hfA : Frames (Lowering.nextSlot first) (Lowering.nextSlot second) global machine (runOps m1 newC) :=
      (hf1.weaken (Nat.le_refl _) (by omega)).trans (hf2.weaken aS.next (by omega))
    have hz2 : (runOps m1 newC).slots effect = 0 := by
      rw [heC.frame m1 (Or.inl (Nat.lt_of_lt_of_le hlow aS.next))]
      exact hz1
    have hrun2 : RunAt stops program ((newS ++ (newC ++ tailOps)) ++ tail, machine)
        (.branch (Operand.slot operand) yl nl :: .label yl :: (yesOps ++ [.label nl] ++ noOps ++ tail), runOps m1 newC) := by
      refine hrun.trans ?_
      have heq : (newC ++ tailOps) ++ tail = newC ++ (.branch (Operand.slot operand) yl nl :: .label yl :: (yesOps ++ [.label nl] ++ noOps ++ tail)) := by
        simp [tailOps, List.append_assoc]
      rw [heq]
      exact (Run.ops (fun op hop => linear_of_expression (heC.pure op hop)) _ m1).toAt
    have hagR : Agrees result'.1.env (runOps m1 newC) global := by rw [hst]; exact hag2
    by_cases hbit : bit = 1
    · have hne : (runOps m1 newC).slots (Operand.slot operand) ≠ 0 := (holds_condition hvalue).2 hbit
      have hprogY : program = (pre ++ newS ++ newC ++ [.branch (Operand.slot operand) yl nl]) ++ .label yl :: (yesOps ++ [.label nl] ++ noOps ++ tail) := by
        rw [hsplit]; simp [tailOps, List.append_assoc]
      have hstep : RunAt stops program (.branch (Operand.slot operand) yl nl :: .label yl :: (yesOps ++ [.label nl] ++ noOps ++ tail), runOps m1 newC)
          (yesOps ++ [.label nl] ++ noOps ++ tail, runOps m1 newC) :=
        (Run.branch (by rw [ite_eq_left hne]; exact afterLabel_split _ hprogY place.distinct)).toAt
      have hzz : yesOps ++ [.label nl] ++ noOps ++ tail = yesOps ++ ([.label nl] ++ noOps ++ tail) := by simp [List.append_assoc]
      have hrun3 := hrun2.trans hstep
      rw [hzz] at hrun3
      exact edge_finish (rest := [.label nl] ++ noOps ++ tail) hyesEff place.effectFree hyes (closed_lt hcy) (hy hbit) hrun3 hagR hfA
    · have hzc : (runOps m1 newC).slots (Operand.slot operand) = 0 := by
        by_cases hz : (runOps m1 newC).slots (Operand.slot operand) = 0
        · exact hz
        · exact absurd ((holds_condition hvalue).1 hz) hbit
      have hprogN : program = (pre ++ newS ++ newC ++ [.branch (Operand.slot operand) yl nl, .label yl] ++ yesOps) ++ .label nl :: (noOps ++ tail) := by
        rw [hsplit]; simp [tailOps, List.append_assoc]
      have hstep : RunAt stops program (.branch (Operand.slot operand) yl nl :: .label yl :: (yesOps ++ [.label nl] ++ noOps ++ tail), runOps m1 newC)
          (noOps ++ tail, runOps m1 newC) :=
        (Run.branch (by
          rw [ite_eq_right (by simpa using hzc)]
          exact afterLabel_split _ hprogN place.distinct)).toAt
      have hrun3 := hrun2.trans hstep
      have hnoLt : no < 2 ^ 64 := by
        rcases hshape with ⟨_, hn', _⟩ | ⟨_, nExp, hcn, _⟩
        · rw [hn']; exact hnextLt
        · exact closed_lt hcn
      rcases hno with ⟨rfl, _⟩ | hgo
      · exact fall_finish hnoLt (hn hbit) hrun3 hagR hfA hz2
      · exact edge_finish (rest := tail) hnoEff place.effectFree hgo hnoLt (hn hbit) hrun3 hagR hfA
  have hdecomp : ∃ noStmts : Bil.Program, block.program = block.program.dropLast ++ [.ifElse condition [.jmp yesExp] noStmts] ∧
      ((noStmts = [] ∧ no = block.next) ∨ ∃ noExp, noStmts = [.jmp noExp] ∧ closedTarget noExp = some no) := by
    rcases hshape with ⟨_, hn', hp⟩ | ⟨_, nExp, hcn, hp⟩
    · exact ⟨[], hp, Or.inl ⟨rfl, hn'⟩⟩
    · exact ⟨[.jmp nExp], hp, Or.inr ⟨nExp, rfl, hcn⟩⟩
  obtain ⟨noStmts, hprog, hnoShape⟩ := hdecomp
  rw [hprog] at hex
  obtain ⟨⟨s1, e1⟩, hfirst, hrest⟩ := exec_snoc _ _ hex
  rw [show (newS ++ (newC ++ tailOps)) ++ tail = newS ++ ((newC ++ tailOps) ++ tail) by simp [List.append_assoc]]
  rcases okS fuel state (s1, e1) global program ((newC ++ tailOps) ++ tail) effect machine ctx hag hfirst with hx | hn
  · exact Or.inl ⟨hx.1, hx.2.toAt⟩
  · cases e1 with
    | normal =>
      obtain ⟨_, m1, hrun, hag1, hf1⟩ := hn
      simp only at hrest
      obtain ⟨fuel', hstmt⟩ := hrest
      obtain ⟨fuel'', bit, _, hev, hbranch⟩ := exec_ifElse hstmt
      have hz1 : m1.slots effect = 0 := by
        rw [hf1.2 effect (Or.inl hlow) place.effectFree]
        exact hzero
      have key := hcont s1 m1 result bit
        (by rw [show (newS ++ (newC ++ tailOps)) ++ tail = newS ++ ((newC ++ tailOps) ++ tail) by simp [List.append_assoc]]; exact hrun.toAt)
        hag1 hf1 hz1 hev
      rw [show (newS ++ (newC ++ tailOps)) ++ tail = newS ++ ((newC ++ tailOps) ++ tail) by simp [List.append_assoc]] at key
      have hjmp : ∀ {exp : Bil.Exp} {t : Nat}, closedTarget exp = some t → ∀ {f : Nat}, Bil.execProgram f s1 [.jmp exp] = .ok result →
          result.1 = s1 ∧ nextPc block result.2 = t := by
        intro exp t hc f he'
        obtain ⟨f', hj⟩ := exec_single he'
        obtain ⟨h1', h2'⟩ := exec_closed hc hj
        exact ⟨h1', nextPc_of_jump h2'⟩
      by_cases hbit : bit = 1
      · rw [ite_eq_left hbit] at hbranch
        obtain ⟨hs, hpc⟩ := hjmp hcy hbranch
        exact key hs (fun _ => hpc) (fun hne => absurd hbit hne)
      · rw [ite_eq_right hbit] at hbranch
        rcases hnoShape with ⟨rfl, hnn⟩ | ⟨nExp, rfl, hcn⟩
        · have hres := exec_nil hbranch
          subst hres
          exact key rfl (fun hb => absurd hb hbit) (fun _ => hnn.symm)
        · obtain ⟨hs, hpc⟩ := hjmp hcn hbranch
          exact key hs (fun hb => absurd hb hbit) (fun _ => hpc)
    | jump t =>
      simp only at hrest
      subst hrest
      exact inner_jump (Nat.le_refl _) (by omega) hn
    | special t => exact absurd hn (by simp)
    | cpuExn t => exact absurd hn (by simp)

/-- A block that ends any other way, with its statements lowered. -/
private theorem lowerExit_other {plan : GraphPlan} {first second : Lowering} {block : Block} {effect : Nat}
    (wf : LayoutWF first) (heff : Lowering.effectSlot first = some effect) (hlow : effect < Lowering.nextSlot first)
    (hnextLt : block.next < 2 ^ 64) {lowered : Lowering} {terminated : Bool} {ops : List Op}
    (h1 : lowerStatements first block.program = some (lowered, terminated))
    (hops : (terminated = true ∧ ops = []) ∨ (ops = [.jump (UInt64.ofNat block.next)]) ∨
      graphEdgeOps lowered (GraphPlan.labels plan) (GraphPlan.edges plan) block.address block.next = some ops)
    (p : Pushed lowered second ops 0 0) :
    ∃ new, Grows first second new ∧ ∀ (stops : Nat → Bool) (global : Lowering) (program tail : List Op), Place first second global new program tail effect →
      ∀ (fuel : Nat) (state : Bil.State) (result : Bil.State × Bil.Effect) (machine : Machine), Agrees state.env machine global →
      machine.slots effect = 0 → Bil.execProgram fuel state block.program = .ok result →
      BlockOutcome (loopLimit + 1 ≤ fuel) stops plan (Lowering.nextSlot first) (Lowering.nextSlot second) global program (new ++ tail, machine) effect block.address block result := by
  obtain ⟨newS, aS, okS⟩ := lowerStatements_correct wf heff hlow h1
  have gp := p.grows aS.wf
  refine ⟨newS ++ ops, aS.grows.trans gp, ?_⟩
  intro stops global program tail place fuel state result machine hag hzero hex
  have ctx := place.context heff hlow (place.sub.before' gp) rfl
  have hlts := gp.next
  have heffL : Lowering.effectSlot lowered = some effect := by rw [aS.effect]; exact heff
  rw [List.append_assoc]
  obtain ⟨st, eff⟩ := result
  rcases okS fuel state (st, eff) global program (ops ++ tail) effect machine ctx hag hex with hx | hn
  · exact Or.inl ⟨hx.1, hx.2.toAt⟩
  · cases eff with
    | normal =>
      obtain ⟨ht, m1, hrun, hag1, hf1⟩ := hn
      have hz1 : m1.slots effect = 0 := by
        rw [hf1.2 effect (Or.inl hlow) place.effectFree]
        exact hzero
      rcases hops with ⟨hd, _⟩ | rfl | hgo
      · rw [ht] at hd
        cases hd
      · exact fall_finish hnextLt rfl hrun.toAt hag1 (hf1.weaken (Nat.le_refl _) hlts) hz1
      · exact edge_finish (rest := tail) heffL place.effectFree hgo hnextLt rfl hrun.toAt hag1 (hf1.weaken (Nat.le_refl _) hlts)
    | jump t => exact inner_jump (Nat.le_refl _) hlts hn
    | special t => exact absurd hn (by simp)
    | cpuExn t => exact absurd hn (by simp)

/-! The way into a block. -/

private def siteOps (effect observed : Nat) (label : Nat) (address : Nat) (guarded : Bool) : List Op :=
  if guarded then
    [.branch observed label (label + 1), .label label, .set effect 0, .code effect (UInt64.ofNat address),
      .goto (label + 1), .label (label + 1)]
  else [.set effect 0, .code effect (UInt64.ofNat address)]

private def entryOps (effect budget observed go address : Nat) (guarded : Bool) : List Op :=
  [.branch budget go (go + 1), .label (go + 1), .set effect 1, .jump (UInt64.ofNat address), .label go] ++
    siteOps effect observed (go + 2) address guarded ++ [.add budget budget (UInt64.ofNat (2 ^ 64 - 1))]

private theorem enterBlock_pushed {lowering : Lowering} {effect : Nat} (budget observed address : Nat) (guarded : Bool)
    (h : Lowering.effectSlot lowering = some effect) :
    Pushed lowering (enterBlock lowering budget observed address guarded)
      (entryOps effect budget observed (Lowering.nextLabel lowering) address guarded) (if guarded then 4 else 2) 0 := by
  cases guarded <;>
    (constructor <;> simp [enterBlock, freshLabel, jumpConstant, setEffect, h, codeSite, entryOps, siteOps, List.append_assoc])

private theorem RunAt.pass {stops : Nat → Bool} {program rest : List Op} {effect : Nat} {target : UInt64} {m : Machine}
    (h : ¬ stops target.toNat = true) : RunAt stops program (.code effect target :: rest, m) (rest, m) :=
  .step (by simp [nextCfgAt, h]) (.refl _)

/-- What running the way into a block does: with no budget left it leaves for the block, a code site may stop it, and
otherwise it counts the block and goes on, with the effect slot 0 and all other slots as they were. -/
theorem entry_sim {stops : Nat → Bool} {program pre more : List Op} {effect budget observed go address : Nat} {guarded : Bool}
    (hsplit : program = pre ++ entryOps effect budget observed go address guarded ++ more) (hd : (labelsOf program).Nodup)
    (hbe : budget ≠ effect) (m : Machine) (hz : m.slots effect = 0) :
    (m.slots budget = 0 ∧ ∃ rest, RunAt stops program (entryOps effect budget observed go address guarded ++ more, m)
        (.jump (UInt64.ofNat address) :: rest, m.write effect (1 : UInt64).toBitVec)) ∨
    (m.slots budget ≠ 0 ∧ stops (UInt64.ofNat address).toNat = true ∧ ∃ rest, RunAt stops program (entryOps effect budget observed go address guarded ++ more, m)
        (.code effect (UInt64.ofNat address) :: rest, m.write effect (0 : UInt64).toBitVec)) ∨
    (m.slots budget ≠ 0 ∧ RunAt stops program (entryOps effect budget observed go address guarded ++ more, m)
        (more, ((m.write effect (0 : UInt64).toBitVec).write budget (m.slots budget + (UInt64.ofNat (2 ^ 64 - 1)).toBitVec)))) := by
  by_cases hb : m.slots budget = 0
  · refine Or.inl ⟨hb, .label go :: (siteOps effect observed (go + 2) address guarded ++ [.add budget budget (UInt64.ofNat (2 ^ 64 - 1))] ++ more), ?_⟩
    have hp : program = (pre ++ [.branch budget go (go + 1)]) ++ .label (go + 1) ::
        (.set effect 1 :: .jump (UInt64.ofNat address) :: .label go ::
          (siteOps effect observed (go + 2) address guarded ++ [.add budget budget (UInt64.ofNat (2 ^ 64 - 1))] ++ more)) := by
      rw [hsplit]; simp [entryOps, List.append_assoc]
    have h1 : Run program (entryOps effect budget observed go address guarded ++ more, m) (.set effect 1 :: .jump (UInt64.ofNat address) :: .label go ::
          (siteOps effect observed (go + 2) address guarded ++ [.add budget budget (UInt64.ofNat (2 ^ 64 - 1))] ++ more), m) := by
      rw [show entryOps effect budget observed go address guarded ++ more = .branch budget go (go + 1) :: .label (go + 1) ::
          .set effect 1 :: .jump (UInt64.ofNat address) :: .label go ::
          (siteOps effect observed (go + 2) address guarded ++ [.add budget budget (UInt64.ofNat (2 ^ 64 - 1))] ++ more) by
        simp [entryOps, List.append_assoc]]
      refine Run.branch ?_
      rw [ite_eq_right (by simpa using hb)]
      exact afterLabel_split _ hp hd
    exact (h1.trans (Run.linear (op := .set effect 1) rfl _ _)).toAt
  · have hp : program = (pre ++ [.branch budget go (go + 1), .label (go + 1), .set effect 1, .jump (UInt64.ofNat address)]) ++ .label go ::
        (siteOps effect observed (go + 2) address guarded ++ [.add budget budget (UInt64.ofNat (2 ^ 64 - 1))] ++ more) := by
      rw [hsplit]; simp [entryOps, List.append_assoc]
    have h1 : Run program (entryOps effect budget observed go address guarded ++ more, m)
        (siteOps effect observed (go + 2) address guarded ++ [.add budget budget (UInt64.ofNat (2 ^ 64 - 1))] ++ more, m) := by
      rw [show entryOps effect budget observed go address guarded ++ more = .branch budget go (go + 1) :: .label (go + 1) ::
          .set effect 1 :: .jump (UInt64.ofNat address) :: .label go ::
          (siteOps effect observed (go + 2) address guarded ++ [.add budget budget (UInt64.ofNat (2 ^ 64 - 1))] ++ more) by
        simp [entryOps, List.append_assoc]]
      refine Run.branch ?_
      rw [ite_eq_left hb]
      exact afterLabel_split _ hp hd
    have hadd : ∀ (n : Machine), n.slots budget = m.slots budget → Run program (.add budget budget (UInt64.ofNat (2 ^ 64 - 1)) :: more, n)
        (more, n.write budget (m.slots budget + (UInt64.ofNat (2 ^ 64 - 1)).toBitVec)) := by
      intro n hn
      have := Run.linear (program := program) (op := .add budget budget (UInt64.ofNat (2 ^ 64 - 1))) rfl more n
      simpa [Bap.Proofs.Primus.step, hn] using this
    by_cases hg : guarded = true
    · subst hg
      have hsplitS : siteOps effect observed (go + 2) address true ++ [.add budget budget (UInt64.ofNat (2 ^ 64 - 1))] ++ more =
          .branch observed (go + 2) (go + 3) :: .label (go + 2) :: .set effect 0 :: .code effect (UInt64.ofNat address) ::
            .goto (go + 3) :: .label (go + 3) :: .add budget budget (UInt64.ofNat (2 ^ 64 - 1)) :: more := by
        simp [siteOps]
      have hpSite : program = (pre ++ [.branch budget go (go + 1), .label (go + 1), .set effect 1, .jump (UInt64.ofNat address), .label go,
          .branch observed (go + 2) (go + 3)]) ++ .label (go + 2) :: (.set effect 0 :: .code effect (UInt64.ofNat address) ::
            .goto (go + 3) :: .label (go + 3) :: .add budget budget (UInt64.ofNat (2 ^ 64 - 1)) :: more) := by
        rw [hsplit]; simp [entryOps, siteOps, List.append_assoc]
      have hpDone : program = (pre ++ [.branch budget go (go + 1), .label (go + 1), .set effect 1, .jump (UInt64.ofNat address), .label go,
          .branch observed (go + 2) (go + 3), .label (go + 2), .set effect 0, .code effect (UInt64.ofNat address), .goto (go + 3)]) ++
            .label (go + 3) :: (.add budget budget (UInt64.ofNat (2 ^ 64 - 1)) :: more) := by
        rw [hsplit]; simp [entryOps, siteOps, List.append_assoc]
      rw [hsplitS] at h1
      by_cases ho : m.slots observed = 0
      · -- nothing observes the site, which leaves the effect, and that is 0 already
        refine Or.inr (Or.inr ⟨hb, ?_⟩)
        have h2 : Run program (.branch observed (go + 2) (go + 3) :: .label (go + 2) :: .set effect 0 :: .code effect (UInt64.ofNat address) ::
            .goto (go + 3) :: .label (go + 3) :: .add budget budget (UInt64.ofNat (2 ^ 64 - 1)) :: more, m)
            (.add budget budget (UInt64.ofNat (2 ^ 64 - 1)) :: more, m) :=
          Run.branch (by
            rw [ite_eq_right (by simpa using ho)]
            exact afterLabel_split _ hpDone hd)
        have hsame : (m.write effect (0 : UInt64).toBitVec) = m := by
          have hfun : (fun other => if other = effect then (0 : UInt64).toBitVec else m.slots other) = m.slots := by
            funext other
            by_cases ho' : other = effect
            · rw [ite_eq_left ho', ho', hz]
              rfl
            · rw [ite_eq_right ho']
          simp only [Machine.write, hfun]
        rw [hsame]
        exact ((h1.trans h2).trans (hadd m rfl)).toAt
      · have h2 : Run program (.branch observed (go + 2) (go + 3) :: .label (go + 2) :: .set effect 0 :: .code effect (UInt64.ofNat address) ::
            .goto (go + 3) :: .label (go + 3) :: .add budget budget (UInt64.ofNat (2 ^ 64 - 1)) :: more, m)
            (.code effect (UInt64.ofNat address) :: .goto (go + 3) :: .label (go + 3) :: .add budget budget (UInt64.ofNat (2 ^ 64 - 1)) :: more,
              m.write effect (0 : UInt64).toBitVec) :=
          (Run.branch (by
            rw [ite_eq_left ho]
            exact afterLabel_split _ hpSite hd)).trans (Run.linear (op := .set effect 0) rfl _ _)
        have hrun := (h1.trans h2).toAt (stops := stops)
        by_cases hs : stops (UInt64.ofNat address).toNat = true
        · exact Or.inr (Or.inl ⟨hb, hs, _, hrun⟩)
        · refine Or.inr (Or.inr ⟨hb, (hrun.trans (RunAt.pass hs)).trans ?_⟩)
          refine (Run.goto (afterLabel_split _ hpDone hd) _).toAt.trans ?_
          exact (hadd (m.write effect (0 : UInt64).toBitVec) (by simp [Machine.write_slots, hbe])).toAt
    · have hgf : guarded = false := by simpa using hg
      subst hgf
      have hsplitS : siteOps effect observed (go + 2) address false ++ [.add budget budget (UInt64.ofNat (2 ^ 64 - 1))] ++ more =
          .set effect 0 :: .code effect (UInt64.ofNat address) :: .add budget budget (UInt64.ofNat (2 ^ 64 - 1)) :: more := by
        simp [siteOps]
      rw [hsplitS] at h1
      have hrun := (h1.trans (Run.linear (op := .set effect 0) rfl _ _)).toAt (stops := stops)
      by_cases hs : stops (UInt64.ofNat address).toNat = true
      · exact Or.inr (Or.inl ⟨hb, hs, _, hrun⟩)
      · refine Or.inr (Or.inr ⟨hb, (hrun.trans (RunAt.pass hs)).trans ?_⟩)
        exact (hadd (m.write effect (0 : UInt64).toBitVec) (by simp [Machine.write_slots, hbe])).toAt

/-- What a lowered block does, from where its statements start. -/
def BlockOK (stops : Nat → Bool) (plan : GraphPlan) (low high : Nat) (global : Lowering) (program start : List Op) (effect : Nat) (block : Block) : Prop :=
  ∀ (fuel : Nat) (state : Bil.State) (result : Bil.State × Bil.Effect) (machine : Machine), Agrees state.env machine global →
    machine.slots effect = 0 → Bil.execProgram fuel state block.program = .ok result →
    BlockOutcome (loopLimit + 1 ≤ fuel) stops plan low high global program (start, machine) effect block.address block result

/-- What lowering the end of a block makes. -/
theorem lowerExit_spec {plan : GraphPlan} {first second : Lowering} {block : Block} {effect : Nat}
    (wf : LayoutWF first) (heff : Lowering.effectSlot first = some effect) (hlow : effect < Lowering.nextSlot first)
    (hnextLt : block.next < 2 ^ 64) (h : lowerExit plan first block = some second) :
    ∃ new, Grows first second new ∧ ∀ (stops : Nat → Bool) (global : Lowering) (program tail : List Op), Place first second global new program tail effect →
      BlockOK stops plan (Lowering.nextSlot first) (Lowering.nextSlot second) global program (new ++ tail) effect block := by
  unfold lowerExit at h
  split at h
  · next target he =>
    obtain ⟨⟨lowered, terminated⟩, h1, h⟩ := obind h
    cases terminated with
    | true => simp at h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨ops, hgo, h⟩ := obind h
      simp only [Option.some.injEq] at h
      subst h
      exact lowerExit_direct wf heff hlow he h1 hgo ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · next condition yes no falls he =>
    obtain ⟨⟨lowered, terminated⟩, h1, h⟩ := obind h
    cases terminated with
    | true => simp at h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨mid, operand⟩, h2, h⟩ := obind h
      simp only at h
      by_cases hw : (Operand.width operand != 1) = true
      · simp [hw] at h
      · simp only [hw, Bool.false_eq_true, ↓reduceIte, freshLabel] at h
        obtain ⟨yesOps, hyes, h⟩ := obind h
        obtain ⟨new0, a1, _⟩ := lowerStatements_correct wf heff hlow h1
        obtain ⟨_, heC, _⟩ := lowerExp_correct condition a1.wf h2
        have hmidEff : Lowering.effectSlot mid = some effect := by rw [heC.effect, a1.effect]; exact heff
        have p : Pushed mid (Lowering.push (freshLabel (freshLabel mid).1).1 ([.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1),
              .label (Lowering.nextLabel mid)] ++ yesOps ++ [.label (Lowering.nextLabel mid + 1)]))
            ([.branch (Operand.slot operand) (Lowering.nextLabel mid) (Lowering.nextLabel mid + 1),
              .label (Lowering.nextLabel mid)] ++ yesOps ++ [.label (Lowering.nextLabel mid + 1)]) 2 0 :=
          ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        split at h
        · next hc =>
          obtain ⟨noOps, hno, h⟩ := obind h
          simp only [Option.some.injEq] at h hno
          subst hno
          simp only [Bool.and_eq_true] at hc
          subst h
          exact lowerExit_branch wf heff hlow he hnextLt h1 h2 hyes (noLowering := mid) (Or.inl ⟨rfl, hc.1⟩) hmidEff hmidEff
            p ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        · obtain ⟨noOps, hno, h⟩ := obind h
          simp only [Option.some.injEq] at h
          subst h
          exact lowerExit_branch wf heff hlow he hnextLt h1 h2 hyes (Or.inr hno) hmidEff hmidEff
            p ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨⟨lowered, terminated⟩, h1, h⟩ := obind h
    simp only at h
    split at h
    · next ht =>
      simp only [Option.some.injEq] at h
      subst h
      exact lowerExit_other (plan := plan) (ops := []) wf heff hlow hnextLt h1 (Or.inl ⟨ht, rfl⟩)
        ⟨by simp, rfl, rfl, rfl, rfl, rfl⟩
    · split at h
      · obtain ⟨ops, hgo, h⟩ := obind h
        simp only [Option.some.injEq] at h
        subst h
        exact lowerExit_other wf heff hlow hnextLt h1 (Or.inr (Or.inr hgo)) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [Option.some.injEq] at h
        subst h
        exact lowerExit_other (plan := plan) wf heff hlow hnextLt h1 (Or.inr (Or.inl rfl)) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What the way into a lowered block does, in a program. -/
def EntryOK (stops : Nat → Bool) (program start body : List Op) (effect budget address : Nat) : Prop :=
  ∀ m : Machine, m.slots effect = 0 →
    (m.slots budget = 0 ∧ ∃ rest, RunAt stops program (start, m)
        (.jump (UInt64.ofNat address) :: rest, m.write effect (1 : UInt64).toBitVec)) ∨
    (m.slots budget ≠ 0 ∧ stops (UInt64.ofNat address).toNat = true ∧ ∃ rest, RunAt stops program (start, m)
        (.code effect (UInt64.ofNat address) :: rest, m.write effect (0 : UInt64).toBitVec)) ∨
    (m.slots budget ≠ 0 ∧ RunAt stops program (start, m)
        (body, ((m.write effect (0 : UInt64).toBitVec).write budget (m.slots budget + (UInt64.ofNat (2 ^ 64 - 1)).toBitVec))))

/-- A block in a program: where its statements start, and how they are reached over edges. -/
def SegOK (stops : Nat → Bool) (plan : GraphPlan) (low high : Nat) (global : Lowering) (program : List Op) (effect : Nat) (block : Block)
    (start : List Op) : Prop :=
  BlockOK stops plan low high global program start effect block ∧
    ((GraphPlan.edges plan).any (fun edge => edge.2 == block.address) = true → ∀ label address,
      (GraphPlan.labels plan).find? (fun (address, _) => address = block.address) = some (address, label) →
      ∃ entry, afterLabel program label = some entry ∧ EntryOK stops program entry start effect (GraphPlan.budget plan) block.address)

theorem BlockOK.weaken {stops : Nat → Bool} {plan : GraphPlan} {low high low' high' : Nat} {global : Lowering} {program start : List Op}
    {effect : Nat} {block : Block} (h : BlockOK stops plan low high global program start effect block) (hl : low' ≤ low) (hh : high ≤ high') :
    BlockOK stops plan low' high' global program start effect block := by
  intro fuel state result machine hag hz hex
  rcases h fuel state result machine hag hz hex with hx | ⟨m, h1, h2, h3, h4⟩ | ⟨m, l, r, h1, h2, h3, h4⟩
  · exact Or.inl hx
  · exact Or.inr (Or.inl ⟨m, h1, h2, h3.weaken hl hh, h4⟩)
  · exact Or.inr (Or.inr ⟨m, l, r, h1, h2, h3, h4.weaken hl hh⟩)

theorem SegOK.weaken {stops : Nat → Bool} {plan : GraphPlan} {low high low' high' : Nat} {global : Lowering} {program start : List Op}
    {effect : Nat} {block : Block} (h : SegOK stops plan low high global program effect block start) (hl : low' ≤ low) (hh : high ≤ high') :
    SegOK stops plan low' high' global program effect block start :=
  ⟨h.1.weaken hl hh, h.2⟩

private theorem lowerEntry_cases {plan : GraphPlan} {lowering second : Lowering} {block : Block} {hasEdge : Bool} {effect : Nat}
    (heff : Lowering.effectSlot lowering = some effect) (h : lowerEntry plan lowering block hasEdge = some second) :
    (hasEdge = false ∧ second = lowering) ∨
    (hasEdge = true ∧ ∃ address label, (GraphPlan.labels plan).find? (fun (address, _) => address = block.address) = some (address, label) ∧
      Pushed lowering second (.label label :: entryOps effect (GraphPlan.budget plan) (GraphPlan.observed plan) (Lowering.nextLabel lowering) block.address (GraphPlan.guarded plan block))
        (if GraphPlan.guarded plan block then 4 else 2) 0) := by
  unfold lowerEntry at h
  cases hasEdge with
  | false =>
    simp only [Bool.not_false, ↓reduceIte] at h
    split at h
    · exact Or.inl ⟨rfl, by simpa using h.symm⟩
    · simp at h
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · next address label hf =>
      simp only [Option.some.injEq] at h
      subst h
      refine Or.inr ⟨rfl, address, label, hf, ?_⟩
      have p := enterBlock_pushed (lowering := Lowering.push lowering [.label label]) (effect := effect)
        (GraphPlan.budget plan) (GraphPlan.observed plan) block.address (GraphPlan.guarded plan block) heff
      exact ⟨by rw [p.ops]; simp [Lowering.push], p.layout, p.next, p.memory, p.effect, p.label⟩
    · simp at h

private theorem find_same {plan : GraphPlan} {address : Nat} {a b l l' : Nat}
    (h1 : (GraphPlan.labels plan).find? (fun (address', _) => address' = address) = some (a, l))
    (h2 : (GraphPlan.labels plan).find? (fun (address', _) => address' = address) = some (b, l')) : l = l' := by
  rw [h1] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact h2.2

/-- What lowering a block makes. -/
theorem lowerBlock_spec {plan : GraphPlan} {first second : Lowering} {block : Block} {effect : Nat}
    (wf : LayoutWF first) (heff : Lowering.effectSlot first = some effect) (hlow : effect < Lowering.nextSlot first)
    (hnextLt : block.next < 2 ^ 64) (hbudget : GraphPlan.edges plan ≠ [] → GraphPlan.budget plan ≠ effect)
    (h : lowerBlock plan first block = some second) :
    ∃ new, Grows first second new ∧ ∀ (stops : Nat → Bool) (global : Lowering) (program tail : List Op),
      Place first second global new program tail effect →
      ∃ start, SegOK stops plan (Lowering.nextSlot first) (Lowering.nextSlot second) global program effect block start ∧
        (block.address = GraphPlan.seed plan → ∀ m, RunAt stops program (new ++ tail, m) (start, m)) := by
  unfold lowerBlock at h
  -- the variables a block has written do not matter to what it does
  generalize hl0 : (if GraphPlan.chained plan = true then Lowering.withWritten first (GraphPlan.definite plan block.address) else first) = l0 at h
  have g0 : Grows first l0 [] := by
    rw [← hl0]
    split
    · exact (show Pushed first (Lowering.withWritten first (GraphPlan.definite plan block.address)) [] 0 0 from
        ⟨by simp [Lowering.withWritten], rfl, rfl, rfl, rfl, rfl⟩).grows wf
    · exact (show Pushed first first [] 0 0 from ⟨by simp, rfl, rfl, rfl, rfl, rfl⟩).grows wf
  have heff0 : Lowering.effectSlot l0 = some effect := by rw [g0.effect]; exact heff
  have hbudgetE : (GraphPlan.edges plan).any (fun edge => edge.2 == block.address) = true → GraphPlan.budget plan ≠ effect := by
    intro hany
    apply hbudget
    intro hnil
    rw [hnil] at hany
    simp at hany
  dsimp only at h
  split at h
  · next hboth =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hboth
    obtain ⟨hseed, hany⟩ := hboth
    simp only [freshLabel] at h
    obtain ⟨l2, h2, h⟩ := obind h
    rw [hany] at h2
    let body := Lowering.nextLabel l0
    have p1 : Pushed l0 (Lowering.push (freshLabel l0).1 [.goto body]) [.goto body] 1 0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    have g1 := p1.grows g0.wf
    have heff1 : Lowering.effectSlot (Lowering.push (freshLabel l0).1 [.goto body]) = some effect := heff0
    rcases lowerEntry_cases heff1 h2 with ⟨hf, _⟩ | ⟨_, address, label, hfind, p2⟩
    · simp at hf
    · have g2 := p2.grows g1.wf
      have p3 : Pushed l2 (Lowering.push l2 [.goto body, .label body]) [.goto body, .label body] 0 0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      have g3 := p3.grows g2.wf
      have gAll := ((g0.trans g1).trans g2).trans g3
      have heff3 : Lowering.effectSlot (Lowering.push l2 [.goto body, .label body]) = some effect := by rw [gAll.effect]; exact heff
      have hlow3 : effect < Lowering.nextSlot (Lowering.push l2 [.goto body, .label body]) := Nat.lt_of_lt_of_le hlow gAll.next
      obtain ⟨newE, gE, okE⟩ := lowerExit_spec gAll.wf heff3 hlow3 hnextLt h
      refine ⟨_, gAll.trans gE, ?_⟩
      intro stops global program tail place
      obtain ⟨pre, hsplit⟩ := place.split
      have hbud := hbudgetE hany
      let entry := entryOps effect (GraphPlan.budget plan) (GraphPlan.observed plan) (Lowering.nextLabel (Lowering.push (freshLabel l0).1 [.goto body])) block.address (GraphPlan.guarded plan block)
      let start := newE ++ tail
      have placeE : Place (Lowering.push l2 [.goto body, .label body]) second global newE program tail effect := {
        effectFree := place.effectFree
        wfGlobal := place.wfGlobal
        sub := place.sub
        split := ⟨pre ++ [.goto body] ++ .label label :: entry ++ [.goto body, .label body], by rw [hsplit]; simp [entry, List.append_assoc]⟩
        distinct := place.distinct }
      have hbodyLabel : afterLabel program body = some start := by
        refine afterLabel_split (pre ++ [.goto body] ++ .label label :: entry ++ [.goto body]) ?_ place.distinct
        rw [hsplit]; simp [entry, start, List.append_assoc]
      refine ⟨start, ⟨(okE stops global program tail placeE).weaken ?_ (Nat.le_refl _), ?_⟩, ?_⟩
      · exact gAll.next
      · intro _ label' address' hfind'
        have hl := find_same hfind hfind'
        subst hl
        refine ⟨entry ++ ([.goto body, .label body] ++ start), ?_, ?_⟩
        · refine afterLabel_split (pre ++ [.goto body]) ?_ place.distinct
          rw [hsplit]; simp [entry, start, List.append_assoc]
        · intro m hz
          have hsim := entry_sim (stops := stops) (program := program) (pre := pre ++ [.goto body, .label label])
            (observed := GraphPlan.observed plan) (go := Lowering.nextLabel (Lowering.push (freshLabel l0).1 [.goto body]))
            (address := block.address) (guarded := GraphPlan.guarded plan block)
            (more := [.goto body, .label body] ++ start) (by rw [hsplit]; simp [start, List.append_assoc]) place.distinct hbud m hz
          rcases hsim with hs | hs | ⟨hb, hs⟩
          · exact Or.inl hs
          · exact Or.inr (Or.inl hs)
          · refine Or.inr (Or.inr ⟨hb, hs.trans ?_⟩)
            exact (Run.goto hbodyLabel _).toAt
      · intro _ m
        have : (([] ++ [.goto body]) ++ (.label label :: entry) ++ [.goto body, .label body] ++ newE) ++ tail =
            .goto body :: (.label label :: entry ++ [.goto body, .label body] ++ start) := by
          simp [start, List.append_assoc]
        rw [this]
        exact (Run.goto hbodyLabel _).toAt
  · next hnot =>
    obtain ⟨l1, h1, hx⟩ := obind h
    rcases lowerEntry_cases heff0 h1 with ⟨hf, rfl⟩ | ⟨hany, address, label, hfind, p1⟩
    · have heff1 := heff0
      have hlow1 : effect < Lowering.nextSlot l1 := Nat.lt_of_lt_of_le hlow g0.next
      obtain ⟨newE, gE, okE⟩ := lowerExit_spec g0.wf heff0 hlow1 hnextLt hx
      refine ⟨_, g0.trans gE, ?_⟩
      intro stops global program tail place
      obtain ⟨pre, hsplit⟩ := place.split
      have placeE : Place l1 second global newE program tail effect := {
        effectFree := place.effectFree
        wfGlobal := place.wfGlobal
        sub := place.sub
        split := ⟨pre, by rw [hsplit]; simp⟩
        distinct := place.distinct }
      refine ⟨newE ++ tail, ⟨(okE stops global program tail placeE).weaken g0.next (Nat.le_refl _), ?_⟩, ?_⟩
      · intro hany'
        rw [hf] at hany'
        simp at hany'
      · intro _ m
        exact .refl _
    · have g1 := p1.grows g0.wf
      have gAll := g0.trans g1
      have heff1 : Lowering.effectSlot l1 = some effect := by rw [gAll.effect]; exact heff
      have hlow1 : effect < Lowering.nextSlot l1 := Nat.lt_of_lt_of_le hlow gAll.next
      obtain ⟨newE, gE, okE⟩ := lowerExit_spec gAll.wf heff1 hlow1 hnextLt hx
      refine ⟨_, gAll.trans gE, ?_⟩
      intro stops global program tail place
      obtain ⟨pre, hsplit⟩ := place.split
      have hbud := hbudgetE hany
      let entry := entryOps effect (GraphPlan.budget plan) (GraphPlan.observed plan) (Lowering.nextLabel l0) block.address (GraphPlan.guarded plan block)
      let start := newE ++ tail
      have placeE : Place l1 second global newE program tail effect := {
        effectFree := place.effectFree
        wfGlobal := place.wfGlobal
        sub := place.sub
        split := ⟨pre ++ .label label :: entry, by rw [hsplit]; simp [entry, List.append_assoc]⟩
        distinct := place.distinct }
      refine ⟨start, ⟨(okE stops global program tail placeE).weaken gAll.next (Nat.le_refl _), ?_⟩, ?_⟩
      · intro _ label' address' hfind'
        have hl := find_same hfind hfind'
        subst hl
        refine ⟨entry ++ start, ?_, ?_⟩
        · refine afterLabel_split pre ?_ place.distinct
          rw [hsplit]; simp [entry, start, List.append_assoc]
        · intro m hz
          exact entry_sim (stops := stops) (program := program) (pre := pre ++ [.label label]) (more := start)
            (observed := GraphPlan.observed plan) (go := Lowering.nextLabel l0)
            (address := block.address) (guarded := GraphPlan.guarded plan block)
            (by rw [hsplit]; simp [start, List.append_assoc]) place.distinct hbud m hz
      · intro hseed
        exfalso
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hnot
        exact hnot hseed hany

/-- What lowering blocks makes. -/
theorem lowerBlocks_spec {plan : GraphPlan} {effect : Nat} (blocks : List Block) {first second : Lowering}
    (wf : LayoutWF first) (heff : Lowering.effectSlot first = some effect) (hlow : effect < Lowering.nextSlot first)
    (hnext : ∀ block ∈ blocks, block.next < 2 ^ 64) (hbudget : GraphPlan.edges plan ≠ [] → GraphPlan.budget plan ≠ effect)
    (h : lowerBlocks plan first blocks = some second) :
    ∃ new, Grows first second new ∧ ∀ (stops : Nat → Bool) (global : Lowering) (program tail : List Op),
      Place first second global new program tail effect →
      (∀ block ∈ blocks, ∃ start, SegOK stops plan (Lowering.nextSlot first) (Lowering.nextSlot second) global program effect block start) ∧
      ∀ block rest, blocks = block :: rest → block.address = GraphPlan.seed plan →
        ∃ start, SegOK stops plan (Lowering.nextSlot first) (Lowering.nextSlot second) global program effect block start ∧
          ∀ m, RunAt stops program (new ++ tail, m) (start, m) := by
  induction blocks generalizing first with
  | nil =>
    simp only [lowerBlocks, Option.some.injEq] at h
    subst h
    refine ⟨[], (show Pushed first first [] 0 0 from ⟨by simp, rfl, rfl, rfl, rfl, rfl⟩).grows wf, ?_⟩
    intro stops global program tail _
    exact ⟨by simp, by simp⟩
  | cons block rest ih =>
    simp only [lowerBlocks] at h
    obtain ⟨mid, h1, h2⟩ := obind h
    obtain ⟨newB, g1, ok1⟩ := lowerBlock_spec wf heff hlow (hnext block List.mem_cons_self) hbudget h1
    obtain ⟨newR, g2, ok2⟩ := ih g1.wf (by rw [g1.effect]; exact heff) (Nat.lt_of_lt_of_le hlow g1.next)
      (fun b hb => hnext b (List.mem_cons_of_mem _ hb)) h2
    refine ⟨newB ++ newR, g1.trans g2, ?_⟩
    intro stops global program tail place
    obtain ⟨pre, hsplit⟩ := place.split
    have place1 : Place first mid global newB program (newR ++ tail) effect := {
      effectFree := place.effectFree
      wfGlobal := place.wfGlobal
      sub := place.sub.before' g2
      split := ⟨pre, by rw [hsplit]; simp [List.append_assoc]⟩
      distinct := place.distinct }
    have place2 : Place mid second global newR program tail effect := {
      effectFree := place.effectFree
      wfGlobal := place.wfGlobal
      sub := place.sub
      split := ⟨pre ++ newB, by rw [hsplit]; simp [List.append_assoc]⟩
      distinct := place.distinct }
    obtain ⟨start, seg, hrun⟩ := ok1 stops global program (newR ++ tail) place1
    obtain ⟨all2, _⟩ := ok2 stops global program tail place2
    have seg' := seg.weaken (low' := Lowering.nextSlot first) (high' := Lowering.nextSlot second) (Nat.le_refl _) g2.next
    refine ⟨?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨start, seg'⟩
      · obtain ⟨s, hs⟩ := all2 b hb
        exact ⟨s, hs.weaken g1.next (Nat.le_refl _)⟩
    · intro b r hbs hseed
      simp only [List.cons.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      refine ⟨start, seg', fun m => ?_⟩
      rw [List.append_assoc]
      exact hrun hseed m

private theorem decrement_toNat {slot : Word64} (h : slot ≠ 0) :
    (slot + (UInt64.ofNat (2 ^ 64 - 1)).toBitVec).toNat = slot.toNat - 1 := by
  have hpos : 0 < slot.toNat := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply h
    apply BitVec.eq_of_toNat_eq
    simpa using hz
  have hlt := slot.isLt
  rw [BitVec.toNat_add]
  have : (UInt64.ofNat (2 ^ 64 - 1)).toBitVec.toNat = 2 ^ 64 - 1 := by decide
  rw [this]
  omega

/-- The interpreter has no fuel left for a block on the way: `graph_progress` is why that is all that can stop it. -/
def OutOfFuel (blocks : List Block) (fuel budget : Nat) (cfg : Bil.State × Nat) : Prop :=
  ∃ count, count ≤ budget ∧ ∃ reached, stepBlocks blocks fuel count cfg = .ok reached ∧ stepBlock blocks fuel reached = .error fuelError

/-- Where a run of a range ends: with `entered` blocks after the first, as many as the budget allows at most, and what the
interpreter has after that many and one blocks, at the pc that it goes on with. -/
def RangeEnds (stops : Nat → Bool) (blocks : List Block) (fuel budget budgetSlot effect : Nat) (global : Lowering) (program : List Op) (start : Cfg)
    (cfg : Bil.State × Nat) : Prop :=
  ∃ entered, entered ≤ budget ∧ ∃ state pc machine, stepBlocks blocks fuel (entered + 1) cfg = .ok (state, pc) ∧
    EndsAt stops program start pc machine ∧ Agrees state.env machine global ∧ (machine.slots budgetSlot).toNat = budget - entered ∧
    (machine.slots effect = 0 ∨ machine.slots effect = 1 ∨ (machine.slots effect = (3 : UInt64).toBitVec ∧ stops pc = true))


private theorem range_step {stops : Nat → Bool} {plan : GraphPlan} {low high effect : Nat} {global : Lowering} {program : List Op} {blocks : List Block}
    (hseg : ∀ block ∈ blocks, ∃ start, SegOK stops plan low high global program effect block start)
    (hlabel : ∀ source target label, EdgeTo plan source target label → ∃ block ∈ blocks, block.address = target ∧
      blockAt blocks target = some block ∧ ∃ address, (GraphPlan.labels plan).find? (fun (address, _) => address = block.address) = some (address, label))
    (hfits : ∀ block ∈ blocks, block.address < 2 ^ 64)
    (hfree : ∀ var, (var, effect) ∉ Lowering.layout global) (hbudgetFree : ∀ var, (var, GraphPlan.budget plan) ∉ Lowering.layout global)
    (hbud : GraphPlan.budget plan ≠ effect) (hbudgetLow : GraphPlan.budget plan < low) (heffLow : effect < low) (fuel budget : Nat)
    (ready : Nat → Bil.Env → Prop)
    (hready : ∀ block ∈ blocks, ∀ state, ready block.address state.env → Progress (Bil.execProgram fuel state block.program)
      (fun result => ∀ target, (block.address, target) ∈ GraphPlan.edges plan → ready target result.1.env))
    (ih : ∀ b, b + 1 = budget → ∀ (block : Block), block ∈ blocks → blockAt blocks block.address = some block →
      ∀ (start : List Op), SegOK stops plan low high global program effect block start →
      ∀ (state : Bil.State) (machine : Machine), Agrees state.env machine global → machine.slots effect = 0 →
      (machine.slots (GraphPlan.budget plan)).toNat = b → ready block.address state.env →
      OutOfFuel blocks fuel b (state, block.address) ∨ (loopLimit + 1 ≤ fuel ∧ ExhaustsAt stops program (start, machine) effect) ∨
        RangeEnds stops blocks fuel b (GraphPlan.budget plan) effect global program (start, machine) (state, block.address)) :
    ∀ (block : Block), block ∈ blocks → blockAt blocks block.address = some block →
      ∀ (start : List Op), SegOK stops plan low high global program effect block start →
      ∀ (state : Bil.State) (machine : Machine), Agrees state.env machine global → machine.slots effect = 0 →
      (machine.slots (GraphPlan.budget plan)).toNat = budget → ready block.address state.env →
      OutOfFuel blocks fuel budget (state, block.address) ∨ (loopLimit + 1 ≤ fuel ∧ ExhaustsAt stops program (start, machine) effect) ∨
        RangeEnds stops blocks fuel budget (GraphPlan.budget plan) effect global program (start, machine) (state, block.address) := by
  intro block hmem hat start seg state machine hag hz hb hr0
  have hstep : ∀ result, Bil.execProgram fuel state block.program = .ok result →
      stepBlock blocks fuel (state, block.address) = .ok (result.1, nextPc block result.2) := by
    intro result he
    simp [stepBlock, hat, he]
  cases hex : Bil.execProgram fuel state block.program with
  | error error =>
    have herror : error = fuelError := by
      rcases hready block hmem state hr0 with he | ⟨_, he, _⟩
      · rw [hex] at he
        simpa using he
      · rw [hex] at he
        cases he
    subst herror
    refine Or.inl ⟨0, Nat.zero_le _, (state, block.address), rfl, ?_⟩
    simp [stepBlock, hat, hex]
  | ok result =>
    have hreadyNext : ∀ target, (block.address, target) ∈ GraphPlan.edges plan → ready target result.1.env := by
      rcases hready block hmem state hr0 with he | ⟨_, he, hpost⟩
      · rw [hex] at he
        cases he
      · rw [hex] at he
        obtain rfl := Except.ok.inj he
        exact hpost
    have hone : stepBlocks blocks fuel 1 (state, block.address) = .ok (result.1, nextPc block result.2) := by
      simp [stepBlocks, hstep result hex]
    rcases seg.1 fuel state result machine hag hz hex with hx | ⟨m1, hend, hag1, hf1, heff1⟩ | ⟨m1, label, rest, hrun, hedge, hag1, hf1⟩
    · exact Or.inr (Or.inl hx)
    · refine Or.inr (Or.inr ⟨0, Nat.zero_le _, result.1, nextPc block result.2, m1, hone, hend, hag1, ?_, ?_⟩)
      · rw [hf1.2 _ hbud (Or.inl hbudgetLow) hbudgetFree, hb]
        simp
      · rcases heff1 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    · obtain ⟨target, htmem, haddr, hatT, address, hfind⟩ := hlabel _ _ _ hedge
      have hbudget1 : m1.slots (GraphPlan.budget plan) = machine.slots (GraphPlan.budget plan) :=
        hf1.2 _ (Or.inl hbudgetLow) hbudgetFree
      have hz1 : m1.slots effect = 0 := by rw [hf1.2 effect (Or.inl heffLow) hfree]; exact hz
      have hlt : target.address < 2 ^ 64 := hfits _ htmem
      have htoNat : (UInt64.ofNat target.address).toNat = target.address := by
        simp only [UInt64.toNat_ofNat']
        exact Nat.mod_eq_of_lt hlt
      obtain ⟨startT, segT⟩ := hseg target htmem
      have hany : (GraphPlan.edges plan).any (fun edge => edge.2 == target.address) = true := by
        rw [List.any_eq_true]
        exact ⟨_, hedge.1, by simp [haddr]⟩
      obtain ⟨entry, hafter, henter⟩ := segT.2 hany label address hfind
      have hgoto : RunAt stops program (start, machine) (entry, m1) :=
        hrun.trans (Run.goto hafter _).toAt
      have hpcT : nextPc block result.2 = target.address := haddr.symm
      rcases henter m1 hz1 with ⟨hzero, r, hr⟩ | ⟨hne, hstop, r, hr⟩ | ⟨hne, hr⟩
      · -- the budget is used up
        refine Or.inr (Or.inr ⟨0, Nat.zero_le _, result.1, target.address, m1.write effect (1 : UInt64).toBitVec, ?_, ?_, hag1.write_free hfree _, ?_, ?_⟩)
        · rw [← hpcT]; exact hone
        · exact Or.inl ⟨r, _, hgoto.trans hr, htoNat⟩
        · simp only [Machine.write_slots, hbud, ↓reduceIte, hzero]
          rw [← hb, ← hbudget1, hzero]
          rfl
        · refine Or.inr (Or.inl ?_)
          simp only [Machine.write_slots, ↓reduceIte]
          rfl
      · -- a code site stops the run
        refine Or.inr (Or.inr ⟨0, Nat.zero_le _, result.1, target.address, (m1.write effect (0 : UInt64).toBitVec).write effect (3 : UInt64).toBitVec, ?_, ?_, ?_, ?_, ?_⟩)
        · rw [← hpcT]; exact hone
        · exact Or.inr (Or.inr ⟨r, effect, _, _, hgoto.trans hr, hstop, rfl, htoNat⟩)
        · exact (hag1.write_free hfree _).write_free hfree _
        · simp only [Machine.write_slots, hbud, ↓reduceIte, hbudget1, hb]
          simp
        · refine Or.inr (Or.inr ⟨?_, by rw [htoNat] at hstop; exact hstop⟩)
          simp only [Machine.write_slots, ↓reduceIte]
      · -- the block counts, and the run goes on in it
        have hbudPos : 0 < budget := by
          apply Nat.pos_of_ne_zero
          intro hb0
          apply hne
          apply BitVec.eq_of_toNat_eq
          rw [hbudget1, hb, hb0]
          rfl
        obtain ⟨b, rfl⟩ : ∃ b, budget = b + 1 := ⟨budget - 1, by omega⟩
        let m2 := (m1.write effect (0 : UInt64).toBitVec).write (GraphPlan.budget plan) (m1.slots (GraphPlan.budget plan) + (UInt64.ofNat (2 ^ 64 - 1)).toBitVec)
        have hag2 : Agrees result.1.env m2 global := (hag1.write_free hfree _).write_free hbudgetFree _
        have hz2 : m2.slots effect = 0 := by
          simp only [m2, Machine.write_slots, Ne.symm hbud, ↓reduceIte]
          rfl
        have hb2 : (m2.slots (GraphPlan.budget plan)).toNat = b := by
          simp only [m2, Machine.write_slots, ↓reduceIte]
          rw [decrement_toNat hne, hbudget1, hb]
          simp
        have hstart := (hgoto.trans hr)
        rcases ih b rfl target htmem (by rw [haddr]; exact hatT) startT segT result.1 m2 hag2 hz2 hb2 (hreadyNext _ (by rw [haddr]; exact hedge.1)) with hfail | hx | hends
        · obtain ⟨count, hc, reached, h1, h2⟩ := hfail
          refine Or.inl ⟨count + 1, by omega, reached, ?_, h2⟩
          simp only [stepBlocks, hstep result hex]
          rw [hpcT]
          exact h1
        · exact Or.inr (Or.inl ⟨hx.1, hx.2.prepend hstart⟩)
        · obtain ⟨entered, he, st, pc, m3, h1, h2, h3, h4, h5⟩ := hends
          refine Or.inr (Or.inr ⟨entered + 1, by omega, st, pc, m3, ?_, h2.prepend hstart, h3, ?_, h5⟩)
          · rw [show entered + 1 + 1 = (entered + 1) + 1 from rfl]
            simp only [stepBlocks, hstep result hex]
            rw [hpcT]
            simpa only [stepBlocks] using h1
          · rw [h4]
            omega

/-- Blocks run one after the other along edges, with a budget: a run from the statements of a block, whose budget slot has `budget`, in an
environment `ready` for it, ends as many blocks later as `RangeEnds` says, unless a loop in it uses up its iterations or the interpreter has no fuel. -/
theorem range_core {stops : Nat → Bool} {plan : GraphPlan} {low high effect : Nat} {global : Lowering} {program : List Op} {blocks : List Block}
    (hseg : ∀ block ∈ blocks, ∃ start, SegOK stops plan low high global program effect block start)
    (hlabel : ∀ source target label, EdgeTo plan source target label → ∃ block ∈ blocks, block.address = target ∧
      blockAt blocks target = some block ∧ ∃ address, (GraphPlan.labels plan).find? (fun (address, _) => address = block.address) = some (address, label))
    (hfits : ∀ block ∈ blocks, block.address < 2 ^ 64)
    (hfree : ∀ var, (var, effect) ∉ Lowering.layout global) (hbudgetFree : ∀ var, (var, GraphPlan.budget plan) ∉ Lowering.layout global)
    (hbe : GraphPlan.edges plan ≠ [] → GraphPlan.budget plan ≠ effect) (hbudgetLow : GraphPlan.budget plan < low) (heffLow : effect < low) (fuel : Nat) (budget : Nat)
    (ready : Nat → Bil.Env → Prop)
    (hready : ∀ block ∈ blocks, ∀ state, ready block.address state.env → Progress (Bil.execProgram fuel state block.program)
      (fun result => ∀ target, (block.address, target) ∈ GraphPlan.edges plan → ready target result.1.env)) :
    GraphPlan.edges plan ≠ [] → ∀ (block : Block), block ∈ blocks → blockAt blocks block.address = some block →
      ∀ (start : List Op), SegOK stops plan low high global program effect block start →
      ∀ (state : Bil.State) (machine : Machine), Agrees state.env machine global → machine.slots effect = 0 →
      (machine.slots (GraphPlan.budget plan)).toNat = budget → ready block.address state.env →
      OutOfFuel blocks fuel budget (state, block.address) ∨ (loopLimit + 1 ≤ fuel ∧ ExhaustsAt stops program (start, machine) effect) ∨
        RangeEnds stops blocks fuel budget (GraphPlan.budget plan) effect global program (start, machine) (state, block.address) := by
  intro hedges
  have hbud := hbe hedges
  induction budget with
  | zero => exact range_step hseg hlabel hfits hfree hbudgetFree hbud hbudgetLow heffLow fuel 0 ready hready (fun _ h => by omega)
  | succ budget ih =>
    refine range_step hseg hlabel hfits hfree hbudgetFree hbud hbudgetLow heffLow fuel (budget + 1) ready hready ?_
    intro b hb
    obtain rfl : b = budget := by omega
    exact ih

/-! The flags. -/

/-- The operations that have flags set next to the moves. -/
def flagOps (flags : List (Nat × Nat)) (ops : List Op) : List Op := ops.flatMap (flagged flags)

@[simp] theorem flagOps_nil (flags : List (Nat × Nat)) : flagOps flags [] = [] := rfl

theorem flagOps_cons (flags : List (Nat × Nat)) (op : Op) (ops : List Op) :
    flagOps flags (op :: ops) = flagged flags op ++ flagOps flags ops := rfl

theorem afterLabel_flagOps (flags : List (Nat × Nat)) (program : List Op) (id : Nat) :
    afterLabel (flagOps flags program) id = (afterLabel program id).map (flagOps flags) := by
  induction program with
  | nil => rfl
  | cons op rest ih =>
    rw [flagOps_cons]
    cases op
    case move dst src =>
      simp only [flagged]
      split <;> simpa [afterLabel] using ih
    case label l =>
      simp only [flagged, List.singleton_append, afterLabel]
      split
      · rfl
      · exact ih
    all_goals
      simp only [flagged, List.singleton_append, afterLabel]
      exact ih

theorem afterLabel_sub {program target : List Op} {id : Nat} (h : afterLabel program id = some target) :
    ∀ op ∈ target, op ∈ program := by
  induction program with
  | nil => simp [afterLabel] at h
  | cons head rest ih =>
    intro op hop
    cases head
    case label l =>
      simp only [afterLabel] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact List.mem_cons_of_mem _ hop
      · exact List.mem_cons_of_mem _ (ih h op hop)
    all_goals exact List.mem_cons_of_mem _ (ih h op hop)

/-- A machine of the operations with flags, and the same machine without them. -/
structure FlagRel (limit : Nat) (flags : List (Nat × Nat)) (m m' : Machine) : Prop where
  slots : ∀ slot, slot < limit → m'.slots slot = m.slots slot
  memory : m'.memory = m.memory
  view : m'.view = m.view
  flag : ∀ slot f, flags.find? (fun flag => flag.1 == slot) = some f → (m'.slots f.2 ≠ 0 ↔ m.moved slot = true)

theorem FlagRel.write {limit : Nat} {flags : List (Nat × Nat)} {m m' : Machine} (h : FlagRel limit flags m m') (hf : ∀ f ∈ flags, limit ≤ f.2)
    {slot : Nat} (hs : slot < limit) (value : Word64) : FlagRel limit flags (m.write slot value) (m'.write slot value) where
  slots := fun other ho => by simp only [Machine.write_slots, h.slots other ho]
  memory := h.memory
  view := h.view
  flag := fun other f hfind => by
    have hne : f.2 ≠ slot := by
      have := hf f (List.mem_of_find?_eq_some hfind)
      omega
    simp only [Machine.write_slots, hne, ↓reduceIte]
    exact h.flag other f hfind

private theorem denoteLoad_congr {m m' : Machine} (hm : m'.memory = m.memory) (hv : m'.view = m.view) (base : Word64) (size : Nat) (big : Bool) :
    denoteLoad (fun address => m'.memory (m'.view address)) base size big = denoteLoad (fun address => m.memory (m.view address)) base size big := by
  rw [hm, hv]

/-- An operation that is not a move does the same on both machines, when it stays in the slots. -/
theorem FlagRel.step {limit : Nat} {flags : List (Nat × Nat)} {m m' : Machine} (h : FlagRel limit flags m m') (hf : ∀ f ∈ flags, limit ≤ f.2)
    {op : Op} (hslots : ∀ slot ∈ opSlots op, slot < limit) (hmove : ∀ dst src, op ≠ .move dst src) :
    FlagRel limit flags (Bap.Proofs.Primus.step m op) (Bap.Proofs.Primus.step m' op) := by
  have hs : ∀ {slot}, slot ∈ opSlots op → m'.slots slot = m.slots slot := fun hm => h.slots _ (hslots _ hm)
  cases op
  case set dst imm =>
    exact h.write hf (hslots dst (by simp [opSlots])) _
  case move dst src => exact absurd rfl (hmove dst src)
  case add dst src imm =>
    have := hs (slot := src) (by simp [opSlots])
    simp only [Bap.Proofs.Primus.step, this]
    exact h.write hf (hslots dst (by simp [opSlots])) _
  case bin op dst left right =>
    have h1 := hs (slot := left) (by simp [opSlots])
    have h2 := hs (slot := right) (by simp [opSlots])
    simp only [Bap.Proofs.Primus.step, h1, h2]
    exact h.write hf (hslots dst (by simp [opSlots])) _
  case andImm dst src imm =>
    have := hs (slot := src) (by simp [opSlots])
    simp only [Bap.Proofs.Primus.step, this]
    exact h.write hf (hslots dst (by simp [opSlots])) _
  case signExtend width dst src =>
    have := hs (slot := src) (by simp [opSlots])
    simp only [Bap.Proofs.Primus.step, this]
    exact h.write hf (hslots dst (by simp [opSlots])) _
  case select dst condition yes no =>
    have h1 := hs (slot := condition) (by simp [opSlots])
    have h2 := hs (slot := yes) (by simp [opSlots])
    have h3 := hs (slot := no) (by simp [opSlots])
    simp only [Bap.Proofs.Primus.step, h1, h2, h3]
    exact h.write hf (hslots dst (by simp [opSlots])) _
  case neg dst src =>
    have := hs (slot := src) (by simp [opSlots])
    simp only [Bap.Proofs.Primus.step, this]
    exact h.write hf (hslots dst (by simp [opSlots])) _
  case not dst src =>
    have := hs (slot := src) (by simp [opSlots])
    simp only [Bap.Proofs.Primus.step, this]
    exact h.write hf (hslots dst (by simp [opSlots])) _
  case ashr width dst left right =>
    have h1 := hs (slot := left) (by simp [opSlots])
    have h2 := hs (slot := right) (by simp [opSlots])
    simp only [Bap.Proofs.Primus.step, h1, h2]
    exact h.write hf (hslots dst (by simp [opSlots])) _
  case memLoad dst address size big =>
    have h1 := hs (slot := address) (by simp [opSlots])
    simp only [Bap.Proofs.Primus.step, h1, denoteLoad_congr h.memory h.view]
    exact h.write hf (hslots dst (by simp [opSlots])) _
  case memStore address value size big =>
    have h1 := hs (slot := address) (by simp [opSlots])
    have h2 := hs (slot := value) (by simp [opSlots])
    refine ⟨h.slots, ?_, h.view, h.flag⟩
    simp only [Bap.Proofs.Primus.step, h1, h2, h.memory, h.view]
  all_goals exact h

private theorem flagSlots_spec (outputs : List (Bap.Var × Nat)) {limit start next : Nat} {init flags : List (Nat × Nat)}
    (h : outputs.foldl (init := (start, init)) (fun (next, flags) output => (next + 1, (output.2, next) :: flags)) = (next, flags))
    (hl : limit ≤ start) (hi : ∀ f ∈ init, limit ≤ f.2 ∧ f.2 < start) (hd : init.Pairwise fun a b => a.2 ≠ b.2) :
    start ≤ next ∧ (∀ f ∈ flags, limit ≤ f.2 ∧ f.2 < next) ∧ (flags.Pairwise fun a b => a.2 ≠ b.2) ∧ (∀ f ∈ init, f ∈ flags) ∧
      ∀ output ∈ outputs, ∃ f ∈ flags, f.1 = output.2 := by
  induction outputs generalizing start init with
  | nil =>
    simp only [List.foldl_nil, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, hi, hd, fun _ h => h, by simp⟩
  | cons head rest ih =>
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih h (by omega)
      (by
        intro f hm
        rcases List.mem_cons.1 hm with rfl | hm
        · simpa using hl
        · have := hi f hm
          omega)
      (by
        refine List.pairwise_cons.2 ⟨?_, hd⟩
        intro f hm
        have := hi f hm
        simp only
        omega)
    refine ⟨by omega, h2, h3, fun f hm => h4 f (List.mem_cons_of_mem _ hm), ?_⟩
    intro output hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨_, h4 _ List.mem_cons_self, rfl⟩
    · exact h5 output hm

/-- A move does the same on both machines, and sets the flag. -/
theorem FlagRel.move {limit : Nat} {flags : List (Nat × Nat)} {m m' : Machine} (h : FlagRel limit flags m m') (hf : ∀ f ∈ flags, limit ≤ f.2)
    (hd : flags.Pairwise fun a b => a.2 ≠ b.2) {dst src : Nat} (hdst : dst < limit) (hsrc : src < limit) :
    ∃ m2', (∀ {stops : Nat → Bool} {program rest : List Op}, RunAt stops program (flagged flags (.move dst src) ++ rest, m') (rest, m2')) ∧
      FlagRel limit flags (Bap.Proofs.Primus.step m (.move dst src)) m2' := by
  have hv : m'.slots src = m.slots src := h.slots src hsrc
  simp only [Bap.Proofs.Primus.step]
  cases hfind : flags.find? (fun flag => flag.1 == dst) with
  | none =>
    refine ⟨Bap.Proofs.Primus.step m' (.move dst src), ?_, ?_⟩
    · intro stops program rest
      simp only [flagged, hfind, List.singleton_append]
      exact (Run.linear (op := .move dst src) rfl rest m').toAt
    · refine ⟨fun other ho => ?_, h.memory, h.view, fun other f hfo => ?_⟩
      · simp only [Bap.Proofs.Primus.step, Machine.markMove_slots, hv, h.slots other ho]
      · have hne : f.2 ≠ dst := by
          have := hf f (List.mem_of_find?_eq_some hfo)
          omega
        have hod : other ≠ dst := by
          intro he
          subst he
          rw [hfind] at hfo
          simp at hfo
        have hslot : (Bap.Proofs.Primus.step m' (.move dst src)).slots f.2 = m'.slots f.2 := by
          simp [Bap.Proofs.Primus.step, hne]
        have hm : (m.markMove dst (m.slots src)).moved other = m.moved other := by simp [Machine.markMove, hod]
        rw [hslot, hm]
        exact h.flag other f hfo
  | some f0 =>
    refine ⟨(Bap.Proofs.Primus.step m' (.move dst src)).write f0.2 (1 : UInt64).toBitVec, ?_, ?_⟩
    · intro stops program rest
      simp only [flagged, hfind, List.cons_append, List.nil_append]
      exact ((Run.linear (op := .move dst src) rfl _ m').trans (Run.linear (op := .set f0.2 1) rfl rest _)).toAt
    · have hf0 := hf f0 (List.mem_of_find?_eq_some hfind)
      refine ⟨fun other ho => ?_, h.memory, h.view, fun other f hfo => ?_⟩
      · have hne : other ≠ f0.2 := by omega
        simp only [Machine.write_slots, hne, ↓reduceIte, Bap.Proofs.Primus.step, Machine.markMove_slots, hv, h.slots other ho]
      · have hne : f.2 ≠ dst := by
          have := hf f (List.mem_of_find?_eq_some hfo)
          omega
        by_cases hod : other = dst
        · subst hod
          rw [hfind] at hfo
          simp only [Option.some.injEq] at hfo
          subst hfo
          simp [Machine.markMove, Machine.write_slots]
        · have hkey : f.1 = other := by simpa using List.find?_some hfo
          have hkey0 : f0.1 = dst := by simpa using List.find?_some hfind
          have hne0 : f.2 ≠ f0.2 := by
            intro he
            have hsame := pairwise_same hd (List.mem_of_find?_eq_some hfo) (List.mem_of_find?_eq_some hfind) he
            apply hod
            rw [← hkey, ← hkey0, hsame]
          have hslot : ((Bap.Proofs.Primus.step m' (.move dst src)).write f0.2 (1 : UInt64).toBitVec).slots f.2 = m'.slots f.2 := by
            simp [Bap.Proofs.Primus.step, hne, hne0, Machine.write_slots]
          have hm : (m.markMove dst (m.slots src)).moved other = m.moved other := by simp [Machine.markMove, hod]
          rw [hslot, hm]
          exact h.flag other f hfo

/-- A run without flags is a run with them. -/
theorem RunAt.withFlags {stops : Nat → Bool} {program : List Op} {limit : Nat} {flags : List (Nat × Nat)} {a b : Cfg}
    (hr : RunAt stops program a b) (hf : ∀ f ∈ flags, limit ≤ f.2) (hd : flags.Pairwise fun a b => a.2 ≠ b.2)
    (hslots : ∀ op ∈ program, ∀ slot ∈ opSlots op, slot < limit) :
    (∀ op ∈ a.1, op ∈ program) → ∀ m', FlagRel limit flags a.2 m' →
      (∀ op ∈ b.1, op ∈ program) ∧ ∃ m2', RunAt stops (flagOps flags program) (flagOps flags a.1, m') (flagOps flags b.1, m2') ∧ FlagRel limit flags b.2 m2' := by
  induction hr with
  | refl cfg =>
    intro hin m' hrel
    exact ⟨hin, m', .refl _, hrel⟩
  | @step first second last hn _ ih =>
    intro hin m' hrel
    obtain ⟨ops, m⟩ := first
    cases ops with
    | nil => simp [nextCfgAt, nextCfg] at hn
    | cons op rest =>
      have hop : op ∈ program := hin op List.mem_cons_self
      have hrest : ∀ o ∈ rest, o ∈ program := fun o ho => hin o (List.mem_cons_of_mem _ ho)
      have hcont : ∀ {m2 : Machine} {m2' : Machine}, FlagRel limit flags m2 m2' → second = (rest, m2) →
          (∀ op ∈ last.1, op ∈ program) ∧ ∃ m3', RunAt stops (flagOps flags program) (flagOps flags rest, m2') (flagOps flags last.1, m3') ∧
            FlagRel limit flags last.2 m3' := by
        intro m2 m2' hr2 he
        subst he
        exact ih hrest m2' hr2
      cases op
      case goto id =>
        simp only [nextCfgAt, nextCfg] at hn
        cases hl : afterLabel program id with
        | none => simp [hl] at hn
        | some target =>
          simp only [hl, Option.map_some, Option.some.injEq] at hn
          subst hn
          obtain ⟨h1, m3, h2, h3⟩ := ih (afterLabel_sub hl) m' hrel
          refine ⟨h1, m3, ?_, h3⟩
          refine .step ?_ h2
          simp [nextCfgAt, nextCfg, flagOps_cons, flagged, afterLabel_flagOps, hl]
      case branch condition yes no =>
        simp only [nextCfgAt, nextCfg] at hn
        have hc : m'.slots condition = m.slots condition := hrel.slots _ (hslots _ hop condition (by simp [opSlots]))
        cases hl : afterLabel program (if m.slots condition ≠ 0 then yes else no) with
        | none =>
          rw [hl] at hn
          simp at hn
        | some target =>
          rw [hl] at hn
          simp only [Option.map_some, Option.some.injEq] at hn
          subst hn
          obtain ⟨h1, m3, h2, h3⟩ := ih (afterLabel_sub hl) m' hrel
          refine ⟨h1, m3, ?_, h3⟩
          refine .step ?_ h2
          show nextCfg (flagOps flags program) (.branch condition yes no :: flagOps flags rest, m') = _
          simp only [nextCfg, hc, afterLabel_flagOps, hl, Option.map_some]
      case jump t => simp [nextCfgAt, nextCfg] at hn
      case jumpSlot s => simp [nextCfgAt, nextCfg] at hn
      case code e t =>
        simp only [nextCfgAt] at hn
        split at hn
        · simp at hn
        · next hs =>
          simp only [Option.some.injEq] at hn
          subst hn
          obtain ⟨h1, m3, h2, h3⟩ := ih hrest m' hrel
          exact ⟨h1, m3, (RunAt.pass hs).trans h2, h3⟩
      case move dst src =>
        have hn' : second = (rest, Bap.Proofs.Primus.step m (.move dst src)) := by
          simpa [nextCfgAt, nextCfg] using hn.symm
        obtain ⟨m2', hrun, hr2⟩ := FlagRel.move hrel hf hd (hslots _ hop dst (by simp [opSlots])) (hslots _ hop src (by simp [opSlots]))
        obtain ⟨h1, m3, h2, h3⟩ := hcont hr2 hn'
        exact ⟨h1, m3, by rw [flagOps_cons]; exact hrun.trans h2, h3⟩
      all_goals
        have hn' := Option.some.inj ((nextCfgAt_of_next (stops := stops) (program := program) (a := (_, m)) (b := (rest, _)) rfl).symm.trans hn)
        have hr2 := FlagRel.step hrel hf (hslots _ hop) (by intro _ _ he; cases he)
        obtain ⟨h1, m3, h2, h3⟩ := hcont hr2 hn'.symm
        refine ⟨h1, m3, ?_, h3⟩
        rw [flagOps_cons]
        exact (Run.linear rfl _ m').toAt.trans h2

private theorem withoutBindings_lookup (var : Bap.Var) (env : Bil.Env) (pending : List Bap.Var) (h : var ∉ pending) :
    Bil.lookup (withoutBindings pending env) var = Bil.lookup env var := by
  induction env generalizing pending with
  | nil => rfl
  | cons binding rest ih =>
    simp only [withoutBindings]
    split
    · rfl
    · split
      · next hc =>
        rw [ih _ (fun hm => h (List.mem_of_mem_erase hm))]
        have hne : (binding.1 == var) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          intro he
          subst he
          exact h (by simpa using hc)
        simp [Bil.lookup, hne]
      · have hl := ih pending h
        simp only [Bil.lookup, List.find?_cons] at hl ⊢
        cases (binding.1 == var) with
        | true => rfl
        | false => exact hl

private theorem syncUpdates_names {outputs : List (Bap.Var × Nat)} {slots : Array UInt64} {update : Bap.Var × Bap.Value}
    (h : update ∈ syncUpdates outputs slots) : ∃ slot, (update.1, slot) ∈ outputs := by
  induction outputs with
  | nil => simp [syncUpdates] at h
  | cons head rest ih =>
    simp only [syncUpdates, List.foldr_cons] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact ⟨head.2, List.mem_cons_self⟩
      · obtain ⟨s, hs⟩ := ih h
        exact ⟨s, List.mem_cons_of_mem _ hs⟩
    · obtain ⟨s, hs⟩ := ih h
      exact ⟨s, List.mem_cons_of_mem _ hs⟩

/-- A variable that the run did not reach keeps what it had. -/
theorem syncState_other {lowering : Lowering} {state : Bil.State} {slots : Array UInt64} {var : Bap.Var}
    (h : ∀ slot, (var, slot) ∉ reachedOutputs lowering slots) :
    Bil.lookup (syncState lowering state slots).env var = Bil.lookup state.env var := by
  have hnames : ∀ update ∈ syncUpdates (reachedOutputs lowering slots) slots, update.1 ≠ var := by
    intro update hu he
    obtain ⟨s, hs⟩ := syncUpdates_names hu
    rw [he] at hs
    exact h s hs
  have hnot : var ∉ (syncUpdates (reachedOutputs lowering slots) slots).map Prod.fst := by
    intro hm
    obtain ⟨u, hu, he⟩ := List.mem_map.1 hm
    exact hnames u hu he
  simp only [syncState]
  rw [← withoutBindings_lookup var state.env _ hnot]
  generalize withoutBindings _ state.env = rest
  generalize syncUpdates (reachedOutputs lowering slots) slots = updates at hnames hnot ⊢
  simp only [Bil.lookup, List.find?_append]
  have : updates.find? (fun binding => binding.1 == var) = none := by
    apply List.find?_eq_none.2
    intro u hu
    simpa using hnames u hu
  simp [this]

/-- The way out of a range: the variables have what the interpreter has, if only a flag may say that one was not written, and what
is not flagged has a value. -/
theorem syncState_flags {lowering global : Lowering} {state : Bil.State} {env : Bil.Env} {m m' : Machine} {out : Array UInt64}
    (hflagKeys : (∀ output ∈ Lowering.outputs lowering, (Lowering.flags lowering).find? (fun flag => flag.1 == output.2) = none →
      ∃ value, Bil.lookup env output.1 = .ok value))
    (hagree : Agrees env m global) (hlayout : Lowering.layout global = Lowering.layout lowering)
    (hwf : LayoutWF lowering) (hsub : ∀ output ∈ Lowering.outputs lowering, output ∈ Lowering.layout lowering)
    (hrel : FlagRel (Lowering.nextSlot global) (Lowering.flags lowering) m m') (hnext : Lowering.nextSlot global ≤ Lowering.nextSlot lowering)
    (hbound : ∀ binding ∈ Lowering.layout lowering, binding.2 < Lowering.nextSlot global)
    (hflagsLow : ∀ f ∈ Lowering.flags lowering, f.2 < Lowering.nextSlot lowering)
    (horigin : m.origin = state.env) (hmoved : ∀ binding ∈ Lowering.layout lowering, m.moved binding.2 = true → binding ∈ Lowering.outputs lowering)
    (hout : ∀ index, index < Lowering.nextSlot lowering → (out.getD index 0).toBitVec = m'.slots index)
    {var : Bap.Var} (hmem : Lowering.memory global ≠ some var) :
    Bil.lookup (syncState lowering state out).env var = Bil.lookup env var := by
  have hflagOf : ∀ f ∈ Lowering.flags lowering, (out.getD f.2 0 != 0) = true → m'.slots f.2 ≠ 0 := by
    intro f hf hne he
    have := hout f.2 (hflagsLow f hf)
    rw [he] at this
    simp only [bne_iff_ne, ne_eq] at hne
    apply hne
    exact UInt64.eq_of_toBitVec_eq (by simpa using this)
  by_cases hin : ∃ slot, (var, slot) ∈ reachedOutputs lowering out
  · obtain ⟨slot, hslot⟩ := hin
    have hoput : (var, slot) ∈ Lowering.outputs lowering := by
      unfold reachedOutputs at hslot
      split at hslot
      · exact hslot
      · exact (List.mem_filter.1 hslot).1
    have hlay := hsub _ hoput
    have hvalue : ∃ value, Bil.lookup env var = .ok value := by
      cases hfind : (Lowering.flags lowering).find? (fun flag => flag.1 == slot) with
      | none => exact hflagKeys _ hoput hfind
      | some f =>
        have hnotEmpty : (Lowering.flags lowering).isEmpty = false := by
          cases hfl : Lowering.flags lowering with
          | nil => rw [hfl] at hfind; simp at hfind
          | cons _ _ => rfl
        unfold reachedOutputs at hslot
        simp only [hnotEmpty, Bool.false_eq_true, ↓reduceIte, List.mem_filter] at hslot
        have hset := hslot.2
        simp only [hfind] at hset
        have hne := hflagOf f (List.mem_of_find?_eq_some hfind) hset
        have hmv := (hrel.flag slot f hfind).1 hne
        exact hagree.bound (var, slot) (by rw [hlayout]; exact hlay) hmv
    obtain ⟨value, hv⟩ := hvalue
    obtain ⟨width, bits, rfl, hw, hholds⟩ := hagree.slots (var, slot) (by rw [hlayout]; exact hlay) value hv
    have hu : ∀ other, (var, other) ∈ reachedOutputs lowering out → other = slot := by
      intro other ho
      have hoo : (var, other) ∈ Lowering.outputs lowering := by
        unfold reachedOutputs at ho
        split at ho
        · exact ho
        · exact (List.mem_filter.1 ho).1
      have := pairwise_same hwf.varsDistinct (hsub _ hoo) hlay rfl
      exact congrArg Prod.snd this
    rw [syncState_output hslot hw hu, hv]
    have hsl := hbound _ hlay
    have heq : (out.getD slot 0).toBitVec = m.slots slot := by
      rw [hout slot (Nat.lt_of_lt_of_le hsl hnext), hrel.slots slot hsl]
    have : Holds (out.getD slot 0).toBitVec bits := by
      rw [heq]
      exact hholds
    rw [slotBits_holds this]
  · have hnone : ∀ slot, (var, slot) ∉ reachedOutputs lowering out := fun slot hs => hin ⟨slot, hs⟩
    rw [syncState_other hnone]
    refine Classical.byContradiction fun hne => ?_
    have hne' : Bil.lookup env var ≠ Bil.lookup m.origin var := by
      rw [horigin]
      exact fun he => hne he.symm
    rcases hagree.changed var hne' with hm | ⟨slot, hl, hmv⟩
    · exact hmem hm
    · have hl' : (var, slot) ∈ Lowering.layout lowering := by rw [← hlayout]; exact hl
      have hoput := hmoved _ hl' hmv
      apply hnone slot
      unfold reachedOutputs
      split
      · exact hoput
      · refine List.mem_filter.2 ⟨hoput, ?_⟩
        cases hfind : (Lowering.flags lowering).find? (fun flag => flag.1 == slot) with
        | none => simp
        | some f =>
          have hset := (hrel.flag slot f hfind).2 hmv
          have := hout f.2 (hflagsLow f (List.mem_of_find?_eq_some hfind))
          simp only [bne_iff_ne, ne_eq]
          intro hz
          rw [hz] at this
          apply hset
          simpa using this.symm

/-! The whole of it. -/

/-- A step within a program stays in it, and only a move marks a slot. -/
private theorem nextCfgAt_inside {stops : Nat → Bool} {program : List Op} {a b : Cfg} (h : nextCfgAt stops program a = some b)
    (hin : ∀ op ∈ a.1, op ∈ program) (hm : ∀ slot, a.2.moved slot = true → ∃ src, Op.move slot src ∈ program) :
    b.2.origin = a.2.origin ∧ (∀ op ∈ b.1, op ∈ program) ∧ ∀ slot, b.2.moved slot = true → ∃ src, Op.move slot src ∈ program := by
  obtain ⟨ops, m⟩ := a
  cases ops with
  | nil => simp [nextCfgAt, nextCfg] at h
  | cons op rest =>
    have hrest : ∀ o ∈ rest, o ∈ program := fun o ho => hin o (List.mem_cons_of_mem _ ho)
    have hop : op ∈ program := hin op List.mem_cons_self
    cases op
    case goto id =>
      simp only [nextCfgAt, nextCfg] at h
      cases hl : afterLabel program id with
      | none => simp [hl] at h
      | some target =>
        simp only [hl, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, afterLabel_sub hl, hm⟩
    case branch condition yes no =>
      simp only [nextCfgAt, nextCfg] at h
      cases hl : afterLabel program (if m.slots condition ≠ 0 then yes else no) with
      | none => rw [hl] at h; simp at h
      | some target =>
        rw [hl] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, afterLabel_sub hl, hm⟩
    case jump t => simp [nextCfgAt, nextCfg] at h
    case jumpSlot s => simp [nextCfgAt, nextCfg] at h
    case code e t =>
      simp only [nextCfgAt] at h
      split at h
      · simp at h
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, hrest, hm⟩
    case move dst src =>
      have hb : b = (rest, Bap.Proofs.Primus.step m (.move dst src)) := by
        simpa [nextCfgAt, nextCfg] using h.symm
      subst hb
      refine ⟨rfl, hrest, fun slot hs => ?_⟩
      simp only [Bap.Proofs.Primus.step, Machine.markMove, Bool.or_eq_true, beq_iff_eq] at hs
      rcases hs with rfl | hs
      · exact ⟨src, hop⟩
      · exact hm slot hs
    all_goals
      have hb := Option.some.inj ((nextCfgAt_of_next (stops := stops) (program := program) (a := (_, m)) (b := (rest, _)) rfl).symm.trans h)
      subst hb
      exact ⟨step_origin _ _, hrest, hm⟩

private theorem RunAt.inside {stops : Nat → Bool} {program : List Op} {a b : Cfg} (h : RunAt stops program a b)
    (hin : ∀ op ∈ a.1, op ∈ program) (hm : ∀ slot, a.2.moved slot = true → ∃ src, Op.move slot src ∈ program) :
    b.2.origin = a.2.origin ∧ (∀ op ∈ b.1, op ∈ program) ∧ ∀ slot, b.2.moved slot = true → ∃ src, Op.move slot src ∈ program := by
  induction h with
  | refl => exact ⟨rfl, hin, hm⟩
  | step hn _ ih =>
    obtain ⟨h0, h1, h2⟩ := nextCfgAt_inside hn hin hm
    obtain ⟨h3, h4, h5⟩ := ih h1 h2
    exact ⟨h3.trans h0, h4, h5⟩

/-- A run that ends in the operations without flags ends the same way in those with them. -/
private theorem EndsAt.withFlags {stops : Nat → Bool} {program : List Op} {limit : Nat} {flags : List (Nat × Nat)} {m0 m0' m : Machine} {pc : Nat}
    (hend : EndsAt stops program (program, m0) pc m) (hf : ∀ f ∈ flags, limit ≤ f.2) (hd : flags.Pairwise fun a b => a.2 ≠ b.2)
    (hslots : ∀ op ∈ program, ∀ slot ∈ opSlots op, slot < limit) (hrel : FlagRel limit flags m0 m0')
    (hm0 : ∀ slot, m0.moved slot = true → ∃ src, Op.move slot src ∈ program) :
    ∃ m', EndsAt stops (flagOps flags program) (flagOps flags program, m0') pc m' ∧ FlagRel limit flags m m' ∧
      m.origin = m0.origin ∧ ∀ slot, m.moved slot = true → ∃ src, Op.move slot src ∈ program := by
  have hin0 : ∀ op ∈ program, op ∈ program := fun _ h => h
  rcases hend with ⟨rest, target, hr, hpc⟩ | ⟨rest, slot, hr, hpc⟩ | ⟨rest, effect, target, before, hr, hstop, rfl, hpc⟩
  · obtain ⟨_, m', h2, h3⟩ := hr.withFlags hf hd hslots hin0 m0' hrel
    have hi := hr.inside hin0 hm0
    exact ⟨m', Or.inl ⟨flagOps flags rest, target, h2, hpc⟩, h3, hi.1, hi.2.2⟩
  · obtain ⟨hin, m', h2, h3⟩ := hr.withFlags hf hd hslots hin0 m0' hrel
    have hs : m'.slots slot = m.slots slot := h3.slots _ (hslots _ (hin _ List.mem_cons_self) slot (by simp [opSlots]))
    have hi := hr.inside hin0 hm0
    exact ⟨m', Or.inr (Or.inl ⟨flagOps flags rest, slot, h2, by rw [hs]; exact hpc⟩), h3, hi.1, hi.2.2⟩
  · obtain ⟨hin, m', h2, h3⟩ := hr.withFlags hf hd hslots hin0 m0' hrel
    have he : effect < limit := hslots _ (hin _ List.mem_cons_self) effect (by simp [opSlots])
    exact ⟨m'.write effect (3 : UInt64).toBitVec, Or.inr (Or.inr ⟨flagOps flags rest, effect, target, m', h2, hstop, rfl, hpc⟩),
      h3.write hf he _, (hr.inside hin0 hm0).1, (hr.inside hin0 hm0).2.2⟩

private theorem opLabels_eq (ops : List Op) : opLabels ops = labelsOf ops := rfl

/-- What the check of a lowering says. -/
private structure Checked (blocks : List Block) (initial lowering : Lowering) : Prop where
  budget : Lowering.budget lowering = Lowering.budget initial
  observed : Lowering.observed lowering = Lowering.observed initial
  addresses : (blocks.map Block.address).Nodup
  fits : ∀ block ∈ blocks, block.address < 2 ^ 64 ∧ block.next < 2 ^ 64
  labels : (labelsOf (Lowering.ops lowering)).Nodup
  slots : ∀ op ∈ Lowering.ops lowering, ∀ slot ∈ opSlots op, slot < Lowering.nextSlot lowering
  outputs : ∀ output ∈ Lowering.outputs lowering, output ∈ Lowering.layout lowering
  inputs : ∀ var ∈ Lowering.inputs lowering, ∃ binding ∈ Lowering.layout lowering, binding.1 = var
  moves : ∀ dst src, Op.move dst src ∈ Lowering.ops lowering → ∀ binding ∈ Lowering.layout lowering, binding.2 = dst → binding ∈ Lowering.outputs lowering

private theorem checked_of {blocks : List Block} {initial lowering : Lowering} (h : lowerGraphChecked blocks initial lowering = true) :
    Checked blocks initial lowering := by
  simp only [lowerGraphChecked, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h7, h8⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h9⟩, h6⟩ := h
  refine ⟨h7, h8, h1, ?_, by rw [← opLabels_eq]; exact h3, ?_, ?_, ?_, ?_⟩
  · intro block hb
    exact h2 block hb
  · intro op hop slot hs
    simpa using h4 op hop slot hs
  · intro output ho
    simpa using h5 output ho
  · intro var hv
    simpa using h9 var hv
  · intro dst src hm binding hb hd
    have := h6 _ hm
    simp only [List.all_eq_true] at this
    have := this binding hb
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem] at this
    rcases this with h | h
    · exact absurd hd h
    · exact h

private theorem blockAt_of_mem {blocks : List Block} {block : Block} (hd : (blocks.map Block.address).Nodup) (hm : block ∈ blocks) :
    blockAt blocks block.address = some block := by
  induction blocks with
  | nil => simp at hm
  | cons head rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hd
    simp only [blockAt, List.find?_cons]
    rcases List.mem_cons.1 hm with rfl | hm
    · simp
    · have hne : head.address ≠ block.address := fun he => hd.1 (he ▸ List.mem_map_of_mem hm)
      have hb : (head.address == block.address) = false := by simpa using hne
      simp only [hb]
      exact ih hd.2 hm

/-- The labels of a graph are those of its blocks. -/
private theorem labels_block {blocks : List Block} {target address label : Nat}
    (h : ((List.range blocks.length).map fun index => (blocks[index]!.address, index)).find? (fun (address, _) => address = target) = some (address, label)) :
    ∃ block ∈ blocks, block.address = target := by
  have hmem := List.mem_of_find?_eq_some h
  have hsat := List.find?_some h
  simp only [decide_eq_true_eq] at hsat
  obtain ⟨index, hi, he⟩ := List.mem_map.1 hmem
  simp only [Prod.mk.injEq] at he
  have hlt := List.mem_range.1 hi
  refine ⟨blocks[index], List.getElem_mem hlt, ?_⟩
  rw [← hsat, ← he.1]
  simp [getElem!_pos, hlt]

/-- What `lowerGraph` is made of. -/
private theorem lowerGraph_parts {blocks : List Block} {edges : List (Nat × Nat)} {wrapFaults : Bool} {lowering : Lowering}
    (h : lowerGraph blocks edges wrapFaults = some lowering) :
    ∃ seed rest plan initial final, blocks = seed :: rest ∧ lowering = flagOutputs (leadingMoves seed.program) final ∧
      lowerBlocks plan initial blocks = some final ∧ lowerGraphChecked blocks initial final = true ∧
      GraphPlan.edges plan = edges ∧ GraphPlan.seed plan = seed.address ∧
      GraphPlan.labels plan = (List.range blocks.length).map (fun index => (blocks[index]!.address, index)) ∧
      Lowering.ops initial = [.set 0 0] ∧ Lowering.layout initial = [] ∧ Lowering.effectSlot initial = some 0 ∧ 0 < Lowering.nextSlot initial ∧
      Lowering.flags initial = [] ∧
      (edges ≠ [] → GraphPlan.budget plan = 1 ∧ Lowering.nextSlot initial = 3 ∧ Lowering.budget initial = some 1 ∧ Lowering.observed initial = some 2) ∧
      GraphPlan.definite plan = writtenAt (definitelyWritten seed.address blocks edges) ∧ GraphPlan.chained plan = !edges.isEmpty ∧
      Lowering.written initial = [] := by
  unfold lowerGraph at h
  cases blocks with
  | nil => simp at h
  | cons seed rest =>
    simp only [List.head?_cons, bind, Option.bind_some] at h
    obtain ⟨final, h1, h⟩ := obind h
    by_cases hc : lowerGraphChecked (seed :: rest) (graphInitial seed (seed :: rest).length wrapFaults !edges.isEmpty) final = true
    · rw [ite_eq_left hc] at h
      simp only [Option.some.injEq] at h
      refine ⟨seed, rest, _, _, final, rfl, h.symm, h1, hc, rfl, rfl, rfl, ?_⟩
      cases edges with
      | nil => simp [graphInitial, graphPlan, setEffect, temporary]
      | cons e es => simp [graphInitial, graphPlan, setEffect, temporary]
    · rw [ite_eq_right hc] at h
      cases h

/-- The fields of a lowering with flags. -/
private theorem flagOutputs_parts (written : List Bap.Var) (final : Lowering) :
    let later := (Lowering.outputs final).filter fun output => !written.contains output.1
    Lowering.ops (flagOutputs written final) = flagOps (flagSlots later (Lowering.nextSlot final)).2 (Lowering.ops final) ∧
    Lowering.flags (flagOutputs written final) = (flagSlots later (Lowering.nextSlot final)).2 ∧
    Lowering.nextSlot (flagOutputs written final) = (flagSlots later (Lowering.nextSlot final)).1 ∧
    Lowering.layout (flagOutputs written final) = Lowering.layout final ∧
    Lowering.outputs (flagOutputs written final) = Lowering.outputs final ∧
    Lowering.memory (flagOutputs written final) = Lowering.memory final ∧
    Lowering.effectSlot (flagOutputs written final) = Lowering.effectSlot final ∧
    Lowering.budget (flagOutputs written final) = Lowering.budget final ∧
    Lowering.observed (flagOutputs written final) = Lowering.observed final ∧
    Lowering.inputs (flagOutputs written final) = Lowering.inputs final :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The encoding of a state has found each input bound. -/
private theorem encode_bound (env : Bil.Env) (inputs : List Bap.Var) (layout : List (Bap.Var × Nat)) (init : Array UInt64) (result : Array UInt64)
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
        if inputs.contains var then .error error else .ok slots) = .ok result)
    (binding : Bap.Var × Nat) (hb : binding ∈ layout) (hi : binding.1 ∈ inputs) : ∃ value, Bil.lookup env binding.1 = .ok value := by
  induction layout generalizing init with
  | nil => simp at hb
  | cons head rest ih =>
    simp only [List.foldlM_cons] at h
    obtain ⟨mid, h1, h2⟩ := bind_ok h
    rcases List.mem_cons.1 hb with rfl | hb
    · cases hl : Bil.lookup env binding.1 with
      | ok value => exact ⟨value, rfl⟩
      | error e =>
        simp only [hl] at h1
        simp [hi] at h1
    · exact ih _ h2 hb

/-- An input with a slot has bits at the width of its variable, if the encoding of a state went through. -/
private theorem encodeState_good {lowering : Lowering} {env : Bil.Env} {slots : Array UInt64} {var : Bap.Var} (wf : LayoutWF lowering)
    (h : encodeState lowering env = .ok slots) (hi : var ∈ Lowering.inputs lowering) (hb : ∃ binding ∈ Lowering.layout lowering, binding.1 = var) :
    Good env var := by
  obtain ⟨binding, hb, rfl⟩ := hb
  obtain ⟨value, hvalue⟩ := encode_bound env (Lowering.inputs lowering) (Lowering.layout lowering) _ slots h binding hb hi
  obtain ⟨w, bits, rfl, hw, _⟩ := encodeState_holds wf h binding hb _ hvalue
  exact ⟨w, hw, bits, hvalue⟩

/-- What the encoding of a state gives to the slots. -/
private theorem encodeState_slots {lowering : Lowering} {env : Bil.Env} {slots : Array UInt64} (wf : LayoutWF lowering)
    (h : encodeState lowering env = .ok slots) :
    slots.size = Lowering.nextSlot lowering ∧ ∀ index, (∀ binding ∈ Lowering.layout lowering, binding.2 ≠ index) → slots.getD index 0 = 0 := by
  obtain ⟨h1, _, h3⟩ := encode_fold env (Lowering.inputs lowering) (Lowering.layout lowering) _ slots
    (fun b hm => by simpa using wf.bound b hm) wf.slotsDistinct h
  refine ⟨by simpa using h1, fun index hi => ?_⟩
  rw [h3 index hi]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> simp

/-- A slot of `withControl`. -/
private theorem withControl_other {lowering : Lowering} {slots : Array UInt64} {budget : Nat} {observed : Bool} {index : Nat}
    (h1 : ∀ slot, Lowering.budget lowering = some slot → slot ≠ index) (h2 : ∀ slot, Lowering.observed lowering = some slot → slot ≠ index) :
    (withControl lowering slots budget observed).getD index 0 = slots.getD index 0 := by
  unfold withControl
  have hset : ∀ (a : Array UInt64) (slot : Nat) (value : UInt64), slot ≠ index → (a.set! slot value).getD index 0 = a.getD index 0 := by
    intro a slot value hne
    simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, hne]
  dsimp only
  cases hb : Lowering.budget lowering with
  | none =>
    cases ho : Lowering.observed lowering with
    | none => rfl
    | some o => exact hset _ _ _ (h2 o ho)
  | some b =>
    cases ho : Lowering.observed lowering with
    | none => exact hset _ _ _ (h1 b hb)
    | some o => rw [hset _ _ _ (h2 o ho)]; exact hset _ _ _ (h1 b hb)

private theorem stepBlocks_first {blocks : List Block} {fuel count : Nat} {state : Bil.State} {block : Block} {result : Bil.State × Nat}
    (h : stepBlocks blocks fuel (count + 1) (state, block.address) = .ok result) (hat : blockAt blocks block.address = some block) :
    ∃ first, Bil.execProgram fuel state block.program = .ok first ∧ stepBlocks blocks fuel count (first.1, nextPc block first.2) = .ok result := by
  simp only [stepBlocks, stepBlock, hat] at h
  cases he : Bil.execProgram fuel state block.program with
  | error error => simp [he] at h
  | ok first =>
    simp only [he] at h
    exact ⟨first, rfl, h⟩

/-- **A compiled range does what its blocks do, one at a time in the interpreter.**

From the slots of `encodeState` and `withControl` with any budget, and any code observer `stops`, with a machine that holds them and the
memory of the state, the program that `lowerGraph` makes for a graph has one of three ends. A loop in it uses up its iterations, which the
runner turns into an error and which takes more fuel than the interpreter runs with (`lowerGraph_interpreterFuel`), or the interpreter has no fuel within the budget, the one thing that can stop it (`graph_progress`), or the run returns. Then it has
entered `entered` blocks after its first, what `budget` minus its budget slot says, at most `budget`. It returns the pc where the interpreter
goes on after `entered + 1` blocks, whichever way it left: over an edge with no budget left (that block not entered), at a code site that stopped it
(likewise, with 3 in the effect slot), at an edge to a block that is not in the range, or at a jump out of a block's statements. Variables other than
the memory then read in `syncState` what the interpreter has for them, whether their flags say they were written or not, and the machine holds the
memory of the interpreter. Native code does this on the terms of `Bap.Jit`, and `nextCfgAt` is those terms for code sites. -/
theorem lowerGraph_correct {blocks : List Block} {edges : List (Nat × Nat)} {wrapFaults : Bool} {lowering : Lowering}
    (h : lowerGraph blocks edges wrapFaults = some lowering) (hedges : edges ≠ []) (stops : Nat → Bool) (fuel budget : Nat) (observed : Bool)
    (hbudget : budget < 2 ^ 64) (state : Bil.State) {slots : Array UInt64} (machine : Machine)
    (henc : encodeState lowering state.env = .ok slots)
    (hslots : ∀ index, machine.slots index = ((withControl lowering slots budget observed).getD index 0).toBitVec)
    (hmem : ∀ var, Lowering.memory lowering = some var → ∀ (width : Nat) (cells : Bap.Memory width),
      Bil.lookup state.env var = .ok (.memory cells) → MemoryInv machine width cells)
    (hbound : ∀ var, Lowering.memory lowering = some var → GoodMem state.env var) :
    Lowering.effectSlot lowering = some 0 ∧ Lowering.budget lowering = some 1 ∧ Lowering.observed lowering = some 2 ∧
    ∃ seed rest, blocks = seed :: rest ∧
    (OutOfFuel blocks fuel budget (state, seed.address) ∨
      (loopLimit + 1 ≤ fuel ∧ ExhaustsAt stops (Lowering.ops lowering) (Lowering.ops lowering, machine) 0) ∨
      ∃ entered, entered ≤ budget ∧ ∃ final pc m, stepBlocks blocks fuel (entered + 1) (state, seed.address) = .ok (final, pc) ∧
        EndsAt stops (Lowering.ops lowering) (Lowering.ops lowering, machine) pc m ∧
        (m.slots 1).toNat = budget - entered ∧
        (m.slots 0 = 0 ∨ m.slots 0 = 1 ∨ (m.slots 0 = (3 : UInt64).toBitVec ∧ stops pc = true)) ∧
        (∀ out : Array UInt64, (∀ index, index < Lowering.nextSlot lowering → (out.getD index 0).toBitVec = m.slots index) →
          ∀ var, Lowering.memory lowering ≠ some var → Bil.lookup (syncState lowering state out).env var = Bil.lookup final.env var) ∧
        (∀ var, Lowering.memory lowering = some var → ∀ (width : Nat) (cells : Bap.Memory width),
          Bil.lookup final.env var = .ok (.memory cells) → MemoryInv m width cells)) := by
  obtain ⟨seed, rest, plan, initial, inner, hblocks, hl, hlower, hcheck, hplanEdges, hplanSeed, hplanLabels, hiops, hilayout, hieff, hinext, _, hichained, hdefinite, hplanChained, _⟩ :=
    lowerGraph_parts h
  obtain ⟨hpb, hin3, hib, hio⟩ := hichained hedges
  obtain ⟨fops, fflags, fnext, flayout, foutputs, fmemory, feffect, fbudget, fobserved, finputs⟩ := flagOutputs_parts (leadingMoves seed.program) inner
  rw [← hl] at fops fflags fnext flayout foutputs fmemory feffect fbudget fobserved finputs
  have chk := checked_of hcheck
  have wfi : LayoutWF initial := layoutWF_of_nil _ hilayout
  have hedgesP : GraphPlan.edges plan ≠ [] := by rw [hplanEdges]; exact hedges
  obtain ⟨new, g, ok⟩ := lowerBlocks_spec (effect := 0) (plan := plan) blocks wfi hieff hinext (fun b hb => (chk.fits b hb).2)
    (fun _ => by rw [hpb]; decide) hlower
  have hprog : Lowering.ops inner = .set 0 0 :: new := by rw [g.ops, hiops]; rfl
  have hsmall : ∀ slot, slot < 3 → ∀ var, (var, slot) ∉ Lowering.layout inner := by
    intro slot hs var hm
    rcases g.later _ hm with hm' | hm'
    · rw [hilayout] at hm'
      simp at hm'
    · simp only at hm'
      omega
  have place : Place initial inner inner new (Lowering.ops inner) [] 0 := {
    effectFree := hsmall 0 (by decide)
    wfGlobal := g.wf
    sub := Sub.refl inner
    split := ⟨[.set 0 0], by rw [hprog]; simp⟩
    distinct := chk.labels }
  obtain ⟨all, seedFact⟩ := ok stops inner (Lowering.ops inner) [] place
  obtain ⟨start, seg, hrunSeed⟩ := seedFact seed rest hblocks hplanSeed.symm
  subst hblocks
  have hseedMem : seed ∈ seed :: rest := List.mem_cons_self
  have hat := blockAt_of_mem chk.addresses hseedMem
  -- the machines
  obtain ⟨hflagNext, hflagLow, hflagDistinct, _, hflagKeys⟩ := flagSlots_spec
    ((Lowering.outputs inner).filter fun output => !(leadingMoves seed.program).contains output.1)
    (limit := Lowering.nextSlot inner) (start := Lowering.nextSlot inner) (init := []) (next := (flagSlots _ _).1) (flags := (flagSlots _ _).2)
    rfl (Nat.le_refl _) (by simp) (by simp)
  have wfL : LayoutWF lowering := ⟨fun b hb => by
      rw [flayout] at hb
      rw [fnext]
      exact Nat.lt_of_lt_of_le (g.wf.bound b hb) hflagNext,
    by rw [flayout]; exact g.wf.slotsDistinct, by rw [flayout]; exact g.wf.varsDistinct⟩
  obtain ⟨_, hzero⟩ := encodeState_slots wfL henc
  have hb1 : Lowering.budget lowering = some 1 := by rw [fbudget, chk.budget]; exact hib
  have ho1 : Lowering.observed lowering = some 2 := by rw [fobserved, chk.observed]; exact hio
  have hN : 3 ≤ Lowering.nextSlot inner := by have := g.next; omega
  have hsize : slots.size = Lowering.nextSlot lowering := (encodeState_slots wfL henc).1
  have hN' : 3 ≤ Lowering.nextSlot lowering := by rw [fnext]; omega
  have hhigh : ∀ index, 3 ≤ index → machine.slots index = (slots.getD index 0).toBitVec := by
    intro index hi
    rw [hslots, withControl_other (by intro s hs; rw [hb1] at hs; simp only [Option.some.injEq] at hs; omega)
      (by intro s hs; rw [ho1] at hs; simp only [Option.some.injEq] at hs; omega)]
  have hbudgetSlot : (machine.slots 1).toNat = budget := by
    rw [hslots]
    simp only [withControl, hb1, ho1]
    have h1 : 1 < slots.size := by omega
    have : ((slots.set! 1 (UInt64.ofNat budget)).set! 2 (if observed = true then 1 else 0)).getD 1 0 = UInt64.ofNat budget := by
      simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, h1]
    rw [this]
    show (UInt64.ofNat budget).toNat = budget
    simp only [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt hbudget
  let flags := Lowering.flags lowering
  have hfl : ∀ f ∈ flags, Lowering.nextSlot inner ≤ f.2 := fun f hf => (hflagLow f (by rw [← fflags]; exact hf)).1
  have hfd : flags.Pairwise fun a b => a.2 ≠ b.2 := by simp only [flags, fflags]; exact hflagDistinct
  let m0 : Machine := { slots := machine.slots, memory := machine.memory, view := machine.view, moved := fun _ => false, origin := state.env }
  have hrel0 : FlagRel (Lowering.nextSlot inner) flags m0 machine := by
    refine ⟨fun _ _ => rfl, rfl, rfl, fun slot f hf => ?_⟩
    have hlow := hfl f (List.mem_of_find?_eq_some hf)
    have hz : machine.slots f.2 = 0 := by
      rw [hhigh _ (by omega), hzero]
      · rfl
      · intro b hb he
        rw [flayout] at hb
        have := g.wf.bound b hb
        omega
    simp [hz, m0]
  have hag0 : Agrees state.env m0 inner := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro binding hb value hv
      obtain ⟨w, bits, h1, h2, h3⟩ := encodeState_holds wfL henc binding (by rw [flayout]; exact hb) value hv
      refine ⟨w, bits, h1, h2, ?_⟩
      have hge : 3 ≤ binding.2 := by
        refine Classical.byContradiction fun hlt => ?_
        exact hsmall binding.2 (by omega) binding.1 hb
      show Holds (machine.slots binding.2) bits
      rw [hhigh _ hge]
      exact h3
    · intro var hv w cells hl
      exact hmem var (by rw [fmemory]; exact hv) w cells hl
    · intro var hne
      exact absurd rfl hne
    · intro binding _ hm
      simp [m0] at hm
  have hag1 := hag0.write_free (hsmall 0 (by decide)) (0 : UInt64).toBitVec
  have hz1 : (m0.write 0 (0 : UInt64).toBitVec).slots 0 = 0 := by
    simp only [Machine.write_slots, ↓reduceIte]
    rfl
  have hb1' : ((m0.write 0 (0 : UInt64).toBitVec).slots 1).toNat = budget := by
    simpa [Machine.write_slots, m0] using hbudgetSlot
  have hstart : RunAt stops (Lowering.ops inner) (Lowering.ops inner, m0) (start, m0.write 0 (0 : UInt64).toBitVec) := by
    have h1 := hrunSeed (m0.write 0 (0 : UInt64).toBitVec)
    rw [List.append_nil] at h1
    refine RunAt.trans ?_ h1
    conv => lhs; rw [hprog]
    exact (Run.linear (program := Lowering.ops inner) (op := .set 0 0) rfl new m0).toAt
  have hlabel : ∀ source target label, EdgeTo plan source target label → ∃ block ∈ seed :: rest, block.address = target ∧
      blockAt (seed :: rest) target = some block ∧ ∃ address, (GraphPlan.labels plan).find? (fun (address, _) => address = block.address) = some (address, label) := by
    intro source target label ⟨_, address, hfind⟩
    rw [hplanLabels] at hfind
    obtain ⟨block, hmemB, haddr⟩ := labels_block hfind
    subst haddr
    exact ⟨block, hmemB, rfl, blockAt_of_mem chk.addresses hmemB, address, by rw [hplanLabels]; exact hfind⟩
  have hin3' : GraphPlan.budget plan < Lowering.nextSlot initial := by rw [hpb, hin3]; decide
  have hchained : GraphPlan.chained plan = true := by
    rw [hplanChained]
    cases edges with
    | nil => exact absurd rfl hedges
    | cons _ _ => rfl
  have hinputs : ∀ var ∈ Lowering.inputs inner, Good state.env var := by
    intro var hv
    exact encodeState_good wfL henc (by rw [finputs]; exact hv) (by rw [flayout]; exact chk.inputs var hv)
  have core := range_core all hlabel (fun b hb => (chk.fits b hb).1) (hsmall 0 (by decide))
    (by rw [hpb]; exact hsmall 1 (by decide)) (fun _ => by rw [hpb]; decide) hin3' hinext fuel budget
    (GraphReady seed.address (seed :: rest) edges inner)
    (fun block hb state ready => by
      rw [hplanEdges]
      exact graph_progress hlower hchained hdefinite chk.addresses hb fuel state ready)
    hedgesP
    seed hseedMem hat start seg state _ hag1 hz1 (by rw [hpb]; exact hb1')
    (graphReady_seed _ _ _ hinputs (fun var hv => hbound var (by rw [fmemory]; exact hv)))
  have hm0 : ∀ slot, m0.moved slot = true → ∃ src, Op.move slot src ∈ Lowering.ops inner := by
    intro slot hs
    simp [m0] at hs
  have hin0 : ∀ op ∈ Lowering.ops inner, op ∈ Lowering.ops inner := fun _ h => h
  have hops : Lowering.ops lowering = flagOps flags (Lowering.ops inner) := by simp only [flags, fflags]; exact fops
  refine ⟨by rw [feffect, g.effect]; exact hieff, hb1, ho1, seed, rest, rfl, ?_⟩
  rw [hops]
  rcases core with hfail | hx | ⟨entered, hle, final, pc, m, hsteps, hend, hagF, hbudF, heffF⟩
  · exact Or.inl hfail
  · obtain ⟨hcap, target, r, mx, hr, h2⟩ := And.intro hx.1 (hx.2.prepend hstart)
    obtain ⟨hin, m', hrun, hr2⟩ := hr.withFlags hfl hfd chk.slots hin0 machine hrel0
    refine Or.inr (Or.inl ⟨hcap, target, flagOps flags r, m', hrun, ?_⟩)
    rw [hr2.slots 0 (by omega)]
    exact h2
  · obtain ⟨m', hend', hrel, horigin, hmoved⟩ := (hend.prepend hstart).withFlags hfl hfd chk.slots hrel0 hm0
    rw [hpb] at hbudF
    refine Or.inr (Or.inr ⟨entered, hle, final, pc, m', hsteps, hend', ?_, ?_, ?_, ?_⟩)
    · rw [hrel.slots 1 (by omega)]
      exact hbudF
    · rw [hrel.slots 0 (by omega)]
      exact heffF
    · intro out hout var hvar
      refine syncState_flags (global := inner) (m := m) (m' := m') ?_ hagF flayout.symm wfL ?_ hrel ?_ ?_ ?_ ?_ ?_ hout (by rw [← fmemory]; exact hvar)
      · intro output ho hfind
        by_cases hlead : output.1 ∈ leadingMoves seed.program
        · obtain ⟨res, hexec, hrest⟩ := stepBlocks_first hsteps hat
          have hb := leadingMoves_bound seed.program hlead hexec
          exact stepBlocks_stays_bound entered hrest hb
        · exfalso
          rw [foutputs] at ho
          have hf : output ∈ (Lowering.outputs inner).filter fun output => !(leadingMoves seed.program).contains output.1 := by
            refine List.mem_filter.2 ⟨ho, ?_⟩
            simpa using hlead
          obtain ⟨f, hfm, hfk⟩ := hflagKeys output hf
          have hne := (List.find?_eq_none.1 hfind) f (by rw [fflags]; exact hfm)
          simp [hfk] at hne
      · intro output ho
        rw [flayout]
        rw [foutputs] at ho
        exact chk.outputs output ho
      · rw [fnext]; exact hflagNext
      · intro b hb
        rw [flayout] at hb
        exact g.wf.bound b hb
      · intro f hf
        rw [fnext]
        exact (hflagLow f (by rw [← fflags]; exact hf)).2
      · exact horigin
      · intro binding hb hmv
        obtain ⟨src, hsrc⟩ := hmoved binding.2 hmv
        rw [foutputs]
        rw [flayout] at hb
        exact chk.moves _ src hsrc binding hb rfl
    · intro var hv w cells hl
      obtain ⟨h1, h2, h3, h4, h5⟩ := hagF.memory var (by rw [← fmemory]; exact hv) w cells hl
      refine ⟨h1, h2, h3, ?_, ?_⟩
      · intro address
        rw [hrel.view]
        exact h4 address
      · rw [WindowOf, hrel.memory]
        exact h5

/-- The pc of a stop changes nothing in what is written back of a range: all of its stops see all of its outputs, with their flags. -/
theorem atCodeStop_flagOutputs (written : List Bap.Var) (final : Lowering) (pc : Nat) :
    atCodeStop (flagOutputs written final) pc = flagOutputs written final := by
  unfold atCodeStop
  split
  · next checkpoint hfind =>
    have hmem := List.mem_of_find?_eq_some hfind
    have : checkpoint.2 = Lowering.outputs final := by
      obtain ⟨c, _, he⟩ := List.mem_map.1 hmem
      rw [← he]
    rw [this]
    rfl
  · rfl

/-- **The limit of native loops and the fuel of the interpreter are one bound.** On the fuel that the interpreter is given (`Bil.runObserved`, or
any less), a compiled range never gives up on a loop before the interpreter would: the end of `lowerGraph_correct` with a loop out of iterations is gone.
A loop runs out of iterations at its 100000th test, the last that `execProgram 100000` can get to, so that the bound is exact. With more fuel, the
interpreter goes on where native code reports an error: both fail, or neither, and with the same state. -/
theorem lowerGraph_interpreterFuel {blocks : List Block} {edges : List (Nat × Nat)} {wrapFaults : Bool} {lowering : Lowering}
    (h : lowerGraph blocks edges wrapFaults = some lowering) (hedges : edges ≠ []) (stops : Nat → Bool) {fuel : Nat} (hfuel : fuel ≤ loopLimit) (budget : Nat)
    (observed : Bool) (hbudget : budget < 2 ^ 64) (state : Bil.State) {slots : Array UInt64} (machine : Machine)
    (henc : encodeState lowering state.env = .ok slots)
    (hslots : ∀ index, machine.slots index = ((withControl lowering slots budget observed).getD index 0).toBitVec)
    (hmem : ∀ var, Lowering.memory lowering = some var → ∀ (width : Nat) (cells : Bap.Memory width),
      Bil.lookup state.env var = .ok (.memory cells) → MemoryInv machine width cells)
    (hbound : ∀ var, Lowering.memory lowering = some var → GoodMem state.env var) :
    ∃ seed rest, blocks = seed :: rest ∧
    (OutOfFuel blocks fuel budget (state, seed.address) ∨
      ∃ entered, entered ≤ budget ∧ ∃ final pc m, stepBlocks blocks fuel (entered + 1) (state, seed.address) = .ok (final, pc) ∧
        EndsAt stops (Lowering.ops lowering) (Lowering.ops lowering, machine) pc m ∧
        (m.slots 1).toNat = budget - entered ∧
        (m.slots 0 = 0 ∨ m.slots 0 = 1 ∨ (m.slots 0 = (3 : UInt64).toBitVec ∧ stops pc = true)) ∧
        (∀ out : Array UInt64, (∀ index, index < Lowering.nextSlot lowering → (out.getD index 0).toBitVec = m.slots index) →
          ∀ var, Lowering.memory lowering ≠ some var → Bil.lookup (syncState lowering state out).env var = Bil.lookup final.env var) ∧
        (∀ var, Lowering.memory lowering = some var → ∀ (width : Nat) (cells : Bap.Memory width),
          Bil.lookup final.env var = .ok (.memory cells) → MemoryInv m width cells)) := by
  obtain ⟨_, _, _, seed, rest, hb, hcases⟩ := lowerGraph_correct h hedges stops fuel budget observed hbudget state machine henc hslots hmem hbound
  refine ⟨seed, rest, hb, ?_⟩
  rcases hcases with hout | hx | hends
  · exact Or.inl hout
  · have := hx.1
    omega
  · exact Or.inr hends

/-- **No input that is not bound reaches native code as a 0.** `encodeState` fails on it, and the runner runs the interpreter instead. A variable that
is not an input and has no value has a 0 in its slot, which nothing reads before writing it (`lowerGraph_correct`). This is why a read in a later block
of what an earlier block only writes after a statement that can leave, which `programWrites` does not count, is at worst slower. -/
theorem encodeState_input_unbound {lowering : Lowering} {env : Bil.Env} {var : Bap.Var} {error : String}
    (hi : var ∈ Lowering.inputs lowering) (hb : ∃ binding ∈ Lowering.layout lowering, binding.1 = var) (hl : Bil.lookup env var = .error error) :
    ∃ reason, encodeState lowering env = .error reason := by
  cases he : encodeState lowering env with
  | error reason => exact ⟨reason, rfl⟩
  | ok slots =>
    obtain ⟨binding, hb, rfl⟩ := hb
    obtain ⟨value, hv⟩ := encode_bound env (Lowering.inputs lowering) (Lowering.layout lowering) _ slots he binding hb hi
    rw [hl] at hv
    cases hv

/-- A range counts what it entered, which is what `lowerGraph_correct` says of its budget slot. -/
theorem chainedCount_entered {lowering : Lowering} {budget entered budgetSlot : Nat} {slots : Array UInt64}
    (hb : Lowering.budget lowering = some budgetSlot) (hs : ((slots.getD budgetSlot 0).toBitVec).toNat = budget - entered) (hle : entered ≤ budget) :
    chainedCount lowering budget slots = some entered := by
  have hs' : (slots.getD budgetSlot 0).toNat = budget - entered := hs
  simp only [chainedCount, hb, Option.map_some, Option.some.injEq]
  omega

/-- What is left of a run is what `EndsAt` says: 1 in the effect slot is a jump to the pc, 2 the error of an exhausted loop, and any other effect goes
on at the pc with a normal effect. -/
theorem nativeOutcome_jump {lowering : Lowering} {following next : Nat} {state : Bil.State} {slots : Array UInt64} {slot : Nat}
    (he : Lowering.effectSlot lowering = some slot) (h : slots.getD slot 0 = 1) :
    nativeOutcome lowering following next state slots = .ok ⟨state, next, following, .jump (BitVec.ofNat 64 next)⟩ := by
  simp [nativeOutcome, he, h]

theorem nativeOutcome_exhausted {lowering : Lowering} {following next : Nat} {state : Bil.State} {slots : Array UInt64} {slot : Nat}
    (he : Lowering.effectSlot lowering = some slot) (h : slots.getD slot 0 = 2) :
    nativeOutcome lowering following next state slots = .error "Primus loop fuel exhausted" := by
  simp [nativeOutcome, he, h]

theorem nativeOutcome_normal {lowering : Lowering} {following next : Nat} {state : Bil.State} {slots : Array UInt64} {slot : Nat}
    (he : Lowering.effectSlot lowering = some slot) (h1 : slots.getD slot 0 ≠ 1) (h2 : slots.getD slot 0 ≠ 2) :
    nativeOutcome lowering following next state slots = .ok ⟨state, next, next, .normal⟩ := by
  simp only [nativeOutcome, he, beq_iff_eq, h1, h2, ↓reduceIte]

/-- **A block that compiled has a result in the interpreter, or has no fuel**, on a state that it encodes with its memory bound. So `lowerGraph_single`,
which is about what has a result, leaves out no other error. -/
theorem lowerGraph_single_progress {blocks : List Block} {wrapFaults : Bool} {lowering : Lowering}
    (h : lowerGraph blocks [] wrapFaults = some lowering) (fuel : Nat) (state : Bil.State) {slots : Array UInt64}
    (henc : encodeState lowering state.env = .ok slots) (hbound : ∀ var, Lowering.memory lowering = some var → GoodMem state.env var) :
    ∃ seed rest, blocks = seed :: rest ∧ (Bil.execProgram fuel state seed.program = .error fuelError ∨ ∃ result, Bil.execProgram fuel state seed.program = .ok result) := by
  obtain ⟨seed, rest, plan, initial, inner, hblocks, hl, hlower, hcheck, hplanEdges, _, _, _, hilayout, hieff, hinext, _, _, _, hplanChained, hiw⟩ :=
    lowerGraph_parts h
  obtain ⟨_, _, fnext, flayout, _, fmemory, _, _, _, finputs⟩ := flagOutputs_parts (leadingMoves seed.program) inner
  rw [← hl] at fnext flayout fmemory finputs
  have chk := checked_of hcheck
  have wfi : LayoutWF initial := layoutWF_of_nil _ hilayout
  obtain ⟨new, g, _⟩ := lowerBlocks_spec (effect := 0) (plan := plan) blocks wfi hieff hinext (fun b hb => (chk.fits b hb).2)
    (fun he => absurd hplanEdges he) hlower
  obtain ⟨hflagNext, _⟩ := flagSlots_spec
    ((Lowering.outputs inner).filter fun output => !(leadingMoves seed.program).contains output.1)
    (limit := Lowering.nextSlot inner) (start := Lowering.nextSlot inner) (init := []) (next := (flagSlots _ _).1) (flags := (flagSlots _ _).2)
    rfl (Nat.le_refl _) (by simp) (by simp)
  have wfL : LayoutWF lowering := ⟨fun b hb => by
      rw [flayout] at hb
      rw [fnext]
      exact Nat.lt_of_lt_of_le (g.wf.bound b hb) hflagNext,
    by rw [flayout]; exact g.wf.slotsDistinct, by rw [flayout]; exact g.wf.varsDistinct⟩
  subst hblocks
  simp only [lowerBlocks] at hlower
  obtain ⟨mid, h1, h2⟩ := obind hlower
  obtain ⟨m1, ok⟩ := lowerBlock_progress h1
  obtain ⟨m2, _⟩ := lowerBlocks_progress rest h2
  refine ⟨seed, rest, rfl, ?_⟩
  have hw : ∀ var ∈ Lowering.written (if GraphPlan.chained plan = true then Lowering.withWritten initial (GraphPlan.definite plan seed.address) else initial), Good state.env var := by
    rw [hplanChained]
    simp [hiw]
  rcases ok fuel state hw
    (fun var hv => encodeState_good wfL henc (by rw [finputs]; exact m2.inputs var hv) (by rw [flayout]; exact chk.inputs var (m2.inputs var hv)))
    (fun var hv => hbound var (by rw [fmemory]; exact m2.memory var hv)) with he | ⟨result, he, _⟩
  · exact Or.inl he
  · exact Or.inr ⟨result, he⟩

/-- **A compiled block does what the interpreter does**, as `lowerGraph_correct` says for a range, for a block on its own, which has no budget and no
code sites: a jump out of it with an output not written yet leaves that output as it was. -/
theorem lowerGraph_single {blocks : List Block} {wrapFaults : Bool} {lowering : Lowering}
    (h : lowerGraph blocks [] wrapFaults = some lowering) (stops : Nat → Bool) (fuel : Nat) (state : Bil.State) {slots : Array UInt64} (machine : Machine)
    (henc : encodeState lowering state.env = .ok slots)
    (hslots : ∀ index, machine.slots index = (slots.getD index 0).toBitVec)
    (hmem : ∀ var, Lowering.memory lowering = some var → ∀ (width : Nat) (cells : Bap.Memory width),
      Bil.lookup state.env var = .ok (.memory cells) → MemoryInv machine width cells) :
    Lowering.effectSlot lowering = some 0 ∧ ∃ seed rest, blocks = seed :: rest ∧ ∀ result, Bil.execProgram fuel state seed.program = .ok result →
      (loopLimit + 1 ≤ fuel ∧ ExhaustsAt stops (Lowering.ops lowering) (Lowering.ops lowering, machine) 0) ∨
      ∃ m, EndsAt stops (Lowering.ops lowering) (Lowering.ops lowering, machine) (nextPc seed result.2) m ∧
        (m.slots 0 = 0 ∨ m.slots 0 = 1) ∧
        (∀ out : Array UInt64, (∀ index, index < Lowering.nextSlot lowering → (out.getD index 0).toBitVec = m.slots index) →
          ∀ var, Lowering.memory lowering ≠ some var → Bil.lookup (syncState lowering state out).env var = Bil.lookup result.1.env var) ∧
        (∀ var, Lowering.memory lowering = some var → ∀ (width : Nat) (cells : Bap.Memory width),
          Bil.lookup result.1.env var = .ok (.memory cells) → MemoryInv m width cells) := by
  obtain ⟨seed, rest, plan, initial, inner, hblocks, hl, hlower, hcheck, hplanEdges, hplanSeed, _, hiops, hilayout, hieff, hinext, _, _, _, _, _⟩ :=
    lowerGraph_parts h
  obtain ⟨fops, fflags, fnext, flayout, foutputs, fmemory, feffect, _, _, _⟩ := flagOutputs_parts (leadingMoves seed.program) inner
  rw [← hl] at fops fflags fnext flayout foutputs fmemory feffect
  have chk := checked_of hcheck
  have wfi : LayoutWF initial := layoutWF_of_nil _ hilayout
  obtain ⟨new, g, ok⟩ := lowerBlocks_spec (effect := 0) (plan := plan) blocks wfi hieff hinext (fun b hb => (chk.fits b hb).2)
    (fun he => absurd hplanEdges he) hlower
  have hprog : Lowering.ops inner = .set 0 0 :: new := by rw [g.ops, hiops]; rfl
  have hsmall : ∀ var, (var, 0) ∉ Lowering.layout inner := by
    intro var hm
    rcases g.later _ hm with hm' | hm'
    · rw [hilayout] at hm'
      simp at hm'
    · simp only at hm'
      omega
  have place : Place initial inner inner new (Lowering.ops inner) [] 0 := {
    effectFree := hsmall
    wfGlobal := g.wf
    sub := Sub.refl inner
    split := ⟨[.set 0 0], by rw [hprog]; simp⟩
    distinct := chk.labels }
  obtain ⟨_, seedFact⟩ := ok stops inner (Lowering.ops inner) [] place
  obtain ⟨start, seg, hrunSeed⟩ := seedFact seed rest hblocks hplanSeed.symm
  subst hblocks
  obtain ⟨hflagNext, hflagLow, hflagDistinct, _, hflagKeys⟩ := flagSlots_spec
    ((Lowering.outputs inner).filter fun output => !(leadingMoves seed.program).contains output.1)
    (limit := Lowering.nextSlot inner) (start := Lowering.nextSlot inner) (init := []) (next := (flagSlots _ _).1) (flags := (flagSlots _ _).2)
    rfl (Nat.le_refl _) (by simp) (by simp)
  have wfL : LayoutWF lowering := ⟨fun b hb => by
      rw [flayout] at hb
      rw [fnext]
      exact Nat.lt_of_lt_of_le (g.wf.bound b hb) hflagNext,
    by rw [flayout]; exact g.wf.slotsDistinct, by rw [flayout]; exact g.wf.varsDistinct⟩
  obtain ⟨_, hzero⟩ := encodeState_slots wfL henc
  have hN : 0 < Lowering.nextSlot inner := by have := g.next; omega
  let flags := Lowering.flags lowering
  have hfl : ∀ f ∈ flags, Lowering.nextSlot inner ≤ f.2 := fun f hf => (hflagLow f (by rw [← fflags]; exact hf)).1
  have hfd : flags.Pairwise fun a b => a.2 ≠ b.2 := by simp only [flags, fflags]; exact hflagDistinct
  let m0 : Machine := { slots := machine.slots, memory := machine.memory, view := machine.view, moved := fun _ => false, origin := state.env }
  have hrel0 : FlagRel (Lowering.nextSlot inner) flags m0 machine := by
    refine ⟨fun _ _ => rfl, rfl, rfl, fun slot f hf => ?_⟩
    have hlow := hfl f (List.mem_of_find?_eq_some hf)
    have hz : machine.slots f.2 = 0 := by
      rw [hslots, hzero]
      · rfl
      · intro b hb he
        rw [flayout] at hb
        have := g.wf.bound b hb
        omega
    simp [hz, m0]
  have hag0 : Agrees state.env m0 inner := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro binding hb value hv
      obtain ⟨w, bits, h1, h2, h3⟩ := encodeState_holds wfL henc binding (by rw [flayout]; exact hb) value hv
      refine ⟨w, bits, h1, h2, ?_⟩
      show Holds (machine.slots binding.2) bits
      rw [hslots]
      exact h3
    · intro var hv w cells hl
      exact hmem var (by rw [fmemory]; exact hv) w cells hl
    · intro var hne
      exact absurd rfl hne
    · intro binding _ hm
      simp [m0] at hm
  have hag1 := hag0.write_free hsmall (0 : UInt64).toBitVec
  have hz1 : (m0.write 0 (0 : UInt64).toBitVec).slots 0 = 0 := by
    simp only [Machine.write_slots, ↓reduceIte]
    rfl
  have hstart : RunAt stops (Lowering.ops inner) (Lowering.ops inner, m0) (start, m0.write 0 (0 : UInt64).toBitVec) := by
    have h1 := hrunSeed (m0.write 0 (0 : UInt64).toBitVec)
    rw [List.append_nil] at h1
    refine RunAt.trans ?_ h1
    conv => lhs; rw [hprog]
    exact (Run.linear (program := Lowering.ops inner) (op := .set 0 0) rfl new m0).toAt
  have hm0 : ∀ slot, m0.moved slot = true → ∃ src, Op.move slot src ∈ Lowering.ops inner := by
    intro slot hs
    simp [m0] at hs
  have hin0 : ∀ op ∈ Lowering.ops inner, op ∈ Lowering.ops inner := fun _ h => h
  have hops : Lowering.ops lowering = flagOps flags (Lowering.ops inner) := by simp only [flags, fflags]; exact fops
  refine ⟨by rw [feffect, g.effect]; exact hieff, seed, rest, rfl, fun result hexec => ?_⟩
  rw [hops]
  rcases seg.1 fuel state result _ hag1 hz1 hexec with hx | ⟨m, hend, hagF, _, heffF⟩ | ⟨_, _, _, _, hedge, _⟩
  · obtain ⟨hcap, target, r, mx, hr, h2⟩ := And.intro hx.1 (hx.2.prepend hstart)
    obtain ⟨hin, m', hrun, hr2⟩ := hr.withFlags hfl hfd chk.slots hin0 machine hrel0
    refine Or.inl ⟨hcap, target, flagOps flags r, m', hrun, ?_⟩
    rw [hr2.slots 0 hN]
    exact h2
  · obtain ⟨m', hend', hrel, horigin, hmoved⟩ := (hend.prepend hstart).withFlags hfl hfd chk.slots hrel0 hm0
    refine Or.inr ⟨m', hend', ?_, ?_, ?_⟩
    · rw [hrel.slots 0 hN]
      exact heffF
    · intro out hout var hvar
      refine syncState_flags (global := inner) (m := m) (m' := m') ?_ hagF flayout.symm wfL ?_ hrel ?_ ?_ ?_ ?_ ?_ hout (by rw [← fmemory]; exact hvar)
      · intro output ho hfind
        by_cases hlead : output.1 ∈ leadingMoves seed.program
        · exact leadingMoves_bound seed.program hlead hexec
        · exfalso
          rw [foutputs] at ho
          have hf : output ∈ (Lowering.outputs inner).filter fun output => !(leadingMoves seed.program).contains output.1 := by
            refine List.mem_filter.2 ⟨ho, ?_⟩
            simpa using hlead
          obtain ⟨f, hfm, hfk⟩ := hflagKeys output hf
          have hne := (List.find?_eq_none.1 hfind) f (by rw [fflags]; exact hfm)
          simp [hfk] at hne
      · intro output ho
        rw [flayout]
        rw [foutputs] at ho
        exact chk.outputs output ho
      · rw [fnext]; exact hflagNext
      · intro b hb
        rw [flayout] at hb
        exact g.wf.bound b hb
      · intro f hf
        rw [fnext]
        exact (hflagLow f (by rw [← fflags]; exact hf)).2
      · exact horigin
      · intro binding hb hmv
        obtain ⟨src, hsrc⟩ := hmoved binding.2 hmv
        rw [foutputs]
        rw [flayout] at hb
        exact chk.moves _ src hsrc binding hb rfl
    · intro var hv w cells hl
      obtain ⟨h1, h2, h3, h4, h5⟩ := hagF.memory var (by rw [← fmemory]; exact hv) w cells hl
      refine ⟨h1, h2, h3, ?_, ?_⟩
      · intro address
        rw [hrel.view]
        exact h4 address
      · rw [WindowOf, hrel.memory]
        exact h5
  · exfalso
    have := hedge.1
    rw [hplanEdges] at this
    simp at this

end Graph

end Bap.Proofs.Jit
