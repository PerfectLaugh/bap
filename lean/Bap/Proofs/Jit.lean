import Lean
import Bap.Primus.Lifted

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
  | .sdiv, l, r => if r = 0 then 2 ^ 64 - 1 else (l.sdiv r).toNat
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
  case sdiv => by_cases h : r = 0#64 <;> simp only [h, ↓reduceIte] <;> first | rfl | simp
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

end Bap.Proofs.Jit
