import Lean.Elab.Tactic.Basic
import Bap.Target.X86
import Bap.Target.AArch64
import Bap.Target.RISCV
import Bap.Target.PowerPC
import Bap.Target.MIPS
import Bap.Target.ARM32
import Bap.Target.Thumb
import Bap.Target.X8632
import Bap.Target.RISCV32
import Bap.Target.MIPS32
import Bap.Target.PowerPC32
import Bap.ABI

namespace Bap.Proofs.Target

open Bap.Target Bap.Target.LLVMLift
open Bap.Disasm (Insn Flow Disassembler)
open Bap.Primus.Semantics.Value (register)

private abbrev PValue := Bap.Primus.Semantics.Value
private abbrev Globals := Bap.Primus.Semantics.Globals

open Lean Elab Term in
/-- A private constant of `Bap.Target.LLVMLift`. -/
local elab "lift% " n:ident : term => do
  let n := n.getId.eraseMacroScopes
  return mkConst (mkPrivateNameCore `Bap.Target.LLVMLift (`Bap.Target.LLVMLift ++ n))

open Lean Elab Term in
/-- A private constant of `Bap.Primus.Semantics`. -/
local elab "primus% " n:ident : term => do
  let n := n.getId.eraseMacroScopes
  return mkConst (mkPrivateNameCore `Bap.Primus.Semantics (`Bap.Primus.Semantics ++ n))

open Lean Elab Tactic in
/-- Unfolds an abbreviation together with the private `LLVMLift` definition it names. -/
local elab "lift_unfold " n:ident : tactic => do
  evalTactic (← `(tactic| dsimp only [$n:ident]))
  let p := mkIdent (mkPrivateNameCore `Bap.Target.LLVMLift (`Bap.Target.LLVMLift ++ n.getId.eraseMacroScopes))
  evalTactic (← `(tactic| unfold $p:ident))

open Lean Elab Tactic in
/-- `simp` with the equations of private `LLVMLift` definitions. -/
local elab "lift_simp " "[" ns:ident,* "]" : tactic => do
  let ns := ns.getElems
  for n in ns do
    evalTactic (← `(tactic| try dsimp only [$n:ident]))
  let ps : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← ns.mapM fun n => do
    let p := mkIdent (mkPrivateNameCore `Bap.Target.LLVMLift (`Bap.Target.LLVMLift ++ n.getId.eraseMacroScopes))
    `(Lean.Parser.Tactic.simpLemma| $p:ident)
  evalTactic (← `(tactic| simp [$[$ps:simpLemma],*]))

open Lean Elab Tactic in
/-- Unfolds the private table of the low x86 registers in a hypothesis. -/
local elab "unfold_low" " at " h:ident : tactic => do
  let p := mkIdent (mkPrivateNameCore `Bap.Target.LLVMLift `Bap.Target.LLVMLift.x86LowRegister)
  evalTactic (← `(tactic| unfold $p:ident at $h:ident))

open Lean Elab Tactic in
/-- Unfolds the private high-byte rewrite of an expression. -/
local elab "unfold_high_exp" : tactic => do
  let p := mkIdent (mkPrivateNameCore `Bap.Target.LLVMLift `Bap.Target.LLVMLift.highBytesExp)
  evalTactic (← `(tactic| unfold $p:ident))

open Lean Elab Tactic in
/-- Rewrites by the unfolding equation of the private high-byte rewrite of a program. -/
local elab "unfold_resolve" : tactic => do
  let p := mkIdent (mkPrivateNameCore `Bap.Target.LLVMLift (`Bap.Target.LLVMLift.resolveHighBytes ++ `eq_def))
  evalTactic (← `(tactic| rw [$p:ident]))

private abbrev aarch64Register : String → PValue := lift% aarch64Register
private abbrev x86LowRegister : String → Option (String × Nat) := lift% x86LowRegister
private abbrev x86HighByteBase : String → Option String := lift% x86HighByteBase
private abbrev x8632HighByteBase : String → Option String := lift% x8632HighByteBase
private abbrev mipsCanonicalName : String → String := lift% mipsCanonicalName
private abbrev resolveHighBytes : (String → Option String) → Nat → Bil.Program → Bil.Program :=
  lift% resolveHighBytes
private abbrev highBytesExp : (String → Option String) → Nat → Bil.Exp → Bil.Exp := lift% highBytesExp
private abbrev x86Register : String → PValue := lift% x86Register
private abbrev x8632Register : String → PValue := lift% x8632Register
private abbrev riscvRegister : String → PValue := lift% riscvRegister
private abbrev riscv32Register : String → PValue := lift% riscv32Register
private abbrev powerpcRegister : String → PValue := lift% powerpcRegister
private abbrev powerpc32Register : String → PValue := lift% powerpc32Register
private abbrev mipsRegisterName : String → String := lift% mipsRegisterName
private abbrev mipsRegister : String → PValue := lift% mipsRegister
private abbrev mips32Register : String → PValue := lift% mips32Register
private abbrev arm32Register : String → PValue := lift% arm32Register
private abbrev aarch64Globals : Globals := lift% aarch64Globals
private abbrev x86Globals : Globals := lift% x86Globals
private abbrev x8632Globals : Globals := lift% x8632Globals
private abbrev riscvGlobals : Globals := lift% riscvGlobals
private abbrev riscv32Globals : Globals := lift% riscv32Globals
private abbrev powerpcGlobals : Globals := lift% powerpcGlobals
private abbrev powerpc32Globals : Globals := lift% powerpc32Globals
private abbrev mipsGlobals : Globals := lift% mipsGlobals
private abbrev mips32Globals : Globals := lift% mips32Globals
private abbrev arm32Globals : Globals := lift% arm32Globals
private abbrev flow : Nat → Flow := lift% flow
private abbrev directControl : Nat → Bool := lift% directControl
private abbrev riscvFlow : Nat → Nat → Flow := lift% riscvFlow
private abbrev arm32Flow : LLVM.Decoded → Flow := lift% arm32Flow
private abbrev powerpcMCTarget : Nat → Nat → List LLVM.MCOperand → Option Nat :=
  lift% powerpcMCTarget
private abbrev riscvIsJal : Nat → Bool := lift% riscvIsJal
private abbrev riscvMCTarget : Nat → Nat → Nat → List LLVM.MCOperand → Option Nat :=
  lift% riscvMCTarget
private abbrev aarch64MCTarget : Nat → Nat → List LLVM.MCOperand → Option Nat :=
  lift% aarch64MCTarget
private abbrev x86MCTarget : Primus.Semantics.Environment → Nat → Nat → List LLVM.MCOperand → Option Nat :=
  lift% x86MCTarget
private abbrev mipsTarget : Nat → LLVM.Decoded → Option Nat := lift% mipsTarget
private abbrev arm32Target : Nat → LLVM.Decoded → Option Nat := lift% arm32Target
private abbrev thumbTarget : Nat → LLVM.Decoded → Option Nat := lift% thumbTarget
private abbrev x86RelativeOpcodes : List String := lift% x86RelativeOpcodes
private abbrev arm32Operand : LLVM.Operand → PValue := lift% arm32Operand
private abbrev arm32Immediate : Int → PValue := lift% arm32Immediate
private abbrev immediate : String → Int → PValue := lift% immediate
private abbrev semanticsContext : Nat → Nat → Primus.Semantics.Context := lift% semanticsContext
private abbrev arm32Context : Nat → Nat → Primus.Semantics.Context := lift% arm32Context

/-! ## Control-flow classification -/

private theorem flow_eq (flags : Nat) :
    flow flags =
      if flags &&& 1 != 0 then .ret
      else if flags &&& 2 != 0 then .call
      else if flags &&& 32 != 0 then .conditionalJump
      else if flags &&& 16 != 0 then .indirectJump
      else if flags &&& 64 != 0 then .jump
      else if flags &&& 4 != 0 || flags &&& 512 != 0 then .barrier
      else .normal := rfl

/-- Complete specification of the flow classifier as a priority decision list. -/
theorem flow_spec (flags : Nat) :
    (flow flags = .ret ↔ flags &&& 1 ≠ 0) ∧
    (flow flags = .call ↔ flags &&& 1 = 0 ∧ flags &&& 2 ≠ 0) ∧
    (flow flags = .conditionalJump ↔ flags &&& 1 = 0 ∧ flags &&& 2 = 0 ∧ flags &&& 32 ≠ 0) ∧
    (flow flags = .indirectJump ↔
      flags &&& 1 = 0 ∧ flags &&& 2 = 0 ∧ flags &&& 32 = 0 ∧ flags &&& 16 ≠ 0) ∧
    (flow flags = .jump ↔
      flags &&& 1 = 0 ∧ flags &&& 2 = 0 ∧ flags &&& 32 = 0 ∧ flags &&& 16 = 0 ∧ flags &&& 64 ≠ 0) ∧
    (flow flags = .barrier ↔
      flags &&& 1 = 0 ∧ flags &&& 2 = 0 ∧ flags &&& 32 = 0 ∧ flags &&& 16 = 0 ∧ flags &&& 64 = 0 ∧
        (flags &&& 4 ≠ 0 ∨ flags &&& 512 ≠ 0)) ∧
    (flow flags = .normal ↔
      flags &&& 1 = 0 ∧ flags &&& 2 = 0 ∧ flags &&& 32 = 0 ∧ flags &&& 16 = 0 ∧ flags &&& 64 = 0 ∧
        flags &&& 4 = 0 ∧ flags &&& 512 = 0) := by
  rw [flow_eq]
  generalize flags &&& 1 = b1
  generalize flags &&& 2 = b2
  generalize flags &&& 32 = b32
  generalize flags &&& 16 = b16
  generalize flags &&& 64 = b64
  generalize flags &&& 4 = b4
  generalize flags &&& 512 = b512
  by_cases h1 : b1 = 0 <;> by_cases h2 : b2 = 0 <;> by_cases h32 : b32 = 0 <;>
    by_cases h16 : b16 = 0 <;> by_cases h64 : b64 = 0 <;> by_cases h4 : b4 = 0 <;>
    by_cases h512 : b512 = 0 <;> simp [h1, h2, h32, h16, h64, h4, h512]

private theorem and_mask (flags mask bit : Nat) (h : mask &&& bit = bit) :
    (flags &&& mask) &&& bit = flags &&& bit := by
  rw [Nat.and_assoc, h]

/-- Frame condition: the load, store and plain-branch bits never influence the classification. -/
theorem flow_ignores_other_flags (flags : Nat) : flow (flags &&& 631) = flow flags := by
  rw [flow_eq, flow_eq]
  rw [and_mask flags 631 1 (by decide), and_mask flags 631 2 (by decide),
    and_mask flags 631 32 (by decide), and_mask flags 631 16 (by decide),
    and_mask flags 631 64 (by decide), and_mask flags 631 4 (by decide),
    and_mask flags 631 512 (by decide)]

/-- An instruction classified from flags has the successors its flags promise. -/
theorem flow_successors (flags : Nat) (insn : Insn) (hf : insn.flow = flow flags) :
    (flags &&& 1 ≠ 0 → insn.successors = []) ∧
      (flags &&& 1 = 0 → flags &&& 2 ≠ 0 → insn.successors = [insn.next]) := by
  have hs := flow_spec flags
  constructor
  · intro h
    have : insn.flow = .ret := hf.trans (hs.1.2 h)
    simp [Insn.successors, this]
  · intro h1 h2
    have : insn.flow = .call := hf.trans (hs.2.1.2 ⟨h1, h2⟩)
    simp [Insn.successors, this]

/-! ## Branch-target computation -/

/-- The common shape of the branch-target helpers. -/
def relTarget (cond : Bool) (disp : Option Int) (compute : Int → Int) : Option Nat :=
  match cond, disp with
  | true, some d => if compute d ≥ 0 then some (compute d).toNat else none
  | _, _ => none

theorem relTarget_some_iff (cond : Bool) (disp : Option Int) (compute : Int → Int) (t : Nat) :
    relTarget cond disp compute = some t ↔
      cond = true ∧ ∃ d, disp = some d ∧ 0 ≤ compute d ∧ (t : Int) = compute d := by
  cases cond with
  | false => simp [relTarget]
  | true =>
    cases disp with
    | none => simp [relTarget]
    | some d =>
      simp only [relTarget, ge_iff_le, Option.some.injEq, true_and, exists_eq_left']
      by_cases hle : 0 ≤ compute d
      · rw [ite_eq_left hle]
        simp only [Option.some.injEq, hle, true_and]
        constructor
        · rintro rfl
          exact Int.toNat_of_nonneg hle
        · intro he
          omega
      · rw [ite_eq_right hle]
        simp [hle]

theorem relTarget_shift (cond : Bool) (disp : Option Int) (compute compute' : Int → Int) (t k : Nat)
    (hc : ∀ d, compute' d = compute d + k) (h : relTarget cond disp compute = some t) :
    relTarget cond disp compute' = some (t + k) := by
  have ⟨h1, d, h2, h3, h4⟩ := (relTarget_some_iff _ _ _ _).1 h
  refine (relTarget_some_iff _ _ _ _).2 ⟨h1, d, h2, ?_, ?_⟩
  · rw [hc]; omega
  · rw [hc]; omega

private abbrev mcImm : Option LLVM.MCOperand → Option Int
  | some (.imm value) => some value
  | _ => none

private abbrev opImm : Option LLVM.Operand → Option Int
  | some (.imm value) => some value
  | _ => none


theorem directControl_iff (flags : Nat) :
    directControl flags = true ↔ (flags &&& 8 ≠ 0 ∧ flags &&& 16 = 0) ∨ flags &&& 2 ≠ 0 := by
  lift_unfold directControl
  simp

private theorem powerpc_eq (address word : Nat) (operands : List LLVM.MCOperand) :
    powerpcMCTarget address word operands =
      relTarget (word / 0x4000000 == 16 || word / 0x4000000 == 18) (mcImm operands.getLast?)
        fun d => (if word &&& 2 != 0 then (0 : Int) else Int.ofNat address) + d * 4 := by
  lift_unfold powerpcMCTarget
  simp only []
  generalize (word / 0x4000000 == 16 || word / 0x4000000 == 18) = c
  generalize operands.getLast? = o
  cases c <;> cases o <;> try rfl
  rename_i op
  cases op <;> rfl

private theorem riscv_eq (address word flags : Nat) (operands : List LLVM.MCOperand) :
    riscvMCTarget address word flags operands =
      relTarget (riscvIsJal word || flags &&& 8 != 0 && flags &&& 16 == 0) (mcImm operands.getLast?)
        fun d => Int.ofNat address + d := by
  lift_unfold riscvMCTarget
  generalize (riscvIsJal word || flags &&& 8 != 0 && flags &&& 16 == 0) = c
  generalize operands.getLast? = o
  cases c <;> cases o <;> try rfl
  rename_i op
  cases op <;> rfl

private theorem aarch64_eq (address flags : Nat) (operands : List LLVM.MCOperand) :
    aarch64MCTarget address flags operands =
      relTarget (directControl flags)
        (mcImm (if flags &&& 32 != 0 then operands.getLast? else operands.head?))
        fun d => Int.ofNat address + d * 4 := by
  dsimp only [directControl]
  lift_unfold aarch64MCTarget
  dsimp only
  generalize (if flags &&& 32 != 0 then operands.getLast? else operands.head?) = o
  generalize (lift% directControl) flags = c
  cases c <;> cases o <;> try rfl
  rename_i op
  cases op <;> rfl

private theorem x86_eq (globals : Primus.Semantics.Environment) (next opcode : Nat)
    (operands : List LLVM.MCOperand) :
    x86MCTarget globals next opcode operands =
      relTarget (globals.relativeOpcodes.contains opcode) (mcImm operands.head?)
        fun d => Int.ofNat next + d := by
  lift_unfold x86MCTarget
  generalize globals.relativeOpcodes.contains opcode = c
  generalize operands.head? = o
  cases c <;> cases o <;> try rfl
  rename_i op
  cases op <;> rfl

private theorem arm32_eq (address : Nat) (decoded : LLVM.Decoded) :
    arm32Target address decoded =
      relTarget (["Bcc", "BL", "BL_pred", "BLXi"].contains decoded.opcode)
        (opImm decoded.operands.head?) fun d => Int.ofNat (address + 8) + d := by
  lift_unfold arm32Target
  generalize ["Bcc", "BL", "BL_pred", "BLXi"].contains decoded.opcode = c
  generalize decoded.operands.head? = o
  cases c <;> cases o <;> try rfl
  rename_i op
  cases op <;> rfl

/-- The operand a Thumb branch or call keeps its displacement in. -/
def thumbDisplacement (decoded : LLVM.Decoded) : Option LLVM.Operand :=
  if ["t2B", "t2Bcc", "tB", "tBcc"].contains decoded.opcode then decoded.operands.head?
  else if ["tBL", "tBLXi", "tCBZ", "tCBNZ"].contains decoded.opcode then decoded.operands.getLast?
  else none

private theorem thumb_eq (address : Nat) (decoded : LLVM.Decoded) :
    thumbTarget address decoded =
      relTarget true (opImm (thumbDisplacement decoded))
        fun d => Int.ofNat (if decoded.opcode = "tBLXi" then (address + 4) / 4 * 4 else address + 4) + d := by
  lift_unfold thumbTarget
  simp only [thumbDisplacement]
  generalize (if ["t2B", "t2Bcc", "tB", "tBcc"].contains decoded.opcode = true then decoded.operands.head?
    else if ["tBL", "tBLXi", "tCBZ", "tCBNZ"].contains decoded.opcode = true then decoded.operands.getLast?
    else none) = o
  cases o with
  | none => rfl
  | some op => cases op <;> rfl

private theorem imm_iff {t : Nat} {o : Option LLVM.MCOperand} {g : Int → Int} :
    (∃ d, mcImm o = some d ∧ 0 ≤ g d ∧ (t : Int) = g d) ↔
      ∃ d, o = some (.imm d) ∧ 0 ≤ g d ∧ (t : Int) = g d := by
  cases o with
  | none => simp
  | some op => cases op <;> simp

private theorem op_imm_iff {t : Nat} {o : Option LLVM.Operand} {g : Int → Int} :
    (∃ d, opImm o = some d ∧ 0 ≤ g d ∧ (t : Int) = g d) ↔
      ∃ d, o = some (.imm d) ∧ 0 ≤ g d ∧ (t : Int) = g d := by
  cases o with
  | none => simp
  | some op => cases op <;> simp

/-- PowerPC: only the B-form and I-form branches have a static target, from their last operand,
which is of words: from the current pc, or from zero when the AA bit is set. -/
theorem powerpcMCTarget_spec (address word t : Nat) (operands : List LLVM.MCOperand) :
    powerpcMCTarget address word operands = some t ↔
      (word / 0x4000000 = 16 ∨ word / 0x4000000 = 18) ∧ ∃ d, operands.getLast? = some (.imm d) ∧
        0 ≤ (if word &&& 2 != 0 then (0 : Int) else Int.ofNat address) + d * 4 ∧
        (t : Int) = (if word &&& 2 != 0 then (0 : Int) else Int.ofNat address) + d * 4 := by
  rw [powerpc_eq, relTarget_some_iff, imm_iff]
  simp

/-- The displacement of a conditional branch is its last operand, whatever `BO` and `BI` are. -/
theorem powerpc_conditional_target (bo bi d : Int) (a w : Nat)
    (hw : w / 0x4000000 = 16) (hrel : w &&& 2 = 0) (hd : 0 ≤ (a : Int) + d * 4) (b : Nat)
    (hb : (b : Int) = a + d * 4) :
    powerpcMCTarget a w [.imm bo, .reg bi.toNat, .imm d] = some b := by
  refine (powerpcMCTarget_spec a w b _).2 ⟨.inl hw, d, rfl, ?_, ?_⟩ <;> simp [hrel, hd, hb]

/-- `BCLR`, `BCCTR` and their kin, which LLVM marks as direct, have no static target. -/
theorem powerpc_register_branch_no_target (address word : Nat) (operands : List LLVM.MCOperand)
    (h1 : word / 0x4000000 ≠ 16) (h2 : word / 0x4000000 ≠ 18) :
    powerpcMCTarget address word operands = none := by
  rw [powerpc_eq]
  simp [relTarget, h1, h2]

/-- RISC-V: JAL and the flagged direct branches have the byte displacement as the last operand. -/
theorem riscvMCTarget_spec (address word flags t : Nat) (operands : List LLVM.MCOperand) :
    riscvMCTarget address word flags operands = some t ↔
      (riscvIsJal word = true ∨ flags &&& 8 ≠ 0 ∧ flags &&& 16 = 0) ∧
        ∃ d, operands.getLast? = some (.imm d) ∧
          0 ≤ Int.ofNat address + d ∧ (t : Int) = address + d := by
  rw [riscv_eq, relTarget_some_iff, imm_iff]
  simp

/-- AArch64: word-scaled displacement, last operand on conditional branches, first otherwise. -/
theorem aarch64MCTarget_spec (address flags t : Nat) (operands : List LLVM.MCOperand) :
    aarch64MCTarget address flags operands = some t ↔
      directControl flags = true ∧ ∃ d,
        (if flags &&& 32 != 0 then operands.getLast? else operands.head?) = some (.imm d) ∧
        0 ≤ Int.ofNat address + d * 4 ∧ (t : Int) = address + d * 4 := by
  rw [aarch64_eq, relTarget_some_iff, imm_iff]
  simp

/-- x86: only registered pc-relative opcodes have a target, measured from the next instruction. -/
theorem x86MCTarget_spec (globals : Primus.Semantics.Environment) (next opcode t : Nat)
    (operands : List LLVM.MCOperand) :
    x86MCTarget globals next opcode operands = some t ↔
      globals.relativeOpcodes.contains opcode = true ∧ ∃ d, operands.head? = some (.imm d) ∧
        0 ≤ Int.ofNat next + d ∧ (t : Int) = next + d := by
  rw [x86_eq, relTarget_some_iff, imm_iff]
  simp

/-- The x86 pc-relative opcodes include the ones that LLVM marks as conditional besides `JCC`. -/
theorem x86_relative_opcodes_cover_loops :
    ∀ opcode ∈ ["JCXZ", "JECXZ", "JRCXZ", "LOOP", "LOOPE", "LOOPNE", "JMP_1", "JCC_1", "CALL64pcrel32"],
      opcode ∈ x86RelativeOpcodes := by
  decide

/-- A32: the pc reads as the address plus eight, and the immediate of LLVM counts from the pc. -/
theorem arm32Target_spec (address t : Nat) (decoded : LLVM.Decoded) :
    arm32Target address decoded = some t ↔
      ["Bcc", "BL", "BL_pred", "BLXi"].contains decoded.opcode = true ∧
        ∃ d, decoded.operands.head? = some (.imm d) ∧
          0 ≤ Int.ofNat (address + 8) + d ∧ (t : Int) = address + 8 + d := by
  rw [arm32_eq, relTarget_some_iff, op_imm_iff]
  simp

/-- Thumb: the pc reads as the address plus four, word-aligned for `BLX`. -/
theorem thumbTarget_spec (address t : Nat) (decoded : LLVM.Decoded) :
    thumbTarget address decoded = some t ↔
      ∃ d, thumbDisplacement decoded = some (.imm d) ∧
        let pc := if decoded.opcode = "tBLXi" then (address + 4) / 4 * 4 else address + 4
        0 ≤ Int.ofNat pc + d ∧ (t : Int) = pc + d := by
  rw [thumb_eq, relTarget_some_iff, op_imm_iff]
  simp

/-- All Thumb branches other than `BLX` keep their distance when the code moves. -/
theorem thumbTarget_shift (address k t : Nat) (decoded : LLVM.Decoded)
    (hb : decoded.opcode ≠ "tBLXi") (h : thumbTarget address decoded = some t) :
    thumbTarget (address + k) decoded = some (t + k) := by
  rw [thumb_eq] at h ⊢
  refine relTarget_shift _ _ _ _ _ _ (fun d => ?_) h
  simp only [hb, ite_false, Int.ofNat_eq_natCast, Int.natCast_add]
  omega

theorem arm32Target_shift (address k t : Nat) (decoded : LLVM.Decoded)
    (h : arm32Target address decoded = some t) :
    arm32Target (address + k) decoded = some (t + k) := by
  rw [arm32_eq] at h ⊢
  refine relTarget_shift _ _ _ _ _ _ (fun d => ?_) h
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  omega

/-- Moving a B-form or I-form branch moves a relative target and keeps an absolute one. -/
theorem powerpcMCTarget_shift (address k word t : Nat) (operands : List LLVM.MCOperand)
    (hrel : word &&& 2 = 0) (h : powerpcMCTarget address word operands = some t) :
    powerpcMCTarget (address + k) word operands = some (t + k) := by
  rw [powerpc_eq] at h ⊢
  refine relTarget_shift _ _ _ _ _ _ (fun d => ?_) h
  simp only [hrel, Int.ofNat_eq_natCast, Int.natCast_add]
  simp
  omega

theorem riscvMCTarget_shift (address k word flags t : Nat) (operands : List LLVM.MCOperand)
    (h : riscvMCTarget address word flags operands = some t) :
    riscvMCTarget (address + k) word flags operands = some (t + k) := by
  rw [riscv_eq] at h ⊢
  refine relTarget_shift _ _ _ _ _ _ (fun d => ?_) h
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  omega

theorem aarch64MCTarget_shift (address k flags t : Nat) (operands : List LLVM.MCOperand)
    (h : aarch64MCTarget address flags operands = some t) :
    aarch64MCTarget (address + k) flags operands = some (t + k) := by
  rw [aarch64_eq] at h ⊢
  refine relTarget_shift _ _ _ _ _ _ (fun d => ?_) h
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  omega

theorem x86MCTarget_shift (globals : Primus.Semantics.Environment) (next k opcode t : Nat)
    (operands : List LLVM.MCOperand) (h : x86MCTarget globals next opcode operands = some t) :
    x86MCTarget globals (next + k) opcode operands = some (t + k) := by
  rw [x86_eq] at h ⊢
  refine relTarget_shift _ _ _ _ _ _ (fun d => ?_) h
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  omega

/-- Register branches never get a static target on AArch64 and RISC-V. -/
theorem indirect_has_no_target (address word flags : Nat) (operands : List LLVM.MCOperand)
    (h : flags &&& 16 ≠ 0) (hc : flags &&& 2 = 0) (hj : riscvIsJal word = false) :
    riscvMCTarget address word flags operands = none ∧
      aarch64MCTarget address flags operands = none := by
  have hd : directControl flags = false := by
    lift_unfold directControl
    simp [h, hc]
  rw [riscv_eq, aarch64_eq, hd, hj]
  simp [relTarget, h]

/-! ### MIPS -/

/-- `J`, `JAL` and `JALX` replace the low 28 bits of the delay slot's address. -/
theorem mips_region_target (address : Nat) (decoded : LLVM.Decoded) (i : Int)
    (hj : ["J", "JAL", "JALX"].contains decoded.opcode = true)
    (hl : decoded.operands.getLast? = some (.imm i)) (hi : 0 ≤ i) (hb : i < 0x10000000) :
    ∃ t, mipsTarget address decoded = some t ∧
      t % 0x10000000 = i.toNat ∧ t / 0x10000000 = (address + 4) / 0x10000000 := by
  refine ⟨(address + 4) / 0x10000000 * 0x10000000 + i.toNat, ?_, ?_, ?_⟩
  · lift_unfold mipsTarget
    rw [hl]
    show (if _ then (if _ then _ else _) else _) = _
    rw [ite_eq_left hj, ite_eq_left hi]
  · have : i.toNat < 0x10000000 := by omega
    omega
  · have : i.toNat < 0x10000000 := by omega
    omega

/-- All other direct branches and calls of MIPS, conditional or not, count from the branch: LLVM
has already added the four bytes of the delay slot. -/
theorem mips_relative_target (address t : Nat) (decoded : LLVM.Decoded) (d : Int)
    (hj : ["J", "JAL", "JALX"].contains decoded.opcode = false)
    (hf : directControl decoded.flags = true) (hl : decoded.operands.getLast? = some (.imm d))
    (hd : 0 ≤ Int.ofNat address + d) (ht : (t : Int) = address + d) :
    mipsTarget address decoded = some t := by
  lift_unfold mipsTarget
  rw [hl]
  have hne : ¬["J", "JAL", "JALX"].contains decoded.opcode = true := by simp only [hj]; decide
  show (if _ then _ else (if _ then (if _ then _ else _) else _)) = _
  rw [ite_eq_right hne, ite_eq_left hf, ite_eq_left hd]
  have h2 : Int.ofNat address + d = (t : Int) := ht.symm
  rw [h2]
  simp

/-- Moving a MIPS branch that counts from itself moves its target. -/
theorem mips_relative_shift (address k t : Nat) (decoded : LLVM.Decoded) (d : Int)
    (hj : ["J", "JAL", "JALX"].contains decoded.opcode = false)
    (hf : directControl decoded.flags = true) (hl : decoded.operands.getLast? = some (.imm d))
    (hd : 0 ≤ Int.ofNat address + d) (ht : (t : Int) = address + d) :
    mipsTarget (address + k) decoded = some (t + k) := by
  refine mips_relative_target _ _ decoded d hj hf hl ?_ ?_ <;>
    simp only [Int.ofNat_eq_natCast, Int.natCast_add] at * <;> omega

/-- A register operand in the last place, as of `JR` and `JALR`, gives no target. -/
theorem mips_register_jump_no_target (address : Nat) (decoded : LLVM.Decoded) (name : String)
    (hl : decoded.operands.getLast? = some (.reg name)) : mipsTarget address decoded = none := by
  lift_unfold mipsTarget
  rw [hl]

/-! ### Control flow that LLVM's flags miss -/

/-- `JAL` and `JALR` have no LLVM flags, their role is from the link registers `X1` and `X5`. -/
theorem riscvFlow_spec (word flags : Nat) :
    (word % 0x80 = 0x6f → riscvFlow word flags = if word / 0x80 % 0x20 = 0 then .jump else .call) ∧
      (word % 0x80 = 0x67 → word / 0x80 % 0x20 ≠ 0 → riscvFlow word flags = .call) ∧
      (word % 0x80 = 0x67 → word / 0x80 % 0x20 = 0 →
        riscvFlow word flags =
          if word / 0x8000 % 0x20 = 1 ∨ word / 0x8000 % 0x20 = 5 then .ret else .indirectJump) ∧
      (word % 0x80 ≠ 0x6f → word % 0x80 ≠ 0x67 → riscvFlow word flags = flow flags) := by
  lift_unfold riscvFlow
  refine ⟨fun h => ?_, fun h h2 => ?_, fun h h2 => ?_, fun h h2 => ?_⟩ <;> simp [*]

/-- `Bcc` with the condition `AL` is a plain jump, and any other ARM instruction goes by its flags. -/
theorem arm32Flow_spec (assembly : String) (size flags : Nat) (d : LLVM.Operand)
    (rest : List LLVM.Operand) :
    arm32Flow ⟨assembly, size, flags, "Bcc", d :: .imm 14 :: rest⟩ = .jump := rfl

theorem arm32Flow_other (decoded : LLVM.Decoded) (h : decoded.opcode ≠ "Bcc") :
    arm32Flow decoded = flow decoded.flags := by
  lift_unfold arm32Flow
  split <;> simp_all

/-! ## Register tables -/

/-- The low partial registers of x86 have the widths of the ISA and full registers as bases. -/
theorem x86LowRegister_spec (name base : String) (width : Nat)
    (h : x86LowRegister name = some (base, width)) :
    (width = 8 ∨ width = 16 ∨ width = 32) ∧
      base ∈ ["RAX", "RBX", "RCX", "RDX", "RSI", "RDI", "RBP", "RSP",
        "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15"] := by
  dsimp only [x86LowRegister] at h
  unfold_low at h
  split at h <;> first | (cases h; exact ⟨by decide, by decide⟩) | cases h

private theorem shape_ite {P : Nat → Nat → Prop} {c : Prop} [Decidable c] {a b : PValue}
    (ha : ∃ n w base, a = register n w base ∧ P w base)
    (hb : ∃ n w base, b = register n w base ∧ P w base) :
    ∃ n w base, (if c then a else b) = register n w base ∧ P w base := by
  by_cases h : c
  · rw [ite_eq_left h]; exact ha
  · rw [ite_eq_right h]; exact hb

/-- Every lifted register operand is a register, with a view no wider than its base. -/
theorem aarch64Register_shape (name : String) :
    ∃ n w b, aarch64Register name = register n w b ∧
      (w, b) ∈ [(1, 1), (8, 128), (16, 128), (32, 128), (64, 128), (128, 128), (32, 64), (64, 64)] := by
  lift_unfold aarch64Register
  dsimp only
  generalize (if name = "LR" then "X30" else if name = "FP" then "X29" else name) = canonical
  repeat' refine shape_ite ?_ ?_
  all_goals exact ⟨_, _, _, rfl, by decide⟩

theorem x86Register_shape (name : String) :
    ∃ n w b, x86Register name = register n w b ∧
      (w, b) ∈ [(1, 1), (8, 8), (8, 64), (16, 64), (32, 64), (64, 64)] := by
  lift_unfold x86Register
  simp only []
  generalize hc : (if (name.isEmpty || decide (name = "NoRegister")) = true then "Nil" else name) = c
  split
  · exact ⟨c, 1, 1, rfl, by decide⟩
  · split
    · exact ⟨c, 8, 8, rfl, by decide⟩
    · cases hl : x86LowRegister c with
      | none =>
        refine ⟨c, 64, 64, ?_, by decide⟩
        dsimp only [x86LowRegister] at hl
        rw [hl]
      | some pair =>
        obtain ⟨base, width⟩ := pair
        have hw := (x86LowRegister_spec _ _ _ hl).1
        refine ⟨base, width, 64, ?_, ?_⟩
        · dsimp only [x86LowRegister] at hl
          rw [hl]
        · rcases hw with rfl | rfl | rfl <;> decide

theorem x8632Register_shape (name : String) :
    ∃ n w b, x8632Register name = register n w b ∧
      (w, b) ∈ [(1, 1), (8, 8), (8, 32), (16, 32), (32, 32)] := by
  lift_unfold x8632Register
  simp only []
  generalize (if (name.isEmpty || decide (name = "NoRegister")) = true then "Nil" else name) = c
  repeat' split
  all_goals exact ⟨_, _, _, rfl, by decide⟩

theorem arm32Register_shape (name : String) :
    ∃ n w, arm32Register name = register n w w ∧ (w = 1 ∨ w = 32) := by
  lift_unfold arm32Register
  simp only []
  repeat' split
  all_goals exact ⟨_, _, rfl, by decide⟩

theorem powerpcRegister_shape (name : String) :
    ∃ n w, powerpcRegister name = register n w w ∧ (w = 1 ∨ w = 64) := by
  lift_unfold powerpcRegister
  simp only []
  repeat' split
  all_goals exact ⟨_, _, rfl, by decide⟩

theorem powerpc32Register_shape (name : String) :
    ∃ n w, powerpc32Register name = register n w w ∧ (w = 1 ∨ w = 32) := by
  lift_unfold powerpc32Register
  simp only []
  repeat' split
  all_goals exact ⟨_, _, rfl, by decide⟩

/-- The 32-bit and 64-bit RISC-V tables differ in width only. -/
theorem riscvRegister_widths (name : String) :
    ∃ n, riscvRegister name = register n 64 64 ∧ riscv32Register name = register n 32 32 ∧
      n = if name = "X0" then "XZR" else name := by
  lift_unfold riscvRegister
  lift_unfold riscv32Register
  by_cases h : name = "X0" <;> simp [h]

/-- The 32-bit and 64-bit MIPS tables differ in width only. -/
theorem mipsRegister_widths (name : String) :
    ∃ n, mipsRegister name = register n 64 64 ∧ mips32Register name = register n 32 32 :=
  ⟨mipsCanonicalName name, rfl, rfl⟩

/-- Register names outside the special classes pass through the table unchanged. -/
theorem arm32Register_name (name : String) (h1 : name ≠ "") (h2 : name ≠ "NoRegister") :
    ∃ w, arm32Register name = register name w w := by
  lift_unfold arm32Register
  have he : name.isEmpty = false := by simpa using h1
  simp only [he, h2, Bool.false_or, decide_false, Bool.false_eq_true, ite_false]
  split <;> exact ⟨_, rfl⟩

/-- x86 aliases map a 32-bit register onto the low half of its 64-bit base. -/
theorem x86_low_half_aliases :
    x86Register "EAX" = register "RAX" 32 64 ∧ x86Register "EBX" = register "RBX" 32 64 ∧
      x86Register "ECX" = register "RCX" 32 64 ∧ x86Register "EDX" = register "RDX" 32 64 ∧
      x86Register "ESI" = register "RSI" 32 64 ∧ x86Register "EDI" = register "RDI" 32 64 ∧
      x86Register "EBP" = register "RBP" 32 64 ∧ x86Register "ESP" = register "RSP" 32 64 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- All the partial views of the numbered registers, and the byte registers of the REX encoding. -/
theorem x86_partial_views :
    x86Register "R8D" = register "R8" 32 64 ∧ x86Register "R8W" = register "R8" 16 64 ∧
      x86Register "R8B" = register "R8" 8 64 ∧ x86Register "R15D" = register "R15" 32 64 ∧
      x86Register "R15W" = register "R15" 16 64 ∧ x86Register "R15B" = register "R15" 8 64 ∧
      x86Register "AX" = register "RAX" 16 64 ∧ x86Register "AL" = register "RAX" 8 64 ∧
      x86Register "SI" = register "RSI" 16 64 ∧ x86Register "SIL" = register "RSI" 8 64 ∧
      x86Register "DIL" = register "RDI" 8 64 ∧ x86Register "BPL" = register "RBP" 8 64 ∧
      x86Register "SPL" = register "RSP" 8 64 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A table entry is what the lifter sees for that register. -/
theorem x86Register_of_low (name base : String) (width : Nat)
    (h : x86LowRegister name = some (base, width)) : x86Register name = register base width 64 := by
  dsimp only [x86LowRegister] at h
  unfold_low at h
  split at h <;> first | (cases h; rfl) | cases h

/-- The bases of the partial registers are not partial themselves. -/
theorem x86LowRegister_base (name base : String) (width : Nat)
    (h : x86LowRegister name = some (base, width)) :
    x86LowRegister base = none ∧ x86HighByteBase base = none := by
  have hb := (x86LowRegister_spec name base width h).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- The registers of the 32-bit mode are views of the 32-bit bases. -/
theorem x8632_partial_views :
    x8632Register "AX" = register "EAX" 16 32 ∧ x8632Register "AL" = register "EAX" 8 32 ∧
      x8632Register "BX" = register "EBX" 16 32 ∧ x8632Register "CL" = register "ECX" 8 32 ∧
      x8632Register "DX" = register "EDX" 16 32 ∧ x8632Register "SI" = register "ESI" 16 32 ∧
      x8632Register "DI" = register "EDI" 16 32 ∧ x8632Register "BP" = register "EBP" 16 32 ∧
      x8632Register "SP" = register "ESP" 16 32 ∧ x8632Register "EAX" = register "EAX" 32 32 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A high byte keeps its name while lifted, and only then becomes bits 15 to 8 of its base. -/
theorem x86_high_bytes :
    x86Register "AH" = register "AH" 8 8 ∧ x86Register "BH" = register "BH" 8 8 ∧
      x86Register "CH" = register "CH" 8 8 ∧ x86Register "DH" = register "DH" 8 8 ∧
      x8632Register "AH" = register "AH" 8 8 ∧ x8632Register "DH" = register "DH" 8 8 ∧
      x86HighByteBase "AH" = some "RAX" ∧ x8632HighByteBase "AH" = some "EAX" :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Reads of a high byte are bits 15 to 8 of the base. -/
theorem highBytes_read (base : String → Option String) (width : Nat) (var : Bap.Var) (name : String)
    (h : base var.name = some name) :
    highBytesExp base width (.var var) = .extract 15 8 (.var ⟨name, .imm width, 0, false⟩) := by
  dsimp only [highBytesExp]
  unfold_high_exp
  simp [h]

/-- Writes of a high byte keep the other bits of the base. -/
theorem highBytes_write (base : String → Option String) (width : Nat) (var : Bap.Var)
    (name : String) (value : Bil.Exp) (rest : Bil.Program) (h : base var.name = some name) :
    resolveHighBytes base width (.move var value :: rest) =
      .move ⟨name, .imm width, 0, false⟩
        (.concat (.extract (width - 1) 16 (.var ⟨name, .imm width, 0, false⟩))
          (.concat (highBytesExp base width value)
            (.extract 7 0 (.var ⟨name, .imm width, 0, false⟩)))) ::
        resolveHighBytes base width rest := by
  dsimp only [resolveHighBytes, highBytesExp]
  unfold_resolve
  simp [h]

/-- A program without high bytes is not changed: moves to other registers keep their targets. -/
theorem highBytes_write_other (base : String → Option String) (width : Nat) (var : Bap.Var)
    (value : Bil.Exp) (rest : Bil.Program) (h : base var.name = none) :
    resolveHighBytes base width (.move var value :: rest) =
      .move var (highBytesExp base width value) :: resolveHighBytes base width rest := by
  dsimp only [resolveHighBytes, highBytesExp]
  unfold_resolve
  simp [h]

/-- Canonicalising a MIPS register name twice is the same as doing it once. -/
theorem mipsRegisterName_idempotent (name : String) :
    mipsRegisterName (mipsRegisterName name) = mipsRegisterName name := by
  by_cases h : name ∈ ["R0", "ZERO", "$zero", "AT", "V0", "V1", "A0", "A1", "A2", "A3", "T0", "T1", "T2", "T3", "T4", "T5", "T6", "T7", "S0", "S1", "S2", "S3", "S4", "S5", "S6", "S7", "T8", "T9", "K0", "K1", "GP", "SP", "FP", "S8", "RA", "$ra"]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hfix : mipsRegisterName name = name := by
      lift_unfold mipsRegisterName
      split <;> simp_all
    rw [hfix, hfix]

/-! ### Register bindings of the semantic environments -/

/-- `riscvGlobals` binds each `Xn` for n below 32, once. -/
theorem riscvGlobals_keys : (riscvGlobals.map (·.1)).Nodup ∧ riscvGlobals.length = 32 :=
  ⟨by decide, rfl⟩

theorem riscv32Globals_keys : (riscv32Globals.map (·.1)).Nodup ∧ riscv32Globals.length = 32 :=
  ⟨by decide, rfl⟩

theorem x86Globals_keys : (x86Globals.map (·.1)).Nodup ∧ x86Globals.length = 47 := ⟨by decide, rfl⟩

theorem x8632Globals_keys : (x8632Globals.map (·.1)).Nodup ∧ x8632Globals.length = 35 :=
  ⟨by decide, rfl⟩

theorem arm32Globals_keys : (arm32Globals.map (·.1)).Nodup ∧ arm32Globals.length = 26 :=
  ⟨by decide, rfl⟩

theorem mipsGlobals_keys : (mipsGlobals.map (·.1)).Nodup ∧ mipsGlobals.length = 36 :=
  ⟨by decide, rfl⟩

theorem mips32Globals_keys : (mips32Globals.map (·.1)).Nodup ∧ mips32Globals.length = 36 :=
  ⟨by decide, rfl⟩

set_option maxRecDepth 20000 in
theorem powerpcGlobals_keys : (powerpcGlobals.map (·.1)).Nodup ∧ powerpcGlobals.length = 73 :=
  ⟨by decide, rfl⟩

set_option maxRecDepth 20000 in
theorem powerpc32Globals_keys : (powerpc32Globals.map (·.1)).Nodup ∧ powerpc32Globals.length = 73 :=
  ⟨by decide, rfl⟩

set_option maxRecDepth 100000 in
theorem aarch64Globals_keys : (aarch64Globals.map (·.1)).Nodup ∧ aarch64Globals.length = 200 :=
  ⟨by decide, rfl⟩


/-! ### Canonical names -/

/-- `WSP` is the low half of `SP`, and writes through its base go to `SP`. -/
theorem aarch64_wsp_is_low_half_of_sp : aarch64Register "WSP" = register "SP" 32 64 := rfl

/-- Every spelling of the MIPS register zero is the zero register, which ignores writes. -/
theorem mips_zero_spellings :
    mipsCanonicalName "R0" = "XZR" ∧ mipsCanonicalName "ZERO" = "XZR" ∧
      mipsCanonicalName "$zero" = "XZR" ∧ mipsCanonicalName "$0" = "XZR" ∧
      mipsCanonicalName "ZERO_64" = "XZR" :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The 64-bit views that LLVM names with a suffix, and the numeric spellings, are the numbered
registers, and floating point registers keep their names. -/
theorem mips_canonical_names :
    mipsCanonicalName "V0_64" = "R2" ∧ mipsCanonicalName "A0_64" = "R4" ∧
      mipsCanonicalName "RA_64" = "R31" ∧ mipsCanonicalName "SP_64" = "R29" ∧
      mipsCanonicalName "$4" = "R4" ∧ mipsCanonicalName "$31" = "R31" ∧
      mipsCanonicalName "F0_64" = "F0_64" ∧ mipsCanonicalName "R4" = "R4" :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The names of the ABI are the names of the lifters -/

/-- The registers of the ARM convention are the registers the ARM lifter writes, in full. -/
theorem arm_abi_names (c : ABI.Convention) (h : ABI.convention .arm = some c) :
    arm32Register c.stackPointer.name = register "SP" 32 32 ∧
      c.returnAddress.map (fun r => arm32Register r.name) = some (register "LR" 32 32) ∧
      (c.functionArguments.map (arm32Register ·.name)).length = 4 ∧
      arm32Register c.result.name = register "R0" 32 32 := by
  simp only [ABI.convention, Option.some.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem x86_abi_names (c : ABI.Convention) (h : ABI.convention .x86 = some c) :
    x8632Register c.stackPointer.name = register "ESP" 32 32 ∧
      x8632Register c.result.name = register "EAX" 32 32 := by
  simp only [ABI.convention, Option.some.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩

theorem x86_64_abi_names (c : ABI.Convention) (h : ABI.convention .x86_64 = some c) :
    x86Register c.stackPointer.name = register "RSP" 64 64 ∧
      x86Register c.result.name = register "RAX" 64 64 := by
  simp only [ABI.convention, Option.some.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩

theorem riscv_abi_names (w : Nat) (c : ABI.Convention) (h : ABI.convention .riscv w = some c) :
    riscvRegister c.stackPointer.name = register "X2" 64 64 ∧
      riscvRegister c.result.name = register "X10" 64 64 := by
  simp only [ABI.convention, Option.some.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩

theorem mips_abi_names (w : Nat) (c : ABI.Convention) (h : ABI.convention .mips w = some c) :
    mipsCanonicalName c.stackPointer.name = "R29" ∧ mipsCanonicalName c.result.name = "R2" ∧
      c.returnAddress.map (fun r => mipsCanonicalName r.name) = some "R31" := by
  simp only [ABI.convention, Option.some.injEq] at h
  subst h
  refine ⟨?_, ?_, ?_⟩
  · show mipsCanonicalName "R29" = _
    decide
  · show mipsCanonicalName "R2" = _
    decide
  · show some (mipsCanonicalName "R31") = _
    decide

/-! ### Writes through partial registers -/

private abbrev assignRegister : Primus.Semantics.Context → String → Nat → Nat → PValue →
    Except String Bil.Program := primus% assignRegister
private abbrev expectBil : Primus.Semantics.Context → PValue → Except String (Nat × Bil.Exp) :=
  primus% expectBil

open Lean Elab Tactic in
/-- Unfolds the private assignment of `Bap.Primus.Semantics`. -/
local elab "unfold_assign" : tactic => do
  let p := mkIdent (mkPrivateNameCore `Bap.Primus.Semantics `Bap.Primus.Semantics.assignRegister)
  evalTactic (← `(tactic| unfold $p:ident))

/-- A write through a partial view replaces its low bits and keeps the others of the base, as the
aliases of `Theory.Target` do in the reference implementation. -/
theorem assign_partial_register (context : Primus.Semantics.Context) (name : String)
    (width base : Nat) (value : PValue) (exp : Bil.Exp) (hn : name ≠ "XZR") (hw : width < base)
    (hv : expectBil context value = .ok (width, exp)) :
    assignRegister context name width base value =
      .ok [.move ⟨name, .imm base, 0, false⟩
        (.concat (.extract (base - 1) width (.var ⟨name, .imm base, 0, false⟩)) exp)] := by
  dsimp only [assignRegister, expectBil] at hv ⊢
  unfold_assign
  simp [hn, hv, hw, bind, Except.bind, pure, Except.pure]

/-- A write of the whole base is a plain move. -/
theorem assign_full_register (context : Primus.Semantics.Context) (name : String)
    (width : Nat) (value : PValue) (exp : Bil.Exp) (hn : name ≠ "XZR")
    (hv : expectBil context value = .ok (width, exp)) :
    assignRegister context name width width value =
      .ok [.move ⟨name, .imm width, 0, false⟩ exp] := by
  dsimp only [assignRegister, expectBil] at hv ⊢
  unfold_assign
  simp [hn, hv, bind, Except.bind, pure, Except.pure]

/-! ## Operands and immediates -/

/-- Decoded immediates are 64-bit, sign-extended from 32 bits for the `i32` opcode family. -/
theorem immediate_spec (opcode : String) (value : Int) :
    (opcode.endsWith "i32" = true → immediate opcode value =
        .bil 64 (.int (BitVec.signExtend 64 (BitVec.ofInt 32 value)))) ∧
      (opcode.endsWith "ri32" = false → opcode.endsWith "mi32" = false →
        opcode.endsWith "i32" = false → immediate opcode value =
          .bil 64 (.int (BitVec.ofInt 64 value))) := by
  constructor
  · intro h
    lift_unfold immediate
    simp [h]
  · intro h1 h2 h3
    lift_unfold immediate
    simp [h1, h2, h3, Primus.Semantics.immediate]

/-- The result of the `i32` immediate has the value of its low 32 bits, read as signed. -/
theorem immediate_i32_value (opcode : String) (value : Int) (h : opcode.endsWith "i32" = true) :
    immediate opcode value = .bil 64 (.int (BitVec.ofInt 64 (BitVec.ofInt 32 value).toInt)) := by
  rw [(immediate_spec opcode value).1 h]
  rfl

/-- Machine immediates are as wide as the context word: 64 bits or 32 bits by decoder family. -/
theorem machineOperand_imm_width (environment : Primus.Semantics.Environment) (a b : Nat)
    (value : Int) :
    Primus.Semantics.machineOperand environment (semanticsContext a b) (.imm value) =
        .ok (.bil 64 (.int (BitVec.ofInt 64 value))) ∧
      Primus.Semantics.machineOperand environment (arm32Context a b) (.imm value) =
        .ok (.bil 32 (.int (BitVec.ofInt 32 value))) := ⟨rfl, rfl⟩

/-- Decoder contexts: the 64-bit family has a 64-bit word and memory, the 32-bit family a 32-bit
word and memory; both default to little endian and carry the given pcs. -/
theorem decoder_contexts (a b : Nat) :
    (semanticsContext a b).bits = 64 ∧ (semanticsContext a b).pc = a ∧
      (semanticsContext a b).nextPc = b ∧ (semanticsContext a b).endian = .little ∧
      (semanticsContext a b).memory.typ = .mem 64 8 ∧
      (arm32Context a b).bits = 32 ∧ (arm32Context a b).pc = a ∧
      (arm32Context a b).nextPc = b ∧ (arm32Context a b).endian = .little ∧
      (arm32Context a b).memory.typ = .mem 32 8 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Decoders -/

/-- `P` holds of every value `m` can return, in any world. -/
def Holds {α} (m : IO α) (P : α → Prop) : Prop := ∀ s r s', m s = EST.Out.ok r s' → P r

/-- `m` returns normally in every world. -/
def NoThrow {α} (m : IO α) : Prop := ∀ s, ∃ r s', m s = EST.Out.ok r s'

/-- `r` is a possible outcome of `m`. -/
def Returns {α} (m : IO α) (r : α) : Prop := ∃ s s', m s = EST.Out.ok r s'

theorem Holds.pure {α} {P : α → Prop} {a : α} (h : P a) : Holds (pure a : IO α) P := by
  intro s r s' he
  cases he
  exact h

private theorem bind_ok {α β} {m : IO α} {f : α → IO β} {s a s1} (h : m s = EST.Out.ok a s1) :
    (m >>= f) s = f a s1 := by
  show EST.bind m f s = _
  unfold EST.bind
  rw [h]

private theorem bind_error {α β} {m : IO α} {f : α → IO β} {s e s1}
    (h : m s = EST.Out.error e s1) : (m >>= f) s = EST.Out.error e s1 := by
  show EST.bind m f s = _
  unfold EST.bind
  rw [h]

theorem Holds.bind {α β} {m : IO α} {f : α → IO β} {P : β → Prop}
    (hf : ∀ a, Holds (f a) P) : Holds (m >>= f) P := by
  intro s r s' he
  cases hms : m s with
  | ok a s1 =>
    rw [bind_ok hms] at he
    exact hf a s1 r s' he
  | error e s1 =>
    rw [bind_error hms] at he
    cases he

/-- What every lifting decoder promises, whatever LLVM and the semantics return: the instruction is
labelled with the requested address and its flow comes from the decoder's classifier. -/
def Lifted {α} (classify : α → Flow) (address : Nat) (insn : Insn) : Prop :=
  insn.address = address ∧ ∃ evidence, insn.flow = classify evidence

/-- Peels monadic steps off a decoder body until its final `pure`. -/
local macro "lifted_decoder" : tactic =>
  `(tactic| (repeat' first
    | exact Holds.pure ⟨rfl, _, rfl⟩
    | refine Holds.bind fun _ => ?_))

theorem decodeX86With_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeX86With globals base address data) (Lifted (flow) address) := by
  unfold decodeX86With
  lifted_decoder

theorem decodeAArch64With_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeAArch64With globals base address data) (Lifted (flow) address) := by
  unfold decodeAArch64With
  lifted_decoder

theorem decodeRISCVWith_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeRISCVWith globals base address data) (Lifted (fun flow : Flow => flow) address) := by
  unfold decodeRISCVWith
  lifted_decoder

theorem decodePowerPCWith_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodePowerPCWith globals base address data) (Lifted (flow) address) := by
  unfold decodePowerPCWith
  lifted_decoder

theorem decodeMIPSWith_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeMIPSWith globals base address data) (Lifted (flow) address) := by
  unfold decodeMIPSWith
  lifted_decoder

theorem decodeARM32With_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeARM32With globals base address data) (Lifted (arm32Flow) address) := by
  unfold decodeARM32With
  lifted_decoder

theorem decodeThumbWith_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeThumbWith globals base address data) (Lifted (flow) address) := by
  unfold decodeThumbWith
  lifted_decoder

theorem decodeX8632With_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeX8632With globals base address data) (Lifted (flow) address) := by
  unfold decodeX8632With
  lifted_decoder

theorem decodeRISCV32With_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeRISCV32With globals base address data) (Lifted (fun flow : Flow => flow) address) := by
  unfold decodeRISCV32With
  lifted_decoder

theorem decodeMIPS32With_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeMIPS32With globals base address data) (Lifted (flow) address) := by
  unfold decodeMIPS32With
  lifted_decoder

theorem decodePowerPC32With_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodePowerPC32With globals base address data) (Lifted (flow) address) := by
  unfold decodePowerPC32With
  lifted_decoder

/-! ## Target modules -/

/-- The error-capturing wrapper each target module puts around its decoder. -/
def wrap {α} (m : IO α) : IO (Except String α) := do
  try
    pure (.ok (← m))
  catch error =>
    pure (.error (toString error))

private theorem tryCatch_ok {ε σ α} {x : EST ε σ α} {handle : ε → EST ε σ α} {s a s1}
    (h : x s = EST.Out.ok a s1) : EST.tryCatch x handle s = EST.Out.ok a s1 := by
  unfold EST.tryCatch
  rw [h]

private theorem tryCatch_error {ε σ α} {x : EST ε σ α} {handle : ε → EST ε σ α} {s e s1}
    (h : x s = EST.Out.error e s1) : EST.tryCatch x handle s = handle e s1 := by
  unfold EST.tryCatch
  rw [h]

private theorem wrap_ok {α} {m : IO α} {s a s1} (h : m s = EST.Out.ok a s1) :
    wrap m s = EST.Out.ok (.ok a) s1 := by
  have hb : (m >>= fun a => Pure.pure (Except.ok a) : IO (Except String α)) s =
      EST.Out.ok (.ok a) s1 := by
    rw [bind_ok h]
    rfl
  exact tryCatch_ok hb

private theorem wrap_error {α} {m : IO α} {s e s1} (h : m s = EST.Out.error e s1) :
    wrap m s = EST.Out.ok (.error (toString e)) s1 := by
  have hb : (m >>= fun a => Pure.pure (Except.ok a) : IO (Except String α)) s =
      EST.Out.error e s1 := bind_error h
  exact (tryCatch_error hb).trans rfl

/-- The wrapper never throws: decoding errors become values. -/
theorem wrap_noThrow {α} (m : IO α) : NoThrow (wrap m) := by
  intro s
  cases h : m s with
  | ok a s1 => exact ⟨_, _, wrap_ok h⟩
  | error e s1 => exact ⟨_, _, wrap_error h⟩

/-- Faithfulness of the wrapper: its successes are exactly those of the wrapped decoder. -/
theorem wrap_returns_ok {α} (m : IO α) (a : α) : Returns (wrap m) (.ok a) ↔ Returns m a := by
  constructor
  · rintro ⟨s, s', he⟩
    cases h : m s with
    | ok b s1 =>
      rw [wrap_ok h] at he
      cases he
      exact ⟨s, s', h⟩
    | error e s1 =>
      rw [wrap_error h] at he
      cases he
  · rintro ⟨s, s', h⟩
    exact ⟨s, s', wrap_ok h⟩

/-- Faithfulness on failures: errors are the rendered exceptions of the wrapped decoder. -/
theorem wrap_returns_error {α} (m : IO α) (message : String) :
    Returns (wrap m) (.error message : Except String α) ↔
      ∃ s e s', m s = EST.Out.error e s' ∧ toString e = message := by
  constructor
  · rintro ⟨s, s', he⟩
    cases h : m s with
    | ok b s1 =>
      rw [wrap_ok h] at he
      cases he
    | error e s1 =>
      rw [wrap_error h] at he
      cases he
      exact ⟨s, e, s', h, rfl⟩
  · rintro ⟨s, e, s', h, rfl⟩
    exact ⟨s, s', wrap_error h⟩

/-- The properties of a disassembler registered by a target module: its name, that decoding never
throws, and that it is label-consistent, which is the premise of the linear and recursive
disassembly proofs. -/
structure RegisteredAs (name : String) (d : Disassembler) : Prop where
  name : d.name = name
  total : ∀ address data, NoThrow (d.decode address data)
  consistent : ∀ address data insn, Returns (d.decode address data) (.ok insn) →
    insn.address = address

private theorem registeredAs_mk (name : String) (decode : Nat → ByteArray → IO (Except String Insn))
    (inner : Nat → ByteArray → IO Insn) (hd : ∀ a d, decode a d = wrap (inner a d))
    {α} (classify : α → Flow) (hi : ∀ a d, Holds (inner a d) (Lifted classify a)) : RegisteredAs name ⟨name, decode⟩ where
  name := rfl
  total a d := by
    show NoThrow (decode a d)
    rw [hd]
    exact wrap_noThrow _
  consistent a d insn h := by
    change Returns (decode a d) _ at h
    rw [hd] at h
    have ⟨s, s', he⟩ := (wrap_returns_ok _ _).1 h
    exact (hi a d s insn s' he).1

/-- Registration data of the 11 target modules. -/
theorem x86_disassembler (base : Nat) :
    Holds (X86.disassembler base) (RegisteredAs "x86-llvm-primus") := by
  unfold X86.disassembler
  refine Holds.bind fun globals => Holds.pure ?_
  exact registeredAs_mk _ _ (decodeX86With globals base) (fun _ _ => rfl) _ (decodeX86With_lifted globals base)

theorem x86_decodeAt (base address : Nat) (data : ByteArray) :
    Holds (X86.decodeAt base address data) fun result =>
      ∀ insn, result = .ok insn → insn.address = address := by
  unfold X86.decodeAt
  refine Holds.bind fun globals => ?_
  intro s r s' he
  intro insn hr
  subst hr
  have hw : Returns (wrap (decodeX86With globals base address data)) (.ok insn) := ⟨s, s', he⟩
  have ⟨s0, s0', h0⟩ := (wrap_returns_ok _ _).1 hw
  exact (decodeX86With_lifted globals base address data s0 insn s0' h0).1

theorem aarch64_disassembler (base : Nat) :
    Holds (AArch64.disassembler base) (RegisteredAs "aarch64-llvm-primus") := by
  unfold AArch64.disassembler
  refine Holds.bind fun globals => Holds.pure ?_
  exact registeredAs_mk _ _ (decodeAArch64With globals base) (fun _ _ => rfl) _ (decodeAArch64With_lifted globals base)

theorem aarch64_decodeAt (base address : Nat) (data : ByteArray) :
    Holds (AArch64.decodeAt base address data) fun result =>
      ∀ insn, result = .ok insn → insn.address = address := by
  unfold AArch64.decodeAt
  refine Holds.bind fun globals => ?_
  intro s r s' he
  intro insn hr
  subst hr
  have hw : Returns (wrap (decodeAArch64With globals base address data)) (.ok insn) := ⟨s, s', he⟩
  have ⟨s0, s0', h0⟩ := (wrap_returns_ok _ _).1 hw
  exact (decodeAArch64With_lifted globals base address data s0 insn s0' h0).1

theorem riscv_disassembler (base : Nat) :
    Holds (RISCV.disassembler base) (RegisteredAs "riscv64-llvm-primus") := by
  unfold RISCV.disassembler
  refine Holds.bind fun globals => Holds.pure ?_
  exact registeredAs_mk _ _ (decodeRISCVWith globals base) (fun _ _ => rfl) _ (decodeRISCVWith_lifted globals base)

theorem riscv_decodeAt (base address : Nat) (data : ByteArray) :
    Holds (RISCV.decodeAt base address data) fun result =>
      ∀ insn, result = .ok insn → insn.address = address := by
  unfold RISCV.decodeAt
  refine Holds.bind fun globals => ?_
  intro s r s' he
  intro insn hr
  subst hr
  have hw : Returns (wrap (decodeRISCVWith globals base address data)) (.ok insn) := ⟨s, s', he⟩
  have ⟨s0, s0', h0⟩ := (wrap_returns_ok _ _).1 hw
  exact (decodeRISCVWith_lifted globals base address data s0 insn s0' h0).1

theorem powerpc_disassembler (base : Nat) :
    Holds (PowerPC.disassembler base) (RegisteredAs "powerpc64le-llvm-primus") := by
  unfold PowerPC.disassembler
  refine Holds.bind fun globals => Holds.pure ?_
  exact registeredAs_mk _ _ (decodePowerPCWith globals base) (fun _ _ => rfl) _ (decodePowerPCWith_lifted globals base)

theorem powerpc_decodeAt (base address : Nat) (data : ByteArray) :
    Holds (PowerPC.decodeAt base address data) fun result =>
      ∀ insn, result = .ok insn → insn.address = address := by
  unfold PowerPC.decodeAt
  refine Holds.bind fun globals => ?_
  intro s r s' he
  intro insn hr
  subst hr
  have hw : Returns (wrap (decodePowerPCWith globals base address data)) (.ok insn) := ⟨s, s', he⟩
  have ⟨s0, s0', h0⟩ := (wrap_returns_ok _ _).1 hw
  exact (decodePowerPCWith_lifted globals base address data s0 insn s0' h0).1

theorem mips_disassembler (base : Nat) :
    Holds (MIPS.disassembler base) (RegisteredAs "mips64-llvm-primus") := by
  unfold MIPS.disassembler
  refine Holds.bind fun globals => Holds.pure ?_
  exact registeredAs_mk _ _ (decodeMIPSWith globals base) (fun _ _ => rfl) _ (decodeMIPSWith_lifted globals base)

theorem mips_decodeAt (base address : Nat) (data : ByteArray) :
    Holds (MIPS.decodeAt base address data) fun result =>
      ∀ insn, result = .ok insn → insn.address = address := by
  unfold MIPS.decodeAt
  refine Holds.bind fun globals => ?_
  intro s r s' he
  intro insn hr
  subst hr
  have hw : Returns (wrap (decodeMIPSWith globals base address data)) (.ok insn) := ⟨s, s', he⟩
  have ⟨s0, s0', h0⟩ := (wrap_returns_ok _ _).1 hw
  exact (decodeMIPSWith_lifted globals base address data s0 insn s0' h0).1

theorem arm32_disassembler (base : Nat) :
    Holds (ARM32.disassembler base) (RegisteredAs "armv7-llvm-primus") := by
  unfold ARM32.disassembler
  refine Holds.bind fun globals => Holds.pure ?_
  exact registeredAs_mk _ _ (decodeARM32With globals base) (fun _ _ => rfl) _ (decodeARM32With_lifted globals base)

theorem arm32_decodeAt (base address : Nat) (data : ByteArray) :
    Holds (ARM32.decodeAt base address data) fun result =>
      ∀ insn, result = .ok insn → insn.address = address := by
  unfold ARM32.decodeAt
  refine Holds.bind fun globals => ?_
  intro s r s' he
  intro insn hr
  subst hr
  have hw : Returns (wrap (decodeARM32With globals base address data)) (.ok insn) := ⟨s, s', he⟩
  have ⟨s0, s0', h0⟩ := (wrap_returns_ok _ _).1 hw
  exact (decodeARM32With_lifted globals base address data s0 insn s0' h0).1

theorem thumb_disassembler (base : Nat) :
    Holds (Thumb.disassembler base) (RegisteredAs "thumbv7-llvm-primus") := by
  unfold Thumb.disassembler
  refine Holds.bind fun globals => Holds.pure ?_
  exact registeredAs_mk _ _ (decodeThumbWith globals base) (fun _ _ => rfl) _ (decodeThumbWith_lifted globals base)

theorem thumb_decodeAt (base address : Nat) (data : ByteArray) :
    Holds (Thumb.decodeAt base address data) fun result =>
      ∀ insn, result = .ok insn → insn.address = address := by
  unfold Thumb.decodeAt
  refine Holds.bind fun globals => ?_
  intro s r s' he
  intro insn hr
  subst hr
  have hw : Returns (wrap (decodeThumbWith globals base address data)) (.ok insn) := ⟨s, s', he⟩
  have ⟨s0, s0', h0⟩ := (wrap_returns_ok _ _).1 hw
  exact (decodeThumbWith_lifted globals base address data s0 insn s0' h0).1

theorem x8632_disassembler (base : Nat) :
    Holds (X8632.disassembler base) (RegisteredAs "i386-llvm-primus") := by
  unfold X8632.disassembler
  refine Holds.bind fun globals => Holds.pure ?_
  exact registeredAs_mk _ _ (decodeX8632With globals base) (fun _ _ => rfl) _ (decodeX8632With_lifted globals base)

theorem x8632_decodeAt (base address : Nat) (data : ByteArray) :
    Holds (X8632.decodeAt base address data) fun result =>
      ∀ insn, result = .ok insn → insn.address = address := by
  unfold X8632.decodeAt
  refine Holds.bind fun globals => ?_
  intro s r s' he
  intro insn hr
  subst hr
  have hw : Returns (wrap (decodeX8632With globals base address data)) (.ok insn) := ⟨s, s', he⟩
  have ⟨s0, s0', h0⟩ := (wrap_returns_ok _ _).1 hw
  exact (decodeX8632With_lifted globals base address data s0 insn s0' h0).1

theorem riscv32_disassembler (base : Nat) :
    Holds (RISCV32.disassembler base) (RegisteredAs "riscv32-llvm-primus") := by
  unfold RISCV32.disassembler
  refine Holds.bind fun globals => Holds.pure ?_
  exact registeredAs_mk _ _ (decodeRISCV32With globals base) (fun _ _ => rfl) _ (decodeRISCV32With_lifted globals base)

theorem riscv32_decodeAt (base address : Nat) (data : ByteArray) :
    Holds (RISCV32.decodeAt base address data) fun result =>
      ∀ insn, result = .ok insn → insn.address = address := by
  unfold RISCV32.decodeAt
  refine Holds.bind fun globals => ?_
  intro s r s' he
  intro insn hr
  subst hr
  have hw : Returns (wrap (decodeRISCV32With globals base address data)) (.ok insn) := ⟨s, s', he⟩
  have ⟨s0, s0', h0⟩ := (wrap_returns_ok _ _).1 hw
  exact (decodeRISCV32With_lifted globals base address data s0 insn s0' h0).1

theorem mips32_disassembler (base : Nat) :
    Holds (MIPS32.disassembler base) (RegisteredAs "mips-llvm-primus") := by
  unfold MIPS32.disassembler
  refine Holds.bind fun globals => Holds.pure ?_
  exact registeredAs_mk _ _ (decodeMIPS32With globals base) (fun _ _ => rfl) _ (decodeMIPS32With_lifted globals base)

theorem mips32_decodeAt (base address : Nat) (data : ByteArray) :
    Holds (MIPS32.decodeAt base address data) fun result =>
      ∀ insn, result = .ok insn → insn.address = address := by
  unfold MIPS32.decodeAt
  refine Holds.bind fun globals => ?_
  intro s r s' he
  intro insn hr
  subst hr
  have hw : Returns (wrap (decodeMIPS32With globals base address data)) (.ok insn) := ⟨s, s', he⟩
  have ⟨s0, s0', h0⟩ := (wrap_returns_ok _ _).1 hw
  exact (decodeMIPS32With_lifted globals base address data s0 insn s0' h0).1

theorem powerpc32_disassembler (base : Nat) :
    Holds (PowerPC32.disassembler base) (RegisteredAs "powerpc-llvm-primus") := by
  unfold PowerPC32.disassembler
  refine Holds.bind fun globals => Holds.pure ?_
  exact registeredAs_mk _ _ (decodePowerPC32With globals base) (fun _ _ => rfl) _ (decodePowerPC32With_lifted globals base)

theorem powerpc32_decodeAt (base address : Nat) (data : ByteArray) :
    Holds (PowerPC32.decodeAt base address data) fun result =>
      ∀ insn, result = .ok insn → insn.address = address := by
  unfold PowerPC32.decodeAt
  refine Holds.bind fun globals => ?_
  intro s r s' he
  intro insn hr
  subst hr
  have hw : Returns (wrap (decodePowerPC32With globals base address data)) (.ok insn) := ⟨s, s', he⟩
  have ⟨s0, s0', h0⟩ := (wrap_returns_ok _ _).1 hw
  exact (decodePowerPC32With_lifted globals base address data s0 insn s0' h0).1

end Bap.Proofs.Target
