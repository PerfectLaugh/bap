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
import Bap.Proofs.Bil
import Bap.Proofs.Core

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
/-- `lift_unfold` in a hypothesis. -/
local elab "lift_unfold " n:ident " at " h:ident : tactic => do
  evalTactic (← `(tactic| dsimp only [$n:ident] at $h:ident))
  let p := mkIdent (mkPrivateNameCore `Bap.Target.LLVMLift (`Bap.Target.LLVMLift ++ n.getId.eraseMacroScopes))
  evalTactic (← `(tactic| unfold $p:ident at $h:ident))

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
/-- Unfolds the private table of the registers of x87 in a hypothesis. -/
local elab "unfold_float" " at " h:ident : tactic => do
  let p := mkIdent (mkPrivateNameCore `Bap.Target.LLVMLift `Bap.Target.LLVMLift.x86FloatRegister)
  evalTactic (← `(tactic| unfold $p:ident at $h:ident))

open Lean Elab Tactic in
/-- Unfolds the private list of the primitives in a hypothesis. -/
local elab "unfold_primitive_globals" " at " h:ident : tactic => do
  let p := mkIdent (mkPrivateNameCore `Bap.Target.LLVMLift `Bap.Target.LLVMLift.primitiveGlobals)
  evalTactic (← `(tactic| unfold $p:ident at $h:ident))

open Lean Elab Tactic in
/-- Unfolds the private table of the status registers of AArch64. -/
local elab "unfold_status" : tactic => do
  let p := mkIdent (mkPrivateNameCore `Bap.Target.LLVMLift `Bap.Target.LLVMLift.aarch64StatusRegister)
  evalTactic (← `(tactic| unfold $p:ident))

open Lean Elab Tactic in
/-- Unfolds the private lookup of a name of the semantics. -/
local elab "unfold_lookup" : tactic => do
  let p := mkIdent (mkPrivateNameCore `Bap.Primus.Semantics `Bap.Primus.Semantics.lookup)
  evalTactic (← `(tactic| unfold $p:ident))

open Lean Elab Tactic in
/-- Unfolds the private alias rewrite of an expression. -/
local elab "unfold_alias_exp" : tactic => do
  let p := mkIdent (mkPrivateNameCore `Bap.Target.LLVMLift `Bap.Target.LLVMLift.aliasExp)
  evalTactic (← `(tactic| unfold $p:ident))

open Lean Elab Tactic in
/-- Rewrites by the unfolding equation of the private alias rewrite of a program. -/
local elab "unfold_resolve" : tactic => do
  let p := mkIdent (mkPrivateNameCore `Bap.Target.LLVMLift (`Bap.Target.LLVMLift.resolveAliases ++ `eq_def))
  evalTactic (← `(tactic| rw [$p:ident]))

private abbrev aarch64Register : String → PValue := lift% aarch64Register
private abbrev x86LowRegister : String → Option (String × Nat) := lift% x86LowRegister
private abbrev x86HighByteBase : String → Option String := lift% x86HighByteBase
private abbrev x8632HighByteBase : String → Option String := lift% x8632HighByteBase
private abbrev mipsCanonicalName : String → String := lift% mipsCanonicalName
private abbrev resolveAliases : (String → Option Alias) → Bil.Program → Bil.Program := lift% resolveAliases
private abbrev aliasExp : (String → Option Alias) → Bil.Exp → Bil.Exp := lift% aliasExp
private abbrev x86Aliases : (String → Option String) → Nat → String → Option Alias := lift% x86Aliases
private abbrev armAliases : String → Option Alias := lift% armAliases
private abbrev powerpcAliases : String → Option Alias := lift% powerpcAliases
private abbrev x86FlagBits : List String := lift% x86FlagBits
private abbrev x86FloatRegister : String → Option PValue := lift% x86FloatRegister
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
private abbrev decodeThumbIt : Primus.Semantics.Environment → Nat → Nat → ByteArray → LLVM.Decoded → Nat → Nat → IO Insn :=
  lift% decodeThumbIt
private abbrev powerpcMCTarget : Nat → Nat → Nat → List LLVM.MCOperand → Option Nat :=
  lift% powerpcMCTarget
private abbrev riscvIsJal : Nat → Bool := lift% riscvIsJal
private abbrev riscvMCTarget : Nat → Nat → Nat → Nat → List LLVM.MCOperand → Option Nat :=
  lift% riscvMCTarget
private abbrev aarch64MCTarget : Nat → Nat → List LLVM.MCOperand → Option Nat :=
  lift% aarch64MCTarget
private abbrev x86MCTarget : Nat → Primus.Semantics.Environment → Nat → Nat → List LLVM.MCOperand → Option Nat :=
  lift% x86MCTarget
private abbrev mipsTarget : Nat → Nat → LLVM.Decoded → Option Nat := lift% mipsTarget
private abbrev mipsFlow : LLVM.Decoded → Flow := lift% mipsFlow
private abbrev wrapAddress : Nat → Int → Nat := lift% wrapAddress
private abbrev programJump : Bil.Program → Option Bool := lift% programJump
private abbrev armControlFlow : Flow → Bil.Program → Flow := lift% armControlFlow
private abbrev armCondition : Int → Option Bil.Exp := lift% armCondition
private abbrev x86VectorRegister : String → Option PValue := lift% x86VectorRegister
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

/-! ### Addresses modulo the width of the address space -/

private theorem pow_pos_int (bits : Nat) : (0 : Int) < (2 ^ bits : Int) :=
  Int.pow_pos (by decide)

private theorem wrapAddress_int (bits : Nat) (x : Int) :
    (wrapAddress bits x : Int) = x % (2 ^ bits : Int) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt (pow_pos_int bits)))

theorem wrapAddress_lt (bits : Nat) (x : Int) : wrapAddress bits x < 2 ^ bits := by
  have h1 := wrapAddress_int bits x
  have h2 := Int.emod_lt_of_pos x (pow_pos_int bits)
  rw [← h1] at h2
  exact_mod_cast h2

/-- An address that fits is kept. -/
theorem wrapAddress_of_fits (bits : Nat) (x : Int) (h0 : 0 ≤ x) (h1 : x < (2 ^ bits : Int)) :
    (wrapAddress bits x : Int) = x := by
  rw [wrapAddress_int, Int.emod_eq_of_lt h0 h1]

/-- A negative address comes from the top of the address space, as `0xfffffffffff6d008` does. -/
theorem wrapAddress_of_negative (bits : Nat) (x : Int) (h0 : -(2 ^ bits : Int) ≤ x) (h1 : x < 0) :
    (wrapAddress bits x : Int) = x + (2 ^ bits : Int) := by
  rw [wrapAddress_int]
  have hp := pow_pos_int bits
  have : x % (2 ^ bits : Int) = (x + (2 ^ bits : Int)) % (2 ^ bits : Int) := by
    rw [Int.add_emod_right]
  rw [this, Int.emod_eq_of_lt (by omega) (by omega)]

/-- Adding a distance is the same before and after wrapping. -/
theorem wrapAddress_add (bits : Nat) (x : Int) (k : Nat) :
    wrapAddress bits ((wrapAddress bits x + k : Nat) : Int) = wrapAddress bits (x + k) := by
  have h : (((wrapAddress bits x + k : Nat) : Int)) % (2 ^ bits : Int) = (x + k) % (2 ^ bits : Int) := by
    rw [Int.natCast_add, wrapAddress_int, Int.emod_add_emod]
  have h1 := wrapAddress_int bits ((wrapAddress bits x + k : Nat) : Int)
  have h2 := wrapAddress_int bits (x + k)
  rw [h, ← h2] at h1
  exact_mod_cast h1

/-- Modular equality of addresses is equality of their wrapped forms. -/
theorem wrapAddress_congr (bits : Nat) (x y : Int) (h : x % (2 ^ bits : Int) = y % (2 ^ bits : Int)) :
    wrapAddress bits x = wrapAddress bits y := by
  have h1 := wrapAddress_int bits x
  have h2 := wrapAddress_int bits y
  rw [h, ← h2] at h1
  exact_mod_cast h1

/-- The common shape of the branch-target helpers. -/
def relTarget (bits : Nat) (cond : Bool) (disp : Option Int) (compute : Int → Int) : Option Nat :=
  match cond, disp with
  | true, some d => some (wrapAddress bits (compute d))
  | _, _ => none

theorem relTarget_some_iff (bits : Nat) (cond : Bool) (disp : Option Int) (compute : Int → Int)
    (t : Nat) :
    relTarget bits cond disp compute = some t ↔
      cond = true ∧ ∃ d, disp = some d ∧ t = wrapAddress bits (compute d) := by
  cases cond with
  | false => simp [relTarget]
  | true =>
    cases disp with
    | none => simp [relTarget]
    | some d => simp [relTarget, eq_comm]

theorem relTarget_shift (bits : Nat) (cond : Bool) (disp : Option Int) (compute compute' : Int → Int)
    (t k : Nat) (hc : ∀ d, compute' d = compute d + k) (h : relTarget bits cond disp compute = some t) :
    relTarget bits cond disp compute' = some (wrapAddress bits ((t + k : Nat) : Int)) := by
  have ⟨h1, d, h2, h3⟩ := (relTarget_some_iff _ _ _ _ _).1 h
  refine (relTarget_some_iff _ _ _ _ _).2 ⟨h1, d, h2, ?_⟩
  rw [h3, hc, wrapAddress_add]

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

private theorem powerpc_eq (bits address word : Nat) (operands : List LLVM.MCOperand) :
    powerpcMCTarget bits address word operands =
      relTarget bits (word / 0x4000000 == 16 || word / 0x4000000 == 18) (mcImm operands.getLast?)
        fun d => (if word &&& 2 != 0 then (0 : Int) else Int.ofNat address) + d * 4 := by
  lift_unfold powerpcMCTarget
  simp only []
  generalize (word / 0x4000000 == 16 || word / 0x4000000 == 18) = c
  generalize operands.getLast? = o
  cases c <;> cases o <;> try rfl
  rename_i op
  cases op <;> rfl

private theorem riscv_eq (bits address word flags : Nat) (operands : List LLVM.MCOperand) :
    riscvMCTarget bits address word flags operands =
      relTarget bits (riscvIsJal word || flags &&& 8 != 0 && flags &&& 16 == 0)
        (mcImm operands.getLast?) fun d => Int.ofNat address + d := by
  dsimp only [riscvIsJal]
  lift_unfold riscvMCTarget
  generalize ((lift% riscvIsJal) word || flags &&& 8 != 0 && flags &&& 16 == 0) = c
  generalize operands.getLast? = o
  cases c <;> cases o <;> try rfl
  rename_i op
  cases op <;> rfl

private theorem aarch64_eq (address flags : Nat) (operands : List LLVM.MCOperand) :
    aarch64MCTarget address flags operands =
      relTarget 64 (directControl flags)
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

private theorem x86_eq (bits : Nat) (globals : Primus.Semantics.Environment) (next opcode : Nat)
    (operands : List LLVM.MCOperand) :
    x86MCTarget bits globals next opcode operands =
      relTarget bits (globals.relativeOpcodes.contains opcode) (mcImm operands.head?)
        fun d => Int.ofNat next + d := by
  lift_unfold x86MCTarget
  generalize globals.relativeOpcodes.contains opcode = c
  generalize operands.head? = o
  cases c <;> cases o <;> try rfl
  rename_i op
  cases op <;> rfl

private theorem arm32_eq (address : Nat) (decoded : LLVM.Decoded) :
    arm32Target address decoded =
      relTarget 32 (["Bcc", "BL", "BL_pred", "BLXi"].contains decoded.opcode)
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
      relTarget 32 true (opImm (thumbDisplacement decoded))
        fun d => Int.ofNat (if decoded.opcode = "tBLXi" then (address + 4) / 4 * 4 else address + 4) + d := by
  lift_unfold thumbTarget
  simp only [thumbDisplacement]
  generalize (if ["t2B", "t2Bcc", "tB", "tBcc"].contains decoded.opcode = true then decoded.operands.head?
    else if ["tBL", "tBLXi", "tCBZ", "tCBNZ"].contains decoded.opcode = true then decoded.operands.getLast?
    else none) = o
  cases o with
  | none => rfl
  | some op => cases op <;> rfl

private theorem imm_iff {t : Nat} {o : Option LLVM.MCOperand} {g : Int → Nat} :
    (∃ d, mcImm o = some d ∧ t = g d) ↔ ∃ d, o = some (.imm d) ∧ t = g d := by
  cases o with
  | none => simp
  | some op => cases op <;> simp

private theorem op_imm_iff {t : Nat} {o : Option LLVM.Operand} {g : Int → Nat} :
    (∃ d, opImm o = some d ∧ t = g d) ↔ ∃ d, o = some (.imm d) ∧ t = g d := by
  cases o with
  | none => simp
  | some op => cases op <;> simp

/-- PowerPC: only the B-form and I-form branches have a static target, from their last operand,
which is of words: from the current pc, or from zero when the AA bit is set. Modulo the width. -/
theorem powerpcMCTarget_spec (bits address word t : Nat) (operands : List LLVM.MCOperand) :
    powerpcMCTarget bits address word operands = some t ↔
      (word / 0x4000000 = 16 ∨ word / 0x4000000 = 18) ∧ ∃ d, operands.getLast? = some (.imm d) ∧
        t = wrapAddress bits ((if word &&& 2 != 0 then (0 : Int) else Int.ofNat address) + d * 4) := by
  rw [powerpc_eq, relTarget_some_iff, imm_iff]
  simp

/-- The displacement of a conditional branch is its last operand, whatever `BO` and `BI` are. -/
theorem powerpc_conditional_target (bits : Nat) (bo bi d : Int) (a w : Nat)
    (hw : w / 0x4000000 = 16) (hrel : w &&& 2 = 0) :
    powerpcMCTarget bits a w [.imm bo, .reg bi.toNat, .imm d] =
      some (wrapAddress bits ((a : Int) + d * 4)) := by
  refine (powerpcMCTarget_spec bits a w _ _).2 ⟨.inl hw, d, rfl, ?_⟩
  simp [hrel]

/-- A negative absolute branch, as a negative `ba`, targets the top of the address space. -/
theorem powerpc_negative_absolute_target (bits : Nat) (a w : Nat) (d : Int)
    (hw : w / 0x4000000 = 18) (habs : w &&& 2 ≠ 0) (h0 : -(2 ^ bits : Int) ≤ d * 4) (h1 : d * 4 < 0) :
    ∃ t, powerpcMCTarget bits a w [.imm d] = some t ∧ (t : Int) = d * 4 + (2 ^ bits : Int) := by
  refine ⟨_, (powerpcMCTarget_spec bits a w _ _).2 ⟨.inr hw, d, rfl, rfl⟩, ?_⟩
  simp only [habs, bne_iff_ne, ne_eq, not_false_eq_true, ite_true, Int.zero_add]
  exact wrapAddress_of_negative bits _ h0 h1

/-- `BCLR`, `BCCTR` and their kin, which LLVM marks as direct, have no static target. -/
theorem powerpc_register_branch_no_target (bits address word : Nat) (operands : List LLVM.MCOperand)
    (h1 : word / 0x4000000 ≠ 16) (h2 : word / 0x4000000 ≠ 18) :
    powerpcMCTarget bits address word operands = none := by
  rw [powerpc_eq]
  simp [relTarget, h1, h2]

/-- RISC-V: JAL and the flagged direct branches have the byte displacement as the last operand. -/
theorem riscvMCTarget_spec (bits address word flags t : Nat) (operands : List LLVM.MCOperand) :
    riscvMCTarget bits address word flags operands = some t ↔
      (riscvIsJal word = true ∨ flags &&& 8 ≠ 0 ∧ flags &&& 16 = 0) ∧
        ∃ d, operands.getLast? = some (.imm d) ∧ t = wrapAddress bits (Int.ofNat address + d) := by
  rw [riscv_eq, relTarget_some_iff, imm_iff]
  simp

/-- AArch64: word-scaled displacement, last operand on conditional branches, first otherwise. -/
theorem aarch64MCTarget_spec (address flags t : Nat) (operands : List LLVM.MCOperand) :
    aarch64MCTarget address flags operands = some t ↔
      directControl flags = true ∧ ∃ d,
        (if flags &&& 32 != 0 then operands.getLast? else operands.head?) = some (.imm d) ∧
        t = wrapAddress 64 (Int.ofNat address + d * 4) := by
  rw [aarch64_eq, relTarget_some_iff, imm_iff]

/-- x86: only registered pc-relative opcodes have a target, measured from the next instruction. -/
theorem x86MCTarget_spec (bits : Nat) (globals : Primus.Semantics.Environment) (next opcode t : Nat)
    (operands : List LLVM.MCOperand) :
    x86MCTarget bits globals next opcode operands = some t ↔
      globals.relativeOpcodes.contains opcode = true ∧ ∃ d, operands.head? = some (.imm d) ∧
        t = wrapAddress bits (Int.ofNat next + d) := by
  rw [x86_eq, relTarget_some_iff, imm_iff]

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
          t = wrapAddress 32 (Int.ofNat (address + 8) + d) := by
  rw [arm32_eq, relTarget_some_iff, op_imm_iff]

/-- Thumb: the pc reads as the address plus four, word-aligned for `BLX`. -/
theorem thumbTarget_spec (address t : Nat) (decoded : LLVM.Decoded) :
    thumbTarget address decoded = some t ↔
      ∃ d, thumbDisplacement decoded = some (.imm d) ∧
        t = wrapAddress 32 (Int.ofNat
          (if decoded.opcode = "tBLXi" then (address + 4) / 4 * 4 else address + 4) + d) := by
  rw [thumb_eq, relTarget_some_iff, op_imm_iff]
  simp

/-- All Thumb branches other than `BLX` keep their distance when the code moves. -/
theorem thumbTarget_shift (address k t : Nat) (decoded : LLVM.Decoded)
    (hb : decoded.opcode ≠ "tBLXi") (h : thumbTarget address decoded = some t) :
    thumbTarget (address + k) decoded = some (wrapAddress 32 ((t + k : Nat) : Int)) := by
  rw [thumb_eq] at h ⊢
  refine relTarget_shift _ _ _ _ _ _ _ (fun d => ?_) h
  simp only [hb, ite_false, Int.ofNat_eq_natCast, Int.natCast_add]
  omega

theorem arm32Target_shift (address k t : Nat) (decoded : LLVM.Decoded)
    (h : arm32Target address decoded = some t) :
    arm32Target (address + k) decoded = some (wrapAddress 32 ((t + k : Nat) : Int)) := by
  rw [arm32_eq] at h ⊢
  refine relTarget_shift _ _ _ _ _ _ _ (fun d => ?_) h
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  omega

/-- Moving a B-form or I-form branch moves a relative target. -/
theorem powerpcMCTarget_shift (bits address k word t : Nat) (operands : List LLVM.MCOperand)
    (hrel : word &&& 2 = 0) (h : powerpcMCTarget bits address word operands = some t) :
    powerpcMCTarget bits (address + k) word operands =
      some (wrapAddress bits ((t + k : Nat) : Int)) := by
  rw [powerpc_eq] at h ⊢
  refine relTarget_shift _ _ _ _ _ _ _ (fun d => ?_) h
  simp only [hrel, Int.ofNat_eq_natCast, Int.natCast_add]
  simp
  omega

theorem riscvMCTarget_shift (bits address k word flags t : Nat) (operands : List LLVM.MCOperand)
    (h : riscvMCTarget bits address word flags operands = some t) :
    riscvMCTarget bits (address + k) word flags operands =
      some (wrapAddress bits ((t + k : Nat) : Int)) := by
  rw [riscv_eq] at h ⊢
  refine relTarget_shift _ _ _ _ _ _ _ (fun d => ?_) h
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  omega

theorem aarch64MCTarget_shift (address k flags t : Nat) (operands : List LLVM.MCOperand)
    (h : aarch64MCTarget address flags operands = some t) :
    aarch64MCTarget (address + k) flags operands = some (wrapAddress 64 ((t + k : Nat) : Int)) := by
  rw [aarch64_eq] at h ⊢
  refine relTarget_shift _ _ _ _ _ _ _ (fun d => ?_) h
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  omega

theorem x86MCTarget_shift (bits : Nat) (globals : Primus.Semantics.Environment) (next k opcode t : Nat)
    (operands : List LLVM.MCOperand) (h : x86MCTarget bits globals next opcode operands = some t) :
    x86MCTarget bits globals (next + k) opcode operands =
      some (wrapAddress bits ((t + k : Nat) : Int)) := by
  rw [x86_eq] at h ⊢
  refine relTarget_shift _ _ _ _ _ _ _ (fun d => ?_) h
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  omega

/-- Register branches never get a static target on AArch64 and RISC-V. -/
theorem indirect_has_no_target (bits address word flags : Nat) (operands : List LLVM.MCOperand)
    (h : flags &&& 16 ≠ 0) (hc : flags &&& 2 = 0) (hj : riscvIsJal word = false) :
    riscvMCTarget bits address word flags operands = none ∧
      aarch64MCTarget address flags operands = none := by
  have hd : directControl flags = false := by
    lift_unfold directControl
    simp [h, hc]
  rw [riscv_eq, aarch64_eq, hd, hj]
  simp [relTarget, h]

/-! ### MIPS -/

/-- `J`, `JAL` and `JALX` replace the low 28 bits of the delay slot's address. -/
theorem mips_region_target (bits address : Nat) (decoded : LLVM.Decoded) (i : Int)
    (hj : ["J", "JAL", "JALX"].contains decoded.opcode = true)
    (hl : decoded.operands.getLast? = some (.imm i)) (hi : 0 ≤ i) (hb : i < 0x10000000)
    (hfits : (address + 4) / 0x10000000 * 0x10000000 + i.toNat < 2 ^ bits) :
    ∃ t, mipsTarget bits address decoded = some t ∧
      t % 0x10000000 = i.toNat ∧ t / 0x10000000 = (address + 4) / 0x10000000 := by
  have hx : Int.ofNat ((address + 4) / 0x10000000 * 0x10000000) + i =
      (((address + 4) / 0x10000000 * 0x10000000 + i.toNat : Nat) : Int) := by
    simp only [Int.ofNat_eq_natCast, Int.natCast_add]
    omega
  have hw : wrapAddress bits (Int.ofNat ((address + 4) / 0x10000000 * 0x10000000) + i) =
      (address + 4) / 0x10000000 * 0x10000000 + i.toNat := by
    have := wrapAddress_of_fits bits (Int.ofNat ((address + 4) / 0x10000000 * 0x10000000) + i)
      (by rw [hx]; omega) (by rw [hx]; exact_mod_cast hfits)
    rw [hx] at this ⊢
    exact_mod_cast this
  refine ⟨(address + 4) / 0x10000000 * 0x10000000 + i.toNat, ?_, ?_, ?_⟩
  · lift_unfold mipsTarget
    rw [hl]
    show (if _ then _ else _) = _
    rw [ite_eq_left hj]
    exact congrArg some hw
  · have : i.toNat < 0x10000000 := by omega
    omega
  · have : i.toNat < 0x10000000 := by omega
    omega

/-- All other direct branches and calls of MIPS, conditional or not, count from the branch: LLVM
has already added the four bytes of the delay slot. -/
theorem mips_relative_target (bits address : Nat) (decoded : LLVM.Decoded) (d : Int)
    (hj : ["J", "JAL", "JALX"].contains decoded.opcode = false)
    (hf : directControl decoded.flags = true) (hl : decoded.operands.getLast? = some (.imm d)) :
    mipsTarget bits address decoded = some (wrapAddress bits (Int.ofNat address + d)) := by
  lift_unfold mipsTarget
  rw [hl]
  have hne : ¬["J", "JAL", "JALX"].contains decoded.opcode = true := by simp only [hj]; decide
  show (if _ then _ else (if _ then _ else _)) = _
  rw [ite_eq_right hne, ite_eq_left hf]

/-- Moving a MIPS branch that counts from itself moves its target. -/
theorem mips_relative_shift (bits address k : Nat) (decoded : LLVM.Decoded) (d : Int)
    (hj : ["J", "JAL", "JALX"].contains decoded.opcode = false)
    (hf : directControl decoded.flags = true) (hl : decoded.operands.getLast? = some (.imm d)) :
    mipsTarget bits (address + k) decoded =
      some (wrapAddress bits (((wrapAddress bits (Int.ofNat address + d) + k : Nat) : Int))) := by
  rw [mips_relative_target bits _ decoded d hj hf hl, wrapAddress_add]
  congr 2
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  omega

/-- A register operand in the last place, as of `JR` and `JALR`, gives no target. -/
theorem mips_register_jump_no_target (bits address : Nat) (decoded : LLVM.Decoded) (name : String)
    (hl : decoded.operands.getLast? = some (.reg name)) :
    mipsTarget bits address decoded = none := by
  lift_unfold mipsTarget
  rw [hl]

/-- `BEQ` of a register with itself is the assembler's `b` and has no fall-through. -/
theorem mips_b_is_a_jump (assembly : String) (size flags : Nat) (r immediate : LLVM.Operand) :
    mipsFlow ⟨assembly, size, flags, "BEQ", [r, r, immediate]⟩ = .jump := by
  lift_unfold mipsFlow
  simp

/-- An instruction has a slot only if it does not fall through, or is a conditional branch and decides past the slot.
The slot of calls and other instructions that fall through is reached by that. -/
theorem mipsHasDelaySlot_no_fallthrough (insn : Insn) (h : mipsHasDelaySlot insn = true) :
    insn.fallsThrough = false ∨ insn.flow = .conditionalJump := by
  unfold mipsHasDelaySlot at h
  cases insn with
  | mk a s asm flow target bil => cases flow <;> simp_all [Insn.fallsThrough]

/-- All conditional branches have a slot, which is what makes the edge from the slot to the target exact. -/
theorem mipsHasDelaySlot_of_conditional (insn : Insn) (hf : insn.flow = .conditionalJump)
    (h1 : insn.asm.startsWith "eret" = false) (h2 : insn.asm.startsWith "deret" = false) :
    mipsHasDelaySlot insn = true := by
  unfold mipsHasDelaySlot
  rw [h1, h2]
  simp [hf]

/-- All delayed jumps without fall-through have a slot, except for the exception returns. -/
theorem mipsHasDelaySlot_of_jump (insn : Insn)
    (hf : insn.flow = .jump ∨ insn.flow = .indirectJump ∨ insn.flow = .ret)
    (h1 : insn.asm.startsWith "eret" = false) (h2 : insn.asm.startsWith "deret" = false) :
    mipsHasDelaySlot insn = true := by
  unfold mipsHasDelaySlot
  rw [h1, h2]
  rcases hf with hf | hf | hf <;> simp [hf]

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

/-- All of `arm32Flow`: `Bcc` with the condition `AL` is the plain `b`, and everything else goes by its flags, including `Bcc`
with another condition. -/
theorem arm32Flow_cases (decoded : LLVM.Decoded) :
    arm32Flow decoded = if decoded.opcode = "Bcc" ∧ decoded.operands.tail.head? = some (.imm 14) then .jump
      else flow decoded.flags := by
  obtain ⟨assembly, size, flags, opcode, operands⟩ := decoded
  lift_unfold arm32Flow
  by_cases h : opcode = "Bcc"
  · subst h
    match operands with
    | [] => simp
    | [_] => simp
    | _ :: .reg _ :: _ => simp
    | _ :: .imm value :: _ =>
      by_cases hv : value = 14
      · subst hv
        rfl
      · have hv' : (LLVM.Operand.imm value == LLVM.Operand.imm 14) = false := by simpa using hv
        simp [hv]
  · simp [h]

/-- All of `mipsFlow`, first: `BEQ` and `BEQL` of a register with itself always branch, and of two registers by the flags. -/
theorem mipsFlow_beq (assembly : String) (size flags : Nat) (opcode : String) (left right immediate : LLVM.Operand)
    (h : opcode = "BEQ" ∨ opcode = "BEQL") :
    mipsFlow ⟨assembly, size, flags, opcode, [left, right, immediate]⟩ = if left = right then .jump else flow flags := by
  rcases h with rfl | rfl <;> lift_unfold mipsFlow <;> simp

/-- `BGEZ` and `BGEZL` of the zero register always branch. -/
theorem mipsFlow_bgez (assembly : String) (size flags : Nat) (opcode zero : String) (immediate : LLVM.Operand)
    (h : opcode = "BGEZ" ∨ opcode = "BGEZL") (hz : zero = "ZERO" ∨ zero = "ZERO_64") :
    mipsFlow ⟨assembly, size, flags, opcode, [.reg zero, immediate]⟩ = .jump := by
  rcases h with rfl | rfl <;> rcases hz with rfl | rfl <;> lift_unfold mipsFlow <;> rfl

/-- Everything else goes by its flags. -/
theorem mipsFlow_other (decoded : LLVM.Decoded)
    (h1 : (decoded.opcode = "BEQ" ∨ decoded.opcode = "BEQL") → decoded.operands.length ≠ 3)
    (h2 : (decoded.opcode = "BGEZ" ∨ decoded.opcode = "BGEZL") →
      ∀ zero immediate, decoded.operands = [.reg zero, immediate] → zero ≠ "ZERO" ∧ zero ≠ "ZERO_64") :
    mipsFlow decoded = flow decoded.flags := by
  obtain ⟨assembly, size, flags, opcode, operands⟩ := decoded
  lift_unfold mipsFlow
  simp only at h1 h2
  split
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · rfl

/-! ### Writes to the pc of ARM -/

private theorem programJump_jmp (target : Bil.Exp) (rest : Bil.Program) :
    programJump (.jmp target :: rest) = some true := by
  lift_simp [programJump]

private theorem programJump_move (var : Bap.Var) (value : Bil.Exp) (rest : Bil.Program) :
    programJump (.move var value :: rest) = programJump rest := by
  lift_simp [programJump]

/-- A program with a jump at its top level always jumps. -/
theorem programJump_of_top_jmp (bil : Bil.Program) (h : ∃ target, .jmp target ∈ bil) :
    programJump bil = some true := by
  induction bil with
  | nil => simp at h
  | cons stmt rest ih =>
    have hr : (∃ target, Bil.Stmt.jmp target ∈ rest) → programJump rest = some true := ih
    have ⟨t, ht⟩ := h
    cases stmt with
    | jmp target => exact programJump_jmp _ _
    | move var value =>
      rw [programJump_move]
      exact hr ⟨t, by simpa using ht⟩
    | special message =>
      have h1 := hr ⟨t, by simpa using ht⟩
      dsimp only [programJump] at h1 ⊢
      rw [←h1]
      lift_simp [programJump]
    | cpuExn number =>
      have h1 := hr ⟨t, by simpa using ht⟩
      dsimp only [programJump] at h1 ⊢
      rw [←h1]
      lift_simp [programJump]
    | «while» condition body =>
      have h1 := hr ⟨t, by simpa using ht⟩
      dsimp only [programJump] at h1 ⊢
      lift_simp [programJump]
      simp [h1]
    | ifElse condition yes no =>
      have h1 := hr ⟨t, by simpa using ht⟩
      dsimp only [programJump] at h1 ⊢
      lift_simp [programJump]
      simp [h1]

/-- A plain program does not jump. -/
theorem programJump_moves (var : Bap.Var) (value : Bil.Exp) :
    programJump [.move var value] = none := by
  lift_simp [programJump]

/-- A jump under a condition is conditional. -/
theorem programJump_conditional (condition target : Bil.Exp) (rest : Bil.Program) :
    programJump [.ifElse condition (.jmp target :: rest) []] = some false := by
  lift_simp [programJump]

/-- An instruction that LLVM calls normal doesn't fall through when its lifted program always
jumps, e.g., `ldr pc, [sp]`, and it may fall through when it jumps under a condition. -/
theorem armControlFlow_of_jump (bil : Bil.Program) (h : programJump bil = some true) :
    armControlFlow .normal bil = .indirectJump := by
  lift_unfold armControlFlow
  dsimp only [programJump] at h
  rw [h]

theorem armControlFlow_of_conditional (flow : Flow) (bil : Bil.Program)
    (hf : flow = .normal ∨ flow = .ret ∨ flow = .indirectJump) (h : programJump bil = some false) :
    armControlFlow flow bil = .conditionalJump := by
  lift_unfold armControlFlow
  dsimp only [programJump] at h
  rw [h]
  rcases hf with rfl | rfl | rfl <;> rfl

/-- Instructions that lift to no jump are classified by their flags. -/
theorem armControlFlow_of_no_jump (flow : Flow) (bil : Bil.Program) (h : programJump bil = none) :
    armControlFlow flow bil = flow := by
  lift_unfold armControlFlow
  dsimp only [programJump] at h
  rw [h]
  cases flow <;> rfl

/-- What LLVM flags as a branch or call stays so. -/
theorem armControlFlow_keeps_branches (flow : Flow) (bil : Bil.Program)
    (hf : flow = .jump ∨ flow = .conditionalJump ∨ flow = .call ∨ flow = .barrier) :
    armControlFlow flow bil = flow := by
  lift_unfold armControlFlow
  generalize (lift% programJump) bil = jump
  rcases hf with rfl | rfl | rfl | rfl <;> cases jump <;> try rfl
  all_goals (rename_i value; cases value <;> rfl)

/-- The conditions of ARM: the codes 14 and 15 always hold. -/
theorem armCondition_always (condition : Int) :
    armCondition condition = none ↔ condition ≠ 0 ∧ condition ≠ 1 ∧ condition ≠ 2 ∧ condition ≠ 3 ∧
      condition ≠ 4 ∧ condition ≠ 5 ∧ condition ≠ 6 ∧ condition ≠ 7 ∧ condition ≠ 8 ∧ condition ≠ 9 ∧
      condition ≠ 10 ∧ condition ≠ 11 ∧ condition ≠ 12 ∧ condition ≠ 13 := by
  lift_unfold armCondition
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
      (w, b) ∈ [(1, 1), (4, 4), (8, 128), (16, 128), (32, 128), (64, 128), (128, 128), (32, 32), (32, 64), (64, 64)] := by
  lift_unfold aarch64Register
  dsimp only
  generalize (if name = "LR" then "X30" else if name = "FP" then "X29" else name) = canonical
  repeat' refine shape_ite ?_ ?_
  · exact ⟨_, _, _, rfl, by decide⟩
  · exact ⟨_, _, _, rfl, by decide⟩
  · split
    · rename_i register h
      revert h
      unfold_status
      split <;> first
        | (intro h; cases h; exact ⟨_, _, _, rfl, by decide⟩)
        | (intro h; cases h)
    · repeat' refine shape_ite ?_ ?_
      all_goals exact ⟨_, _, _, rfl, by decide⟩

/-- The vector registers have their architectural widths, and XMM is the low half of YMM. -/
theorem x86VectorRegister_shape (name : String) (value : PValue)
    (h : x86VectorRegister name = some value) :
    ∃ n w b, value = register n w b ∧ (w, b) ∈ [(128, 256), (256, 256), (512, 512)] := by
  lift_unfold x86VectorRegister at h
  split at h
  all_goals first
    | cases h
    | (split at h
       · cases h
         exact ⟨_, _, _, rfl, by decide⟩
       · cases h)

private theorem vector_getD {P : Nat → Nat → Prop} (name : String) (fallback : PValue)
    (hd : ∃ n w b, fallback = register n w b ∧ P w b)
    (hv : P 128 256 ∧ P 256 256 ∧ P 512 512) :
    ∃ n w b, (x86VectorRegister name).getD fallback = register n w b ∧ P w b := by
  cases h : x86VectorRegister name with
  | none => exact hd
  | some value =>
    have ⟨n, w, b, he, hm⟩ := x86VectorRegister_shape name value h
    refine ⟨n, w, b, he, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hv.1
    · exact hv.2.1
    · exact hv.2.2

/-- The registers that the semantics see as vectors. -/
theorem x86_vector_views :
    x86Register "XMM0" = register "YMM0" 128 256 ∧ x86Register "XMM15" = register "YMM15" 128 256 ∧
      x86Register "YMM3" = register "YMM3" 256 256 ∧ x86Register "ZMM4" = register "ZMM4" 512 512 ∧
      x8632Register "XMM7" = register "YMM7" 128 256 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The registers of x87 have 80 bits, the control words 16, and MXCSR and EFLAGS 32, as they have no bases. -/
private theorem float_shape {P : Nat → Nat → Prop} (name : String) (value : PValue)
    (h : (lift% x86FloatRegister) name = some value) (hp : P 80 80 ∧ P 16 16 ∧ P 32 32) :
    ∃ n w b, value = register n w b ∧ P w b := by
  unfold_float at h
  repeat' split at h
  all_goals first
    | cases h
      first
        | exact ⟨_, 80, 80, rfl, hp.1⟩
        | exact ⟨_, 16, 16, rfl, hp.2.1⟩
        | exact ⟨_, 32, 32, rfl, hp.2.2⟩
    | cases h

theorem x86Register_shape (name : String) :
    ∃ n w b, x86Register name = register n w b ∧
      (w, b) ∈ [(1, 1), (8, 8), (8, 64), (16, 16), (16, 64), (32, 32), (32, 64), (64, 64), (80, 80), (128, 256),
        (256, 256), (512, 512)] := by
  lift_unfold x86Register
  simp only []
  generalize hc : (if (name.isEmpty || decide (name = "NoRegister")) = true then "Nil" else name) = c
  split
  · exact ⟨c, 1, 1, rfl, by decide⟩
  · split
    · exact ⟨c, 8, 8, rfl, by decide⟩
    · cases hl : x86LowRegister c with
      | none =>
        dsimp only [x86LowRegister] at hl
        rw [hl]
        dsimp only
        split
        · exact float_shape _ _ (by assumption) (by decide)
        · exact vector_getD c _ ⟨c, 64, 64, rfl, by decide⟩ (by decide)
      | some pair =>
        obtain ⟨base, width⟩ := pair
        have hw := (x86LowRegister_spec _ _ _ hl).1
        refine ⟨base, width, 64, ?_, ?_⟩
        · dsimp only [x86LowRegister] at hl
          rw [hl]
        · rcases hw with rfl | rfl | rfl <;> decide

theorem x8632Register_shape (name : String) :
    ∃ n w b, x8632Register name = register n w b ∧
      (w, b) ∈ [(1, 1), (8, 8), (8, 32), (16, 16), (16, 32), (32, 32), (80, 80), (128, 256), (256, 256),
        (512, 512)] := by
  lift_unfold x8632Register
  simp only []
  generalize (if (name.isEmpty || decide (name = "NoRegister")) = true then "Nil" else name) = c
  repeat' split
  all_goals first
    | exact ⟨_, 1, _, rfl, by decide⟩
    | exact ⟨_, 8, _, rfl, by decide⟩
    | exact ⟨_, 16, _, rfl, by decide⟩
    | exact float_shape _ _ (by assumption) (by decide)
    | exact vector_getD c _ ⟨c, 32, 32, rfl, by decide⟩ (by decide)

theorem arm32Register_shape (name : String) :
    ∃ n w, arm32Register name = register n w w ∧ (w = 1 ∨ w = 32 ∨ w = 64 ∨ w = 128) := by
  lift_unfold arm32Register
  simp only []
  repeat' split
  all_goals exact ⟨_, _, rfl, by simp⟩

theorem powerpcRegister_shape (name : String) :
    ∃ n w, powerpcRegister name = register n w w ∧ (w = 1 ∨ w = 4 ∨ w = 64) := by
  lift_unfold powerpcRegister
  simp only []
  repeat' split
  all_goals exact ⟨_, _, rfl, by decide⟩

theorem powerpc32Register_shape (name : String) :
    ∃ n w, powerpc32Register name = register n w w ∧ (w = 1 ∨ w = 4 ∨ w = 32) := by
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

/-- The 32-bit and 64-bit MIPS tables differ in width only, but for the condition codes, which are bits. -/
theorem mipsRegister_widths (name : String) (h : (lift% mipsConditionCode) name = false) :
    ∃ n, mipsRegister name = register n 64 64 ∧ mips32Register name = register n 32 32 := by
  refine ⟨mipsCanonicalName name, ?_, ?_⟩
  · lift_unfold mipsRegister
    simp [h]
  · lift_unfold mips32Register
    simp [h]

theorem mips_condition_codes :
    mipsRegister "FCC0" = register "FCC0" 1 1 ∧ mips32Register "FCC7" = register "FCC7" 1 1 := ⟨rfl, rfl⟩

/-- Register names outside the special classes pass through the table unchanged. -/
theorem arm32Register_name (name : String) (h1 : name ≠ "") (h2 : name ≠ "NoRegister") :
    ∃ w, arm32Register name = register name w w := by
  lift_unfold arm32Register
  have he : name.isEmpty = false := by simpa using h1
  simp only [he, h2, Bool.false_or, decide_false, Bool.false_eq_true, ite_false]
  repeat' split
  all_goals first
    | exact ⟨_, rfl⟩
    | exact ⟨64, rfl⟩
    | exact ⟨32, rfl⟩

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

/-- Reads of an alias are its value. -/
theorem alias_read (aliases : String → Option Alias) (var : Bap.Var) (alias : Alias)
    (h : aliases var.name = some alias) : aliasExp aliases (.var var) = aliasRead alias := by
  dsimp only [aliasExp]
  unfold_alias_exp
  simp [h]

/-- Writes of an alias are the writes of its parts. -/
theorem alias_write (aliases : String → Option Alias) (var : Bap.Var) (alias : Alias) (value : Bil.Exp)
    (rest : Bil.Program) (h : aliases var.name = some alias) :
    resolveAliases aliases (.move var value :: rest) =
      aliasWrite var.typ (aliasExp aliases value) alias ++ resolveAliases aliases rest := by
  dsimp only [resolveAliases]
  unfold_resolve
  simp [h]

/-- A program without aliases is not changed: moves to other registers keep their targets. -/
theorem alias_write_other (aliases : String → Option Alias) (var : Bap.Var) (value : Bil.Exp) (rest : Bil.Program)
    (h : aliases var.name = none) :
    resolveAliases aliases (.move var value :: rest) =
      .move var (aliasExp aliases value) :: resolveAliases aliases rest := by
  dsimp only [resolveAliases]
  unfold_resolve
  simp [h]

private theorem highByte_alias (base : String → Option String) (width : Nat) (name base' : String)
    (h : base name = some base') (hflags : name ≠ "EFLAGS") :
    x86Aliases base width name = some (⟨base', width, 15, 8⟩, []) := by
  lift_unfold x86Aliases
  simp [h, hflags]

/-- Reads of a high byte are bits 15 to 8 of the base. -/
theorem highBytes_read (base : String → Option String) (width : Nat) (var : Bap.Var) (name : String)
    (h : base var.name = some name) (hflags : var.name ≠ "EFLAGS") :
    aliasExp (x86Aliases base width) (.var var) = .extract 15 8 (.var ⟨name, .imm width, 0, false⟩) := by
  rw [alias_read _ _ _ (highByte_alias base width _ _ h hflags)]
  simp [aliasRead, AliasPart.read, AliasPart.var]

/-- Writes of a high byte keep the other bits of the base. -/
theorem highBytes_write (base : String → Option String) (width : Nat) (var : Bap.Var)
    (name : String) (value : Bil.Exp) (rest : Bil.Program) (h : base var.name = some name)
    (hflags : var.name ≠ "EFLAGS") (hwidth : 16 < width) :
    resolveAliases (x86Aliases base width) (.move var value :: rest) =
      .move ⟨name, .imm width, 0, false⟩
        (.concat (.extract (width - 1) 16 (.var ⟨name, .imm width, 0, false⟩))
          (.concat (aliasExp (x86Aliases base width) value)
            (.extract 7 0 (.var ⟨name, .imm width, 0, false⟩)))) ::
        resolveAliases (x86Aliases base width) rest := by
  rw [alias_write _ _ _ _ _ (highByte_alias base width _ _ h hflags)]
  simp [aliasWrite, AliasPart.write, AliasPart.var, hwidth]

/-- A move to another register than a high byte or EFLAGS keeps its target. -/
theorem highBytes_write_other (base : String → Option String) (width : Nat) (var : Bap.Var)
    (value : Bil.Exp) (rest : Bil.Program) (h : base var.name = none) (hflags : var.name ≠ "EFLAGS") :
    resolveAliases (x86Aliases base width) (.move var value :: rest) =
      .move var (aliasExp (x86Aliases base width) value) :: resolveAliases (x86Aliases base width) rest := by
  apply alias_write_other
  lift_unfold x86Aliases
  simp [h, hflags]

/-- Canonicalising a MIPS register name twice is the same as doing it once. -/
theorem mipsRegisterName_idempotent (name : String) :
    mipsRegisterName (mipsRegisterName name) = mipsRegisterName name := by
  by_cases h : name ∈ ["R0", "ZERO", "$zero", "AT", "V0", "V1", "A0", "A1", "A2", "A3", "T0", "T1", "T2", "T3", "T4", "T5", "T6", "T7", "S0", "S1", "S2", "S3", "S4", "S5", "S6", "S7", "T8", "T9", "K0", "K1", "GP", "SP", "FP", "S8", "RA", "$ra"]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hfix : mipsRegisterName name = name := by
      lift_unfold mipsRegisterName
      split <;> simp_all
    rw [hfix, hfix]

/-! ### Register bindings of the semantic environments -/

set_option maxRecDepth 20000 in
/-- `riscvGlobals` binds each `Xn` for n below 32, once. -/
theorem riscvGlobals_keys : (riscvGlobals.map (·.1)).Nodup ∧ riscvGlobals.length = 66 :=
  ⟨by decide +kernel, rfl⟩

set_option maxRecDepth 20000 in
theorem riscv32Globals_keys : (riscv32Globals.map (·.1)).Nodup ∧ riscv32Globals.length = 66 :=
  ⟨by decide +kernel, rfl⟩

set_option maxRecDepth 20000 in
theorem x86Globals_keys : (x86Globals.map (·.1)).Nodup ∧ x86Globals.length = 92 := ⟨by decide +kernel, rfl⟩

set_option maxRecDepth 20000 in
theorem x8632Globals_keys : (x8632Globals.map (·.1)).Nodup ∧ x8632Globals.length = 64 :=
  ⟨by decide +kernel, rfl⟩

set_option maxRecDepth 20000 in
theorem arm32Globals_keys : (arm32Globals.map (·.1)).Nodup ∧ arm32Globals.length = 61 :=
  ⟨by decide +kernel, rfl⟩

set_option maxRecDepth 20000 in
theorem mipsGlobals_keys : (mipsGlobals.map (·.1)).Nodup ∧ mipsGlobals.length = 77 :=
  ⟨by decide +kernel, rfl⟩

set_option maxRecDepth 20000 in
theorem mips32Globals_keys : (mips32Globals.map (·.1)).Nodup ∧ mips32Globals.length = 77 :=
  ⟨by decide +kernel, rfl⟩

set_option maxRecDepth 20000 in
theorem powerpcGlobals_keys : (powerpcGlobals.map (·.1)).Nodup ∧ powerpcGlobals.length = 85 :=
  ⟨by decide +kernel, rfl⟩

set_option maxRecDepth 20000 in
theorem powerpc32Globals_keys : (powerpc32Globals.map (·.1)).Nodup ∧ powerpc32Globals.length = 85 :=
  ⟨by decide +kernel, rfl⟩

set_option maxRecDepth 100000 in
theorem aarch64Globals_keys : (aarch64Globals.map (·.1)).Nodup ∧ aarch64Globals.length = 210 :=
  ⟨by decide +kernel, rfl⟩


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

/-! ### Loads and stores of multiple registers of ARM -/

private abbrev armMultiple : Nat → Primus.Semantics.Context → LLVM.Decoded → Option Bil.Program :=
  lift% armMultiple
private abbrev ArmMultipleKind := ArmMultiple
private abbrev armMultipleOperands : String → List LLVM.Operand →
    Option (Bool × ArmMultipleKind × Bool × String × Int × List String) := lift% armMultipleOperands

private theorem operand_names (g : LLVM.Operand → Option String) (hg : ∀ n, g (.reg n) = some n)
    (names : List String) : (names.map LLVM.Operand.reg).mapM g = some names := by
  induction names with
  | nil => rfl
  | cons name rest ih => simp only [List.map_cons, List.mapM_cons, ih, hg]; rfl

/-- `pop` has the condition and the list of registers as its operands, from the stack pointer. -/
theorem pop_operands (condition : Int) (predicate : LLVM.Operand) (names : List String) :
    armMultipleOperands "tPOP" (.imm condition :: predicate :: names.map .reg) =
      some (true, ArmMultiple.increaseAfter, true, "SP", condition, names) := by
  lift_unfold armMultipleOperands
  show Option.map _ (List.mapM _ _) = _
  rw [operand_names _ fun _ => rfl]
  rfl

private theorem programJump_all_moves (bil : Bil.Program)
    (h : ∀ stmt ∈ bil, ∃ var value, stmt = .move var value) : programJump bil = none := by
  induction bil with
  | nil =>
    lift_simp [programJump]
  | cons stmt rest ih =>
    have ⟨var, value, he⟩ := h stmt (by simp)
    subst he
    rw [programJump_move]
    exact ih fun s hs => h s (List.mem_cons_of_mem _ hs)

private theorem mem_indexed {α} (list : List α) (x : α) (h : x ∈ list) :
    ∃ i, (i, x) ∈ (List.range list.length).zip list := by
  have ⟨i, hi, he⟩ := List.getElem_of_mem h
  refine ⟨i, ?_⟩
  have hlen : i < ((List.range list.length).zip list).length := by simpa using hi
  have := List.getElem_mem hlen
  simpa [he] using this

/-- A load of multiple registers that holds PC always jumps, if its condition always holds, which
is why `pop {r0, pc}` and `ldm r0, {pc}` have no fall-through. -/
theorem armMultiple_load_pc (pc : Nat) (context : Primus.Semantics.Context) (decoded : LLVM.Decoded)
    (addressing : ArmMultipleKind) (writeback : Bool) (base : String) (condition : Int)
    (list : List String)
    (h : armMultipleOperands decoded.opcode decoded.operands =
      some (true, addressing, writeback, base, condition, list))
    (hc : armCondition condition = none) (hpc : "PC" ∈ list) :
    ∃ bil, armMultiple pc context decoded = some bil ∧ programJump bil = some true := by
  dsimp only [armMultipleOperands, armCondition] at h hc
  lift_unfold armMultiple
  rw [h]
  refine ⟨_, rfl, ?_⟩
  dsimp only
  rw [hc]
  unfold armMultipleBody
  dsimp only
  refine programJump_of_top_jmp _ ?_
  have ⟨i, hi⟩ := mem_indexed list "PC" hpc
  simp only [↓reduceIte, List.mem_cons, List.mem_append, List.mem_map, reduceCtorEq, false_or]
  exact ⟨_, .inr ⟨(i, "PC"), hi, ite_eq_left rfl⟩⟩

/-- A load of multiple registers without PC, as `pop {r0}`, has no jump and falls through. -/
theorem armMultiple_load_no_pc (pc : Nat) (context : Primus.Semantics.Context) (decoded : LLVM.Decoded)
    (addressing : ArmMultipleKind) (writeback : Bool) (base : String) (condition : Int)
    (list : List String)
    (h : armMultipleOperands decoded.opcode decoded.operands =
      some (true, addressing, writeback, base, condition, list))
    (hc : armCondition condition = none) (hpc : "PC" ∉ list) :
    ∃ bil, armMultiple pc context decoded = some bil ∧ programJump bil = none := by
  dsimp only [armMultipleOperands, armCondition] at h hc
  lift_unfold armMultiple
  rw [h]
  refine ⟨_, rfl, ?_⟩
  dsimp only
  rw [hc]
  unfold armMultipleBody
  dsimp only
  refine programJump_all_moves _ ?_
  intro stmt hs
  rcases List.mem_cons.1 hs with rfl | hs
  · exact ⟨_, _, rfl⟩
  rcases List.mem_append.1 hs with hs | hs
  · cases writeback <;> simp at hs
    subst hs
    exact ⟨_, _, rfl⟩
  · rcases List.mem_map.1 hs with ⟨⟨i, name⟩, hm, rfl⟩
    have hname : name ∈ list := (List.of_mem_zip hm).2
    have hne : name ≠ "PC" := fun he => hpc (he ▸ hname)
    simp only [hne, ite_false]
    exact ⟨_, _, rfl⟩

/-- A store of multiple registers never jumps, even if PC is on the list. -/
theorem armMultiple_store (pc : Nat) (context : Primus.Semantics.Context) (decoded : LLVM.Decoded)
    (addressing : ArmMultipleKind) (writeback : Bool) (base : String) (condition : Int)
    (list : List String)
    (h : armMultipleOperands decoded.opcode decoded.operands =
      some (false, addressing, writeback, base, condition, list))
    (hc : armCondition condition = none) :
    ∃ bil, armMultiple pc context decoded = some bil ∧ programJump bil = none := by
  dsimp only [armMultipleOperands, armCondition] at h hc
  lift_unfold armMultiple
  rw [h]
  refine ⟨_, rfl, ?_⟩
  dsimp only
  rw [hc]
  unfold armMultipleBody
  dsimp only
  refine programJump_all_moves _ ?_
  intro stmt hs
  rcases List.mem_cons.1 hs with rfl | hs
  · exact ⟨_, _, rfl⟩
  rcases List.mem_append.1 hs with hs | hs
  · rcases List.mem_map.1 hs with ⟨_, _, rfl⟩
    exact ⟨_, _, rfl⟩
  · cases writeback <;> simp at hs
    subst hs
    exact ⟨_, _, rfl⟩

/-- `pop {.., pc}` is classified as an indirect jump, with no fall-through. -/
theorem pop_pc_is_indirect (pc : Nat) (context : Primus.Semantics.Context) (assembly : String)
    (size flags : Nat) (predicate : LLVM.Operand) (names : List String) (hpc : "PC" ∈ names) :
    ∃ bil, armMultiple pc context
        ⟨assembly, size, flags, "tPOP", .imm 14 :: predicate :: names.map .reg⟩ = some bil ∧
      armControlFlow .normal bil = .indirectJump := by
  have ⟨bil, h1, h2⟩ := armMultiple_load_pc pc context
    ⟨assembly, size, flags, "tPOP", .imm 14 :: predicate :: names.map .reg⟩ _ _ _ 14 names
    (pop_operands 14 predicate names) rfl hpc
  exact ⟨bil, h1, armControlFlow_of_jump bil h2⟩

/-! ### What a load or store of multiple registers does

The Lean evaluator of Primus semantics has no definitions by arity, so these instructions are built by `armMultiple`, and
this is what the programs it builds compute. Each register is at its own address and the base is written back. -/

/-- A general purpose register of ARM. -/
private abbrev armVar (name : String) : Bap.Var := ⟨name, .imm 32, 0, false⟩

/-- The lowest address of the transfer of `size` bytes, from the base. -/
def armFirstAddress (addressing : ArmMultiple) (base : BitVec 32) (size : Nat) : BitVec 32 :=
  match addressing with
  | .increaseAfter => base
  | .increaseBefore => base + BitVec.ofNat 32 4
  | .decreaseAfter => base + BitVec.ofNat 32 4 - BitVec.ofNat 32 size
  | .decreaseBefore => base - BitVec.ofNat 32 size

/-- The base written back: past the registers, whichever way it goes. -/
def armAfterAddress (addressing : ArmMultiple) (base : BitVec 32) (size : Nat) : BitVec 32 :=
  match addressing with
  | .increaseAfter | .increaseBefore => base + BitVec.ofNat 32 size
  | .decreaseAfter | .decreaseBefore => base - BitVec.ofNat 32 size

private theorem eval_add_int {env : Bil.Env} {a : Bil.Exp} {f : BitVec 32} (c : Nat) (h : Bil.evalExp env a = .ok (.bits f)) :
    Bil.evalExp env (.bin .add a (armWord c)) = .ok (.bits (f + BitVec.ofNat 32 c)) := by
  simp only [Bil.evalExp, armWord, h]
  rfl

private theorem eval_sub_int {env : Bil.Env} {a : Bil.Exp} {f : BitVec 32} (c : Nat) (h : Bil.evalExp env a = .ok (.bits f)) :
    Bil.evalExp env (.bin .sub a (armWord c)) = .ok (.bits (f - BitVec.ofNat 32 c)) := by
  simp only [Bil.evalExp, armWord, h]
  rfl

private theorem eval_first {env : Bil.Env} {b : BitVec 32} (addressing : ArmMultiple) (size : Nat)
    (h : Bil.lookup env armMultipleBase = .ok (.bits b)) :
    Bil.evalExp env (armMultipleFirst addressing size) = .ok (.bits (armFirstAddress addressing b size)) := by
  have hv : Bil.evalExp env (.var armMultipleBase) = .ok (.bits b) := h
  cases addressing
  · exact hv
  · exact eval_add_int _ hv
  · exact eval_sub_int _ (eval_add_int _ hv)
  · exact eval_sub_int _ hv

private theorem eval_after {env : Bil.Env} {b : BitVec 32} (addressing : ArmMultiple) (size : Nat)
    (h : Bil.lookup env armMultipleBase = .ok (.bits b)) :
    Bil.evalExp env (armMultipleAfter addressing size) = .ok (.bits (armAfterAddress addressing b size)) := by
  have hv : Bil.evalExp env (.var armMultipleBase) = .ok (.bits b) := h
  cases addressing
  · exact eval_add_int _ hv
  · exact eval_add_int _ hv
  · exact eval_sub_int _ hv
  · exact eval_sub_int _ hv

private theorem exec_move {fuel : Nat} {state : Bil.State} {var : Bap.Var} {exp : Bil.Exp} {value : Bap.Value} {rest : Bil.Program}
    (he : Bil.evalExp state.env exp = .ok value) :
    Bil.execProgram (fuel + 2) state (.move var exp :: rest) =
      Bil.execProgram (fuel + 1) { env := Bil.bind state.env var value } rest := by
  rw [Bil.execProgram, Bil.execStmt]
  simp only [Bil.execExp, he, bind, Except.bind]

private theorem lookup_bind_same (env : Bil.Env) (var : Bap.Var) (value : Bap.Value) :
    Bil.lookup (Bil.bind env var value) var = .ok value := by
  simp [Bil.lookup, Bil.bind]

private theorem lookup_bind_ne (env : Bil.Env) {var other : Bap.Var} (value : Bap.Value) (h : other ≠ var) :
    Bil.lookup (Bil.bind env var value) other = Bil.lookup env other :=
  Bap.Proofs.Bil.lookup_bind_other env value h

/-- The loads in order, each from its own address. -/
private def armLoads (first : Bil.Exp) (memory : Bap.Var) (endian : Endian) (entries : List (Nat × String)) : Bil.Program :=
  entries.map fun entry =>
    .move (armVar entry.2) (.load (.var memory) (.bin .add first (armWord (4 * entry.1))) endian 4)

private theorem exec_loads {first : Bil.Exp} {memory : Bap.Var} {endian : Endian} {m : Memory 32} {f : BitVec 32} :
    ∀ (entries : List (Nat × String)) (fuel : Nat) (state : Bil.State) (rest : Bil.Program),
      (∀ entry ∈ entries, armVar entry.2 ≠ memory) →
      (entries.map Prod.snd).Nodup →
      (∀ env : Bil.Env, (∀ var, var ∉ entries.map (armVar ·.2) → Bil.lookup env var = Bil.lookup state.env var) →
        Bil.evalExp env first = .ok (.bits f)) →
      Bil.lookup state.env memory = .ok (.memory m) →
      ∃ state', Bil.execProgram (fuel + entries.length + 2) state (armLoads first memory endian entries ++ rest) =
          Bil.execProgram (fuel + 2) state' rest ∧
        (∀ entry ∈ entries, Bil.lookup state'.env (armVar entry.2) =
          .ok (.bits (Memory.read m (f + BitVec.ofNat 32 (4 * entry.1)) endian 4))) ∧
        ∀ var, var ∉ entries.map (armVar ·.2) → Bil.lookup state'.env var = Bil.lookup state.env var
  | [], fuel, state, rest, _, _, _, _ => ⟨state, rfl, by simp, fun _ _ => rfl⟩
  | entry :: entries, fuel, state, rest, hne, hnd, hfirst, hm => by
    have hfirst' := hfirst state.env (fun _ _ => rfl)
    have hmem : Bil.evalExp state.env (.var memory) = .ok (.memory m) := hm
    have haddr := eval_add_int (4 * entry.1) hfirst'
    have hload : Bil.evalExp state.env
        (.load (.var memory) (.bin .add first (armWord (4 * entry.1))) endian 4) =
        .ok (.bits (Memory.read m (f + BitVec.ofNat 32 (4 * entry.1)) endian 4)) :=
      Bap.Proofs.Bil.eval_load_iff.2 ⟨32, m, _, hmem, haddr, rfl⟩
    have hstep : Bil.execProgram (fuel + (entry :: entries).length + 2) state
        (armLoads first memory endian (entry :: entries) ++ rest) =
        Bil.execProgram (fuel + entries.length + 2)
          { env := Bil.bind state.env (armVar entry.2) (.bits (Memory.read m (f + BitVec.ofNat 32 (4 * entry.1)) endian 4)) }
          (armLoads first memory endian entries ++ rest) := by
      have e : fuel + (entry :: entries).length + 2 = (fuel + entries.length + 1) + 2 := by
        simp only [List.length_cons]
        omega
      rw [e]
      exact exec_move hload
    rw [hstep]
    have hnd' := List.nodup_cons.1 (by simpa using hnd : (entry.2 :: entries.map Prod.snd).Nodup)
    have ⟨state', he, hl, ho⟩ := exec_loads (endian := endian) (m := m) (f := f) (first := first) (memory := memory) entries fuel
      { env := Bil.bind state.env (armVar entry.2) (.bits (Memory.read m (f + BitVec.ofNat 32 (4 * entry.1)) endian 4)) } rest
      (fun e h => hne e (List.mem_cons_of_mem _ h)) hnd'.2
      (fun env hsame => hfirst env fun var hvar => by
        rw [hsame var (fun h => hvar (List.mem_cons_of_mem _ h))]
        exact lookup_bind_ne _ _ (fun h => hvar (by rw [h]; simp)))
      (by
        show Bil.lookup (Bil.bind _ _ _) memory = _
        exact (lookup_bind_ne _ _ (Ne.symm (hne entry (by simp)))).trans hm)
    refine ⟨state', he, ?_, ?_⟩
    · intro e hme
      rcases List.mem_cons.1 hme with rfl | hme
      · have hnot : armVar e.2 ∉ entries.map (armVar ·.2) := by
          intro h
          rcases List.mem_map.1 h with ⟨o, ho', hequal⟩
          apply hnd'.1
          have : o.2 = e.2 := by
            have := congrArg Bap.Var.name hequal
            simpa using this
          exact List.mem_map.2 ⟨o, ho', this⟩
        rw [ho _ hnot]
        exact lookup_bind_same _ _ _
      · exact hl e hme
    · intro var hvar
      rw [ho var (fun h => hvar (List.mem_cons_of_mem _ h))]
      exact lookup_bind_ne _ _ (fun h => hvar (by rw [h]; simp))

/-- `LDM` and its relatives, evaluated: each register holds the word at its address, the lowest register at the lowest
address; the base is written back if it is not loaded, and a loaded base keeps the loaded value; memory and every other
register stay. -/
theorem armMultipleBody_load_eval (pc : Nat) (context : Primus.Semantics.Context)
    (addressing : ArmMultiple) (writeback : Bool) (base : String) (list : List String)
    (hpc : "PC" ∉ list) (hnd : list.Nodup)
    (hn : armMultipleBase.name ∉ list) (hbn : base ≠ armMultipleBase.name)
    (hmem : context.memory.typ ≠ .imm 32) (fuel : Nat)
    {env : Bil.Env} {b : BitVec 32} {m : Memory 32}
    (hbase : Bil.lookup env (armVar base) = .ok (.bits b)) (hm : Bil.lookup env context.memory = .ok (.memory m)) :
    let first := armFirstAddress addressing b (4 * list.length)
    ∃ state', Bil.execProgram (fuel + list.length + 5) { env := env }
        (armMultipleBody pc context true addressing writeback base list) = .ok (state', .normal) ∧
      (∀ entry ∈ (List.range list.length).zip list, Bil.lookup state'.env (armVar entry.2) =
        .ok (.bits (Memory.read m (first + BitVec.ofNat 32 (4 * entry.1)) context.endian 4))) ∧
      (writeback = true → base ∉ list →
        Bil.lookup state'.env (armVar base) = .ok (.bits (armAfterAddress addressing b (4 * list.length)))) ∧
      (writeback = false → base ∉ list → Bil.lookup state'.env (armVar base) = .ok (.bits b)) ∧
      Bil.lookup state'.env context.memory = .ok (.memory m) ∧
      ∀ var, var ≠ armMultipleBase → var ≠ armVar base → (∀ name ∈ list, var ≠ armVar name) →
        Bil.lookup state'.env var = Bil.lookup env var := by
  intro first
  have hne : ∀ name, armVar name ≠ context.memory := fun name he => hmem (by rw [← he])
  have hbvm : armMultipleBase ≠ context.memory := fun he => hmem (by rw [← he]; rfl)
  have hbv : armVar base ≠ armMultipleBase := fun he => hbn (congrArg Bap.Var.name he)
  have hnames : ∀ name ∈ list, armVar name ≠ armMultipleBase := fun name hin he =>
    hn ((congrArg Bap.Var.name he) ▸ hin)
  let entries := (List.range list.length).zip list
  have hsnd : entries.map Prod.snd = list := by
    simp [entries, List.map_snd_zip]
  have hmemEntries : ∀ entry ∈ entries, entry.2 ∈ list := fun entry he =>
    hsnd ▸ List.mem_map.2 ⟨entry, he, rfl⟩
  have hnotPc : ∀ entry ∈ entries, entry.2 ≠ "PC" := fun entry he hp => hpc (hp ▸ hmemEntries entry he)
  have hprogram : ((List.range list.length).zip list).map (fun (x : Nat × String) =>
      (if x.2 = "PC" then Bil.Stmt.jmp (.bin .and (.load (.var context.memory)
          (.bin .add (armMultipleFirst addressing (4 * list.length)) (armWord (4 * x.1))) context.endian 4) (armWord 0xfffffffe))
        else .move ⟨x.2, .imm 32, 0, false⟩ (.load (.var context.memory)
          (.bin .add (armMultipleFirst addressing (4 * list.length)) (armWord (4 * x.1))) context.endian 4))) =
      armLoads (armMultipleFirst addressing (4 * list.length)) context.memory context.endian entries := by
    apply List.map_congr_left
    intro x hx
    rw [ite_eq_right (hnotPc x hx)]
  have hbody : armMultipleBody pc context true addressing writeback base list =
      .move armMultipleBase (.var (armVar base)) ::
        ((if writeback then [.move (armVar base) (armMultipleAfter addressing (4 * list.length))] else []) ++
          (armLoads (armMultipleFirst addressing (4 * list.length)) context.memory context.endian entries ++ [])) := by
    rw [List.append_nil, ← hprogram]
    rfl
  rw [hbody]
  have h1 : Bil.evalExp env (.var (armVar base)) = .ok (.bits b) := hbase
  have step1 := exec_move (fuel := fuel + list.length + 3) (state := { env := env }) (var := armMultipleBase)
    (rest := (if writeback then [.move (armVar base) (armMultipleAfter addressing (4 * list.length))] else []) ++
      (armLoads (armMultipleFirst addressing (4 * list.length)) context.memory context.endian entries ++ [])) h1
  have e1 : fuel + list.length + 5 = fuel + list.length + 3 + 2 := by omega
  rw [e1, step1]
  have hB1 : Bil.lookup (Bil.bind env armMultipleBase (.bits b)) armMultipleBase = .ok (.bits b) := lookup_bind_same ..
  have hAfter := eval_after (env := Bil.bind env armMultipleBase (.bits b)) addressing (4 * list.length) hB1
  -- the state before the loads, whether it writes back or not
  obtain ⟨state1, fuel1, hstate, hBs, hMs, hOther, hBase⟩ : ∃ (state1 : Bil.State) (fuel1 : Nat),
      Bil.execProgram (fuel + list.length + 3 + 1) { env := Bil.bind env armMultipleBase (.bits b) }
          ((if writeback then [.move (armVar base) (armMultipleAfter addressing (4 * list.length))] else []) ++
            (armLoads (armMultipleFirst addressing (4 * list.length)) context.memory context.endian entries ++ [])) =
        Bil.execProgram (fuel1 + entries.length + 2) state1
          (armLoads (armMultipleFirst addressing (4 * list.length)) context.memory context.endian entries ++ []) ∧
      Bil.lookup state1.env armMultipleBase = .ok (.bits b) ∧
      Bil.lookup state1.env context.memory = .ok (.memory m) ∧
      (∀ var, var ≠ armMultipleBase → var ≠ armVar base → Bil.lookup state1.env var = Bil.lookup env var) ∧
      Bil.lookup state1.env (armVar base) =
        .ok (.bits (if writeback then armAfterAddress addressing b (4 * list.length) else b)) := by
    have hlen : entries.length = list.length := by simp [entries]
    have hmem1 : Bil.lookup (Bil.bind env armMultipleBase (.bits b)) context.memory = .ok (.memory m) := by
      exact (lookup_bind_ne _ _ (Ne.symm hbvm)).trans hm
    cases writeback with
    | true =>
      let written : Bap.Value := .bits (armAfterAddress addressing b (4 * list.length))
      refine ⟨{ env := Bil.bind (Bil.bind env armMultipleBase (.bits b)) (armVar base) written }, fuel + 1, ?_, ?_, ?_, ?_, ?_⟩
      · have e : fuel + list.length + 3 + 1 = (fuel + list.length + 2) + 2 := by omega
        rw [e]
        simp only [ite_true, List.singleton_append]
        rw [exec_move (state := { env := Bil.bind env armMultipleBase (.bits b) }) (var := armVar base) hAfter, hlen]
        have : fuel + 1 + list.length + 2 = fuel + list.length + 2 + 1 := by omega
        rw [this]
      · show Bil.lookup (Bil.bind _ _ _) armMultipleBase = _
        exact (lookup_bind_ne _ _ (Ne.symm hbv)).trans hB1
      · show Bil.lookup (Bil.bind _ _ _) context.memory = _
        exact (lookup_bind_ne _ _ (Ne.symm (hne base))).trans hmem1
      · intro var h1 h2
        show Bil.lookup (Bil.bind _ _ _) var = _
        exact (lookup_bind_ne _ _ h2).trans (lookup_bind_ne _ _ h1)
      · exact lookup_bind_same ..
    | false =>
      refine ⟨{ env := Bil.bind env armMultipleBase (.bits b) }, fuel + 2, ?_, hB1, hmem1, ?_, ?_⟩
      · simp only [Bool.false_eq_true, ite_false, List.nil_append]
        rw [hlen, show fuel + list.length + 3 + 1 = fuel + 2 + list.length + 2 by omega]
      · intro var h1 _
        exact lookup_bind_ne _ _ h1
      · simp only [Bool.false_eq_true, ite_false]
        show Bil.lookup (Bil.bind _ _ _) _ = _
        exact (lookup_bind_ne _ _ hbv).trans hbase
  have hnd' : (entries.map Prod.snd).Nodup := by rw [hsnd]; exact hnd
  have ⟨state', hexec, hloaded, hframe⟩ := exec_loads (endian := context.endian) (m := m) (f := first)
    (first := armMultipleFirst addressing (4 * list.length)) (memory := context.memory) entries fuel1 state1 []
    (fun entry _ => hne entry.2) hnd'
    (fun env' hsame => eval_first addressing (4 * list.length) (by
      rw [hsame armMultipleBase (fun h => by
        rcases List.mem_map.1 h with ⟨o, ho, he⟩
        exact hnames o.2 (hmemEntries o ho) he)]
      exact hBs)) hMs
  have hnotList : ∀ var, (∀ name ∈ list, var ≠ armVar name) → var ∉ entries.map (armVar ·.2) := fun var hv h => by
    rcases List.mem_map.1 h with ⟨o, ho, he⟩
    exact hv o.2 (hmemEntries o ho) he.symm
  have hbaseNot : base ∉ list → armVar base ∉ entries.map (armVar ·.2) := fun hb =>
    hnotList _ fun name hin he => hb (by
      have := congrArg Bap.Var.name he
      simp only at this
      exact this ▸ hin)
  refine ⟨state', ?_, hloaded, ?_, ?_, ?_, ?_⟩
  · rw [hstate, hexec]
    rw [Bil.execProgram]
  · intro hw hb
    rw [hframe _ (hbaseNot hb), hBase, hw]
    rfl
  · intro hw hb
    rw [hframe _ (hbaseNot hb), hBase, hw]
    rfl
  · rw [hframe _ (fun h => by
      rcases List.mem_map.1 h with ⟨o, _, he⟩
      exact hne o.2 he)]
    exact hMs
  · intro var h1 h2 h3
    rw [hframe var (hnotList var h3), hOther var h1 h2]

/-- An instruction whose condition always holds is its body, so those theorems say what it does. -/
theorem armMultiple_unconditional (pc : Nat) (context : Primus.Semantics.Context) (decoded : LLVM.Decoded)
    (addressing : ArmMultipleKind) (writeback : Bool) (base : String) (condition : Int) (list : List String)
    (h : armMultipleOperands decoded.opcode decoded.operands = some (true, addressing, writeback, base, condition, list))
    (hc : armCondition condition = none) :
    armMultiple pc context decoded = some (armMultipleBody pc context true addressing writeback base list) := by
  dsimp only [armMultipleOperands, armCondition] at h hc
  lift_unfold armMultiple
  rw [h]
  simp only [Option.map]
  rw [hc]

/-- And under a condition, the instruction does this only if the condition holds, and otherwise nothing. -/
theorem armMultiple_conditional (pc : Nat) (context : Primus.Semantics.Context) (decoded : LLVM.Decoded)
    (load : Bool) (addressing : ArmMultipleKind) (writeback : Bool) (base : String) (condition : Int) (list : List String)
    {holds : Bil.Exp} (h : armMultipleOperands decoded.opcode decoded.operands = some (load, addressing, writeback, base, condition, list))
    (hc : armCondition condition = some holds) :
    armMultiple pc context decoded = some [.ifElse holds (armMultipleBody pc context load addressing writeback base list) []] := by
  dsimp only [armMultipleOperands, armCondition] at h hc
  lift_unfold armMultiple
  rw [h]
  simp only [Option.map]
  rw [hc]

/-- `tLDMIA` writes back exactly if it does not load its base, as the architecture has it. -/
theorem tLDMIA_writeback (base : String) (condition : Int) (predicate : LLVM.Operand) (list : List String) :
    armMultipleOperands "tLDMIA" (.reg base :: .imm condition :: predicate :: list.map .reg) =
      some (true, ArmMultiple.increaseAfter, !list.contains base, base, condition, list) := by
  lift_unfold armMultipleOperands
  show Option.map _ (List.mapM _ _) = _
  rw [operand_names _ fun _ => rfl]
  simp

/-- The stores in order, each to its own address. -/
private def armStores (first : Bil.Exp) (memory : Bap.Var) (endian : Endian) (pc : Nat) (entries : List (Nat × String)) :
    Bil.Program :=
  entries.map fun entry =>
    .move memory (.store (.var memory) (.bin .add first (armWord (4 * entry.1)))
      (if entry.2 = "PC" then armWord pc else .var (armVar entry.2)) endian 4)

open Bap.Proofs.Core.MemoryLaws in
private theorem read_of_bytes {m m' : Memory 32} {a : BitVec 32} {endian : Endian} {size : Nat}
    (h : ∀ k, k < size → Memory.readByte m' (a + BitVec.ofNat 32 k) = Memory.readByte m (a + BitVec.ofNat 32 k)) :
    Memory.read m' a endian size = Memory.read m a endian size := by
  have : ((List.range size).map fun offset => Memory.readByte m' (a + BitVec.ofNat 32 offset)) =
      (List.range size).map fun offset => Memory.readByte m (a + BitVec.ofNat 32 offset) :=
    List.map_congr_left fun k hk => h k (List.mem_range.1 hk)
  simp only [Memory.read, this]

open Bap.Proofs.Core.MemoryLaws in
private theorem exec_stores {first : Bil.Exp} {memory : Bap.Var} {endian : Endian} {pc : Nat} {f : BitVec 32}
    (regs : String → BitVec 32) (hpc : ∀ name, name = "PC" → regs name = BitVec.ofNat 32 pc)
    (hmemvar : ∀ name, armVar name ≠ memory) :
    ∀ (entries : List (Nat × String)) (fuel : Nat) (state : Bil.State) (rest : Bil.Program) (m : Memory 32),
      PagesSized m →
      entries.Pairwise (fun x y => ∀ k l, k < 4 → l < 4 →
        f + BitVec.ofNat 32 (4 * x.1) + BitVec.ofNat 32 k ≠ f + BitVec.ofNat 32 (4 * y.1) + BitVec.ofNat 32 l) →
      (∀ env : Bil.Env, (∀ var, var ≠ memory → Bil.lookup env var = Bil.lookup state.env var) →
        Bil.evalExp env first = .ok (.bits f)) →
      (∀ entry ∈ entries, entry.2 ≠ "PC" → Bil.lookup state.env (armVar entry.2) = .ok (.bits (regs entry.2))) →
      Bil.lookup state.env memory = .ok (.memory m) →
      ∃ (state' : Bil.State) (m' : Memory 32), Bil.execProgram (fuel + entries.length + 2) state (armStores first memory endian pc entries ++ rest) =
          Bil.execProgram (fuel + 2) state' rest ∧
        PagesSized m' ∧ Bil.lookup state'.env memory = .ok (.memory m') ∧
        (∀ entry ∈ entries, Memory.read m' (f + BitVec.ofNat 32 (4 * entry.1)) endian 4 = regs entry.2) ∧
        (∀ a, (∀ entry ∈ entries, ∀ k, k < 4 → a ≠ f + BitVec.ofNat 32 (4 * entry.1) + BitVec.ofNat 32 k) →
          Memory.readByte m' a = Memory.readByte m a) ∧
        ∀ var, var ≠ memory → Bil.lookup state'.env var = Bil.lookup state.env var
  | [], fuel, state, rest, m, hp, _, _, _, hm => ⟨state, m, rfl, hp, hm, by simp, fun _ _ => rfl, fun _ _ => rfl⟩
  | entry :: entries, fuel, state, rest, m, hp, hdis, hfirst, hregs, hm => by
    have hfirst' := hfirst state.env (fun _ _ => rfl)
    have hmem : Bil.evalExp state.env (.var memory) = .ok (.memory m) := hm
    have haddr := eval_add_int (4 * entry.1) hfirst'
    have hval : Bil.evalExp state.env (if entry.2 = "PC" then armWord pc else .var (armVar entry.2)) =
        .ok (.bits (regs entry.2)) := by
      by_cases hn : entry.2 = "PC"
      · rw [ite_eq_left hn, hpc _ hn]
        rfl
      · rw [ite_eq_right hn]
        exact hregs entry (by simp) hn
    let address := f + BitVec.ofNat 32 (4 * entry.1)
    have ⟨m1, hwrite⟩ : ∃ m1, Memory.write m address (regs entry.2) endian 4 = .ok m1 := ⟨_, write_eq rfl endian⟩
    have hstore : Bil.evalExp state.env (.store (.var memory) (.bin .add first (armWord (4 * entry.1)))
        (if entry.2 = "PC" then armWord pc else .var (armVar entry.2)) endian 4) = .ok (.memory m1) :=
      Bap.Proofs.Bil.eval_store_iff.2 ⟨32, m, address, 32, regs entry.2, m1, hmem, haddr, hval, hwrite, rfl⟩
    have hstep : Bil.execProgram (fuel + (entry :: entries).length + 2) state
        (armStores first memory endian pc (entry :: entries) ++ rest) =
        Bil.execProgram (fuel + entries.length + 2) { env := Bil.bind state.env memory (.memory m1) }
          (armStores first memory endian pc entries ++ rest) := by
      have e : fuel + (entry :: entries).length + 2 = (fuel + entries.length + 1) + 2 := by
        simp only [List.length_cons]
        omega
      rw [e]
      exact exec_move hstore
    rw [hstep]
    have hp1 := write_pagesSized hp hwrite
    have ⟨hd, hrest⟩ := List.pairwise_cons.1 hdis
    have ⟨state', m', he, hp', hm', hread, hbytes, hother⟩ := exec_stores (endian := endian) (first := first) (pc := pc) (f := f) regs hpc hmemvar entries fuel
      { env := Bil.bind state.env memory (.memory m1) } rest m1 hp1 hrest
      (fun env hsame => hfirst env fun var hvar => (hsame var hvar).trans (lookup_bind_ne _ _ hvar))
      (fun e hme hn => by
        show Bil.lookup (Bil.bind _ _ _) _ = _
        exact (lookup_bind_ne _ _ (hmemvar e.2)).trans (hregs e (List.mem_cons_of_mem _ hme) hn))
      (lookup_bind_same ..)
    refine ⟨state', m', he, hp', hm', ?_, ?_, ?_⟩
    · intro e hme
      rcases List.mem_cons.1 hme with rfl | hme
      · have hsame : Memory.read m' address endian 4 = Memory.read m1 address endian 4 :=
          read_of_bytes fun k hk => hbytes _ fun o ho l hl he' => hd o ho k l hk hl he'
        rw [hsame]
        exact read_write hp address (regs e.2) endian (by decide : 4 ≤ 2 ^ 32) hwrite
      · exact hread e hme
    · intro a ha
      rw [hbytes a (fun o ho k hk => ha o (List.mem_cons_of_mem _ ho) k hk)]
      exact readByte_write_frame hp hwrite fun k hk => ha entry (by simp) k hk
    · intro var hvar
      exact (hother var hvar).trans (lookup_bind_ne _ _ hvar)

/-- `STM` and its relatives, evaluated: the word at each address holds its register, the lowest register at the lowest
address, and of PC its value as the architecture reads it; no other byte of memory changes and no register, except that the
base is written back after the stores, which stored its old value if it is on the list. -/
theorem armMultipleBody_store_eval (pc : Nat) (context : Primus.Semantics.Context)
    (addressing : ArmMultiple) (writeback : Bool) (base : String) (list : List String)
    (hlen : 4 * list.length ≤ 2 ^ 32) (hbn : base ≠ armMultipleBase.name)
    (hn : armMultipleBase.name ∉ list)
    (hmem : context.memory.typ ≠ .imm 32) (fuel : Nat)
    {env : Bil.Env} {b : BitVec 32} {m : Memory 32} (regs : String → BitVec 32)
    (hpages : Bap.Proofs.Core.MemoryLaws.PagesSized m)
    (hPc : regs "PC" = BitVec.ofNat 32 pc)
    (hbase : Bil.lookup env (armVar base) = .ok (.bits b)) (hm : Bil.lookup env context.memory = .ok (.memory m))
    (hregs : ∀ name ∈ list, name ≠ "PC" → Bil.lookup env (armVar name) = .ok (.bits (regs name))) :
    let first := armFirstAddress addressing b (4 * list.length)
    ∃ (state' : Bil.State) (m' : Memory 32), Bil.execProgram (fuel + list.length + 5) { env := env }
        (armMultipleBody pc context false addressing writeback base list) = .ok (state', .normal) ∧
      Bil.lookup state'.env context.memory = .ok (.memory m') ∧
      (∀ entry ∈ (List.range list.length).zip list,
        Memory.read m' (first + BitVec.ofNat 32 (4 * entry.1)) context.endian 4 = regs entry.2) ∧
      (∀ a, (∀ index, index < list.length → ∀ k, k < 4 → a ≠ first + BitVec.ofNat 32 (4 * index) + BitVec.ofNat 32 k) →
        Memory.readByte m' a = Memory.readByte m a) ∧
      (writeback = true → Bil.lookup state'.env (armVar base) = .ok (.bits (armAfterAddress addressing b (4 * list.length)))) ∧
      (writeback = false → Bil.lookup state'.env (armVar base) = .ok (.bits b)) ∧
      ∀ var, var ≠ armMultipleBase → var ≠ armVar base → var ≠ context.memory →
        Bil.lookup state'.env var = Bil.lookup env var := by
  intro first
  have hne : ∀ name, armVar name ≠ context.memory := fun name he => hmem (by rw [← he])
  have hbvm : armMultipleBase ≠ context.memory := fun he => hmem (by rw [← he]; rfl)
  have hbv : armVar base ≠ armMultipleBase := fun he => hbn (congrArg Bap.Var.name he)
  have hnames : ∀ name ∈ list, armVar name ≠ armMultipleBase := fun name hin he =>
    hn ((congrArg Bap.Var.name he) ▸ hin)
  let entries := (List.range list.length).zip list
  have hentries : entries.length = list.length := by simp [entries]
  have hsnd : entries.map Prod.snd = list := by simp [entries, List.map_snd_zip]
  have hfst : entries.map Prod.fst = List.range list.length := by simp [entries, List.map_fst_zip]
  have hmemEntries : ∀ entry ∈ entries, entry.2 ∈ list := fun entry he =>
    hsnd ▸ List.mem_map.2 ⟨entry, he, rfl⟩
  have hindex : ∀ entry ∈ entries, entry.1 < list.length := fun entry he =>
    List.mem_range.1 (hfst ▸ List.mem_map.2 ⟨entry, he, rfl⟩)
  have hbody : armMultipleBody pc context false addressing writeback base list =
      .move armMultipleBase (.var (armVar base)) ::
        (armStores (armMultipleFirst addressing (4 * list.length)) context.memory context.endian pc entries ++
          (if writeback then [.move (armVar base) (armMultipleAfter addressing (4 * list.length))] else [])) := rfl
  rw [hbody]
  have h1 : Bil.evalExp env (.var (armVar base)) = .ok (.bits b) := hbase
  rw [show fuel + list.length + 5 = fuel + list.length + 3 + 2 by omega, exec_move h1]
  have hB1 : Bil.lookup (Bil.bind env armMultipleBase (.bits b)) armMultipleBase = .ok (.bits b) := lookup_bind_same ..
  have hdis : entries.Pairwise (fun x y => ∀ k l, k < 4 → l < 4 →
      first + BitVec.ofNat 32 (4 * x.1) + BitVec.ofNat 32 k ≠ first + BitVec.ofNat 32 (4 * y.1) + BitVec.ofNat 32 l) := by
    have hnd : (entries.map Prod.fst).Nodup := by rw [hfst]; exact List.nodup_range
    have hp := List.pairwise_map.1 hnd
    refine List.Pairwise.imp_of_mem ?_ hp
    intro x y hx hy hxy k l hk hl he
    have hx' := hindex x hx
    have hy' := hindex y hy
    rw [BitVec.add_assoc, BitVec.add_assoc] at he
    have hcancel := (BitVec.add_right_inj first).1 he
    have e1 : BitVec.ofNat 32 (4 * x.1) + BitVec.ofNat 32 k = BitVec.ofNat 32 (4 * x.1 + k) := by
      apply BitVec.eq_of_toNat_eq
      simp
    have e2 : BitVec.ofNat 32 (4 * y.1) + BitVec.ofNat 32 l = BitVec.ofNat 32 (4 * y.1 + l) := by
      apply BitVec.eq_of_toNat_eq
      simp
    rw [e1, e2] at hcancel
    have := congrArg BitVec.toNat hcancel
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hmem1 : Bil.lookup (Bil.bind env armMultipleBase (.bits b)) context.memory = .ok (.memory m) :=
    (lookup_bind_ne _ _ (Ne.symm hbvm)).trans hm
  have ⟨state1, m', hexec, hp', hm', hread, hbytes, hother⟩ := exec_stores (endian := context.endian) (pc := pc) (f := first)
    (first := armMultipleFirst addressing (4 * list.length)) (memory := context.memory)
    regs (fun name h => h ▸ hPc) hne entries (fuel + 2)
    { env := Bil.bind env armMultipleBase (.bits b) }
    (if writeback then [.move (armVar base) (armMultipleAfter addressing (4 * list.length))] else [])
    m hpages hdis
    (fun env' hsame => eval_first addressing (4 * list.length) ((hsame _ hbvm).trans hB1))
    (fun entry he hp => (lookup_bind_ne _ _ (hnames _ (hmemEntries entry he))).trans
      (hregs _ (hmemEntries entry he) hp)) hmem1
  have hAfter := eval_after (env := state1.env) addressing (4 * list.length) ((hother _ hbvm).trans hB1)
  have hbaseOf : Bil.lookup state1.env (armVar base) = .ok (.bits b) :=
    (hother _ (hne base)).trans ((lookup_bind_ne _ _ hbv).trans hbase)
  have hbytes' : ∀ a, (∀ index, index < list.length → ∀ k, k < 4 → a ≠ first + BitVec.ofNat 32 (4 * index) + BitVec.ofNat 32 k) →
      Memory.readByte m' a = Memory.readByte m a := fun a ha =>
    hbytes a fun entry he k hk => ha entry.1 (hindex entry he) k hk
  rw [show fuel + list.length + 3 + 1 = fuel + 2 + entries.length + 2 by rw [hentries]; omega, hexec]
  cases writeback with
  | true =>
    refine ⟨{ env := Bil.bind state1.env (armVar base) (.bits (armAfterAddress addressing b (4 * list.length))) }, m', ?_,
      (lookup_bind_ne _ _ (Ne.symm (hne base))).trans hm', hread, hbytes', fun _ => lookup_bind_same .., (fun h => by cases h), ?_⟩
    · simp only [ite_true]
      rw [exec_move hAfter, Bil.execProgram]
    · intro var h1 h2 h3
      exact (lookup_bind_ne _ _ h2).trans ((hother _ h3).trans (lookup_bind_ne _ _ h1))
  | false =>
    refine ⟨state1, m', ?_, hm', hread, hbytes', (fun h => by cases h), fun _ => hbaseOf, ?_⟩
    · simp only [Bool.false_eq_true, ite_false]
      rw [Bil.execProgram]
    · intro var h1 _ h3
      exact (hother _ h3).trans (lookup_bind_ne _ _ h1)

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

/-- The flow of a RISC-V instruction is the role its registers give it, as in `riscvFlow`. -/
theorem decodeRISCVWith_flow (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeRISCVWith globals base address data)
      (fun insn => insn.address = address ∧ ∃ word flags, insn.flow = riscvFlow word flags) := by
  unfold decodeRISCVWith
  repeat' first
    | with_reducible refine Holds.bind fun _ => ?_
    | with_reducible exact Holds.pure ⟨rfl, _, _, rfl⟩

theorem decodeRISCVWith_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeRISCVWith globals base address data) (Lifted (fun flow : Flow => flow) address) :=
  fun s r s' he => ⟨(decodeRISCVWith_flow globals base address data s r s' he).1, _, rfl⟩

theorem decodePowerPCWith_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodePowerPCWith globals base address data) (Lifted (flow) address) := by
  unfold decodePowerPCWith
  lifted_decoder

theorem decodeMIPSWith_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeMIPSWith globals base address data) (Lifted mipsFlow address) := by
  unfold decodeMIPSWith
  lifted_decoder

/-- A PowerPC instruction of any variant says how it goes on as its LLVM flags do. -/
theorem decodePowerPCOf_lifted (variant : PowerPCVariant) (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodePowerPCOf variant globals base address data) (Lifted (flow) address) := by
  unfold decodePowerPCOf
  lifted_decoder

/-- A MIPS instruction of any variant, also of release 6 and little-endian, is at its address, with the flow of `mipsFlow`. -/
theorem decodeMIPSOf_lifted (variant : MipsVariant) (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeMIPSOf variant globals base address data) (Lifted mipsFlow address) := by
  unfold decodeMIPSOf
  lifted_decoder

/-- The flow of an A32 instruction is what `arm32Flow` says of it, corrected by what its program does to the pc. -/
theorem decodeARM32With_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeARM32With globals base address data)
      (Lifted (fun evidence : LLVM.Decoded × Bil.Program => armControlFlow (arm32Flow evidence.1) evidence.2) address) := by
  unfold decodeARM32With
  refine Holds.bind fun _ => ?_
  dsimp only
  split
  · exact Holds.pure ⟨rfl, (_, _), rfl⟩
  · exact Holds.bind fun _ => Holds.pure ⟨rfl, (_, _), rfl⟩

/-- The flow of a T32 instruction goes by its flags, corrected by what its program does to the pc, and that of an IT block
by those of its last instruction, except that it can always be skipped. -/
inductive ThumbFlow : Flow → Prop
  | single (flags : Nat) (bil : Bil.Program) : ThumbFlow (armControlFlow (flow flags) bil)
  | block (flow' : Flow) (bil : Bil.Program) : ThumbFlow (thumbItFlow (armControlFlow flow' bil))

/-- The block of an IT instruction, as `ITAdvance` has it: the first instruction has `firstcond`, and each next one its top
three bits and the next bit of the mask. The lowest bit set in the mask ends the block. -/
theorem thumbItConditions_spec (firstcond mask : Nat) :
    (mask % 2 = 1 → (thumbItConditions firstcond mask).length = 4) ∧
      (mask % 4 = 2 → (thumbItConditions firstcond mask).length = 3) ∧
      (mask % 8 = 4 → (thumbItConditions firstcond mask).length = 2) ∧
      (mask % 16 = 8 → (thumbItConditions firstcond mask).length = 1) ∧
      (thumbItConditions firstcond mask)[0]? = some (firstcond : Int) ∧
      ∀ index, 0 < index → (h : index < (thumbItConditions firstcond mask).length) →
        (thumbItConditions firstcond mask)[index] =
          ((firstcond / 2 * 2 + (mask >>> (4 - index)) % 2 : Nat) : Int) := by
  unfold thumbItConditions
  simp only [List.length_map, List.length_range]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    simp [h]
  · intro h
    have h1 : ¬ mask % 2 = 1 := by omega
    simp [h, h1]
  · intro h
    have h1 : ¬ mask % 2 = 1 := by omega
    have h2 : ¬ mask % 4 = 2 := by omega
    simp [h, h1, h2]
  · intro h
    have h1 : ¬ mask % 2 = 1 := by omega
    have h2 : ¬ mask % 4 = 2 := by omega
    have h3 : ¬ mask % 8 = 4 := by omega
    simp [h1, h2, h3]
  · split <;> (try split) <;> (try split) <;> simp
  · intro index h0 _
    have hi : index ≠ 0 := by omega
    simp [hi]

/-- The blocks of the examples of the manual: `ITE EQ` is then and else, and `ITTE LT` then, then and else. -/
theorem thumbItConditions_examples :
    thumbItConditions 0 0b1100 = [0, 1] ∧ thumbItConditions 0b1011 0b1010 = [0b1011, 0b1011, 0b1010] := by
  decide

/-- In a block, nothing sets the flags. -/
theorem thumbPredicated_no_flags (condition : Int) (operands : List LLVM.Operand) :
    LLVM.Operand.reg "CPSR" ∉ thumbPredicated condition operands := by
  unfold thumbPredicated
  fun_induction thumbPredicated.go condition operands <;> simp_all
  rename_i h _ _
  exact fun e => h e.symm

/-- The predicate operand of an instruction of a block holds its condition, and the flags operand does not ask for them. -/
theorem thumbPredicated_operands (condition : Int) (rest : List LLVM.Operand) :
    thumbPredicated condition (.imm 14 :: .reg "Nil" :: rest) =
        .imm (thumbBlockPredicate condition) :: .reg "Nil" :: thumbPredicated condition rest ∧
      thumbPredicated condition (.reg "CPSR" :: rest) = .reg "Nil" :: thumbPredicated condition rest := by
  constructor <;> (unfold thumbPredicated; rw [thumbPredicated.go])

/-- A predicate in a block is never the one of an instruction out of a block, whose narrow forms set the flags, and
it is its condition if that can fail. -/
theorem thumbBlockPredicate_spec (condition : Int) :
    thumbBlockPredicate condition ≠ 14 ∧ (condition ≠ 14 → thumbBlockPredicate condition = condition) ∧
      (armCondition condition = none → armCondition (thumbBlockPredicate condition) = none) := by
  unfold thumbBlockPredicate
  split
  · subst_vars
    exact ⟨by decide, by simp, fun _ => rfl⟩
  · exact ⟨‹_›, fun _ => rfl, id⟩

/-- `it al`: the only condition of the block always holds, and the instruction is not told that it is out of a block. -/
theorem thumb_it_always :
    thumbItConditions 14 8 = [14] ∧ armCondition 14 = none ∧ armCondition (thumbBlockPredicate 14) = none ∧
      thumbBlockPredicate 14 ≠ 14 :=
  ⟨by decide, rfl, rfl, by decide⟩

/-- A block can always be skipped: what is `.normal` or a call stays, and the rest is conditional. -/
theorem thumbItFlow_spec (flow' : Flow) :
    thumbItFlow flow' = (match flow' with
      | .normal => .normal
      | .call => .call
      | _ => .conditionalJump) := by
  cases flow' <;> rfl

private theorem decodeThumbIt_flow (globals : Primus.Semantics.Environment) (base address : Nat) (data : ByteArray)
    (it : LLVM.Decoded) (firstcond mask : Nat) :
    Holds (decodeThumbIt globals base address data it firstcond mask)
      (fun insn => insn.address = address ∧ ThumbFlow insn.flow) := by
  lift_unfold decodeThumbIt
  refine Holds.bind fun _ => ?_
  dsimp only
  split <;> exact Holds.pure ⟨rfl, .block _ _⟩

private theorem decodeThumbIt_fields (globals : Primus.Semantics.Environment) (base address : Nat) (data : ByteArray)
    (it : LLVM.Decoded) (firstcond mask : Nat) :
    Holds (decodeThumbIt globals base address data it firstcond mask)
      (fun insn => insn.address = address ∧ ∃ flow' : Flow, insn.flow = thumbItFlow (armControlFlow flow' insn.bil)) := by
  lift_unfold decodeThumbIt
  refine Holds.bind fun _ => ?_
  dsimp only
  split <;> exact Holds.pure ⟨rfl, _, rfl⟩

theorem decodeThumbWith_flow (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeThumbWith globals base address data)
      (fun insn => insn.address = address ∧ ThumbFlow insn.flow) := by
  unfold decodeThumbWith
  refine Holds.bind fun _ => ?_
  split
  · exact decodeThumbIt_flow globals base address data _ _ _
  · exact Holds.bind fun _ => Holds.pure ⟨rfl, .single _ _⟩

theorem decodeThumbWith_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeThumbWith globals base address data) (Lifted (fun flow : Flow => flow) address) :=
  fun s r s' he => ⟨(decodeThumbWith_flow globals base address data s r s' he).1, _, rfl⟩

theorem decodeX8632With_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeX8632With globals base address data) (Lifted (flow) address) := by
  unfold decodeX8632With
  lifted_decoder

/-- The flow of a RISC-V instruction is the role its registers give it, as in `riscvFlow`. -/
theorem decodeRISCV32With_flow (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeRISCV32With globals base address data)
      (fun insn => insn.address = address ∧ ∃ word flags, insn.flow = riscvFlow word flags) := by
  unfold decodeRISCV32With
  repeat' first
    | with_reducible refine Holds.bind fun _ => ?_
    | with_reducible exact Holds.pure ⟨rfl, _, _, rfl⟩

theorem decodeRISCV32With_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeRISCV32With globals base address data) (Lifted (fun flow : Flow => flow) address) :=
  fun s r s' he => ⟨(decodeRISCV32With_flow globals base address data s r s' he).1, _, rfl⟩

theorem decodeMIPS32With_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodeMIPS32With globals base address data) (Lifted mipsFlow address) := by
  unfold decodeMIPS32With
  lifted_decoder

theorem decodePowerPC32With_lifted (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : Holds (decodePowerPC32With globals base address data) (Lifted (flow) address) := by
  unfold decodePowerPC32With
  lifted_decoder

/-! ### What the decoders return, field by field -/

private abbrev normalizeAssembly : String → String := lift% normalizeAssembly
private abbrev instructionWord : Endian → ByteArray → Nat := lift% instructionWord
private abbrev riscvAddress (address : Nat) (data : ByteArray) (base : Nat) : Nat :=
  instructionWord .little (instructionBytes data (address - base))

/-- An instruction as it comes of the machine instruction of LLVM: its size and text are the ones of LLVM, its flow
and target are computed from them, and its program is what `resolve` makes of the lifted one. -/
def FromMC (address : Nat) (flowOf : LLVM.MCDecoded → Flow) (targetOf : LLVM.MCDecoded → List LLVM.MCOperand → Option Nat)
    (resolve : Bil.Program → Bil.Program) (insn : Insn) : Prop :=
  insn.address = address ∧ ∃ (decoded : LLVM.MCDecoded) (operands : List LLVM.MCOperand) (bil : Bil.Program),
    insn.size = decoded.size ∧ insn.asm = normalizeAssembly decoded.assembly ∧ insn.flow = flowOf decoded ∧
      insn.target = targetOf decoded operands ∧ insn.bil = resolve bil

/-- Peels monadic steps off a decoder body until its final `pure`. -/
local macro "fields_decoder" : tactic =>
  `(tactic| (repeat' first
    | refine Holds.bind fun _ => ?_
    | exact Holds.pure ⟨rfl, _, _, _, rfl, rfl, rfl, rfl, rfl⟩))

theorem decodeX86With_fields (globals : Primus.Semantics.Environment) (base address : Nat) (data : ByteArray) :
    Holds (decodeX86With globals base address data)
      (FromMC address (flow ·.flags)
        (fun decoded operands => x86MCTarget 64 globals (address + decoded.size) (LLVM.mcOpcode decoded.instruction) operands)
        (resolveAliases (x86Aliases x86HighByteBase 64))) := by
  unfold decodeX86With
  refine Holds.bind fun decoded => ?_
  refine Holds.bind fun operands => ?_
  refine Holds.bind fun _ => ?_
  refine Holds.bind fun bil => ?_
  exact Holds.pure ⟨rfl, decoded, operands, bil, rfl, rfl, rfl, rfl, rfl⟩

theorem decodeX8632With_fields (globals : Primus.Semantics.Environment) (base address : Nat) (data : ByteArray) :
    Holds (decodeX8632With globals base address data)
      (FromMC address (flow ·.flags)
        (fun decoded operands => x86MCTarget 32 globals (address + decoded.size) (LLVM.mcOpcode decoded.instruction) operands)
        (resolveAliases (x86Aliases x8632HighByteBase 32))) := by
  unfold decodeX8632With
  refine Holds.bind fun decoded => ?_
  refine Holds.bind fun operands => ?_
  refine Holds.bind fun _ => ?_
  refine Holds.bind fun bil => ?_
  exact Holds.pure ⟨rfl, decoded, operands, bil, rfl, rfl, rfl, rfl, rfl⟩

theorem decodeAArch64With_fields (globals : Primus.Semantics.Environment) (base address : Nat) (data : ByteArray) :
    Holds (decodeAArch64With globals base address data)
      (FromMC address (flow ·.flags) (fun decoded operands => aarch64MCTarget address decoded.flags operands) id) := by
  unfold decodeAArch64With
  fields_decoder

/-- The word of a RISC-V instruction, which `riscvFlow` and `riscvMCTarget` read, is the one at its address. -/
theorem decodeRISCVWith_fields (globals : Primus.Semantics.Environment) (base address : Nat) (data : ByteArray) :
    Holds (decodeRISCVWith globals base address data)
      (FromMC address (fun decoded => riscvFlow (riscvAddress address data base) decoded.flags)
        (fun decoded operands => riscvMCTarget 64 address (riscvAddress address data base) decoded.flags operands) id) := by
  unfold decodeRISCVWith
  refine Holds.bind fun decoded => ?_
  refine Holds.bind fun operands => ?_
  refine Holds.bind fun _ => ?_
  refine Holds.bind fun bil => ?_
  exact Holds.pure ⟨rfl, decoded, operands, bil, rfl, rfl, by dsimp only, by dsimp only, rfl⟩

theorem decodeRISCV32With_fields (globals : Primus.Semantics.Environment) (base address : Nat) (data : ByteArray) :
    Holds (decodeRISCV32With globals base address data)
      (FromMC address (fun decoded => riscvFlow (riscvAddress address data base) decoded.flags)
        (fun decoded operands => riscvMCTarget 32 address (riscvAddress address data base) decoded.flags operands) id) := by
  unfold decodeRISCV32With
  refine Holds.bind fun decoded => ?_
  refine Holds.bind fun operands => ?_
  refine Holds.bind fun _ => ?_
  refine Holds.bind fun bil => ?_
  exact Holds.pure ⟨rfl, decoded, operands, bil, rfl, rfl, by dsimp only, by dsimp only, rfl⟩

theorem decodePowerPCWith_fields (globals : Primus.Semantics.Environment) (base address : Nat) (data : ByteArray) :
    Holds (decodePowerPCWith globals base address data)
      (FromMC address (flow ·.flags)
        (fun _ operands => powerpcMCTarget 64 address (riscvAddress address data base) operands)
        (resolveAliases powerpcAliases)) := by
  unfold decodePowerPCWith
  fields_decoder

theorem decodePowerPC32With_fields (globals : Primus.Semantics.Environment) (base address : Nat) (data : ByteArray) :
    Holds (decodePowerPC32With globals base address data)
      (FromMC address (flow ·.flags)
        (fun _ operands => powerpcMCTarget 32 address (instructionWord .big (instructionBytes data (address - base))) operands)
        (resolveAliases powerpcAliases)) := by
  unfold decodePowerPC32With
  fields_decoder

/-- An instruction as it comes of the text of LLVM, with the opcode name that it is lifted by. -/
def FromText (address : Nat) (flowOf : LLVM.Decoded → Bil.Program → Flow) (targetOf : LLVM.Decoded → Option Nat)
    (insn : Insn) : Prop :=
  insn.address = address ∧ ∃ decoded : LLVM.Decoded,
    insn.size = decoded.size ∧ insn.asm = normalizeAssembly decoded.assembly ∧ insn.flow = flowOf decoded insn.bil ∧
      insn.target = targetOf decoded

local macro "text_decoder" : tactic =>
  `(tactic| (repeat' first
    | exact Holds.pure ⟨rfl, _, rfl, rfl, rfl, rfl⟩
    | refine Holds.bind fun _ => ?_))

theorem decodeMIPSWith_fields (globals : Primus.Semantics.Environment) (base address : Nat) (data : ByteArray) :
    Holds (decodeMIPSWith globals base address data)
      (FromText address (fun decoded _ => mipsFlow decoded) (mipsTarget 64 address)) := by
  unfold decodeMIPSWith
  text_decoder

theorem decodeMIPS32With_fields (globals : Primus.Semantics.Environment) (base address : Nat) (data : ByteArray) :
    Holds (decodeMIPS32With globals base address data)
      (FromText address (fun decoded _ => mipsFlow decoded) (mipsTarget 32 address)) := by
  unfold decodeMIPS32With
  text_decoder

theorem decodeARM32With_fields (globals : Primus.Semantics.Environment) (base address : Nat) (data : ByteArray) :
    Holds (decodeARM32With globals base address data)
      (FromText address (fun decoded bil => armControlFlow (arm32Flow decoded) bil) (arm32Target address)) := by
  unfold decodeARM32With
  refine Holds.bind fun _ => ?_
  dsimp only
  split <;> exact Holds.bind fun _ => Holds.pure ⟨rfl, _, rfl, rfl, rfl, rfl⟩

/-- A Thumb instruction out of a block is what it is, and a block has the program and the flow of `thumbItFlow`, whose
target is the one of its last instruction. -/
theorem decodeThumbWith_fields (globals : Primus.Semantics.Environment) (base address : Nat) (data : ByteArray) :
    Holds (decodeThumbWith globals base address data) fun insn =>
      insn.address = address ∧
        ((∃ decoded : LLVM.Decoded, insn.size = decoded.size ∧ insn.asm = normalizeAssembly decoded.assembly ∧
            insn.flow = armControlFlow (flow decoded.flags) insn.bil ∧ insn.target = thumbTarget address decoded) ∨
          (∃ flow' : Flow, insn.flow = thumbItFlow (armControlFlow flow' insn.bil))) := by
  unfold decodeThumbWith
  refine Holds.bind fun _ => ?_
  split
  · refine fun s r s' he => ?_
    have := decodeThumbIt_fields globals base address data _ _ _ s r s' he
    exact ⟨this.1, .inr this.2⟩
  · exact Holds.bind fun _ => Holds.pure ⟨rfl, .inl ⟨_, rfl, rfl, rfl, rfl⟩⟩

/-! ### What aliases evaluate to -/

/-- An expression evaluates to a word of this width with this value. -/
def Reads (env : Bil.Env) (exp : Bil.Exp) (width value : Nat) : Prop :=
  ∃ (w : Nat) (x : BitVec w), Bil.evalExp env exp = .ok (.bits x) ∧ w = width ∧ x.toNat = value

private theorem Reads.concat {env : Bil.Env} {left right : Bil.Exp} {lw rw l r : Nat}
    (hl : Reads env left lw l) (hr : Reads env right rw r) :
    Reads env (.concat left right) (lw + rw) (2 ^ rw * l + r) := by
  obtain ⟨w1, x1, h1, rfl, rfl⟩ := hl
  obtain ⟨w2, x2, h2, rfl, rfl⟩ := hr
  refine ⟨_, Word.concat x1 x2, ?_, rfl, Bap.Proofs.Core.WordLaws.concat_toNat x1 x2⟩
  simp [Bil.evalExp, h1, h2, Bap.Value.asBits, bind, Except.bind]

private theorem Reads.extract {env : Bil.Env} {value : Bil.Exp} {w v high low : Nat}
    (h : Reads env value w v) (h1 : low ≤ high) (h2 : high < w) :
    Reads env (.extract high low value) (high - low + 1) (v / 2 ^ low % 2 ^ (high - low + 1)) := by
  obtain ⟨w, x, he, rfl, rfl⟩ := h
  refine ⟨_, BitVec.extractLsb high low x, ?_, rfl, Bap.Proofs.Core.WordLaws.extract_toNat x high low⟩
  simp [Bil.evalExp, he, Bap.Value.asBits, Bap.Proofs.Core.WordLaws.extract_ok x high low h1 h2, bind, Except.bind]

private theorem Reads.var {env : Bil.Env} {var : Bap.Var} {w : Nat} {x : BitVec w}
    (h : Bil.lookup env var = .ok (.bits x)) : Reads env (.var var) w x.toNat :=
  ⟨w, x, by simpa [Bil.evalExp] using h, rfl, rfl⟩

/-- The flags are the bits of `v`, the last one is the lowest. -/
private def FlagsHold (env : Bil.Env) : List String → Nat → Prop
  | [], _ => True
  | name :: rest, v =>
    (∃ (w : Nat) (x : BitVec w), Bil.lookup env (flagPart name).var = .ok (.bits x) ∧ w = 1 ∧ x.toNat = v / 2 ^ rest.length % 2) ∧
      FlagsHold env rest v

private theorem flagPart_read (name : String) : (flagPart name).read = .var (flagPart name).var := by
  simp [AliasPart.read, flagPart]

private theorem flagPart_write (name : String) (value : Bil.Exp) :
    (flagPart name).write value = .move (flagPart name).var value := by
  simp [AliasPart.write, flagPart]

private theorem flags_read {env : Bil.Env} {v : Nat} :
    ∀ (name : String) (rest : List String), FlagsHold env (name :: rest) v →
      Reads env (aliasRead (flagPart name, rest.map flagPart)) (rest.length + 1) (v % 2 ^ (rest.length + 1))
  | name, [], ⟨⟨w, x, hx, hw, hv⟩, _⟩ => by
    subst hw
    have hr := Reads.var hx
    rw [hv] at hr
    simp only [List.map_nil, aliasRead, flagPart_read]
    simpa [Nat.pow_zero, Nat.div_one] using hr
  | name, next :: rest, ⟨⟨w, x, hx, hw, hv⟩, htail⟩ => by
    subst hw
    have hr := Reads.var hx
    rw [hv] at hr
    have hs := flags_read next rest htail
    have hc := Reads.concat hr hs
    simp only [List.map_cons, aliasRead, flagPart_read, List.length_cons] at hc ⊢
    have hnat : 2 ^ (rest.length + 1) * (v / 2 ^ (rest.length + 1) % 2) + v % 2 ^ (rest.length + 1) =
        v % 2 ^ (rest.length + 1 + 1) := by
      rw [Nat.mod_pow_succ (k := rest.length + 1)]
      omega
    rw [hnat] at hc
    rw [show rest.length + 1 + 1 = 1 + (rest.length + 1) by omega]
    rw [show 1 + (rest.length + 1) = rest.length + 1 + 1 by omega] at *
    simpa [Nat.add_comm] using hc

/-- Setting the flags from the bits of a value in a temporary. -/
private theorem flags_write (temporary : Bap.Var) {v w : Nat} (x : BitVec w) (hv : x.toNat = v) (fuel : Nat) :
    ∀ (names : List String) (state : Bil.State) (rest : Bil.Program),
      names.Nodup → names.length ≤ w → (∀ name ∈ names, (flagPart name).var ≠ temporary) →
      Bil.lookup state.env temporary = .ok (.bits x) →
      ∃ state', Bil.execProgram (fuel + names.length + 2) state
          (aliasWrites (.var temporary) names.length (names.map flagPart) ++ rest) =
          Bil.execProgram (fuel + 2) state' rest ∧ FlagsHold state'.env names v ∧
        ∀ var, (∀ name ∈ names, var ≠ (flagPart name).var) → Bil.lookup state'.env var = Bil.lookup state.env var := by
  intro names
  induction names with
  | nil =>
    intro state rest _ _ _ _
    exact ⟨state, rfl, by simp [FlagsHold], fun _ _ => rfl⟩
  | cons name others ih =>
    intro state rest hnodup hlen hne htemp
    have hndp := List.nodup_cons.1 hnodup
    have htail : others.length < w := by simp only [List.length_cons] at hlen; omega
    have hsize : (flagPart name).size = 1 := rfl
    have hread : Reads state.env (.var temporary) w v := by
      rw [← hv]; exact Reads.var htemp
    have hbit := Reads.extract hread (Nat.le_refl _) htail
    obtain ⟨w', y, he, hw', hy⟩ := hbit
    have hw1 : w' = 1 := by omega
    let state1 : Bil.State := { env := Bil.bind state.env (flagPart name).var (.bits y) }
    have htemp1 : Bil.lookup state1.env temporary = .ok (.bits x) := by
      rw [lookup_bind_ne _ _ (fun e => hne name (by simp) e.symm)]; exact htemp
    obtain ⟨state2, hrun, hhold, hframe⟩ := ih state1 rest hndp.2 (by omega)
      (fun n hn => hne n (by simp [hn])) htemp1
    have hexec : Bil.execProgram (fuel + (name :: others).length + 2) state
        (aliasWrites (.var temporary) (name :: others).length ((name :: others).map flagPart) ++ rest) =
        Bil.execProgram (fuel + 2) state2 rest := by
      have hstep : aliasWrites (.var temporary) (others.length + 1) ((name :: others).map flagPart) =
          .move (flagPart name).var (.extract others.length others.length (.var temporary)) ::
            aliasWrites (.var temporary) others.length (others.map flagPart) := by
        simp [aliasWrites, flagPart_write, hsize]
      simp only [List.length_cons]
      rw [hstep, List.cons_append, show fuel + (others.length + 1) + 2 = (fuel + others.length + 1) + 2 by omega,
        exec_move he]
      rw [show fuel + others.length + 1 + 1 = fuel + others.length + 2 by omega]
      exact hrun
    have hlook : Bil.lookup state2.env (flagPart name).var = .ok (.bits y) := by
      rw [hframe _ (fun n hn e => hndp.1 (by
        have : name = n := by simpa [flagPart, AliasPart.var] using e
        rw [this]; exact hn))]
      exact lookup_bind_same _ _ _
    have hval : y.toNat = v / 2 ^ others.length % 2 := by simpa using hy
    refine ⟨state2, hexec, ⟨⟨w', y, hlook, hw1, hval⟩, hhold⟩, ?_⟩
    intro var hvar
    rw [hframe var (fun n hn => hvar n (by simp [hn]))]
    exact lookup_bind_ne _ _ (hvar name (by simp))

private theorem flag_sizes (names : List String) :
    (names.map flagPart).foldr (fun part size => part.size + size) 0 = names.length := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
    simp only [List.map_cons, List.foldr_cons, List.length_cons, ih]
    show 1 + rest.length = _
    omega

/-- An alias of several flags has the value that is assigned to it, and the flags have the bits of the value. -/
theorem flagAlias_write_read (typ : Typ) (value : Bil.Exp) (name next : String) (others : List String) (state : Bil.State)
    (rest : Bil.Program) (fuel w : Nat) (x : BitVec w) (hvalue : Bil.evalExp state.env value = .ok (.bits x))
    (hnodup : (name :: next :: others).Nodup) (hlen : others.length + 2 ≤ w)
    (htemp : ∀ n ∈ name :: next :: others, (flagPart n).var ≠ aliasTemporary typ) :
    ∃ state', Bil.execProgram (fuel + others.length + 5) state
        (aliasWrite typ value (flagPart name, (next :: others).map flagPart) ++ rest) =
        Bil.execProgram (fuel + 2) state' rest ∧
      Reads state'.env (aliasRead (flagPart name, (next :: others).map flagPart)) (others.length + 2)
        (x.toNat % 2 ^ (others.length + 2)) ∧
      FlagsHold state'.env (name :: next :: others) x.toNat ∧
      ∀ var, var ≠ aliasTemporary typ → (∀ n ∈ name :: next :: others, var ≠ (flagPart n).var) →
        Bil.lookup state'.env var = Bil.lookup state.env var := by
  let state1 : Bil.State := { env := Bil.bind state.env (aliasTemporary typ) (.bits x) }
  obtain ⟨state2, hrun, hhold, hframe⟩ := flags_write (aliasTemporary typ) x rfl fuel (name :: next :: others) state1 rest
    hnodup (by simp only [List.length_cons]; omega) htemp (lookup_bind_same _ _ _)
  refine ⟨state2, ?_, ?_, hhold, ?_⟩
  · have hshape : aliasWrite typ value (flagPart name, (next :: others).map flagPart) =
        .move (aliasTemporary typ) value ::
          aliasWrites (.var (aliasTemporary typ)) (name :: next :: others).length ((name :: next :: others).map flagPart) := by
      change Bil.Stmt.move _ value :: aliasWrites _ (((name :: next :: others).map flagPart).foldr
        (fun part size => part.size + size) 0) ((name :: next :: others).map flagPart) = _
      rw [flag_sizes]
    rw [hshape, List.cons_append, show fuel + others.length + 5 = (fuel + others.length + 3) + 2 by omega, exec_move hvalue]
    rw [show fuel + others.length + 3 + 1 = fuel + (name :: next :: others).length + 2 by simp only [List.length_cons]; omega]
    exact hrun
  · have := flags_read name (next :: others) hhold
    simpa only [List.length_cons] using this
  · intro var ht hv
    rw [hframe var hv]
    exact lookup_bind_ne _ _ ht

private theorem flag_not_temporary (typ : Typ) (names : List String) (h : "_alias" ∉ names) :
    ∀ n ∈ names, (flagPart n).var ≠ aliasTemporary typ := by
  intro n hn e
  have : n = "_alias" := congrArg Bap.Var.name e
  exact h (this ▸ hn)

/-- EFLAGS is the 32 flags: what is written to it is what is read from it, whatever it is. -/
theorem x86_eflags_write_read (base : String → Option String) (bits : Nat) (typ : Typ) (value : Bil.Exp) (state : Bil.State)
    (rest : Bil.Program) (fuel : Nat) (x : BitVec 32) (hvalue : Bil.evalExp state.env value = .ok (.bits x)) :
    ∃ alias state', (lift% x86Aliases) base bits "EFLAGS" = some alias ∧
      Bil.execProgram (fuel + 35) state (aliasWrite typ value alias ++ rest) = Bil.execProgram (fuel + 2) state' rest ∧
      Reads state'.env (aliasRead alias) 32 x.toNat ∧ FlagsHold state'.env (lift% x86FlagBits) x.toNat := by
  have hnames : (lift% x86FlagBits) = "AI" :: "AES" :: ((lift% x86FlagBits).drop 2) := rfl
  have hnodup : (lift% x86FlagBits).Nodup := by decide
  have htemp : "_alias" ∉ (lift% x86FlagBits) := by decide
  rw [hnames] at hnodup htemp
  obtain ⟨state', hrun, hread, hhold, _⟩ := flagAlias_write_read typ value "AI" "AES" ((lift% x86FlagBits).drop 2) state rest
    fuel 32 x hvalue hnodup (by decide) (flag_not_temporary typ _ htemp)
  refine ⟨_, state', rfl, hrun, ?_, hhold⟩
  have hlt : x.toNat % 2 ^ 32 = x.toNat := Nat.mod_eq_of_lt x.isLt
  exact hlt ▸ hread

/-- The flags are where the architecture has them in EFLAGS, from the lowest bit: CF, PF, AF, ZF, SF, TF, IF, DF, OF. -/
theorem x86_eflags_bits :
    (lift% x86FlagBits).length = 32 ∧ (lift% x86FlagBits)[31 - 0]? = some "CF" ∧ (lift% x86FlagBits)[31 - 2]? = some "PF" ∧
      (lift% x86FlagBits)[31 - 4]? = some "AF" ∧ (lift% x86FlagBits)[31 - 6]? = some "ZF" ∧
      (lift% x86FlagBits)[31 - 7]? = some "SF" ∧ (lift% x86FlagBits)[31 - 8]? = some "TF" ∧
      (lift% x86FlagBits)[31 - 9]? = some "IF" ∧ (lift% x86FlagBits)[31 - 10]? = some "DF" ∧
      (lift% x86FlagBits)[31 - 11]? = some "OF" :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem field_case (lt gt eq un : String) (hnodup : [lt, gt, eq, un].Nodup) (htemp : "_alias" ∉ [lt, gt, eq, un])
    (typ : Typ) (value : Bil.Exp) (state : Bil.State) (rest : Bil.Program) (fuel : Nat) (x : BitVec 4)
    (hvalue : Bil.evalExp state.env value = .ok (.bits x)) :
    ∃ state', Bil.execProgram (fuel + 7) state
        (aliasWrite typ value (flagPart lt, [flagPart gt, flagPart eq, flagPart un]) ++ rest) =
        Bil.execProgram (fuel + 2) state' rest ∧
      Reads state'.env (aliasRead (flagPart lt, [flagPart gt, flagPart eq, flagPart un])) 4 x.toNat := by
  have hlt : x.toNat % 2 ^ 4 = x.toNat := Nat.mod_eq_of_lt x.isLt
  obtain ⟨state', hrun, hread, _, _⟩ := flagAlias_write_read typ value lt gt [eq, un] state rest fuel 4 x hvalue
    hnodup (by simp) (flag_not_temporary typ _ htemp)
  exact ⟨state', hrun, hlt ▸ hread⟩

/-- A field of the condition register of PowerPC is its bits: what is written to it is what is read from it. -/
theorem powerpc_field_write_read (name : String) (h : name ∈ ["CR0", "CR1", "CR2", "CR3", "CR4", "CR5", "CR6", "CR7"])
    (typ : Typ) (value : Bil.Exp) (state : Bil.State) (rest : Bil.Program) (fuel : Nat) (x : BitVec 4)
    (hvalue : Bil.evalExp state.env value = .ok (.bits x)) :
    ∃ alias state', (lift% powerpcAliases) name = some alias ∧
      Bil.execProgram (fuel + 7) state (aliasWrite typ value alias ++ rest) = Bil.execProgram (fuel + 2) state' rest ∧
      Reads state'.env (aliasRead alias) 4 x.toNat := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨s, h1, h2⟩ := field_case "CR0LT" "CR0GT" "CR0EQ" "CR0UN" (by decide) (by decide) typ value state rest fuel x hvalue
    exact ⟨_, s, rfl, h1, h2⟩
  · obtain ⟨s, h1, h2⟩ := field_case "CR1LT" "CR1GT" "CR1EQ" "CR1UN" (by decide) (by decide) typ value state rest fuel x hvalue
    exact ⟨_, s, rfl, h1, h2⟩
  · obtain ⟨s, h1, h2⟩ := field_case "CR2LT" "CR2GT" "CR2EQ" "CR2UN" (by decide) (by decide) typ value state rest fuel x hvalue
    exact ⟨_, s, rfl, h1, h2⟩
  · obtain ⟨s, h1, h2⟩ := field_case "CR3LT" "CR3GT" "CR3EQ" "CR3UN" (by decide) (by decide) typ value state rest fuel x hvalue
    exact ⟨_, s, rfl, h1, h2⟩
  · obtain ⟨s, h1, h2⟩ := field_case "CR4LT" "CR4GT" "CR4EQ" "CR4UN" (by decide) (by decide) typ value state rest fuel x hvalue
    exact ⟨_, s, rfl, h1, h2⟩
  · obtain ⟨s, h1, h2⟩ := field_case "CR5LT" "CR5GT" "CR5EQ" "CR5UN" (by decide) (by decide) typ value state rest fuel x hvalue
    exact ⟨_, s, rfl, h1, h2⟩
  · obtain ⟨s, h1, h2⟩ := field_case "CR6LT" "CR6GT" "CR6EQ" "CR6UN" (by decide) (by decide) typ value state rest fuel x hvalue
    exact ⟨_, s, rfl, h1, h2⟩
  · obtain ⟨s, h1, h2⟩ := field_case "CR7LT" "CR7GT" "CR7EQ" "CR7UN" (by decide) (by decide) typ value state rest fuel x hvalue
    exact ⟨_, s, rfl, h1, h2⟩

private theorem part_bits (s l q v r : Nat) (hr : r < 2 ^ l) (hv : v < 2 ^ s) :
    (2 ^ (s + l) * q + (2 ^ l * v + r)) / 2 ^ l % 2 ^ s = v := by
  have hpos : 0 < 2 ^ l := Nat.two_pow_pos l
  have heq : 2 ^ (s + l) * q + (2 ^ l * v + r) = 2 ^ l * (2 ^ s * q + v) + r := by
    rw [Nat.pow_add, Nat.mul_add, Nat.add_assoc, Nat.mul_comm (2 ^ s) (2 ^ l), Nat.mul_assoc]
  rw [heq, Nat.mul_add_div hpos, Nat.div_eq_of_lt hr, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]

/-- A part of a register has the value that is written to it, and the other bits of the register stay. This is what
the high bytes of x86 and the `Sn` of ARM are. -/
theorem aliasPart_write_read (part : AliasPart) (hlow : part.low ≤ part.high) (hhigh : part.high < part.width)
    (value : Bil.Exp) (state : Bil.State) (rest : Bil.Program) (fuel : Nat) (b : BitVec part.width)
    (v : BitVec (part.high + 1 - part.low)) (hbase : Bil.lookup state.env part.var = .ok (.bits b))
    (hvalue : Bil.evalExp state.env value = .ok (.bits v)) :
    ∃ state', Bil.execProgram (fuel + 2) state (part.write value :: rest) = Bil.execProgram (fuel + 1) state' rest ∧
      Reads state'.env part.read (part.high + 1 - part.low) v.toNat ∧
      Reads state'.env (.var part.var) part.width
        (2 ^ (part.high + 1) * (b.toNat / 2 ^ (part.high + 1)) + (2 ^ part.low * v.toNat + b.toNat % 2 ^ part.low)) ∧
      ∀ other, other ≠ part.var → Bil.lookup state'.env other = Bil.lookup state.env other := by
  obtain ⟨base, width, high, low⟩ := part
  dsimp only at hlow hhigh b v ⊢
  have hbaseRead : Reads state.env (.var (AliasPart.var ⟨base, width, high, low⟩)) width b.toNat := Reads.var hbase
  have hvalueRead : Reads state.env value (high + 1 - low) v.toNat := ⟨_, v, hvalue, rfl, rfl⟩
  have hlowLt : b.toNat % 2 ^ low < 2 ^ low := Nat.mod_lt _ (Nat.two_pow_pos low)
  -- the value that is moved to the register
  have hbelow : Reads state.env
      (if low = 0 then value else .concat value (.extract (low - 1) 0 (.var (AliasPart.var ⟨base, width, high, low⟩))))
      (high + 1) (2 ^ low * v.toNat + b.toNat % 2 ^ low) := by
    split
    · rename_i h0
      subst h0
      simpa [Nat.mod_one] using hvalueRead
    · rename_i h0
      have he := Reads.extract hbaseRead (Nat.zero_le (low - 1)) (by omega)
      have hc := Reads.concat hvalueRead he
      have hw : high + 1 - low + (low - 1 - 0 + 1) = high + 1 := by omega
      have hs : low - 1 - 0 + 1 = low := by omega
      rw [hw] at hc
      rw [hs] at hc
      simpa using hc
  have hall : Reads state.env
      (if high + 1 < width then
        .concat (.extract (width - 1) (high + 1) (.var (AliasPart.var ⟨base, width, high, low⟩)))
          (if low = 0 then value else .concat value (.extract (low - 1) 0 (.var (AliasPart.var ⟨base, width, high, low⟩))))
      else (if low = 0 then value else .concat value (.extract (low - 1) 0 (.var (AliasPart.var ⟨base, width, high, low⟩)))))
      width (2 ^ (high + 1) * (b.toNat / 2 ^ (high + 1)) + (2 ^ low * v.toNat + b.toNat % 2 ^ low)) := by
    split
    · rename_i hup
      have he := Reads.extract hbaseRead (show high + 1 ≤ width - 1 by omega) (show width - 1 < width by omega)
      have hc := Reads.concat he hbelow
      have hw : width - 1 - (high + 1) + 1 + (high + 1) = width := by omega
      have hs : width - 1 - (high + 1) + 1 = width - (high + 1) := by omega
      rw [hw, hs, Nat.mod_eq_of_lt] at hc
      · exact hc
      · have := b.isLt
        exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; rw [show high + 1 + (width - (high + 1)) = width by omega]; exact this)
    · rename_i hup
      have hw : width = high + 1 := by omega
      have hq : b.toNat / 2 ^ (high + 1) = 0 := Nat.div_eq_of_lt (hw ▸ b.isLt)
      rw [hq, Nat.mul_zero, Nat.zero_add]
      exact hw ▸ hbelow
  obtain ⟨w', y, he, hw', hy⟩ := hall
  refine ⟨{ env := Bil.bind state.env (AliasPart.var ⟨base, width, high, low⟩) (.bits y) }, ?_, ?_, ?_, ?_⟩
  · exact exec_move he
  · subst hw'
    have hnew : Reads (Bil.bind state.env (AliasPart.var ⟨base, w', high, low⟩) (.bits y))
        (.var (AliasPart.var ⟨base, w', high, low⟩)) w' y.toNat := Reads.var (lookup_bind_same _ _ _)
    unfold AliasPart.read
    dsimp only
    split
    · rename_i hwhole
      obtain ⟨h0, h1⟩ := hwhole
      subst h0
      have hq : b.toNat / 2 ^ (high + 1) = 0 := Nat.div_eq_of_lt (h1 ▸ b.isLt)
      have hyv : y.toNat = v.toNat := by simp [hy, hq, Nat.mod_one]
      rw [← hyv]
      have hw : high + 1 - 0 = w' := by omega
      rw [hw]
      exact hnew
    · have hx := Reads.extract hnew hlow hhigh
      have hs : high - low + 1 = high + 1 - low := by omega
      rw [hs, hy] at hx
      have hsum : high + 1 = (high + 1 - low) + low := by omega
      have hbits := part_bits (high + 1 - low) low (b.toNat / 2 ^ (high + 1)) v.toNat (b.toNat % 2 ^ low) hlowLt v.isLt
      rw [← hsum] at hbits
      rw [hbits] at hx
      exact hx
  · subst hw'
    rw [← hy]
    exact Reads.var (lookup_bind_same _ _ _)
  · intro other hother
    exact lookup_bind_ne _ _ hother

/-! ### The tables of the registers -/

/-- As in `x86_target` of the reference implementation. -/
theorem x86_status_registers :
    x86Register "ST0" = register "ST0" 80 80 ∧ x86Register "ST7" = register "ST7" 80 80 ∧
      x86Register "EFLAGS" = register "EFLAGS" 32 32 ∧ x86Register "MXCSR" = register "MXCSR" 32 32 ∧
      x86Register "FPU_CONTROL" = register "FPU_CONTROL" 16 16 ∧ x86Register "FPU_STATUS" = register "FPU_STATUS" 16 16 ∧
      x86Register "FPU_TAG" = register "FPU_TAG" 16 16 ∧ x8632Register "ST0" = register "ST0" 80 80 ∧
      x8632Register "EFLAGS" = register "EFLAGS" 32 32 ∧ x8632Register "MXCSR" = register "MXCSR" 32 32 ∧
      x8632Register "FPU_TAG" = register "FPU_TAG" 16 16 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- As in `arm_target` of the reference implementation, where `Sn` and `Qn` are aliases of `Dn`. -/
theorem arm_registers :
    arm32Register "D0" = register "D0" 64 64 ∧ arm32Register "D31" = register "D31" 64 64 ∧
      arm32Register "Q15" = register "Q15" 128 128 ∧ arm32Register "S1" = register "S1" 32 32 ∧
      arm32Register "FPSCR" = register "FPSCR" 32 32 ∧ arm32Register "TPIDRURO" = register "TPIDRURO" 32 32 ∧
      arm32Register "TPIDRURW" = register "TPIDRURW" 32 32 ∧ arm32Register "QF" = register "QF" 1 1 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `S0` and `S1` are the low and high halves of `D0`, `S31` the high half of `D15`, and `Qn` is `D(2n+1):D(2n)`. -/
theorem arm_aliases :
    armAliases "S0" = some (⟨"D0", 64, 31, 0⟩, []) ∧ armAliases "S1" = some (⟨"D0", 64, 63, 32⟩, []) ∧
      armAliases "S31" = some (⟨"D15", 64, 63, 32⟩, []) ∧
      armAliases "Q0" = some (⟨"D1", 64, 63, 0⟩, [⟨"D0", 64, 63, 0⟩]) ∧
      armAliases "Q15" = some (⟨"D31", 64, 63, 0⟩, [⟨"D30", 64, 63, 0⟩]) ∧
      armAliases "D0" = none ∧ armAliases "R0" = none ∧ armAliases "SP" = none ∧ armAliases "S32" = none ∧
      armAliases "Q16" = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 20000 in
/-- `R31` is the stack pointer, whose variable is `SP`, and PSTATE is what it has of each field. -/
theorem aarch64_status_registers :
    aarch64Register "DAIF" = register "DAIF" 4 4 ∧ aarch64Register "SPSel" = register "SPSel" 1 1 ∧
      aarch64Register "PAN" = register "PAN" 1 1 ∧ aarch64Register "UAO" = register "UAO" 1 1 ∧
      aarch64Register "R31" = register "SP" 64 64 ∧ aarch64Register "SP_EL0" = register "SP_EL0" 64 64 ∧
      aarch64Register "SP_EL1" = register "SP_EL1" 64 64 ∧ aarch64Register "CNTVCT_EL0" = register "CNTVCT_EL0" 64 64 ∧
      aarch64Register "FPCR" = register "FPCR" 32 32 ∧ aarch64Register "FPSR" = register "FPSR" 32 32 := by
  and_intros <;> rfl

set_option maxRecDepth 20000 in
theorem powerpc_status_registers :
    powerpcRegister "CR0" = register "CR0" 4 4 ∧ powerpcRegister "CR7" = register "CR7" 4 4 ∧
      powerpcRegister "FE" = register "FE" 1 1 ∧ powerpcRegister "FG" = register "FG" 1 1 ∧
      powerpcRegister "FL" = register "FL" 1 1 ∧ powerpcRegister "FU" = register "FU" 1 1 ∧
      powerpc32Register "CR0" = register "CR0" 4 4 ∧ powerpc32Register "FE" = register "FE" 1 1 ∧
      powerpcAliases "CR2" = some (⟨"CR2LT", 1, 0, 0⟩, [⟨"CR2GT", 1, 0, 0⟩, ⟨"CR2EQ", 1, 0, 0⟩, ⟨"CR2UN", 1, 0, 0⟩]) ∧
      powerpcAliases "CR2LT" = none := by
  and_intros <;> rfl

set_option maxRecDepth 20000 in
theorem riscv_status_registers :
    Assoc.get "FCSR" riscvGlobals = some (register "FCSR" 32 32) ∧ Assoc.get "VXRM" riscvGlobals = some (register "VXRM" 32 32) ∧
      Assoc.get "FCSR" riscv32Globals = some (register "FCSR" 32 32) ∧
      Assoc.get "VXRM" riscv32Globals = some (register "VXRM" 32 32) ∧
      Assoc.get "F31" riscv32Globals = some (register "F31" 64 64) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 20000 in
theorem mips_status_registers :
    Assoc.get "USERLOCAL" mipsGlobals = some (register "USERLOCAL" 64 64) ∧
      Assoc.get "USERLOCAL" mips32Globals = some (register "USERLOCAL" 32 32) ∧
      Assoc.get "F31" mipsGlobals = some (register "F31" 64 64) ∧
      Assoc.get "F31" mips32Globals = some (register "F31" 32 32) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### The prefixes of x86 -/

/-- What isn't a prefix ends them: a repeated string instruction has a prefix, a plain one doesn't. -/
theorem x86Prefixes_stop (long : Bool) (byte : Nat) (rest : List Nat) (h : x86LegacyPrefix byte = false)
    (hrex : long = false ∨ byte / 16 ≠ 4 ∨ (rest.head?.map x86LegacyPrefix).getD false = false) :
    x86Prefixes long (byte :: rest) = [] := by
  simp only [x86Prefixes, h, Bool.false_eq_true, ite_false]
  rcases hrex with rfl | hrex | hrex
  · simp
  · simp [hrex]
  · simp [hrex]

/-- The prefixes are bytes of the instruction. -/
theorem x86Prefixes_mem (long : Bool) (bytes : List Nat) (byte : Nat) (h : byte ∈ x86Prefixes long bytes) : byte ∈ bytes := by
  induction bytes with
  | nil => cases h
  | cons head tail ih =>
    unfold x86Prefixes at h
    split at h
    · dsimp only at h
      split at h
      · exact List.mem_cons_of_mem _ (ih h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih h)
    · split at h
      · exact List.mem_cons_of_mem _ (ih h)
      · cases h

/-- REP and REPNE are of one group: an instruction has one of them, the last one, which is what `x86-prefix` reports. -/
theorem x86Prefixes_one_repeat (long : Bool) (bytes : List Nat) :
    ((x86Prefixes long bytes).filter x86RepeatPrefix).length ≤ 1 := by
  induction bytes with
  | nil => simp [x86Prefixes]
  | cons head tail ih =>
    unfold x86Prefixes
    split
    · dsimp only
      split
      · exact ih
      · rename_i hboth
        by_cases hr : x86RepeatPrefix head = true
        · have hnone : (x86Prefixes long tail).any x86RepeatPrefix = false := by
            simpa [hr] using hboth
          have hempty : (x86Prefixes long tail).filter x86RepeatPrefix = [] := by
            simp only [List.any_eq_false] at hnone
            simp only [List.filter_eq_nil_iff]
            exact hnone
          simp [hr, hempty]
        · simpa [List.filter_cons, hr] using ih
    · split
      · exact ih
      · simp

theorem x86Prefixes_examples :
    x86Prefixes true [0xf3, 0xa4] = [0xf3] ∧ x86Prefixes false [0xf3, 0xa4] = [0xf3] ∧ x86Prefixes true [0xa4] = [] ∧
      x86Prefixes true [0xf2, 0xae] = [0xf2] ∧ x86Prefixes true [0xf3, 0xf2, 0xae] = [0xf2] ∧
      x86Prefixes true [0xf2, 0xf3, 0xae] = [0xf3] ∧ x86Prefixes true [0x66, 0xf3, 0xa5] = [0x66, 0xf3] ∧
      x86Prefixes true [0x48, 0xf3, 0xa4] = [0xf3] ∧ x86Prefixes false [0x48, 0xf3, 0xa4] = [] ∧
      x86Prefixes true [0xf3, 0x48, 0xab] = [0xf3] := by
  decide

/-! ### The likely calls of MIPS -/

theorem mips_likely_calls : mipsLikelyMnemonics.contains "bltzall" = true ∧ mipsLikelyMnemonics.contains "bgezall" = true ∧
    mipsLikelyMnemonics.contains "bltzal" = false ∧ mipsLikelyMnemonics.contains "bgezal" = false := by
  decide

/-! ### The order of the semantics -/

/-- The primitives that are bound first are primitives of the semantics, so that a name resolves to what it did. -/
theorem semanticsPrimitives_are_primitives : ∀ name ∈ semanticsPrimitives, name ∈ Primus.Semantics.primitiveNames := by
  intro name h
  exact (List.mem_filter.1 h).1

/-- Which names they are: every primitive but `replicate`, which the lookups handle first, however a definition binds it. -/
theorem mem_semanticsPrimitives (name : String) :
    name ∈ semanticsPrimitives ↔ name ∈ Primus.Semantics.primitiveNames ∧ name ≠ "replicate" := by
  simp [semanticsPrimitives, List.mem_filter]

/-- `replicate` is a primitive, so that it is the only one left out. -/
theorem replicate_is_primitive : "replicate" ∈ Primus.Semantics.primitiveNames := by decide

theorem primitive_not_core : ∀ name ∈ semanticsPrimitives, name.startsWith "core:" = false := by
  have key : ∀ name ∈ Primus.Semantics.primitiveNames, name.startsWith "core:" = false := by
    simp [Primus.Semantics.primitiveNames]
  exact fun name h => key name (List.mem_filter.1 h).1

private theorem get_prims (ps : List String) (rest : Globals) (name : String) :
    Assoc.get name ((ps.map fun n => ((n, .callable (.primitive n)) : String × PValue)) ++ rest) =
      if name ∈ ps then some (.callable (.primitive name)) else Assoc.get name rest := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    by_cases hp : name = p
    · subst hp
      simp [Assoc.get]
    · have hb : (name == p) = false := by simpa using hp
      have : Assoc.get name (((p :: ps).map fun n => ((n, .callable (.primitive n)) : String × PValue)) ++ rest) =
          Assoc.get name ((ps.map fun n => ((n, .callable (.primitive n)) : String × PValue)) ++ rest) := by
        simp [Assoc.get, List.lookup, hb]
      rw [this, ih]
      simp [hp]

/-- Binding the primitives first doesn't change what a name resolves to, unless a register has the name of a primitive,
as none has. -/
theorem lookup_primitiveGlobals (definitions rest : Globals) (name : String) (locals : Bap.Primus.Semantics.Locals)
    (hrest : ∀ n ∈ semanticsPrimitives, Assoc.get n definitions = none → Assoc.get n rest = none) :
    (primus% lookup) name locals ((lift% primitiveGlobals) definitions ++ rest) = (primus% lookup) name locals rest := by
  have hget : Assoc.get name ((lift% primitiveGlobals) definitions ++ rest) =
      if name ∈ semanticsPrimitives.filter (fun n => (Assoc.get n definitions).isNone) then
        some (.callable (.primitive name))
      else Assoc.get name rest := get_prims _ rest name
  unfold_lookup
  dsimp only
  rw [hget]
  by_cases hn : name ∈ semanticsPrimitives.filter (fun n => (Assoc.get n definitions).isNone)
  · have hmem := (List.mem_filter.1 hn).1
    have hnone := hrest name hmem (by simpa using (List.mem_filter.1 hn).2)
    have hcore := primitive_not_core name hmem
    have hprim := semanticsPrimitives_are_primitives name hmem
    simp [hn, hnone, hcore, hprim]
  · simp [hn]

theorem primitiveGlobals_spec (definitions : Globals) (binding : String × PValue)
    (h : binding ∈ (lift% primitiveGlobals) definitions) :
    binding.1 ∈ Primus.Semantics.primitiveNames ∧ Assoc.get binding.1 definitions = none ∧
      binding.2 = .callable (.primitive binding.1) := by
  unfold_primitive_globals at h
  simp only [List.mem_map, List.mem_filter, Option.isNone_iff_eq_none] at h
  obtain ⟨name, ⟨hname, hnone⟩, rfl⟩ := h
  exact ⟨semanticsPrimitives_are_primitives name hname, hnone, rfl⟩

/-- A window of the bytes of a decoder is long enough for an instruction and it holds the same bytes. -/
theorem instructionBytes_get (data : ByteArray) (offset index : Nat) (hindex : index < 16) (hsize : offset + index < data.size) :
    (instructionBytes data offset)[index]! = data[offset + index]! := by
  have bang_eq (page : ByteArray) (j : Nat) : page[j]! = (page.data[j]?).getD 0 := by
    have hpage : page[j]! = page.data[j]! := by
      by_cases hj : j < page.size
      · simp [getElem!_pos, hj]
        rfl
      · have hj' : ¬ j < page.data.size := hj
        simp [getElem!_neg, hj]
    rw [hpage, getElem!_def]
    cases page.data[j]? <;> rfl
  have hd : min (offset + 16) data.data.size - offset > index := by
    have : data.data.size = data.size := rfl
    omega
  rw [bang_eq, bang_eq, instructionBytes, ByteArray.data_extract, Array.getElem?_extract, ite_eq_left hd]

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
    {α} (classify : α → Flow) (hi : ∀ a d, Holds (inner a d) (Lifted classify a))
    (delay : Insn → Bool) (annul : Insn → Bool := fun _ => false)
    (sizes : Nat → ByteArray → IO (Option Nat) := fun _ _ => pure none) :
    RegisteredAs name { name := name, decode := decode, hasDelaySlot := delay, annulsSlot := annul, sizeAt := sizes } where
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

/-- MIPS scans cover their delay slots, and no other target has one. -/
theorem mips_delay_slots (base : Nat) :
    Holds (MIPS.disassembler base) (fun d => d.hasDelaySlot = mipsHasDelaySlot ∧ d.annulsSlot = mipsAnnulsSlot) ∧
      Holds (MIPS32.disassembler base) (fun d => d.hasDelaySlot = mipsHasDelaySlot ∧ d.annulsSlot = mipsAnnulsSlot) ∧
      Holds (X86.disassembler base) (fun d => ∀ insn, d.hasDelaySlot insn = false) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold MIPS.disassembler
    exact Holds.bind fun _ => Holds.pure ⟨rfl, rfl⟩
  · unfold MIPS32.disassembler
    exact Holds.bind fun _ => Holds.pure ⟨rfl, rfl⟩
  · unfold X86.disassembler
    exact Holds.bind fun _ => Holds.pure fun _ => rfl

/-- Registration data of the 11 target modules. -/
theorem x86_disassembler (base : Nat) :
    Holds (X86.disassembler base) (RegisteredAs "x86-llvm-primus") := by
  unfold X86.disassembler
  refine Holds.bind fun globals => Holds.pure ?_
  exact registeredAs_mk _ _ (decodeX86With globals base) (fun _ _ => rfl) _ (decodeX86With_lifted globals base) _ _ _

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
  exact registeredAs_mk _ _ (decodeAArch64With globals base) (fun _ _ => rfl) _ (decodeAArch64With_lifted globals base) _

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
  exact registeredAs_mk _ _ (decodeRISCVWith globals base) (fun _ _ => rfl) _ (decodeRISCVWith_lifted globals base) _ _ _

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
  exact registeredAs_mk _ _ (decodePowerPCWith globals base) (fun _ _ => rfl) _ (decodePowerPCWith_lifted globals base) _

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
  exact registeredAs_mk _ _ (decodeMIPSWith globals base) (fun _ _ => rfl) _ (decodeMIPSWith_lifted globals base) _ _

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
  exact registeredAs_mk _ _ (decodeARM32With globals base) (fun _ _ => rfl) _ (decodeARM32With_lifted globals base) _

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
  exact registeredAs_mk _ _ (decodeThumbWith globals base) (fun _ _ => rfl) _ (decodeThumbWith_lifted globals base) _ _ _

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
  exact registeredAs_mk _ _ (decodeX8632With globals base) (fun _ _ => rfl) _ (decodeX8632With_lifted globals base) _ _ _

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
  exact registeredAs_mk _ _ (decodeRISCV32With globals base) (fun _ _ => rfl) _ (decodeRISCV32With_lifted globals base) _ _ _

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
  exact registeredAs_mk _ _ (decodeMIPS32With globals base) (fun _ _ => rfl) _ (decodeMIPS32With_lifted globals base) _ _

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
  exact registeredAs_mk _ _ (decodePowerPC32With globals base) (fun _ _ => rfl) _ (decodePowerPC32With_lifted globals base) _

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
