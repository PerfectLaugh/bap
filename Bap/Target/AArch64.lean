import Bap.Target.LLVMLift

namespace Bap.Target.AArch64

private def decodeWith (globals : Primus.Semantics.Environment) (base : Nat)
    (address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← LLVMLift.decodeAArch64With globals base address data))
  catch error =>
    pure (.error (toString error))

/-- The instruction at an address of bytes that start at `base`, lifted by the semantics of AArch64. -/
def decodeAt (base address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  decodeWith (← LLVMLift.aarch64Environment) base address data

/-- The decoder of AArch64, with its semantics loaded once, for a project: what it lifts is what the instructions say, with no top byte
ignored, as that is what Linux sets up and not the architecture. See `emulatorDisassembler`. -/
def disassembler (base : Nat := 0) : IO Disasm.Disassembler := do
  let globals ← LLVMLift.aarch64Environment
  pure { name := "aarch64-llvm-primus", decode := decodeWith globals base }

/-! ### Top byte ignore

Linux runs a program with the top byte of an address ignored, for what it loads and stores and where it goes to: TCR_EL1.TBI0 is
set and TBID0 isn't. An address is translated by bits 55 to 0, with bit 55 for the bits above it, as `AArch64.AddrTop` and
`BranchAddr` of the architecture have it, so that a pointer may carry a tag in its top byte. -/

/-- A value of 64 bits as the architecture translates it: bits 55 to 0, and bit 55 above them. -/
def untag (value : Nat) : Nat :=
  let low := value % 2 ^ 56
  if low ≥ 2 ^ 55 then low + (2 ^ 64 - 2 ^ 56) else low

/-- An address with its top byte ignored, which an address that is a number already is when it has no tag. -/
def ignoreTopByte (address : Bil.Exp) : Bil.Exp :=
  match address with
  | @Bil.Exp.int width value =>
    if width == 64 then
      if untag value.toNat == value.toNat then address else .int (BitVec.ofNat 64 (untag value.toNat))
    else .cast .signed 64 (.extract 55 0 address)
  | _ => .cast .signed 64 (.extract 55 0 address)

/-- An expression whose loads and stores ignore the top byte of their addresses. -/
def ignoreTopByteExp : Bil.Exp → Bil.Exp
  | .load memory address endian size => .load (ignoreTopByteExp memory) (ignoreTopByte (ignoreTopByteExp address)) endian size
  | .store memory address value endian size =>
    .store (ignoreTopByteExp memory) (ignoreTopByte (ignoreTopByteExp address)) (ignoreTopByteExp value) endian size
  | .bin op left right => .bin op (ignoreTopByteExp left) (ignoreTopByteExp right)
  | .un op value => .un op (ignoreTopByteExp value)
  | .cast kind width value => .cast kind width (ignoreTopByteExp value)
  | .letIn var value body => .letIn var (ignoreTopByteExp value) (ignoreTopByteExp body)
  | .ite condition yes no => .ite (ignoreTopByteExp condition) (ignoreTopByteExp yes) (ignoreTopByteExp no)
  | .extract high low value => .extract high low (ignoreTopByteExp value)
  | .concat left right => .concat (ignoreTopByteExp left) (ignoreTopByteExp right)
  | other => other

mutual
/-- A statement as it runs with the top byte ignored: of what it loads and stores, and of where it jumps to. -/
def ignoreTopByteStmt : Bil.Stmt → Bil.Stmt
  | .move var value => .move var (ignoreTopByteExp value)
  | .jmp target => .jmp (ignoreTopByte (ignoreTopByteExp target))
  | .while condition body => .while (ignoreTopByteExp condition) (ignoreTopByteProgram body)
  | .ifElse condition yes no => .ifElse (ignoreTopByteExp condition) (ignoreTopByteProgram yes) (ignoreTopByteProgram no)
  | other => other

/-- `ignoreTopByteStmt` of each statement. -/
def ignoreTopByteProgram : List Bil.Stmt → List Bil.Stmt
  | [] => []
  | stmt :: rest => ignoreTopByteStmt stmt :: ignoreTopByteProgram rest
end

/-- The decoder of a program that runs on Linux, where the top byte of an address is ignored. -/
def emulatorDisassembler (base : Nat := 0) : IO Disasm.Disassembler := do
  let globals ← LLVMLift.aarch64Environment
  pure {
    name := "aarch64-llvm-primus-tbi"
    decode := fun address data => do
      pure ((← decodeWith globals base address data).map fun insn => { insn with bil := ignoreTopByteProgram insn.bil }) }

end Bap.Target.AArch64
