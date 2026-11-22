import Bap.Target.LLVMLift

namespace Bap.Target.X8632

private def decodeWith (globals : Primus.Semantics.Environment) (base : Nat)
    (address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← LLVMLift.decodeX8632With globals base address data))
  catch error =>
    pure (.error (toString error))

def decodeAt (base address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  decodeWith (← LLVMLift.x8632Environment) base address data

private def decodeMemo (memo : IO.Ref LLVMLift.LiftMemo) (globals : Primus.Semantics.Environment) (base : Nat)
    (address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← LLVMLift.decodeX8632Memo memo globals base address data))
  catch error =>
    pure (.error (toString error))

private def decodeLoop (memo : IO.Ref LLVMLift.LiftMemo) (globals : Primus.Semantics.Environment) (base : Nat)
    (address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← LLVMLift.decodeX8632Loop memo globals base address data))
  catch error =>
    pure (.error (toString error))

/-- The decoder of a project: an instruction that repeats by going back to itself is one loop, as `Disasm.Insn.asLoop` has it, for
what reads the code and doesn't run it. See `emulatorDisassembler`. -/
def disassembler (base : Nat := 0) : IO Disasm.Disassembler := do
  let globals ← LLVMLift.x8632Environment
  let memo ← IO.mkRef {}
  pure { name := "i386-llvm-primus", decode := decodeLoop memo globals base, sizeAt := LLVMLift.sizeAt "i386" base }

/-- The decoder of what runs: an instruction is what the semantics lift, of which a repeated one is a round of it. -/
def emulatorDisassembler (base : Nat := 0) : IO Disasm.Disassembler := do
  let globals ← LLVMLift.x8632Environment
  let memo ← IO.mkRef {}
  pure { name := "i386-llvm-primus", decode := decodeMemo memo globals base, sizeAt := LLVMLift.sizeAt "i386" base }

end Bap.Target.X8632
