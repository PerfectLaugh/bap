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

def disassembler (base : Nat := 0) : IO Disasm.Disassembler := do
  let globals ← LLVMLift.x8632Environment
  let memo ← IO.mkRef {}
  pure { name := "i386-llvm-primus", decode := decodeMemo memo globals base, sizeAt := LLVMLift.sizeAt "i386" base }

end Bap.Target.X8632
