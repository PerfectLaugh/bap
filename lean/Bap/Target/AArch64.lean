import Bap.Target.LLVMLift

namespace Bap.Target.AArch64

private def decodeWith (globals : Primus.Semantics.Environment) (base : Nat)
    (address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← LLVMLift.decodeAArch64With globals base address data))
  catch error =>
    pure (.error (toString error))

private initialize environmentCache : IO.Ref (Option Primus.Semantics.Environment) ← IO.mkRef none

private def environment : IO Primus.Semantics.Environment := do
  match ← environmentCache.get with
  | some environment => pure environment
  | none =>
    let environment ← LLVMLift.aarch64Environment
    environmentCache.set (some environment)
    pure environment

def decodeAt (base address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  decodeWith (← environment) base address data

def disassembler (base : Nat := 0) : IO Disasm.Disassembler := do
  let globals ← environment
  pure ⟨"aarch64-llvm-primus", decodeWith globals base⟩

end Bap.Target.AArch64
