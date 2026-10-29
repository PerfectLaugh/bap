import BapTests.Support

namespace Bap.Tests.SymbolicMemory

open Bap
open Bap.Symbolic

private def address : Expr := .const (BitVec.ofNat 64 0x1000)
private def value : Expr := .const (BitVec.ofNat 32 0xdeadbeef)
private def expectedLittle : Expr := .const (BitVec.ofNat 32 0xdeadbeef)
private def expectedBig : Expr := .const (BitVec.ofNat 32 0xefbeadde)
private def memVar : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
private def resultVar : Bap.Var := ⟨"result", .imm 32, 0, false⟩

private def different (left right : Expr) : Expr := .app "distinct" 1 [left, right]

def run : IO Unit := do
  let written := Bap.Symbolic.Memory.write Bap.Symbolic.Memory.empty address value .little 4
  let little := Bap.Symbolic.Memory.read written address .little 4
  let big := Bap.Symbolic.Memory.read written address .big 4
  assertEqual "symbolic memory little endian" true (← FFI.Z3.isUnsat [different little expectedLittle])
  assertEqual "symbolic memory big endian" true (← FFI.Z3.isUnsat [different big expectedBig])
  assertEqual "symbolic default zero byte" "(_ bv0 8)" (Bap.Symbolic.Memory.readByte Bap.Symbolic.Memory.empty address |>.render)
  let byteMemory := Bap.Symbolic.Memory.writeByte Bap.Symbolic.Memory.empty address (.const (BitVec.ofNat 8 9))
  assertEqual "symbolic byte write/read" "(_ bv9 8)" (Bap.Symbolic.Memory.readByte byteMemory address |>.render)
  let bilAddress : Bil.Exp := .int (BitVec.ofNat 64 0x1000)
  let bilValue : Bil.Exp := .int (BitVec.ofNat 32 0xdeadbeef)
  let program : Bil.Program := [
    .move memVar (.store (.var memVar) bilAddress bilValue .little 4),
    .move resultVar (.load (.var memVar) bilAddress .big 4)
  ]
  match Bap.Symbolic.run program with
  | .error error => throw <| IO.userError error
  | .ok [result] =>
    match Assoc.get resultVar result.state.env with
    | some loaded => assertEqual "BIL symbolic memory load" true (← FFI.Z3.isUnsat [different loaded expectedBig])
    | none => throw <| IO.userError "missing symbolic memory result"
  | .ok _ => throw <| IO.userError "unexpected symbolic memory result count"

end Bap.Tests.SymbolicMemory
