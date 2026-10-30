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

private def equal (left right : Expr) : Expr := .app "=" 1 [left, right]
private def byte (value : Nat) : Expr := .const (BitVec.ofNat 8 value)
private def address64 (value : Nat) : Expr := .const (BitVec.ofNat 64 value)

private def regressions : IO Unit := do
  let x : Expr := .var "x" 64
  let y : Expr := .var "y" 64
  let aliased := (Bap.Symbolic.Memory.empty.writeByte x (byte 1)).writeByte y (byte 2)
  let readX := aliased.readByte x
  assertEqual "aliased write is visible" true (← FFI.Z3.isUnsat [equal x y, different readX (byte 2)])
  assertEqual "distinct write leaves the byte" true
    (← FFI.Z3.isUnsat [different x y, different readX (byte 1)])
  let overlap := Bap.Symbolic.Memory.write Bap.Symbolic.Memory.empty (address64 4) (.const (BitVec.ofNat 16 0xbbaa)) .little 2
  assertEqual "concrete overlap resolved statically" "((_ extract 15 8) (_ bv48042 16))"
    (Bap.Symbolic.Memory.read overlap (address64 5) .little 1).render
  assertEqual "concrete distinct write is skipped" "(|mem@64| (_ bv9 64))"
    (overlap.readByte (address64 9)).render
  let unwritten := Bap.Symbolic.Memory.empty.readByte (address64 0x1000)
  assertEqual "unwritten byte can be 5" true (← FFI.Z3.isSat [equal unwritten (byte 5)])
  assertEqual "unwritten byte can be 6" true (← FFI.Z3.isSat [equal unwritten (byte 6)])
  assertEqual "unwritten bytes are a function of the address" true
    (← FFI.Z3.isUnsat [equal x y, different (Bap.Symbolic.Memory.empty.readByte x) (Bap.Symbolic.Memory.empty.readByte y)])
  let m1 : Bap.Var := ⟨"m1", .mem 64 8, 0, false⟩
  let m2 : Bap.Var := ⟨"m2", .mem 64 8, 0, false⟩
  let r1 : Bap.Var := ⟨"r1", .imm 8, 0, false⟩
  let r2 : Bap.Var := ⟨"r2", .imm 8, 0, false⟩
  let at0 : Bil.Exp := .int (BitVec.ofNat 64 0)
  match Bap.Symbolic.run [
    .move m1 (.store (.var m1) at0 (.int (BitVec.ofNat 8 7)) .little 1),
    .move r1 (.load (.var m1) at0 .little 1),
    .move r2 (.load (.var m2) at0 .little 1)
  ] with
  | .ok [result] =>
    match Assoc.get r1 result.state.env, Assoc.get r2 result.state.env with
    | some one, some two =>
      assertEqual "write is visible in its memory" true (← FFI.Z3.isUnsat [different one (byte 7)])
      assertEqual "write is not visible in another memory" true (← FFI.Z3.isSat [different two (byte 7)])
    | _, _ => throw <| IO.userError "missing memory results"
  | _ => throw <| IO.userError "unexpected memory variable results"

def run : IO Unit := do
  let written := Bap.Symbolic.Memory.write Bap.Symbolic.Memory.empty address value .little 4
  let little := Bap.Symbolic.Memory.read written address .little 4
  let big := Bap.Symbolic.Memory.read written address .big 4
  assertEqual "symbolic memory little endian" true (← FFI.Z3.isUnsat [different little expectedLittle])
  assertEqual "symbolic memory big endian" true (← FFI.Z3.isUnsat [different big expectedBig])
  assertEqual "symbolic unwritten byte is unconstrained" "(|mem@64| (_ bv4096 64))"
    (Bap.Symbolic.Memory.readByte Bap.Symbolic.Memory.empty address |>.render)
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
  regressions


end Bap.Tests.SymbolicMemory
