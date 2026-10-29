import BapTests.Support

namespace Bap.Tests.Symbolic

open Bap
open Bap.Symbolic

private def x : Bap.Var := ⟨"x", .imm 64, 0, false⟩
private def y : Bap.Var := ⟨"y", .imm 64, 0, false⟩
private def int (value : Nat) : Bil.Exp := .int (BitVec.ofNat 64 value)
private def xExpr : Expr := .var "x" 64

def run : IO Unit := do
  let script := renderScript [Expr.eqOne xExpr]
  assertTrue "SMT declares symbolic xExpr" ((script.splitOn "declare-const x (_ BitVec 64)").length > 1)
  assertTrue "SMT uses bitvector logic" ((script.splitOn "(set-logic QF_BV)").length > 1)
  assertEqual "SMT satisfiable" true (← FFI.Z3.isSat [Expr.eqOne xExpr])
  assertEqual "SMT contradictory" true (← FFI.Z3.isUnsat [Expr.eqOne xExpr, Expr.eqZero xExpr])
  let env : Env := [(x, xExpr)]
  match evalExp { env := env } (.bin .add (.var x) (int 2)) with
  | .ok value => assertEqual "symbolic addition width" 64 value.width
  | .error error => throw <| IO.userError error
  let program : Bil.Program := [
    .move y (.bin .add (.var x) (int 2)),
    .ifElse (.bin .gt (.var y) (int 0)) [.jmp (int 1)] [.jmp (int 2)]
  ]
  match Bap.Symbolic.run program { env := env } with
  | .error error => throw <| IO.userError error
  | .ok results =>
    assertEqual "symbolic branch count" 2 results.length
    for result in results do
      assertEqual "symbolic path is satisfiable" true (← FFI.Z3.isSat result.state.constraints)
  match Bap.Symbolic.run [.jmp (int 1)] { env := env } 0 with
  | .error _ => IO.println "ok: symbolic fuel exhaustion reported"
  | .ok _ => throw <| IO.userError "symbolic zero-fuel execution succeeded"
  let checkCast (name : String) (exp : Bil.Exp) (expected : Expr) : IO Unit := do
    match evalExp {} exp with
    | .error error => throw <| IO.userError error
    | .ok actual =>
      assertEqual s!"{name} width" expected.width actual.width
      assertEqual name true (← FFI.Z3.isUnsat [.app "distinct" 1 [actual, expected]])
  checkCast "symbolic signed extension" (.cast .signed 16 (.int (BitVec.ofNat 8 0x80)))
    (.const (BitVec.ofNat 16 0xff80))
  checkCast "symbolic unsigned extension" (.cast .unsigned 16 (.int (BitVec.ofNat 8 0x80)))
    (.const (BitVec.ofNat 16 0x80))
  checkCast "symbolic low extension" (.cast .low 16 (.int (BitVec.ofNat 12 0xab8)))
    (.const (BitVec.ofNat 16 0xab8))
  checkCast "symbolic low truncation" (.cast .low 4 (.int (BitVec.ofNat 12 0xab8)))
    (.const (BitVec.ofNat 4 8))
  checkCast "symbolic high truncation" (.cast .high 4 (.int (BitVec.ofNat 12 0xab8)))
    (.const (BitVec.ofNat 4 0xa))
  match evalExp {} (.cast .high 16 (.int (BitVec.ofNat 8 0x80))) with
  | .error _ => IO.println "ok: invalid symbolic high cast rejected"
  | .ok _ => throw <| IO.userError "invalid symbolic high cast succeeded"

end Bap.Tests.Symbolic
