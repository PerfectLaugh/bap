import BapTests.Support

namespace Bap.Tests.Symbolic

open Bap
open Bap.Symbolic

private def x : Bap.Var := ⟨"x", .imm 64, 0, false⟩
private def y : Bap.Var := ⟨"y", .imm 64, 0, false⟩
private def int (value : Nat) : Bil.Exp := .int (BitVec.ofNat 64 value)
private def xExpr : Expr := .var "x" 64

private def bit : Bap.Var := ⟨"c", .imm 1, 0, false⟩
private def bitExpr : Expr := .var "c" 1
private def equal (left right : Expr) : Expr := .app "=" 1 [left, right]
private def different (left right : Expr) : Expr := .app "distinct" 1 [left, right]

private def paths : IO Unit := do
  let env : Env := [(bit, bitExpr)]
  match Bap.Symbolic.run [.ifElse (.var bit) [] [], .special "after"] { env := env } with
  | .ok [yes, no] =>
    assertEqual "then path keeps its condition" true (← FFI.Z3.isUnsat (equal bitExpr (.const (BitVec.ofNat 1 0)) :: yes.state.constraints))
    assertEqual "else path keeps its condition" true (← FFI.Z3.isUnsat (equal bitExpr (.const (BitVec.ofNat 1 1)) :: no.state.constraints))
  | _ => throw <| IO.userError "both branches should reach the following statement"
  match Bap.Symbolic.run [.while (.int (BitVec.ofNat 1 0)) []] with
  | .ok [⟨state, .normal⟩] => assertEqual "while false adds no constraint" 0 state.constraints.length
  | _ => throw <| IO.userError "while false should be a no-op"
  match Bap.Symbolic.run [.while (.int (BitVec.ofNat 1 1)) []] {} 5 with
  | .ok [⟨_, .exhausted⟩] => IO.println "ok: while true reports the bound"
  | _ => throw <| IO.userError "while true should be reported as exhausted"
  let counter : Bap.Var := ⟨"i", .imm 8, 0, false⟩
  let counting : Bil.Program := [
    .move counter (.int (BitVec.ofNat 8 0)),
    .while (.bin .lt (.var counter) (.int (BitVec.ofNat 8 3))) [.move counter (.bin .add (.var counter) (.int (BitVec.ofNat 8 1)))]
  ]
  match Bap.Symbolic.run counting with
  | .ok [⟨state, .normal⟩] =>
    match Assoc.get counter state.env with
    | some value => assertEqual "concrete loop runs to its end" "(_ bv3 8)" value.render
    | none => throw <| IO.userError "missing loop counter"
  | _ => throw <| IO.userError "concrete loop should have one path"
  match Bap.Symbolic.run [.while (.var bit) []] { env := env } 4 with
  | .ok results =>
    assertTrue "symbolic loop exits" (results.any fun result => result.outcome matches .normal)
    assertTrue "symbolic loop reports the bound" (results.any fun result => result.outcome matches .exhausted)
  | .error error => throw <| IO.userError error
  let u : Bap.Var := ⟨"u", .imm 8, 0, false⟩
  let v : Bap.Var := ⟨"v", .imm 8, 0, false⟩
  match Bap.Symbolic.run [.move u (.unknown "same" (.imm 8)), .move v (.unknown "same" (.imm 8))] with
  | .ok [⟨state, .normal⟩] =>
    match Assoc.get u state.env, Assoc.get v state.env with
    | some first, some second =>
      assertEqual "unknowns are separate values" true (← FFI.Z3.isSat [different first second])
    | _, _ => throw <| IO.userError "missing unknowns"
  | _ => throw <| IO.userError "unexpected unknown results"

private def naming : IO Unit := do
  let dotted : Expr := .var "a.b" 8
  let underscored : Expr := .var "a_b" 8
  let zero : Expr := .const (BitVec.ofNat 8 0)
  let one : Expr := .const (BitVec.ofNat 8 1)
  assertEqual "names are not merged" true (← FFI.Z3.isSat [equal dotted zero, equal underscored one])
  assertEqual "structural equality sees names" false (Expr.structuralEq dotted underscored)
  assertEqual "structural equality sees widths" false (Expr.structuralEq (.var "x" 8) (.var "x" 64))
  assertEqual "structural equality sees kinds" false (Expr.structuralEq (.app "x" 1 []) (.var "x" 1))
  assertEqual "widths are separate variables" true
    (← FFI.Z3.isSat [equal (.var "x" 8) zero, equal (.var "x" 64) (.const (BitVec.ofNat 64 1))])
  assertEqual "odd names are valid symbols" true
    (← FFI.Z3.isSat [equal (.var "1 x|\\" 8) zero, equal (.var "true" 8) zero, equal (.var "" 8) zero])

private def operators : List Bil.BinOp :=
  [.add, .sub, .mul, .div, .sdiv, .rem, .srem, .smod, .lshift, .rshift, .ashift, .and, .or, .xor,
   .eq, .neq, .lt, .le, .gt, .ge, .slt, .sle, .sgt, .sge]

/-- Z3 and the BIL evaluator agree on every operator, including the division and modulus corners. -/
private def checkOperators : IO Unit := do
  let samples : List Nat := [0, 1, 3, 0x80, 0xf9, 0xff]
  let a : Bap.Var := ⟨"a", .imm 8, 0, false⟩
  let b : Bap.Var := ⟨"b", .imm 8, 0, false⟩
  let aExpr : Expr := .var "a" 8
  let bExpr : Expr := .var "b" 8
  let state : State := { env := [(a, aExpr), (b, bExpr)] }
  for op in operators do
    for left in samples do
      for right in samples do
        let leftValue := BitVec.ofNat 8 left
        let rightValue := BitVec.ofNat 8 right
        let exp : Bil.Exp := .bin op (.var a) (.var b)
        let concrete := Bil.evalExp [(a, .bits leftValue), (b, .bits rightValue)] exp
        match evalExp state exp, concrete with
        | .ok symbolic, .ok (.bits expected) =>
          let bound := [equal aExpr (.const leftValue), equal bExpr (.const rightValue)]
          assertEqual s!"{repr op} {left} {right}" true
            (← FFI.Z3.isUnsat (different symbolic (.const expected) :: bound))
        | _, _ => throw <| IO.userError "operator evaluation failed"

/-- Every expression form is well sorted, in terms and in assertions: Z3 can refute each one. -/
private def checkSorts : IO Unit := do
  let wide : Expr := .var "w" 8
  let contradiction (value : Expr) : IO Unit := do
    assertEqual s!"well sorted: {value.render}" true (← FFI.Z3.isUnsat [Expr.eqOne value, Expr.eqZero value])
  contradiction bitExpr
  contradiction (.const (BitVec.ofNat 1 1))
  contradiction (Expr.bool true)
  contradiction (equal wide wide)
  contradiction (.app "bvult" 1 [wide, wide])
  contradiction (.app "bvnot" 1 [bitExpr])
  contradiction (.app "bvand" 1 [equal wide wide, bitExpr])
  contradiction (.extract 3 3 wide)
  contradiction (.ite bitExpr bitExpr (equal wide wide))
  contradiction (.ite (equal wide wide) (equal wide wide) bitExpr)
  contradiction (.extract 8 8 (.concat bitExpr wide))
  contradiction (.extract 0 0 (.select "m" (.var "p" 64)))
  contradiction (.extract 0 0 (.app "(_ sign_extend 8)" 16 [wide]))
  assertEqual "assert of a bit" true (← FFI.Z3.isUnsat [bitExpr, Expr.eqZero bitExpr])
  assertEqual "assert of a literal" true (← FFI.Z3.isUnsat [.const (BitVec.ofNat 1 0)])
  assertEqual "assert of a true literal" true (← FFI.Z3.isSat [.const (BitVec.ofNat 1 1)])

def run : IO Unit := do
  let script := renderScript [Expr.eqOne xExpr]
  assertTrue "SMT declares symbolic xExpr" ((script.splitOn "declare-const |x!64| (_ BitVec 64)").length > 1)
  assertTrue "SMT uses bitvector logic" ((script.splitOn "(set-logic QF_BV)").length > 1)
  assertEqual "SMT satisfiable" true (← FFI.Z3.isSat [Expr.eqOne xExpr])
  assertEqual "SMT contradictory" true (← FFI.Z3.isUnsat [Expr.eqOne xExpr, Expr.eqZero xExpr])
  match (← (FFI.Z3.checkSat "(declare-const c (_ BitVec 1)) (assert c)").toBaseIO) with
  | .error _ => IO.println "ok: Z3 reports an ill-sorted script as an error"
  | .ok _ => throw <| IO.userError "ill-sorted script accepted"
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
  | .ok [⟨_, .exhausted⟩] => IO.println "ok: symbolic fuel exhaustion reported"
  | _ => throw <| IO.userError "symbolic zero-fuel execution was not reported as exhausted"
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
  match evalExp {} (.extract 0 5 (.int (BitVec.ofNat 8 0x80))) with
  | .error _ => IO.println "ok: inverted symbolic extract rejected"
  | .ok _ => throw <| IO.userError "inverted symbolic extract succeeded"
  paths
  naming
  checkOperators
  checkSorts

end Bap.Tests.Symbolic
