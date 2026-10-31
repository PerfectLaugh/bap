import BapTests.Support
import Bap.Proofs.SmtReader

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

/-- The text given to Z3 reads as the script it is the printing of. -/
private def reader : IO Unit := do
  let path := [equal xExpr (.const (BitVec.ofNat 64 7)), equal (.select "mem" xExpr) (.const (BitVec.ofNat 8 1)),
    .app "bvult" 1 [.extract 7 0 xExpr, .concat (.extract 3 0 xExpr) (.extract 3 0 (.var "with space|bar" 64))]]
  match Proofs.Symbolic.SmtReader.readScript (renderScript path) with
  | none => throw <| IO.userError "a script should be read"
  | some script =>
    assertEqual "a script reads back to its commands" 8 script.length
    assertEqual "reading then printing is the text" (renderScript path)
      (String.intercalate "\n" (script.map Proofs.Symbolic.SmtCommand.print))
  assertTrue "a script with a stray parenthesis isn't one" (Proofs.Symbolic.SmtReader.readScript ")(").isNone

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

private def nodeCount : Expr → Nat
  | .var .. | .const .. => 1
  | .app _ _ args => 1 + (args.attach.map fun ⟨a, _⟩ => nodeCount a).sum
  | .extract _ _ value => 1 + nodeCount value
  | .concat left right => 1 + nodeCount left + nodeCount right
  | .ite condition yes no => 1 + nodeCount condition + nodeCount yes + nodeCount no
  | .select _ address => 1 + nodeCount address

private def inputs : IO Unit := do
  match Bap.Symbolic.run [.move y (.bin .add (.var x) (int 2))] with
  | .ok [⟨state, .normal⟩] =>
    match Assoc.get y state.env with
    | some value =>
      let input : Expr := .var (inputName x) 64
      assertEqual "unset register is an input" true
        (← FFI.Z3.isUnsat [different value (.app "bvadd" 64 [input, .const (BitVec.ofNat 64 2)])])
      assertEqual "input is unconstrained" true
        (← FFI.Z3.isSat [equal input (.const (BitVec.ofNat 64 7))])
    | none => throw <| IO.userError "missing assigned register"
  | _ => throw <| IO.userError "reading an unset register should succeed"
  match evalExp {} (.var x), evalExp {} (.var x) with
  | .ok first, .ok second => assertEqual "an input is one value" true (← FFI.Z3.isUnsat [different first second])
  | _, _ => throw <| IO.userError "input evaluation failed"
  let mem : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
  match evalExp {} (.var mem) with
  | .error _ => IO.println "ok: memory is not a bitvector input"
  | .ok _ => throw <| IO.userError "memory read as a bitvector"

private def rejected (name : String) (result : Except String α) : IO Unit :=
  match result with
  | .error _ => IO.println s!"ok: {name}"
  | .ok _ => throw <| IO.userError s!"{name}: accepted"

private def zeroWidth : IO Unit := do
  let mem : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
  let empty : Bap.Var := ⟨"empty", .imm 0, 0, false⟩
  rejected "zero-size load rejected" (evalExp {} (.load (.var mem) (int 0) .little 0))
  rejected "zero-width constant rejected" (evalExp {} (.int (BitVec.ofNat 0 0)))
  rejected "zero-width input rejected" (evalExp {} (.var empty))
  rejected "zero-width unknown rejected" (evalExp {} (.unknown "u" (.imm 0)))
  rejected "zero-size store rejected" (Bap.Symbolic.run [.move mem (.store (.var mem) (int 0) (.int (BitVec.ofNat 8 1)) .little 0)])
  rejected "overlapping store rejected"
    (Bap.Symbolic.run [.move ⟨"small", .mem 1 8, 0, false⟩
      (.store (.var ⟨"small", .mem 1 8, 0, false⟩) (.int (BitVec.ofNat 1 0)) (.int (BitVec.ofNat 24 1)) .little 3)])

/-- What the proofs of `Bap/Proofs/Symbolic.lean` found: operands the sort system has no term for are rejected. -/
private def wellSorted : IO Unit := do
  let wide : Bap.Var := ⟨"wide", .imm 16, 0, false⟩
  let narrow : Bap.Var := ⟨"narrow", .imm 8, 0, false⟩
  rejected "operands of different widths rejected" (evalExp {} (.bin .add (.var wide) (.var narrow)))
  rejected "comparison of different widths rejected" (evalExp {} (.bin .eq (.var wide) (.var narrow)))
  let mem : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
  let written := Bap.Symbolic.Memory.empty.writeByte (.var "at32" 32) (.const (BitVec.ofNat 8 7))
  let read64 := written.readByte (.var "at64" 64)
  assertEqual "addresses of different widths are different locations"
    (Bap.Symbolic.Memory.empty.readByte (.var "at64" 64)).render read64.render
  assertEqual "reading another width is well sorted" true (← FFI.Z3.isSat [Expr.eqOne (equal read64 read64)])
  rejected "reading no bytes rejected" (Bap.Symbolic.Memory.empty.read (.var "at" 64) .little 0)
  rejected "loading no bytes rejected" (evalExp {} (.load (.var mem) (int 0) .big 0))
  match Bap.Symbolic.Memory.empty.read (.var "at" 64) .little 1 with
  | .ok byte => assertEqual "reading a byte has eight bits" 8 byte.width
  | .error error => throw <| IO.userError error

/-- Different variables are different inputs, whatever part of them differs, and no input is an unknown. -/
private def inputNames : IO Unit := do
  let base : Bap.Var := ⟨"v", .imm 8, 0, false⟩
  let others : List Bap.Var := [{ base with isVirtual := true }, { base with index := 1 }, { base with name := "w" },
    { base with typ := .imm 16 }, { base with typ := .unit }, { base with typ := .mem 64 8 },
    { base with typ := .mem 32 8 }, { base with typ := .mem 64 16 }, { base with typ := .unknown }]
  for other in base :: others do
    for another in base :: others do
      assertEqual s!"{repr other} and {repr another}" (other == another) (inputName other == inputName another)
  let virtual : Bap.Var := { base with isVirtual := true }
  match evalExp {} (.var base), evalExp {} (.var virtual) with
  | .ok first, .ok second =>
    assertEqual "a variable and its virtual namesake are separate inputs" true (← FFI.Z3.isSat [different first second])
  | _, _ => throw <| IO.userError "input evaluation failed"
  let flag : Bap.Var := ⟨"f", .unit, 0, false⟩
  let bitFlag : Bap.Var := ⟨"f", .imm 1, 0, false⟩
  match evalExp {} (.var flag), evalExp {} (.var bitFlag) with
  | .ok first, .ok second =>
    assertEqual "one width and another type are separate inputs" true (← FFI.Z3.isSat [different first second])
  | _, _ => throw <| IO.userError "input evaluation failed"
  let trap : Bap.Var := ⟨"unknown_a#0?", .imm 8, 0, false⟩
  match evalExp {} (.var trap), evalExp {} (.unknown "a#0" (.imm 8)) with
  | .ok first, .ok second =>
    assertEqual "an input is not an unknown of the same spelling" true (← FFI.Z3.isSat [different first second])
  | _, _ => throw <| IO.userError "input evaluation failed"

/-- Soundness covers unknowns: a run that doesn't reach one is covered as ever, and one that does under any oracle. -/
private def unknowns : IO Unit := do
  let u : Bap.Var := ⟨"u", .imm 8, 0, false⟩
  let program : Bil.Program := [
    .ifElse (.bin .eq (.var x) (int 0)) [.move u (.int (BitVec.ofNat 8 1))] [.move u (.unknown "drawn" (.imm 8))]]
  match Bil.run program { env := [(x, .bits (BitVec.ofNat 64 0))] } with
  | .ok (final, _) => assertBits "a run past an unknown it doesn't reach" (BitVec.ofNat 8 1) (Bil.lookup final.env u)
  | .error error => throw <| IO.userError error
  match Bap.Symbolic.run program with
  | .ok [yes, no] =>
    assertEqual "both paths are explored" true
      (← FFI.Z3.isSat yes.state.constraints <&&> FFI.Z3.isSat no.state.constraints)
    match Assoc.get u no.state.env with
    | some value =>
      assertEqual "an unknown may be any value" true
        (← FFI.Z3.isSat (equal value (.const (BitVec.ofNat 8 7)) :: no.state.constraints))
    | none => throw <| IO.userError "missing unknown"
  | _ => throw <| IO.userError "unexpected unknown paths"
  let mem : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
  match Bap.Symbolic.run [.move mem (.unknown "image" (.mem 64 8)), .move u (.load (.var mem) (int 0) .little 1)] with
  | .ok [⟨state, .normal⟩] =>
    match Assoc.get u state.env with
    | some value =>
      assertEqual "an unknown memory is well sorted" true (← FFI.Z3.isSat [equal value (.const (BitVec.ofNat 8 7))])
    | none => throw <| IO.userError "missing load"
  | _ => throw <| IO.userError "unexpected unknown memory results"

private def memoryChoice : IO Unit := do
  let mem : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
  let result : Bap.Var := ⟨"r", .imm 8, 0, false⟩
  let at0 := int 0
  let stored (value : Nat) : Bil.Exp := .store (.var mem) at0 (.int (BitVec.ofNat 8 value)) .little 1
  let byteAt (value : Nat) : Expr := .const (BitVec.ofNat 8 value)
  match evalExp {} (.load (.ite (.var bit) (stored 1) (stored 2)) at0 .little 1) with
  | .ok loaded =>
    let c : Expr := .var (inputName bit) 1
    assertEqual "conditional memory, then" true (← FFI.Z3.isUnsat [Expr.eqOne c, different loaded (byteAt 1)])
    assertEqual "conditional memory, else" true (← FFI.Z3.isUnsat [Expr.eqZero c, different loaded (byteAt 2)])
    assertEqual "conditional memory, either" true (← FFI.Z3.isSat [equal loaded (byteAt 1)])
  | .error error => throw <| IO.userError error
  match evalExp {} (.load (.ite (.int (BitVec.ofNat 1 1)) (stored 1) (stored 2)) at0 .little 1) with
  | .ok loaded => assertEqual "known condition picks a memory" "((_ extract 7 0) (_ bv1 8))" loaded.render
  | .error error => throw <| IO.userError error
  let _ := result

private def sameBase : IO Unit := do
  let base : Expr := .var "b" 64
  let offset (value : Nat) : Expr := .app "bvadd" 64 [base, .const (BitVec.ofNat 64 value)]
  let lowered (value : Nat) : Expr := .app "bvsub" 64 [base, .const (BitVec.ofNat 64 value)]
  let byteAt (value : Nat) : Expr := .const (BitVec.ofNat 8 value)
  let written := Bap.Symbolic.Memory.empty.writeByte (offset 1) (byteAt 7)
  assertEqual "different offsets need no guard" (Bap.Symbolic.Memory.empty.readByte (offset 2)).render (written.readByte (offset 2)).render
  assertEqual "offset from the base itself needs no guard" (Bap.Symbolic.Memory.empty.readByte base).render (written.readByte base).render
  let below := Bap.Symbolic.Memory.empty.writeByte (lowered 8) (byteAt 7)
  assertEqual "lowered offsets need no guard" (Bap.Symbolic.Memory.empty.readByte (lowered 16)).render (below.readByte (lowered 16)).render
  assertEqual "same offset by another route is the same byte" true
    (← FFI.Z3.isUnsat [different ((Bap.Symbolic.Memory.empty.writeByte (offset (2 ^ 64 - 8)) (byteAt 7)).readByte (lowered 8)) (byteAt 7)])
  assertEqual "other bases still alias" true
    (← FFI.Z3.isUnsat [equal base (.var "other" 64),
      different (written.readByte (.app "bvadd" 64 [.var "other" 64, .const (BitVec.ofNat 64 1)])) (byteAt 7)])
  let sp : Bap.Var := ⟨"sp", .imm 64, 0, false⟩
  let mem : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
  let result : Bap.Var := ⟨"r", .imm 64, 0, false⟩
  let slot (index : Nat) : Bil.Exp := .bin .add (.var sp) (int (8 * index))
  let program (count : Nat) : Bil.Program :=
    (List.range count).map (fun index => .move mem (.store (.var mem) (slot index) (int index) .little 8)) ++
      [.move result (.load (.var mem) (slot 0) .little 8)]
  match Bap.Symbolic.run (program 64) with
  | .ok [⟨state, .normal⟩] =>
    match Assoc.get result state.env with
    | some loaded =>
      assertTrue s!"read through 64 stack slots stays small: {nodeCount loaded}" (nodeCount loaded < 500)
      assertEqual "read through 64 stack slots" true (← FFI.Z3.isUnsat [different loaded (.const (BitVec.ofNat 64 0))])
    | none => throw <| IO.userError "missing load"
  | _ => throw <| IO.userError "unexpected stack results"

private def fuelStability : IO Unit := do
  let branching : Bil.Program := [.ifElse (.var bit) [.move y (int 1)] [.ifElse (.var bit) [] [.jmp (int 2)]], .special "end"]
  match Bap.Symbolic.run branching {} 8, Bap.Symbolic.run branching {} 100 with
  | .ok small, .ok large =>
    assertTrue "no path is exhausted" (small.all fun result => !(result.outcome matches .exhausted))
    assertEqual "more fuel changes nothing" (repr small).pretty (repr large).pretty
  | _, _ => throw <| IO.userError "fuel stability run failed"

def run : IO Unit := do
  reader
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
  inputs
  zeroWidth
  wellSorted
  inputNames
  unknowns
  memoryChoice
  sameBase
  fuelStability
  naming
  checkOperators
  checkSorts

end Bap.Tests.Symbolic
