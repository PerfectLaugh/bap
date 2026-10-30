import BapTests.Support

namespace Bap.Tests.Bil

open Bap
open Bap.Bil

private def reg (name : String) (width : Nat := 32) : Var := ⟨name, .imm width, 0, false⟩
private def int (width value : Nat) : Exp := .int (BitVec.ofNat width value)
private def plus (left right : Exp) : Exp := .bin .add left right
private def sub (left right : Exp) : Exp := .bin .sub left right

private def collatz : Program :=
  let a := reg "a"
  let r := reg "r"
  [
    .move a (int 32 17),
    .move r (int 32 0),
    .while (.bin .neq (int 32 1) (.var a)) [
      .ifElse (.bin .eq (int 32 0) (.bin .rem (.var a) (int 32 2)))
        [.move a (.bin .div (.var a) (int 32 2))]
        [.move a (plus (.bin .mul (.var a) (int 32 3)) (int 32 1))],
      .move r (plus (.var r) (int 32 1))
    ]
  ]

def run : IO Unit := do
  let a := reg "a" 8
  let nested := Exp.letIn a (int 8 2) (.letIn a (plus (.var a) (int 8 3)) (.bin .mul (.var a) (int 8 2)))
  assertBits "nested lexical let" (BitVec.ofNat 8 10) (evalExp [] nested)
  let rebound := bind (bind [] a (.bits (BitVec.ofNat 8 2))) a (.bits (BitVec.ofNat 8 3))
  assertEqual "BIL bind replaces older bindings" 1 rebound.length
  assertBits "BIL bind returns newest value" (BitVec.ofNat 8 3) (lookup rebound a)
  let b := reg "b" 8
  let updates := [
    (a, Value.bits (BitVec.ofNat 8 4)),
    (b, Value.bits (BitVec.ofNat 8 5)),
    (a, Value.bits (BitVec.ofNat 8 6))
  ]
  let sequential := updates.foldl (init := rebound) fun env update => bind env update.1 update.2
  let batch := bindMany rebound updates
  assertEqual "BIL bindMany matches sequential order" (sequential.map fun binding => binding.1.name)
    (batch.map fun binding => binding.1.name)
  assertEqual "BIL bindMany matches sequential length" sequential.length batch.length
  assertBits "BIL bindMany returns newest value" (BitVec.ofNat 8 6) (lookup batch a)
  assertBits "BIL bindMany binds additional value" (BitVec.ofNat 8 5) (lookup batch b)
  let mem : Var := ⟨"mem", .mem 32 8, 0, false⟩
  let stored := Exp.store (.var mem) (int 32 0) (int 32 0xdeadbeef) .little 4
  let loaded := Exp.load stored (int 32 0) .big 4
  let initialMemory : Env := [(mem, .memory (Memory.empty 32))]
  assertBits "BIL store/load endianness" (BitVec.ofNat 32 0xefbeadde) (evalExp initialMemory loaded)
  let program : Program := [
    .move (reg "a") (int 32 3),
    .move (reg "b") (int 32 2),
    .move (reg "result") (plus (.var (reg "a")) (.var (reg "b")))
  ]
  let (final, effect) ← match Bap.Bil.run program {} 100 with
    | .ok result => pure result
    | .error error => throw <| IO.userError error
  match effect with
  | Effect.normal => pure ()
  | other => throw <| IO.userError s!"unexpected effect {repr other}"
  assertBits "three-statement program" (BitVec.ofNat 32 5) (lookup final.env (reg "result"))
  let (collatzFinal, _) ← match Bap.Bil.run collatz {} 10000 with
    | .ok result => pure result
    | .error error => throw <| IO.userError error
  assertBits "Collatz loop" (BitVec.ofNat 32 12) (lookup collatzFinal.env (reg "r"))
  let sample : Program := [
    .move (reg "x") (.cast .signed 16 (int 8 0x80)),
    .ifElse (int 1 1) [.special "yes"] [.special "no"],
    .cpuExn 7
  ]
  let rendered := Wire.renderProgram sample
  let reparsed ← match Wire.parseProgram rendered with
    | .ok program => pure program
    | .error error => throw <| IO.userError error
  assertEqual "BIL wire round trip" rendered (Wire.renderProgram reparsed)
  let sub : IR.Sub := {
    tid := 1
    name := "main"
    args := [{ tid := 2, var := reg "arg", rhs := .var (reg "arg") }]
    blks := [{
      tid := 3
      phis := [{ tid := 4, var := reg "x", values := [(0, int 32 0)] }]
      defs := [{ tid := 5, var := reg "x", rhs := int 32 1 }]
      jmps := [{
        tid := 6
        condition := some (int 1 1)
        kind := .call (.direct 9) (some (.indirect (int 32 0)))
      }]
    }]
  }
  let subRendered := IR.Wire.renderSub sub
  let subReparsed ← match IR.Wire.parseSubString subRendered with
    | .ok value => pure value
    | .error error => throw <| IO.userError error
  assertEqual "BIR wire round trip" subRendered (IR.Wire.renderSub subReparsed)
  let x := reg "x"
  let y := reg "y"
  let result := reg "result"
  let decompiled := Decompile.function "add" [x, y] [
    .move result (plus (.var x) (.var y)),
    .move mem (.store (.var mem) (int 32 0) (int 32 42) .little 4),
    .ifElse (.bin .eq (.var result) (int 32 1))
      [.move result (.bin .smod (.var result) (int 32 3))]
      [.jmp (int 32 0x400)]
  ]
  assertTrue "decompiler renders function signature"
    ((decompiled.splitOn "void add(uint32_t x, uint32_t y) {").length > 1)
  assertTrue "decompiler renders arithmetic" ((decompiled.splitOn "result = (x + y);").length > 1)
  assertTrue "decompiler renders endian stores" ((decompiled.splitOn "write32_le(mem, 0x0, 0x2a);").length > 1)
  assertTrue "decompiler renders signed modulus" ((decompiled.splitOn "result = smod(result, 0x3);").length > 1)
  assertTrue "decompiler renders direct jumps" ((decompiled.splitOn "goto loc_400;").length > 1)
  let decompiledLoop := Decompile.program collatz
  assertTrue "decompiler renders loops" ((decompiledLoop.splitOn "while ((0x1 != a))").length > 1)
  assertTrue "decompiler renders conditionals" ((decompiledLoop.splitOn "if ((0x0 == (a % 0x2)))").length > 1)
  let signedLess := Decompile.exp (.bin .slt (.var x) (.var y))
  assertEqual "decompiler renders signed comparison" "slt(x, y)" signedLess
  assertEqual "decompiler renders unsigned comparison" "(x < y)" (Decompile.exp (.bin .lt (.var x) (.var y)))
  assertEqual "decompiler escapes punctuation" "a_0x2e_b" (Decompile.exp (.var (reg "a.b")))
  assertEqual "decompiler keeps underscores" "a_b" (Decompile.exp (.var (reg "a_b")))
  assertEqual "decompiler escapes a leading digit" "_0x31_x" (Decompile.exp (.var (reg "1x")))
  assertEqual "decompiler separates variable versions" "x_0v1" (Decompile.exp (.var ⟨"x", .imm 32, 1, false⟩))
  assertEqual "decompiler keeps a variable that looks like a version" "x_1" (Decompile.exp (.var (reg "x_1")))
  assertEqual "decompiler renders computed jumps" "goto *x;" (Decompile.stmt 0 (.jmp (.var x)))
  assertEqual "decompiler names a store to another memory" "other = write8_le(mem, 0x0, 0x2a);"
    (Decompile.stmt 0 (.move ⟨"other", .mem 32 8, 0, false⟩ (.store (.var mem) (int 32 0) (int 32 42) .little 1)))
  assertEqual "decompiler renders unknown types" "unknown(oops, uint32_t)" (Decompile.exp (.unknown "oops" (.imm 32)))
  assertTrue "decompiler renders unusual widths"
    (((Decompile.function "f" [⟨"b", .imm 1, 0, false⟩] []).splitOn "unsigned _BitInt(1) b").length > 1)
  let z := reg "z"
  let tainted := Analysis.Taint.sourceVar {} x [1]
  let z := reg "z"
  let tainted := Analysis.Taint.sourceVar {} x [1]
  let tainted := Analysis.Taint.sourceMemory tainted 0x3000 [2]
  let tainted := Analysis.Taint.run tainted [
    .move y (plus (.var x) (int 32 2)),
    .move z (.load (.var mem) (int 32 0x3000) .little 4),
    .move mem (.store (.var mem) (int 32 0x4000) (.var z) .little 4),
    .move result (.ite (.var x) (int 32 1) (int 32 2)),
    .move y (int 32 0)
  ]
  assertEqual "taint propagates through memory" [2] (Analysis.Taint.labelsOfMemory tainted 0x4000)
  assertEqual "taint propagates through loads" [2] (Analysis.Taint.labelsOfVar tainted z)
  assertEqual "taint ite ignores condition" [] (Analysis.Taint.labelsOfVar tainted result)
  assertEqual "taint constant assignment sanitizes" [] (Analysis.Taint.labelsOfVar tainted y)
  let retainted := Analysis.Taint.sourceVar tainted y [3]
  assertEqual "taint source is reported" [3] (Analysis.Taint.labelsOfVar retainted y)
  assertEqual "taint clear removes labels" [] (Analysis.Taint.labelsOfVar (Analysis.Taint.clearVar retainted y) y)
  let propagated := Analysis.Propagate.propagate [
    .move x (int 32 40),
    .move y (plus (.var x) (int 32 2)),
    .move z (plus (.var y) (int 32 1)),
    .move x (.var (reg "unknown")),
    .move result (plus (.var x) (int 32 1))
  ]
  match propagated with
  | [_, .move _ (.int yv), .move _ (.int zv), _, .move _ remaining] =>
    assertEqual "constant propagation folds first assignment" 42 yv.toNat
    assertEqual "constant propagation folds second assignment" 43 zv.toNat
    match remaining with
    | .int value => throw <| IO.userError s!"constant propagation retained invalidated assignment {value.toNat}"
    | _ => IO.println "ok: constant propagation invalidates unknown input"
  | _ => throw <| IO.userError "constant propagation changed program shape"
  let propagatedBranch := Analysis.Propagate.propagate [
    .move x (int 32 1),
    .ifElse (.int (BitVec.ofNat 1 1)) [.move x (int 32 2)] [],
    .move y (.var x)
  ]
  match propagatedBranch.getLast? with
  | some (.move _ (.var _)) => IO.println "ok: constant propagation forgets a value a branch changes"
  | _ => throw <| IO.userError "constant propagation kept a stale value after a branch"
  let bothBranches := Analysis.Propagate.propagate [
    .ifElse (.var z) [.move x (int 32 2)] [.move x (int 32 2)],
    .move y (.var x)
  ]
  match bothBranches.getLast? with
  | some (.move _ (.int value)) => assertEqual "constant propagation joins equal branches" 2 value.toNat
  | _ => throw <| IO.userError "constant propagation lost a value both branches agree on"
  let stoppingLoop : Program := [
    .move x (int 32 0),
    .while (.bin .eq (.var x) (int 32 0)) [.move x (int 32 1)]
  ]
  let runProgram (program : Program) : IO (Bil.State × Bil.Effect) :=
    match _root_.Bap.Bil.run program with
    | .ok result => pure result
    | .error error => throw <| IO.userError error
  let (loopState, _) ← runProgram (Analysis.Propagate.propagate stoppingLoop)
  match Bil.lookup loopState.env x with
  | .ok (.bits value) => assertEqual "constant propagation keeps loop condition live" 1 value.toNat
  | _ => throw <| IO.userError "propagated loop lost its variable"
  let jumpProgram : Program := [.move x (int 32 1), .jmp (int 32 0), .move x (int 32 2)]
  let (jumpOptimized, _) ← runProgram (Analysis.DeadCode.optimize [x] jumpProgram)
  match Bil.lookup jumpOptimized.env x with
  | .ok (.bits value) => assertEqual "dead code keeps writes before a jump" 1 value.toNat
  | _ => throw <| IO.userError "dead code removed a write before a jump"
  let k := reg "k"
  let flag : Bil.Exp := .int (BitVec.ofNat 1 1)
  let loopProgram : Program := [
    .move z (int 32 7),
    .move x (int 32 0),
    .move k flag,
    .while (.var k) [.move y (.var x), .move x (.var z), .move k (.int (BitVec.ofNat 1 0))]
  ]
  let loopOptimized := Analysis.DeadCode.optimize [y] loopProgram
  discard <| runProgram loopOptimized
  assertTrue "dead code keeps what later loop iterations read"
    (loopOptimized.any fun statement => match statement with | .move dst _ => dst = z | _ => false)
  let tainted2 := Analysis.Taint.sourceVar {} z [7]
  let loopTaint := Analysis.Taint.run tainted2 [
    .while (.var k) [.move x (.var y), .move y (.var z)]
  ]
  assertEqual "taint reaches the loop fixpoint" [7] (Analysis.Taint.labelsOfVar loopTaint x)
  let branchTaint := Analysis.Taint.run (Analysis.Taint.sourceVar {} x [1])
    [.ifElse (.var k) [.move x (int 32 0)] []]
  assertEqual "taint joins branches" [1] (Analysis.Taint.labelsOfVar branchTaint x)
  let wideLoad := Analysis.Taint.run (Analysis.Taint.sourceMemory {} 0x3001 [2])
    [.move z (.load (.var mem) (int 32 0x3000) .little 4)]
  assertEqual "taint load covers its width" [2] (Analysis.Taint.labelsOfVar wideLoad z)
  let wideStore := Analysis.Taint.run (Analysis.Taint.sourceVar {} x [1])
    [.move mem (.store (.var mem) (int 32 0x4000) (.var x) .little 4)]
  assertEqual "taint store covers its width" [1] (Analysis.Taint.labelsOfMemory wideStore 0x4003)
  let dynamicStore := Analysis.Taint.run (Analysis.Taint.sourceVar {} x [1])
    [.move mem (.store (.var mem) (.var y) (.var x) .little 4)]
  assertEqual "taint of a dynamic store reaches every address" [1]
    (Analysis.Taint.labelsOfMemory dynamicStore 0x5000)
  let aliased : Memory 8 := ⟨(({} : Std.TreeMap Nat ByteArray).insert 0
    (ByteArray.mk (List.replicate 256 1).toArray)).insert 1 (ByteArray.mk (List.replicate 256 2).toArray)⟩
  let selfCompare := Analysis.Validate.compare [] [] [] { env := [(mem, .memory aliased)] }
  match selfCompare with
  | .ok result => assertTrue "validation is reflexive on aliased memory" (Analysis.Validate.ok result)
  | .error error => throw <| IO.userError error
  let deadProgram : Program := [
    .move x (int 32 40),
    .move y (plus (.var x) (int 32 2)),
    .move z (plus (.var y) (int 32 1)),
    .move (reg "unused") (plus (.var x) (int 32 9)),
    .move result (plus (.var z) (int 32 3))
  ]
  let optimized := Analysis.DeadCode.optimize [result] deadProgram
  assertEqual "dead code removes unused assignment" 4 optimized.length
  assertTrue "dead code preserves output dependencies"
    (optimized.any fun statement => match statement with | .move dst _ => dst = result | _ => false)
  assertTrue "dead code removes unused destination"
    !(optimized.any fun statement => match statement with | .move dst _ => dst = reg "unused" | _ => false)
  let folded := Analysis.DeadCode.optimizePropagated [result] deadProgram
  match folded.getLast? with
  | some (.move _ (.int value)) => assertEqual "dead code folds preserved result" 46 value.toNat
  | _ => throw <| IO.userError "dead code lost preserved result"
  let store := Analysis.DeadCode.optimize [] [.move mem (.store (.var mem) (int 32 0) (.var result) .little 4)]
  assertEqual "dead code preserves memory stores" 1 store.length
  let validation ← match Analysis.Validate.compare [result] deadProgram optimized with
    | .ok result => pure result
    | .error error => throw <| IO.userError error
  assertTrue "execution validation accepts equivalent optimization" (Analysis.Validate.ok validation)
  assertTrue "execution validation compares registers" validation.registers
  assertTrue "execution validation compares memory" validation.memory
  assertTrue "execution validation compares continuation" validation.continuation
  let divergent ← match Analysis.Validate.compare [result] deadProgram (deadProgram ++ [.move result (int 32 0)]) with
    | .ok result => pure result
    | .error error => throw <| IO.userError error
  assertTrue "execution validation rejects changed result" !(Analysis.Validate.ok divergent)
  assertTrue "execution validation reports register mismatch" !divergent.registers

  let captured := reg "x" 8
  let binder := reg "y" 8
  let avoided := substitute [(captured, .var binder)] (.letIn binder (int 8 1) (.var captured))
  assertBits "substitution avoids capture" (BitVec.ofNat 8 7)
    (evalExp [(binder, .bits (BitVec.ofNat 8 7))] avoided)
  let kept := substitute [(captured, .var binder)] (.letIn (reg "z" 8) (int 8 1) (.var captured))
  assertEqual "substitution keeps a non-capturing binder"
    (toString (Wire.printExp (.letIn (reg "z" 8) (int 8 1) (.var binder)))) (toString (Wire.printExp kept))
  assertTrue "simplification keeps width errors"
    ((evalExp [] (simplifyExp (plus (int 8 0) (int 16 1)))).toOption.isNone)
  assertTrue "simplification keeps unknown errors"
    ((evalExp [] (simplifyExp (.bin .mul (int 8 0) (.unknown "x" (.imm 8))))).toOption.isNone)
  assertTrue "simplification keeps condition-width errors"
    ((evalExp [] (simplifyExp (.ite (int 8 0) (int 8 1) (int 8 2)))).toOption.isNone)
  let memoryVar : Var := ⟨"mem", .mem 64 8, 0, false⟩
  let rejected (exp : Exp) : Bool := (inferExp exp).toOption.isNone
  assertTrue "unary operator on memory is rejected" (rejected (.un .neg (.var memoryVar)))
  assertTrue "load address width mismatch is rejected" (rejected (.load (.var memoryVar) (int 32 0) .little 1))
  assertTrue "store address width mismatch is rejected"
    (rejected (.store (.var memoryVar) (int 32 0) (int 8 0) .little 1))
  assertTrue "widening high cast is rejected" (rejected (.cast .high 16 (int 8 0)))
  assertTrue "widening low cast is rejected" (rejected (.cast .low 16 (int 8 0)))
  assertTrue "widening unsigned cast is accepted" (!rejected (.cast .unsigned 16 (int 8 0)))
  assertTrue "well-typed load is accepted" (!rejected (.load (.var memoryVar) (int 64 0) .little 1))
  assertTrue "oversized literal is rejected"
    (match Wire.parseExp (.list [.atom "int", .atom "8", .atom "100"]) with
      | .error _ => true
      | .ok _ => false)
  assertTrue "largest literal is accepted"
    (match Wire.parseExp (.list [.atom "int", .atom "8", .atom "ff"]) with
      | .ok _ => true
      | .error _ => false)
  let failing : Exp := .load (int 8 0) (.unknown "a" .unit) .little 1
  let observedResult ← evalExpObserved none [] failing
  assertTrue "observed evaluation reports the same first error"
    (match observedResult, evalExp [] failing with
      | .error first, .error second => first == second
      | _, _ => false)
end Bap.Tests.Bil
