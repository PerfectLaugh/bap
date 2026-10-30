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

end Bap.Tests.Bil
