import BapTests.Support

namespace Bap.Tests.Primus

open Bap
open Bap.Primus

private def bytes : ByteArray := ByteArray.mk #[1, 2, 3, 4]
private def rw : Protection := ⟨true, true, true⟩
private def ro : Protection := ⟨true, false, false⟩
private def memVar : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
private def reg (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩
private def int (value : Nat) : Bil.Exp := .int (BitVec.ofNat 64 value)

private def mapped : IO Primus.Memory :=
  match Primus.Memory.map Primus.Memory.empty 0x1000 bytes rw with
  | .ok memory => pure memory
  | .error error => throw <| IO.userError s!"map failed: {repr error}"

private def modify (machine : Machine) (f : Instance → Instance) : IO Machine :=
  match machine.modifyCurrent f with
  | .ok machine => pure machine
  | .error error => throw <| IO.userError error

private def expectError (name : String) : Except String α → IO Unit
  | .error _ => IO.println s!"ok: {name}"
  | .ok _ => throw <| IO.userError s!"{name}: unexpectedly succeeded"

private def current (machine : Machine) : IO Instance :=
  match machine.currentInstance with
  | some inst => pure inst
  | none => throw <| IO.userError "current machine does not exist"

private def semanticsForms (bits : Nat) (input : String) : IO Primus.Semantics.State := do
  let context : Primus.Semantics.Context := { bits }
  let forms ← match Sexp.parseMany input with
    | .ok forms => pure forms
    | .error error => throw <| IO.userError error
  match Primus.Semantics.evalForms context [("R", Primus.Semantics.register "R" bits bits)] forms with
  | .ok state => pure state
  | .error error => throw <| IO.userError error

private def assignedConstant (state : Primus.Semantics.State) : IO Nat :=
  match state.code with
  | [.move _ (.int value)] => pure value.toNat
  | _ => throw <| IO.userError s!"expected one constant move, got {repr state.code}"

private def semanticsRegressions : IO Unit := do
  assertEqual "word-width of a literal is the machine word" 32
    (← assignedConstant (← semanticsForms 32 "(set R (word-width 5))"))
  assertEqual "word-width of a literal agrees with arithmetic" 64
    (← assignedConstant (← semanticsForms 64 "(set R (word-width 5))"))
  match (← semanticsForms 32 "(set R (mod 0xfffffff9 3))").code with
  | [.move _ (.bin .rem _ _)] => IO.println "ok: mod is the unsigned remainder"
  | code => throw <| IO.userError s!"mod changed: {repr code}"
  match (← semanticsForms 32 "(set R (signed-mod 0xfffffff9 3))").code with
  | [.move _ (.bin .smod _ _)] => IO.println "ok: signed-mod takes the sign of the divisor"
  | code => throw <| IO.userError s!"signed-mod changed: {repr code}"
  match (← semanticsForms 32 "(set R (signed-rem 0xfffffff9 3))").code with
  | [.move _ (.bin .srem _ _)] => IO.println "ok: signed-rem takes the sign of the dividend"
  | code => throw <| IO.userError s!"signed-rem changed: {repr code}"
  assertEqual "local binding shadows replicate" 7
    (← assignedConstant (← semanticsForms 64 "(let ((replicate 7)) (set R replicate))"))
  match (← semanticsForms 64 "(let ((replicate 7)) (set R (replicate 1:32 2)))").code with
  | [.move _ (.concat _ _)] => IO.println "ok: replicate stays callable under a local binding"
  | code => throw <| IO.userError s!"replicate call changed: {repr code}"
  let compiled ← semanticsForms 64 "(defun op () (let ((replicate 7)) (set R replicate)))"
  match (← Primus.Semantics.lift compiled.globals {} "op" []) with
  | [.move _ (.int value)] => assertEqual "compiled local shadows replicate" 7 value.toNat
  | code => throw <| IO.userError s!"compiled replicate shadow changed: {repr code}"
  assertEqual "word-width with no arguments is the machine word" 32
    (← assignedConstant (← semanticsForms 32 "(set R (word-width))"))
  assertEqual "word-width is the widest argument" 16
    (← assignedConstant (← semanticsForms 32 "(set R (word-width 1:8 1:16 1:4))"))
  assertEqual "word-width counts a literal as a machine word" 32
    (← assignedConstant (← semanticsForms 32 "(set R (word-width 1:8 5))"))
  match (← semanticsForms 64 "(let ((x 1)) (set x 2) (set R x))").code with
  | [.move slot (.int first), .move assigned (.int second), .move _ (.var read)] =>
    assertEqual "set assigns the let variable" (1, 2) (first.toNat, second.toNat)
    assertTrue "the assignment and the read use the let variable" (slot == assigned && assigned == read)
  | code => throw <| IO.userError s!"let assignment changed: {repr code}"
  match (← semanticsForms 64 "(let ((x 1)) (if (is-zero R) (set x 2) (set x 3)) (set R x))").code with
  | [.move slot _, .ifElse _ (.move yes _ :: _) (.move no _ :: _), .move _ (.var read)] =>
    assertTrue "both branches assign the let variable" (slot == yes && yes == no && no == read)
  | code => throw <| IO.userError s!"conditional let assignment changed: {repr code}"
  match (← semanticsForms 64 "(defmacro put (v e) (set v e)) (let ((x 1)) (put x 2) (set R x))").code with
  | [.move slot _, .move assigned _, .move _ (.var read)] =>
    assertTrue "a macro assigns the let variable" (slot == assigned && assigned == read)
  | code => throw <| IO.userError s!"macro let assignment changed: {repr code}"
  let assigning ← semanticsForms 64 "(defun op () (let ((x 1)) (set x 2) (set R x)))"
  match (← Primus.Semantics.lift assigning.globals {} "op" []) with
  | [_, _, .move _ (.var _)] => IO.println "ok: a function assigning a let variable lifts"
  | code => throw <| IO.userError s!"let assignment in a function changed: {repr code}"
  match (← semanticsForms 64 "(let ((x 1)) (set R x))").code with
  | [.move _ (.int value)] => assertEqual "an unassigned let variable stays a constant" 1 value.toNat
  | code => throw <| IO.userError s!"constant let changed: {repr code}"
  for (source, value) in [("0o17", 15), ("0b101", 5), ("1_000", 1000), ("0x1_0", 16), ("0", 0)] do
    assertEqual s!"literal {source} parses" value (← assignedConstant (← semanticsForms 64 s!"(set R {source})"))
  assertEqual "negative hexadecimal literal parses" (2 ^ 64 - 16)
    (← assignedConstant (← semanticsForms 64 "(set R -0x10)"))
  for source in ["(set R 0xzz)", "(set R 12abc)", "(set R 1:2:3)", "(set R 5:abc)", "(set R 0x_1)",
      "(defun unused () 0xzz)", "(defmacro unused (x) (+ x 9z))", "(set R -1q)"] do
    match (← (semanticsForms 64 source).toBaseIO) with
    | .error _ => IO.println s!"ok: {source} is rejected"
    | .ok _ => throw <| IO.userError s!"{source} accepted"
  let documented ← semanticsForms 64 "(defun op () \"64-bit add\" (set R 1))"
  assertTrue "documentation strings are not literals" (Assoc.get "op" documented.globals).isSome
  assertEqual "an atom not starting like a number is a symbol" 0
    (← semanticsForms 64 "(defun x1y () 1)").code.length
  assertEqual "hexadecimal literal parses" 16 (← assignedConstant (← semanticsForms 64 "(set R 0x10)"))
  assertEqual "bare 0x is zero, as in Zarith" 0 (← assignedConstant (← semanticsForms 64 "(set R 0x)"))

private def semanticsTargets : List (String × Primus.Semantics.Context × String × List String × IO Primus.Semantics.Environment) :=
  let word32 : Primus.Semantics.Context := { bits := 32, memory := ⟨"mem", .mem 32 8, 0, false⟩ }
  [("aarch64", {}, "arm", ["aarch64"], Target.LLVMLift.aarch64Environment),
   ("x86_64", {}, "x86", ["bits", "x86-64", "x86-bits", "x86-move", "x86-arith", "x86-control"], Target.LLVMLift.x86Environment),
   ("x86", word32, "x86", ["bits", "x86-32", "x86-bits", "x86-move", "x86-arith", "x86-control"], Target.LLVMLift.x8632Environment),
   ("riscv64", {}, "riscv", ["riscv"], Target.LLVMLift.riscvEnvironment),
   ("riscv32", word32, "riscv", ["riscv"], Target.LLVMLift.riscv32Environment),
   ("powerpc64", {}, "powerpc", ["bits", "powerpc"], Target.LLVMLift.powerpcEnvironment),
   ("powerpc32", { word32 with endian := .big }, "powerpc", ["bits", "powerpc"], Target.LLVMLift.powerpc32Environment),
   ("mips64", { endian := .big }, "mips", ["mips"], Target.LLVMLift.mipsEnvironment),
   ("mips32", { word32 with endian := .big }, "mips", ["mips"], Target.LLVMLift.mips32Environment),
   ("arm", word32, "arm", ["arm"], Target.LLVMLift.arm32Environment),
   ("thumb", word32, "arm", ["thumb2"], Target.LLVMLift.thumbEnvironment),
   ("x86_64+", {}, "x86", ["bits", "x86-64", "x86-bits", "x86-move", "x86-arith", "x86-control", "x86-bmi", "x86-shift", "x86-sse", "x86-simd", "x86-sse-intrinsics", "x86-pcmpstr"], Target.LLVMLift.x86Environment),
   ("x86+", word32, "x86", ["bits", "x86-32", "x86-bits", "x86-move", "x86-arith", "x86-control", "x86-bmi", "x86-shift", "x86-sse", "x86-simd", "x86-sse-intrinsics", "x86-pcmpstr"], Target.LLVMLift.x8632Environment),
   ("thumb+", word32, "arm", ["thumb2", "thumb", "thumb-vfp"], Target.LLVMLift.thumbEnvironment),
   ("arm+", word32, "arm", ["arm", "arm-float"], Target.LLVMLift.arm32Environment)]

/-- The registers the semantics names that the target tables of `Bap/Target/LLVMLift.lean` do not have. -/
private def missingRegisters (name : String) : Bool :=
  ([] : List String).contains name

/-- Every name and arity the semantics of a target use, statically, as the evaluator resolves them. -/
private def auditSemantics : IO Unit := do
  for (name, context, directory, entries, environment) in semanticsTargets do
    let definitions ← Primus.Semantics.loadMany [s!"semantics/{directory}", "semantics/core"] entries context
    let environment ← environment
    let names := environment.globals.filter fun binding => (Assoc.get binding.1 definitions).isNone
    let findings := Primus.Semantics.auditGlobals context (definitions ++ names)
    let real := findings.filter fun finding =>
      match finding.2.dropPrefix? "unknown symbol " with
      | some register => !missingRegisters register.toString
      | none => true
    assertEqual s!"semantics of {name} resolve" [] real

private def semanticsValue (state : Primus.Semantics.State) : IO Nat :=
  match state.code with
  | [.move _ value] =>
    match Bil.evalExp [] value with
    | .ok (.bits value) => pure value.toNat
    | _ => throw <| IO.userError s!"not a constant: {repr value}"
  | code => throw <| IO.userError s!"expected one move, got {repr code}"

private def expectRejected (bits : Nat) (source : String) : IO Unit := do
  match (← (semanticsForms bits source).toBaseIO) with
  | .error _ => IO.println s!"ok: {source} is rejected"
  | .ok _ => throw <| IO.userError s!"{source} accepted"

private def runProgram (program : Bil.Program) (state : Bil.State) : IO Bil.State :=
  match Bil.run program state with
  | .ok (state, _) => pure state
  | .error error => throw <| IO.userError error

private def overloadRegressions : IO Unit := do
  let functions := "(defun f (x) (set R x)) (defun f (x y) (set R (+ x y))) "
  assertEqual "a function is selected by its arity" 1 (← semanticsValue (← semanticsForms 64 (functions ++ "(f 1)")))
  assertEqual "the other arity is kept" 5 (← semanticsValue (← semanticsForms 64 (functions ++ "(f 2 3)")))
  expectRejected 64 (functions ++ "(f 1 2 3)")
  assertEqual "a later definition of the same arity replaces" 2
    (← semanticsValue (← semanticsForms 64 "(defun f (x) (set R 1)) (defun f (y) (set R 2)) (f 0)"))
  let compiled ← semanticsForms 64 (functions ++ "(defun g () (f 1 2))")
  match (← Primus.Semantics.lift compiled.globals {} "f" [.int 7]) with
  | [.move _ (.int value)] => assertEqual "a compiled overload is selected by its arity" 7 value.toNat
  | code => throw <| IO.userError s!"compiled overload changed: {repr code}"
  match (← Primus.Semantics.lift compiled.globals {} "g" []) with
  | [.move _ _] => IO.println "ok: a compiled call selects the overload"
  | code => throw <| IO.userError s!"compiled call changed: {repr code}"
  let counting := "(defmacro count (r) 1) (defmacro count (r rs) (+ 1 (count rs))) "
  assertEqual "the last macro parameter takes the rest" 3
    (← semanticsValue (← semanticsForms 64 (counting ++ "(set R (count a b c))")))
  assertEqual "the most specific macro is selected" 1
    (← semanticsValue (← semanticsForms 64 (counting ++ "(set R (count a))")))
  expectRejected 64 "(defmacro two (a b) a) (two 1)"
  expectRejected 64 "(defmacro whole (a) a) (whole 1 2)"
  assertEqual "macros hide functions of the same name" 9
    (← semanticsValue (← semanticsForms 64 "(defun m (x) (set R 1)) (defmacro m (x) (set R 9)) (m 0)"))
  expectRejected 64 "(progn (defun nested () 1))"

private def languageRegressions : IO Unit := do
  assertEqual "a character literal is its code" 97
    (← semanticsValue (← semanticsForms 64 "(set R (cast-unsigned 64 ?a))"))
  assertEqual "a character literal has 8 bits" 8
    (← assignedConstant (← semanticsForms 64 "(set R (word-width ?a))"))
  expectRejected 64 "(set R ?ab)"
  expectRejected 64 "(set R ?)"
  assertEqual "a parameter holds its value" 5
    (← semanticsValue (← semanticsForms 64 "(defparameter *p* 5) (set R *p*)"))
  expectRejected 64 "(error \"stop\")"
  assertEqual "msg has no effect" 0
    (← semanticsForms 64 "(msg \"text\" R)").code.length
  assertEqual "a method is not semantics" 0
    (← semanticsForms 64 "(defmethod bap:patterns-action (a) (unknown a))").code.length
  assertEqual "symbols concatenate" 1
    (← assignedConstant (← semanticsForms 64 "(set R (if (= (symbol-concat 'a 'b '32 :sep '_) 'a_b_32) 1 0))"))
  assertEqual "a symbol names the assigned register" 3
    (← assignedConstant (← semanticsForms 64 "(set$ 'R 3)"))
  match (← semanticsForms 64 "(set R (unquote 'R))").code with
  | [.move _ (.var read)] => assertEqual "unquote reads the register" "R" read.name
  | code => throw <| IO.userError s!"unquote changed: {repr code}"
  for (source, value) in [("(cast-saturate :signed 8 0x100:16)", 127), ("(cast-saturate :signed 8 0xff00:16)", 128),
      ("(cast-saturate :signed 8 0x7f:16)", 127), ("(cast-saturate :signed 8 0xfffe:16)", 254),
      ("(cast-saturate :unsigned 8 0x100:16)", 255), ("(cast-saturate :unsigned 8 0xffff:16)", 0),
      ("(cast-saturate :unsigned 8 0x12:16)", 18)] do
    assertEqual s!"{source}" value
      (← semanticsValue (← semanticsForms 64 s!"(set R (cast-unsigned 64 {source}))"))
  let context : Primus.Semantics.Context := {}
  let forms ← match Sexp.parseMany "(set R (x86-prefix 0xf3))" with
    | .ok forms => pure forms
    | .error error => throw <| IO.userError error
  let globals := [("R", Primus.Semantics.register "R" 1 1)]
  expectError "a prefix is an error when the decoder gives none" (Primus.Semantics.evalForms context globals forms)
  match Primus.Semantics.evalForms { context with prefixes := some [0xf3] } globals forms with
  | .ok state => assertEqual "a prefix of the instruction is present" 1 state.code.length
  | .error error => throw <| IO.userError error
  -- the value of an intrinsic survives the next call, which overwrites its output variable
  match (← semanticsForms 64 "(set R (+ (intrinsic 'f 1:64 :result 64) (intrinsic 'g 2:64 :result 64)))").code with
  | [.move x0 _, .special "f", .move first (.var y0), .move _ _, .special "g", .move second (.var _), .move _ _] =>
    assertEqual "an intrinsic gets its arguments in intrinsic:x0" "intrinsic:x0" x0.name
    assertEqual "an intrinsic gives its result in intrinsic:y0" "intrinsic:y0" y0.name
    assertTrue "the results are copies" (first != second)
  | code => throw <| IO.userError s!"intrinsic changed: {repr code}"
  match (← semanticsForms 64 "(defun op () (intrinsic 'trap :aborts)) (op)").code with
  | [.special "trap"] => IO.println "ok: :aborts is not an argument"
  | code => throw <| IO.userError s!"intrinsic changed: {repr code}"
  match (← semanticsForms 32 "(set R (cast-unsigned 32 (+. :rne 1:32 2:32)))").code with
  | [.move _ _, .move _ _, .special "fadd_rne_ieee754_binary_32", .move _ _, .move _ _] =>
    IO.println "ok: a floating-point primitive calls its intrinsic"
  | code => throw <| IO.userError s!"floating-point primitive changed: {repr code}"
  -- the condition is computed again before every test, and a loop ends the block only when it ends
  let loop ← semanticsForms 64 "(let ((i 0)) (while (< i 3) (set i (+ i 1))) (set R i))"
  let final ← runProgram loop.code {}
  match Bil.lookup final.env ⟨"R", .imm 64, 0, false⟩ with
  | .ok (.bits value) => assertEqual "while runs until the condition fails" 3 value.toNat
  | _ => throw <| IO.userError "while has no result"
  assertEqual "a false loop condition has no code" 0 (← semanticsForms 64 "(while false (set R 1))").code.length
  let compiledLoop ← semanticsForms 64 "(defun op () (let ((i 0)) (while (< i 3) (set i (+ i 1))) (set R i)))"
  let final ← runProgram (← Primus.Semantics.lift compiledLoop.globals {} "op" []) {}
  match Bil.lookup final.env ⟨"R", .imm 64, 0, false⟩ with
  | .ok (.bits value) => assertEqual "a function with a loop lifts" 3 value.toNat
  | _ => throw <| IO.userError "while has no result"
  let prelude ← Primus.Semantics.loadMany ["semantics/core"] [] context
  let withPrelude (source : String) : IO Primus.Semantics.State := do
    let forms ← match Sexp.parseMany source with
      | .ok forms => pure forms
      | .error error => throw <| IO.userError error
    match Primus.Semantics.evalForms context (prelude ++ [("R", Primus.Semantics.register "R" 64 64)]) forms with
    | .ok state => pure state
    | .error error => throw <| IO.userError error
  assertEqual "and is the last value" 3 (← semanticsValue (← withPrelude "(set R (if (and 1:1 1:1 0:1) 2 3))"))
  assertEqual "or is the first true value" 2 (← semanticsValue (← withPrelude "(set R (if (or 0:1 1:1 0:1) 2 3))"))
  assertEqual "dolist applies to each argument" 2
    (← withPrelude "(defun z (r) (set$ r 0)) (dolist z 'R 'R)").code.length
  assertEqual "the core loads with an entry" 1
    (← withPrelude "(+= R 4)").code.length
  -- endianness of a definition
  let forms ← match Sexp.parseMany "(defun e () (set R 0)) (defun e () (declare (context (endianness le))) (set R 1)) (e)" with
    | .ok forms => pure forms
    | .error error => throw <| IO.userError error
  let register := [("R", Primus.Semantics.register "R" 64 64)]
  match Primus.Semantics.evalForms { context with endian := .little } register forms,
      Primus.Semantics.evalForms { context with endian := .big } register forms with
  | .ok little, .ok big =>
    assertEqual "an le definition holds on little-endian" 1 (← assignedConstant little)
    assertEqual "an le definition does not on big-endian" 0 (← assignedConstant big)
  | _, _ => throw <| IO.userError "endianness context failed"

/-- The floating point of SSE from `x86-sse-intrinsics.lisp`, loaded as the x86 targets load the other files. -/
private def sseRegressions : IO Unit := do
  let context : Primus.Semantics.Context := {}
  let definitions ← Primus.Semantics.loadMany ["semantics/x86", "semantics/core"]
    ["bits", "x86-64", "x86-bits", "x86-move", "x86-arith", "x86-control", "x86-shift", "x86-bmi", "x86-sse", "x86-simd",
      "x86-pcmpstr", "x86-sse-intrinsics"] context
  let environment := Primus.Semantics.Environment.ofGlobals (Primus.Semantics.compileGlobals definitions)
  let xmm (name : String) := Primus.Semantics.register name 128 256
  let specials (code : Bil.Program) := code.filterMap fun stmt =>
    match stmt with
    | .special name => some name
    | _ => none
  let writes (code : Bil.Program) := code.filterMap fun stmt =>
    match stmt with
    | .move var _ => some var.name
    | _ => none
  let addsd ← Primus.Semantics.liftWith environment context "ADDSDrr_Int" [xmm "YMM0", xmm "YMM0", xmm "YMM1"]
  assertEqual "addsd calls its intrinsic once" ["fadd_rne_ieee754_binary_64"] (specials addsd)
  assertEqual "addsd gets its result" "YMM0" ((writes addsd).getLast?.getD "")
  let mulss ← Primus.Semantics.liftWith environment context "MULSSrr_Int" [xmm "YMM0", xmm "YMM0", xmm "YMM1"]
  assertEqual "mulss has the size in its name" ["fmul_rne_ieee754_binary_32"] (specials mulss)
  let addpd ← Primus.Semantics.liftWith environment context "ADDPDrr" [xmm "YMM0", xmm "YMM0", xmm "YMM1"]
  assertEqual "addpd calls its intrinsic per lane"
    ["fadd_rne_ieee754_binary_64", "fadd_rne_ieee754_binary_64"] (specials addpd)
  let paddsw ← Primus.Semantics.liftWith environment context "PADDSWrr" [xmm "YMM0", xmm "YMM0", xmm "YMM1"]
  assertEqual "integer lanes are not floating point, whatever the load order" [] (specials paddsw)
  assertTrue "integer lanes saturate" (!paddsw.isEmpty)
  assertEqual "the high part of a whole value is empty" 8
    (← assignedConstant (← semanticsForms 64 "(set R (word-width (concat (cast-high 0 1:8) 5:8)))"))
  assertEqual "an empty part changes no value" 5
    (← semanticsValue (← semanticsForms 64 "(set R (cast-unsigned 64 (concat (cast-high 0 1:8) 5:8)))"))

private def armWord (value : Nat) : Primus.Semantics.Value := .bil 32 (.int (BitVec.ofNat 32 value))

/-- `arm-a32-multiple.lisp` lifts through the arity of the register list, with no workaround. -/
private def armMultipleRegressions : IO Unit := do
  let environment ← Target.LLVMLift.arm32Environment
  let context : Primus.Semantics.Context := { bits := 32, memory := ⟨"mem", .mem 32 8, 0, false⟩ }
  let register (name : String) := Primus.Semantics.register name 32 32
  let var (name : String) : Bap.Var := ⟨name, .imm 32, 0, false⟩
  let memory := Bap.Memory.ofCells (addressWidth := 32)
    ((List.range 12).map fun offset => (BitVec.ofNat 32 (0x100 + offset), UInt8.ofNat (offset + 1)))
  let initial : Bil.State := { env := [
    (context.memory, .memory memory), (var "R0", .bits (BitVec.ofNat 32 0x100)),
    (var "R1", .bits (BitVec.ofNat 32 0)), (var "R2", .bits (BitVec.ofNat 32 0)),
    (var "R3", .bits (BitVec.ofNat 32 0)), (var "R4", .bits (BitVec.ofNat 32 0xaabbccdd))] }
  let value (state : Bil.State) (name : String) : IO Nat :=
    match Bil.lookup state.env (var name) with
    | .ok (.bits value) => pure value.toNat
    | _ => throw <| IO.userError s!"{name} is missing"
  let ldm ← Primus.Semantics.liftWith environment context "LDMIA"
    [register "R0", armWord 14, register "Nil", register "R1", register "R2"]
  let loaded ← runProgram ldm initial
  assertEqual "LDMIA of two loads the first word" 0x04030201 (← value loaded "R1")
  assertEqual "LDMIA of two loads the second word" 0x08070605 (← value loaded "R2")
  let three ← Primus.Semantics.liftWith environment context "LDMIA"
    [register "R0", armWord 14, register "Nil", register "R1", register "R2", register "R3"]
  let loaded ← runProgram three initial
  assertEqual "LDMIA of three loads the third word" 0x0c0b0a09 (← value loaded "R3")
  let update ← Primus.Semantics.liftWith environment context "LDMIA_UPD"
    [register "R0", register "R0", armWord 14, register "Nil", register "R1"]
  let loaded ← runProgram update initial
  assertEqual "LDMIA_UPD writes the base back" 0x104 (← value loaded "R0")
  let store ← Primus.Semantics.liftWith environment context "STMDB_UPD"
    [register "R0", register "R0", armWord 14, register "Nil", register "R4"]
  let stored ← runProgram store initial
  assertEqual "STMDB_UPD writes the base back" 0xfc (← value stored "R0")
  match Bil.lookup stored.env context.memory with
  | .ok (@Value.memory width stored) =>
    assertEqual "STMDB stores below the base" 0xdd
      (Bap.Memory.readByte stored (BitVec.ofNat width 0xfc)).toNat
  | _ => throw <| IO.userError "memory is missing"
  let vfp := Primus.Semantics.register "D0" 64 64
  let vldm ← Primus.Semantics.liftWith environment context "VLDMDIA"
    [register "R0", armWord 14, register "Nil", vfp, Primus.Semantics.register "D1" 64 64]
  let loaded ← runProgram vldm { env := initial.env ++ [(⟨"D0", .imm 64, 0, false⟩, .bits (BitVec.ofNat 64 0)),
    (⟨"D1", .imm 64, 0, false⟩, .bits (BitVec.ofNat 64 0))] }
  match Bil.lookup loaded.env ⟨"D1", .imm 64, 0, false⟩ with
  | .ok (.bits value) => assertEqual "VLDM selects the list of its arity" 0 (value.toNat - 0x100f0e0d0c0b0a09)
  | _ => throw <| IO.userError "D1 is missing"

private def protectRegressions : IO Unit := do
  let memory ← mapped
  let protected_ := memory.protect 0x1001 0x1003 ro
  assertEqual "a partial protection splits the region" (some ro) (protected_.protection 0x1001)
  assertEqual "the end of the range stays exclusive" (some ro) (protected_.protection 0x1002)
  assertEqual "the bytes below the range keep their protection" (some rw) (protected_.protection 0x1000)
  assertEqual "the bytes above the range keep their protection" (some rw) (protected_.protection 0x1003)
  assertEqual "protection does not map" none (protected_.protection 0x1004)
  assertEqual "an empty range changes nothing" (some rw) ((memory.protect 0x1002 0x1002 ro).protection 0x1002)
  assertEqual "a range before the region changes nothing" (some rw) ((memory.protect 0 0x1000 ro).protection 0x1000)
  assertEqual "a covering range protects it all" (some ro) ((memory.protect 0 0x2000 ro).protection 0x1003)

/-- A conditional whose branches make code has the value of the branch that runs. -/
private def conditionalValues : IO Unit := do
  let source := "(defun f (x) (set R x) (+ x 1)) (set S (if (= R 1) (f 1) (f 2)))"
  let forms ← match Sexp.parseMany source with
    | .ok forms => pure forms
    | .error error => throw <| IO.userError error
  let globals := [("R", Primus.Semantics.register "R" 64 64), ("S", Primus.Semantics.register "S" 64 64)]
  let program ← match Primus.Semantics.evalForms {} globals forms with
    | .ok state => pure state.code
    | .error error => throw <| IO.userError error
  let finalS (r : Nat) : IO (Option Nat) := do
    let state ← runProgram program { env := [(⟨"R", .imm 64, 0, false⟩, .bits (BitVec.ofNat 64 r))] }
    match Bil.evalExp state.env (.var ⟨"S", .imm 64, 0, false⟩) with
    | .ok (.bits value) => pure (some value.toNat)
    | _ => pure none
  assertEqual "the value of the branch with code that runs" (some 2) (← finalS 1)
  assertEqual "and of the other" (some 3) (← finalS 0)
  let compiled ← match Sexp.parseMany "(defun f (x) (set R x) (+ x 1)) (defun g () (set S (if (= R 1) (f 1) (f 2))))" with
    | .ok forms =>
      match Primus.Semantics.evalForms {} globals forms with
      | .ok state => Primus.Semantics.lift state.globals {} "g" []
      | .error error => throw <| IO.userError error
    | .error error => throw <| IO.userError error
  assertEqual "compiled, it makes the same code" (toString (Bil.Wire.printProgram program)) (toString (Bil.Wire.printProgram compiled))
  -- Nothing reads the value of this one, so what is lifted has no variable for it, nor for what only that reads.
  let unread ← match Sexp.parseMany "(defun h () (if (= R 1) (set S 2) (set S 3))) (defun i () (let ((a (if (= R 1) (set S 2) (set S 3)))) (if (= R 2) (set S 4) (set S a)) 1))" with
    | .ok forms =>
      match Primus.Semantics.evalForms {} globals forms with
      | .ok state => pure state.globals
      | .error error => throw <| IO.userError error
    | .error error => throw <| IO.userError error
  let unreadCode ← Primus.Semantics.lift unread {} "h" []
  assertEqual "the value of a conditional nothing reads has no variable"
    "((if (binop EQ (cast UNSIGNED 64 (var R 0 (imm 64) 0)) (cast UNSIGNED 64 (int 64 1))) ((move (var S 0 (imm 64) 0) (int 64 2))) ((move (var S 0 (imm 64) 0) (int 64 3)))))"
    (toString (Bil.Wire.printProgram unreadCode))
  let readCode ← Primus.Semantics.lift unread {} "i" []
  let runs (code : Bil.Program) (r : Nat) : IO (Option Nat) := do
    let state ← runProgram code { env := [(⟨"R", .imm 64, 0, false⟩, .bits (BitVec.ofNat 64 r))] }
    match Bil.evalExp state.env (.var ⟨"S", .imm 64, 0, false⟩) with
    | .ok (.bits value) => pure (some value.toNat)
    | _ => pure none
  assertEqual "and it does what it did" (some 2) (← runs unreadCode 1)
  assertEqual "and what it did on the other branch" (some 3) (← runs unreadCode 0)
  assertEqual "the value of a conditional something reads is still there" (some 3) (← runs readCode 0)
  assertEqual "the other value of it" (some 4) (← runs readCode 2)
  -- on a real instruction, whose branches assign and yield
  let cmpxchg ← Target.LLVMLift.decodeX86 0 0 (← LLVM.assemble "x86_64" "cmpxchgq %rcx, %rdx")
  assertTrue "no temporary a lifted instruction assigns is unread"
    ((Bil.programTemporaries cmpxchg.bil).all fun var => (Bil.readsOfProgram cmpxchg.bil).contains var)

/-- Instructions of a thunked environment lift as they do written out, which `thunked_opcode_agrees` proves. -/
private def thunkedRegressions : IO Unit := do
  let forms ← match Sexp.parseMany "(defmacro twice (x) (+ x x)) (defun helper (x) (twice x)) (defun insn (r x) (set$ r (helper x)))" with
    | .ok forms => pure forms
    | .error error => throw <| IO.userError error
  let state ← match Primus.Semantics.evalForms {} [("R", Primus.Semantics.register "R" 64 64)] forms with
    | .ok state => pure state
    | .error error => throw <| IO.userError error
  let (lazy, eager) := state.globals.partition fun binding => binding.1 == "insn"
  let lazy := lazy.filterMap fun binding =>
    match binding.2 with
    | .callable callable => some ((binding.1, callable), 7)
    | _ => none
  let environment := Primus.Semantics.Environment.thunked eager lazy
  let operands : List Primus.Semantics.Value := [Primus.Semantics.register "R" 64 64, .bil 64 (.int 21#64)]
  let thunked ← Primus.Semantics.liftMC environment {} 7 operands
  let byName ← Primus.Semantics.liftWith environment {} "insn" operands
  let written ← Primus.Semantics.liftWith { environment with instructions := {} } {} "insn" operands
  assertEqual "a thunk lifts as the instruction written" (repr written).pretty (repr thunked).pretty
  assertEqual "by name as well" (repr written).pretty (repr byName).pretty
  let x86 ← Target.LLVMLift.x86Environment
  let registers ← ["RAX", "RAX", "RBX"].mapM fun name =>
    match Assoc.get name x86.globals with
    | some register => pure register
    | none => throw <| IO.userError s!"no register {name}"
  for opcode in ["ADD64rr", "SUB64rr", "XOR64rr"] do
    let forced ← Primus.Semantics.liftWith x86 {} opcode registers
    let written ← Primus.Semantics.liftWith { x86 with instructions := {} } {} opcode registers
    assertEqual s!"{opcode} lifts as written" (repr written).pretty (repr forced).pretty

def run : IO Unit := do
  conditionalValues
  thunkedRegressions
  -- A binding that is no function shadows a function of the same name further on, in the index as in the definitions.
  let shadowed := Primus.Semantics.Environment.ofGlobals
    [("f", .int 1#64), ("f", .callable (.primitive "+")), ("g", .callable (.primitive "-"))]
  assertTrue "a value shadows a function in the index" (shadowed.operations.get? "f").isNone
  assertTrue "a function stays in the index" (shadowed.operations.get? "g").isSome
  auditSemantics
  overloadRegressions
  languageRegressions
  armMultipleRegressions
  sseRegressions
  protectRegressions
  let memory ← mapped
  match memory.loadByte 0x1001 with
  | .ok value => assertEqual "Primus mapped byte" 2 value
  | .error error => throw <| IO.userError s!"load failed: {repr error}"
  match memory.load 0x1000 .little 4 with
  | .ok value => assertEqual "Primus little-endian word" 0x04030201 value.toNat
  | .error error => throw <| IO.userError s!"word load failed: {repr error}"
  let modified ← match memory.storeByte 0x1001 9 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError s!"store failed: {repr error}"
  match modified.loadByte 0x1001 with
  | .ok value => assertEqual "Primus store/read" 9 value
  | .error error => throw <| IO.userError s!"store read failed: {repr error}"
  match Primus.Memory.restore (Primus.Memory.snapshot memory) modified |>.loadByte 0x1001 with
  | .ok value => assertEqual "Primus snapshot restore" 2 value
  | .error error => throw <| IO.userError s!"restore failed: {repr error}"
  match memory.loadByte 0x2000 with
  | .error (.unmapped 0x2000) => IO.println "ok: unmapped access rejected"
  | .error error => throw <| IO.userError s!"wrong unmapped error: {repr error}"
  | .ok _ => throw <| IO.userError "unmapped access accepted"
  match memory.storeByte 0x2000 0 with
  | .error (.unmapped 0x2000) => IO.println "ok: unmapped store rejected"
  | .error error => throw <| IO.userError s!"wrong store error: {repr error}"
  | .ok _ => throw <| IO.userError "unmapped store accepted"
  let readOnly ← match Primus.Memory.map Primus.Memory.empty 0x3000 bytes ro with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError s!"read-only map failed: {repr error}"
  match readOnly.storeByte 0x3000 0 with
  | .error (.readonly 0x3000) => IO.println "ok: read-only store rejected"
  | .error error => throw <| IO.userError s!"wrong read-only error: {repr error}"
  | .ok _ => throw <| IO.userError "read-only store accepted"
  match readOnly.fetch 0x3000 with
  | .error (.notExecutable 0x3000) => IO.println "ok: non-executable fetch rejected"
  | .error error => throw <| IO.userError s!"wrong fetch error: {repr error}"
  | .ok _ => throw <| IO.userError "non-executable fetch accepted"
  let executeOnly ← match Primus.Memory.map Primus.Memory.empty 0x4000 bytes ⟨false, false, true⟩ with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError s!"map failed: {repr error}"
  match executeOnly.fetch 0x4001 with
  | .ok value => assertEqual "execute-only memory is fetchable" 2 value
  | .error error => throw <| IO.userError s!"execute-only fetch failed: {repr error}"
  match executeOnly.loadByte 0x4001 with
  | .error (.unmapped 0x4001) => IO.println "ok: execute-only memory is not loadable"
  | _ => throw <| IO.userError "execute-only load accepted"
  match Primus.Memory.map Primus.Memory.empty (2 ^ 64 - 4) bytes rw with
  | .ok top =>
    match top.loadByte (2 ^ 64 - 1) with
    | .ok value => assertEqual "last byte of the address space is mapped" 4 value
    | .error error => throw <| IO.userError s!"top load failed: {repr error}"
  | .error error => throw <| IO.userError s!"map at the top failed: {repr error}"
  match Primus.Memory.map Primus.Memory.empty (2 ^ 64 - 3) bytes rw with
  | .error (.outOfRange ..) => IO.println "ok: mapping across the end of the address space rejected"
  | _ => throw <| IO.userError "mapping across the end of the address space accepted"
  let aliased : Primus.Memory := ⟨Primus.Memory.empty.cells, [⟨0, 2 ^ 64 + 1, rw⟩]⟩
  match aliased.storeByte (2 ^ 64) 7 with
  | .error (.unmapped _) => IO.println "ok: store at 2^64 does not alias address 0"
  | _ => throw <| IO.userError "store at 2^64 accepted"
  semanticsRegressions
  match memory.addRegion ⟨0x1000, 0x1004, rw⟩ with
  | .error (.overlap 0x1000 0x1004) => IO.println "ok: overlapping region rejected"
  | .error error => throw <| IO.userError s!"wrong overlap error: {repr error}"
  | .ok _ => throw <| IO.userError "overlapping region accepted"
  let x := reg "x"
  let y := reg "y"
  let initial ← modify ({ : Machine }) fun inst =>
    { inst with state := { env := [(x, .bits (BitVec.ofNat 64 40)), (memVar, .memory Primus.Memory.empty.cells)] } }
  let program : Bil.Program := [
    .move y (.bin .add (.var x) (int 2)),
    .jmp (.var y)
  ]
  let system : System := { observers := [fun _ machine => .ok machine] }
  match Machine.run initial system program with
  | .error error => throw <| IO.userError error
  | .ok (final, effect) =>
    match effect with
    | .jump target => assertEqual "Primus jump target" 42 target.toNat
    | other => throw <| IO.userError s!"unexpected Primus effect {repr other}"
    assertEqual "Primus execution time" 2 final.time
    assertEqual "Primus observer delivery" 2 final.observerHits
    assertTrue "Primus jump event" (final.log.any fun event => match event with | .jump 42 => true | _ => false)
  let committed := Machine.runAtomic initial system program
  match committed.result with
  | .error error => throw <| IO.userError error
  | .ok (.jump target) => assertEqual "Primus transaction commits control flow" 42 target.toNat
  | .ok effect => throw <| IO.userError s!"unexpected transaction effect {repr effect}"
  let committedInst ← current committed.machine
  assertBits "Primus transaction commits registers" (BitVec.ofNat 64 42)
    (Bil.lookup committedInst.state.env y)
  assertEqual "Primus transaction commits time" 2 committed.machine.time
  assertEqual "Primus transaction commits events" 5 committed.machine.log.length

  let broken : Bil.Program := [
    .move y (int 42),
    .move memVar (.store (.var memVar) (int 0) (.int (BitVec.ofNat 8 0x42)) .little 1),
    .move (reg "z") (.var (reg "missing"))
  ]
  let rolled := Machine.runAtomic initial system broken
  expectError "Primus transaction propagates interpreter failure" rolled.result
  let rolledInst ← current rolled.machine
  assertEqual "Primus rollback restores time" initial.time rolled.machine.time
  assertEqual "Primus rollback restores event log" initial.log rolled.machine.log
  assertEqual "Primus rollback restores observer count" initial.observerHits rolled.machine.observerHits
  expectError "Primus rollback restores registers" (Bil.lookup rolledInst.state.env y)
  assertEqual "Primus rollback restores memory" 0
    (Bap.Memory.readByte rolledInst.memory.cells (BitVec.ofNat 64 0))

  let failingSystem : System := { observers := [fun _ _ => .error "observer failed"] }
  let observerRolled := Machine.stepAtomic initial failingSystem (.move y (int 42))
  expectError "Primus transaction propagates observer failure" observerRolled.result
  assertEqual "Primus observer failure restores event log" initial.log observerRolled.machine.log
  let observerInst ← current observerRolled.machine
  expectError "Primus observer failure restores registers" (Bil.lookup observerInst.state.env y)

  let exhausted := Machine.runAtomic initial system program 0
  expectError "Primus transaction reports fuel exhaustion" exhausted.result
  assertEqual "Primus fuel exhaustion restores time" initial.time exhausted.machine.time
  assertEqual "Primus fuel exhaustion restores log" initial.log exhausted.machine.log

  let (machines, id) := Machine.newMachine {}
  let machines ← match machines.switch id with
    | .ok machine => pure machine
    | .error error => throw <| IO.userError error
  let machines ← modify machines fun inst => { inst with state := { env := [(x, .bits (BitVec.ofNat 64 1))] } }
  let machines ← match machines.switch 0 with
    | .ok machine => pure machine
    | .error error => throw <| IO.userError error
  let machines ← modify machines fun inst => { inst with state := { env := [(x, .bits (BitVec.ofNat 64 2))] } }
  let machines ← match machines.switch id with
    | .ok machine => pure machine
    | .error error => throw <| IO.userError error
  match machines.currentInstance with
  | some inst => assertBits "machine instances are independent" (BitVec.ofNat 64 1) (Bil.lookup inst.state.env x)
  | none => throw <| IO.userError "missing machine instance"

end Bap.Tests.Primus
