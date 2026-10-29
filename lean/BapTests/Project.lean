import BapTests.Support

namespace Bap.Tests.Project

open Bap
open Bap.Project
open Bap.Plugin

private def recordingPass (name : String) (dependencies : List String := []) : Pass := {
  name := name
  dependencies := dependencies
  autorun := true
  run := fun project =>
    let trace := (project.get "trace").getD ""
    .ok (project.set "trace" (trace ++ name))
}

def run : IO Unit := do
  let a := recordingPass "a"
  let b := recordingPass "b" ["a"]
  let c := recordingPass "c" ["b"]
  match runPasses [c, a, b] {} with
  | .error error => throw <| IO.userError s!"passes failed: {repr error}"
  | .ok project =>
    assertEqual "passes respect dependencies" "abc" ((project.get "trace").getD "")
    match runPasses [a] project with
    | .ok again => assertEqual "runonce avoids duplicate execution" "abc" ((again.get "trace").getD "")
    | .error error => throw <| IO.userError s!"runonce failed: {repr error}"
  match runPasses [recordingPass "bad" ["missing"]] {} with
  | .error (.missingDependency "bad" "missing") => IO.println "ok: missing dependency rejected"
  | .error error => throw <| IO.userError s!"wrong dependency error: {repr error}"
  | .ok _ => throw <| IO.userError "missing dependency accepted"
  let left := recordingPass "left" ["right"]
  let right := recordingPass "right" ["left"]
  match runPasses [left, right] {} with
  | .error (.cycle _) => IO.println "ok: dependency cycle rejected"
  | .error error => throw <| IO.userError s!"wrong cycle error: {repr error}"
  | .ok _ => throw <| IO.userError "dependency cycle accepted"
  let failing : Pass := {
    name := "failing"
    run := fun _ => .error "intentional failure"
  }
  match runPasses [failing] {} with
  | .error (.runtime "failing" "intentional failure") => IO.println "ok: pass runtime error propagated"
  | .error error => throw <| IO.userError s!"wrong runtime error: {repr error}"
  | .ok _ => throw <| IO.userError "pass runtime error ignored"
  let project ← Project.load "/bin/echo"
  assertTrue "project is disassembled" project.disassembled
  match analyze defaultRegistry project with
  | .error error => throw <| IO.userError s!"default analysis failed: {repr error}"
  | .ok analyzed =>
    assertEqual "default instruction summary" (some "13") (analyzed.get "instructions")
    assertEqual "default block summary" (some "2") (analyzed.get "blocks")
    assertEqual "default analysis status" (some "analyzed") (analyzed.get "status")
  match analyze defaultRegistry project ["report"] with
  | .error error => throw <| IO.userError s!"selected analysis failed: {repr error}"
  | .ok analyzed => assertEqual "selected pass includes dependencies" (some "13") (analyzed.get "instructions")
  let mem : Var := ⟨"mem", .mem 64 8, 0, false⟩
  let rax : Var := ⟨"RAX", .imm 64, 0, false⟩
  let target : Bil.Exp := .int (BitVec.ofNat 64 0x2000)
  let address : Bil.Exp := .int (BitVec.ofNat 64 0x3000)
  let instructions : List Disasm.Insn := [
    ⟨0x1000, 4, "call", .call, some 0x2000, [.jmp target]⟩,
    ⟨0x1004, 4, "load", .normal, none, [.move rax (.load (.var mem) address .little 8)]⟩,
    ⟨0x1008, 4, "store", .normal, none, [.move mem (.store (.var mem) address (.var rax) .little 8)]⟩,
    ⟨0x100c, 4, "jump", .jump, some 0x2000, [.jmp target]⟩
  ]
  let image : Image.Image := {
    arch := .x86_64
    addrWidth := 64
    endian := .little
    entryPoint := 0x1000
    data := ByteArray.empty
    symbols := [
      ⟨"main", 0x1000, 16, true, false⟩,
      ⟨"foo", 0x2000, 4, true, false⟩
    ]
  }
  let xrefProject : Project.Project := {
    image := some image
    disasm := some { entry := 0x1000, instructions }
  }
  let xrefs := Analysis.Xrefs.create xrefProject
  assertEqual "xrefs finds direct caller" [0x1000]
    ((Analysis.Xrefs.callers xrefs 0x2000).map Analysis.Xrefs.Xref.source)
  assertEqual "xrefs finds direct callee" [0x2000]
    ((Analysis.Xrefs.callees xrefs "main").map Analysis.Xrefs.Xref.target)
  assertEqual "xrefs finds constant load" [0x1004]
    ((Analysis.Xrefs.references xrefs .load 0x3000).map Analysis.Xrefs.Xref.source)
  assertEqual "xrefs finds constant store" [0x1008]
    ((Analysis.Xrefs.references xrefs .store 0x3000).map Analysis.Xrefs.Xref.source)
  assertEqual "xrefs finds direct jump" [0x100c]
    ((Analysis.Xrefs.references xrefs .jump 0x2000).map Analysis.Xrefs.Xref.source)
  assertEqual "xrefs resolves function owner" (some "main")
    ((Analysis.Xrefs.functionOf xrefs 0x1004).map Image.Symbol.name)
  assertEqual "xrefs resolves function symbol" (some "foo")
    ((Analysis.Xrefs.functionAt xrefs 0x2000).map Image.Symbol.name)
  assertEqual "xrefs lists functions" ["main", "foo"] (Analysis.Xrefs.functions xrefs)
  let decompiledProject := Decompile.project xrefProject
  assertTrue "project decompiler renders main" ((decompiledProject.splitOn "void main()").length > 1)
  assertTrue "project decompiler renders memory load" ((decompiledProject.splitOn "RAX = read64_le(mem, 0x3000);").length > 1)
  assertTrue "project decompiler renders empty function" ((decompiledProject.splitOn "void foo()").length > 1)
  let callgraph := Analysis.Callgraph.create xrefs
  assertTrue "callgraph reaches callee" ((Analysis.Callgraph.reachable callgraph [0x1000]).contains 0x2000)
  assertEqual "acyclic callgraph has no recursive functions" [] (Analysis.Callgraph.recursiveFunctions callgraph)
  assertEqual "acyclic callgraph has singleton SCCs" 2 (Analysis.Callgraph.stronglyConnected callgraph).length
  assertTrue "callgraph renders named edge" (((Analysis.Callgraph.render callgraph).splitOn "main -> foo").length > 1)
  let cyclicIndex : Analysis.Xrefs.Index := { xrefs with
    xrefs := xrefs.xrefs ++ [⟨0x2000, 0x1000, .call⟩]
  }
  let cyclic := Analysis.Callgraph.create cyclicIndex
  assertTrue "callgraph detects recursive SCC"
    ((Analysis.Callgraph.stronglyConnected cyclic).any fun component => component.length = 2)
  assertEqual "callgraph reports both recursive functions" [0x1000, 0x2000]
    (Analysis.Callgraph.recursiveFunctions cyclic)
  let state : Var := ⟨"state", .imm 64, 0, false⟩
  let smInstructions : List Disasm.Insn := [
    ⟨0x1000, 4, "set1", .normal, none, [.move state (.int (BitVec.ofNat 64 1))]⟩,
    ⟨0x1004, 4, "case1", .jump, some 0x2000, [.jmp (.int (BitVec.ofNat 64 0x2000))]⟩,
    ⟨0x1008, 4, "set2", .normal, none, [.move state (.int (BitVec.ofNat 64 2))]⟩,
    ⟨0x100c, 4, "case2", .jump, some 0x3000, [.jmp (.int (BitVec.ofNat 64 0x3000))]⟩
  ]
  let machine := Analysis.StateMachine.analyze smInstructions
  assertEqual "state machine selects state variable" (some "state") (machine.stateVar.map Bap.Var.name)
  assertEqual "state machine recovers case values" [1, 2] (machine.cases.map Analysis.StateMachine.Case.value)
  assertEqual "state machine recovers case targets" [0x2000, 0x3000]
    (machine.cases.map Analysis.StateMachine.Case.target)
  assertTrue "state machine recognizes flattened CFG" (Analysis.StateMachine.isFlattened machine)
  assertEqual "state machine resolves transition" (some 0x3000) (Analysis.StateMachine.transition machine 2)
  assertTrue "state machine renders cases" (((Analysis.StateMachine.render machine).splitOn "state state").length > 1)
  let indirectMachine := Analysis.StateMachine.analyze (smInstructions ++
    [⟨0x1010, 4, "indirect", .indirectJump, none, [.jmp (.var state)]⟩])
  assertTrue "state machine marks indirect CFG incomplete" !indirectMachine.complete
  assertTrue "state machine rejects incomplete flattening" !(Analysis.StateMachine.isFlattened indirectMachine)
  let recovery := Analysis.Deflatten.recover 0x1000 smInstructions [0x2000, 0x3000]
  assertTrue "deflattening accepts declared external targets" recovery.complete
  assertTrue "deflattening adds first direct case edge" (recovery.disasm.edges.contains (0x1000, 0x2000))
  assertTrue "deflattening adds second direct case edge" (recovery.disasm.edges.contains (0x1008, 0x3000))
  assertEqual "deflattening preserves state variable" (some "state") (recovery.stateVar.map Bap.Var.name)
  let missingRecovery := Analysis.Deflatten.recover 0x1000 smInstructions
  assertTrue "deflattening rejects undeclared external targets" !missingRecovery.complete
  let memorySlice := Analysis.Slice.backwardProject xrefProject 0x1000 [.mem 0x3000 8]
  assertEqual "backward slice follows memory stores" [0x1004, 0x1008] memorySlice.sites
  assertEqual "backward slice preserves memory input" [Analysis.Slice.Location.mem 0x3000 8] memorySlice.live
  assertTrue "constant memory slice is complete" memorySlice.complete
  let registerSlice := Analysis.Slice.backwardProject xrefProject 0x1000 [.reg rax]
  assertEqual "backward slice follows stored register" [0x1004, 0x1008] registerSlice.sites
  assertEqual "backward slice replaces register with memory input" [Analysis.Slice.Location.mem 0x3000 8] registerSlice.live
  let unrelatedSlice := Analysis.Slice.backwardProject xrefProject 0x1000
    [.reg ⟨"RDX", .imm 64, 0, false⟩]
  assertEqual "backward slice excludes unrelated instructions" [] unrelatedSlice.sites
  assertEqual "backward slice keeps unrelated live register" [Analysis.Slice.Location.reg ⟨"RDX", .imm 64, 0, false⟩]
    unrelatedSlice.live
  let partialDynamic := Analysis.DynamicSlice.backward xrefProject 0x1000 [0x1008] [.mem 0x3000 8]
  assertEqual "dynamic slice keeps traced site" [0x1008] partialDynamic.sites
  assertEqual "dynamic slice reports missing producer" [0x1004] partialDynamic.gaps
  assertTrue "dynamic slice with gaps is incomplete" !partialDynamic.complete
  let fullDynamic := Analysis.DynamicSlice.backward xrefProject 0x1000 [0x1004, 0x1008] [.mem 0x3000 8]
  assertEqual "dynamic slice with coverage includes all sites" [0x1004, 0x1008] fullDynamic.sites
  assertEqual "dynamic slice with coverage has no gaps" [] fullDynamic.gaps
  assertTrue "dynamic slice with coverage is complete" fullDynamic.complete
  let outsideAccess : Bap.Emu.TraceAccess := {
    insn := 0
    pc := 0x2000
    address := 0x3000
    size := 8
    write := true
    value := some 0
    thread := 1
  }
  let outsideDynamic := Analysis.DynamicSlice.backwardWithAccesses xrefProject 0x1000 [0x1004, 0x1008]
    [outsideAccess] [.mem 0x3000 8]
  assertEqual "dynamic slice reports outside writer" [0x2000] outsideDynamic.gaps
  assertTrue "dynamic slice outside writer is incomplete" !outsideDynamic.complete
  IO.FS.writeFile "native/build/plugin-test.scm"
    "(plugin demo (pass marker (set origin plugin)) (pass detailed (deps marker) (set detail ok)))"
  let registry ← Plugin.loadMany defaultRegistry ["native/build/plugin-test.scm"]
  assertTrue "dynamic plugin pass is registered" (registry.findPass "detailed").isSome
  match analyze registry project ["detailed"] with
  | .error error => throw <| IO.userError s!"dynamic plugin analysis failed: {repr error}"
  | .ok analyzed =>
    assertEqual "dynamic plugin pass executes" (some "plugin") (analyzed.get "origin")
    assertEqual "dynamic plugin dependency executes" (some "ok") (analyzed.get "detail")
    assertTrue "dynamic plugin records pass history" (analyzed.passed.contains "marker")

end Bap.Tests.Project
