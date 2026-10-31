import BapTests.Support

namespace Bap.Tests.Project

open Bap
open Bap.Project

private def summarize : Pass := {
  name := "summarize"
  run := fun project =>
    let instructions := project.disasm.map (fun disasm => disasm.instructions.length) |>.getD 0
    .ok (project.set "instructions" (toString instructions))
}

private def report : Pass := {
  name := "report"
  dependencies := ["summarize"]
  run := fun project =>
    let blocks := project.disasm.map (fun disasm => disasm.blocks.length) |>.getD 0
    .ok (project.set "blocks" (toString blocks) |>.set "status" "analyzed")
}

private def recordingPass (name : String) (dependencies : List String := []) : Pass := {
  name := name
  dependencies := dependencies
  run := fun project =>
    let trace := (project.get "trace").getD ""
    .ok (project.set "trace" (trace ++ name))
}

/-- `functionOf` as it is defined, against which the binary search of its table is tested. -/
private def functionOfBySpec (functions : List Image.Symbol) (address : Nat) : Option Image.Symbol :=
  let nearest := functions.foldl (init := (none : Option Nat)) fun best symbol =>
    if symbol.addr ≤ address && best.all (· ≤ symbol.addr) then some symbol.addr else best
  let spans (symbol : Image.Symbol) : Bool :=
    symbol.addr ≤ address && if symbol.size = 0 then nearest = some symbol.addr else address < symbol.addr + symbol.size
  functions.foldl (init := none) fun best symbol =>
    if spans symbol && best.all (·.addr ≤ symbol.addr) then some symbol else best

/-- Pseudorandom functions, of few addresses to have aliases, overlaps and functions without sizes. -/
private def randomFunctions (seed count : Nat) : List Image.Symbol :=
  ((List.range count).foldl (init := (seed, ([] : List Image.Symbol))) fun state index =>
    let next := (state.1 * 1103515245 + 12345) % 2147483648
    let addr := next / 1024 % 64
    let size := if next % 3 == 0 then 0 else next / 65536 % 16
    (next, ⟨s!"f{index}", addr, size, true, false⟩ :: state.2)).2

/-- `stronglyConnected` as it reads. -/
private def componentsBySpec (callgraph : Analysis.Callgraph.Callgraph) : List (List Nat) :=
  let components := callgraph.graph.nodes.foldl (init := (callgraph.graph.nodes, [])) fun current node =>
    if !current.1.contains node then current
    else
      let forward := Graph.reachable callgraph.graph node
      let component := forward.filter fun candidate =>
        (Graph.reachable callgraph.graph candidate).contains node
      (current.1.filter fun candidate => !component.contains candidate, current.2 ++ [component])
  components.2

private def componentsFastPath : IO Unit := do
  let graphs : List (Graph.Graph Nat) := [
    {},
    { nodes := [1, 2, 3], edges := [(1, 2), (2, 1), (3, 3), (9, 1), (1, 9)] },
    { nodes := (List.range 40).reverse, edges := (List.range 40).flatMap fun i => [(i, (i * 7 + 3) % 40), (i, (i * i + 1) % 40)] },
    { nodes := [5, 5, 6, 7], edges := [(5, 6), (6, 5), (6, 7), (6, 7)] },
    { nodes := List.range 60, edges := (List.range 59).map fun i => (i, i + 1) }]
  for graph in graphs do
    let callgraph : Analysis.Callgraph.Callgraph := { graph := graph }
    assertEqual "strongly connected components" (componentsBySpec callgraph) (Analysis.Callgraph.stronglyConnected callgraph)

def run : IO Unit := do
  componentsFastPath
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
  match runPasses [report, summarize] project with
  | .error error => throw <| IO.userError s!"analysis failed: {repr error}"
  | .ok analyzed =>
    assertTrue "the summary is of the whole of the code" (((analyzed.get "instructions").bind String.toNat?).getD 0 > 1000)
    assertTrue "and of many blocks" (((analyzed.get "blocks").bind String.toNat?).getD 0 > 100)
    assertEqual "default analysis status" (some "analyzed") (analyzed.get "status")
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
  for seed in List.range 40 do
    let functions := randomFunctions seed (seed % 13 * 4)
    let index : Analysis.Xrefs.Index := { functions }
    for address in List.range 90 do
      if !((Analysis.Xrefs.functionOf index address).map (·.name) == (functionOfBySpec functions address).map (·.name)) then
        throw <| IO.userError s!"functionOf differs from its specification, seed {seed} address {address}"
  IO.println "ok: binary search of functions agrees with the definition"
  let binary ← Project.load "/mnt/data/Dev/bap/testsuite/bin/x86_64-linux-gnu-crc-loop"
  let binaryDisasm := binary.disasm.getD { entry := 0 }
  assertEqual "whole binary: instructions" 134 binaryDisasm.instructions.length
  assertEqual "whole binary: blocks" 32 binaryDisasm.blocks.length
  assertEqual "whole binary: errors" [] binaryDisasm.errors
  let binaryIndex := Analysis.Xrefs.discover binary
  let binaryGraph := Analysis.Callgraph.create binaryIndex
  assertEqual "whole binary: xrefs" 30 binaryIndex.xrefs.length
  assertEqual "whole binary: functions" 10 binaryIndex.functions.length
  assertEqual "whole binary: callgraph edges" 2 binaryGraph.graph.edges.length
  assertTrue "whole binary: main is a function" (binaryIndex.functions.any (·.name == "main"))
  let stripped ← Project.load "/mnt/data/Dev/bap/testsuite/bin/x86_64-linux-gnu-loader-stdin-stripped"
  let strippedIndex := Analysis.Xrefs.discover stripped
  assertTrue "a stripped binary has its functions from the scan"
    (strippedIndex.functions.any fun symbol => symbol.name.startsWith "sub_")
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
  assertEqual "backward slice preserves memory input" [Analysis.Slice.Location.memOf mem 0x3000 8] memorySlice.live
  assertTrue "constant memory slice is determined" memorySlice.determined
  assertEqual "slice reports the call it crosses with memory live" [0x1000] memorySlice.calls
  assertTrue "slice across a live call is incomplete" !memorySlice.complete
  -- several memory variables: a store to the second doesn't hide the store to the first at the same address
  let memOne : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
  let memTwo : Bap.Var := ⟨"other", .mem 64 8, 0, false⟩
  let cell : Bil.Exp := .int (BitVec.ofNat 64 0x3000)
  let storeTo (memory : Bap.Var) (value : Nat) : Bil.Stmt :=
    .move memory (.store (.var memory) cell (.int (BitVec.ofNat 8 value)) .little 1)
  let aliased : List Disasm.Insn := [
    { address := 0, size := 1, asm := "", bil := [storeTo memOne 1] },
    { address := 1, size := 1, asm := "", bil := [storeTo memTwo 2] }]
  assertEqual "the memory variables of the code" [memOne, memTwo] (Analysis.Slice.memories aliased)
  let firstMemory := Analysis.Slice.backward aliased [.memOf memOne 0x3000 1]
  assertEqual "a store to another memory is no site" [0] firstMemory.sites
  assertTrue "code with two memories can be complete" firstMemory.complete
  let bothMemories := Analysis.Slice.backward aliased [.mem 0x3000 1]
  assertEqual "a criterion naming no memory is about each of them" [0, 1] bothMemories.sites
  assertTrue "a criterion naming no memory is complete with two memories" bothMemories.complete
  let moved : List Disasm.Insn := [
    { address := 0, size := 1, asm := "", bil := [storeTo memOne 1] },
    { address := 1, size := 1, asm := "", bil := [.move memTwo (.var memOne)] },
    { address := 2, size := 1, asm := "", bil := [storeTo memOne 9] }]
  let movedSlice := Analysis.Slice.backward moved [.memOf memTwo 0x3000 1]
  assertEqual "a move between memories carries what is live" [0, 1] movedSlice.sites
  assertEqual "nothing is live before the store that a move carries" [] movedSlice.live
  assertTrue "a slice through a move between memories is complete" movedSlice.complete
  let unmoved := Analysis.Slice.backward moved.tail [.memOf memTwo 0x3000 1]
  assertEqual "a move renames a live range" [Analysis.Slice.Location.memOf memOne 0x3000 1] unmoved.live
  let noCallSlice := Analysis.Slice.backward instructions.tail [.mem 0x3000 8]
  assertTrue "constant memory slice without calls is complete" noCallSlice.complete
  let registerSlice := Analysis.Slice.backwardProject xrefProject 0x1000 [.reg rax]
  -- the store only reads the register, so it has no part in its value
  assertEqual "backward slice takes the definition of a register, not what reads it" [0x1004] registerSlice.sites
  assertEqual "backward slice replaces register with memory input" [Analysis.Slice.Location.memOf mem 0x3000 8] registerSlice.live
  let unrelatedSlice := Analysis.Slice.backwardProject xrefProject 0x1000
    [.reg ⟨"RDX", .imm 64, 0, false⟩]
  assertEqual "backward slice excludes unrelated instructions" [] unrelatedSlice.sites
  assertEqual "backward slice keeps unrelated live register" [Analysis.Slice.Location.reg ⟨"RDX", .imm 64, 0, false⟩]
    unrelatedSlice.live
  -- control flow: a branch is in the slice exactly when what runs next depends on it
  let sliceX : Bap.Var := ⟨"x", .imm 64, 0, false⟩
  let sliceY : Bap.Var := ⟨"y", .imm 64, 0, false⟩
  let sliceC : Bap.Var := ⟨"c", .imm 1, 0, false⟩
  let word (value : Nat) : Bil.Exp := .int (BitVec.ofNat 64 value)
  let setTo (var : Bap.Var) (value : Nat) : Bil.Program := [.move var (word value)]
  let branch (address target : Nat) : Disasm.Insn :=
    ⟨address, 1, "branch", .conditionalJump, some target, [.ifElse (.var sliceC) [.jmp (word target)] []]⟩
  let jump (address target : Nat) : Disasm.Insn := ⟨address, 1, "jump", .jump, some target, [.jmp (word target)]⟩
  let plain (address : Nat) (bil : Bil.Program) : Disasm.Insn := ⟨address, 1, "plain", .normal, none, bil⟩
  let chooses : List Disasm.Insn :=
    [branch 0 3, plain 1 (setTo sliceX 1), jump 2 4, plain 3 (setTo sliceX 2), plain 4 (setTo sliceY 3)]
  let chosen := Analysis.Slice.backward chooses [.reg sliceX]
  assertEqual "a branch choosing a definition and both definitions are the slice" [0, 1, 3] chosen.sites
  assertEqual "the branch condition is what is live" [Analysis.Slice.Location.reg sliceC] chosen.live
  assertTrue "a slice of a diamond is complete" chosen.complete
  assertEqual "what follows a definition without another site is the end" none (chosen.nextSite 2)
  let around : List Disasm.Insn :=
    [plain 0 (setTo sliceX 5), branch 1 3, plain 2 (setTo sliceY 1), plain 3 [.move sliceY (.var sliceX)]]
  let aroundSlice := Analysis.Slice.backward around [.reg sliceX]
  assertEqual "a branch nothing depends on stays out" [0] aroundSlice.sites
  assertEqual "no site follows the definition" none (aroundSlice.nextSite 1)
  assertTrue "a slice past an irrelevant branch is complete" aroundSlice.complete
  let joined : List Disasm.Insn :=
    [branch 0 2, plain 1 (setTo sliceY 1), plain 2 (setTo sliceX 7), plain 3 (setTo sliceY 2)]
  let joinedSlice := Analysis.Slice.backward joined [.reg sliceX]
  assertEqual "arms joining before the definition leave the branch out" [2] joinedSlice.sites
  assertEqual "both arms go on at the definition" (some 2) (joinedSlice.nextSite 1)
  assertEqual "the branch goes on at the definition" (some 2) (joinedSlice.nextSite 0)
  assertTrue "a slice after a join is complete" joinedSlice.complete
  let bump : Bil.Stmt := .move sliceX (.bin .add (.var sliceX) (word 1))
  let loop : List Disasm.Insn := [plain 0 (setTo sliceX 0), branch 1 4, plain 2 [bump], jump 3 1, plain 4 (setTo sliceY 2)]
  let loopSlice := Analysis.Slice.backward loop [.reg sliceX]
  assertEqual "a loop computing the criterion is in the slice" [0, 1, 2] loopSlice.sites
  assertEqual "only the loop condition is live before it" [Analysis.Slice.Location.reg sliceC] loopSlice.live
  assertTrue "a slice of a loop is complete" loopSlice.complete
  assertEqual "the back edge goes on at the loop head" (some 1) (loopSlice.nextSite 3)
  let loopOther := Analysis.Slice.backward loop [.reg sliceY]
  assertEqual "a loop nothing depends on stays out" [4] loopOther.sites
  assertTrue "a slice skipping a loop is complete" loopOther.complete
  let indirect : List Disasm.Insn := [plain 0 (setTo sliceX 1), ⟨1, 1, "jmp", .indirectJump, none, [.jmp (.var sliceY)]⟩]
  assertTrue "an indirect jump leaves a slice incomplete" !(Analysis.Slice.backward indirect [.reg sliceX]).complete
  assertTrue "an indirect jump leaves a slice undetermined" !(Analysis.Slice.backward indirect [.reg sliceX]).determined
  let noEdge : List Disasm.Insn := [plain 0 [.ifElse (.var sliceC) [.jmp (word 2)] []], plain 1 (setTo sliceX 1), plain 2 (setTo sliceY 1)]
  assertTrue "a jump the CFG has no edge for leaves a slice incomplete" !(Analysis.Slice.backward noEdge [.reg sliceX]).complete
  let withEdge := Analysis.Slice.backwardCfg noEdge [(0, 1), (0, 2), (1, 2)] none [.reg sliceX]
  assertTrue "the edges of the CFG describe the same code" withEdge.complete
  assertEqual "a site follows its branch with the edges of the CFG" [0, 1] withEdge.sites
  let unknownOther : List Disasm.Insn := [{ address := 0, size := 1, asm := "", bil :=
    [.move memTwo (.store (.var memTwo) (.var rax) (.int (BitVec.ofNat 8 1)) .little 1)] }]
  assertEqual "an unknown store to another memory is no site" []
    (Analysis.Slice.backward unknownOther [.memOf memOne 0x3000 1]).sites
  assertEqual "an unknown store to this memory is a site" [0]
    (Analysis.Slice.backward unknownOther [.memOf memTwo 0x3000 1]).sites
  assertTrue "a site writes the same at an address that agrees, wherever it is"
    (Analysis.Slice.backward unknownOther [.memOf memTwo 0x3000 1]).complete
  -- value analysis: slots of a stack pointer, through the casts of the lifters and its adjustments
  let stackPointer : Var := ⟨"RSP", .imm 64, 0, false⟩
  let word (value : Nat) : Bil.Exp := .int (BitVec.ofNat 64 value)
  let slot (offset : Nat) : Bil.Exp :=
    .cast .low 64 (.bin .add (.cast .unsigned 64 (.var stackPointer)) (.cast .unsigned 64 (word offset)))
  let slots : List Disasm.Insn := [
    { address := 0, size := 1, asm := "", bil := [.move memOne (.store (.var memOne) (slot 8) (.var rax) .little 8)] },
    { address := 1, size := 1, asm := "", bil := [.move memOne (.store (.var memOne) (slot 16) (word 1) .little 8)] },
    { address := 2, size := 1, asm := "", bil := [.move rax (.load (.var memOne) (slot 8) .little 8)] }]
  let slotSlice := Analysis.Slice.backward slots [.reg rax]
  assertEqual "a store to another stack slot is no site" [0, 2] slotSlice.sites
  assertTrue "stack slots leave a slice complete" slotSlice.complete
  let index : Var := ⟨"RCX", .imm 64, 0, false⟩
  let indexed : List Disasm.Insn := [
    { address := 0, size := 1, asm := "", bil := [.move memOne (.store (.var memOne) (slot 8) (word 1) .little 8)] },
    { address := 1, size := 1, asm := "", bil := [.move rax (.load (.var memOne) (.bin .add (.var index) (.var stackPointer)) .little 8)] }]
  let indexedSlice := Analysis.Slice.backward indexed [.reg rax]
  assertEqual "a read at an address that is not known needs every store" [0, 1] indexedSlice.sites
  assertTrue "and is no reason to give up" indexedSlice.complete
  let partialDynamic := Analysis.DynamicSlice.backward xrefProject 0x1000 [0x1008] [.mem 0x3000 8]
  assertEqual "dynamic slice keeps traced site" [0x1008] partialDynamic.sites
  assertEqual "dynamic slice reports missing producer" [0x1004] partialDynamic.gaps
  assertTrue "dynamic slice with gaps is incomplete" !partialDynamic.complete
  let fullDynamic := Analysis.DynamicSlice.backward xrefProject 0x1000 [0x1004, 0x1008] [.mem 0x3000 8]
  assertEqual "dynamic slice with coverage includes all sites" [0x1004, 0x1008] fullDynamic.sites
  assertEqual "dynamic slice with coverage has no gaps" [] fullDynamic.gaps
  assertTrue "dynamic slice with coverage is complete" fullDynamic.complete
  let executedCall := Analysis.DynamicSlice.backward xrefProject 0x1000 [0x1000, 0x1004, 0x1008] [.mem 0x3000 8]
  assertTrue "dynamic slice through an executed call is incomplete" !executedCall.complete
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
  match Analysis.Protobuf.fields (ByteArray.mk #[255, 255, 255, 255, 255, 255, 255, 255, 255, 127]) with
  | .error "protobuf varint exceeds 64 bits" => IO.println "ok: protobuf rejects varints above 64 bits"
  | .error error => throw <| IO.userError s!"wrong protobuf varint error: {error}"
  | .ok _ => throw <| IO.userError "protobuf accepted a varint above 64 bits"
  match Analysis.Protobuf.fields (ByteArray.mk #[128, 128, 128, 128, 16, 0]) with
  | .error "protobuf field number above 2^29 - 1" => IO.println "ok: protobuf rejects field numbers above 2^29 - 1"
  | .error error => throw <| IO.userError s!"wrong protobuf field number error: {error}"
  | .ok _ => throw <| IO.userError "protobuf accepted an oversized field number"
  match Analysis.Protobuf.fields (ByteArray.mk #[248, 255, 255, 255, 15, 7]) with
  | .ok [{ number, .. }] => assertEqual "protobuf keeps the largest field number" (2 ^ 29 - 1) number
  | _ => throw <| IO.userError "protobuf rejected the largest field number"
  match Analysis.Protobuf.fields (ByteArray.mk #[8, 255, 255, 255, 255, 255, 255, 255, 255, 255, 1]) with
  | .ok [{ value := .varint value, .. }] => assertEqual "protobuf keeps the largest 64-bit varint" (2 ^ 64 - 1) value
  | _ => throw <| IO.userError "protobuf rejected a 64-bit varint"
  let flag : Var := ⟨"flag", .imm 1, 0, false⟩
  let rbx : Var := ⟨"RBX", .imm 64, 0, false⟩
  let value (number : Nat) : Bil.Exp := .int (BitVec.ofNat 64 number)
  let trace : List Disasm.Insn := [
    ⟨0, 4, "", .normal, none, [.move rax (value 5)]⟩,
    ⟨4, 4, "", .normal, none, [.move rbx (value 7)]⟩,
    ⟨8, 4, "", .normal, none, [.move mem (.store (.var mem) (value 0x4000) (.var rbx) .little 8)]⟩,
    ⟨12, 4, "", .normal, none, [.move mem (.store (.var mem) (value 0x3000) (.var rax) .little 8)]⟩,
    ⟨16, 4, "", .normal, none, [.move rbx (value 9)]⟩
  ]
  let endToEnd := Analysis.Slice.backward trace [.mem 0x3000 8]
  assertEqual "slice keeps only what the criterion needs" [0, 12] endToEnd.sites
  assertTrue "slice of a call-free trace is complete" endToEnd.complete
  let runTrace (listed : List Disasm.Insn) : Except String Bil.State :=
    listed.foldlM (fun state insn => do
      let (next, _) ← Bil.execProgram 100 state insn.bil
      .ok next) { env := [(mem, .memory (Memory.empty 64))] }
  let readCriterion (result : Except String Bil.State) : Option Nat :=
    match result with
    | .ok state =>
      match Bil.lookup state.env mem with
      | .ok (@Value.memory width memory) =>
        some (Memory.read memory (BitVec.ofNat width 0x3000) .little 8).toNat
      | _ => none
    | .error _ => none
  assertEqual "running the whole trace writes the criterion" (some 5) (readCriterion (runTrace trace))
  assertEqual "running only the sites reproduces the criterion" (some 5)
    (readCriterion (runTrace (trace.filter fun insn => endToEnd.sites.contains insn.address)))
  let wrapping := Analysis.Slice.backward
    [⟨0, 4, "", .normal, none, [.move mem (.store (.var mem) (.int (BitVec.ofNat 64 (2 ^ 64 - 2))) (.var rax) .little 8)]⟩]
    [.mem 0 4]
  assertEqual "backward slice includes a store that wraps onto a location" [0] wrapping.sites
  assertTrue "a store that wraps is the same store in both runs" wrapping.complete
  let afterExit := Analysis.Slice.backward
    [⟨0, 4, "", .normal, none, [.move rax (.int (BitVec.ofNat 64 5))]⟩,
     ⟨4, 4, "", .normal, none, [.jmp (.int (BitVec.ofNat 64 0x20)), .move rax (.int (BitVec.ofNat 64 6))]⟩]
    [.reg rax]
  assertEqual "backward slice keeps a definition a jump may skip" [0, 4] afterExit.sites
  let insn (address : Nat) (code : Bil.Program) : Disasm.Insn := ⟨address, 4, "", .normal, none, code⟩
  let five : Bil.Exp := .int (BitVec.ofNat 64 5)
  let conditional := Analysis.Slice.backward
    [insn 0 [.move rax five], insn 4 [.ifElse (.var flag) [.move rax five] []]] [.reg rax]
  assertEqual "backward slice keeps definitions a branch may skip" [0, 4] conditional.sites
  let store (location : Bil.Exp) (size : Nat) : Bil.Stmt :=
    .move mem (.store (.var mem) location five .little size)
  let overlapping := Analysis.Slice.backward [insn 0 [store address 8]] [.mem 0x3000 4]
  assertEqual "backward slice finds overlapping stores" [0] overlapping.sites
  assertEqual "backward slice lets a covering store end liveness" [] overlapping.live
  let partialStore := Analysis.Slice.backward [insn 0 [store address 2]] [.mem 0x3000 4]
  assertEqual "backward slice keeps a partly overwritten location" [Analysis.Slice.Location.memOf mem 0x3000 4] partialStore.live
  let dynamicStore := Analysis.Slice.backward [insn 0 [store (.var rax) 8]] [.mem 0x3000 4]
  assertEqual "backward slice includes stores that may alias" [0] dynamicStore.sites
  assertTrue "a dynamic store is a site that writes the same" dynamicStore.complete
  let branching : Project.Project := { xrefProject with
    disasm := some { entry := 0x1000, instructions := instructions.dropLast ++ [⟨0x100c, 4, "jcc", .conditionalJump, some 0x1004, []⟩] } }
  let branchingSlice := Analysis.Slice.backwardProject branching 0x1000 [.mem 0x3000 8]
  assertEqual "project slice follows a loop over its CFG" [0x1004, 0x1008, 0x100c] branchingSlice.sites
  assertTrue "project slice with a live call stays incomplete over branches" !branchingSlice.complete
  let withoutCall : Project.Project := { branching with
    disasm := branching.disasm.map fun disasm => { disasm with instructions := disasm.instructions.tail } }
  let loopingSlice := Analysis.Slice.backwardProject withoutCall 0x1004 [.mem 0x3000 8]
  assertEqual "project slice of a loop without calls has its sites" [0x1004, 0x1008, 0x100c] loopingSlice.sites
  assertTrue "project slice of a loop without calls is complete" loopingSlice.complete
  let overlappingWriter : Bap.Emu.TraceAccess := { outsideAccess with address := 0x3004, size := 8 }
  assertEqual "dynamic slice reports overlapping writer" [0x2000]
    (Analysis.DynamicSlice.backwardWithAccesses xrefProject 0x1000 [0x1004, 0x1008] [overlappingWriter] [.mem 0x3000 8]).gaps
  let sizedIndex : Analysis.Xrefs.Index := { functions := [⟨"sized", 0x1000, 16, true, false⟩] }
  assertEqual "xrefs ends a function at its size" (none : Option String)
    ((Analysis.Xrefs.functionOf sizedIndex 0x1010).map Image.Symbol.name)
  let aliasImage : Image.Image := { image with
    symbols := [⟨"first", 0x1000, 16, true, false⟩, ⟨"second", 0x1000, 16, true, false⟩] }
  let aliasDecompiled := Decompile.project { xrefProject with image := some aliasImage }
  assertEqual "aliases both render their body" 3 (aliasDecompiled.splitOn "RAX = read64_le(mem, 0x3000);").length
  let chain := ["p0", "p1", "p2", "p3", "p4"]
  let chainPasses := (chain.zip ["p1", "p2", "p3", "p4", "a"]).map (fun pair => recordingPass pair.1 [pair.2, "a"]) ++
    [recordingPass "a"]
  match runPasses chainPasses {} with
  | .ok chained => assertEqual "long dependency chains schedule" (some "ap4p3p2p1p0") (chained.get "trace")
  | .error error => throw <| IO.userError s!"acyclic chain failed: {repr error}"
  let regions : Project.Project := { image := some { image with
    memory := (Image.MemoryMap.empty.add ⟨0x1000, ByteArray.mk #[1], true, false, false⟩ ()).add
      ⟨0x1000, ByteArray.mk #[2], true, false, false⟩ () } }
  Project.save regions "native/build/project-regions.sexp"
  let reloaded ← Project.loadSaved "native/build/project-regions.sexp"
  assertEqual "project reload keeps region order" [[2], [1]]
    ((reloaded.image.map fun loaded => loaded.memory.entries.map fun entry => entry.1.data.toList.map UInt8.toNat).getD [])
  let nestedCode : Bil.Program := [.while (.var rax) [.while (.var rax) [.ifElse (.var rax) [.jmp target] []]]]
  let nested : Project.Project := {
    disasm := some { entry := 0, instructions := [⟨0, 4, "quoted \"asm\" (text)", .normal, some 8, nestedCode⟩] }
    storage := [("key with space", "a\nb")]
    passed := ["pass one"]
  }
  match Project.serialize nested with
  | .error error => throw <| IO.userError error
  | .ok text =>
    match Project.deserialize text with
    | .error error => throw <| IO.userError error
    | .ok restored =>
      assertEqual "text round trip keeps storage" nested.storage restored.storage
      assertEqual "text round trip keeps pass history" nested.passed restored.passed
      assertEqual "text round trip keeps instruction text" (some ["quoted \"asm\" (text)"])
        (restored.disasm.map fun disasm => disasm.instructions.map Disasm.Insn.asm)
      assertEqual "text round trip keeps nested code"
        (some [toString (Bil.Wire.printProgram nestedCode)])
        (restored.disasm.map fun disasm => disasm.instructions.map fun insn => toString (Bil.Wire.printProgram insn.bil))

end Bap.Tests.Project
