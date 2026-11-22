import BapTests.Support
import Bap.Analysis.Flattening

/-! What `Bap.Analysis.Flattening` finds of `testsuite/src/flattened.c` of each target, without running it: the dispatcher of `steps`,
where it keeps its state, the handler of each state, and the graph of the states, of each the way it chooses the next: directly, or
on a condition, by a branch or a conditional move that the compiler hoisted out of the handler; and a partition with the flow that
the machine hides, which `Frame` and `Values` go over. The same of `testsuite/src/cff.c` compiled without optimization, whose state is
on the stack. Of x86_64 and AArch64, a run with the profile that it found sees no other
way between the states, and the handlers start where it says. And a partition takes the targets of a jump that a run saw, where the
code doesn't say them. -/

namespace Bap.Tests.Flattening

open Bap Bap.Analysis

private def targets : List String :=
  ["x86_64", "i686", "aarch64", "riscv64", "arm", "mips", "mips64el", "powerpc", "powerpc64le"]

/-- The graph of `steps`: of each state, the states it goes to, and whether it chooses. -/
private def expected : List (Nat × List Nat × Bool) :=
  [(0x3a1f, [0x91c4], false), (0x91c4, [0x5e02, 0x77b0], true), (0x77b0, [0x1d6e, 0xc823], true), (0x1d6e, [0x4b19], false),
    (0xc823, [0x4b19], false), (0x4b19, [0x0e55, 0x91c4], true), (0x0e55, [0x91c4], false)]

private def ofTarget (arch : String) (path : String := s!"testsuite/bin/{arch}-linux-none-flattened")
    (state : Option Cff.StateLocation := none) : IO Unit := do
  let project ← Project.Project.load path
  let some image := project.image | throw (IO.userError s!"{path} doesn't load")
  let some partition ← Values.partition project | throw (IO.userError s!"{path} has no partition")
  let some symbol := image.symbols.find? (·.name == "steps") | throw (IO.userError s!"{path} has no steps")
  let machines ← Flattening.machines image partition
  assertEqual s!"{arch}: steps is the one flattened machine" [symbol.addr] (machines.map (·.function))
  let some machine := machines.head? | throw (IO.userError s!"{path} has no machine")
  if let some state := state then assertEqual s!"{arch}: where the state is" state machine.state
  assertEqual s!"{arch}: the first state" (some 0x3a1f) machine.initial
  let states : List Nat := expected.map fun (state, _, _) => state
  assertEqual s!"{arch}: the states" ((states ++ [0x5e02]).mergeSort (· ≤ ·)) machine.cfg.states
  assertEqual s!"{arch}: what ends" [0x5e02] machine.cfg.exits
  for (source, nexts, chooses) in expected do
    let edges := machine.cfg.edges.filter (·.source == source)
    assertEqual s!"{arch}: where {source} goes" (nexts.map some) ((edges.map (·.target)).mergeSort fun a b => a.getD 0 ≤ b.getD 0)
    assertTrue s!"{arch}: how {source} chooses" (edges.all (·.kind == if chooses then .conditional else .direct))
  -- each handler starts in steps, apart from the others and the dispatcher
  let starts := machine.handlers.map (·.2)
  assertEqual s!"{arch}: each state has a handler" machine.cfg.states.length starts.length
  assertEqual s!"{arch}: and they start apart" starts.length (Partition.dedup starts).length
  assertTrue s!"{arch}: none at the dispatcher" (!starts.contains machine.dispatcher)
  assertTrue s!"{arch}: all in steps"
    (starts.all fun start => symbol.addr ≤ start && start < symbol.addr + symbol.size)
  -- the flow that the machine hides: from where each round ends, to the handlers of the states it sets
  let flat := Flattening.deflatten partition machines
  for (source, nexts, _) in expected do
    let lasts := (machine.arrivals.filter fun arrival => arrival.state == some source).filterMap (·.last)
    for next in nexts do
      let some handler := machine.handlerOf next | throw (IO.userError s!"{path}: no handler of {next}")
      assertTrue s!"{arch}: the end of {source} goes to the handler of {next}"
        (lasts.any fun last => flat.edges.contains (last, handler))
  let backs := flat.edges.filter fun (source, target) =>
    target == machine.dispatcher && machine.arrivals.any fun arrival => arrival.last == some source && arrival.state.isSome
  assertEqual s!"{arch}: no round goes back to the dispatcher" ([] : List (Nat × Nat)) backs
  -- which the analyses of frames and values go over
  let some frames := Frame.frames image flat | throw (IO.userError s!"{path}: no frames of the flow")
  let some signature := frames.signatures.find? (·.entry == symbol.addr) | throw (IO.userError s!"{path}: no signature")
  assertEqual s!"{arch}: steps takes one argument, of the flow" 1 (signature.registerArguments + signature.stackArguments.length)
  assertTrue s!"{arch}: and has variables" (Values.ofPartition image flat frames).isSome

/-- A run with the profile that was found without running: the ways between the states are those found, and the handlers start
where they were found to. -/
private def ran (arch : String) : IO Unit := do
  let path := s!"testsuite/bin/{arch}-linux-none-flattened"
  let project ← Project.Project.load path
  let some image := project.image | throw (IO.userError s!"{path} doesn't load")
  let some partition ← Values.partition project | throw (IO.userError s!"{path} has no partition")
  let some machine := (← Flattening.machines image partition).head? | throw (IO.userError s!"{path} has no machine")
  let kernel := Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile path)
  let running ← Bap.Linux.start kernel "/test" ["/test"]
  let journal ← running.journal
  let recorder ← Cff.Recorder.attach running.emu machine.profile
  assertEqual s!"{arch}: the flattened program ends" (Bap.Tasks.ScheduleOutcome.finished 0) (← running.run fun _ => pure ())
  let dispatcher ← Cff.recoverIn running.emu machine.profile (← recorder.visits.get) (some (← journal.toRecord))
  assertEqual s!"{arch}: steps of 27 runs 448 rounds" 448 dispatcher.transitions.length
  assertEqual s!"{arch}: what ran is what was found" ([] : List String) (Flattening.agrees machine dispatcher)
  -- and all the ways that were found, but that of 4b19 to e55, which 27 takes once, were taken
  assertEqual s!"{arch}: the run took each way" machine.cfg.edges.length dispatcher.graph.length

/-- A jump that a partition doesn't resolve without what value sets know, with the targets that a run would have seen. -/
private def observed : IO Unit := do
  let project ← Project.Project.load "testsuite/bin/x86_64-linux-none-hoisted"
  let some known ← Values.partition project | throw (IO.userError "hoisted has no partition")
  let some table := known.tables.head? | throw (IO.userError "hoisted has no table")
  let some alone ← Partition.partition project | throw (IO.userError "hoisted has no partition")
  assertEqual "a partition alone leaves the jump" [table.jump] alone.unresolved
  let some seen ← Partition.partition project (observed := fun jump => if jump == table.jump then table.targets else [])
    | throw (IO.userError "hoisted has no partition")
  assertEqual "of what a run saw, it doesn't" ([] : List Nat) seen.unresolved
  assertEqual "and goes to all of it" (table.targets.mergeSort (· ≤ ·))
    (((seen.tables.find? (·.jump == table.jump)).map (·.targets)).getD [] |>.mergeSort (· ≤ ·))
  let handler := table.targets.headD 0
  assertTrue "and has the code of its targets" (seen.disasm.instructions.any (·.address == handler))

/-- The first state is of the first way from the entry to the dispatcher, not of one that returned before it; and a choice of
more constants than are gone over isn't some of them. -/
private def units : IO Unit := do
  let arrivals : List Flattening.Arrival :=
    [{ state := none, last := some 1, nexts := none, ended := true }, { state := none, last := some 2, nexts := some [7] },
      { state := some 7, last := some 3, nexts := some [8] }, { state := some 8, last := some 4, nexts := some [7] }]
  assertEqual "the first state is of a way that came to the dispatcher" (some 7) (Flattening.graphOf arrivals).entry
  let selector : Symbolic.Expr := .var "choice@0" 5
  let chain (count : Nat) : Symbolic.Expr := (List.range count).foldl (init := .const (BitVec.ofNat 32 1000))
    fun others index => .ite (.app "=" 1 [selector, .const (BitVec.ofNat 5 index)]) (.const (BitVec.ofNat 32 index)) others
  assertEqual "a choice of a few constants is all of them" (some 4) ((Flattening.choices (chain 3)).map (·.length))
  assertEqual "a choice of more than are gone over isn't some of them" none (Flattening.choices (chain 20))

/-- A flattened function without optimization, `testsuite/src/flattened0.c`: its state is four bytes on the stack beside what its
handlers change, whose cells aren't kept with it from round to round, so that no round is cut short of what memory has grown to, and
every state has its edges. -/
private def unoptimized : IO Unit := do
  let path := "testsuite/bin/x86_64-linux-none-flattened0"
  let project ← Project.Project.load path
  let some image := project.image | throw (IO.userError s!"{path} doesn't load")
  let some partition ← Values.partition project | throw (IO.userError s!"{path} has no partition")
  let machines ← Flattening.machines image partition
  let some machine := machines.head? | throw (IO.userError s!"{path} has no machine")
  assertEqual "flattened0: the states" [0x11, 0x22, 0x33, 0x44, 0x55, 0x66] machine.cfg.states
  for (source, nexts) in [(0x11, [0x22]), (0x22, [0x33, 0x44]), (0x33, [0x55]), (0x44, [0x55]), (0x55, [0x22, 0x66])] do
    assertEqual s!"flattened0: where {source} goes" (nexts.map some)
      (((machine.cfg.edges.filter (·.source == source)).map (·.target)).mergeSort fun a b => a.getD 0 ≤ b.getD 0)
  assertTrue "flattened0: the last state ends" (machine.cfg.exits.contains 0x66)

def run : IO Unit := do
  units
  unoptimized
  for arch in targets do
    ofTarget arch
  -- cff.c, as it is compiled without optimization: its state on the stack, which every case's code jumps to the end of a loop after
  -- setting
  ofTarget "x86_64 cff" "testsuite/bin/x86_64-linux-gnu-cff" (some (.relative "RBP" (-4) 4))
  for arch in ["x86_64", "aarch64"] do
    ran arch
  observed

end Bap.Tests.Flattening
