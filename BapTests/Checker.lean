import BapTests.Support
import Bap.Analysis.Checker

/-! What `Bap.Analysis.Checker` finds of `testsuite/src/checker.c` of each target, and only that: a load through what one way makes
null; a load of a local that one way doesn't write, but not of one that every way does; a store at an index past an array of the
stack, and one past an array of the program, but not the loads within them; a way that calls `taken`, which some input takes, and
none that calls `untaken`, which none does. -/

namespace Bap.Tests.Checker

open Bap Bap.Analysis

private def targets : List String :=
  ["x86_64", "i686", "aarch64", "riscv64", "arm", "mips", "mips64el", "powerpc", "powerpc64le"]

private def ofTarget (arch : String) : IO Unit := do
  let path := s!"testsuite/bin/{arch}-linux-none-checker"
  let project ← Project.Project.load path
  let some image := project.image | throw (IO.userError s!"{path} doesn't load")
  let some partition ← Values.partition project | throw (IO.userError s!"{path} has no partition")
  let function (name : String) : IO Partition.Function := do
    let some symbol := image.symbols.find? (·.name == name) | throw (IO.userError s!"{path} has no {name}")
    let some found := partition.functionAt symbol.addr | throw (IO.userError s!"{path}: no function at {name}")
    pure found
  let findings ← Checker.check image partition
  let nameOf (entry : Nat) : String := ((partition.functions.find? (·.entry == entry)).map (·.name)).getD "?"
  let of (tag : Checker.Tag) : List String :=
    ((findings.filter (·.tag == tag)).map (nameOf ·.function)).mergeSort (· ≤ ·)
  assertEqual s!"{arch}: what loads through null" ["nulls"] (of .nullDereference)
  assertEqual s!"{arch}: what reads what it may not have written" ["uninit"] (of .uninitialized)
  assertEqual s!"{arch}: what stores past an array" ["globalOverflow", "overflow"] (of .outOfBounds)
  -- the way to the load of null ends at it
  for finding in findings.filter (·.tag == .nullDereference) do
    assertEqual s!"{arch}: the way to the load of null ends at it" (some finding.insn) finding.path.getLast?
    assertEqual s!"{arch}: the way to the load of null starts at its function" (some finding.function) finding.path.head?
  -- of the calls of `feasible`, the way to `taken` and none to `untaken`
  let feasible ← function "feasible"
  for (callee, expected) in [("taken", true), ("untaken", false)] do
    let target ← function callee
    let calls := feasible.calls.filter (·.2 == target.entry)
    assertEqual s!"{arch}: feasible calls {callee} once" 1 calls.length
    for (call, _) in calls do
      let way ← Checker.feasiblePath image partition feasible call
      assertEqual s!"{arch}: some input takes a way to {callee}" expected way.isSome
      if let some way := way then
        assertEqual s!"{arch}: the way to {callee} goes from the entry to the call" (some feasible.entry, some call)
          (way.head?, way.getLast?)

def run : IO Unit := do
  for arch in targets do
    ofTarget arch

end Bap.Tests.Checker
