import BapTests.Support
import Bap.Analysis.Partition

/-! What `Bap.Analysis.Partition` finds of `testsuite/src/partition.c` of each target, as its symbols say it should: each function
with all the instructions in its symbol, which those of a `switch` only are of the targets of its table; no indirect jump left
unresolved; what never returns, and what only calls that; a thunk and a tail call. Of programs linked to libc, the stubs of their
imports by the names of what they import, and that a call of `abort` doesn't come back. -/

namespace Bap.Tests.Partition

open Bap Bap.Analysis.Partition

/-- The targets of the partition program, with how many tables each has, of the switches that its compiler makes a table of. -/
private def targets : List (String × Nat) :=
  [("x86_64", 2), ("i686", 2), ("aarch64", 1), ("riscv64", 2), ("arm", 2), ("thumb", 2), ("mips", 2), ("mipsel", 2),
    ("mips64el", 2), ("powerpc", 0), ("powerpc64le", 0)]

/-- Those whose compiler makes `thunk` a jump to `target`, and `tail` end in one. -/
private def jumpingTails : List String := ["x86_64", "aarch64", "riscv64", "arm", "thumb"]

private def ofTarget (arch : String) (tables : Nat) : IO Unit := do
  let path := s!"testsuite/bin/{arch}-linux-none-partition"
  let project ← Project.Project.load path
  let some image := project.image | throw (IO.userError s!"{path} doesn't load")
  let some partition ← partition project | throw (IO.userError s!"{path} has no partition")
  let function (name : String) : IO Function := do
    let some symbol := image.symbols.find? (·.name == name) | throw (IO.userError s!"{path} has no {name}")
    let some found := partition.functionAt symbol.addr | throw (IO.userError s!"{path}: no function at {name}")
    pure found
  -- each function has all that its symbol has of the instructions
  for name in ["dense", "offset", "letters", "die", "fail", "target", "thunk", "tail", "_start"] do
    let some symbol := image.symbols.find? (·.name == name) | throw (IO.userError s!"{path} has no {name}")
    let found ← function name
    let missing := partition.disasm.instructions.filter fun insn =>
      symbol.addr ≤ insn.address && insn.address < symbol.addr + symbol.size && !found.instructions.contains insn.address
    assertEqual s!"{arch} {name} has all of its instructions" ([] : List Nat) (missing.map (·.address))
  assertEqual s!"{arch} has its jump tables" tables partition.tables.length
  assertTrue s!"{arch} bounds its tables" (partition.tables.all (·.bounded))
  assertEqual s!"{arch} has the cases of its tables" (if tables == 0 then [] else if tables == 1 then [10] else [8, 10])
    ((partition.tables.map (·.targets.length)).mergeSort (· ≤ ·))
  assertEqual s!"{arch} leaves no indirect jump unresolved" ([] : List Nat) partition.unresolved
  -- what never returns, and what only calls that, and what does
  for name in ["die", "fail", "_start"] do
    assertTrue s!"{arch} {name} doesn't return" !(← function name).returns
  for name in ["dense", "offset", "letters", "target", "thunk", "tail"] do
    assertTrue s!"{arch} {name} returns" (← function name).returns
  if jumpingTails.contains arch then
    let target ← function "target"
    assertEqual s!"{arch} thunk is a thunk of target" (some target.entry) (← function "thunk").thunkOf
    assertTrue s!"{arch} tail calls target in its tail" ((← function "tail").tailCalls.any (·.2 == target.entry))

/-- The stubs of the imports of a program linked to libc, and what doesn't return of them. -/
private def ofLibc (name : String) (imports : List String) (noReturn : List String) : IO Unit := do
  let project ← Project.Project.load s!"testsuite/bin/{name}"
  let some partition ← partition project | throw (IO.userError s!"{name} has no partition")
  let stubs := partition.functions.filterMap (·.importName)
  for expected in imports do
    assertTrue s!"{name} has a stub of {expected}" (stubs.contains expected)
  for expected in noReturn do
    let stub := partition.functions.find? (·.importName == some expected)
    assertEqual s!"{name}: {expected} doesn't return" (some false) (stub.map (·.returns))
    assertEqual s!"{name}: the stub of {expected} is named for it" (some s!"{expected}@plt") (stub.map (·.name))

def run : IO Unit := do
  for (arch, tables) in targets do
    ofTarget arch tables
  ofLibc "x86_64-linux-gnu-echo" ["putchar", "malloc", "strlen", "__libc_start_main"] ["__libc_start_main"]
  ofLibc "aarch64-linux-gnu-echo" ["putchar", "malloc", "abort", "__stack_chk_fail"] ["abort", "__stack_chk_fail", "__libc_start_main"]

end Bap.Tests.Partition
