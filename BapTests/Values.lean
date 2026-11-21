import BapTests.Support
import Bap.Analysis.Values

/-! What `Bap.Analysis.Values` finds of `testsuite/src/variables.c` of each target: of `locals`, an array of four words of its stack,
all of which a load at an index of a mask covers, and a word beside it; of the program, the array `table`, which `globals` writes
at an index, the array of constants `weights`, which it reads at one, and `sink`, each of all of its size. Of
`testsuite/src/hoisted.c`, the table of a switch in a loop, whose base a register holds from before the loop, which a partition
has of what value sets know. -/

namespace Bap.Tests.Values

open Bap Bap.Analysis

private def targets : List String :=
  ["x86_64", "i686", "aarch64", "riscv64", "arm", "mips", "mips64el", "powerpc", "powerpc64le"]

private def ofTarget (arch : String) : IO Unit := do
  let path := s!"testsuite/bin/{arch}-linux-none-variables"
  let project ← Project.Project.load path
  let some image := project.image | throw (IO.userError s!"{path} doesn't load")
  let some partition ← Partition.partition project | throw (IO.userError s!"{path} has no partition")
  let some frames := Frame.frames image partition | throw (IO.userError s!"{path} has no frames")
  let some variables := Values.ofPartition image partition frames | throw (IO.userError s!"{path} has no variables")
  let word := image.addrWidth / 8
  let symbol (name : String) : IO Image.Symbol := do
    let some found := image.symbols.find? (·.name == name) | throw (IO.userError s!"{path} has no {name}")
    pure found
  -- the stack of `locals`
  let locals ← symbol "locals"
  let some function := variables.functionAt locals.addr | throw (IO.userError s!"{path}: no variables of locals")
  let own := function.stack.filter (·.kind == .automatic)
  assertEqual s!"{arch} locals has an array of four words and a word" [word, 4 * word]
    ((own.map (·.size)).mergeSort (· ≤ ·))
  -- the globals
  let globals ← symbol "globals"
  for (name, size, written) in [("table", 8 * word, true), ("weights", 4 * word, false), ("sink", word, false)] do
    let found ← symbol name
    let some global := variables.globalAt found.addr | throw (IO.userError s!"{path}: no variable of {name}")
    assertEqual s!"{arch} {name} is a variable of all of it" ((found.addr : Int), size) (global.extent.start, global.extent.size)
    assertEqual s!"{arch} {name} is named" (some name) global.name
    assertTrue s!"{arch} globals reads {name}" (global.readers.contains globals.addr)
    assertEqual s!"{arch} globals writes {name}" written (global.writers.contains globals.addr)

/-- The table that a partition of what value sets know has, and one without them doesn't. -/
private def hoisted (arch : String) : IO Unit := do
  let path := s!"testsuite/bin/{arch}-linux-none-hoisted"
  let project ← Project.Project.load path
  let some alone ← Partition.partition project | throw (IO.userError s!"{path} has no partition")
  assertEqual s!"{arch} hoisted: a partition alone doesn't resolve the table" 1 alone.unresolved.length
  let some known ← Values.partition project | throw (IO.userError s!"{path} has no partition")
  assertEqual s!"{arch} hoisted: of what value sets know, it does" ([] : List Nat) known.unresolved
  assertEqual s!"{arch} hoisted has the cases of the table" [(true, 8)]
    (known.tables.map fun table => (table.bounded, table.targets.length))

/-- A stack pointer aligned isn't a number that has lost whose it is; a register that a way didn't write is what it held on entry
there. -/
private def units : IO Unit := do
  let sp := Values.Value.set (some "RSP") 64 (-8) (-8) 0
  assertEqual "an aligned stack pointer isn't known" Values.Value.top (Values.binary .and sp (.const 64 (2 ^ 64 - 16)))
  assertEqual "a register masked of its low bits is below the mask" (Values.Value.set none 64 0 3 1)
    (Values.binary .and (.set (some "RDI") 64 0 0 0) (.const 64 3))
  assertEqual "a constant of all the bits taken from an address of the stack is added, as `sub rax, -128` does"
    (Values.Value.set (some "RSP") 64 (-72) (-72) 0) (Values.binary .sub (.set (some "RSP") 64 (-200) (-200) 0) (.const 64 (2 ^ 64 - 128)))
  let left : Values.State := { env := ({} : Std.HashMap String Values.Value).insert "RBX" (.set (some "RBX") 64 8 8 0) }
  assertEqual "a register one way moved is of both, joined" (some (Values.Value.set (some "RBX") 64 0 8 8))
    ((left.join {}).env["RBX"]?)

def run : IO Unit := do
  units
  for arch in targets do
    ofTarget arch
  for arch in ["x86_64", "riscv64"] do
    hoisted arch

end Bap.Tests.Values
