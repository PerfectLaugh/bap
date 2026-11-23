import BapTests.Support
import Bap.Analysis.Partition
import Bap.Image.Raw

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
  for name in ["dense", "offset", "letters", "die", "fail", "target", "thunk", "tail", "chainUser", "_start"] do
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
  -- and what only calls in its tail what itself only does, with what calls that, all of it
  for name in ["dense", "offset", "letters", "target", "thunk", "tail", "chainLeaf", "chainMid", "chainTop", "chainUser"] do
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

/-- What a bit of a field of a condition register is, of what is beside it that isn't known: an `extract` of a `concat` of the part
it is of. -/
private def folds : IO Unit := do
  let unknown : Symbolic.Expr := .var "SO" 1
  let field : Symbolic.Expr := .concat (.concat (.const (BitVec.ofNat 1 1)) (.const (BitVec.ofNat 1 0))) unknown
  assertTrue "a bit of a concat beside what isn't known is a constant"
    (match simplify (.extract 2 2 field) with | .const value => value.toNat == 1 | _ => false)
  assertTrue "an extract of an extract is one"
    (match simplify (.extract 0 0 (.extract 2 1 field)) with | .const value => value.toNat == 0 | _ => false)

/-- A call of a condition goes on when the condition doesn't hold, whatever it calls: `cmp r0, #0; bleq abort; mov r0, #1; bx lr`
keeps the edge from the call to what follows it, which `bl abort` doesn't have. -/
private def conditionalCalls : IO Unit := do
  let r (name : String) (width : Nat := 32) : Bap.Var := ⟨name, .imm width, 0, false⟩
  let c (value : Nat) : Bil.Exp := .int (BitVec.ofNat 32 value)
  let call : Bil.Program := [.move (r "LR") (c 8), .jmp (c 0x100)]
  let instructions (asm : String) (code : Bil.Program) : List Disasm.Insn :=
    [{ address := 0, size := 4, asm := "cmp r0, #0", bil := [.move (r "ZF" 1) (.bin .eq (.var (r "R0")) (c 0))] },
      { address := 4, size := 4, asm, flow := .call, target := some 0x100, bil := code },
      { address := 8, size := 4, asm := "mov r0, #1", bil := [.move (r "R0") (c 1)] },
      { address := 12, size := 4, asm := "bx lr", flow := .indirectJump, bil := [.jmp (.var (r "LR"))] }]
  let edgesOf (instructions : List Disasm.Insn) : List (Nat × Nat) :=
    let disasm : Disasm.Disasm := { entry := 0, instructions, edges := [(0, 4), (4, 8), (8, 12)] }
    flowEdges .arm disasm (Graph.ofEdges instructions disasm.edges) [] (fun _ => false) (· == 0x100)
  assertEqual "a call of a condition of what doesn't return goes on" [(0, 4), (4, 8), (8, 12)]
    (edgesOf (instructions "bleq abort" [.ifElse (.var (r "ZF" 1)) call []]))
  assertEqual "a call of what doesn't return doesn't" [(0, 4), (8, 12)] (edgesOf (instructions "bl abort" call))
  -- as MIPS's `bgezal` links first, and jumps of its condition
  assertEqual "a call that links and then jumps of a condition goes on" [(0, 4), (4, 8), (8, 12)]
    (edgesOf (instructions "bgezal" [.move (r "LR") (c 8), .ifElse (.var (r "ZF" 1)) [.jmp (c 0x100)] []]))

/-- What leads to an indirect jump is walked within a budget, whatever it shares: 24 instructions that each make a register of
three of itself, `rax := rax + rax * rax`, make a target of 3^24 parts, of which nothing is walked whole. The targets that
`pathTargets` gives are of no more parts than a few instructions make of what `bounded` leaves, and the jump has no table. -/
private def sharedPaths : IO Unit := do
  let rax : Bap.Var := ⟨"RAX", .imm 64, 0, false⟩
  let mem : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
  let count := 24
  let ofBody (asm : String) (body : Bil.Program) : IO Unit := do
    let instructions : List Disasm.Insn :=
      ((List.range count).map fun index => { address := 0x1000 + 3 * index, size := 3, asm, bil := body }) ++
        [{ address := 0x1000 + 3 * count, size := 2, asm := "jmp rax", flow := .indirectJump, bil := [.jmp (.var rax)] }]
    let edges := (List.range count).map fun index => (0x1000 + 3 * index, 0x1000 + 3 * (index + 1))
    let graph := Graph.ofEdges instructions edges
    let path := pathTo graph (0x1000 + 3 * count)
    assertEqual s!"{asm}: the path to the jump has what leads to it" (count + 1) path.length
    let targets := pathTargets path
    assertTrue s!"{asm}: the target of a jump after instructions that share is of few parts"
      (!targets.isEmpty && targets.all fun (_, target) => walkable target (64 * maxWalk))
    let image := Image.Raw.load (ByteArray.mk (Array.replicate 256 0x90)) 0x1000 .little
    assertEqual s!"{asm}: and the jump has no table" none
      ((resolveJump image graph (0x1000 + 3 * count) (0x1000, 0x1100)).map (·.targets))
  let tripled : Bil.Exp := .bin .add (.var rax) (.bin .mul (.var rax) (.var rax))
  ofBody "imul rax, rax" [.move rax tripled]
  -- and stored where it says, which a read there compares the addresses of
  ofBody "mov [rax], rax" [.move rax tripled, .move mem (.store (.var mem) (.var rax) (.var rax) .little 8),
    .move rax (.bin .add (.var rax) (.load (.var mem) (.var rax) .little 8))]
  -- a target of more than `maxWalk` parts has no table
  let big : Symbolic.Expr := (List.range 13).foldl (init := .var "RAX#0" 64) fun expr _ => .app "bvadd" 64 [expr, expr]
  assertTrue "an expression of 2^14 parts is past the budget" (!walkable big && sizeOf maxWalk big == maxWalk + 1)
  assertEqual "and has no table" none ((tableTargets image0 big []).map (·.2.2))
where
  image0 : Image.Image := Image.Raw.load (ByteArray.mk (Array.replicate 256 0x90)) 0x1000 .little

/-- The tests of what the review 30 found, which need no program. -/
def review30 : IO Unit := do
  conditionalCalls
  sharedPaths

def run : IO Unit := do
  folds
  review30
  for (arch, tables) in targets do
    ofTarget arch tables
  ofLibc "x86_64-linux-gnu-echo" ["putchar", "malloc", "strlen", "__libc_start_main"] ["__libc_start_main"]
  ofLibc "aarch64-linux-gnu-echo" ["putchar", "malloc", "abort", "__stack_chk_fail"] ["abort", "__stack_chk_fail", "__libc_start_main"]

end Bap.Tests.Partition
