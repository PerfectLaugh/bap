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

/-- The accesses and the states of hand-made instructions of a target, one after the other from 0, each of `size` bytes. -/
private def analyzed (arch : Image.Arch) (width size : Nat) (instructions : List Disasm.Insn) :
    IO (Array Values.Access × Std.HashMap Nat Values.State) := do
  let some convention := ABI.convention arch width | throw (IO.userError "no convention")
  let frame : Frame.Context := { arch, width, convention, calleeSaved := Frame.calleeSaved arch width
                                 volatile := Frame.volatileOf arch convention }
  let context : Values.Context := { frame, stackPointer := convention.stackPointer, deltas := {}
                                    machine := { stackPointer := convention.stackPointer.name.str } }
  let addresses := instructions.map (·.address)
  let program : Frame.Program :=
    { instructions := instructions.foldl (init := {}) fun table insn => table.insert insn.address insn
      successors := addresses.foldl (init := {}) fun table address => table.insert address [address + size] }
  let function : Partition.Function := { entry := 0, name := "f", instructions := addresses, returns := true }
  pure (Values.analyze context program function)

/-- What a call of MIPS does, it does after its delay slot: `int x; f(&x); return x;` with the address given in the slot reads
what `f` may have written, and the register of the argument isn't the address after. -/
private def delaySlots : IO Unit := do
  let r (name : String) : Bap.Var := ⟨name, .imm 32, 0, false⟩
  let mem : Bap.Var := ⟨"mem", .mem 32 8, 0, false⟩
  let c (value : Nat) : Bil.Exp := .int (BitVec.ofNat 32 value)
  let instructions : List Disasm.Insn :=
    [{ address := 0, size := 4, asm := "addiu $sp, $sp, -32", bil := [.move (r "R29") (.bin .sub (.var (r "R29")) (c 32))] },
      { address := 4, size := 4, asm := "jal f", flow := .call, target := some 0x100
        bil := [.move (r "R31") (c 12), .jmp (c 0x100)] },
      { address := 8, size := 4, asm := "addiu $a0, $sp, 24", bil := [.move (r "R4") (.bin .add (.var (r "R29")) (c 24))] },
      { address := 12, size := 4, asm := "lw $v0, 24($sp)"
        bil := [.move (r "R2") (.load (.var mem) (.bin .add (.var (r "R29")) (c 24)) .big 4)] },
      { address := 16, size := 4, asm := "jr $ra", flow := .ret, bil := [.jmp (.var (r "R31"))] }]
  let (accesses, states) ← analyzed .mips 32 4 instructions
  assertEqual "mips: a load of what a call was given the address of in its delay slot is of what may be written" [true]
    ((accesses.toList.filter (·.insn == 12)).map (·.initialized))
  assertEqual "mips: a call clobbers what its delay slot sets" (some Values.Value.top) ((states.getD 12 {}).env["R4"]?)

/-- An address of the stack in a register that isn't of the arguments is given too: x8 of AArch64, where what is called puts a
result too big for registers, and ecx of i686, as `fastcall` passes. -/
private def givenRegisters : IO Unit := do
  for (arch, width, stack, register, link) in
      [(Image.Arch.aarch64, 64, "SP", "X8", some "X30"), (.aarch64, 64, "SP", "X0", some "X30"), (.x86, 32, "ESP", "ECX", none)] do
    let r (name : String) : Bap.Var := ⟨name, .imm width, 0, false⟩
    let mem : Bap.Var := ⟨"mem", .mem width 8, 0, false⟩
    let c (value : Nat) : Bil.Exp := .int (BitVec.ofNat width value)
    let instructions : List Disasm.Insn :=
      [{ address := 0, size := 1, asm := "sub sp, sp, #0x40", bil := [.move (r stack) (.bin .sub (.var (r stack)) (c 0x40))] },
        { address := 1, size := 1, asm := "add x8, sp, #0x10", bil := [.move (r register) (.bin .add (.var (r stack)) (c 0x10))] },
        { address := 2, size := 1, asm := "bl f", flow := .call, target := some 0x100
          bil := (link.map fun link => Bil.Stmt.move (r link) (c 3)).toList ++ [.jmp (c 0x100)] },
        { address := 3, size := 1, asm := "ldr x0, [sp, #0x10]"
          bil := [.move (r register) (.load (.var mem) (.bin .add (.var (r stack)) (c 0x10)) .little (width / 8))] },
        { address := 4, size := 1, asm := "ret", flow := .ret, bil := [.jmp (c 0)] }]
    let (accesses, _) ← analyzed arch width 1 instructions
    assertEqual s!"an address of the stack in {register} is given to a call, which may write there" [true]
      ((accesses.toList.filter (·.insn == 3)).map (·.initialized))

/-- What a register that isn't the stack pointer points to, a call may write, and so may a store through another pointer:
`*p = i & 15; g(); arr[*p] = 1` doesn't store within sixteen of `arr`, as far as is known. -/
private def otherSlots : IO Unit := do
  let r (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩
  let mem : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
  let c (value : Nat) : Bil.Exp := .int (BitVec.ofNat 64 value)
  let store (address value : Bil.Exp) (size : Nat := 8) : Bil.Stmt := .move mem (.store (.var mem) address value .little size)
  let between : List (String × Disasm.Insn) :=
    [("a call", { address := 3, size := 1, asm := "call g", flow := .call, target := some 0x100
                  bil := [.move (r "RSP") (.bin .sub (.var (r "RSP")) (c 8)), store (.var (r "RSP")) (c 4), .jmp (c 0x100)] }),
      ("a store through another pointer", { address := 3, size := 1, asm := "mov qword [rdx], 100", bil := [store (.var (r "RDX")) (c 100)] }),
      ("a store at a number", { address := 3, size := 1, asm := "mov qword [0x5000], 100", bil := [store (c 0x5000) (c 100)] }),
      ("a call of the system", { address := 3, size := 1, asm := "syscall", bil := [.special "syscall"] })]
  let kept : List (String × Disasm.Insn) :=
    [("a store to the stack", { address := 3, size := 1, asm := "mov qword [rsp-16], 100"
                                bil := [store (.bin .sub (.var (r "RSP")) (c 16)) (c 100)] }),
      ("a store beside it", { address := 3, size := 1, asm := "mov qword [rbx+8], 100", bil := [store (.bin .add (.var (r "RBX")) (c 8)) (c 100)] })]
  for ((name, insn), stays) in between.map (·, false) ++ kept.map (·, true) do
    let instructions : List Disasm.Insn :=
      [{ address := 0, size := 1, asm := "mov rbx, rdi", bil := [.move (r "RBX") (.var (r "RDI"))] },
        { address := 1, size := 1, asm := "and rsi, 15", bil := [.move (r "RSI") (.bin .and (.var (r "RSI")) (c 15))] },
        { address := 2, size := 1, asm := "mov [rbx], rsi", bil := [store (.var (r "RBX")) (.var (r "RSI"))] },
        insn,
        { address := 4, size := 1, asm := "mov rax, [rbx]", bil := [.move (r "RAX") (.load (.var mem) (.var (r "RBX")) .little 8)] },
        { address := 5, size := 1, asm := "mov dword [0x4000+rax*4], 1"
          bil := [store (.bin .add (c 0x4000) (.bin .mul (.var (r "RAX")) (c 4))) (.int (BitVec.ofNat 32 1)) 4] },
        { address := 6, size := 1, asm := "ret", flow := .ret, bil := [.jmp (c 0)] }]
    let (accesses, _) ← analyzed .x86_64 64 1 instructions
    let stored := (accesses.toList.filter fun access => access.insn == 5 && access.write).map (·.address)
    if stays then
      assertEqual s!"what a pointer points to is as it was stored after {name}" [Values.Value.set none 64 0x4000 0x403c 4] stored
    else
      assertEqual s!"what a pointer points to isn't known after {name}" [Values.Value.top] stored

/-- The tests of what the review 30 found, which need no program. -/
def review30 : IO Unit := do
  delaySlots
  givenRegisters
  otherSlots

def run : IO Unit := do
  units
  review30
  for arch in targets do
    ofTarget arch
  for arch in ["x86_64", "riscv64"] do
    hoisted arch

end Bap.Tests.Values
