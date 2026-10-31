import Bap.Image.Basic
import Bap.Bil.Syntax
import Bap.Graph.Basic
import Std.Data.HashSet

namespace Bap.Disasm

inductive Flow where
  | normal
  | jump
  | conditionalJump
  | indirectJump
  | call
  | ret
  | barrier
  deriving DecidableEq, Repr

structure Insn where
  address : Nat
  size : Nat
  asm : String
  flow : Flow := .normal
  target : Option Nat := none
  bil : Bil.Program := []
  deriving Repr

namespace Insn

@[simp] def next (insn : Insn) : Nat := insn.address + insn.size

def successors (insn : Insn) : List Nat :=
  match insn.flow with
  | .normal | .call => [insn.next]
  | .jump => insn.target.toList
  | .conditionalJump => insn.next :: insn.target.toList
  | .indirectJump | .ret | .barrier => []

/-- Control can continue at the next instruction. -/
def fallsThrough (insn : Insn) : Bool :=
  match insn.flow with
  | .normal | .call | .conditionalJump => true
  | .jump | .indirectJump | .ret | .barrier => false

end Insn

structure Disassembler where
  name : String
  decode : Nat → ByteArray → IO (Except String Insn)
  /-- The next instruction runs before this one transfers control, although control doesn't fall
  through to it, as in the delay slot of a MIPS `J`. -/
  hasDelaySlot : Insn → Bool := fun _ => false
  /-- Of a delayed conditional branch: the slot only runs if the branch is taken, as in a MIPS `BEQL`. -/
  annulsSlot : Insn → Bool := fun _ => false

structure Disasm where
  entry : Nat
  instructions : List Insn := []
  edges : List (Nat × Nat) := []
  errors : List String := []

structure Block where
  start : Nat
  instructions : List Insn
  deriving Repr

def sortedInstructions (disasm : Disasm) : List Insn :=
  disasm.instructions.mergeSort fun left right => left.address ≤ right.address

/-- The addresses where a block has to start. -/
def Disasm.leaders (disasm : Disasm) (instructions : List Insn) : List Nat :=
  disasm.entry :: instructions.flatMap fun insn =>
    match insn.flow with
    | .normal => insn.target.toList
    | _ => insn.next :: insn.target.toList

/-- The blocks of the instructions, and the current block, both from the last one. -/
private def buildBlocks (leaders : Std.HashSet Nat) (current : List Insn) (blocks : List Block) : List Insn → List Block
  | [] =>
    match current.getLast? with
    | none => blocks
    | some head => ⟨head.address, current.reverse⟩ :: blocks
  | insn :: rest =>
    if leaders.contains insn.address then
      match current.getLast? with
      | none => buildBlocks leaders [insn] blocks rest
      | some head => buildBlocks leaders [insn] (⟨head.address, current.reverse⟩ :: blocks) rest
    else
      buildBlocks leaders (insn :: current) blocks rest

def Disasm.blocks (disasm : Disasm) : List Block :=
  let instructions := sortedInstructions disasm
  let leaders := (disasm.leaders instructions).foldl (init := ({} : Std.HashSet Nat)) fun set address => set.insert address
  (buildBlocks leaders [] [] instructions).reverse

def Disasm.render (disasm : Disasm) : String :=
  let lines := (sortedInstructions disasm).map fun insn =>
    s!"{insn.address}: {insn.asm}"
  let errors := disasm.errors.map fun error => s!"error: {error}"
  String.intercalate "\n" (lines ++ errors)

end Bap.Disasm
