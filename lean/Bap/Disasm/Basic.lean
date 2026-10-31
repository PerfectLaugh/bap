import Bap.Image.Basic
import Bap.Bil.Syntax
import Bap.Graph.Basic

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

structure Disasm where
  entry : Nat
  instructions : List Insn := []
  edges : List (Nat × Nat) := []
  errors : List String := []

structure Block where
  start : Nat
  instructions : List Insn
  deriving Repr

private def insertInsn (insn : Insn) : List Insn → List Insn
  | [] => [insn]
  | head :: tail =>
    if insn.address ≤ head.address then insn :: head :: tail else head :: insertInsn insn tail

def sortedInstructions (disasm : Disasm) : List Insn :=
  disasm.instructions.foldl (fun result insn => insertInsn insn result) []

def Disasm.blocks (disasm : Disasm) : List Block :=
  let instructions := sortedInstructions disasm
  let leaders := disasm.entry :: instructions.flatMap fun insn =>
    match insn.flow with
    | .normal => insn.target.toList
    | _ => insn.next :: insn.target.toList
  let rec build (current : List Insn) (blocks : List Block) : List Insn → List Block
    | [] =>
      match current with
      | [] => blocks
      | head :: _ => blocks ++ [⟨head.address, current⟩]
    | insn :: rest =>
      if insn.address ∈ leaders && !current.isEmpty then
        match current with
        | [] => build [insn] blocks rest
        | head :: _ => build [insn] (blocks ++ [⟨head.address, current⟩]) rest
      else
        build (current ++ [insn]) blocks rest
  build [] [] instructions

def Disasm.render (disasm : Disasm) : String :=
  let lines := (sortedInstructions disasm).map fun insn =>
    s!"{insn.address}: {insn.asm}"
  let errors := disasm.errors.map fun error => s!"error: {error}"
  String.intercalate "\n" (lines ++ errors)

end Bap.Disasm
