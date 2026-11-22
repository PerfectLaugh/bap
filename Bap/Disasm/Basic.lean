import Bap.Image.Basic
import Bap.Bil.Syntax
import Bap.Graph.Basic
import Std.Data.HashSet

namespace Bap.Disasm

/-- How an instruction passes control on. -/
inductive Flow where
  | normal
  | jump
  | conditionalJump
  | indirectJump
  | call
  | ret
  | barrier
  deriving DecidableEq, Repr

/-- A decoded instruction: where it is, how big, its text, how it passes control on and where to if that is known, and its BIL. -/
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

/-- Where control may go after it, of what is known. -/
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

mutual
  /-- Whether a statement can end in any other way than running off its end. -/
  private def stmtLeaves : Bil.Stmt → Bool
    | .move .. => false
    | .ifElse _ yes no => programLeaves yes || programLeaves no
    | .while _ body => programLeaves body
    | _ => true

  private def programLeaves : Bil.Program → Bool
    | [] => false
    | stmt :: rest => stmtLeaves stmt || programLeaves rest
end

/-- What says whether a loop of `asLoop` has a round to go. -/
def repeats : Bap.Var := ⟨"_repeats", .imm 1, 0, false⟩

/-- The program of an instruction at `address`, before the one at `next`, that repeats by going back to itself, as one loop: see
`asLoop`. Any other program is itself. -/
def loopOf (address next : Nat) (program : Bil.Program) : Bil.Program :=
  match program with
  | .ifElse done [.jmp (.int exit)] [] :: rest =>
    match rest.getLast? with
    | some (.ifElse again [.jmp (.int self)] []) =>
      let round := rest.dropLast
      if exit.toNat != next || self.toNat != address || programLeaves round then program
      else
        let more : Bil.Exp := match done with
          | .bin .eq left right => .bin .neq left right
          | done => .un .not done
        -- A round that goes on whenever there is more to do is the body of a loop of that condition.
        if again = more then [.while more round]
        else [.move repeats (.int 1#1), .while (.bin .and (.var repeats) more) (round ++ [.move repeats again])]
    | _ => program
  | _ => program

/-- An instruction that repeats by going back to itself, as one loop. A repeated string instruction of x86 is lifted as one round of
it: nothing if `done` holds, which goes to the next instruction; else what a round does, and a jump to the instruction itself if `again`
holds after that. That is what runs, so that what interrupts it, as a fault does, finds the rounds that completed, as of the processor,
and no instruction is a loop of as many rounds as its count. What reads a function an instruction after the other has no edge from an
instruction to itself: for it, this is the loop of the rounds, which leaves the state that the rounds leave when the next instruction
runs. Any other instruction is itself. -/
def asLoop (insn : Insn) : Insn := { insn with bil := loopOf insn.address insn.next insn.bil }

end Insn

/-- What decodes the instructions of a target, one at a time, with what it says of delay slots. -/
structure Disassembler where
  name : String
  decode : Nat → ByteArray → IO (Except String Insn)
  /-- The next instruction runs before this one transfers control, although control doesn't fall
  through to it, as in the delay slot of a MIPS `J`. -/
  hasDelaySlot : Insn → Bool := fun _ => false
  /-- Of a delayed conditional branch: the slot only runs if the branch is taken, as in a MIPS `BEQL`. -/
  annulsSlot : Insn → Bool := fun _ => false
  /-- The size of what decodes at an address, without lifting it, if it does. A linear sweep goes on past an instruction
  that it can't lift by it. -/
  sizeAt : Nat → ByteArray → IO (Option Nat) := fun _ _ => pure none

/-- The addresses of the instructions that have a delay slot. -/
def Disassembler.delayed (disassembler : Disassembler) (instructions : List Insn) : List Nat :=
  (instructions.filter disassembler.hasDelaySlot).map Insn.address

/-- What decoding from an entry found: its instructions, the edges between them, and what couldn't be decoded. -/
structure Disasm where
  entry : Nat
  instructions : List Insn := []
  edges : List (Nat × Nat) := []
  errors : List String := []
  /-- The addresses of the instructions with a delay slot: the one after each runs before control goes where it sends it. -/
  delayed : List Nat := []

/-- Instructions that run one after the other, from one that is a target or follows a branch. -/
structure Block where
  start : Nat
  instructions : List Insn
  deriving Repr

/-- The instructions, by address. -/
def sortedInstructions (disasm : Disasm) : List Insn :=
  disasm.instructions.mergeSort fun left right => left.address ≤ right.address

/-- Of instructions by address, those that don't start where the one before ends, as after one that didn't decode. -/
def gapStarts (instructions : List Insn) : List Nat :=
  (instructions.zip instructions.tail).filterMap fun (before, insn) => if before.next != insn.address then some insn.address else none

/-- Where what runs in a line with an instruction ends: after it, or after its delay slot if it has one, which is of its size. -/
def Disasm.resumes (disasm : Disasm) (insn : Insn) : Nat :=
  if disasm.delayed.contains insn.address then insn.next + insn.size else insn.next

/-- The addresses where a block has to start: what control goes to otherwise than by falling through, and an instruction that the one
before doesn't fall through to, which of a branch with a delay slot is the one after the slot: the slot ends the block of its branch. -/
def Disasm.leaders (disasm : Disasm) (instructions : List Insn) : List Nat :=
  let delayed : Std.HashSet Nat := Std.HashSet.ofList disasm.delayed
  disasm.entry :: (instructions.flatMap fun insn =>
    match insn.flow with
    | .normal => insn.target.toList
    | _ => (if delayed.contains insn.address then insn.next + insn.size else insn.next) :: insn.target.toList) ++ gapStarts instructions

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

/-- The instructions as blocks. -/
def Disasm.blocks (disasm : Disasm) : List Block :=
  let instructions := sortedInstructions disasm
  let leaders := (disasm.leaders instructions).foldl (init := ({} : Std.HashSet Nat)) fun set address => set.insert address
  (buildBlocks leaders [] [] instructions).reverse

/-- The instructions and errors, as text. -/
def Disasm.render (disasm : Disasm) : String :=
  let lines := (sortedInstructions disasm).map fun insn =>
    s!"{insn.address}: {insn.asm}"
  let errors := disasm.errors.map fun error => s!"error: {error}"
  String.intercalate "\n" (lines ++ errors)

end Bap.Disasm
