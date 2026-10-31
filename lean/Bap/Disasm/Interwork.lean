import Bap.Disasm.Basic
import Std.Data.HashSet

/-! The scan of code in ARM and Thumb states. Instructions of both are at even addresses, so a number says both where an
instruction is and in which state it is decoded, the way the architecture says it to `BX`: bit 0 set is Thumb. The scan
of `Recursive` goes over such keys as over addresses, and it finds each pair of an address and a state once. -/

namespace Bap.Disasm.Interwork

/-- The key of an instruction at an address in a state. -/
def key (address : Nat) (thumb : Bool) : Nat := address - address % 2 + if thumb then 1 else 0

/-- The address of a key. -/
def addressOf (key : Nat) : Nat := key - key % 2

/-- The state of a key. -/
def isThumb (key : Nat) : Bool := key % 2 == 1

/-- What is at some addresses, by the mapping symbols of the ARM ELF ABI: `$a`, `$t` and `$d`. -/
inductive Code where
  | arm
  | thumb
  | data
  deriving DecidableEq, Repr

/-- `$a`, `$t` or `$d`, each possibly with a dot and more after it. -/
def mappingKind (name : String) : Option Code :=
  let code := if name.startsWith "$a" then some Code.arm
    else if name.startsWith "$t" then some Code.thumb
    else if name.startsWith "$d" then some Code.data
    else none
  if name.length == 2 || (name.drop 2).startsWith "." then code else none

/-- The addresses from `start` up to `stop` hold `kind`. -/
structure Run where
  start : Nat
  stop : Nat
  kind : Code
  deriving DecidableEq, Repr

/-- The kind of the run that an address is in, of runs in the order of their addresses. -/
def runAt (runs : Array Run) (address : Nat) : Option Code :=
  let rec go : Nat → Nat → Nat → Option Code
    | 0, _, _ => none
    | fuel + 1, low, high =>
      if low ≥ high then none
      else
        let middle := (low + high) / 2
        match runs[middle]? with
        | none => none
        | some run =>
          if address < run.start then go fuel low middle
          else if run.stop ≤ address then go fuel (middle + 1) high
          else some run.kind
  go (runs.size + 1) 0 runs.size

/-- The instruction that ends an instruction or an IT block. -/
private def lastAssembly (insn : Insn) : String :=
  (insn.asm.splitOn "; ").getLast?.getD insn.asm

/-- Whether a direct branch goes to the other state: `BLX` of an immediate always does, and `BX` of the pc goes to bit 0 of
the pc, which is clear, so it does from Thumb state. -/
def switchesState (thumb : Bool) (insn : Insn) : Bool :=
  insn.target.isSome && ((lastAssembly insn).startsWith "blx" || (thumb && lastAssembly insn == "bx pc"))

/-- `BX` of the pc jumps to a constant, the word of the pc, four bytes ahead in Thumb state and eight in ARM state, as Thumb
stubs get to the ARM code after them. It isn't a return or an indirect jump, whatever the flags of its encoding are. -/
def constantBx (thumb : Bool) (insn : Insn) : Insn :=
  if insn.asm == "bx pc" then
    { insn with flow := .jump, target := some ((insn.address + if thumb then 4 else 8) / 4 * 4) }
  else insn

/-- The key of the target of a direct branch of an instruction in a state. -/
def targetKey (thumb switches : Bool) (target : Nat) : Nat :=
  key target (thumb != switches)

/-- An instruction of the scan, which has the key of its address and those of its target. Its size is even, so the key of
what follows it has its state too. -/
def rekey (thumb : Bool) (insn : Insn) : Insn :=
  let insn := constantBx thumb insn
  { insn with
    address := key insn.address thumb
    target := insn.target.map (targetKey thumb (switchesState thumb insn)) }

/-- The instruction as the rest of the program knows it, with addresses. -/
def unkeyInsn (insn : Insn) : Insn :=
  { insn with address := addressOf insn.address, target := insn.target.map addressOf }

/-- The instructions with addresses, each address once: the first found of those that are of both states. -/
def unkeyAll (instructions : List Insn) : List Insn :=
  (instructions.foldl (init := (({} : Std.HashSet Nat), ([] : List Insn))) fun state insn =>
    let insn := unkeyInsn insn
    if state.1.contains insn.address then state else (state.1.insert insn.address, insn :: state.2)).2.reverse

/-- What a scan of keys found, with addresses. -/
def unkey (disasm : Disasm) : Disasm :=
  { disasm with
    instructions := unkeyAll disasm.instructions
    edges := disasm.edges.map fun edge => (addressOf edge.1, addressOf edge.2) }

/-- The decoder of keys, from those of the two states: the mapping symbols have the last word on what an address holds,
and an A32 instruction is at a multiple of four. -/
def decoder (runs : Array Run) (arm thumb : Disassembler) : Disassembler :=
  { arm with
    decode := fun code data => do
      let address := addressOf code
      match runAt runs address, isThumb code with
      | some .data, _ => pure (.error s!"{address} is data")
      | some .arm, true => pure (.error s!"{address} is not in Thumb state")
      | some .thumb, false => pure (.error s!"{address} is not in ARM state")
      | _, true => return (rekey true <$> (← thumb.decode address data))
      | _, false =>
        if address % 4 != 0 then pure (.error s!"{address} is not aligned for ARM state")
        else return (rekey false <$> (← arm.decode address data))
    sizeAt := fun code data =>
      if isThumb code then thumb.sizeAt (addressOf code) data else arm.sizeAt code data }

end Bap.Disasm.Interwork
