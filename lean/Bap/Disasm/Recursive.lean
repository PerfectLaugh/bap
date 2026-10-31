import Bap.Disasm.Basic
import Std.Data.HashSet
import Std.Data.HashMap

namespace Bap.Disasm.Recursive

/-- The error of a scan that stopped with reachable addresses left to decode. -/
def outOfFuel : String := "recursive disassembly ran out of fuel with addresses left to decode"

/-- The instructions with one more, unless an instruction of that address is already listed. -/
def addInsn (insn : Insn) (instructions : List Insn) : List Insn :=
  if instructions.any (·.address == insn.address) then instructions else instructions ++ [insn]

/-- What runs after the instruction and its delay slot if the branch is not taken. Slots have the size of a branch. -/
def pastSlot (insn : Insn) : Nat := insn.next + insn.size

/-- Whether the instruction is a conditional branch with a delay slot, so that it can continue past the slot. -/
def isDelayedConditional (disassembler : Disassembler) (insn : Insn) : Bool :=
  disassembler.hasDelaySlot insn && insn.flow == .conditionalJump

/-- Whether the instruction is a call that annuls its slot if it is not taken, as a MIPS `BLTZALL`. A call goes on
through its slot, which is what it falls through to, and this one can also skip it. -/
def isAnnulledCall (disassembler : Disassembler) (insn : Insn) : Bool :=
  !disassembler.hasDelaySlot insn && disassembler.annulsSlot insn && insn.flow == .call

/-- Where control goes on from an instruction: a delayed conditional branch does not continue at its slot, but after it. -/
def flowAddresses (disassembler : Disassembler) (insn : Insn) : List Nat :=
  if isDelayedConditional disassembler insn then pastSlot insn :: insn.target.toList
  else if isAnnulledCall disassembler insn then [insn.next, pastSlot insn]
  else insn.successors

/-- The subroutine a direct call starts. It is no edge of the flow of its caller, which goes on after the call. -/
def callTarget (insn : Insn) : List Nat :=
  if insn.flow == .call then insn.target.toList else []

/-- The calls of an instruction. -/
def callEdges (insn : Insn) : List (Nat × Nat) := (callTarget insn).map (insn.address, ·)

/-- Where a scan goes on from an instruction: where control goes on, and the subroutine it calls. -/
def nextAddresses (disassembler : Disassembler) (insn : Insn) : List Nat :=
  flowAddresses disassembler insn ++ callTarget insn

/-- The edges of an instruction. A delayed transfer goes through its slot, so the slot is followed by the successors of
the branch and not by its own fall-through. A conditional branch runs its slot either way and decides after it, unless
it annuls the slot: then a branch that is not taken skips the slot, and only the taken one goes through it. -/
def flowEdges (disassembler : Disassembler) (insn : Insn) : List (Nat × Nat) :=
  if disassembler.hasDelaySlot insn then
    if isDelayedConditional disassembler insn then
      if disassembler.annulsSlot insn then
        (insn.address, insn.next) :: (insn.address, pastSlot insn) :: insn.target.toList.map (insn.next, ·)
      else
        (insn.address, insn.next) :: (insn.next, pastSlot insn) :: insn.target.toList.map (insn.next, ·)
    else
      (insn.address, insn.next) :: insn.successors.map (insn.next, ·)
  else if isAnnulledCall disassembler insn then
    [(insn.address, insn.next), (insn.address, pastSlot insn)]
  else
    insn.successors.map (insn.address, ·)

/-- The decoder of code in several regions: an address decodes in the region it lies in, and nowhere else. What else
the regions do is what `base` does. -/
def _root_.Bap.Disasm.Disassembler.ofRegions (base : Disassembler) (regions : List (Image.MemRegion × Disassembler)) : Disassembler :=
  { base with
    decode := fun address _ =>
      match regions.find? (·.1.contains address) with
      | some (region, disassembler) => disassembler.decode address region.data
      | none => pure (.error s!"{address} is not in code") }

/-- What a scan has found so far, with the addresses of the instructions as a set. -/
structure ScanState where
  visited : Std.HashSet Nat := {}
  addresses : Std.HashSet Nat := {}
  instructions : Array Insn := #[]
  edges : Array (Nat × Nat) := #[]
  errors : Array String := #[]

namespace ScanState

/-- `addInsn` on the array. -/
def add (state : ScanState) (insn : Insn) : ScanState :=
  if state.addresses.contains insn.address then state
  else { state with addresses := state.addresses.insert insn.address, instructions := state.instructions.push insn }

def error (state : ScanState) (message : String) : ScanState := { state with errors := state.errors.push message }

def visit (state : ScanState) (address : Nat) : ScanState := { state with visited := state.visited.insert address }

end ScanState

/-- Decodes the delay slot of a branch: the slot is listed but its own successors are not followed.
If something else reaches the slot address, the scan visits it as usual. -/
private def decodeSlot (disassembler : Disassembler) (data : ByteArray) (slot : Nat) (state : ScanState) : IO ScanState := do
  match ← disassembler.decode slot data with
  | .error error => pure (state.error error)
  | .ok insn =>
    if insn.address != slot || insn.size = 0 then
      pure (state.error "decoder returned an inconsistent instruction")
    else
      pure (state.add insn)

/-- Fuel counts decoded addresses only: popping an address that was already visited is free. -/
private def scanAux (disassembler : Disassembler) (data : ByteArray) : Nat → List Nat → ScanState → IO ScanState
  | 0, work, state =>
    if work.all state.visited.contains then
      pure state
    else
      pure (state.error outOfFuel)
  | fuel + 1, work, state =>
    match work.dropWhile state.visited.contains with
    | [] => pure state
    | address :: work => do
      match ← disassembler.decode address data with
      | .error error =>
        scanAux disassembler data fuel work ((state.visit address).error error)
      | .ok insn =>
        if insn.address != address || insn.size = 0 then
          scanAux disassembler data fuel work
            ((state.visit address).error "decoder returned an inconsistent instruction")
        else
          let added := (state.visit address).add insn
          let state := { added with edges := added.edges ++ (flowEdges disassembler insn).toArray }
          let work := nextAddresses disassembler insn ++ work
          if disassembler.hasDelaySlot insn then
            scanAux disassembler data fuel work (← decodeSlot disassembler data insn.next state)
          else
            scanAux disassembler data fuel work state

/-- Scans from all the `roots`, and what is reachable from them, in `bytes` bytes of code. Every instruction starts at
one of them and adds at most three addresses, some possibly out of range, so a decoder that fails out of range visits
no more than `4 * bytes + roots.length + 1` addresses. -/
def scanRoots (disassembler : Disassembler) (data : ByteArray) (bytes entry : Nat) (roots : List Nat) : IO Disasm := do
  let state ← scanAux disassembler data (4 * bytes + roots.length + 1) roots {}
  pure { entry := entry, instructions := state.instructions.toList, edges := state.edges.toList, errors := state.errors.toList }

/-- The scan of the code in `data` from one root. -/
def scan (disassembler : Disassembler) (data : ByteArray) (entry : Nat) : IO Disasm :=
  scanRoots disassembler data data.size entry [entry]

/-- A walk over the addresses of a linear sweep, with the sizes of the first `seen` instructions of the scan. -/
structure Walk where
  sizes : Std.HashMap Nat Nat := {}
  seen : Nat := 0

namespace Walk

/-- The sizes of all the instructions of a scan. -/
def sync (walk : Walk) (state : ScanState) : Walk :=
  (state.instructions.extract walk.seen state.instructions.size).foldl (init := { walk with seen := state.instructions.size })
    fun walk insn => { walk with sizes := walk.sizes.insert insn.address insn.size }

end Walk

/-- The next multiple of `alignment` after `address`. -/
def nextAligned (alignment address : Nat) : Nat :=
  (address / alignment + 1) * alignment

/-- Goes linearly through the addresses from `address` up to `limit`. What the scan already found it steps over, and it
scans from what it hasn't. Where that fails, it tries again at the next multiple of `alignment`. -/
private def sweepRange (disassembler : Disassembler) (data : ByteArray) (fuel alignment limit : Nat) :
    Nat → Nat → Walk → ScanState → IO (Walk × ScanState)
  | 0, _, walk, state => pure (walk, state)
  | steps + 1, address, walk, state =>
    if limit ≤ address then pure (walk, state)
    else
      let walk := walk.sync state
      match walk.sizes[address]? with
      | some size => sweepRange disassembler data fuel alignment limit steps (address + size) walk state
      | none =>
        if state.visited.contains address then
          sweepRange disassembler data fuel alignment limit steps (nextAligned alignment address) walk state
        else do
          let state ← scanAux disassembler data fuel [address] state
          sweepRange disassembler data fuel alignment limit steps address walk state

/-- Scans from all the `roots`, and then sweeps the `ranges` linearly. What a sweep can't decode isn't an error, since
it needn't be code. -/
def scanRegions (disassembler : Disassembler) (bytes entry : Nat) (roots : List Nat) (alignment : Nat)
    (ranges : List (Nat × Nat)) : IO Disasm := do
  let data := ByteArray.empty
  let fuel := 4 * bytes + roots.length + 1
  let state ← scanAux disassembler data fuel roots {}
  let errors := state.errors
  let (_, state) ← ranges.foldlM (init := (({} : Walk), state)) fun (walk, state) range =>
    sweepRange disassembler data fuel alignment range.2 (2 * (range.2 - range.1) + 1) range.1 walk state
  pure { entry := entry, instructions := state.instructions.toList, edges := state.edges.toList, errors := errors.toList }

end Bap.Disasm.Recursive
