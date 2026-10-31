import Bap.Analysis.Xrefs
import Std.Data.HashMap
import Std.Data.HashSet

namespace Bap.Analysis.Slice

inductive Location where
  | reg (var : Bap.Var)
  /-- Bytes of every memory variable the sliced code mentions, for a criterion that names none. -/
  | mem (address size : Nat)
  /-- Bytes of one memory variable. -/
  | memOf (memory : Bap.Var) (address size : Nat)
  /-- Bytes of one memory variable at `offset` from the value of the register `base` where the location is live, the
  stack slots of a stack pointer or a frame pointer among them. It says the register too. -/
  | rel (memory base : Bap.Var) (offset : Int) (size : Nat)
  /-- All of one memory variable, which is what a read at an address that is not known needs. -/
  | whole (memory : Bap.Var)
  deriving DecidableEq, Repr

instance : Hashable Location where
  hash
    | .reg var => mixHash 1 (hash var)
    | .mem address size => mixHash 2 (mixHash (hash address) (hash size))
    | .memOf memory address size => mixHash 3 (mixHash (hash memory) (mixHash (hash address) (hash size)))
    | .rel memory base offset size => mixHash 4 (mixHash (hash memory) (mixHash (hash base) (mixHash (hash offset) (hash size))))
    | .whole memory => mixHash 5 (hash memory)

namespace Location

/-- Whether `size` bytes at offset `left` and `rightSize` bytes at offset `right` from one address never meet in the
address space of `memory`, around its end included. -/
def apart (memory : Bap.Var) (left leftSize right rightSize : Int) : Bool :=
  match memory.typ with
  | .mem width _ =>
    (left + leftSize ≤ right && right + rightSize - left ≤ (2 : Int) ^ width) ||
      (right + rightSize ≤ left && left + leftSize - right ≤ (2 : Int) ^ width)
  | _ => false

/-- Whether two locations may share a register or at least one byte. Locations from two registers may. -/
def overlaps : Location → Location → Bool
  | .reg left, .reg right => left == right
  | .mem left leftSize, .mem right rightSize
  | .mem left leftSize, .memOf _ right rightSize
  | .memOf _ left leftSize, .mem right rightSize =>
    left < right + rightSize && right < left + leftSize
  | .memOf leftMemory left leftSize, .memOf rightMemory right rightSize =>
    leftMemory == rightMemory && left < right + rightSize && right < left + leftSize
  | .mem _ _, .rel .. | .rel .., .mem _ _ | .mem _ _, .whole _ | .whole _, .mem _ _ => true
  | .memOf left _ _, .rel right .. | .rel left .., .memOf right _ _ | .memOf left _ _, .whole right
  | .whole left, .memOf right _ _ | .rel left .., .whole right | .whole left, .rel right ..
  | .whole left, .whole right => left == right
  | .rel leftMemory leftBase left leftSize, .rel rightMemory rightBase right rightSize =>
    leftMemory == rightMemory && (leftBase != rightBase || !apart leftMemory left leftSize right rightSize)
  | _, _ => false

/-- Whether a write can change what a live location says: what it may share, and a register that a location goes by. -/
def affects (write live : Location) : Bool :=
  write.overlaps live || match write, live with
    | .reg var, .rel _ base _ _ => var == base
    | _, _ => false

/-- Whether a write to `outer` overwrites every byte of `inner`. -/
def covers (outer inner : Location) : Bool :=
  outer.overlaps inner && match outer, inner with
    | .mem outerAddress outerSize, .mem innerAddress innerSize
    | .mem outerAddress outerSize, .memOf _ innerAddress innerSize
    | .memOf _ outerAddress outerSize, .mem innerAddress innerSize
    | .memOf _ outerAddress outerSize, .memOf _ innerAddress innerSize =>
      outerAddress ≤ innerAddress && innerAddress + innerSize ≤ outerAddress + outerSize
    | .rel _ outerBase outer outerSize, .rel _ innerBase inner innerSize =>
      outerBase == innerBase && outer ≤ inner && inner + innerSize ≤ outer + outerSize
    | .reg _, .reg _ => true
    | _, _ => false

/-- Whether this is a location of the memory variable `memory`. -/
def inMemory (memory : Bap.Var) : Location → Bool
  | .memOf other _ _ | .rel other .. | .whole other => other == memory
  | .mem _ _ => true
  | .reg _ => false

end Location

/-- What an instruction can touch. `writes` may be overwritten, and each of `wholesale` may change at
bytes that could not be determined: stored to at an unknown address, or assigned another memory. -/
private structure Info where
  writes : List Location := []
  wholesale : List Bap.Var := []
  uses : List Location := []
  dynamic : Bool := false
  always : Bool := false

/-- The constant address of a `size`-byte access. An access that wraps around the address space
is not one contiguous `Location`, and counts as dynamic. -/
private def constantRange (exp : Bil.Exp) (size : Nat) : Option Nat :=
  match Bil.evalExp [] exp with
  | .ok value =>
    match Bap.Value.asBits value with
    | .ok address => if address.2.toNat + size ≤ 2 ^ address.1 then some address.2.toNat else none
    | .error _ => none
  | .error _ => none

/-- The value of an expression that no variable changes. -/
private def closedBits (exp : Bil.Exp) : Option (Σ width, BitVec width) :=
  match Bil.evalExp [] exp with
  | .ok value => (Bap.Value.asBits value).toOption
  | .error _ => none

/-- The register an expression adds a constant to, the constant, and its width if it is known: the value of an address
as the lifters write it, with casts that do nothing and constants on either side. `none` for a width is the register
itself, as wide as it is. -/
private def affine : Bil.Exp → Option (Bap.Var × Int × Option Nat)
  | .var var => if var.typ matches .imm _ then some (var, 0, none) else none
  | .cast kind width value =>
    if kind == .low || kind == .unsigned then
      match affine value with
      | some (base, offset, known) =>
        match known with
        | none => if offset == 0 then some (base, 0, some width) else none
        | some other => if other == width then some (base, offset, some width) else none
      | none => none
    else none
  | .bin .add left right =>
    match closedBits right with
    | some constant =>
      match affine left with
      | some (base, offset, known) =>
        if known.all (· == constant.1) then some (base, offset + constant.2.toInt, some constant.1) else none
      | none => none
    | none =>
      match closedBits left with
      | some constant =>
        match affine right with
        | some (base, offset, known) =>
          if known.all (· == constant.1) then some (base, offset + constant.2.toInt, some constant.1) else none
        | none => none
      | none => none
  | .bin .sub left right =>
    match closedBits right with
    | some constant =>
      match affine left with
      | some (base, offset, known) =>
        if known.all (· == constant.1) then some (base, offset - constant.2.toInt, some constant.1) else none
      | none => none
    | none => none
  | _ => none

/-- How far from its register a location keeps track of its bytes: a loop that moves a pointer ends in `whole`. -/
private def offsetLimit : Int := 4096

/-- The location of `size` bytes of `memory` at an address, the less the more of it is known: `offset` from a register,
or wherever. -/
private def accessAt (memory : Bap.Var) (address : Bil.Exp) (size : Nat) : Location :=
  match constantRange address size with
  | some constant => .memOf memory constant size
  | none =>
    match memory.typ, affine address with
    | .mem width _, some (base, offset, known) =>
      if known.all (· == width) && decide (-offsetLimit ≤ offset) && decide (offset ≤ offsetLimit) then
        .rel memory base offset size
      else .whole memory
    | _, _ => .whole memory

/-- A location in the body of a `let`: bytes that go by what it binds are nothing outside of it. -/
private def bound (var : Bap.Var) (location : Location) : Location :=
  match location with
  | .rel memory base _ _ => if base == var then .whole memory else location
  | other => other

/-- What an expression reads. A load is only known through a memory variable itself. -/
private def usesExp : Bil.Exp → Info
  | .int _ => {}
  | .var var => if var.typ matches .imm _ then { uses := [.reg var] } else {}
  | .load memory address _ size =>
    let inner := usesExp address
    let outer := usesExp memory
    match memory with
    | .var source => { uses := accessAt source address size :: inner.uses, dynamic := inner.dynamic }
    | _ => { uses := outer.uses ++ inner.uses, dynamic := true }
  | .store memory address value _ _ =>
    let left := usesExp memory
    let middle := usesExp address
    let right := usesExp value
    { uses := left.uses ++ middle.uses ++ right.uses, dynamic := left.dynamic || middle.dynamic || right.dynamic }
  | .bin _ left right =>
    let left := usesExp left
    let right := usesExp right
    { uses := left.uses ++ right.uses, dynamic := left.dynamic || right.dynamic }
  | .un _ value => usesExp value
  | .cast _ _ value => usesExp value
  | .letIn var value body =>
    let value := usesExp value
    let body := usesExp body
    { uses := value.uses ++ body.uses.map (bound var), dynamic := value.dynamic || body.dynamic }
  | .ite condition yes no =>
    let condition := usesExp condition
    let yes := usesExp yes
    let no := usesExp no
    { uses := condition.uses ++ yes.uses ++ no.uses, dynamic := condition.dynamic || yes.dynamic || no.dynamic }
  | .extract _ _ value => usesExp value
  | .concat left right =>
    let left := usesExp left
    let right := usesExp right
    { uses := left.uses ++ right.uses, dynamic := left.dynamic || right.dynamic }
  | .unknown _ _ => { dynamic := true, always := true }

private def merge (left right : Info) : Info := {
  writes := left.writes ++ right.writes
  wholesale := left.wholesale ++ right.wholesale
  uses := left.uses ++ right.uses
  dynamic := left.dynamic || right.dynamic
  always := left.always || right.always
}

/-- The memory a chain of stores starts from. -/
private def chainRoot : Bil.Exp → Option Bap.Var
  | .var source => some source
  | .store memory _ _ _ _ => chainRoot memory
  | _ => none

/-- The locations of `dst` that a chain of stores writes, and whether it stores anywhere unknown. -/
private def memoryWrites (dst : Bap.Var) : Bil.Exp → List Location × Bool
  | .store memory address _ _ size =>
    let inner := memoryWrites dst memory
    match accessAt dst address size with
    | .whole _ => (inner.1, true)
    | location => (location :: inner.1, inner.2)
  | .var _ => ([], false)
  | _ => ([], true)

private def isStore : Bil.Exp → Bool
  | .store .. => true
  | _ => false

/-- Whether a store of a chain is longer than the address space of `dst`, and so lands on itself. -/
private def oversized (dst : Bap.Var) : Bil.Exp → Bool
  | .store memory _ _ _ size =>
    oversized dst memory ||
      match dst.typ with
      | .mem width _ => decide ((2 : Nat) ^ width < size)
      | _ => true
  | _ => false

private def stmtInfo : Bil.Stmt → Info
  | .move var value =>
    if var.typ matches .mem _ _ then
      let writes := memoryWrites var value
      { writes := writes.1
        wholesale := if writes.2 || chainRoot value != some var then [var] else []
        uses := (usesExp value).uses
        dynamic := oversized var value || (usesExp value).dynamic }
    else
      { writes := [.reg var], uses := (usesExp value).uses, dynamic := isStore value || (usesExp value).dynamic }
  | .jmp target => usesExp target
  | .special _ => { dynamic := true, always := true }
  | .cpuExn _ => { dynamic := true, always := true }
  | .while condition body =>
    let condition := usesExp condition
    let body := body.foldl (fun info stmt => merge info (stmtInfo stmt)) {}
    merge condition { body with always := true, dynamic := true }
  | .ifElse condition yes no =>
    let condition := usesExp condition
    let yes := yes.foldl (fun info stmt => merge info (stmtInfo stmt)) {}
    let no := no.foldl (fun info stmt => merge info (stmtInfo stmt)) {}
    merge condition (merge yes no)

private def blockInfo (code : Bil.Program) : Info :=
  code.foldl (fun info stmt => merge info (stmtInfo stmt)) {}

/-- Whether something an instruction may write is live. -/
private def relevant (live : List Location) (info : Info) : Bool :=
  info.always || info.wholesale.any (fun memory => live.any (Location.inMemory memory)) ||
    info.writes.any (fun write => live.any write.affects)

/-- The bytes of `memory` at `offset` from the register `dst` after `dst := value`, in terms of before it. -/
private def throughMove (memory : Bap.Var) (value : Bil.Exp) (offset : Int) (size : Nat) : Location :=
  match memory.typ, affine value, closedBits value with
  | .mem width _, some (base, moved, known), _ =>
    if known.all (· == width) && decide (-offsetLimit ≤ moved + offset) && decide (moved + offset ≤ offsetLimit) then
      .rel memory base (moved + offset) size
    else .whole memory
  | .mem width _, none, some constant =>
    if constant.1 == width && decide (0 ≤ constant.2.toNat + offset) && decide (constant.2.toNat + offset + size ≤ (2 : Int) ^ width) then
      .memOf memory (constant.2.toNat + offset).toNat size
    else .whole memory
  | _, _, _ => .whole memory

/-- What must agree before `dst := value` for `live` to agree after it, leaving aside what `value`
reads: a live register or byte of another location stays, a live range of `dst` comes from the
written bytes, unless a store covers it, and otherwise from the memory the chain of stores starts at, and
bytes that go by a register that is written go by what it is written with, if that is known. -/
private def moveBefore (dst : Bap.Var) (value : Bil.Exp) (live : List Location) : List Location :=
  if dst.typ matches .mem _ _ then
    live.filterMap fun location =>
      match location with
      | .memOf memory address size =>
        if memory != dst then some location
        else if (memoryWrites dst value).1.any (·.covers location) then none
        else match chainRoot value with
          | some root => some (.memOf root address size)
          | none => some location
      | .rel memory base offset size =>
        if memory != dst then some location
        else if (memoryWrites dst value).1.any (·.covers location) then none
        else match chainRoot value with
          | some root => some (.rel root base offset size)
          | none => some location
      | .whole memory =>
        if memory != dst then some location
        else match chainRoot value with
          | some root => some (.whole root)
          | none => some location
      | other => some other
  else
    (live.filter (· != .reg dst)).map fun location =>
      match location with
      | .rel memory base offset size =>
        if base == dst then throughMove memory value offset size else location
      | other => other

mutual
  /-- What must agree before a statement, given what must agree after it if it falls through and
  `exit` if it jumps: a jump does not run what follows, and reads have to agree when they happen. -/
  private def stmtBefore (exit : List Location) : Bil.Stmt → List Location → List Location
    | .move var value, after => (usesExp value).uses ++ moveBefore var value after
    | .jmp target, _ => (usesExp target).uses ++ exit
    | .special _, after | .cpuExn _, after => exit ++ after
    | .while condition body, after =>
      (usesExp condition).uses ++ exit ++ after ++ codeBefore exit body after
    | .ifElse condition yes no, after =>
      (usesExp condition).uses ++ codeBefore exit yes after ++ codeBefore exit no after

  private def codeBefore (exit : List Location) : List Bil.Stmt → List Location → List Location
    | [], after => after
    | stmt :: rest, after => stmtBefore exit stmt (codeBefore exit rest after)
end

/-- What must agree before an instruction for `live` to agree after it, however it ends. -/
private def insnBefore (code : Bil.Program) (live : List Location) : List Location :=
  codeBefore live code live

/-! Where an instruction can go, from its statements. -/

/-- `falls` whether control can reach the end of the code, `targets` the constants it can jump to, and
`unknown` whether it can do anything else. -/
private structure Exits where
  falls : Bool := true
  targets : List Nat := []
  unknown : Bool := false

private def constantTarget (exp : Bil.Exp) : Option Nat :=
  match Bil.evalExp [] exp with
  | .ok value =>
    match Bap.Value.asBits value with
    | .ok target => some target.2.toNat
    | .error _ => none
  | .error _ => none

mutual
  private def stmtExits : Bil.Stmt → Exits
    | .move _ _ => {}
    | .jmp target =>
      match constantTarget target with
      | some constant => { falls := false, targets := [constant] }
      | none => { falls := false, unknown := true }
    | .special _ | .cpuExn _ => { falls := false, unknown := true }
    | .while _ _ => { unknown := true }
    | .ifElse _ yes no =>
      let yes := codeExits yes
      let no := codeExits no
      { falls := yes.falls || no.falls, targets := yes.targets ++ no.targets, unknown := yes.unknown || no.unknown }

  private def codeExits : List Bil.Stmt → Exits
    | [] => {}
    | stmt :: rest =>
      let first := stmtExits stmt
      if first.falls then
        let next := codeExits rest
        { falls := next.falls, targets := first.targets ++ next.targets, unknown := first.unknown || next.unknown }
      else
        first
end

/-- The next address an instruction ending with `effect` goes to. A call is followed by its return address:
callees are not modelled, and `Result.calls` reports the ones with something live after them. -/
def nextAddress (insn : Disasm.Insn) : Bil.Effect → Option Nat
  | .normal => some insn.next
  | .jump target => some (if insn.flow = .call then insn.next else target.toNat)
  | .special _ | .cpuExn _ => none

/-- Whether an instruction may end the run: go nowhere, or to an address `successors` does not list. -/
private def mayEnd (insn : Disasm.Insn) (successors : List Nat) : Bool :=
  let exits := codeExits insn.bil
  exits.unknown ||
    (exits.falls && !successors.contains insn.next) ||
    (if insn.flow = .call then !successors.contains insn.next
     else exits.targets.any (fun target => !successors.contains target))

/-- The first site a run reaches from an instruction, if it is not in a site itself. `never` is
for code no terminating run goes through, and `conflict` for a choice that would have to be a site. -/
inductive Next where
  | never
  | exit
  | site (address : Nat)
  | conflict
  deriving DecidableEq, Repr, Inhabited

namespace Next

def join : Next → Next → Next
  | .never, other | other, .never => other
  | .conflict, _ | _, .conflict => .conflict
  | left, right => if left = right then left else .conflict

end Next

/-- What the analysis found at an address: whether it is a site, what must agree before and after
it, and what runs next if it is not a site. -/
structure Entry where
  site : Bool := false
  before : List Location := []
  after : List Location := []
  next : Next := .never
  deriving Repr, Inhabited

/-- `Result.table` holds an `Entry` per address. -/
structure Result where
  sites : List Nat := []
  live : List Location := []
  /-- Every site's effect on live locations is known, leaving aside what calls do, and the tables check out
  against the CFG, which describes the code. -/
  determined : Bool := true
  /-- Calls with something live after them. Callees are not modelled and may change it. -/
  calls : List Nat := []
  /-- `determined` with no such call: running only the sites reproduces the criteria. -/
  complete : Bool := true
  table : Std.HashMap Nat Entry := {}
  deriving Repr

def Result.entry (result : Result) (address : Nat) : Entry := result.table.getD address {}

/-- The first site a run reaches from an address, `none` when it reaches none. -/
def Result.nextSite (result : Result) (address : Nat) : Option Nat :=
  match (result.entry address).next with
  | .site site => some site
  | _ => none

/-- The memory variables an expression reads. -/
private def expMemories : Bil.Exp → List Bap.Var
  | .var var => if var.typ matches .mem _ _ then [var] else []
  | .load memory address _ _ => expMemories memory ++ expMemories address
  | .store memory address value _ _ => expMemories memory ++ expMemories address ++ expMemories value
  | .bin _ left right | .concat left right => expMemories left ++ expMemories right
  | .un _ value | .cast _ _ value | .extract _ _ value => expMemories value
  | .letIn _ value body => expMemories value ++ expMemories body
  | .ite condition yes no => expMemories condition ++ expMemories yes ++ expMemories no
  | .int _ | .unknown _ _ => []

/-- The memory variables a statement reads or writes. -/
private def stmtMemories : Bil.Stmt → List Bap.Var
  | .move var value => (if var.typ matches .mem _ _ then [var] else []) ++ expMemories value
  | .jmp target => expMemories target
  | .special _ | .cpuExn _ => []
  | .while condition body => expMemories condition ++ body.flatMap stmtMemories
  | .ifElse condition yes no => expMemories condition ++ yes.flatMap stmtMemories ++ no.flatMap stmtMemories

/-- The memory variables some instruction mentions. -/
def memories (instructions : List Disasm.Insn) : List Bap.Var :=
  (instructions.flatMap fun insn => insn.bil.flatMap stmtMemories).eraseDups

/-- A criterion that names no memory stands for its bytes in each memory the code mentions. -/
def expandCriteria (instructions : List Disasm.Insn) (criteria : List Location) : List Location :=
  let all := memories instructions
  (criteria.flatMap fun criterion =>
    match criterion with
    | .mem address size =>
      if all.isEmpty then [criterion] else all.map (Location.memOf · address size)
    | other => [other]).eraseDups

/-- The successors of each address that the CFG has and the listing holds. -/
private def successorTable (instructions : List Disasm.Insn) (edges : List (Nat × Nat)) :
    Std.HashMap Nat (List Nat) :=
  let listed : Std.HashMap Nat Unit := instructions.foldl (fun table insn => table.insert insn.address ()) {}
  edges.foldl (fun table edge =>
    if listed.contains edge.2 then table.insert edge.1 (edge.2 :: table.getD edge.1 []) else table) {}

/-! The solver. It computes what passes over the listing would, with an entry per address, each pass going through the
listing backwards and an instruction taking what it finds as it stands then, so the lists it ends with are the same ones
in the same order and a budget of passes runs out in the same place. Three things keep it from doing that work:

- Locations are numbered once per slice, and a set of them is a list of numbers and a bitset of what it holds.
- An instruction is only visited if something it reads changed. Visiting any other changes nothing.
- The sets only grow by putting locations in front, so what an instruction has not seen of a set is a prefix of it. What
  must agree before it is some fixed locations and images of each location live after it, one at a time, so what a set
  gained is all it needs to take through its code, once it has taken it all there once. Most locations are not what an
  instruction assigns, which tells without going through the code. -/

/-- Locations by number. `marks` has a bit per variable of each location, and all of them for one that is in no variable
in particular, so that a location and a set of variables with no bit in common have no variable in common. -/
private structure Numbering where
  numbers : Std.HashMap Location Nat := {}
  locations : Array Location := #[]
  marks : Array UInt64 := #[]
  variables : Std.HashMap Bap.Var UInt64 := {}

/-- The bit of a variable. Past 64 of them they share. -/
private def Numbering.bit (numbering : Numbering) (var : Bap.Var) : UInt64 × Numbering :=
  match numbering with
  | ⟨numbers, locations, marks, variables⟩ =>
    match variables[var]? with
    | some bit => (bit, ⟨numbers, locations, marks, variables⟩)
    | none =>
      let bit : UInt64 := 1 <<< UInt64.ofNat (variables.size % 64)
      (bit, ⟨numbers, locations, marks, variables.insert var bit⟩)

/-- The bits of some variables. -/
private def Numbering.bits (numbering : Numbering) (vars : List Bap.Var) : UInt64 × Numbering :=
  vars.foldl (init := (0, numbering)) fun state var =>
    let (bit, numbering) := state.2.bit var
    (state.1 ||| bit, numbering)

private def Location.mark (location : Location) (numbering : Numbering) : UInt64 × Numbering :=
  match location with
  | .reg var | .whole var | .memOf var _ _ => numbering.bit var
  | .rel memory base _ _ => numbering.bits [memory, base]
  | .mem _ _ => (UInt64.ofNat (2 ^ 64 - 1), numbering)

private def Numbering.number (numbering : Numbering) (location : Location) : Nat × Numbering :=
  match numbering.numbers[location]? with
  | some number => (number, numbering)
  | none =>
    let (mark, numbering) := location.mark numbering
    match numbering with
    | ⟨numbers, locations, marks, variables⟩ =>
      (locations.size, ⟨numbers.insert location locations.size, locations.push location, marks.push mark, variables⟩)

/-- The location of a number. -/
private def Numbering.named (numbering : Numbering) (number : Nat) : Location :=
  numbering.locations.getD number (.mem 0 0)

/-- A set of numbers: `list` has its elements, each once and the last added first, `size` of them, and `bits` tells. -/
private structure LiveSet where
  list : List Nat := []
  size : Nat := 0
  bits : ByteArray := ByteArray.empty

instance : Inhabited LiveSet := ⟨{}⟩

/-- `bits` with room for the byte `index`. -/
private def roomFor (bits : ByteArray) (index : Nat) : ByteArray :=
  if index < bits.size then bits
  else bits ++ ByteArray.mk (Array.replicate (2 * index + 16 - bits.size) 0)

private def LiveSet.add (set : LiveSet) (number : Nat) : LiveSet :=
  match set with
  | ⟨list, size, bits⟩ =>
    let index := number / 8
    let mask : UInt8 := 1 <<< (UInt8.ofNat (number % 8))
    let bits := roomFor bits index
    let byte := bits.get! index
    if byte &&& mask == 0 then ⟨number :: list, size + 1, bits.set! index (byte ||| mask)⟩ else ⟨list, size, bits⟩

private def LiveSet.addAll (set : LiveSet) (numbers : List Nat) : LiveSet :=
  numbers.foldl LiveSet.add set

/-- `set` with `locations` numbered and added, in order. -/
private def LiveSet.addLocations (set : LiveSet) (numbering : Numbering) :
    List Location → LiveSet × Numbering
  | [] => (set, numbering)
  | location :: rest =>
    let (number, numbering) := numbering.number location
    LiveSet.addLocations (set.add number) numbering rest

/-- The variables a statement assigns. -/
private def stmtAssigned : Bil.Stmt → List Bap.Var
  | .move var _ => [var]
  | .jmp _ | .special _ | .cpuExn _ => []
  | .while _ body => body.flatMap stmtAssigned
  | .ifElse _ yes no => yes.flatMap stmtAssigned ++ no.flatMap stmtAssigned

private def isPlain : Bil.Stmt → Bool
  | .move .. | .jmp _ => true
  | _ => false

/-- An element of the listing, as `code` has them. `slot` is the place of its address in the tables. -/
private structure Visit where
  address : Nat
  slot : Nat
  bil : Bil.Program
  info : Info
  ends : Bool
  /-- The bits of the variables it assigns. -/
  moved : UInt64
  /-- Nothing but assignments and jumps: what must agree before it is some fixed locations, then one location or none
  for each location live after it, in order, and the same one if it has no bit in common with `moved`. -/
  plain : Bool

instance : Inhabited Visit := ⟨⟨0, 0, [], {}, false, 0, false⟩⟩

/-- What does not change as the tables fill up. By slot: `edges` has the slots an address goes to, each with its number
among all edges, `readers` the visits with an edge to it, and `peers` its own, more than one if the listing has an
address twice. -/
private structure Plan where
  code : Array Visit
  edges : Array (List (Nat × Nat))
  readers : Array (List Nat)
  peers : Array (List Nat)
  criteria : List Nat

/-- The tables, by slot, and how far each visit got, by visit: `done` is how much of `after` it took, `taken` whether it
has been through its code, as `pending` and `ended` whether it has anything to look at or the criteria yet. `seen` is
how much of what an edge goes to it got. -/
private structure Tables where
  after : Array LiveSet
  before : Array LiveSet
  site : Array Bool
  next : Array Next
  seen : Array Nat
  done : Array Nat
  taken : Array Bool
  ended : Array Bool
  pending : Array Bool
  numbering : Numbering

/-- What the edges in `edges` add to `set`, of which only what `seen` has not been told is news. -/
private def pull (before : Array LiveSet) (edges : List (Nat × Nat)) (set : LiveSet) (seen : Array Nat) :
    LiveSet × Array Nat :=
  match edges with
  | [] => (set, seen)
  | (edge, target) :: rest =>
    let source := before[target]!
    let news := source.size - seen[edge]!
    if news == 0 then pull before rest set seen
    else pull before rest (set.addAll (source.list.take news)) (seen.set! edge source.size)

private def mark (flags : Array Bool) (visits : List Nat) : Array Bool :=
  visits.foldl (fun flags visit => flags.set! visit true) flags

/-- `set` with what must agree before a plain instruction for `numbers` to agree after it, leaving aside what it reads
whatever is live. -/
private def LiveSet.addThrough (visit : Visit) (set : LiveSet) (numbering : Numbering) :
    List Nat → LiveSet × Numbering
  | [] => (set, numbering)
  | number :: rest =>
    if numbering.marks[number]! &&& visit.moved == 0 then
      LiveSet.addThrough visit (set.add number) numbering rest
    else
      let (set, numbering) := set.addLocations numbering (insnBefore visit.bil [numbering.named number])
      LiveSet.addThrough visit set numbering rest

/-- Visits an instruction: `true` if a table changed. -/
private def livenessVisit (plan : Plan) (position : Nat) (tables : Tables) : Tables × Bool :=
  match tables with
  | ⟨after, before, site, next, seen, done, taken, ended, pending, numbering⟩ =>
    let pending := pending.set! position false
    let visit := plan.code[position]!
    let slot := visit.slot
    let set := after[slot]!
    let after := after.set! slot {}
    let sizeAfter := set.size
    let (set, seen) := pull before plan.edges[slot]! set seen
    let (set, ended) :=
      if visit.ends && !ended[position]! then (set.addAll plan.criteria, ended.set! position true) else (set, ended)
    let news := set.list.take (set.size - done[position]!)
    let done := done.set! position set.size
    let wasSite := site[slot]!
    let isSite := wasSite || visit.info.always || news.any fun number =>
      numbering.marks[number]! &&& visit.moved != 0 && relevant [numbering.named number] visit.info
    let inputs := set.list
    let sizeNow := set.size
    let after := after.set! slot set
    let gained := before[slot]!
    let before := before.set! slot {}
    let sizeBefore := gained.size
    let first := isSite && !taken[position]!
    let taken := if first then taken.set! position true else taken
    let (gained, numbering) :=
      if !isSite then (gained.addAll news, numbering)
      else if visit.plain then
        if first then
          let (gained, numbering) := gained.addLocations numbering (insnBefore visit.bil [])
          gained.addThrough visit numbering inputs
        else gained.addThrough visit numbering news
      else if first then gained.addLocations numbering (insnBefore visit.bil (inputs.map numbering.named))
      else if news.isEmpty then (gained, numbering)
      else gained.addLocations numbering (insnBefore visit.bil (news.map numbering.named))
    let grewBefore := gained.size != sizeBefore
    let before := before.set! slot gained
    let site := if isSite != wasSite then site.set! slot isSite else site
    let grew := isSite != wasSite || grewBefore || sizeNow != sizeAfter
    let pending := if grewBefore then mark pending plan.readers[slot]! else pending
    let pending :=
      match plan.peers[slot]! with
      | [_] => pending
      | peers => if grew then mark pending (peers.filter (· != position)) else pending
    (⟨after, before, site, next, seen, done, taken, ended, pending, numbering⟩, grew)

/-- One pass over visits from `position`, the ones that are pending. -/
private def livenessPass (plan : Plan) : Nat → Nat → Tables → Bool → Tables × Bool
  | 0, _, tables, changed => (tables, changed)
  | count + 1, position, tables, changed =>
    if tables.pending[position]! then
      let (tables, grew) := livenessVisit plan position tables
      livenessPass plan count (position + 1) tables (changed || grew)
    else
      livenessPass plan count (position + 1) tables changed

private def livenessFix (plan : Plan) : Nat → Tables → Tables
  | 0, tables => tables
  | fuel + 1, tables =>
    let (tables, changed) := livenessPass plan plan.code.size 0 tables false
    if changed then livenessFix plan fuel tables else tables

/-- One pass of what runs next, given the sites, over the visits that are pending. -/
private def nextPass (plan : Plan) (site : Array Bool) :
    Nat → Nat → Array Next → Array Bool → Bool → Array Next × Array Bool × Bool
  | 0, _, next, pending, changed => (next, pending, changed)
  | count + 1, position, next, pending, changed =>
    if pending[position]! then
      let pending := pending.set! position false
      let visit := plan.code[position]!
      let slot := visit.slot
      let found : Next :=
        if site[slot]! then .site visit.address
        else
          (plan.edges[slot]!).foldl (fun found edge => Next.join found next[edge.2]!)
            (if visit.ends then Next.exit else Next.never)
      if next[slot]! == found then
        nextPass plan site count (position + 1) next pending changed
      else
        let pending := mark pending plan.readers[slot]!
        let pending :=
          match plan.peers[slot]! with
          | [_] => pending
          | peers => mark pending (peers.filter (· != position))
        nextPass plan site count (position + 1) (next.set! slot found) pending true
    else
      nextPass plan site count (position + 1) next pending changed

private def nextFix (plan : Plan) (site : Array Bool) : Nat → Array Next → Array Bool → Array Next
  | 0, next, _ => next
  | fuel + 1, next, pending =>
    let (next, pending, changed) := nextPass plan site plan.code.size 0 next pending false
    if changed then nextFix plan site fuel next pending else next

/-- The choices that have to become sites: where what runs next depends on the path taken. Those whose
successors agree on no conflict come first, as making them sites may settle the ones before them. -/
private def conflicts (plan : Plan) (next : Array Next) : List Nat :=
  let all := plan.code.toList.filter fun visit => next[visit.slot]! == .conflict
  let origins := all.filter fun visit =>
    (plan.edges[visit.slot]!).all fun edge => next[edge.2]! != .conflict
  (if origins.isEmpty then all else origins).map (·.slot)

/-- Liveness and sites to a fixpoint, then what runs next; a choice that conflicts joins the sites,
and all of it again. Out of fuel, `check` finds the tables wanting. -/
private def solve (plan : Plan) (passes : Nat) : Nat → Tables → Tables
  | 0, tables => tables
  | fuel + 1, tables =>
    let tables := livenessFix plan passes tables
    let slots := plan.edges.size
    let next := nextFix plan tables.site passes (Array.replicate slots Next.never)
      (Array.replicate plan.code.size true)
    match conflicts plan next with
    | [] => { tables with next }
    | added =>
      let site := added.foldl (fun site slot => site.set! slot true) tables.site
      let pending := added.foldl (fun pending slot => mark pending plan.peers[slot]!) tables.pending
      solve plan passes fuel { tables with next, site, pending }

/-- Lays out what `solve` works on, the listing being given backwards. -/
private def planOf (code : List Disasm.Insn) (successors : Std.HashMap Nat (List Nat)) (criteria : List Location) :
    Plan × Tables :=
  let (slots, count) := code.foldl (init := (({} : Std.HashMap Nat Nat), 0)) fun state insn =>
    if state.1.contains insn.address then state else (state.1.insert insn.address state.2, state.2 + 1)
  let (visits, numbering) := code.foldl (init := ((#[] : Array Visit), ({} : Numbering))) fun state insn =>
    let next := successors.getD insn.address []
    let (moved, numbering) := state.2.bits (insn.bil.flatMap stmtAssigned)
    (state.1.push { address := insn.address, slot := slots.getD insn.address 0, bil := insn.bil, info := blockInfo insn.bil
                    ends := mayEnd insn next, moved, plain := insn.bil.all isPlain }, numbering)
  let (edges, edgeCount) := code.foldl (init := (Array.replicate count [], 0)) fun state insn =>
    let slot := slots.getD insn.address 0
    if state.1[slot]!.isEmpty then
      let targets := (successors.getD insn.address []).map (slots.getD · 0)
      (state.1.set! slot (targets.zipIdx state.2 |>.map fun edge => (edge.2, edge.1)), state.2 + targets.length)
    else state
  let peers := (visits.zipIdx.foldr (init := Array.replicate count []) fun visit peers =>
    peers.modify visit.1.slot (visit.2 :: ·))
  let readers := visits.zipIdx.foldr (init := Array.replicate count []) fun visit readers =>
    (edges[visit.1.slot]!).foldl (fun readers edge => readers.modify edge.2 (visit.2 :: ·)) readers
  let numbering := criteria.foldl (fun numbering location => (numbering.number location).2) numbering
  ({ code := visits, edges, readers, peers
     criteria := criteria.map fun location => (numbering.number location).1 },
   { after := Array.replicate count {}, before := Array.replicate count {}, site := Array.replicate count false
     next := Array.replicate count .never, seen := Array.replicate edgeCount 0, done := Array.replicate visits.size 0
     taken := Array.replicate visits.size false, ended := Array.replicate visits.size false
     pending := Array.replicate visits.size true, numbering })

/-- The entries of what `solve` found, for `code`, in the order an entry is first written by a pass. -/
private def tableOf (plan : Plan) (tables : Tables) : Std.HashMap Nat Entry :=
  plan.code.foldl (init := {}) fun table visit =>
    let slot := visit.slot
    if table.contains visit.address then table
    else table.insert visit.address {
      site := tables.site[slot]!
      before := tables.before[slot]!.list.map tables.numbering.named
      after := tables.after[slot]!.list.map tables.numbering.named
      next := tables.next[slot]! }

/-- The tables are a solution of the equations: this and nothing else is what soundness rests on. -/
private def checkInsn (entry : Nat → Entry) (next : List Nat) (criteria : List Location)
    (insn : Disasm.Insn) : Bool :=
  let here := entry insn.address
  next.all (fun target => (entry target).before.all here.after.contains) &&
  (!mayEnd insn next || criteria.all here.after.contains) &&
  (!relevant here.after (blockInfo insn.bil) || here.site) &&
  (if here.site then
    (insnBefore insn.bil here.after).all here.before.contains && here.next == .site insn.address
  else
    here.after.all here.before.contains &&
    (!mayEnd insn next || here.next == .exit) &&
    next.all fun target => (entry target).next == here.next || (entry target).next == .never)

/-- `checkInsn`, with what it looks in hashed. -/
private def checkInsnFast (entry : Nat → Entry) (next : List Nat) (criteria : List Location)
    (insn : Disasm.Insn) : Bool :=
  let here := entry insn.address
  let after : Std.HashSet Location := Std.HashSet.ofList here.after
  let before : Std.HashSet Location := Std.HashSet.ofList here.before
  next.all (fun target => (entry target).before.all after.contains) &&
  (!mayEnd insn next || criteria.all after.contains) &&
  (!relevant here.after (blockInfo insn.bil) || here.site) &&
  (if here.site then
    (insnBefore insn.bil here.after).all before.contains && here.next == .site insn.address
  else
    here.after.all before.contains &&
    (!mayEnd insn next || here.next == .exit) &&
    next.all fun target => (entry target).next == here.next || (entry target).next == .never)

private theorem contains_hashed (list : List Location) :
    (Std.HashSet.ofList list).contains = list.contains := by
  funext location
  simp [Std.HashSet.contains_ofList]

@[csimp] private theorem checkInsn_eq_fast : @checkInsn = @checkInsnFast := by
  funext entry next criteria insn
  simp only [checkInsn, checkInsnFast, contains_hashed]

/-- Every constant jump into the listing is an edge of the CFG, or the CFG does not describe the code. -/
private def checkEdges (listed : Nat → Bool) (next : List Nat) (insn : Disasm.Insn) : Bool :=
  insn.flow == .call || (codeExits insn.bil).targets.all fun target => next.contains target || !listed target

/-- An indirect jump goes anywhere, and the CFG has no edges for it. -/
private def checkFlow (insn : Disasm.Insn) : Bool := insn.flow != .indirectJump

/-! The equations and the checks of `backwardCfg`, for a test to hold its solver against another. -/
namespace Equations

def successors (instructions : List Disasm.Insn) (edges : List (Nat × Nat)) : Std.HashMap Nat (List Nat) :=
  successorTable instructions edges

def mayEnd (insn : Disasm.Insn) (successors : List Nat) : Bool := Slice.mayEnd insn successors

def relevant (live : List Location) (code : Bil.Program) : Bool := Slice.relevant live (blockInfo code)

def before (code : Bil.Program) (live : List Location) : List Location := insnBefore code live

/-- `Result.determined` of tables. -/
def determined (instructions : List Disasm.Insn) (edges : List (Nat × Nat)) (criteria : List Location)
    (entry : Nat → Entry) : Bool :=
  let successors := successorTable instructions edges
  let listed : Std.HashMap Nat Unit := instructions.foldl (fun table insn => table.insert insn.address ()) {}
  ((instructions.filter fun insn => (entry insn.address).site).all fun insn => !(blockInfo insn.bil).dynamic) &&
    instructions.all fun insn =>
      let next := successors.getD insn.address []
      checkInsn entry next criteria insn && checkEdges (listed.contains ·) next insn && checkFlow insn

end Equations

/-- Slices `instructions` over the CFG `edges`, as of `entry`. An instruction is a site if it writes
something live after it, or if what runs next depends on it: `Result.nextSite` tells what follows
an address if not a site, and a choice between different next sites is a site. -/
def backwardCfg (instructions : List Disasm.Insn) (edges : List (Nat × Nat)) (entry : Option Nat)
    (criteria : List Location) : Result :=
  let criteria := expandCriteria instructions criteria
  let successors := successorTable instructions edges
  -- Backwards through the listing, so most facts need only one pass.
  let code := instructions.reverse
  let passes := 4 * (instructions.length + 2) * (criteria.length + (instructions.map (·.bil.length)).sum + 2)
  let (plan, start) := planOf code successors criteria
  let table := tableOf plan (solve plan passes (instructions.length + 1) start)
  let lookup (address : Nat) : Entry := table.getD address {}
  let listed : Std.HashMap Nat Unit := instructions.foldl (fun table insn => table.insert insn.address ()) {}
  let sited := instructions.filter fun insn => (lookup insn.address).site
  let calls := (instructions.filter fun insn =>
    insn.flow = .call && !(lookup insn.address).after.isEmpty).map (·.address)
  let tables := instructions.all fun insn =>
    let next := successors.getD insn.address []
    checkInsn lookup next criteria insn && checkEdges (listed.contains ·) next insn && checkFlow insn
  let determined := (sited.all fun insn => !(blockInfo insn.bil).dynamic) && tables
  {
    sites := sited.map (·.address)
    live := match entry <|> instructions.head?.map (·.address) with
      | some address => if listed.contains address then (lookup address).before else criteria
      | none => criteria
    determined
    calls
    complete := determined && calls.isEmpty
    table
  }

/-- The edges of each instruction, as its flow tells them. -/
def flowEdges (instructions : List Disasm.Insn) : List (Nat × Nat) :=
  instructions.flatMap fun insn => insn.successors.map (insn.address, ·)

/-- Slices `instructions` over the control flow their `flow` and `target` give, from the first. -/
def backward (instructions : List Disasm.Insn) (criteria : List Location) : Result :=
  backwardCfg instructions (flowEdges instructions) none criteria

/-- Slices the function of `entry`, or the whole listing if no function has it, over the CFG of the
project. An edge the flow of an instruction gives counts even if the disassembly left it out. -/
def backwardProject (project : Project.Project) (entry : Nat) (criteria : List Location) : Result :=
  let index := Xrefs.create project
  let owner := (Xrefs.functionOf index entry).map Image.Symbol.addr
  let instructions := project.disasm.map (fun disasm =>
    if owner.isSome then
      disasm.instructions.filter fun insn =>
        (Xrefs.functionOf index insn.address).map Image.Symbol.addr = owner
    else
      disasm.instructions) |>.getD []
  let edges := (project.disasm.map (·.edges)).getD [] ++ flowEdges instructions
  backwardCfg instructions edges (some entry) criteria

end Bap.Analysis.Slice
