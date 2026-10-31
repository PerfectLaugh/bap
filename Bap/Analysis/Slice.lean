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
  `exit` if it jumps: a jump does not run what follows, and reads have to agree when they happen. What the arms of
  an `if` have in common only counts once, or a run of them doubles the list each time. -/
  private def stmtBefore (exit : List Location) : Bil.Stmt → List Location → List Location
    | .move var value, after => (usesExp value).uses ++ moveBefore var value after
    | .jmp target, _ => (usesExp target).uses ++ exit
    | .special _, after | .cpuExn _, after => exit ++ after
    | .while condition body, after =>
      (usesExp condition).uses ++ exit ++ (after ++ codeBefore exit body after).eraseDups
    | .ifElse condition yes no, after =>
      (usesExp condition).uses ++ (codeBefore exit yes after ++ codeBefore exit no after).eraseDups

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

/-- The bit of a variable in a mark. Variables can share one, which only costs a look. -/
private def varBit (var : Bap.Var) : UInt64 := 1 <<< (hash var)

/-- A bit of each variable of a location, and all of them for one that is in no variable in particular: a location and a
set of variables with no bit in common have no variable in common. -/
private def Location.mark : Location → UInt64
  | .reg var | .whole var | .memOf var _ _ => varBit var
  | .rel memory base _ _ => varBit memory ||| varBit base
  | .mem _ _ => UInt64.ofNat (2 ^ 64 - 1)

/-- An `Entry` as `backwardCfg` keeps it: a set has a bit per number of a location. -/
structure Cell where
  site : Bool := false
  before : ByteArray := ByteArray.empty
  after : ByteArray := ByteArray.empty
  next : Next := .never
  deriving Inhabited

/-- Whether a set holds a number. -/
@[inline] def has (set : ByteArray) (number : Nat) : Bool :=
  (set.get! (number / 8) >>> UInt8.ofNat (number % 8)) &&& 1 != 0

/-- The tables of a slice. `slots` has the place in `cells` of each address, and `marks` the mark of each location. -/
structure Numbered where
  slots : Std.HashMap Nat Nat := {}
  cells : Array Cell := #[]
  locations : Array Location := #[]
  numbers : Std.HashMap Location Nat := {}
  marks : Array UInt64 := #[]
  marked : marks = locations.map Location.mark := by simp

namespace Numbered

def cell (tables : Numbered) (address : Nat) : Cell :=
  match tables.slots[address]? with
  | some slot => tables.cells.getD slot {}
  | none => {}

/-- The locations of a set. -/
def setOf (tables : Numbered) (set : ByteArray) : List Location :=
  (List.range tables.locations.size).filterMap fun number =>
    if has set number then tables.locations[number]? else none

/-- What the analysis found at an address. -/
def entry (tables : Numbered) (address : Nat) : Entry :=
  let cell := tables.cell address
  { site := cell.site, before := tables.setOf cell.before, after := tables.setOf cell.after, next := cell.next }

end Numbered

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
  /-- Some register had too many offsets, and what went by it became all of the memory: see `offsetsPerBase`. -/
  widened : Bool := false
  tables : Numbered := {}

def Result.entry (result : Result) (address : Nat) : Entry := result.tables.entry address

/-- The first site a run reaches from an address, `none` when it reaches none. -/
def Result.nextSite (result : Result) (address : Nat) : Option Nat :=
  match (result.tables.cell address).next with
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

/-- `expandCriteria`, given the memory variables. -/
private def expandWith (all : List Bap.Var) (criteria : List Location) : List Location :=
  (criteria.flatMap fun criterion =>
    match criterion with
    | .mem address size =>
      if all.isEmpty then [criterion] else all.map (Location.memOf · address size)
    | other => [other]).eraseDups

/-- A criterion that names no memory stands for its bytes in each memory the code mentions. -/
def expandCriteria (instructions : List Disasm.Insn) (criteria : List Location) : List Location :=
  expandWith (memories instructions) criteria

/-- The successors of each address that the CFG has and the listing holds. -/
private def successorTable (instructions : List Disasm.Insn) (edges : List (Nat × Nat)) :
    Std.HashMap Nat (List Nat) :=
  let listed : Std.HashMap Nat Unit := instructions.foldl (fun table insn => table.insert insn.address ()) {}
  edges.foldl (fun table edge =>
    if listed.contains edge.2 then table.insert edge.1 (edge.2 :: table.getD edge.1 []) else table) {}

/-! The solver. `check` below is what soundness rests on, so nothing here has to be right; what it finds is the least
solution of the equations, but for `offsetsPerBase`. Three things keep it from redoing work:

- Locations are numbered once per slice, on top of what a listing always reads, and a set of them is a bit per number.
  Sets that are the same share their bits.
- An instruction is only visited if something it reads changed. Visiting any other changes nothing.
- What must agree before an instruction is some fixed locations and images of each location live after it, one at a
  time, so what it gained is all it needs to take through its code, once it has taken it all there once. Most locations
  are not what an instruction assigns, which tells without going through the code. -/

/-- How many offsets from one register one memory is tracked at in a slice. A pointer that walks in a loop has a location
per step otherwise, up to `offsetLimit` away on either side. Past this many, what would be one more location is all of
the memory and the register: more to agree on, and so more sites, never fewer. -/
private def offsetsPerBase : Nat := 8

/-- Locations by number. `counts` has how many are at some offset from a register of a memory, and `widened` whether
there were more. -/
private structure Numbering where
  numbers : Std.HashMap Location Nat := {}
  locations : Array Location := #[]
  marks : Array UInt64 := #[]
  marked : marks = locations.map Location.mark := by simp
  counts : Std.HashMap (Bap.Var × Bap.Var) Nat := {}
  widened : Bool := false

private def Numbering.number (numbering : Numbering) (location : Location) : Nat × Numbering :=
  match numbering.numbers[location]? with
  | some number => (number, numbering)
  | none =>
    match numbering with
    | ⟨numbers, locations, marks, marked, counts, widened⟩ =>
      (locations.size, ⟨numbers.insert location locations.size, locations.push location, marks.push location.mark,
        by simp [marked], counts, widened⟩)

/-- The location of a number. -/
private def Numbering.named (numbering : Numbering) (number : Nat) : Location :=
  numbering.locations.getD number (.mem 0 0)

/-- Zeros to make room with. -/
private def zeros : ByteArray := ByteArray.mk (Array.replicate 32 0)

/-- `bits` with room for the byte `index`. -/
@[inline] private def roomFor (bits : ByteArray) (index : Nat) : ByteArray :=
  if index < bits.size then bits else go bits (index + 1)
where
  go (bits : ByteArray) : Nat → ByteArray
    | 0 => bits
    | fuel + 1 => if index < bits.size then bits else go (bits ++ zeros) fuel

/-- `bits` with a number. -/
private def addBit (bits : ByteArray) (number : Nat) : ByteArray :=
  let index := number / 8
  let mask : UInt8 := 1 <<< (UInt8.ofNat (number % 8))
  let bits := roomFor bits index
  let byte := bits.get! index
  if byte &&& mask == 0 then bits.set! index (byte ||| mask) else bits

/-- `left` with the numbers of `right`, and whether that is more: `right` itself if `left` has no room yet, so the two
share their bits, and `left` itself if `right` adds nothing. -/
private def union (left right : ByteArray) : ByteArray × Bool :=
  if left.size == 0 then (right, right.size != 0) else go right.size left false
where
  go : Nat → ByteArray → Bool → ByteArray × Bool
    | 0, left, grew => (left, grew)
    | index + 1, left, grew =>
      let byte := right.get! index
      if byte == 0 then go index left grew
      else
        let left := roomFor left index
        let old := left.get! index
        if old ||| byte == old then go index left grew
        else go index (left.set! index (old ||| byte)) true

/-- The numbers in `bits` that are not in `seen`. -/
private def newNumbers (bits seen : ByteArray) : List Nat :=
  go bits.size []
where
  go : Nat → List Nat → List Nat
    | 0, numbers => numbers
    | index + 1, numbers =>
      let byte := bits.get! index &&& ~~~(if index < seen.size then seen.get! index else 0)
      if byte == 0 then go index numbers
      else go index (fromByte byte index 8 numbers)
  fromByte (byte : UInt8) (index : Nat) : Nat → List Nat → List Nat
    | 0, numbers => numbers
    | bit + 1, numbers =>
      fromByte byte index bit
        (if (byte >>> UInt8.ofNat bit) &&& 1 == 0 then numbers else (8 * index + bit) :: numbers)

/-- `bits` with `location`, or, if that is one offset too many from a register, what holds it anyway. -/
private def addLocation (bits : ByteArray) (numbering : Numbering) (location : Location) : ByteArray × Numbering :=
  match location with
  | .rel memory base _ _ =>
    if numbering.numbers.contains location then
      let (number, numbering) := numbering.number location
      (addBit bits number, numbering)
    else
      let key := (memory, base)
      let count := numbering.counts.getD key 0
      if count < offsetsPerBase then
        let (number, numbering) := numbering.number location
        (addBit bits number, { numbering with counts := numbering.counts.insert key (count + 1) })
      else
        let (whole, numbering) := numbering.number (.whole memory)
        let (register, numbering) := numbering.number (.reg base)
        (addBit (addBit bits whole) register, { numbering with widened := true })
  | _ =>
    let (number, numbering) := numbering.number location
    (addBit bits number, numbering)

/-- `bits` with `locations` numbered and added, in order. -/
private def addLocations (bits : ByteArray) (numbering : Numbering) : List Location → ByteArray × Numbering
  | [] => (bits, numbering)
  | location :: rest =>
    let (bits, numbering) := addLocation bits numbering location
    addLocations bits numbering rest

/-- The variables a statement assigns. -/
private def stmtAssigned : Bil.Stmt → List Bap.Var
  | .move var _ => [var]
  | .jmp _ | .special _ | .cpuExn _ => []
  | .while _ body => body.flatMap stmtAssigned
  | .ifElse _ yes no => yes.flatMap stmtAssigned ++ no.flatMap stmtAssigned

private def isPlain : Bil.Stmt → Bool
  | .move .. | .jmp _ => true
  | _ => false

/-- The bits of the variables some code assigns. -/
private def movedOf (code : Bil.Program) : UInt64 :=
  (code.flatMap stmtAssigned).foldl (fun bits var => bits ||| varBit var) 0

/-- `dst := value`, with what `moveBefore` wants of it worked out. -/
private structure Step where
  dst : Bap.Var
  /-- For a register: what `throughMove` wants of `value`. -/
  moved : Option (Bap.Var × Int × Option Nat)
  closed : Option (Σ width, BitVec width)
  /-- For a memory: what a chain of stores writes, and what it starts at. -/
  writes : List Location
  root : Option Bap.Var

private def stepOf (dst : Bap.Var) (value : Bil.Exp) : Step :=
  { dst, moved := affine value, closed := closedBits value, writes := (memoryWrites dst value).1, root := chainRoot value }

/-- `throughMove` of a step. -/
private def Step.through (step : Step) (memory : Bap.Var) (offset : Int) (size : Nat) : Location :=
  match memory.typ, step.moved, step.closed with
  | .mem width _, some (base, moved, known), _ =>
    if known.all (· == width) && decide (-offsetLimit ≤ moved + offset) && decide (moved + offset ≤ offsetLimit) then
      .rel memory base (moved + offset) size
    else .whole memory
  | .mem width _, none, some constant =>
    if constant.1 == width && decide (0 ≤ constant.2.toNat + offset) && decide (constant.2.toNat + offset + size ≤ (2 : Int) ^ width) then
      .memOf memory (constant.2.toNat + offset).toNat size
    else .whole memory
  | _, _, _ => .whole memory

/-- `moveBefore` of a step, for one location. -/
private def Step.image (step : Step) (location : Location) : List Location :=
  let dst := step.dst
  if dst.typ matches .mem _ _ then
    match location with
    | .memOf memory address size =>
      if memory != dst then [location]
      else if step.writes.any (·.covers location) then []
      else match step.root with
        | some root => [.memOf root address size]
        | none => [location]
    | .rel memory base offset size =>
      if memory != dst then [location]
      else if step.writes.any (·.covers location) then []
      else match step.root with
        | some root => [.rel root base offset size]
        | none => [location]
    | .whole memory =>
      if memory != dst then [location]
      else match step.root with
        | some root => [.whole root]
        | none => [location]
    | other => [other]
  else if location == .reg dst then []
  else match location with
    | .rel memory base offset size =>
      [if base == dst then step.through memory offset size else location]
    | other => [other]

/-- The assignments of plain code as far as it goes: a jump ends it. -/
private def stepsOf : Bil.Program → List Step
  | .move var value :: rest => stepOf var value :: stepsOf rest
  | _ => []

/-- What must agree before steps for `location` to agree after them, leaving aside what they read. -/
private def imageOf (steps : List Step) (location : Location) : List Location :=
  steps.foldr (fun step live => live.flatMap step.image) [location]

/-- An element of the listing, with what does not depend on what is live. `slot` is the place of its address in the
tables and `next` where the CFG goes from it. -/
private structure Visit where
  insn : Disasm.Insn
  slot : Nat
  next : List Nat
  info : Info
  ends : Bool
  moved : UInt64
  /-- Nothing but assignments and jumps: what must agree before it is `fixed`, then one location or none for each
  location live after it, in order, and the same one if it has no bit in common with `moved`. -/
  plain : Bool
  fixed : List Location
  /-- The numbers of `fixed` in what the numbering of a slice starts from, as bits and one by one. -/
  fixedBits : ByteArray
  fixedNumbers : List Nat
  steps : List Step

instance : Inhabited Visit := ⟨⟨⟨0, 0, "", .normal, none, []⟩, 0, [], {}, false, 0, false, [], ByteArray.empty, [], []⟩⟩

private def visitOf (slots : Std.HashMap Nat Nat) (successors : Std.HashMap Nat (List Nat)) (numbering : Numbering)
    (insn : Disasm.Insn) : Visit :=
  let next := successors.getD insn.address []
  let fixed := insnBefore insn.bil []
  let fixedNumbers := fixed.map (numbering.numbers.getD · 0)
  { insn, slot := slots.getD insn.address 0, next, info := blockInfo insn.bil, ends := mayEnd insn next
    moved := movedOf insn.bil, plain := insn.bil.all isPlain, fixed, fixedNumbers
    fixedBits := fixedNumbers.foldl addBit ByteArray.empty, steps := stepsOf insn.bil }

/-- What must agree before a visit for `location` to agree after it, whatever it reads aside. -/
private def imageAt (visit : Visit) (location : Location) : List Location :=
  if visit.plain then imageOf visit.steps location else insnBefore visit.insn.bil [location]

/-- What does not change as the tables fill up. By slot: `edges` has the slots an address goes to, `readers` the visits
with an edge to it, and `peers` its own, more than one if the listing has an address twice. -/
private structure Plan where
  code : Array Visit
  edges : Array (List Nat)
  readers : Array (List Nat)
  peers : Array (List Nat)
  /-- What every slice numbers. -/
  numbering : Numbering

/-- The tables, by slot, and how far each visit got, by visit: `done` is what of `after` it took, `taken` whether it has
been through its code, as `pending` and `ended` whether it has anything to look at or the criteria yet. -/
private structure Tables where
  after : Array ByteArray
  before : Array ByteArray
  site : Array Bool
  next : Array Next
  done : Array ByteArray
  taken : Array Bool
  ended : Array Bool
  pending : Array Bool
  numbering : Numbering

/-- What the edges in `edges` add to `set`. -/
private def pull (before : Array ByteArray) : List Nat → ByteArray → Bool → ByteArray × Bool
  | [], set, grew => (set, grew)
  | target :: rest, set, grew =>
    let (set, more) := union set before[target]!
    pull before rest set (grew || more)

private def flag (flags : Array Bool) (visits : List Nat) : Array Bool :=
  visits.foldl (fun flags visit => flags.set! visit true) flags

/-- `bits` with what must agree before an instruction for `numbers` to agree after it, leaving aside what it reads
whatever is live. -/
private def addThrough (visit : Visit) (bits : ByteArray) (numbering : Numbering) :
    List Nat → ByteArray × Numbering
  | [] => (bits, numbering)
  | number :: rest =>
    if numbering.marks[number]! &&& visit.moved == 0 then
      addThrough visit (addBit bits number) numbering rest
    else
      let (bits, numbering) := addLocations bits numbering (imageAt visit (numbering.named number))
      addThrough visit bits numbering rest

/-- Visits an instruction: `true` if a table changed. -/
private def livenessVisit (plan : Plan) (criteria : ByteArray) (position : Nat) (tables : Tables) : Tables × Bool :=
  match tables with
  | ⟨after, before, site, next, done, taken, ended, pending, numbering⟩ =>
    let pending := pending.set! position false
    let visit := plan.code[position]!
    let slot := visit.slot
    let set := after[slot]!
    let after := after.set! slot ByteArray.empty
    let (set, grewAfter) := pull before plan.edges[slot]! set false
    let (set, grewAfter, ended) :=
      if visit.ends && !ended[position]! then
        let (set, more) := union set criteria
        (set, grewAfter || more, ended.set! position true)
      else (set, grewAfter, ended)
    let wasSite := site[slot]!
    let seen := done[position]!
    -- A set that did not grow here is what the last visit left, unless the address has another visit.
    let news := match plan.peers[slot]! with
      | [_] => if grewAfter then newNumbers set seen else []
      | _ => newNumbers set seen
    let isSite := wasSite || visit.info.always || news.any fun number =>
      numbering.marks[number]! &&& visit.moved != 0 && relevant [numbering.named number] visit.info
    let first := isSite && !taken[position]!
    if news.isEmpty && !first then
      let site := if isSite != wasSite then site.set! slot isSite else site
      (⟨after.set! slot set, before, site, next, done, taken, ended, pending, numbering⟩, grewAfter || isSite != wasSite)
    else
    let done := done.set! position set
    let taken := if first then taken.set! position true else taken
    let gained := before[slot]!
    let before := before.set! slot ByteArray.empty
    let start := gained
    let (gained, numbering) :=
      if !isSite then ((union gained set).1, numbering)
      else if first then
        let (gained, _) := union gained visit.fixedBits
        addThrough visit gained numbering (newNumbers set ByteArray.empty)
      else addThrough visit gained numbering news
    let grewBefore := gained != start
    let before := before.set! slot gained
    let site := if isSite != wasSite then site.set! slot isSite else site
    let grew := isSite != wasSite || grewBefore || grewAfter
    let pending := if grewBefore then flag pending plan.readers[slot]! else pending
    let pending :=
      match plan.peers[slot]! with
      | [_] => pending
      | peers => if grew then flag pending (peers.filter (· != position)) else pending
    (⟨after.set! slot set, before, site, next, done, taken, ended, pending, numbering⟩, grew)

/-- One pass over visits from `position`, the ones that are pending. -/
private def livenessPass (plan : Plan) (criteria : ByteArray) : Nat → Nat → Tables → Bool → Tables × Bool
  | 0, _, tables, changed => (tables, changed)
  | count + 1, position, tables, changed =>
    if tables.pending[position]! then
      let (tables, grew) := livenessVisit plan criteria position tables
      livenessPass plan criteria count (position + 1) tables (changed || grew)
    else
      livenessPass plan criteria count (position + 1) tables changed

private def livenessFix (plan : Plan) (criteria : ByteArray) : Nat → Tables → Tables
  | 0, tables => tables
  | fuel + 1, tables =>
    let (tables, changed) := livenessPass plan criteria plan.code.size 0 tables false
    if changed then livenessFix plan criteria fuel tables else tables

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
        if site[slot]! then .site visit.insn.address
        else
          (plan.edges[slot]!).foldl (fun found target => Next.join found next[target]!)
            (if visit.ends then Next.exit else Next.never)
      if next[slot]! == found then
        nextPass plan site count (position + 1) next pending changed
      else
        let pending := flag pending plan.readers[slot]!
        let pending :=
          match plan.peers[slot]! with
          | [_] => pending
          | peers => flag pending (peers.filter (· != position))
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
    (plan.edges[visit.slot]!).all fun target => next[target]! != .conflict
  (if origins.isEmpty then all else origins).map (·.slot)

/-- Liveness and sites to a fixpoint, then what runs next; a choice that conflicts joins the sites,
and all of it again. Out of fuel, `check` finds the tables wanting. -/
private def solve (plan : Plan) (criteria : ByteArray) (passes : Nat) : Nat → Tables → Tables
  | 0, tables => tables
  | fuel + 1, tables =>
    let tables := livenessFix plan criteria passes tables
    let slots := plan.edges.size
    let next := nextFix plan tables.site passes (Array.replicate slots Next.never)
      (Array.replicate plan.code.size true)
    match conflicts plan next with
    | [] => { tables with next }
    | added =>
      let site := added.foldl (fun site slot => site.set! slot true) tables.site
      let pending := added.foldl (fun pending slot => flag pending plan.peers[slot]!) tables.pending
      solve plan criteria passes fuel { tables with next, site, pending }

/-- The visits after the ones they go to, as far as the edges let them: facts go backwards along edges, so most need only
one pass in this order. -/
private def postorder (visits : Array Visit) (slots : Std.HashMap Nat Nat) (count : Nat) : Array Visit :=
  let bySlot := visits.foldl (init := Array.replicate count ([] : List Nat)) fun state visit =>
    state.modify visit.slot fun list => if list.isEmpty then visit.next.map (slots.getD · 0) else list
  let roots := (Array.range visits.size).foldr (fun position roots => visits[position]!.slot :: roots) []
  let finished := go bySlot (2 * visits.size + (bySlot.foldl (fun sum list => sum + list.length) 0) + 2)
    (roots.map (·, false)) (Array.replicate count false) #[]
  let positions := visits.zipIdx.foldr (init := Array.replicate count ([] : List Nat)) fun visit positions =>
    positions.modify visit.1.slot (visit.2 :: ·)
  finished.foldl (init := #[]) fun out slot =>
    positions[slot]!.foldl (fun out position => out.push visits[position]!) out
where
  go (edges : Array (List Nat)) : Nat → List (Nat × Bool) → Array Bool → Array Nat → Array Nat
    | 0, _, _, out => out
    | fuel + 1, stack, seen, out =>
      match stack with
      | [] => out
      | (slot, true) :: rest => go edges fuel rest seen (out.push slot)
      | (slot, false) :: rest =>
        if seen[slot]! then go edges fuel rest seen out
        else go edges fuel (edges[slot]!.foldr (fun target stack => (target, false) :: stack) ((slot, true) :: rest))
          (seen.set! slot true) out

/-- Lays out what `solve` works on. -/
private def planOf (visits : Array Visit) (slots : Std.HashMap Nat Nat) (numbering : Numbering) (count : Nat) : Plan :=
  let edges := visits.foldl (init := Array.replicate count []) fun edges visit =>
    if edges[visit.slot]!.isEmpty then edges.set! visit.slot (visit.next.map (slots.getD · 0)) else edges
  let peers := visits.zipIdx.foldr (init := Array.replicate count []) fun visit peers =>
    peers.modify visit.1.slot (visit.2 :: ·)
  let readers := visits.zipIdx.foldr (init := Array.replicate count []) fun visit readers =>
    (edges[visit.1.slot]!).foldl (fun readers target => readers.modify target (visit.2 :: ·)) readers
  { code := visits, edges, readers, peers, numbering }

/-- The tables `solve` starts from. -/
private def startOf (plan : Plan) (criteria : List Location) : ByteArray × Tables :=
  let count := plan.edges.size
  let visits := plan.code.size
  let (bits, numbering) := criteria.foldl (init := (ByteArray.empty, plan.numbering)) fun state location =>
    let (number, numbering) := state.2.number location
    (addBit state.1 number, numbering)
  (bits,
   { after := Array.replicate count ByteArray.empty, before := Array.replicate count ByteArray.empty
     site := Array.replicate count false, next := Array.replicate count .never
     done := Array.replicate visits ByteArray.empty, taken := Array.replicate visits false
     ended := Array.replicate visits false, pending := Array.replicate visits true, numbering })

/-- The tables of a slice from what `solve` found. -/
private def numberedOf (slots : Std.HashMap Nat Nat) (tables : Tables) : Numbered :=
  let cells := (Array.range tables.site.size).map fun slot =>
    { site := tables.site[slot]!, before := tables.before[slot]!, after := tables.after[slot]!
      next := tables.next[slot]! : Cell }
  { slots, cells, locations := tables.numbering.locations, numbers := tables.numbering.numbers
    marks := tables.numbering.marks, marked := tables.numbering.marked }

/-- Whether `live` holds a location: says it, or, for bytes that go by a register, says all of the memory and the
register. -/
private def holds (live : List Location) (location : Location) : Bool :=
  live.contains location || match location with
    | .rel memory base _ _ => live.contains (.whole memory) && live.contains (.reg base)
    | _ => false

/-- The tables are a solution of the equations: this and nothing else is what soundness rests on. -/
private def checkInsn (entry : Nat → Entry) (next : List Nat) (criteria : List Location)
    (insn : Disasm.Insn) : Bool :=
  let here := entry insn.address
  next.all (fun target => (entry target).before.all here.after.contains) &&
  (!mayEnd insn next || criteria.all here.after.contains) &&
  (!relevant here.after (blockInfo insn.bil) || here.site) &&
  (if here.site then
    (insnBefore insn.bil here.after).all (holds here.before) && here.next == .site insn.address
  else
    here.after.all here.before.contains &&
    (!mayEnd insn next || here.next == .exit) &&
    next.all fun target => (entry target).next == here.next || (entry target).next == .never)

/-! `checkInsn` on the numbers, which implies it whatever the tables are: a number it finds in a set names the location
it looks at, and the rest is that a plain instruction takes what is live one location at a time. -/

/-- Whether `p` holds of every number below one. -/
@[specialize] private def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | count + 1 => p count && allBelow p count

/-- Whether `p` holds of every number in a set. -/
@[specialize] private def allIn (p : Nat → Bool) (set : ByteArray) : Bool :=
  allBelow (fun index =>
    let byte := set.get! index
    byte == 0 || allBelow (fun bit => (byte >>> UInt8.ofNat bit) &&& 1 == 0 || p (8 * index + bit)) 8) set.size

namespace Numbered

/-- Whether a set has a location, found by its number. -/
private def says (tables : Numbered) (set : ByteArray) (location : Location) : Bool :=
  match tables.numbers[location]? with
  | some number => has set number && tables.locations[number]? == some location
  | none => false

/-- `holds` on a set. -/
private def holdsIn (tables : Numbered) (set : ByteArray) (location : Location) : Bool :=
  tables.says set location || match location with
    | .rel memory base _ _ => tables.says set (.whole memory) && tables.says set (.reg base)
    | _ => false

/-- Whether a number names a location that a plain instruction does not assign. -/
private def untouched (tables : Numbered) (visit : Visit) (number : Nat) : Bool :=
  visit.plain && tables.marks.getD number 0 &&& visit.moved == 0

/-- `!relevant` of a set. -/
private def quiet (tables : Numbered) (visit : Visit) (set : ByteArray) : Bool :=
  !visit.info.always && allIn (fun number =>
    tables.untouched visit number ||
      match tables.locations[number]? with
      | some location => !relevant [location] visit.info
      | none => true) set

/-- What must agree before a visit, with `after` after it, is in `before`. -/
private def through (tables : Numbered) (visit : Visit) (after before : ByteArray) : Bool :=
  (visit.fixed.zip visit.fixedNumbers).all (fun pair =>
    (has before pair.2 && tables.locations[pair.2]? == some pair.1) || tables.holdsIn before pair.1) &&
  allIn (fun number =>
    if tables.marks.getD number 0 &&& visit.moved == 0 then has before number
    else match tables.locations[number]? with
      | some location => (imageAt visit location).all (tables.holdsIn before)
      | none => true) after

/-- `checkInsn` on the numbers. -/
private def check (tables : Numbered) (criteria : List Location) (visit : Visit) : Bool :=
  let here := tables.cell visit.insn.address
  visit.next.all (fun target => allIn (has here.after) (tables.cell target).before) &&
  (!visit.ends || criteria.all (tables.says here.after)) &&
  (here.site || tables.quiet visit here.after) &&
  (if here.site then
    tables.through visit here.after here.before && here.next == .site visit.insn.address
  else
    allIn (has here.before) here.after &&
    (!visit.ends || here.next == .exit) &&
    visit.next.all fun target => (tables.cell target).next == here.next || (tables.cell target).next == .never)

end Numbered

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

/-- What slices of one listing over one CFG have in common, for many criteria over it. -/
structure Prepared where
  instructions : List Disasm.Insn
  visits : List Visit
  plan : Plan
  slots : Std.HashMap Nat Nat
  listed : Std.HashMap Nat Unit
  memories : List Bap.Var
  statements : Nat
  /-- Whether the CFG describes the code, whatever is live. -/
  flows : Bool

/-- What a listing always reads, numbered. -/
private def baseNumbering (instructions : List Disasm.Insn) : Numbering :=
  instructions.foldl (init := {}) fun numbering insn =>
    (insnBefore insn.bil []).foldl (init := numbering) fun numbering location =>
      let known := numbering.numbers.contains location
      let numbering := (numbering.number location).2
      match location with
      | .rel memory base _ _ =>
        if known then numbering
        else { numbering with counts := numbering.counts.insert (memory, base) (numbering.counts.getD (memory, base) 0 + 1) }
      | _ => numbering

/-- The place in the tables of each address, and how many. -/
private def slotTable (instructions : List Disasm.Insn) : Std.HashMap Nat Nat × Nat :=
  instructions.reverse.foldl (init := ({}, 0)) fun state insn =>
    if state.1.contains insn.address then state else (state.1.insert insn.address state.2, state.2 + 1)

/-- Prepares `instructions` over the CFG `edges`. -/
def prepare (instructions : List Disasm.Insn) (edges : List (Nat × Nat)) : Prepared :=
  let successors := successorTable instructions edges
  let laid := slotTable instructions
  let slots := laid.1
  let count := laid.2
  let numbering := baseNumbering instructions
  let visits := instructions.map (visitOf slots successors numbering)
  let listed : Std.HashMap Nat Unit := instructions.foldl (fun table insn => table.insert insn.address ()) {}
  { instructions, visits, slots, listed
    plan := planOf (postorder visits.toArray slots count) slots numbering count
    memories := memories instructions
    statements := (instructions.map (·.bil.length)).sum
    flows := instructions.all fun insn =>
      checkEdges (listed.contains ·) (successors.getD insn.address []) insn && checkFlow insn }

/-- What tables say, whatever found them. -/
private def resultOf (prepared : Prepared) (entry : Option Nat) (criteria : List Location) (tables : Numbered)
    (widened : Bool) : Result :=
  let determined := prepared.flows &&
    prepared.visits.all (fun visit => !(tables.cell visit.insn.address).site || !visit.info.dynamic) &&
    prepared.visits.all fun visit =>
      tables.check criteria visit || checkInsn tables.entry visit.next criteria visit.insn
  let calls := (prepared.instructions.filter fun insn =>
    insn.flow = .call && !(tables.setOf (tables.cell insn.address).after).isEmpty).map (·.address)
  {
    sites := (prepared.instructions.filter fun insn => (tables.cell insn.address).site).map (·.address)
    live := match entry <|> prepared.instructions.head?.map (·.address) with
      | some address => if prepared.listed.contains address then (tables.entry address).before else criteria
      | none => criteria
    determined
    calls
    complete := determined && calls.isEmpty
    widened
    tables
  }

/-- Slices what is prepared, as of `entry`. An instruction is a site if it writes something live after it, or if what
runs next depends on it: `Result.nextSite` tells what follows an address if not a site, and a choice between different
next sites is a site. -/
def Prepared.slice (prepared : Prepared) (entry : Option Nat) (criteria : List Location) : Result :=
  let criteria := expandWith prepared.memories criteria
  let count := prepared.instructions.length
  let passes := 4 * (count + 2) * (criteria.length + prepared.statements + 2)
  let start := startOf prepared.plan criteria
  let found := solve prepared.plan start.1 passes (count + 1) start.2
  resultOf prepared entry criteria (numberedOf prepared.slots found) found.numbering.widened

/-- Slices `instructions` over the CFG `edges`, as of `entry`. -/
def backwardCfg (instructions : List Disasm.Insn) (edges : List (Nat × Nat)) (entry : Option Nat)
    (criteria : List Location) : Result :=
  (prepare instructions edges).slice entry criteria

/-- The edges of each instruction, as its flow tells them. -/
def flowEdges (instructions : List Disasm.Insn) : List (Nat × Nat) :=
  instructions.flatMap fun insn => insn.successors.map (insn.address, ·)

/-- Slices `instructions` over the control flow their `flow` and `target` give, from the first. -/
def backward (instructions : List Disasm.Insn) (criteria : List Location) : Result :=
  backwardCfg instructions (flowEdges instructions) none criteria

/-! Slices of the functions of a project. -/

/-- The elements of a list that have a key, by key, each in the order of the list. -/
private def groupBy {α : Type} (key : α → Option Nat) (list : List α) : Std.HashMap Nat (List α) :=
  list.foldr (fun element groups =>
    match key element with
    | some found => groups.insert found (element :: groups.getD found [])
    | none => groups) {}

/-- The function an address is in, if any. -/
def ownerOf (index : Xrefs.Index) (address : Nat) : Option Nat :=
  (Xrefs.functionOf index address).map Image.Symbol.addr

/-- What `prepare` makes of a function, once it is needed, by the address of the function. -/
structure ProjectPlan where
  index : Xrefs.Index
  edges : Std.HashMap Nat (List (Nat × Nat))
  functions : Std.HashMap Nat (Thunk Prepared)
  all : Thunk Prepared

/-- Prepares the functions of a project: criteria and entries over one project take from here. -/
def prepareProject (project : Project.Project) : ProjectPlan :=
  let index := Xrefs.create project
  let instructions := (project.disasm.map (·.instructions)).getD []
  let cfg := (project.disasm.map (·.edges)).getD []
  let edges := groupBy (fun edge => ownerOf index edge.1) cfg
  { index, edges
    functions := (groupBy (fun insn => ownerOf index insn.address) instructions).map fun owner listed =>
      Thunk.mk fun _ => prepare listed (edges.getD owner [] ++ flowEdges listed)
    all := Thunk.mk fun _ => prepare instructions (cfg ++ flowEdges instructions) }

/-- What is prepared for the function of `entry`, or the whole listing if no function has it. -/
def ProjectPlan.prepared (plan : ProjectPlan) (entry : Nat) : Prepared :=
  match ownerOf plan.index entry with
  | some owner =>
    match plan.functions[owner]? with
    | some prepared => prepared.get
    | none => prepare [] (plan.edges.getD owner [] ++ flowEdges [])
  | none => plan.all.get

/-- Slices the function of `entry`, or the whole listing if no function has it, over the CFG of the project. An edge the
flow of an instruction gives counts even if the disassembly left it out. -/
def ProjectPlan.slice (plan : ProjectPlan) (entry : Nat) (criteria : List Location) : Result :=
  (plan.prepared entry).slice (some entry) criteria

/-- `ProjectPlan.slice` for one slice. -/
def backwardProject (project : Project.Project) (entry : Nat) (criteria : List Location) : Result :=
  (prepareProject project).slice entry criteria

end Bap.Analysis.Slice
