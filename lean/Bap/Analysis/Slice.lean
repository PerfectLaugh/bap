import Bap.Analysis.Xrefs
import Std.Data.HashMap

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

/-- The union of two sets kept as lists, the first in its order. -/
private def addAll (live additions : List Location) : List Location :=
  additions.foldl (fun live location => if live.contains location then live else location :: live) live

/-- One backward pass over the sites and liveness: an instruction joins the sites when it writes
something live after it, and the tables only ever grow. Returns whether anything changed. -/
private def livenessPass (code : List Disasm.Insn) (successors : Std.HashMap Nat (List Nat))
    (criteria : List Location) (table : Std.HashMap Nat Entry) : Std.HashMap Nat Entry × Bool :=
  code.foldl (init := (table, false)) fun state insn =>
    let (table, changed) := state
    let entry := table.getD insn.address {}
    let next := successors.getD insn.address []
    let after := next.foldl (fun live target => addAll live (table.getD target {}).before) entry.after
    let after := if mayEnd insn next then addAll after criteria else after
    let site := entry.site || relevant after (blockInfo insn.bil)
    let before := addAll entry.before (if site then insnBefore insn.bil after else after)
    let grew := site != entry.site || before.length != entry.before.length || after.length != entry.after.length
    (table.insert insn.address { entry with site, before, after }, changed || grew)

private def livenessFix (code : List Disasm.Insn) (successors : Std.HashMap Nat (List Nat))
    (criteria : List Location) : Nat → Std.HashMap Nat Entry → Std.HashMap Nat Entry
  | 0, table => table
  | fuel + 1, table =>
    let (table, changed) := livenessPass code successors criteria table
    if changed then livenessFix code successors criteria fuel table else table

/-- One backward pass of what runs next, given the sites. -/
private def nextPass (code : List Disasm.Insn) (successors : Std.HashMap Nat (List Nat))
    (table : Std.HashMap Nat Entry) : Std.HashMap Nat Entry × Bool :=
  code.foldl (init := (table, false)) fun state insn =>
    let (table, changed) := state
    let entry := table.getD insn.address {}
    if entry.site then
      let next := .site insn.address
      (table.insert insn.address { entry with next }, changed || entry.next != next)
    else
      let targets := successors.getD insn.address []
      let start := if mayEnd insn targets then Next.exit else Next.never
      let next := targets.foldl (fun next target => Next.join next (table.getD target {}).next) start
      (table.insert insn.address { entry with next }, changed || entry.next != next)

private def nextFix (code : List Disasm.Insn) (successors : Std.HashMap Nat (List Nat)) :
    Nat → Std.HashMap Nat Entry → Std.HashMap Nat Entry
  | 0, table => table
  | fuel + 1, table =>
    let (table, changed) := nextPass code successors table
    if changed then nextFix code successors fuel table else table

/-- The choices that have to become sites: where what runs next depends on the path taken. Those whose
successors agree on no conflict come first, as making them sites may settle the ones before them. -/
private def conflicts (code : List Disasm.Insn) (successors : Std.HashMap Nat (List Nat))
    (table : Std.HashMap Nat Entry) : List Nat :=
  let all := code.filter fun insn => (table.getD insn.address {}).next == .conflict
  let origins := all.filter fun insn =>
    (successors.getD insn.address []).all fun target => (table.getD target {}).next != .conflict
  (if origins.isEmpty then all else origins).map (·.address)

/-- Liveness and sites to a fixpoint, then what runs next; a choice that conflicts joins the sites,
and all of it again. Out of fuel, `check` finds the tables wanting. -/
private def solve (code : List Disasm.Insn) (successors : Std.HashMap Nat (List Nat))
    (criteria : List Location) (passes : Nat) : Nat → Std.HashMap Nat Entry → Std.HashMap Nat Entry
  | 0, table => table
  | fuel + 1, table =>
    let table := livenessFix code successors criteria passes table
    let cleared := code.foldl (fun table insn =>
      table.insert insn.address { table.getD insn.address {} with next := .never }) table
    let table := nextFix code successors passes cleared
    match conflicts code successors table with
    | [] => table
    | added =>
      let table := added.foldl (fun table address =>
        table.insert address { table.getD address {} with site := true }) table
      solve code successors criteria passes fuel table

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

/-- Every constant jump into the listing is an edge of the CFG, or the CFG does not describe the code. -/
private def checkEdges (listed : Nat → Bool) (next : List Nat) (insn : Disasm.Insn) : Bool :=
  insn.flow == .call || (codeExits insn.bil).targets.all fun target => next.contains target || !listed target

/-- An indirect jump goes anywhere, and the CFG has no edges for it. -/
private def checkFlow (insn : Disasm.Insn) : Bool := insn.flow != .indirectJump

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
  let table := solve code successors criteria passes (instructions.length + 1) {}
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
