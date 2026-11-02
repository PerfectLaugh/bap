import Bap.Emu.Tasks
import Bap.Linux.Wire

/-! Where each byte of a run came from, as it runs. A static slice has to say that a store through a pointer it doesn't know may be
anywhere, which is how it comes to all of memory: here the address is known, so that a byte has one producer.

Every byte of memory, by address space, and of a register, by thread, has a tag. It says what last produced the byte: a *node* of a graph
of what depends on what, or, for a byte that nothing marked has reached, just the instruction that computed it. So a run costs memory only
for what depends on a source. A node is one assignment or store, with what each of its bytes came from, by the byte. Bytes follow
registers, memory, extracts, shifts by whole bytes, masks and vector operations by the byte, and a carry only goes up.

An edge says how: `data`, `address` for a byte reached through a pointer or a table that depends on a source, `condition` for a selection
such as `csel`, and `guard`. A constant has no data behind it, and a `'1'` that a check chose comes from the branch that the check
took, which is what an implicit flow is. There is no postdominator to say where a branch stops mattering in a run through flattened code, so
a *guard* lasts for `guardWindow` instructions of its thread and until its function returns, and it is what is likely, not what is proved. It reaches constants, and clean
bytes narrower than a word that are stored, as a saved register is a word and says nothing. A branch on what depends on nothing is not a guard, which is what
a dispatcher of flattened code on a clean state is.

The bytes of a shared mapping have their tag by file and offset, so that they are the same in every process. A copy that doesn't change a byte
leaves it its tag in a register, and has a node in memory, which is where the way it took shows.

What it can't see: flags that an intrinsic of floating point raises, what the kernel keeps of a write, and registers restored by `sigreturn`,
which keep what they had. A file is a source by what is read from it, whatever a program wrote to it before. -/

namespace Bap.Analysis.DynamicTaint

open Bap.Emu (Emu ThreadId)

inductive Edge where
  | data | address | condition | guard
  deriving DecidableEq, Repr, Inhabited

/-- What produced a byte. 0 is that nothing here has, an odd number is a clean byte of the instruction at half of it, and an even one is a byte of a node. -/
abbrev Tag := Nat

def cleanTag (pc : Nat) : Tag := 2 * pc + 1
def nodeTag (id byte : Nat) : Tag := 2 * ((id + 1) * 4096 + byte)
def Tag.isNode (tag : Tag) : Bool := tag != 0 && tag % 2 == 0
def Tag.isClean (tag : Tag) : Bool := tag % 2 == 1
def Tag.node (tag : Tag) : Nat := tag / 2 / 4096 - 1
def Tag.byte (tag : Tag) : Nat := tag / 2 % 4096

structure Input where
  tag : Tag
  edge : Edge
  deriving DecidableEq, Repr, Inhabited

inductive NodeKind where
  /-- What came in from outside, as it was called, and where in what it came from each byte of the node starts. -/
  | source (label : String) (offset : Option Nat)
  | copy
  | compute
  /-- A constant, or a clean byte, that a branch chose. -/
  | constant
  | branch (target : Option Nat)
  deriving DecidableEq, Repr, Inhabited

inductive Place where
  | register (name : String)
  | memory (address : Nat)
  | control
  deriving DecidableEq, Repr, Inhabited

structure Node where
  id : Nat
  /-- How many instructions it is since tracking started, of all threads. -/
  insn : Nat
  pc : Nat
  thread : ThreadId
  space : Nat
  kind : NodeKind
  place : Place
  /-- What it is, by the byte: of a register from the least significant, and of memory from its address up. Absent when it can't be known. -/
  values : List (Option UInt8)
  inputs : Array (List Input)
  guard : Option Tag := none
  deriving Repr, Inhabited

structure Config where
  /-- How many instructions of a thread a branch on a tainted condition guards what comes after it. -/
  guardWindow : Nat := 64
  /-- How many nodes are kept, of which the oldest half goes when they run out. What led to it is then missing, and says so. -/
  capacity : Nat := 4000000
  /-- What a system call is called as a source, with where it reads from if that means something: none if it is no source. -/
  describe : Nat → List Nat → IO (Option (String × Option Nat)) := fun number _ => pure (some (s!"syscall {number}", none))
  /-- What sees a call and its result, such as to know what was opened. -/
  called : Nat → List Nat → Option Nat → IO Unit := fun _ _ _ => pure ()

structure Tracker where
  emu : Emu
  config : Config
  nodes : IO.Ref (Array Node)
  /-- The id of the first node that is still there. -/
  base : IO.Ref Nat
  insn : IO.Ref Nat
  registers : IO.Ref (Std.HashMap ThreadId (Std.HashMap String (Array Tag)))
  pages : IO.Ref (Std.HashMap (Nat × Nat) (Array Tag))
  /-- The last branch on what is tainted of each thread, when it was and how many calls deep. -/
  guards : IO.Ref (Std.HashMap ThreadId (Tag × Nat × Nat))
  /-- Where each thread's calls go back to, the innermost first. -/
  calls : IO.Ref (Std.HashMap ThreadId (List Nat))
  /-- Which thread last ran of each process, for what a new thread starts with. -/
  lastOfGroup : IO.Ref (Std.HashMap Nat ThreadId)
  programs : IO.Ref (Std.HashMap Nat (ByteArray × Bil.Program))
  /-- What was called, with its number and arguments, for a call in progress, and how it is called if it is a source. -/
  calling : IO.Ref (Option (Nat × List Nat))
  label : IO.Ref (Option (String × Option Nat))
  /-- How many bytes of what the current call read have gone by. -/
  written : IO.Ref Nat
  /-- Where instructions were that this couldn't follow all of, with how many times. -/
  gaps : IO.Ref (Std.HashMap Nat Nat)

/-! ### Shades: what a value being computed came from -/

/-- What a byte of a value being computed came from. `origin` is the tag of a clean byte that hasn't changed, and `copied` says that the byte is
the byte of the one input or origin that it has. A `literal` depends on nothing at all. -/
structure Byte where
  inputs : List Input := []
  origin : Tag := 0
  copied : Bool := false
  literal : Bool := false
  deriving Inhabited

abbrev Shade := Array Byte

private def bytesOf (width : Nat) : Nat := (width + 7) / 8

private def union (left right : List Input) : List Input :=
  right.foldl (fun out input => if out.contains input then out else out ++ [input]) left

private def combine (left right : Byte) : Byte :=
  { inputs := union left.inputs right.inputs, literal := left.literal && right.literal }

private def changed (byte : Byte) : Byte := { inputs := byte.inputs, literal := byte.literal }

private def ofTag (tag : Tag) : Byte :=
  if tag.isNode then { inputs := [{ tag, edge := .data }], copied := true }
  else { origin := tag, copied := true }

private def literalShade (width : Nat) : Shade := Array.replicate (bytesOf width) { literal := true }

private def opaqueShade (width : Nat) : Shade := Array.replicate (bytesOf width) {}

/-- All that a shade has, as the inputs of something that depends on all of it. -/
private def allInputs (shade : Shade) : List Input :=
  shade.foldl (fun out byte => union out byte.inputs) []

private def isLiteral (shade : Shade) : Bool := shade.all (·.literal)

/-- The same inputs, by another edge, and what they add to each byte of a shade. -/
private def withInputs (edge : Edge) (inputs : List Input) (shade : Shade) : Shade :=
  if inputs.isEmpty then shade else
    let again := inputs.map fun input => { input with edge }
    shade.map fun byte => { inputs := union byte.inputs again }

private def byteAt (shade : Shade) (index : Nat) : Byte := shade.getD index {}

/-- Each byte has what is at it and below it of both, as a carry goes up. -/
private def carrying (left right : Shade) (size : Nat) : Shade :=
  let (_, out) := (List.range size).foldl (init := (({} : Byte), (#[] : Shade))) fun (below, out) index =>
    let byte := combine (combine (byteAt left index) (byteAt right index)) below
    (byte, out.push byte)
  out

/-- Each byte has all that both have. -/
private def everything (left right : Shade) (size : Nat) : Shade :=
  let both : Byte := { inputs := union (allInputs left) (allInputs right), literal := isLiteral left && isLiteral right }
  Array.replicate size both

private def bitsValue (bits : Option (Σ width, BitVec width)) : Option Nat := bits.map (·.2.toNat)

private def byteOfValue (value index : Nat) : Nat := (value >>> (8 * index)) % 256

/-- What a shift by a known amount does: a byte comes from the one or two that it overlaps. -/
private def shifted (shade : Shade) (size amount : Nat) (up : Bool) (arithmetic : Bool) : Shade :=
  let whole := amount / 8
  let part := amount % 8
  let source (index : Nat) : Byte :=
    if up then
      if index < whole then { literal := true } else byteAt shade (index - whole)
    else
      if index + whole < size then byteAt shade (index + whole)
      else if arithmetic then changed (byteAt shade (size - 1)) else { literal := true }
  (Array.range size).map fun index =>
    if part == 0 then source index
    else
      let next := if up then (if index ≥ whole + 1 then byteAt shade (index - whole - 1) else { literal := true })
        else if index + whole + 1 < size then byteAt shade (index + whole + 1)
        else if arithmetic then byteAt shade (size - 1) else { literal := true }
      combine (source index) next

/-- A byte of a value under one that nothing marked reached and that is known: what that decides depends on nothing, and what it leaves stays what it was. -/
private def underMask (op : Bil.BinOp) (byte : Byte) (part : Nat) : Byte :=
  match op with
  | .and =>
    if part == 0 then { literal := true }
    else if part == 255 then byte else changed byte
  | .or =>
    if part == 255 then { literal := true }
    else if part == 0 then byte else changed byte
  | _ => if part == 0 then byte else changed byte

/-- `and`, `or` and `xor`, which go by the byte, with either side as a mask wherever that is clean. -/
private def bitwise (op : Bil.BinOp) (left right : Shade) (leftValue rightValue : Option Nat) (size : Nat) : Shade :=
  (Array.range size).map fun index =>
    let l := byteAt left index
    let r := byteAt right index
    match l.inputs.isEmpty, leftValue, r.inputs.isEmpty, rightValue with
    | true, some value, false, _ => underMask op r (byteOfValue value index)
    | false, _, true, some value => underMask op l (byteOfValue value index)
    | _, _, _, _ => combine l r

private def isClean (shade : Shade) : Bool := shade.all (·.inputs.isEmpty)

private def binShade (op : Bil.BinOp) (leftExp rightExp : Bil.Exp) (left right : Shade)
    (leftBits rightBits : Option (Σ width, BitVec width)) (width : Nat) : Shade :=
  let size := bytesOf width
  match op with
  | .xor | .sub =>
    -- `eor x, x` is a zero whatever `x` is, and `xor` otherwise goes by the byte.
    if leftExp == rightExp then literalShade width
    else if op == .xor then bitwise op left right (bitsValue leftBits) (bitsValue rightBits) size
    else carrying left right size
  | .and | .or => bitwise op left right (bitsValue leftBits) (bitsValue rightBits) size
  | .add | .mul => carrying left right size
  | .lshift | .rshift | .ashift =>
    match isClean right, bitsValue rightBits with
    | true, some amount => shifted left size amount (op == .lshift) (op == .ashift)
    | _, _ => everything left right size
  | _ => everything left right size

/-- A value of a width as another: what is new of it is a copy of the top for a signed cast, and otherwise is nothing. -/
private def castShade (kind : Bil.Cast) (width : Nat) (value : Shade) (from_ : Nat) : Shade :=
  let size := bytesOf width
  match kind with
  | .low => (Array.range size).map (byteAt value)
  | .high =>
    let dropped := from_ - width
    if dropped % 8 == 0 then (Array.range size).map fun index => byteAt value (index + dropped / 8)
    else (shifted value (bytesOf from_) dropped false false).extract 0 size
  | .unsigned => (Array.range size).map fun index => if index < value.size then byteAt value index else { literal := true }
  | .signed =>
    (Array.range size).map fun index =>
      if index < value.size then byteAt value index else changed (byteAt value (value.size - 1))

private def extractShade (high low : Nat) (value : Shade) : Shade :=
  let width := high + 1 - low
  let size := bytesOf width
  if low % 8 == 0 then (Array.range size).map fun index => byteAt value (index + low / 8)
  else
    (Array.range size).map fun index =>
      let first := (low + index * 8) / 8
      let last := min high (low + index * 8 + 7) / 8
      (List.range (last + 1 - first)).foldl (fun out offset => combine out (byteAt value (first + offset))) {}

/-! ### Tags -/

namespace Tracker

private def keyOf (tracker : Tracker) (space address : Nat) : IO (Nat × Nat) := do
  match ← tracker.emu.futexKey.get with
  | some key =>
    match ← key address with
    | some found => pure found
    | none => pure (space, address)
  | none => pure (space, address)

private def tagAt (tracker : Tracker) (space address : Nat) : IO Tag := do
  let (space, address) ← keyOf tracker space address
  match (← tracker.pages.get)[(space, address / 4096)]? with
  | some page => pure (page.getD (address % 4096) 0)
  | none => pure 0

private def setTag (tracker : Tracker) (space address : Nat) (tag : Tag) : IO Unit := do
  let (space, address) ← keyOf tracker space address
  tracker.pages.modify fun pages =>
    let key := (space, address / 4096)
    let page := pages.getD key (Array.replicate 4096 0)
    pages.insert key (page.setIfInBounds (address % 4096) tag)

/-- What a thread that hasn't run yet has in its registers is what the last thread of its parent had. -/
private def registersOf (tracker : Tracker) (thread : ThreadId) : IO (Std.HashMap String (Array Tag)) := do
  let registers ← tracker.registers.get
  if let some found := registers[thread]? then return found
  let table ← tracker.emu.taskTable.get
  let inherited ← match table.find? thread with
    | some task =>
      let groups ← tracker.lastOfGroup.get
      pure ((groups[task.group]?.orElse fun _ => groups[task.parent]?).bind fun other => registers[other]?)
    | none => pure none
  let found := inherited.getD {}
  tracker.registers.modify (·.insert thread found)
  pure found

private def push (tracker : Tracker) (node : Node) : IO Unit := do
  tracker.nodes.modify (·.push node)
  if (← tracker.nodes.get).size > tracker.config.capacity then
    let half := tracker.config.capacity / 2
    tracker.nodes.modify fun nodes => nodes.extract half nodes.size
    tracker.base.modify (· + half)

private def nextId (tracker : Tracker) : IO Nat := do
  pure ((← tracker.base.get) + (← tracker.nodes.get).size)

private def gap (tracker : Tracker) (pc : Nat) : IO Unit :=
  tracker.gaps.modify fun gaps => gaps.insert pc (gaps.getD pc 0 + 1)

def node? (tracker : Tracker) (id : Nat) : IO (Option Node) := do
  let base ← tracker.base.get
  if id < base then return none
  pure (← tracker.nodes.get)[id - base]?

/-! ### Following an instruction -/

/-- Bytes of an instruction that have happened as far as it knows, until they all have. -/
private structure Frame where
  pc : Nat
  thread : ThreadId
  space : Nat
  insn : Nat
  env : Bil.Env
  /-- Whether it goes somewhere else whatever it does, as a call: what it writes then is its own and isn't chosen by a branch. -/
  jumps : Bool
  variables : IO.Ref (Std.HashMap Bap.Var (Option (Σ width, BitVec width) × Shade))
  memory : IO.Ref (Std.HashMap Nat UInt8)
  tags : IO.Ref (Std.HashMap Nat Tag)
  regionsNow : List Emu.Region
  newNodes : IO.Ref (Array Node)
  firstId : Nat
  newRegisters : IO.Ref (List (String × Array Tag))
  newGuard : IO.Ref (Option Tag)
  incomplete : IO.Ref Bool
  operands : IO.Ref (List Input)
  depth : Nat
  /-- Where a call that this instruction makes comes back to, which it leaves as a constant, where a target has it. -/
  link : IO.Ref (Option Nat)
  jumped : IO.Ref Bool

private def faultMessage : String := "dynamic taint: this instruction faults"

private def nodeIdOf (frame : Frame) : IO Nat := do
  pure (frame.firstId + (← frame.newNodes.get).size)

private def activeGuard (tracker : Tracker) (frame : Frame) : IO (Option Tag) := do
  if let some tag := ← frame.newGuard.get then return some tag
  match (← tracker.guards.get)[frame.thread]? with
  | some (tag, at_, depth) =>
    pure (if frame.insn - at_ ≤ tracker.config.guardWindow && depth ≤ frame.depth then some tag else none)
  | none => pure none

private def loadBytes (tracker : Tracker) (frame : Frame) (address size : Nat) : IO (ByteArray × Array Tag) := do
  let overlay ← frame.memory.get
  let tags ← frame.tags.get
  let mut bytes := ByteArray.emptyWithCapacity size
  let mut out : Array Tag := #[]
  let raw ← Emu.peek tracker.emu address size
  for offset in List.range size do
    let at_ := address + offset
    match Emu.lookupRegion frame.regionsNow at_ with
    | some region => if !region.protection.readable then throw (IO.userError faultMessage)
    | none => throw (IO.userError faultMessage)
    bytes := bytes.push (overlay.getD at_ (raw.get! offset))
    out := out.push (← match tags[at_]? with
      | some tag => pure tag
      | none => tagAt tracker frame.space at_)
  pure (bytes, out)

/-- A node for what has its bytes as given, if any of them needs one, and what each byte is now. A byte that stays a copy keeps the tag it had in a
register. In memory a copy has a node, as that is the way it took. -/
private def assign (tracker : Tracker) (frame : Frame) (place : Place) (shade : Shade) (values : List (Option UInt8))
    (literalGuarded : Bool) (narrowGuarded : Bool) : IO (Array Tag) := do
  let id ← nodeIdOf frame
  let guard ← activeGuard tracker frame
  let inMemory := match place with | .memory _ => true | _ => false
  let mut tags : Array Tag := #[]
  let mut inputs : Array (List Input) := #[]
  let mut needed := false
  let mut allCopies := true
  let mut guarded := false
  for index in List.range shade.size do
    let byte := byteAt shade index
    let clean := byte.inputs.isEmpty
    if clean then
      let chosen := guard.isSome && ((byte.literal && literalGuarded) || (!byte.literal && narrowGuarded))
      if chosen then
        tags := tags.push (nodeTag id index)
        inputs := inputs.push []
        needed := true
        guarded := true
      else
        tags := tags.push (if byte.copied && byte.origin != 0 then byte.origin else cleanTag frame.pc)
        inputs := inputs.push []
    else
      let single := match byte.inputs with
        | [{ edge := .data, .. }] => byte.copied
        | _ => false
      if single && !inMemory then
        tags := tags.push (byte.inputs.head?.map (·.tag) |>.getD 0)
        inputs := inputs.push []
      else
        if !single then allCopies := false
        tags := tags.push (nodeTag id index)
        inputs := inputs.push byte.inputs
        needed := true
  if needed then
    let kind : NodeKind := if guarded && inputs.all List.isEmpty then .constant else if allCopies then .copy else .compute
    frame.newNodes.modify (·.push {
      id, insn := frame.insn, pc := frame.pc, thread := frame.thread, space := frame.space, kind, place, values, inputs
      guard := if guarded then guard else none })
  pure tags

private def valueBytes (bits : Option (Σ width, BitVec width)) (size : Nat) : List (Option UInt8) :=
  (List.range size).map fun index => (bitsValue bits).map fun value => UInt8.ofNat (byteOfValue value index)

private def constantly (exp : Bil.Exp) : Option (Σ width, BitVec width) :=
  match Bil.evalExp [] exp with
  | .ok value => (Bap.Value.asBits value).toOption
  | .error _ => none

private def isTemporary (var : Bap.Var) : Bool :=
  var.isVirtual || var.name.startsWith "intrinsic:" || var.name.startsWith "#" || var.name.startsWith "_primus_"

/-- Whether what an instruction leaves may be where a call comes back to: just after it, in a word or two. It is a call if it then jumps. -/
private def noteLink (frame : Frame) (bits : Option (Σ width, BitVec width)) : IO Unit := do
  if let some value := bitsValue bits then
    if frame.pc < value && value ≤ frame.pc + 32 then frame.link.set (some value)

private def widthOfTyp : Typ → Nat
  | .imm width => width
  | _ => 0

private def lookupVariable (tracker : Tracker) (frame : Frame) (var : Bap.Var) : IO (Option (Σ width, BitVec width) × Shade) := do
  if let some found := (← frame.variables.get)[var]? then return found
  let width := widthOfTyp var.typ
  let bits := match Bil.lookup frame.env var with
    | .ok value => (Bap.Value.asBits value).toOption
    | .error _ => none
  let tags := ((← registersOf tracker frame.thread).get? var.name).getD (Array.replicate (bytesOf width) (0 : Tag))
  pure (bits, tags.map ofTag)

mutual

private partial def evaluate (tracker : Tracker) (frame : Frame) : Bil.Exp → IO (Option (Σ width, BitVec width) × Shade)
  | @Bil.Exp.int width value => pure (some ⟨width, value⟩, literalShade width)
  | .var var => lookupVariable tracker frame var
  | .unknown _ typ => pure (none, opaqueShade (widthOfTyp typ))
  | .letIn var value body => do
    let bound ← evaluate tracker frame value
    let before := (← frame.variables.get)[var]?
    frame.variables.modify (·.insert var bound)
    let result ← evaluate tracker frame body
    frame.variables.modify fun variables => match before with
      | some previous => variables.insert var previous
      | none => variables.erase var
    pure result
  | .ite condition yes no => do
    let (bits, shade) ← evaluate tracker frame condition
    let inputs := allInputs shade
    match bitsValue bits with
    | some value =>
      let (result, chosen) ← evaluate tracker frame (if value != 0 then yes else no)
      pure (result, withInputs .condition inputs chosen)
    | none =>
      let (_, first) ← evaluate tracker frame yes
      let (_, second) ← evaluate tracker frame no
      pure (none, withInputs .condition inputs ((Array.range first.size).map fun index => combine (byteAt first index) (byteAt second index)))
  | .un op value => do
    let (bits, shade) ← evaluate tracker frame value
    let result := bits.bind fun bits => constantly (.un op (.int bits.2))
    match op with
    | .not => pure (result, shade.map changed)
    | .neg => pure (result, carrying shade shade shade.size)
  | .bin op left right => do
    let (leftBits, leftShade) ← evaluate tracker frame left
    let (rightBits, rightShade) ← evaluate tracker frame right
    let value := match leftBits, rightBits with
      | some l, some r =>
        match Bil.evalBin op l r with
        | .ok result => (Bap.Value.asBits result).toOption
        | .error _ => none
      | _, _ => none
    let size := max leftShade.size rightShade.size
    let width := match value with
      | some bits => bits.1
      | none => size * 8
    let compares := match op with
      | .eq | .neq | .lt | .le | .gt | .ge | .slt | .sle | .sgt | .sge => true
      | _ => false
    if compares then
      pure (value, #[{ inputs := union (allInputs leftShade) (allInputs rightShade), literal := isLiteral leftShade && isLiteral rightShade }])
    else
      pure (value, binShade op left right leftShade rightShade leftBits rightBits width)
  | .cast kind width value => do
    let (bits, shade) ← evaluate tracker frame value
    let from_ := match bits with
      | some bits => bits.1
      | none => shade.size * 8
    pure (bits.bind (fun bits => constantly (.cast kind width (.int bits.2))), castShade kind width shade from_)
  | .extract high low value => do
    let (bits, shade) ← evaluate tracker frame value
    pure (bits.bind (fun bits => constantly (.extract high low (.int bits.2))), extractShade high low shade)
  | .concat left right => do
    let (leftBits, leftShade) ← evaluate tracker frame left
    let (rightBits, rightShade) ← evaluate tracker frame right
    let value := match leftBits, rightBits with
      | some l, some r => constantly (.concat (.int l.2) (.int r.2))
      | _, _ => none
    let lowWidth := match rightBits with
      | some bits => bits.1
      | none => rightShade.size * 8
    if lowWidth % 8 == 0 then pure (value, rightShade ++ leftShade)
    else
      let size := (rightShade.size + leftShade.size)
      pure (value, everything leftShade rightShade size)
  | .load memory address endian size => do
    let _ ← evaluate tracker frame memory
    let (addressBits, addressShade) ← evaluate tracker frame address
    let inputs := allInputs addressShade
    match bitsValue addressBits with
    | none =>
      frame.incomplete.set true
      pure (none, withInputs .address inputs (opaqueShade (size * 8)))
    | some at_ =>
      let (bytes, tags) ← loadBytes tracker frame at_ size
      let inOrder := match endian with | .little => (List.range size) | .big => (List.range size).reverse
      let value := inOrder.foldr (fun index total => total * 256 + (bytes.get! index).toNat) 0
      let shade := (inOrder.map fun index => ofTag (tags.getD index 0)).toArray
      pure (some ⟨size * 8, BitVec.ofNat (size * 8) value⟩, withInputs .address inputs shade)
  | .store memory address value endian size => do
    let _ ← evaluate tracker frame memory
    let (addressBits, addressShade) ← evaluate tracker frame address
    let (bits, shade) ← evaluate tracker frame value
    let inputs := allInputs addressShade
    noteLink frame bits
    match bitsValue addressBits with
    | none => frame.incomplete.set true
    | some at_ =>
      for offset in List.range size do
        match Emu.lookupRegion frame.regionsNow (at_ + offset) with
        | some region => if !region.protection.writable then throw (IO.userError faultMessage)
        | none => throw (IO.userError faultMessage)
      -- From the address up, as a node of memory has it.
      let raw := withInputs .address inputs shade
      let bySignificance := valueBytes bits size
      let ordered : Shade := match endian with
        | .little => (Array.range size).map (byteAt raw)
        | .big => (Array.range size).map fun index => byteAt raw (size - 1 - index)
      let values := match endian with
        | .little => bySignificance
        | .big => bySignificance.reverse
      let word := (← Emu.wordWidth tracker.emu) / 8
      let tags ← assign tracker frame (.memory at_) ordered values (!frame.jumps) (size < word)
      for offset in List.range size do
        frame.tags.modify (·.insert (at_ + offset) (tags.getD offset 0))
        if let some byte := values.getD offset none then
          frame.memory.modify (·.insert (at_ + offset) byte)
    pure (none, #[])

private partial def perform (tracker : Tracker) (frame : Frame) : Nat → Bil.Program → IO Bool
  | 0, _ => do
    frame.incomplete.set true
    pure false
  | _ + 1, [] => pure true
  | fuel + 1, stmt :: rest => do
    match stmt with
    | .move var value =>
      let (bits, shade) ← evaluate tracker frame value
      noteLink frame bits
      if var == tracker.emu.config.memory then
        pure ()
      else if isTemporary var then
        if var.name.startsWith "intrinsic:x" then
          frame.operands.modify (union · (allInputs shade))
        frame.variables.modify (·.insert var (bits, shade))
      else
        let width := widthOfTyp var.typ
        let size := bytesOf width
        let sized := (Array.range size).map (byteAt shade)
        let tags ← assign tracker frame (.register var.name) sized (valueBytes bits size) (width > 1 && !frame.jumps) false
        frame.newRegisters.modify ((var.name, tags) :: ·)
        frame.variables.modify (·.insert var (bits, tags.map ofTag))
      perform tracker frame fuel rest
    | .jmp target =>
      let (bits, shade) ← evaluate tracker frame target
      let inputs := allInputs shade
      if !inputs.isEmpty then branchNode tracker frame inputs (bitsValue bits)
      frame.jumped.set true
      pure false
    | .special name =>
      -- What an intrinsic gives depends on all that it was given. Nothing here runs it, so that what it is isn't known.
      if name != "syscall" && name != "svc" && name != "interrupt" then
        let operands ← frame.operands.get
        frame.operands.set []
        frame.incomplete.set true
        let result : Shade := #[{ inputs := operands.map fun input => { input with edge := .data } }]
        frame.variables.modify fun variables =>
          variables.insert ⟨"intrinsic:y0", .imm 64, 0, false⟩ (none, Array.replicate 16 (byteAt result 0))
      perform tracker frame fuel rest
    | .cpuExn _ => pure false
    | .ifElse condition yes no =>
      let (bits, shade) ← evaluate tracker frame condition
      let inputs := allInputs shade
      if !inputs.isEmpty then branchNode tracker frame inputs none
      match bitsValue bits with
      | some value =>
        let go ← perform tracker frame fuel (if value != 0 then yes else no)
        if go then perform tracker frame fuel rest else pure false
      | none =>
        frame.incomplete.set true
        let _ ← perform tracker frame fuel yes
        let _ ← perform tracker frame fuel no
        perform tracker frame fuel rest
    | .while condition body =>
      let (bits, shade) ← evaluate tracker frame condition
      let inputs := allInputs shade
      if !inputs.isEmpty then branchNode tracker frame inputs none
      match bitsValue bits with
      | some 0 => perform tracker frame fuel rest
      | some _ =>
        let go ← perform tracker frame fuel body
        if go then perform tracker frame fuel (stmt :: rest) else pure false
      | none =>
        frame.incomplete.set true
        perform tracker frame fuel rest

private partial def branchNode (_tracker : Tracker) (frame : Frame) (inputs : List Input) (target : Option Nat) : IO Unit := do
  let id ← nodeIdOf frame
  frame.newNodes.modify (·.push {
    id, insn := frame.insn, pc := frame.pc, thread := frame.thread, space := frame.space, kind := .branch target
    place := .control, values := [], inputs := #[inputs.map fun input => { input with edge := .condition }] })
  frame.newGuard.set (some (nodeTag id 0))

end

private partial def jumpsAlways : Bil.Program → Bool
  | [] => false
  | .jmp _ :: _ => true
  | _ :: rest => jumpsAlways rest

private def programOf (tracker : Tracker) (pc : Nat) : IO (Option Bil.Program) := do
  let code ← Emu.codeAt tracker.emu pc
  match (← tracker.programs.get)[pc]? with
  | some (bytes, program) =>
    if bytes == code then return some program
  | none => pure ()
  match ← Emu.programAt tracker.emu pc with
  | some program =>
    tracker.programs.modify (·.insert pc (code, program))
    pure (some program)
  | none => pure none

/-- The bytes of what a function returns that nothing marked reached, as a constant under the branch that it last took on what is marked. -/
private def resultUnderGuard (tracker : Tracker) (thread : ThreadId) (space pc insn : Nat) (guard : Tag) : IO Unit := do
  let (_, _, register) := Emu.syscallRegisters tracker.emu.config.syscallAbi
  let width ← Emu.wordWidth tracker.emu
  let size := bytesOf width
  let bits := match Bil.lookup (← tracker.emu.state.get).env ⟨register, .imm width, 0, false⟩ with
    | .ok value => (Bap.Value.asBits value).toOption
    | .error _ => none
  let current ← registersOf tracker thread
  let tags := (current.get? register).getD (Array.replicate size 0)
  if tags.any Tag.isNode then return
  let id ← nextId tracker
  push tracker {
    id, insn, pc, thread, space, kind := .constant, place := .register register, values := valueBytes bits size
    inputs := Array.replicate size [], guard := some guard }
  tracker.registers.modify (·.insert thread (current.insert register ((Array.range size).map (nodeTag id))))

/-- What an instruction is about to do. It is worked out on what it can see and only then applied, so that one that faults has done nothing here, either. -/
private def follow (tracker : Tracker) (pc : Nat) : IO Unit := do
  let emu := tracker.emu
  let thread ← Emu.thread emu
  let table ← emu.taskTable.get
  let space := table.spaceOf thread
  if let some task := table.find? thread then
    tracker.lastOfGroup.modify (·.insert task.group thread)
  let insn ← tracker.insn.get
  tracker.insn.set (insn + 1)
  -- Back where a call was going to come back to is the end of that call and of those within it, which may not have come back.
  let calls := (← tracker.calls.get).getD thread []
  -- With the bit of Thumb, if it has that.
  let calls := match calls.dropWhile (fun site => site != pc && site != pc + 1) with
    | _ :: outer => outer
    | [] => calls
  let depth := calls.length
  -- What a function decided is over when it has returned, whatever is called next at that depth. What it returns is what it decided,
  -- though it may have set that before it branched, and the branch was that nothing changed it.
  if let some (guard, at_, guardDepth) := (← tracker.guards.get)[thread]? then
    if depth < guardDepth then
      tracker.guards.modify (·.erase thread)
      if insn - at_ ≤ tracker.config.guardWindow then resultUnderGuard tracker thread space pc insn guard
  let some program ← programOf tracker pc | gap tracker pc
  let frame : Frame := {
    pc, thread, space, insn
    env := (← emu.state.get).env
    jumps := jumpsAlways program
    variables := ← IO.mkRef {}
    memory := ← IO.mkRef {}
    tags := ← IO.mkRef {}
    regionsNow := ← emu.regions.get
    newNodes := ← IO.mkRef #[]
    firstId := ← nextId tracker
    newRegisters := ← IO.mkRef []
    newGuard := ← IO.mkRef none
    incomplete := ← IO.mkRef false
    operands := ← IO.mkRef []
    depth
    link := ← IO.mkRef none
    jumped := ← IO.mkRef false }
  try
    let _ ← perform tracker frame 65536 program
  catch error =>
    if error.toString == faultMessage then return
    gap tracker pc
    return
  if ← frame.incomplete.get then gap tracker pc
  for node in ← frame.newNodes.get do push tracker node
  for (address, tag) in (← frame.tags.get).toList do setTag tracker space address tag
  let written := (← frame.newRegisters.get).reverse
  if !written.isEmpty then
    let current ← registersOf tracker thread
    let updated := written.foldl (fun registers (name, tags) => registers.insert name tags) current
    tracker.registers.modify (·.insert thread updated)
  if let some guard := ← frame.newGuard.get then
    tracker.guards.modify (·.insert thread (guard, insn, depth))
  let calls := match ← frame.link.get, ← frame.jumped.get with
    | some site, true => site :: calls
    | _, _ => calls
  tracker.calls.modify (·.insert thread calls)

/-! ### Sources -/

/-- A source of `size` bytes in a thread's memory or registers, whose bytes have what is there now. -/
private def sourceNode (tracker : Tracker) (place : Place) (label : String) (offset : Option Nat) (values : List (Option UInt8)) : IO Nat := do
  let id ← nextId tracker
  let thread ← Emu.thread tracker.emu
  push tracker {
    id, insn := ← tracker.insn.get, pc := ← tracker.emu.pc.get, thread, space := ← Emu.spaceOf tracker.emu thread
    kind := .source label offset, place, values, inputs := Array.replicate values.length [] }
  pure id

/-- Says that the bytes of memory at `address` are a source called `label`. -/
def markMemory (tracker : Tracker) (address size : Nat) (label : String) (offset : Option Nat := none) : IO Unit := do
  if size == 0 then return
  let raw ← Emu.peek tracker.emu address size
  let id ← sourceNode tracker (.memory address) label offset (raw.toList.map some)
  let space ← Emu.spaceOf tracker.emu (← Emu.thread tracker.emu)
  for index in List.range size do
    setTag tracker space (address + index) (nodeTag id index)

private def setRegisterTags (tracker : Tracker) (thread : ThreadId) (name : String) (tags : Array Tag) : IO Unit := do
  let current ← registersOf tracker thread
  tracker.registers.modify (·.insert thread (current.insert name tags))

/-- Says that a register of the thread that runs is a source called `label`. -/
def markRegister (tracker : Tracker) (var : Bap.Var) (label : String) : IO Unit := do
  let thread ← Emu.thread tracker.emu
  let size := bytesOf (widthOfTyp var.typ)
  let bits := match Bil.lookup (← tracker.emu.state.get).env var with
    | .ok value => (Bap.Value.asBits value).toOption
    | .error _ => none
  let id ← sourceNode tracker (.register var.name) label none (valueBytes bits size)
  setRegisterTags tracker thread var.name ((Array.range size).map (nodeTag id))

/-- Bytes that came from outside any instruction: a source if a call that is one is in progress, and otherwise what nobody made. -/
private def externalWrite (tracker : Tracker) (address size : Nat) (cleared : Bool) : IO Unit := do
  let space ← Emu.spaceOf tracker.emu (← Emu.thread tracker.emu)
  match ← tracker.label.get with
  | some (label, offset) =>
    if cleared then
      for index in List.range size do setTag tracker space (address + index) 0
    else
      let done ← tracker.written.get
      tracker.written.set (done + size)
      markMemory tracker address size label (offset.map (· + done))
  | none =>
    for index in List.range size do setTag tracker space (address + index) 0

private def wordVar (emu : Emu) (name : String) : IO Bap.Var := do
  pure ⟨name, .imm (← Emu.wordWidth emu), 0, false⟩

private def callStarts (tracker : Tracker) (number : Nat) (args : List Nat) : IO Unit := do
  tracker.calling.set (some (number, args))
  tracker.written.set 0
  tracker.label.set (← tracker.config.describe number args)

private def callEnds (tracker : Tracker) (result : Option Nat) : IO Unit := do
  if let some (number, args) := ← tracker.calling.get then
    tracker.config.called number args result
  if let some (label, _) := ← tracker.label.get then
    let (_, _, register) := Emu.syscallRegisters tracker.emu.config.syscallAbi
    if result.isSome then markRegister tracker (← wordVar tracker.emu register) s!"{label} result"
  else
    -- What it returns says nothing, and whatever was in the register has gone.
    let (_, _, register) := Emu.syscallRegisters tracker.emu.config.syscallAbi
    if result.isSome then
      let var ← wordVar tracker.emu register
      let thread ← Emu.thread tracker.emu
      setRegisterTags tracker thread var.name (Array.replicate (bytesOf (widthOfTyp var.typ)) (cleanTag (← tracker.emu.pc.get)))
  tracker.calling.set none
  tracker.label.set none

/-- A new process has a copy of what its parent has, as it does of the memory. -/
private def forked (tracker : Tracker) (parent child : Nat) : IO Unit := do
  let source ← Emu.spaceOf tracker.emu parent
  tracker.pages.modify fun pages =>
    pages.fold (init := pages) fun out (space, page) tags =>
      if space == source then out.insert (child, page) tags else out

/-- Starts tracking the emulator, from here on. All its code runs one instruction at a time from then on, in what is much slower than the JIT, though
the guest does the same as it would have. Not in a parallel round. -/
def start (emu : Emu) (config : Config := {}) : IO Tracker := do
  let tracker : Tracker := {
    emu, config
    nodes := ← IO.mkRef #[]
    base := ← IO.mkRef 0
    insn := ← IO.mkRef 0
    registers := ← IO.mkRef {}
    pages := ← IO.mkRef {}
    guards := ← IO.mkRef {}
    calls := ← IO.mkRef {}
    lastOfGroup := ← IO.mkRef {}
    programs := ← IO.mkRef {}
    calling := ← IO.mkRef none
    label := ← IO.mkRef none
    written := ← IO.mkRef 0
    gaps := ← IO.mkRef {} }
  let width ← Emu.wordWidth emu
  let _ ← Emu.onCode emu (0, 2 ^ width - 1) fun _ pc => follow tracker pc
  emu.syscallStarts.set (some (callStarts tracker))
  emu.syscallEnds.set (some (callEnds tracker))
  emu.memoryChanged.set (some (externalWrite tracker))
  emu.hostStarts.set (some fun label => do
    tracker.written.set 0
    tracker.label.set (some (label, none)))
  emu.hostEnds.set (some fun register => do
    if let some (label, _) := ← tracker.label.get then
      markRegister tracker (← wordVar emu register) s!"{label} result"
    tracker.label.set none)
  emu.processHooks.modify ((fun parent child => forked tracker parent child) :: ·)
  pure tracker

/-! ### Saying where a byte came from -/

/-- What is known of a byte that a question was asked about. -/
inductive Origin where
  /-- Nothing that was followed has written it: it was there when tracking started, or the host put it there. -/
  | untouched
  /-- Nothing marked reached it: this is the instruction that computed it. -/
  | clean (pc : Nat)
  | tainted (node : Nat) (byte : Nat)
  deriving DecidableEq, Repr

/-- A step of the way that a byte took, oldest first: the byte of a node, and how the next step depends on it. -/
structure Step where
  node : Node
  byte : Nat
  edge : Edge
  deriving Repr

structure Explanation where
  origin : Origin
  /-- The way from the nearest source, by the strongest edges that reach one, oldest first, ending at the byte. Without a source, the longest way back. -/
  path : List Step := []
  /-- Every source that it depends on at all, with the weakest edge that it took to get there: `data` if by data alone. -/
  sources : List (Node × Nat × Edge) := []
  /-- Every branch that a constant in what led to it was under, oldest first. -/
  branches : List Node := []
  /-- Whether any of what led to it has gone, for which `capacity` was too small. -/
  truncated : Bool := false
  deriving Repr

private def inputsOf (node : Node) (byte : Nat) : List Input :=
  let direct := node.inputs.getD (if node.kind matches .branch _ then 0 else byte) []
  match node.guard with
  | some tag => if direct.isEmpty then direct ++ [{ tag, edge := .guard }] else direct
  | none => direct

private def edgeRank : Edge → Nat
  | .data => 0
  | .condition => 1
  | .guard => 2
  | .address => 3

/-- What depends on what from a byte, as far as edges of `limit` go: breadth first, so that a way that it finds is the shortest of those. -/
private partial def search (tracker : Tracker) (root : Tag) (limit : Nat) :
    IO (Std.HashMap Tag (Tag × Edge) × Array Tag × Bool) := do
  let parents ← IO.mkRef ({} : Std.HashMap Tag (Tag × Edge))
  let order ← IO.mkRef (#[root] : Array Tag)
  let truncated ← IO.mkRef false
  let rec loop (index : Nat) : IO Unit := do
    let found ← order.get
    if h : index < found.size then
      let tag := found[index]
      match ← node? tracker tag.node with
      | none => truncated.set true
      | some node =>
        let next := (inputsOf node tag.byte).toArray.qsort (fun left right => edgeRank left.edge < edgeRank right.edge)
        for input in next do
          if input.tag.isNode && edgeRank input.edge ≤ limit && input.tag != root && !(← parents.get).contains input.tag then
            parents.modify (·.insert input.tag (tag, input.edge))
            order.modify (·.push input.tag)
      loop (index + 1)
  loop 0
  pure (← parents.get, ← order.get, ← truncated.get)

private partial def walkFrom (tracker : Tracker) (parents : Std.HashMap Tag (Tag × Edge)) (root tag : Tag) (edge : Edge) (out : List Step) : IO (List Step) := do
  match ← node? tracker tag.node with
  | none => pure out
  | some node =>
    let out := out ++ [{ node, byte := tag.byte, edge }]
    if tag == root then pure out
    else
      match parents[tag]? with
      | some (parent, edgeThere) => walkFrom tracker parents root parent edgeThere out
      | none => pure out

/-- Where the byte with this tag came from. -/
def explainTag (tracker : Tracker) (root : Tag) : IO Explanation := do
  if !root.isNode then
    return { origin := if root.isClean then .clean (root / 2) else .untouched }
  let isSource (tag : Tag) : IO Bool := do
    match ← node? tracker tag.node with
    | some { kind := .source .., .. } => pure true
    | _ => pure false
  -- The strongest way that reaches a source: data alone, then with what selected it, then branches, then pointers.
  let rec attempt : List Nat → IO (Option (Std.HashMap Tag (Tag × Edge) × Tag))
    | [] => pure none
    | limit :: rest => do
      let (parents, order, _) ← search tracker root limit
      match ← order.findM? isSource with
      | some tag => pure (some (parents, tag))
      | none => attempt rest
  let (allParents, allOrder, truncated) ← search tracker root 3
  let path ← match ← attempt [0, 1, 2, 3] with
    | some (parents, tag) => walkFrom tracker parents root tag .data []
    | none =>
      match allOrder.back? with
      | some tag => walkFrom tracker allParents root tag .data []
      | none => pure []
  -- The weakest edge on the way to each source.
  let weakest ← IO.mkRef ({} : Std.HashMap Tag Nat)
  weakest.modify (·.insert root 0)
  let mut sources : List (Node × Nat × Edge) := []
  let mut branches : List Node := []
  for tag in allOrder do
    let known ← weakest.get
    let rank := match allParents[tag]? with
      | some (parent, edge) => max (known.getD parent 0) (edgeRank edge)
      | none => 0
    weakest.modify (·.insert tag rank)
    if let some node := ← node? tracker tag.node then
      match node.kind with
      | .source .. =>
        let edge := match rank with | 0 => Edge.data | 1 => .condition | 2 => .guard | _ => .address
        sources := sources ++ [(node, tag.byte, edge)]
      | .branch _ => branches := node :: branches
      | _ => pure ()
  pure {
    origin := .tainted root.node root.byte
    path, sources, branches := (branches.toArray.qsort fun left right => left.id < right.id).toList
    truncated := truncated }

/-- Where a byte of memory came from, in an address space. -/
def explainMemory (tracker : Tracker) (address : Nat) (space : Option Nat := none) : IO Explanation := do
  let space ← match space with
    | some space => pure space
    | none => Emu.spaceOf tracker.emu (← Emu.thread tracker.emu)
  explainTag tracker (← tagAt tracker space address)

/-- Where a byte of a register came from, by significance, in a thread. -/
def explainRegister (tracker : Tracker) (name : String) (byte : Nat := 0) (thread : Option ThreadId := none) : IO Explanation := do
  let thread ← match thread with
    | some thread => pure thread
    | none => Emu.thread tracker.emu
  let registers ← registersOf tracker thread
  explainTag tracker ((registers.get? name).bind (·[byte]?) |>.getD 0)

private def hex (value : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 value)

/-- A step in a line. -/
def Step.text (step : Step) : String :=
  let node := step.node
  let place := match node.place with
    | .register name => name
    | .memory address => s!"[{hex (address + step.byte)}]"
    | .control => "branch"
  let value := match node.values.getD step.byte none with
    | some byte => s!" = {hex byte.toNat}"
    | none => ""
  let what := match node.kind with
    | .source label offset =>
      match offset with
      | some offset => s!"{label} at {offset + step.byte}"
      | none => label
    | .copy => "copy"
    | .compute => "computed"
    | .constant => "constant under a branch"
    | .branch target =>
      match target with
      | some target => s!"branch to {hex target}"
      | none => "branch"
  s!"{what} at {hex node.pc}, thread {node.thread}: {place}{value}"

/-- The way a byte took without what only copied it, which is the way a person wants: oldest first. -/
def Explanation.summary (explanation : Explanation) : List Step :=
  match explanation.path.getLast? with
  | none => []
  | some last =>
    let middle := explanation.path.filter fun step => !(step.node.kind matches .copy)
    match middle.getLast? with
    | some final => if final.node.id == last.node.id then middle else middle ++ [last]
    | none => [last]

def Explanation.text (explanation : Explanation) : String :=
  match explanation.origin with
  | .untouched => "nothing that was followed wrote it"
  | .clean pc => s!"computed at {hex pc} from nothing that was marked"
  | .tainted .. =>
    let steps := explanation.summary.map Step.text
    let lines := String.intercalate "\n  -> " steps
    if explanation.truncated then lines ++ "\n  (what led to it has gone: capacity was too small)" else lines

/-- Where it couldn't follow all of an instruction, and how many times. -/
def gapsOf (tracker : Tracker) : IO (List (Nat × Nat)) := do
  pure (← tracker.gaps.get).toList

end Tracker

end Bap.Analysis.DynamicTaint
