import Bap.Analysis.CallSites
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

What a program writes to a file or a pipe keeps what it came from there, by the byte, for whoever reads it, and a child has a copy of what its parent had.

What it can't see: flags that an intrinsic of floating point raises, a file that is truncated and then grows, which has what it had, and registers restored by
`sigreturn` or after `Machine.call`, which keep what they had. -/

namespace Bap.Analysis.DynamicTaint

open Bap.Emu (Emu ThreadId)

/-- How a byte depends on what it came from: as its value, through an address, by what a selection chose, or by a branch that guards it. -/
inductive Edge where
  | data | address | condition | guard
  deriving DecidableEq, Repr, Inhabited

/-- What produced a byte. 0 is that nothing here has, an odd number is a clean byte of the instruction at half of it, and an even one is a byte of a node. -/
abbrev Tag := Nat

/-- The tag of a clean byte that the instruction at `pc` computed. -/
def cleanTag (pc : Nat) : Tag := 2 * pc + 1
/-- How many bytes a node has at most, as `read` of a file gives at once: its bytes are tags of their own. -/
def nodeBytes : Nat := 2 ^ 32

/-- The tag of a byte of a node. -/
def nodeTag (id byte : Nat) : Tag := 2 * ((id + 1) * nodeBytes + byte)
/-- Whether it is the tag of a byte of a node. -/
def Tag.isNode (tag : Tag) : Bool := tag != 0 && tag % 2 == 0
/-- Whether it is the tag of a clean byte. -/
def Tag.isClean (tag : Tag) : Bool := tag % 2 == 1
/-- The node of the tag of a byte of one. -/
def Tag.node (tag : Tag) : Nat := tag / 2 / nodeBytes - 1
/-- Which byte of its node the tag of a byte of one is. -/
def Tag.byte (tag : Tag) : Nat := tag / 2 % nodeBytes

/-- What a byte of a node came from, and how. -/
structure Input where
  tag : Tag
  edge : Edge
  deriving DecidableEq, Repr, Inhabited

/-- What a node is. -/
inductive NodeKind where
  /-- What came in from outside, as it was called, and where in what it came from each byte of the node starts. -/
  | source (label : String) (offset : Option Nat)
  | copy
  | compute
  /-- A constant, or a clean byte, that a branch chose. -/
  | constant
  | branch (target : Option Nat)
  /-- What a program sent somewhere that it can be had from again, such as a file or a pipe, as it was called. -/
  | carried (label : String)
  deriving DecidableEq, Repr, Inhabited

/-- Where a node is: in a register, at an address, in the control of a thread, as a branch is, or in a file or a pipe. -/
inductive Place where
  | register (name : String)
  | memory (address : Nat)
  | control
  /-- Bytes of a file or a pipe, from an offset of it, by what they are kept under. -/
  | stream (space offset : Nat)
  deriving DecidableEq, Repr, Inhabited

private instance : Repr ByteArray := ⟨fun bytes _ => repr bytes.toList⟩

/-- An assignment or a store that depends on something marked, with what each of its bytes came from, where and when it was, and what it was. -/
structure Node where
  id : Nat
  /-- How many instructions it is since tracking started, of all threads. -/
  insn : Nat
  pc : Nat
  thread : ThreadId
  space : Nat
  kind : NodeKind
  place : Place
  /-- What it is, by the byte: of a register from the least significant, and of memory from its address up. Empty when it can't be known. -/
  values : ByteArray
  inputs : Array (List Input)
  guard : Option Tag := none
  deriving Repr, Inhabited

/-- Bytes of memory that go to a file or a pipe: where they are, how many, what they are kept under there and from what offset, and what to call that. -/
structure Send where
  address : Nat
  size : Nat
  space : Nat
  offset : Nat
  label : String

/-- What a byte of a node was, if that is known. -/
def Node.valueAt (node : Node) (byte : Nat) : Option UInt8 :=
  if h : byte < node.values.size then some node.values[byte] else none

/-- What a tracker follows and keeps, and what the host says of the system calls that move bytes. -/
structure Config where
  /-- How many instructions of a thread a branch on a tainted condition guards what comes after it. -/
  guardWindow : Nat := 64
  /-- How many nodes are kept, of which the oldest half goes when they run out. What led to it is then missing, and says so. -/
  capacity : Nat := 4000000
  /-- What a system call is called as a source, with where it reads from if that means something: none if it is no source. -/
  describe : Nat → List Nat → IO (Option (String × Option Nat)) := fun number _ => pure (some (s!"syscall {number}", none))
  /-- What a system call reads from where bytes keep their tags, as what they are kept under and from what offset. -/
  backing : Nat → List Nat → IO (Option (Nat × Nat)) := fun _ _ => pure none
  /-- What a system call is about to send to where bytes keep their tags. -/
  sends : Nat → List Nat → IO (List Send) := fun _ _ => pure []
  /-- What sees a call and its result, such as to know what was opened. -/
  called : Nat → List Nat → Option Nat → IO Unit := fun _ _ _ => pure ()

/-! ### Shades: what a value being computed came from -/

/-- What a byte of a value being computed came from. There are several of these for each operand of each instruction, so that the common ones take as little as they can. -/
inductive Byte where
  /-- Nothing marked reached it. `origin` is the tag of a byte that hasn't changed, `copied` says that it hasn't, and a `literal` depends on nothing at all. -/
  | clean (origin : Tag) (copied literal : Bool)
  /-- The byte of what has this tag, unchanged. -/
  | same (tag : Tag)
  /-- It depends on these, of which there is at least one. -/
  | mixed (inputs : List Input)
  deriving Inhabited

namespace Byte

/-- What a byte came from, of what is followed. -/
def inputs : Byte → List Input
  | .clean .. => []
  | .same tag => [{ tag, edge := .data }]
  | .mixed inputs => inputs

/-- Whether nothing marked reached it. -/
def isClean : Byte → Bool
  | .clean .. => true
  | _ => false

/-- The tag of a clean byte that hasn't changed, or 0. -/
def origin : Byte → Tag
  | .clean origin .. => origin
  | _ => 0

/-- Whether it is a byte of something else, unchanged. -/
def copied : Byte → Bool
  | .clean _ copied _ => copied
  | .same _ => true
  | .mixed _ => false

/-- Whether it depends on nothing at all. -/
def literal : Byte → Bool
  | .clean _ _ literal => literal
  | _ => false

end Byte

/-- A byte with nothing known of it, and a constant. -/
private def noByte : Byte := .clean 0 false false
private def literalByte : Byte := .clean 0 false true

private def ofInputs (inputs : List Input) (literal : Bool := false) : Byte :=
  if inputs.isEmpty then (if literal then literalByte else noByte) else .mixed inputs

/-- What is needed of an instruction that only computes registers from registers, by which it does nothing here when none of them depends on anything: what it reads, and what it
writes, with what they then have. -/
structure Plain where
  reads : Array String
  writes : Array (String × Array Tag)

/-- What an instruction has done as far as it knows, until it all has. There is one, which each instruction starts on empty, as it runs for all of them and only one runs at a time. Few things
happen in an instruction, and so what is here goes in lists. -/
structure Scratch where
  variables : IO.Ref (List (Bap.Var × Option (Σ width, BitVec width) × Array Byte))
  memory : IO.Ref (List (Nat × UInt8))
  tags : IO.Ref (List (Nat × Tag))
  newNodes : IO.Ref (Array Node)
  newRegisters : IO.Ref (List (String × Array Tag))
  newGuard : IO.Ref (Option Tag)
  incomplete : IO.Ref Bool
  operands : IO.Ref (List Input)
  link : IO.Ref (Option Nat)
  jumped : IO.Ref Bool

/-- What follows a run: the nodes that it has made, the tag of every byte of every register and address space, the guards that last, and
the hooks that it put on the machine. `Machine.track` makes one. -/
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
  calls : IO.Ref (Std.HashMap ThreadId CallSites)
  /-- Which thread last ran of each process, for what a new thread starts with. -/
  lastOfGroup : IO.Ref (Std.HashMap Nat ThreadId)
  programs : IO.Ref (Std.HashMap Nat (ByteArray × Bil.Program × Option Plain))
  /-- What was called, with its number and arguments, for a call in progress, and how it is called if it is a source. -/
  calling : IO.Ref (Option (Nat × List Nat))
  label : IO.Ref (Option (String × Option Nat))
  backing : IO.Ref (Option (Nat × Nat))
  /-- What was being served when the host started on something else. -/
  outer : IO.Ref (List (Option (String × Option Nat)))
  /-- How many bytes of what the current call read have gone by. -/
  written : IO.Ref Nat
  /-- Where instructions were that this couldn't follow all of, with how many times. -/
  gaps : IO.Ref (Std.HashMap Nat Nat)
  scratch : Scratch
  /-- When the machine was put back to what it was, by what, which is where a byte that nothing followed may have come from. -/
  restores : IO.Ref (List (Nat × String))
  /-- The checkpoint that this went on from, and how far it was then, which isn't saved, as going on from one changes nothing of what it was. -/
  loadedFrom : IO.Ref (Option (Nat × String))

/-- What each byte of a value being computed came from, the least significant first. -/
abbrev Shade := Array Byte

private def bytesOf (width : Nat) : Nat := (width + 7) / 8

private def union (left right : List Input) : List Input :=
  right.foldl (fun out input => if out.contains input then out else out ++ [input]) left

private def combine (left right : Byte) : Byte :=
  match left, right with
  | .clean _ _ l, .clean _ _ r => if l && r then literalByte else noByte
  | .clean .., other | other, .clean .. => ofInputs other.inputs
  | _, _ => ofInputs (union left.inputs right.inputs)

private def changed (byte : Byte) : Byte :=
  match byte with
  | .clean _ _ literal => if literal then literalByte else noByte
  | other => ofInputs other.inputs

/-- A byte that nothing has made, as a read of what was there when tracking started has. -/
private def untouchedByte : Byte := .clean 0 true false

private def ofTag (tag : Tag) : Byte :=
  if tag == 0 then untouchedByte
  else if tag.isNode then .same tag
  else .clean tag true false

private def literal1 : Shade := #[literalByte]
private def literal2 : Shade := #[literalByte, literalByte]
private def literal4 : Shade := #[literalByte, literalByte, literalByte, literalByte]
private def literal8 : Shade := #[literalByte, literalByte, literalByte, literalByte, literalByte, literalByte, literalByte, literalByte]

/-- There is one for each of the widths that nearly all have, as there are constants in nearly all that is run. -/
private def literalShade (width : Nat) : Shade :=
  match bytesOf width with
  | 1 => literal1
  | 2 => literal2
  | 4 => literal4
  | 8 => literal8
  | size => Array.replicate size literalByte

private def opaqueShade (width : Nat) : Shade := Array.replicate (bytesOf width) noByte

/-- All that a shade has, as the inputs of something that depends on all of it. -/
private def allInputs (shade : Shade) : List Input :=
  shade.foldl (fun out byte => if byte.isClean then out else union out byte.inputs) []

private def isLiteral (shade : Shade) : Bool := shade.all (·.literal)

/-- The same inputs, by another edge, and what they add to each byte of a shade. -/
private def withInputs (edge : Edge) (inputs : List Input) (shade : Shade) : Shade :=
  if inputs.isEmpty then shade else
    let again := inputs.map fun input => { input with edge }
    shade.map fun byte => .mixed (union byte.inputs again)

private def byteAt (shade : Shade) (index : Nat) : Byte := shade.getD index noByte

/-- Each byte has what is at it and below it of both, as a carry goes up. -/
private def carrying (left right : Shade) (size : Nat) : Shade :=
  let (_, out) := (List.range size).foldl (init := (literalByte, (#[] : Shade))) fun (below, out) index =>
    let byte := combine below (combine (byteAt left index) (byteAt right index))
    (byte, out.push byte)
  out

/-- Each byte has all that both have. -/
private def everything (left right : Shade) (size : Nat) : Shade :=
  let both := ofInputs (union (allInputs left) (allInputs right)) (isLiteral left && isLiteral right)
  Array.replicate size both

private def bitsValue (bits : Option (Σ width, BitVec width)) : Option Nat := bits.map (·.2.toNat)

private def byteOfValue (value index : Nat) : Nat := (value >>> (8 * index)) % 256

/-- What a shift by a known amount does: a byte comes from the one or two that it overlaps. -/
private def shifted (shade : Shade) (size amount : Nat) (up : Bool) (arithmetic : Bool) : Shade :=
  let whole := amount / 8
  let part := amount % 8
  let source (index : Nat) : Byte :=
    if up then
      if index < whole then literalByte else byteAt shade (index - whole)
    else
      if index + whole < size then byteAt shade (index + whole)
      else if arithmetic then changed (byteAt shade (size - 1)) else literalByte
  (Array.range size).map fun index =>
    if part == 0 then source index
    else
      let next := if up then (if index ≥ whole + 1 then byteAt shade (index - whole - 1) else literalByte)
        else if index + whole + 1 < size then byteAt shade (index + whole + 1)
        else if arithmetic then byteAt shade (size - 1) else literalByte
      combine (source index) next

/-- A byte of a value under one that nothing marked reached and that is known: what that decides depends on nothing, and what it leaves stays what it was. -/
private def underMask (op : Bil.BinOp) (byte : Byte) (part : Nat) : Byte :=
  match op with
  | .and =>
    if part == 0 then literalByte
    else if part == 255 then byte else changed byte
  | .or =>
    if part == 255 then literalByte
    else if part == 0 then byte else changed byte
  | _ => if part == 0 then byte else changed byte

/-- `and`, `or` and `xor`, which go by the byte, with either side as a mask wherever that is clean. -/
private def bitwise (op : Bil.BinOp) (left right : Shade) (leftValue rightValue : Option Nat) (size : Nat) : Shade :=
  (Array.range size).map fun index =>
    let l := byteAt left index
    let r := byteAt right index
    match l.isClean, leftValue, r.isClean, rightValue with
    | true, some value, false, _ => underMask op r (byteOfValue value index)
    | false, _, true, some value => underMask op l (byteOfValue value index)
    | _, _, _, _ => combine l r

private def isClean (shade : Shade) : Bool := shade.all Byte.isClean

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
  | .unsigned => (Array.range size).map fun index => if index < value.size then byteAt value index else literalByte
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
      (List.range (last + 1 - first)).foldl (fun out offset => combine out (byteAt value (first + offset))) literalByte

/-! ### Tags -/

namespace Tracker

private def keyOf (tracker : Tracker) (space address : Nat) : IO (Nat × Nat) := do
  match ← tracker.emu.futexKey.get with
  | some key =>
    match ← key address with
    | some found => pure found
    | none => pure (space, address)
  | none => pure (space, address)

private def rawTag (tracker : Tracker) (space offset : Nat) : IO Tag := do
  match (← tracker.pages.get)[(space, offset / 4096)]? with
  | some page => pure (page.getD (offset % 4096) 0)
  | none => pure 0

/-- It changes the page in place, as what is taken out of the table is then the only one. -/
private def setRawTag (tracker : Tracker) (space offset : Nat) (tag : Tag) : IO Unit :=
  tracker.pages.modify (·.alter (space, offset / 4096) fun page =>
    some ((page.getD (Array.replicate 4096 0)).setIfInBounds (offset % 4096) tag))

private def tagAt (tracker : Tracker) (space address : Nat) : IO Tag := do
  let (space, address) ← keyOf tracker space address
  rawTag tracker space address

/-- The tags of bytes in a row. What they are kept under goes by the page, as a mapping does. -/
private def tagsAt (tracker : Tracker) (space address size : Nat) : IO (Array Tag) := do
  let mut out := Array.emptyWithCapacity size
  let mut at_ := address
  while at_ < address + size do
    let stop := min (address + size) ((at_ / 4096 + 1) * 4096)
    let (kept, offset) ← keyOf tracker space at_
    let page := (← tracker.pages.get)[(kept, offset / 4096)]?
    for index in List.range (stop - at_) do
      out := out.push (match page with
        | some page => page.getD (offset % 4096 + index) 0
        | none => 0)
    at_ := stop
  pure out

private def setTag (tracker : Tracker) (space address : Nat) (tag : Tag) : IO Unit := do
  let (space, address) ← keyOf tracker space address
  setRawTag tracker space address tag

/-- Bytes in a row have nothing that made them. Most of a big range has never had anything, so that this goes by what there is. -/
private def clearTags (tracker : Tracker) (space address size : Nat) : IO Unit := do
  if size == 0 then return
  let (kept, offset) ← keyOf tracker space address
  let stop := offset + size
  let whole (page : Nat) : Bool := page * 4096 ≥ offset && (page + 1) * 4096 ≤ stop
  let touched (page : Nat) : Bool := page * 4096 < stop && offset < (page + 1) * 4096
  let clear (out : Std.HashMap (Nat × Nat) (Array Tag)) (key : Nat × Nat) (tags : Array Tag) :=
    if key.1 != kept || !touched key.2 then out
    else if whole key.2 then out.erase key
    else
      let first := key.2 * 4096
      out.insert key ((List.range 4096).foldl (fun tags index =>
        if first + index ≥ offset && first + index < stop then tags.setIfInBounds index 0 else tags) tags)
  let lowest := offset / 4096
  let many := (stop - 1) / 4096 + 1 - lowest
  tracker.pages.modify fun pages =>
    if many ≤ pages.size then
      (List.range many).foldl (init := pages) fun out index =>
        match pages[(kept, lowest + index)]? with
        | some tags => clear out (kept, lowest + index) tags
        | none => out
    else pages.fold (init := pages) clear

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

/-- A node, if it is still kept. -/
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
  firstId : Nat
  depth : Nat
  scratch : Scratch

private def faultMessage : String := "dynamic taint: this instruction faults"

private def nodeIdOf (frame : Frame) : IO Nat := do
  pure (frame.firstId + (← frame.scratch.newNodes.get).size)

private def activeGuard (tracker : Tracker) (frame : Frame) : IO (Option Tag) := do
  if let some tag := ← frame.scratch.newGuard.get then return some tag
  match (← tracker.guards.get)[frame.thread]? with
  | some (tag, at_, depth) =>
    pure (if frame.insn - at_ ≤ tracker.config.guardWindow && depth ≤ frame.depth then some tag else none)
  | none => pure none

private def loadBytes (tracker : Tracker) (frame : Frame) (address size : Nat) : IO (ByteArray × Array Tag) := do
  -- One region nearly always has all of it, and the first byte says that.
  let regions ← Emu.regionsTouching tracker.emu address size
  let mut at_ := address
  while at_ < address + size do
    match Emu.lookupRegion regions at_ with
    | some region =>
      if !region.protection.readable then throw (IO.userError faultMessage)
      at_ := region.address + region.data.size
    | none => throw (IO.userError faultMessage)
  let raw ← Emu.peek tracker.emu address size
  let tags ← tagsAt tracker frame.space address size
  let overlay ← frame.scratch.memory.get
  let written ← frame.scratch.tags.get
  if overlay.isEmpty && written.isEmpty then return (raw, tags)
  let mut bytes := raw
  let mut out := tags
  for offset in List.range size do
    if let some byte := overlay.lookup (address + offset) then bytes := bytes.set! offset byte
    if let some tag := written.lookup (address + offset) then out := out.setIfInBounds offset tag
  pure (bytes, out)

/-- A node for what has its bytes as given, if any of them needs one, and what each byte is now. A byte that stays a copy keeps the tag it had in a
register. In memory a copy has a node, as that is the way it took. -/
private def assign (tracker : Tracker) (frame : Frame) (place : Place) (shade : Shade) (values : ByteArray)
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
    if byte.isClean then
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
        -- What goes up by a carry has all that the byte below has, and that is the most of what a node holds: it says so instead.
        let below := byteAt shade (index - 1)
        let shared := index > 0 && !below.inputs.isEmpty && !below.copied && below.inputs.isPrefixOf byte.inputs
        inputs := inputs.push (if shared then { tag := nodeTag id (index - 1), edge := .data } :: byte.inputs.drop below.inputs.length else byte.inputs)
        needed := true
  if needed then
    let kind : NodeKind := if guarded && inputs.all List.isEmpty then .constant else if allCopies then .copy else .compute
    frame.scratch.newNodes.modify (·.push {
      id, insn := frame.insn, pc := frame.pc, thread := frame.thread, space := frame.space, kind, place, values, inputs
      guard := if guarded then guard else none })
  pure tags

private def valueBytes (bits : Option (Σ width, BitVec width)) (size : Nat) : ByteArray :=
  match bitsValue bits with
  | some value => (List.range size).foldl (fun out index => out.push (UInt8.ofNat (byteOfValue value index))) (ByteArray.emptyWithCapacity size)
  | none => ByteArray.empty

private def constantly (exp : Bil.Exp) : Option (Σ width, BitVec width) :=
  match Bil.evalExp [] exp with
  | .ok value => (Bap.Value.asBits value).toOption
  | .error _ => none

private def isTemporary (var : Bap.Var) : Bool :=
  var.isVirtual || var.name.startsWith "intrinsic:" || var.name.startsWith "#" || var.name.startsWith "_primus_"

/-- Whether what an instruction leaves may be where a call comes back to: just after it, in a word or two. It is a call if it then jumps. -/
private def noteLink (frame : Frame) (bits : Option (Σ width, BitVec width)) : IO Unit := do
  if let some value := bitsValue bits then
    if frame.pc < value && value ≤ frame.pc + 32 then frame.scratch.link.set (some value)

private def widthOfTyp : Typ → Nat
  | .imm width => width
  | _ => 0

private def lookupVariable (tracker : Tracker) (frame : Frame) (var : Bap.Var) : IO (Option (Σ width, BitVec width) × Shade) := do
  if let some found := (← frame.scratch.variables.get).lookup var then return found
  -- The zero register, which every target's lifter calls this: a constant, as `addiu $1, $zero, 3` makes one as `mov w8, #3` does.
  if var.name == "XZR" then
    let width := widthOfTyp var.typ
    return (some ⟨width, BitVec.ofNat width 0⟩, literalShade width)
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
    frame.scratch.variables.modify ((var, bound) :: ·)
    let result ← evaluate tracker frame body
    frame.scratch.variables.modify (·.drop 1)
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
      pure (value, #[ofInputs (union (allInputs leftShade) (allInputs rightShade)) (isLiteral leftShade && isLiteral rightShade)])
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
      frame.scratch.incomplete.set true
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
    | none => frame.scratch.incomplete.set true
    | some at_ =>
      let regions ← Emu.regionsTouching tracker.emu at_ size
      for offset in List.range size do
        match Emu.lookupRegion regions (at_ + offset) with
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
        | .big => ByteArray.mk bySignificance.data.reverse
      let word := (← Emu.wordWidth tracker.emu) / 8
      let tags ← assign tracker frame (.memory at_) ordered values (!frame.jumps) (size < word)
      for offset in List.range size do
        frame.scratch.tags.modify (((at_ + offset), tags.getD offset 0) :: ·)
        if h : offset < values.size then
          frame.scratch.memory.modify (((at_ + offset), values[offset]) :: ·)
    pure (none, #[])

private partial def perform (tracker : Tracker) (frame : Frame) : Nat → Bil.Program → IO Bool
  | 0, _ => do
    frame.scratch.incomplete.set true
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
          frame.scratch.operands.modify (union · (allInputs shade))
        frame.scratch.variables.modify ((var, bits, shade) :: ·)
      else
        let width := widthOfTyp var.typ
        let size := bytesOf width
        let sized := (Array.range size).map (byteAt shade)
        let tags ← assign tracker frame (.register var.name) sized (valueBytes bits size) (width > 1 && !frame.jumps) false
        frame.scratch.newRegisters.modify ((var.name, tags) :: ·)
        frame.scratch.variables.modify ((var, bits, tags.map ofTag) :: ·)
      perform tracker frame fuel rest
    | .jmp target =>
      let (bits, shade) ← evaluate tracker frame target
      let inputs := allInputs shade
      if !inputs.isEmpty then branchNode frame inputs (bitsValue bits)
      frame.scratch.jumped.set true
      pure false
    | .special name =>
      -- What an intrinsic gives depends on all that it was given. Nothing here runs it, so that what it is isn't known.
      if name != "syscall" && name != "svc" && name != "interrupt" then
        let operands ← frame.scratch.operands.get
        frame.scratch.operands.set []
        frame.scratch.incomplete.set true
        let result : Shade := #[ofInputs (operands.map fun input => { input with edge := .data })]
        frame.scratch.variables.modify ((⟨"intrinsic:y0", .imm 64, 0, false⟩, none, Array.replicate 16 (byteAt result 0)) :: ·)
      perform tracker frame fuel rest
    | .cpuExn _ => pure false
    | .ifElse condition yes no =>
      let (bits, shade) ← evaluate tracker frame condition
      let inputs := allInputs shade
      if !inputs.isEmpty then branchNode frame inputs none
      match bitsValue bits with
      | some value =>
        let go ← perform tracker frame fuel (if value != 0 then yes else no)
        if go then perform tracker frame fuel rest else pure false
      | none =>
        frame.scratch.incomplete.set true
        let _ ← perform tracker frame fuel yes
        let _ ← perform tracker frame fuel no
        perform tracker frame fuel rest
    | .while condition body =>
      let (bits, shade) ← evaluate tracker frame condition
      let inputs := allInputs shade
      if !inputs.isEmpty then branchNode frame inputs none
      match bitsValue bits with
      | some 0 => perform tracker frame fuel rest
      | some _ =>
        let go ← perform tracker frame fuel body
        if go then perform tracker frame fuel (stmt :: rest) else pure false
      | none =>
        frame.scratch.incomplete.set true
        perform tracker frame fuel rest

private partial def branchNode (frame : Frame) (inputs : List Input) (target : Option Nat) : IO Unit := do
  let id ← nodeIdOf frame
  frame.scratch.newNodes.modify (·.push {
    id, insn := frame.insn, pc := frame.pc, thread := frame.thread, space := frame.space, kind := .branch target
    place := .control, values := ByteArray.empty, inputs := #[inputs.map fun input => { input with edge := .condition }] })
  frame.scratch.newGuard.set (some (nodeTag id 0))

end

private partial def jumpsAlways : Bil.Program → Bool
  | [] => false
  | .jmp _ :: _ => true
  | _ :: rest => jumpsAlways rest

/-- What an expression reads, if it is only registers. -/
private def readsOf (exp : Bil.Exp) (out : Array String) : Option (Array String) :=
  match exp with
  | .int _ => some out
  | .var var => some (if isTemporary var || out.contains var.name then out else out.push var.name)
  | .bin _ left right => readsOf left out >>= readsOf right
  | .un _ value | .cast _ _ value | .extract _ _ value => readsOf value out
  | .letIn _ value body => readsOf value out >>= readsOf body
  | .ite condition yes no => readsOf condition out >>= readsOf yes >>= readsOf no
  | .concat left right => readsOf left out >>= readsOf right
  | .load .. | .store .. | .unknown .. => none

/-- A program of moves from registers to registers, in order, and nothing else. -/
private def plainOf (memory : Bap.Var) (pc : Nat) (program : Bil.Program) : Option Plain := do
  let (reads, writes) ← program.foldlM (init := ((#[] : Array String), (#[] : Array (String × Array Tag)))) fun (reads, writes) stmt =>
    match stmt with
    | .move var value =>
      if var == memory then none
      else
        match readsOf value reads with
        | none => none
        | some reads =>
          if isTemporary var then some (reads, writes)
          else
            let tags := Array.replicate (bytesOf (widthOfTyp var.typ)) (cleanTag pc)
            some (reads, (writes.filter (·.1 != var.name)).push (var.name, tags))
    | _ => none
  some { reads, writes }

private def programOf (tracker : Tracker) (pc : Nat) : IO (Option (Bil.Program × Option Plain)) := do
  let code ← Emu.codeAt tracker.emu pc
  match (← tracker.programs.get)[pc]? with
  | some (bytes, program, plain) =>
    if bytes == code then return some (program, plain)
  | none => pure ()
  match ← Emu.programAt tracker.emu pc with
  | some program =>
    let plain := plainOf tracker.emu.config.memory pc program
    tracker.programs.modify (·.insert pc (code, program, plain))
    pure (some (program, plain))
  | none => pure none

/-- What a plain instruction does when nothing that it reads depends on anything and no branch is choosing what it does: its registers depend on nothing, which is all there is to say. -/
private def followPlain (tracker : Tracker) (thread : ThreadId) (plain : Plain) (insn depth : Nat) : IO Bool := do
  let _ ← registersOf tracker thread
  if let some (_, at_, guardDepth) := (← tracker.guards.get)[thread]? then
    if insn - at_ ≤ tracker.config.guardWindow && guardDepth ≤ depth && !plain.writes.isEmpty then return false
  let registers ← tracker.registers.get
  match registers[thread]? with
  | none => return false
  | some own =>
    let tainted := plain.reads.any fun name =>
      match own[name]? with
      | some tags => tags.any Tag.isNode
      | none => false
    if tainted then return false
  tracker.registers.modify (·.alter thread fun own =>
    some (plain.writes.foldl (fun own (name, tags) => own.insert name tags) (own.getD {})))
  pure true

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
  let held := (← tracker.calls.get).getD thread {}
  -- With the bit of Thumb, if it has that.
  let popped := held.pop pc
  let calls := match popped with
    | some (rest, _) => rest
    | none => held
  let depth := calls.depth
  -- What a function decided is over when it has returned, whatever is called next at that depth. What it returns is what it decided,
  -- though it may have set that before it branched, and the branch was that nothing changed it.
  if let some (guard, at_, guardDepth) := (← tracker.guards.get)[thread]? then
    if depth < guardDepth then
      tracker.guards.modify (·.erase thread)
      if insn - at_ ≤ tracker.config.guardWindow then resultUnderGuard tracker thread space pc insn guard
  let some (program, plain) ← programOf tracker pc | gap tracker pc
  if let some plain := plain then
    if ← followPlain tracker thread plain insn depth then
      if popped.isSome then tracker.calls.modify (·.insert thread calls)
      return
  let frame : Frame := {
    pc, thread, space, insn
    env := (← emu.state.get).env
    jumps := jumpsAlways program
    firstId := ← nextId tracker
    depth
    scratch := tracker.scratch }
  let scratch := tracker.scratch
  scratch.variables.set []
  scratch.memory.set []
  scratch.tags.set []
  scratch.newNodes.set #[]
  scratch.newRegisters.set []
  scratch.newGuard.set none
  scratch.incomplete.set false
  scratch.operands.set []
  scratch.link.set none
  scratch.jumped.set false
  try
    let _ ← perform tracker frame 65536 program
  catch error =>
    if error.toString == faultMessage then return
    gap tracker pc
    return
  if ← frame.scratch.incomplete.get then gap tracker pc
  for node in ← frame.scratch.newNodes.get do push tracker node
  -- The latest of each, as an instruction may write a byte twice.
  for (address, tag) in (← frame.scratch.tags.get).reverse do setTag tracker space address tag
  let written := (← frame.scratch.newRegisters.get).reverse
  if !written.isEmpty then
    let _ ← registersOf tracker thread
    -- In place, as nothing else holds what the thread has.
    tracker.registers.modify (·.alter thread fun registers =>
      some (written.foldl (fun registers (name, tags) => registers.insert name tags) (registers.getD {})))
  if let some guard := ← frame.scratch.newGuard.get then
    tracker.guards.modify (·.insert thread (guard, insn, depth))
  match ← frame.scratch.link.get, ← frame.scratch.jumped.get with
  | some site, true => tracker.calls.modify (·.insert thread (calls.push site))
  | _, _ => if popped.isSome then tracker.calls.modify (·.insert thread calls)

/-! ### Sources -/

/-- A source of `size` bytes in a thread's memory or registers, whose bytes have what is there now. -/
private def sourceNode (tracker : Tracker) (place : Place) (label : String) (offset : Option Nat) (values : ByteArray) : IO Nat := do
  let id ← nextId tracker
  let thread ← Emu.thread tracker.emu
  push tracker {
    id, insn := ← tracker.insn.get, pc := ← tracker.emu.pc.get, thread, space := ← Emu.spaceOf tracker.emu thread
    kind := .source label offset, place, values, inputs := #[] }
  pure id

/-- Says that the bytes of memory at `address` are a source called `label`. -/
def markMemory (tracker : Tracker) (address size : Nat) (label : String) (offset : Option Nat := none) : IO Unit := do
  if size == 0 then return
  let raw ← Emu.peek tracker.emu address size
  let id ← sourceNode tracker (.memory address) label offset raw
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

/-- Bytes go to a file or a pipe with what they came from, so that whoever reads them there has that. -/
private def carry (tracker : Tracker) (send : Send) : IO Unit := do
  if send.size == 0 then return
  let emu := tracker.emu
  let thread ← Emu.thread emu
  let space ← Emu.spaceOf emu thread
  let tags ← (List.range send.size).mapM fun index => tagAt tracker space (send.address + index)
  if tags.any Tag.isNode then
    let id ← nextId tracker
    let raw ← (Emu.peek emu send.address send.size).toBaseIO
    push tracker {
      id, insn := ← tracker.insn.get, pc := ← emu.pc.get, thread, space, kind := .carried send.label
      place := .stream send.space send.offset
      values := match raw with
        | .ok bytes => bytes
        | .error _ => ByteArray.empty
      inputs := (tags.map fun tag => if tag.isNode then [{ tag, edge := .data }] else []).toArray }
    for (tag, index) in tags.zipIdx do
      setRawTag tracker send.space (send.offset + index) (if tag.isNode then nodeTag id index else tag)
  else
    for (tag, index) in tags.zipIdx do setRawTag tracker send.space (send.offset + index) tag

/-- What a file holds comes to be in memory by a mapping: with what it came from where that is known, and as a source called `label` if one is given. -/
def mapped (tracker : Tracker) (address size space offset : Nat) (label : Option String) : IO Unit := do
  let current ← Emu.spaceOf tracker.emu (← Emu.thread tracker.emu)
  let source ← match label with
    | some label =>
      -- Its values are in the file, and all that it could be is many.
      let id ← sourceNode tracker (.memory address) label (some offset) ByteArray.empty
      pure (some id)
    | none => pure none
  for index in List.range size do
    let tag ← rawTag tracker space (offset + index)
    if tag.isNode then setTag tracker current (address + index) tag
    else if let some id := source then setTag tracker current (address + index) (nodeTag id index)

/-- The tags of bytes that the host moved go with them. -/
private def copied (tracker : Tracker) (from_ to size : Nat) : IO Unit := do
  let space ← Emu.spaceOf tracker.emu (← Emu.thread tracker.emu)
  for index in List.range size do
    setTag tracker space (to + index) (← tagAt tracker space (from_ + index))

/-- Bytes that came from outside any instruction: a source if a call that is one is in progress, and otherwise what nobody made. -/
private def externalWrite (tracker : Tracker) (address size : Nat) (cleared : Bool) : IO Unit := do
  let space ← Emu.spaceOf tracker.emu (← Emu.thread tracker.emu)
  match ← tracker.label.get with
  | some (label, offset) =>
    if cleared then clearTags tracker space address size
    else
      let done ← tracker.written.get
      tracker.written.set (done + size)
      markMemory tracker address size label (offset.map (· + done))
      -- What is known of where it was has what it came from.
      if let some (kept, start) := ← tracker.backing.get then
        for index in List.range size do
          let tag ← rawTag tracker kept (start + done + index)
          if tag.isNode then setTag tracker space (address + index) tag
  | none => clearTags tracker space address size

private def wordVar (emu : Emu) (name : String) : IO Bap.Var := do
  pure ⟨name, .imm (← Emu.wordWidth emu), 0, false⟩

private def callStarts (tracker : Tracker) (number : Nat) (args : List Nat) : IO Unit := do
  tracker.calling.set (some (number, args))
  tracker.written.set 0
  tracker.label.set (← tracker.config.describe number args)
  tracker.backing.set (← tracker.config.backing number args)
  for send in ← tracker.config.sends number args do carry tracker send

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
  tracker.backing.set none

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
    backing := ← IO.mkRef none
    outer := ← IO.mkRef []
    written := ← IO.mkRef 0
    gaps := ← IO.mkRef {}
    restores := ← IO.mkRef []
    loadedFrom := ← IO.mkRef none
    scratch := {
      variables := ← IO.mkRef []
      memory := ← IO.mkRef []
      tags := ← IO.mkRef []
      newNodes := ← IO.mkRef #[]
      newRegisters := ← IO.mkRef []
      newGuard := ← IO.mkRef none
      incomplete := ← IO.mkRef false
      operands := ← IO.mkRef []
      link := ← IO.mkRef none
      jumped := ← IO.mkRef false } }
  let width ← Emu.wordWidth emu
  let _ ← Emu.onCode emu (0, 2 ^ width - 1) fun _ pc => follow tracker pc
  emu.syscallStarts.modify (callStarts tracker :: ·)
  emu.syscallEnds.modify (callEnds tracker :: ·)
  emu.memoryChanged.modify (externalWrite tracker :: ·)
  emu.memoryCopied.modify (copied tracker :: ·)
  emu.hostStarts.modify ((fun label => do
    tracker.written.set 0
    let held ← tracker.label.get
    tracker.outer.modify (held :: ·)
    tracker.label.set (some (label, none))) :: ·)
  emu.hostEnds.modify ((fun register => do
    if let (some (label, _), some register) := (← tracker.label.get, register) then
      markRegister tracker (← wordVar emu register) s!"{label} result"
    match ← tracker.outer.get with
    | previous :: rest =>
      tracker.label.set previous
      tracker.outer.set rest
    | [] => tracker.label.set none) :: ·)
  emu.processHooks.modify ((fun parent child => forked tracker parent child) :: ·)
  pure tracker

/-! ### Saying where a byte came from -/

/-- What is known of a byte that a question was asked about. -/
inductive Origin where
  /-- Nothing that was followed has written it: it was there when tracking started, or the host put it there. -/
  | untouched
  /-- Nothing marked reached it: this is the instruction that computed it, or the last to move it between registers. -/
  | clean (pc : Nat)
  | tainted (node : Nat) (byte : Nat)
  deriving DecidableEq, Repr

/-- A step of the way that a byte took, oldest first: the byte of a node, and how the next step depends on it. -/
structure Step where
  node : Node
  byte : Nat
  edge : Edge
  deriving Repr

/-- Where a byte came from: what it is, the way it took from a source, the sources it reached, and what can't be said of it. -/
structure Explanation where
  origin : Origin
  /-- Of a byte that nothing followed wrote, when the machine was put back to what it was before then and by what, the latest last: what it is came from there, or from before tracking started. -/
  restoredFrom : List (Nat × String) := []
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

/-- What a byte depends on, each by its strongest way: the weakest edge on a way is what it is, and a byte is reached first by data alone,
then with what selected it, then by branches and then by pointers, each of those breadth first. That is one search of what it reaches, in
which a byte goes into the queue of each edge at most once, where there were one for each edge and one of all. It gives each byte's way back
to the root, the bytes in the order that they were reached, how weak each one's way is, and whether what led to any has gone. -/
private def search (tracker : Tracker) (root : Tag) :
    IO (Std.HashMap Tag (Tag × Edge) × Array Tag × Std.HashMap Tag Nat × Bool) := do
  let mut parents : Std.HashMap Tag (Tag × Edge) := {}
  let mut levels : Std.HashMap Tag Nat := ({} : Std.HashMap Tag Nat).insert root 0
  let mut queues : Array (Array Tag) := #[#[root], #[], #[], #[]]
  let mut order : Array Tag := #[]
  let mut truncated := false
  for level in List.range 4 do
    let mut at_ := 0
    while at_ < queues[level]!.size do
      let tag := queues[level]![at_]!
      at_ := at_ + 1
      -- What a stronger way reached already, it went on from then.
      if levels.getD tag 4 < level then continue
      order := order.push tag
      match ← node? tracker tag.node with
      | none => truncated := true
      | some node =>
        let next := (inputsOf node tag.byte).toArray.qsort (fun left right => edgeRank left.edge < edgeRank right.edge)
        for input in next do
          if input.tag.isNode then
            let reached := max level (edgeRank input.edge)
            if reached < levels.getD input.tag 4 then
              levels := levels.insert input.tag reached
              parents := parents.insert input.tag (tag, input.edge)
              queues := queues.modify reached (·.push input.tag)
  pure (parents, order, levels, truncated)

private partial def walkFrom (tracker : Tracker) (parents : Std.HashMap Tag (Tag × Edge)) (root tag : Tag) (edge : Edge) (out : Array Step) : IO (Array Step) := do
  match ← node? tracker tag.node with
  | none => pure out
  | some node =>
    let out := out.push { node, byte := tag.byte, edge }
    if tag == root then pure out
    else
      match parents[tag]? with
      | some (parent, edgeThere) => walkFrom tracker parents root parent edgeThere out
      | none => pure out

/-- The sources and branches of what a search reached, each source with the weakest edge of its strongest way. -/
private def reached (tracker : Tracker) (order : Array Tag) (levels : Std.HashMap Tag Nat) :
    IO (List (Node × Nat × Edge) × List Node) := do
  let mut sources : Array (Node × Nat × Edge) := #[]
  let mut branches : Array Node := #[]
  for tag in order do
    if let some node := ← node? tracker tag.node then
      match node.kind with
      | .source .. =>
        let edge := match levels.getD tag 0 with | 0 => Edge.data | 1 => .condition | 2 => .guard | _ => .address
        sources := sources.push (node, tag.byte, edge)
      | .branch _ => branches := branches.push node
      | _ => pure ()
  pure (sources.toList, branches.toList)

/-- Every source that a byte depends on, with the weakest edge of its strongest way, which is what `explainTag` says of them without the way to any. -/
def sourcesOf (tracker : Tracker) (root : Tag) : IO (List (Node × Nat × Edge)) := do
  if !root.isNode then return []
  let (_, order, levels, _) ← search tracker root
  pure (← reached tracker order levels).1

/-- Where the byte with this tag came from. -/
def explainTag (tracker : Tracker) (root : Tag) : IO Explanation := do
  if !root.isNode then
    let restores := (← tracker.restores.get).reverse ++ (← tracker.loadedFrom.get).toList
    return { origin := if root.isClean then .clean (root / 2) else .untouched
             restoredFrom := if root.isClean then [] else restores }
  let (parents, order, levels, truncated) ← search tracker root
  let (sources, branches) ← reached tracker order levels
  -- The strongest way to a source is the first that the search reached; without one, the way to what it reached last.
  let target := match sources.head? with
    | some (node, byte, _) => some (nodeTag node.id byte)
    | none => order.back?
  let path ← match target with
    | some tag => walkFrom tracker parents root tag .data #[]
    | none => pure #[]
  pure {
    origin := .tainted root.node root.byte
    path := path.toList, sources, branches := (branches.toArray.qsort fun left right => left.id < right.id).toList
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
    | .stream _ offset => s!"at {offset + step.byte}"
  let value := match node.valueAt step.byte with
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
    | .carried label => label
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
    -- A carry goes through the bytes of a node, which is one thing that happened.
    let middle := middle.foldr (fun step out => match out with
      | next :: _ => if next.node.id == step.node.id then out else step :: out
      | [] => [step]) []
    match middle.getLast? with
    | some final => if final.node.id == last.node.id then middle else middle ++ [last]
    | none => [last]

/-- What an explanation says, as text for a person. -/
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

/-- That the machine was put back, as this says. Going on from a checkpoint is noted apart, as what is saved again has to be what was. -/
def noteRestored (tracker : Tracker) (label : String) : IO Unit := do
  if label.startsWith "checkpoint" then tracker.loadedFrom.set (some (← tracker.insn.get, label))
  else tracker.restores.modify ((← tracker.insn.get, label) :: ·)

/-! ### For a checkpoint -/

open Bap.Linux.Wire

private def putOptionNat (out : ByteArray) : Option Nat → ByteArray
  | none => putNat out 0
  | some value => putNat out (value + 1)

private def getOptionNat : Decoder (Option Nat) := fun data at_ => do
  let (value, at_) ← getNat data at_
  .ok (if value == 0 then none else some (value - 1), at_)

private def edgeOf : Nat → Except String Edge
  | 0 => .ok .data
  | 1 => .ok .condition
  | 2 => .ok .guard
  | 3 => .ok .address
  | _ => .error "a taint checkpoint with an edge that isn't one"

private def putInput (out : ByteArray) (input : Input) : ByteArray := putNat (putNat out input.tag) (edgeRank input.edge)

private def getInput : Decoder Input := fun data at_ => do
  let (tag, at_) ← getNat data at_
  let (rank, at_) ← getNat data at_
  .ok ({ tag, edge := ← edgeOf rank }, at_)

private def putKind (out : ByteArray) : NodeKind → ByteArray
  | .source label offset => putOptionNat (putText (putNat out 0) label) offset
  | .copy => putNat out 1
  | .compute => putNat out 2
  | .constant => putNat out 3
  | .branch target => putOptionNat (putNat out 4) target
  | .carried label => putText (putNat out 5) label

private def getKind : Decoder NodeKind := fun data at_ => do
  let (which, at_) ← getNat data at_
  match which with
  | 0 =>
    let (label, at_) ← getText data at_
    let (offset, at_) ← getOptionNat data at_
    .ok (.source label offset, at_)
  | 1 => .ok (.copy, at_)
  | 2 => .ok (.compute, at_)
  | 3 => .ok (.constant, at_)
  | 4 =>
    let (target, at_) ← getOptionNat data at_
    .ok (.branch target, at_)
  | 5 =>
    let (label, at_) ← getText data at_
    .ok (.carried label, at_)
  | _ => .error "a taint checkpoint with a node that isn't one"

private def putPlace (out : ByteArray) : Place → ByteArray
  | .register name => putText (putNat out 0) name
  | .memory address => putNat (putNat out 1) address
  | .control => putNat out 2
  | .stream space offset => putNat (putNat (putNat out 3) space) offset

private def getPlace : Decoder Place := fun data at_ => do
  let (which, at_) ← getNat data at_
  match which with
  | 0 =>
    let (name, at_) ← getText data at_
    .ok (.register name, at_)
  | 1 =>
    let (address, at_) ← getNat data at_
    .ok (.memory address, at_)
  | 2 => .ok (.control, at_)
  | 3 =>
    let (space, at_) ← getNat data at_
    let (offset, at_) ← getNat data at_
    .ok (.stream space offset, at_)
  | _ => .error "a taint checkpoint with a place that isn't one"

private def putNode (out : ByteArray) (node : Node) : ByteArray :=
  let out := putNat (putNat (putNat (putNat (putNat out node.id) node.insn) node.pc) node.thread) node.space
  let out := putPlace (putKind out node.kind) node.place
  let out := putBytes out node.values
  let out := putList (putList putInput) out node.inputs.toList
  putOptionNat out node.guard

private def getNode : Decoder Node := fun data at_ => do
  let (id, at_) ← getNat data at_
  let (insn, at_) ← getNat data at_
  let (pc, at_) ← getNat data at_
  let (thread, at_) ← getNat data at_
  let (space, at_) ← getNat data at_
  let (kind, at_) ← getKind data at_
  let (place, at_) ← getPlace data at_
  let (values, at_) ← getBytes data at_
  let (inputs, at_) ← getList (getList getInput) data at_
  let (guard, at_) ← getOptionNat data at_
  .ok ({ id, insn, pc, thread, space, kind, place, values, inputs := inputs.toArray, guard }, at_)

private def putPage (out : ByteArray) (entry : (Nat × Nat) × Array Tag) : ByteArray :=
  let tagged := entry.2.toList.zipIdx.filter (·.1 != 0)
  putList (fun out pair => putNat (putNat out pair.2) pair.1) (putNat (putNat out entry.1.1) entry.1.2) tagged

private def getPage : Decoder ((Nat × Nat) × Array Tag) := fun data at_ => do
  let (space, at_) ← getNat data at_
  let (page, at_) ← getNat data at_
  let (tagged, at_) ← getList (fun data at_ => do
    let (index, at_) ← getNat data at_
    let (tag, at_) ← getNat data at_
    .ok ((index, tag), at_)) data at_
  let tags := tagged.foldl (init := Array.replicate 4096 (0 : Tag)) fun tags (index, tag) => tags.setIfInBounds index tag
  .ok (((space, page), tags), at_)

private def putRegisters (out : ByteArray) (entry : Nat × Std.HashMap String (Array Tag)) : ByteArray :=
  let sorted := entry.2.toList.toArray.qsort (fun left right => left.1 < right.1) |>.toList
  putList (fun out pair => putList putNat (putText out pair.1) pair.2.toList) (putNat out entry.1) sorted

private def getRegisters : Decoder (Nat × Std.HashMap String (Array Tag)) := fun data at_ => do
  let (thread, at_) ← getNat data at_
  let (registers, at_) ← getList (fun data at_ => do
    let (name, at_) ← getText data at_
    let (tags, at_) ← getList getNat data at_
    .ok ((name, tags.toArray), at_)) data at_
  .ok ((thread, registers.foldl (fun map pair => map.insert pair.1 pair.2) {}), at_)

private def byKey {α : Type} (entries : List (Nat × α)) : List (Nat × α) :=
  (entries.toArray.qsort fun left right => left.1 < right.1).toList

/-- All that it knows, in an order that the same run always has. -/
def save (tracker : Tracker) : IO ByteArray := do
  let out := putList putNode ByteArray.empty (← tracker.nodes.get).toList
  let out := putNat (putNat out (← tracker.base.get)) (← tracker.insn.get)
  let out := putList putRegisters out (byKey (← tracker.registers.get).toList)
  let pages := ((← tracker.pages.get).toList.toArray.qsort fun left right =>
    left.1.1 < right.1.1 || (left.1.1 == right.1.1 && left.1.2 < right.1.2)).toList
  let out := putList putPage out pages
  let out := putList (fun out entry => putNat (putNat (putNat (putNat out entry.1) entry.2.1) entry.2.2.1) entry.2.2.2) out
    (byKey (← tracker.guards.get).toList)
  let out := putList (fun out entry => putList putNat (putNat out entry.1) entry.2.sites) out (byKey (← tracker.calls.get).toList)
  let out := putList (fun out entry => putNat (putNat out entry.1) entry.2) out (byKey (← tracker.lastOfGroup.get).toList)
  let out := putList (fun out entry => putNat (putNat out entry.1) entry.2) out (byKey (← tracker.gaps.get).toList)
  pure (putList (fun out entry => putText (putNat out entry.1) entry.2) out (← tracker.restores.get))

private def getNatPair : Decoder (Nat × Nat) := fun data at_ => do
  let (left, at_) ← getNat data at_
  let (right, at_) ← getNat data at_
  .ok ((left, right), at_)

/-- What `save` gave, and where it ends. -/
def load (tracker : Tracker) (data : ByteArray) (at_ : Nat := 0) : IO Nat := do
  let decoded : Except String _ := do
    let (nodes, at_) ← getList getNode data at_
    let (base, at_) ← getNat data at_
    let (insn, at_) ← getNat data at_
    let (registers, at_) ← getList getRegisters data at_
    let (pages, at_) ← getList getPage data at_
    let (guards, at_) ← getList (fun data at_ => do
      let (thread, at_) ← getNat data at_
      let (tag, at_) ← getNat data at_
      let (insn, at_) ← getNat data at_
      let (depth, at_) ← getNat data at_
      .ok ((thread, tag, insn, depth), at_)) data at_
    let (calls, at_) ← getList (fun data at_ => do
      let (thread, at_) ← getNat data at_
      let (sites, at_) ← getList getNat data at_
      .ok ((thread, sites), at_)) data at_
    let (lastOfGroup, at_) ← getList getNatPair data at_
    let (gaps, at_) ← getList getNatPair data at_
    let (restores, at_) ← getList (fun data at_ => do
      let (insn, at_) ← getNat data at_
      let (label, at_) ← getText data at_
      .ok ((insn, label), at_)) data at_
    .ok (nodes, base, insn, registers, pages, guards, calls, lastOfGroup, gaps, restores, at_)
  let (nodes, base, insn, registers, pages, guards, calls, lastOfGroup, gaps, restores, at_) ← IO.ofExcept decoded
  tracker.restores.set restores
  tracker.nodes.set nodes.toArray
  tracker.base.set base
  tracker.insn.set insn
  tracker.registers.set (registers.foldl (fun map pair => map.insert pair.1 pair.2) {})
  tracker.pages.set (pages.foldl (fun map pair => map.insert pair.1 pair.2) {})
  tracker.guards.set (guards.foldl (fun map pair => map.insert pair.1 pair.2) {})
  tracker.calls.set (calls.foldl (fun map pair => map.insert pair.1 (CallSites.ofSites pair.2)) {})
  tracker.lastOfGroup.set (lastOfGroup.foldl (fun map pair => map.insert pair.1 pair.2) {})
  tracker.gaps.set (gaps.foldl (fun map pair => map.insert pair.1 pair.2) {})
  pure at_

end Tracker

end Bap.Analysis.DynamicTaint
