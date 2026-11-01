/-! The bytes of a checkpoint: numbers of as many bytes as they need, so that none is too wide for the format, lists, and tables in an
order of their own. -/

namespace Bap.Linux

namespace Wire

/-- A number, seven bits at a time from the low end. A byte with its high bit set has another after it. -/
def putNat (out : ByteArray) (value : Nat) : ByteArray :=
  if value < 128 then out.push value.toUInt8
  else putNat (out.push (value % 128 + 128).toUInt8) (value / 128)
termination_by value
decreasing_by omega

def putBytes (out data : ByteArray) : ByteArray := putNat out data.size ++ data

def putText (out : ByteArray) (text : String) : ByteArray := putBytes out text.toUTF8

def putList (put : ByteArray → α → ByteArray) (out : ByteArray) (items : List α) : ByteArray :=
  items.foldl put (putNat out items.length)

/-- What a decoder gives, and the offset after it. -/
abbrev Decoder (α : Type) := ByteArray → Nat → Except String (α × Nat)

def getNatFrom (data : ByteArray) : Nat → Nat → Nat → Nat → Except String (Nat × Nat)
  | 0, _, _, _ => .error "truncated Linux checkpoint"
  | fuel + 1, at_, scale, value =>
    if h : at_ < data.size then
      let byte := data[at_].toNat
      if byte < 128 then .ok (value + byte * scale, at_ + 1)
      else getNatFrom data fuel (at_ + 1) (scale * 128) (value + (byte - 128) * scale)
    else .error "truncated Linux checkpoint"

def getNat : Decoder Nat := fun data at_ => getNatFrom data (data.size - at_) at_ 1 0

def getBytes : Decoder ByteArray := fun data at_ => do
  let (size, at_) ← getNat data at_
  if at_ + size ≤ data.size then .ok (data.extract at_ (at_ + size), at_ + size)
  else .error "truncated Linux checkpoint"

def getText : Decoder String := fun data at_ => do
  let (bytes, at_) ← getBytes data at_
  match String.fromUTF8? bytes with
  | some text => .ok (text, at_)
  | none => .error "a Linux checkpoint with a path that isn't text"

/-- `count` items. A list can't have more of them than there are bytes left, which a bad file might say. -/
def getItems (get : Decoder α) (data : ByteArray) : Nat → Nat → List α → Except String (List α × Nat)
  | 0, at_, items => .ok (items.reverse, at_)
  | count + 1, at_, items => do
    let (item, at_) ← get data at_
    getItems get data count at_ (item :: items)

def getList (get : Decoder α) : Decoder (List α) := fun data at_ => do
  let (count, at_) ← getNat data at_
  getItems get data count at_ []

/-- A truth value. -/
def putFlag (out : ByteArray) (value : Bool) : ByteArray := putNat out (if value then 1 else 0)

def getFlag : Decoder Bool := fun data at_ => do
  let (value, at_) ← getNat data at_
  match value with
  | 0 => .ok (false, at_)
  | 1 => .ok (true, at_)
  | _ => .error "a checkpoint with a truth value that isn't"

def putOption (put : ByteArray → α → ByteArray) (out : ByteArray) : Option α → ByteArray
  | none => putNat out 0
  | some value => put (putNat out 1) value

def getOption (get : Decoder α) : Decoder (Option α) := fun data at_ => do
  let (tag, at_) ← getNat data at_
  match tag with
  | 0 => .ok (none, at_)
  | 1 =>
    let (value, at_) ← get data at_
    .ok (some value, at_)
  | _ => .error "a checkpoint with an option that isn't"

/-- Bytes before bytes, as they compare in a file. -/
private def bytesBefore (left right : ByteArray) : Bool :=
  let rec go : Nat → Bool
    | 0 => left.size ≤ right.size
    | fuel + 1 =>
      let index := min left.size right.size - (fuel + 1)
      if left[index]! < right[index]! then true
      else if right[index]! < left[index]! then false
      else go fuel
  go (min left.size right.size)

/-- The entries of a table or a set, in the order of their bytes, whatever order they came in: what a `HashMap` gives depends on what
was done to it, and the same state has to make the same file. `getList` reads it back. -/
def putSorted (put : ByteArray → α → ByteArray) (out : ByteArray) (items : List α) : ByteArray :=
  let encoded := (items.map fun item => put ByteArray.empty item).mergeSort fun left right => bytesBefore left right
  encoded.foldl (· ++ ·) (putNat out items.length)

/-- All the bytes were read: a checkpoint with more than it should have isn't one. -/
def expectEnd (data : ByteArray) (at_ : Nat) : Except String Unit :=
  if at_ == data.size then .ok () else .error "a checkpoint with bytes after its end"

/-- FNV-1a of 64 bits, from what came before. It says that bytes changed by accident or that they are of something else, and
doesn't keep out anyone who means to. -/
def digest (data : ByteArray) (seed : UInt64 := 0xcbf29ce484222325) : UInt64 :=
  data.foldl (init := seed) fun hash byte => (hash ^^^ byte.toUInt64) * 0x100000001b3

/-- A number of exactly eight bytes, which can be found from the end of a file. -/
def fixedBytes (value : UInt64) : ByteArray :=
  ByteArray.mk ((List.range 8).map fun index => (value >>> (8 * index).toUInt64).toUInt8).toArray

def ofFixedBytes (data : ByteArray) (at_ : Nat) : UInt64 :=
  (List.range 8).foldr (init := 0) fun index value => value <<< 8 ||| (data[at_ + index]!).toUInt64

end Wire

/-- What a model of a runtime holds that can change what a guest does, where the kernel and the emulator don't have it: locks, what
threads wait for, debuggers, allocators, handles of a managed language, counters of calls. `save` makes bytes of all of it, with
`Wire.putSorted` for what is in a table, so that the same state has the same bytes. `load` puts it back, or throws without changing
anything. -/
structure ModelState where
  save : IO ByteArray
  load : ByteArray → IO Unit

end Bap.Linux
