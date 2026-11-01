import Bap.Linux.Kernel

/-! What a kernel is as plain data and as bytes, to go in a checkpoint. Tables are sorted, so that a kernel has one image and the
same state makes the same file. A number has as many bytes as it needs, so that none of them can be too wide for the format. -/

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

end Wire

/-- A process, with its descriptors in order. -/
structure ProcessImage where
  group : Nat
  descriptors : List (Nat × Nat × Bool)
  cwd : String
  umask : Nat
  breakStart : Nat
  breakEnd : Nat
  deriving DecidableEq

/-- An inode, with what is in it as a tag and bytes: a link has its target in them. -/
structure InodeImage where
  number : Nat
  mode : Nat
  kind : Nat
  data : ByteArray
  deriving DecidableEq

/-- A kernel as plain data. -/
structure Image where
  paths : List (String × Nat)
  inodes : List InodeImage
  nextInode : Nat
  openFiles : List (Nat × Nat × Nat × Nat)
  nextOpenFile : Nat
  processes : List ProcessImage
  output : ByteArray
  clock : Nat
  cycles : Nat
  deriving DecidableEq

private def sorted (items : List (Nat × α)) : List (Nat × α) :=
  (items.toArray.qsort fun left right => left.1 < right.1).toList

/-- The image of a kernel. -/
def Kernel.image (kernel : Kernel) : Image where
  paths := (kernel.paths.toList.toArray.qsort fun left right => left.1 < right.1).toList
  inodes := (sorted kernel.inodes.toList).map fun (number, inode) =>
    let (kind, data) := match inode.content with
      | .file data => (0, data)
      | .directory => (1, ByteArray.empty)
      | .symlink target => (2, target.toUTF8)
      | .console input => (3, input)
    { number, mode := inode.mode, kind, data }
  nextInode := kernel.nextInode
  openFiles := (sorted kernel.openFiles.toList).map fun (id, file) => (id, file.inode, file.offset, file.flags)
  nextOpenFile := kernel.nextOpenFile
  processes := (sorted kernel.processes.toList).map fun (group, process) =>
    { group, cwd := process.cwd, umask := process.umask, breakStart := process.breakStart, breakEnd := process.breakEnd
      descriptors := (sorted process.descriptors.toList).map fun (fd, entry) => (fd, entry.openFile, entry.closeOnExec) }
  output := kernel.output
  clock := kernel.clock
  cycles := kernel.cycles

/-- The kernel of an image, or why there can't be one. -/
def Image.kernel (image : Image) : Except String Kernel := do
  let inodes ← image.inodes.foldlM (init := ({} : Std.HashMap Nat Inode)) fun inodes entry => do
    let content ← match entry.kind with
      | 0 => pure (Content.file entry.data)
      | 1 => pure Content.directory
      | 2 =>
        match String.fromUTF8? entry.data with
        | some target => pure (Content.symlink target)
        | none => .error "a Linux checkpoint with a link that isn't text"
      | 3 => pure (Content.console entry.data)
      | kind => .error s!"a Linux checkpoint with an inode of kind {kind}"
    pure (inodes.insert entry.number { number := entry.number, content, mode := entry.mode })
  pure {
    paths := image.paths.foldl (init := {}) fun paths entry => paths.insert entry.1 entry.2
    inodes
    nextInode := image.nextInode
    openFiles := image.openFiles.foldl (init := {}) fun files (id, inode, offset, flags) => files.insert id { inode, offset, flags }
    nextOpenFile := image.nextOpenFile
    processes := image.processes.foldl (init := {}) fun processes process =>
      processes.insert process.group
        { cwd := process.cwd, umask := process.umask, breakStart := process.breakStart, breakEnd := process.breakEnd
          descriptors := process.descriptors.foldl (init := {}) fun descriptors (fd, openFile, closeOnExec) =>
            descriptors.insert fd { openFile, closeOnExec } }
    output := image.output
    clock := image.clock
    cycles := image.cycles }

namespace Image

open Wire

def putBool (out : ByteArray) (value : Bool) : ByteArray := putNat out (if value then 1 else 0)

def getBool : Decoder Bool := fun data at_ => do
  let (value, at_) ← getNat data at_
  match value with
  | 0 => .ok (false, at_)
  | 1 => .ok (true, at_)
  | _ => .error "a Linux checkpoint with a truth value that isn't"

def putDescriptor (out : ByteArray) (entry : Nat × Nat × Bool) : ByteArray :=
  putBool (putNat (putNat out entry.1) entry.2.1) entry.2.2

def getDescriptor : Decoder (Nat × Nat × Bool) := fun data at_ => do
  let (fd, at_) ← getNat data at_
  let (openFile, at_) ← getNat data at_
  let (closeOnExec, at_) ← getBool data at_
  .ok ((fd, openFile, closeOnExec), at_)

def putProcess (out : ByteArray) (process : ProcessImage) : ByteArray :=
  let out := putNat out process.group
  let out := putList putDescriptor out process.descriptors
  let out := putText out process.cwd
  let out := putNat out process.umask
  putNat (putNat out process.breakStart) process.breakEnd

def getProcess : Decoder ProcessImage := fun data at_ => do
  let (group, at_) ← getNat data at_
  let (descriptors, at_) ← getList getDescriptor data at_
  let (cwd, at_) ← getText data at_
  let (umask, at_) ← getNat data at_
  let (breakStart, at_) ← getNat data at_
  let (breakEnd, at_) ← getNat data at_
  .ok ({ group, descriptors, cwd, umask, breakStart, breakEnd }, at_)

def putInode (out : ByteArray) (inode : InodeImage) : ByteArray :=
  putBytes (putNat (putNat (putNat out inode.number) inode.mode) inode.kind) inode.data

def getInode : Decoder InodeImage := fun data at_ => do
  let (number, at_) ← getNat data at_
  let (mode, at_) ← getNat data at_
  let (kind, at_) ← getNat data at_
  let (bytes, at_) ← getBytes data at_
  .ok ({ number, mode, kind, data := bytes }, at_)

def putPath (out : ByteArray) (entry : String × Nat) : ByteArray := putNat (putText out entry.1) entry.2

def getPath : Decoder (String × Nat) := fun data at_ => do
  let (path, at_) ← getText data at_
  let (inode, at_) ← getNat data at_
  .ok ((path, inode), at_)

def putOpenFile (out : ByteArray) (entry : Nat × Nat × Nat × Nat) : ByteArray :=
  putNat (putNat (putNat (putNat out entry.1) entry.2.1) entry.2.2.1) entry.2.2.2

def getOpenFile : Decoder (Nat × Nat × Nat × Nat) := fun data at_ => do
  let (id, at_) ← getNat data at_
  let (inode, at_) ← getNat data at_
  let (offset, at_) ← getNat data at_
  let (flags, at_) ← getNat data at_
  .ok ((id, inode, offset, flags), at_)

/-- The bytes of an image, after `out`. -/
def encode (out : ByteArray) (image : Image) : ByteArray :=
  let out := putList putPath out image.paths
  let out := putList putInode out image.inodes
  let out := putNat out image.nextInode
  let out := putList putOpenFile out image.openFiles
  let out := putNat out image.nextOpenFile
  let out := putList putProcess out image.processes
  let out := putBytes out image.output
  putNat (putNat out image.clock) image.cycles

/-- An image from bytes, and where they end. -/
def decode : Decoder Image := fun data at_ => do
  let (paths, at_) ← getList getPath data at_
  let (inodes, at_) ← getList getInode data at_
  let (nextInode, at_) ← getNat data at_
  let (openFiles, at_) ← getList getOpenFile data at_
  let (nextOpenFile, at_) ← getNat data at_
  let (processes, at_) ← getList getProcess data at_
  let (output, at_) ← getBytes data at_
  let (clock, at_) ← getNat data at_
  let (cycles, at_) ← getNat data at_
  .ok ({ paths, inodes, nextInode, openFiles, nextOpenFile, processes, output, clock, cycles }, at_)

end Image

end Bap.Linux
