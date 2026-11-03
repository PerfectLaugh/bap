import Bap.Jit
import Bap.Linux.Kernel
import Bap.Linux.Wire

/-! What a kernel is as plain data and as bytes, to go in a checkpoint. Tables are sorted, so that a kernel has one image and the
same state makes the same file. A number has as many bytes as it needs, so that none of them can be too wide for the format. -/

namespace Bap.Linux

/-- A process, with its descriptors in order. -/
structure ProcessImage where
  group : Nat
  descriptors : List (Nat × Nat × Bool)
  cwd : String
  umask : Nat
  breakStart : Nat
  breakEnd : Nat
  command : List String
  environment : List String
  program : String
  auxiliary : List Nat
  mappings : List FileMapping
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

/-- The bytes of a socket, which are those of its inode. -/
def socketBytes (socket : Socket) : ByteArray :=
  let putMessage (out : ByteArray) (message : Message) : ByteArray :=
    Wire.putList Wire.putNat (Wire.putOption Wire.putText (Wire.putBytes out message.data) message.sender) message.rights
  let out := Wire.putNat ByteArray.empty socket.type
  let out := Wire.putOption Wire.putText out socket.name
  let out := Wire.putOption Wire.putNat out socket.peer
  let out := Wire.putFlag out socket.listening
  let out := Wire.putList Wire.putNat out socket.pending
  let out := Wire.putFlag out socket.waiting
  let out := Wire.putList putMessage out socket.incoming.toList
  let out := Wire.putFlag (Wire.putFlag out socket.readShut) socket.writeShut
  Wire.putNat out socket.owner

/-- A socket from the bytes of its inode. -/
def socketOfBytes (data : ByteArray) : Except String Socket := do
  let getMessage : Wire.Decoder Message := fun data at_ => do
    let (bytes, at_) ← Wire.getBytes data at_
    let (sender, at_) ← Wire.getOption Wire.getText data at_
    let (rights, at_) ← Wire.getList Wire.getNat data at_
    .ok ({ data := bytes, sender, rights }, at_)
  let (type, at_) ← Wire.getNat data 0
  let (name, at_) ← Wire.getOption Wire.getText data at_
  let (peer, at_) ← Wire.getOption Wire.getNat data at_
  let (listening, at_) ← Wire.getFlag data at_
  let (pending, at_) ← Wire.getList Wire.getNat data at_
  let (waiting, at_) ← Wire.getFlag data at_
  let (incoming, at_) ← Wire.getList getMessage data at_
  let (readShut, at_) ← Wire.getFlag data at_
  let (writeShut, at_) ← Wire.getFlag data at_
  let (owner, at_) ← Wire.getNat data at_
  Wire.expectEnd data at_
  pure { type, name, peer, listening, pending, waiting, incoming := incoming.toArray, readShut, writeShut, owner }

/-- The image of a kernel. -/
def Kernel.image (kernel : Kernel) : Image where
  paths := (kernel.paths.toList.toArray.qsort fun left right => left.1 < right.1).toList
  inodes := (sorted kernel.inodes.toList).map fun (number, inode) =>
    let (kind, data) := match inode.content with
      | .file data => (0, data)
      | .directory => (1, ByteArray.empty)
      | .symlink target => (2, target.toUTF8)
      | .console input => (3, input)
      | .generated name => (4, name.toUTF8)
      | .pipe buffer head consumed => (5, Wire.putBytes (Wire.putNat ByteArray.empty consumed) (buffer.extract head buffer.size))
      | .socket socket => (6, socketBytes socket)
    { number, mode := inode.mode, kind, data }
  nextInode := kernel.nextInode
  openFiles := (sorted kernel.openFiles.toList).map fun (id, file) => (id, file.inode, file.offset, file.flags)
  nextOpenFile := kernel.nextOpenFile
  processes := (sorted kernel.processes.toList).map fun (group, process) =>
    { group, cwd := process.cwd, umask := process.umask, breakStart := process.breakStart, breakEnd := process.breakEnd
      command := process.command, environment := process.environment, program := process.program
      auxiliary := process.auxiliary, mappings := process.mappings
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
      | 4 =>
        match String.fromUTF8? entry.data with
        | some name => pure (Content.generated name)
        | none => .error "a Linux checkpoint with a generator that isn't text"
      | 5 =>
        let (consumed, at_) ← Wire.getNat entry.data 0
        let (buffer, _) ← Wire.getBytes entry.data at_
        pure (Content.pipe buffer 0 consumed)
      | 6 => pure (Content.socket (← socketOfBytes entry.data))
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
          command := process.command, environment := process.environment, program := process.program
          auxiliary := process.auxiliary, mappings := process.mappings
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

def putMapping (out : ByteArray) (mapping : FileMapping) : ByteArray :=
  let out := putNat (putNat out mapping.start) mapping.size
  let out := putNat (putNat out mapping.inode) mapping.offset
  putBool (putBool out mapping.shared) mapping.mayWrite

def getMapping : Decoder FileMapping := fun data at_ => do
  let (start, at_) ← getNat data at_
  let (size, at_) ← getNat data at_
  let (inode, at_) ← getNat data at_
  let (offset, at_) ← getNat data at_
  let (shared, at_) ← getBool data at_
  let (mayWrite, at_) ← getBool data at_
  .ok ({ start, size, inode, offset, shared, mayWrite }, at_)

def putProcess (out : ByteArray) (process : ProcessImage) : ByteArray :=
  let out := putNat out process.group
  let out := putList putDescriptor out process.descriptors
  let out := putText out process.cwd
  let out := putNat out process.umask
  let out := putNat (putNat out process.breakStart) process.breakEnd
  let out := putList putText out process.command
  let out := putList putText out process.environment
  let out := putText out process.program
  let out := putList putNat out process.auxiliary
  putList putMapping out process.mappings

def getProcess : Decoder ProcessImage := fun data at_ => do
  let (group, at_) ← getNat data at_
  let (descriptors, at_) ← getList getDescriptor data at_
  let (cwd, at_) ← getText data at_
  let (umask, at_) ← getNat data at_
  let (breakStart, at_) ← getNat data at_
  let (breakEnd, at_) ← getNat data at_
  let (command, at_) ← getList getText data at_
  let (environment, at_) ← getList getText data at_
  let (program, at_) ← getText data at_
  let (auxiliary, at_) ← getList getNat data at_
  let (mappings, at_) ← getList getMapping data at_
  .ok ({ group, descriptors, cwd, umask, breakStart, breakEnd, command, environment, program, auxiliary, mappings }, at_)

def putPiece (out : ByteArray) (piece : Nat × ByteArray) : ByteArray := putBytes (putNat out piece.1) piece.2

def getPiece : Decoder (Nat × ByteArray) := fun data at_ => do
  let (start, at_) ← getNat data at_
  let (bytes, at_) ← getBytes data at_
  .ok ((start, bytes), at_)

/-- Bytes as their size and what of them isn't zeros, which is all that memory that is shared and hardly used has, or as they are when
they are too many for `Jit.fill`. -/
def putSparse (out data : ByteArray) : ByteArray :=
  if data.size < Bap.Jit.fillLimit then putList putPiece (putNat (putNat out 1) data.size) (Bap.Jit.pieces data)
  else putBytes (putNat out 0) data

def getSparse : Decoder ByteArray := fun data at_ => do
  let (tag, at_) ← getNat data at_
  match tag with
  | 0 => getBytes data at_
  | 1 =>
    let (size, at_) ← getNat data at_
    if size ≥ Bap.Jit.fillLimit then .error "a Linux checkpoint with bytes too many to be" else
    let (pieces, at_) ← getList getPiece data at_
    .ok (Bap.Jit.fill size pieces, at_)
  | _ => .error "a Linux checkpoint with bytes of an unknown kind"

def putInode (out : ByteArray) (inode : InodeImage) : ByteArray :=
  putSparse (putNat (putNat (putNat out inode.number) inode.mode) inode.kind) inode.data

def getInode : Decoder InodeImage := fun data at_ => do
  let (number, at_) ← getNat data at_
  let (mode, at_) ← getNat data at_
  let (kind, at_) ← getNat data at_
  let (bytes, at_) ← getSparse data at_
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
