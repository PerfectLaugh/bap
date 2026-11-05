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
  /-- Its process group, session, terminal, credentials, limits and nice value, and whether it ended: see `identityBytes`. -/
  identity : ByteArray := ByteArray.empty
  deriving DecidableEq

/-- An inode, with what is in it as a tag and bytes: a link has its target in them. -/
structure InodeImage where
  number : Nat
  mode : Nat
  kind : Nat
  data : ByteArray
  /-- Its times, owner, extended attributes and seals: see `metaBytes`. -/
  details : ByteArray := ByteArray.empty
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
  /-- What is mounted: see `mountsBytes`. -/
  mounts : ByteArray := ByteArray.empty
  /-- What SysV IPC has: see `ipcBytes`. -/
  ipc : ByteArray := ByteArray.empty
  /-- How many bytes `getrandom` has given. -/
  randomGiven : Nat := 0
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
  Wire.putOption Wire.putText (Wire.putNat (Wire.putNat out socket.owner) socket.family) socket.remote

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
  -- What a socket of the Unix domain had before there were others.
  let (family, remote, at_) ← if at_ == data.size then pure (1, none, at_) else do
    let (family, at_) ← Wire.getNat data at_
    let (remote, at_) ← Wire.getOption Wire.getText data at_
    pure (family, remote, at_)
  Wire.expectEnd data at_
  pure { type, name, peer, listening, pending, waiting, incoming := incoming.toArray, readShut, writeShut, owner, family, remote }

/-- Of a process, its process group, session, terminal, credentials, limits and nice value, and whether it ended, as bytes. -/
def identityBytes (process : Process) : ByteArray :=
  let out := Wire.putOption Wire.putNat (Wire.putNat (Wire.putNat ByteArray.empty process.pgid) process.sid) process.terminal
  let ids := process.credentials
  let out := Wire.putList Wire.putNat (Wire.putList Wire.putNat out
    [ids.uid, ids.euid, ids.suid, ids.fsuid, ids.gid, ids.egid, ids.sgid, ids.fsgid]) ids.groups
  let out := Wire.putList (fun out (resource, soft, hard) => Wire.putNat (Wire.putNat (Wire.putNat out resource) soft) hard) out
    process.limits
  Wire.putNat (Wire.putText (Wire.putFlag (Wire.putNat out process.nice) process.ended) process.root) process.barriers

/-- What `identityBytes` made, on a process that has the rest; nothing at all is what a process starts with. -/
def withIdentity (process : Process) (data : ByteArray) : Except String Process := do
  if data.isEmpty then return process
  let (pgid, at_) ← Wire.getNat data 0
  let (sid, at_) ← Wire.getNat data at_
  let (terminal, at_) ← Wire.getOption Wire.getNat data at_
  let (ids, at_) ← Wire.getList Wire.getNat data at_
  let (groups, at_) ← Wire.getList Wire.getNat data at_
  let (limits, at_) ← Wire.getList (fun data at_ => do
    let (resource, at_) ← Wire.getNat data at_
    let (soft, at_) ← Wire.getNat data at_
    let (hard, at_) ← Wire.getNat data at_
    .ok ((resource, soft, hard), at_)) data at_
  let (nice, at_) ← Wire.getNat data at_
  let (ended, at_) ← Wire.getFlag data at_
  let (root, at_) ← Wire.getText data at_
  let (barriers, at_) ← Wire.getNat data at_
  Wire.expectEnd data at_
  let id (index : Nat) : Nat := ids.getD index 0
  pure { process with pgid, sid, terminal, limits, nice, ended, root, barriers
                      credentials := { uid := id 0, euid := id 1, suid := id 2, fsuid := id 3, gid := id 4, egid := id 5, sgid := id 6
                                       fsgid := id 7, groups } }

/-- Of an inode, its times, owner, extended attributes and seals, as bytes. -/
def metaBytes (details : Meta) : ByteArray :=
  let out := Wire.putList Wire.putNat ByteArray.empty [details.accessed, details.modified, details.changed, details.uid, details.gid, details.seals]
  let out := Wire.putList (fun out (name, value) => Wire.putBytes (Wire.putText out name) value) out details.attributes
  Wire.putList (Wire.putList Wire.putNat) out (details.locks.map fun lock =>
    let (kind, owner) := match lock.owner with
      | .process group => (0, group)
      | .openFile id => (1, id)
      | .flock id => (2, id)
    [kind, owner, lock.start, lock.stop, if lock.exclusive then 1 else 0])

/-- What `metaBytes` made; nothing at all is what an inode starts with. -/
def metaOfBytes (data : ByteArray) : Except String Meta := do
  if data.isEmpty then return {}
  let (numbers, at_) ← Wire.getList Wire.getNat data 0
  let (attributes, at_) ← Wire.getList (fun data at_ => do
    let (name, at_) ← Wire.getText data at_
    let (value, at_) ← Wire.getBytes data at_
    .ok ((name, value), at_)) data at_
  let (locks, at_) ← Wire.getList (Wire.getList Wire.getNat) data at_
  Wire.expectEnd data at_
  let locks ← locks.mapM fun fields => do
    let field (index : Nat) : Nat := fields.getD index 0
    let owner ← match field 0 with
      | 0 => pure (LockOwner.process (field 1))
      | 1 => pure (.openFile (field 1))
      | 2 => pure (.flock (field 1))
      | other => throw s!"no lock is of kind {other}"
    pure { owner, start := field 2, stop := field 3, exclusive := field 4 == 1 : FileLock }
  let number (index : Nat) : Nat := numbers.getD index 0
  pure { accessed := number 0, modified := number 1, changed := number 2, uid := number 3, gid := number 4, seals := number 5
         attributes, locks }

/-- What is mounted, as bytes. -/
def mountsBytes (mounts : List Mount) : ByteArray :=
  Wire.putList (fun out mount =>
    Wire.putNat (Wire.putText (Wire.putText (Wire.putText (Wire.putText out mount.target) mount.source) mount.fstype) mount.device) mount.flags)
    ByteArray.empty mounts

/-- What `mountsBytes` made. -/
def mountsOfBytes (data : ByteArray) : Except String (List Mount) := do
  if data.isEmpty then return []
  let (mounts, at_) ← Wire.getList (fun data at_ => do
    let (target, at_) ← Wire.getText data at_
    let (source, at_) ← Wire.getText data at_
    let (fstype, at_) ← Wire.getText data at_
    let (device, at_) ← Wire.getText data at_
    let (flags, at_) ← Wire.getNat data at_
    .ok ({ target, source, fstype, device, flags }, at_)) data 0
  Wire.expectEnd data at_
  pure mounts

private def putPerm (out : ByteArray) (perm : IpcPerm) : ByteArray :=
  Wire.putList Wire.putNat out [perm.key, perm.uid, perm.gid, perm.cuid, perm.cgid, perm.mode]

private def getPerm : Wire.Decoder IpcPerm := fun data at_ => do
  let (fields, at_) ← Wire.getList Wire.getNat data at_
  let field (index : Nat) : Nat := fields.getD index 0
  .ok ({ key := field 0, uid := field 1, gid := field 2, cuid := field 3, cgid := field 4, mode := field 5 }, at_)

/-- What SysV IPC has, as bytes. -/
def ipcBytes (ipc : Ipc) : ByteArray :=
  let out := Wire.putList (fun out (segment : Segment) =>
    Wire.putFlag (Wire.putList Wire.putNat (putPerm out segment.perm) [segment.id, segment.inode, segment.size, segment.cpid,
      segment.lpid, segment.atime, segment.dtime, segment.ctime]) segment.removed) ByteArray.empty ipc.segments
  let out := Wire.putList (fun out (set : SemaphoreSet) =>
    Wire.putList Wire.putNat (Wire.putList Wire.putNat (Wire.putList Wire.putNat (putPerm out set.perm) [set.id, set.otime, set.ctime])
      set.values) set.pids) out ipc.sets
  let out := Wire.putList (fun out (queue : MessageQueue) =>
    Wire.putList (fun out (type, text) => Wire.putBytes (Wire.putNat out type) text)
      (Wire.putList Wire.putNat (putPerm out queue.perm) [queue.id, queue.qbytes, queue.stime, queue.rtime, queue.ctime, queue.lspid,
        queue.lrpid]) queue.messages) out ipc.queues
  let out := Wire.putList Wire.putNat out [ipc.made.1, ipc.made.2.1, ipc.made.2.2]
  Wire.putList (fun out (group, set, number, change) =>
    Wire.putFlag (Wire.putList Wire.putNat out [group, set, number, change.natAbs]) (change < 0)) out ipc.undo

/-- What `ipcBytes` made. -/
def ipcOfBytes (data : ByteArray) : Except String Ipc := do
  if data.isEmpty then return {}
  let numbers : Wire.Decoder (List Nat) := Wire.getList Wire.getNat
  let (segments, at_) ← Wire.getList (fun data at_ => do
    let (perm, at_) ← getPerm data at_
    let (fields, at_) ← numbers data at_
    let (removed, at_) ← Wire.getFlag data at_
    let field (index : Nat) : Nat := fields.getD index 0
    .ok ({ perm, id := field 0, inode := field 1, size := field 2, cpid := field 3, lpid := field 4, atime := field 5, dtime := field 6
           ctime := field 7, removed : Segment }, at_)) data 0
  let (sets, at_) ← Wire.getList (fun data at_ => do
    let (perm, at_) ← getPerm data at_
    let (fields, at_) ← numbers data at_
    let (values, at_) ← numbers data at_
    let (pids, at_) ← numbers data at_
    .ok ({ perm, id := fields.getD 0 0, otime := fields.getD 1 0, ctime := fields.getD 2 0, values, pids : SemaphoreSet }, at_)) data at_
  let (queues, at_) ← Wire.getList (fun data at_ => do
    let (perm, at_) ← getPerm data at_
    let (fields, at_) ← numbers data at_
    let (messages, at_) ← Wire.getList (fun data at_ => do
      let (type, at_) ← Wire.getNat data at_
      let (text, at_) ← Wire.getBytes data at_
      .ok ((type, text), at_)) data at_
    let field (index : Nat) : Nat := fields.getD index 0
    .ok ({ perm, id := field 0, qbytes := field 1, stime := field 2, rtime := field 3, ctime := field 4, lspid := field 5, lrpid := field 6
           messages : MessageQueue }, at_)) data at_
  let (made, at_) ← numbers data at_
  let (undo, at_) ← Wire.getList (fun data at_ => do
    let (fields, at_) ← numbers data at_
    let (negative, at_) ← Wire.getFlag data at_
    let change : Int := if negative then -(fields.getD 3 0 : Int) else fields.getD 3 0
    .ok ((fields.getD 0 0, fields.getD 1 0, fields.getD 2 0, change), at_)) data at_
  Wire.expectEnd data at_
  pure { segments, sets, queues, made := (made.getD 0 0, made.getD 1 0, made.getD 2 0), undo }

/-- A terminal, as bytes. -/
def terminalBytes (terminal : Terminal) : ByteArray :=
  let out := Wire.putList Wire.putNat ByteArray.empty
    [terminal.index, terminal.iflag, terminal.oflag, terminal.cflag, terminal.lflag, terminal.rows, terminal.cols, terminal.ends,
     terminal.foreground, terminal.session]
  let out := Wire.putList Wire.putNat out terminal.cc
  let out := Wire.putBytes (Wire.putList Wire.putBytes out terminal.input) terminal.line
  Wire.putFlag (Wire.putFlag (Wire.putBytes out terminal.output) terminal.locked) terminal.opened

/-- What `terminalBytes` made. -/
def terminalOfBytes (data : ByteArray) : Except String Terminal := do
  let (numbers, at_) ← Wire.getList Wire.getNat data 0
  let (cc, at_) ← Wire.getList Wire.getNat data at_
  let (input, at_) ← Wire.getList Wire.getBytes data at_
  let (line, at_) ← Wire.getBytes data at_
  let (output, at_) ← Wire.getBytes data at_
  let (locked, at_) ← Wire.getFlag data at_
  let (opened, at_) ← Wire.getFlag data at_
  Wire.expectEnd data at_
  let number (index : Nat) : Nat := numbers.getD index 0
  pure { index := number 0, iflag := number 1, oflag := number 2, cflag := number 3, lflag := number 4, rows := number 5
         cols := number 6, ends := number 7, foreground := number 8, session := number 9, cc, input, line, output, locked, opened }

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
      | .eventfd count semaphore => (7, Wire.putFlag (Wire.putNat ByteArray.empty count) semaphore)
      | .timerfd expiry interval => (8, Wire.putNat (Wire.putOption Wire.putNat ByteArray.empty expiry) interval)
      | .signalfd mask => (9, Wire.putNat ByteArray.empty mask)
      | .epoll items => (10, Wire.putList (fun out (item : EpollItem) =>
          Wire.putFlag (Wire.putNat (Wire.putNat (Wire.putNat (Wire.putNat out item.fd) item.file) item.events) item.data) item.told)
          ByteArray.empty items)
      | .ptyMaster terminal => (11, terminalBytes terminal)
      | .ptySlave master => (12, Wire.putNat ByteArray.empty master)
      | .device kind => (13, Wire.putNat ByteArray.empty kind)
      | .inotify watches notices next cookies =>
        let out := Wire.putList (Wire.putList Wire.putNat) ByteArray.empty (watches.map fun watch => [watch.wd, watch.inode, watch.mask])
        let out := Wire.putList (fun out (notice : Notice) =>
          Wire.putText (Wire.putList Wire.putNat out [notice.wd, notice.mask, notice.cookie]) notice.name) out notices.toList
        (14, Wire.putNat (Wire.putNat out next) cookies)
      | .mqueue messages capacity size notify =>
        let out := Wire.putList (fun out (priority, text) => Wire.putBytes (Wire.putNat out priority) text) ByteArray.empty messages
        let out := Wire.putList Wire.putNat (Wire.putNat (Wire.putNat out capacity) size)
          (match notify with | some (group, how, signal, value) => [group, how, signal, value] | none => [])
        (15, out)
    { number, mode := inode.mode, kind, data, details := metaBytes inode.details }
  nextInode := kernel.nextInode
  openFiles := (sorted kernel.openFiles.toList).map fun (id, file) => (id, file.inode, file.offset, file.flags)
  nextOpenFile := kernel.nextOpenFile
  processes := (sorted kernel.processes.toList).map fun (group, process) =>
    { group, cwd := process.cwd, umask := process.umask, breakStart := process.breakStart, breakEnd := process.breakEnd
      command := process.command, environment := process.environment, program := process.program
      auxiliary := process.auxiliary, mappings := process.mappings
      descriptors := (sorted process.descriptors.toList).map fun (fd, entry) => (fd, entry.openFile, entry.closeOnExec)
      identity := identityBytes process }
  output := kernel.output
  clock := kernel.clock
  cycles := kernel.cycles
  mounts := mountsBytes kernel.mounts
  ipc := ipcBytes kernel.ipc
  randomGiven := kernel.randomGiven

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
      | 7 =>
        let (count, at_) ← Wire.getNat entry.data 0
        let (semaphore, _) ← Wire.getFlag entry.data at_
        pure (Content.eventfd count semaphore)
      | 8 =>
        let (expiry, at_) ← Wire.getOption Wire.getNat entry.data 0
        let (interval, _) ← Wire.getNat entry.data at_
        pure (Content.timerfd expiry interval)
      | 9 => pure (Content.signalfd (← Wire.getNat entry.data 0).1)
      | 10 =>
        let (items, _) ← Wire.getList (fun data at_ => do
          let (fd, at_) ← Wire.getNat data at_
          let (file, at_) ← Wire.getNat data at_
          let (events, at_) ← Wire.getNat data at_
          let (value, at_) ← Wire.getNat data at_
          let (told, at_) ← Wire.getFlag data at_
          .ok ({ fd, file, events, data := value, told }, at_)) entry.data 0
        pure (Content.epoll items)
      | 11 => pure (Content.ptyMaster (← terminalOfBytes entry.data))
      | 12 => pure (Content.ptySlave (← Wire.getNat entry.data 0).1)
      | 13 => pure (Content.device (← Wire.getNat entry.data 0).1)
      | 14 =>
        let (watches, at_) ← Wire.getList (Wire.getList Wire.getNat) entry.data 0
        let (notices, at_) ← Wire.getList (fun data at_ => do
          let (numbers, at_) ← Wire.getList Wire.getNat data at_
          let (name, at_) ← Wire.getText data at_
          .ok ({ wd := numbers.getD 0 0, mask := numbers.getD 1 0, cookie := numbers.getD 2 0, name }, at_)) entry.data at_
        let (next, at_) ← Wire.getNat entry.data at_
        let (cookies, _) ← Wire.getNat entry.data at_
        pure (Content.inotify (watches.map fun fields => { wd := fields.getD 0 0, inode := fields.getD 1 0, mask := fields.getD 2 0 })
          notices.toArray next cookies)
      | 15 =>
        let (messages, at_) ← Wire.getList (fun data at_ => do
          let (priority, at_) ← Wire.getNat data at_
          let (text, at_) ← Wire.getBytes data at_
          .ok ((priority, text), at_)) entry.data 0
        let (capacity, at_) ← Wire.getNat entry.data at_
        let (size, at_) ← Wire.getNat entry.data at_
        let (notify, _) ← Wire.getList Wire.getNat entry.data at_
        pure (Content.mqueue messages capacity size (match notify with
          | [group, how, signal, value] => some (group, how, signal, value)
          | _ => none))
      | kind => .error s!"a Linux checkpoint with an inode of kind {kind}"
    pure (inodes.insert entry.number { number := entry.number, content, mode := entry.mode, details := ← metaOfBytes entry.details })
  pure {
    paths := image.paths.foldl (init := {}) fun paths entry => paths.insert entry.1 entry.2
    inodes
    nextInode := image.nextInode
    openFiles := image.openFiles.foldl (init := {}) fun files (id, inode, offset, flags) => files.insert id { inode, offset, flags }
    nextOpenFile := image.nextOpenFile
    processes := ← image.processes.foldlM (init := {}) fun processes process => do
      let made : Process :=
        { cwd := process.cwd, umask := process.umask, breakStart := process.breakStart, breakEnd := process.breakEnd
          command := process.command, environment := process.environment, program := process.program
          auxiliary := process.auxiliary, mappings := process.mappings
          descriptors := process.descriptors.foldl (init := {}) fun descriptors (fd, openFile, closeOnExec) =>
            descriptors.insert fd { openFile, closeOnExec } }
      pure (processes.insert process.group (← withIdentity made process.identity))
    output := image.output
    clock := image.clock
    cycles := image.cycles
    mounts := ← mountsOfBytes image.mounts
    ipc := ← ipcOfBytes image.ipc
    randomGiven := image.randomGiven }

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
  let out := putList putMapping out process.mappings
  putBytes out process.identity

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
  let (identity, at_) ← getBytes data at_
  .ok ({ group, descriptors, cwd, umask, breakStart, breakEnd, command, environment, program, auxiliary, mappings, identity }, at_)

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
  putBytes (putSparse (putNat (putNat (putNat out inode.number) inode.mode) inode.kind) inode.data) inode.details

def getInode : Decoder InodeImage := fun data at_ => do
  let (number, at_) ← getNat data at_
  let (mode, at_) ← getNat data at_
  let (kind, at_) ← getNat data at_
  let (bytes, at_) ← getSparse data at_
  let (details, at_) ← getBytes data at_
  .ok ({ number, mode, kind, data := bytes, details }, at_)

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
  let out := putBytes (putBytes (putNat (putNat out image.clock) image.cycles) image.mounts) image.ipc
  putNat out image.randomGiven

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
  let (mounts, at_) ← getBytes data at_
  let (ipc, at_) ← getBytes data at_
  let (randomGiven, at_) ← getNat data at_
  .ok ({ paths, inodes, nextInode, openFiles, nextOpenFile, processes, output, clock, cycles, mounts, ipc, randomGiven }, at_)

end Image

end Bap.Linux
