import Std.Data.HashMap
import Bap.Core.Zeros

/-! # A virtual Linux kernel

What a program sees of Linux besides its memory and its tasks: files, directories, descriptors, the working directory, the
program break and a clock. This is pure and it is all there is: nothing here touches the machine that this runs on, so a run
is the same wherever and whenever it happens, and a program can do no harm. A file of the host is in here only if somebody put
it in before the run.

Everyone is root, and modes are kept but not enforced. Times come from a clock that ticks when it is read. -/

namespace Bap.Linux

namespace Errno
def eperm : Nat := 1
def eacces : Nat := 13
def enoent : Nat := 2
def eio : Nat := 5
def ebadf : Nat := 9
def enomem : Nat := 12
def efault : Nat := 14
def eexist : Nat := 17
def enotdir : Nat := 20
def eisdir : Nat := 21
def einval : Nat := 22
def emfile : Nat := 24
def enotty : Nat := 25
def espipe : Nat := 29
def erange : Nat := 34
def enosys : Nat := 38
def enotempty : Nat := 39
def eloop : Nat := 40
end Errno

inductive Content where
  | file (data : ByteArray)
  | directory
  | symlink (target : String)
  /-- What reads get from it, in order, and writes go to the output of the kernel. It can't seek. -/
  | console (input : ByteArray)
  /-- What a generator of this name makes when it is opened, as the files of `/proc` are: see `addGenerated`. -/
  | generated (name : String)

structure Inode where
  number : Nat
  content : Content
  mode : Nat

/-- What `open` makes: `dup` and `fork` share it, and with it the offset. -/
structure OpenFile where
  inode : Nat
  offset : Nat := 0
  flags : Nat

structure Descriptor where
  openFile : Nat
  closeOnExec : Bool := false

/-- What belongs to a process. -/
structure Process where
  descriptors : Std.HashMap Nat Descriptor := {}
  cwd : String := "/"
  umask : Nat := 0o022
  /-- Where the heap starts and where it ends now. -/
  breakStart : Nat := 0
  breakEnd : Nat := 0
  /-- What it was started with, as `/proc` says. A child has what its parent has. -/
  command : List String := []
  environment : List String := []
  program : String := ""

/-- What a mapping of a process is: where, how much, and what it may do. -/
structure MappedRange where
  start : Nat
  size : Nat
  readable : Bool
  writable : Bool
  executable : Bool
  deriving DecidableEq, Repr

/-- What a generator of a file sees: the process that it is about, and the machine. It is plain data, which comes from the kernel
and from the emulator when the file is opened. -/
structure ProcessView where
  pid : Nat
  parent : Nat
  /-- The tasks of the process. -/
  threads : List Nat := []
  command : List String := []
  environment : List String := []
  program : String := ""
  cwd : String := "/"
  ranges : List MappedRange := []
  breakStart : Nat := 0
  breakEnd : Nat := 0
  stackStart : Nat := 0
  /-- How many bits it has, and what `uname` calls it. -/
  bits : Nat := 64
  machine : String := ""
  /-- Nanoseconds since the epoch, and since the kernel started. -/
  clock : Nat := 0
  uptime : Nat := 0
  /-- The processes that there are. -/
  processes : List Nat := []

/-- What makes the bytes of a generated file. -/
abbrev Generator := ProcessView → ByteArray

structure Kernel where
  /-- From an absolute path without `.`, `..` or a trailing slash to its inode. -/
  paths : Std.HashMap String Nat := {}
  inodes : Std.HashMap Nat Inode := {}
  nextInode : Nat := 2
  openFiles : Std.HashMap Nat OpenFile := {}
  nextOpenFile : Nat := 0
  processes : Std.HashMap Nat Process := {}
  /-- What was written to the console and hasn't been taken yet. -/
  output : ByteArray := ByteArray.empty
  /-- Nanoseconds since the epoch. -/
  clock : Nat := 1700000000 * 1000000000
  /-- What the time stamp counter of the processor reads, which is kept here so that it is part of what a checkpoint holds. -/
  cycles : Nat := 1000000
  /-- What makes the generated files that aren't those of `/proc`, by name. A function can't go in a checkpoint: only the names do,
  and these are given again to go on from it. -/
  generators : Std.HashMap String Generator := {}

/-- A result, or the number of an error. -/
abbrev Result (α : Type) := Except Nat α

namespace Path

/-- The parts of a path, from `base` if it is relative, with `.` and `..` gone. `..` of the root is the root. -/
def parts (base path : String) : List String :=
  let absolute := if path.startsWith "/" then path else base ++ "/" ++ path
  let kept := (absolute.splitOn "/").foldl (init := ([] : List String)) fun kept part =>
    if part == "" || part == "." then kept
    else if part == ".." then kept.drop 1
    else part :: kept
  kept.reverse

def ofParts (parts : List String) : String := "/" ++ "/".intercalate parts

/-- Without its last part. -/
def parent (path : String) : String := ofParts (parts "/" path).dropLast

def name (path : String) : String := (parts "/" path).getLast?.getD "/"

end Path

namespace Kernel

/-- A kernel with an empty root directory. -/
def empty : Kernel :=
  { paths := ({} : Std.HashMap String Nat).insert "/" 1
    inodes := ({} : Std.HashMap Nat Inode).insert 1 { number := 1, content := .directory, mode := 0o40755 } }

private def addInode (kernel : Kernel) (path : String) (content : Content) (mode : Nat) : Kernel × Nat :=
  let number := kernel.nextInode
  ({ kernel with
      paths := kernel.paths.insert path number
      inodes := kernel.inodes.insert number { number, content, mode }
      nextInode := number + 1 }, number)

/-- Follows a path, and its last part if `follow`, up to 40 links as Linux does. Each part before the last must be a directory,
and the last doesn't have to be there: the result says whether it is. -/
def resolve (kernel : Kernel) (base path : String) (follow : Bool := true) (links : Nat := 40) :
    Result (String × Option Nat) :=
  let rec walk (done : List String) (todo : List String) : Nat → Nat → Result (String × Option Nat)
    | 0, _ => .error Errno.eloop
    | fuel + 1, links =>
      match todo with
      | [] =>
        let path := Path.ofParts done.reverse
        .ok (path, kernel.paths.get? path)
      | part :: rest =>
        let path := Path.ofParts (part :: done).reverse
        match kernel.paths.get? path with
        | none => if rest.isEmpty then .ok (path, none) else .error Errno.enoent
        | some number =>
          match kernel.inodes.get? number with
          | none => .error Errno.eio
          | some inode =>
            match inode.content with
            | .symlink target =>
              if rest.isEmpty && !follow then .ok (path, some number)
              else if links == 0 then .error Errno.eloop
              else
                let from_ := if target.startsWith "/" then [] else done.reverse
                walk [] (Path.parts (Path.ofParts from_) target ++ rest) fuel (links - 1)
            | .directory => walk (part :: done) rest fuel links
            | _ => if rest.isEmpty then .ok (path, some number) else .error Errno.enotdir
  walk [] (Path.parts base path) (links * 256 + 4096) links

/-- Makes the directories of a path. For setting up, and it replaces nothing. -/
def addDirectories (kernel : Kernel) (path : String) : Kernel :=
  let parts := Path.parts "/" path
  (List.range parts.length).foldl (init := kernel) fun kernel count =>
    let prefix_ := Path.ofParts (parts.take (count + 1))
    if kernel.paths.contains prefix_ then kernel else (addInode kernel prefix_ .directory 0o40755).1

/-- Puts a file in, with the directories it needs. For setting up, before a run. -/
def addFile (kernel : Kernel) (path : String) (data : ByteArray) (mode : Nat := 0o100755) : Kernel :=
  let normal := Path.ofParts (Path.parts "/" path)
  let kernel := addDirectories kernel (Path.parent normal)
  match kernel.paths.get? normal with
  | some number =>
    { kernel with inodes := kernel.inodes.insert number { number, content := .file data, mode } }
  | none => (addInode kernel normal (.file data) mode).1

/-- Puts a file in whose bytes `generate` makes each time that it is opened, for what it sees of the process that opens it. What is
open has those bytes until it is closed, and stat says that it is empty, as for a file of `/proc`. For setting up, before a run. It
replaces what is there, so that this can say what a file of `/proc` has. -/
def addGenerated (kernel : Kernel) (path : String) (generate : Generator) (mode : Nat := 0o100444) : Kernel :=
  let normal := Path.ofParts (Path.parts "/" path)
  let kernel := addDirectories kernel (Path.parent normal)
  let kernel := { kernel with generators := kernel.generators.insert normal generate }
  match kernel.paths.get? normal with
  | some number =>
    { kernel with inodes := kernel.inodes.insert number { number, content := .generated normal, mode } }
  | none => (addInode kernel normal (.generated normal) mode).1

/-- A file that some generator of the kernel's own makes, by its name, if there is nothing there yet. -/
def addBuiltin (kernel : Kernel) (path name : String) (mode : Nat := 0o100444) : Kernel :=
  let normal := Path.ofParts (Path.parts "/" path)
  if kernel.paths.contains normal then kernel
  else
    let kernel := addDirectories kernel (Path.parent normal)
    (addInode kernel normal (.generated name) mode).1

/-- Forgets what is under a directory, which stays. -/
def removeUnder (kernel : Kernel) (directory : String) : Kernel :=
  let inside := directory ++ "/"
  let gone := kernel.paths.toList.filter fun entry => entry.1.startsWith inside
  gone.foldl (init := kernel) fun kernel entry =>
    { kernel with
      paths := kernel.paths.erase entry.1
      inodes := kernel.inodes.erase entry.2 }

/-- A link at a path, whatever was there. -/
def setSymlink (kernel : Kernel) (path target : String) : Kernel :=
  let normal := Path.ofParts (Path.parts "/" path)
  let kernel := addDirectories kernel (Path.parent normal)
  match kernel.paths.get? normal with
  | some number =>
    { kernel with inodes := kernel.inodes.insert number { number, content := .symlink target, mode := 0o120777 } }
  | none => (addInode kernel normal (.symlink target) 0o120777).1

/-- Puts a symbolic link in. For setting up, before a run. -/
def addSymlink (kernel : Kernel) (path target : String) : Kernel :=
  let normal := Path.ofParts (Path.parts "/" path)
  (addInode (addDirectories kernel (Path.parent normal)) normal (.symlink target) 0o120777).1

def process (kernel : Kernel) (group : Nat) : Process := kernel.processes.getD group {}

def setProcess (kernel : Kernel) (group : Nat) (process : Process) : Kernel :=
  { kernel with processes := kernel.processes.insert group process }

private def lowestFree (descriptors : Std.HashMap Nat Descriptor) (from_ : Nat) : Nat :=
  let rec go : Nat → Nat → Nat
    | 0, candidate => candidate
    | fuel + 1, candidate => if descriptors.contains candidate then go fuel (candidate + 1) else candidate
  go (descriptors.size + 1) from_

/-- A descriptor of an open file, the lowest free from `from_`. -/
def addDescriptor (kernel : Kernel) (group openFile : Nat) (closeOnExec : Bool := false) (from_ : Nat := 0) : Kernel × Nat :=
  let process := kernel.process group
  let fd := lowestFree process.descriptors from_
  (kernel.setProcess group { process with descriptors := process.descriptors.insert fd { openFile, closeOnExec } }, fd)

/-- A descriptor of bytes that are nowhere in the tree: what a generated file gives the one that opens it. -/
def openBytes (kernel : Kernel) (group : Nat) (data : ByteArray) (flags : Nat) (mode : Nat := 0o100444) : Kernel × Nat :=
  let number := kernel.nextInode
  let openFile := kernel.nextOpenFile
  let kernel := { kernel with
    inodes := kernel.inodes.insert number { number, content := .file data, mode }
    nextInode := number + 1
    openFiles := kernel.openFiles.insert openFile { inode := number, flags := flags &&& 3 }
    nextOpenFile := openFile + 1 }
  kernel.addDescriptor group openFile (flags &&& 0x80000 != 0)

/-- The three standard descriptors, on a console, for the first process. -/
def withConsole (kernel : Kernel) (group : Nat) (input : ByteArray := ByteArray.empty) : Kernel :=
  let number := kernel.nextInode
  let kernel := { kernel with
    inodes := kernel.inodes.insert number { number, content := .console input, mode := 0o20620 }
    nextInode := number + 1 }
  let openFile := kernel.nextOpenFile
  let kernel := { kernel with
    openFiles := kernel.openFiles.insert openFile { inode := number, flags := 2 }
    nextOpenFile := openFile + 1 }
  (List.range 3).foldl (init := kernel) fun kernel _ => (kernel.addDescriptor group openFile).1

/-- A child has copies of the descriptors, which share the open files with its parent, and the rest of its parent's state. -/
def fork (kernel : Kernel) (parent child : Nat) : Kernel :=
  kernel.setProcess child (kernel.process parent)

/-- A process is gone, and what only it had open with it. -/
def exitProcess (kernel : Kernel) (group : Nat) : Kernel :=
  { kernel with processes := kernel.processes.erase group }

def openFileOf (kernel : Kernel) (group fd : Nat) : Result (Nat × OpenFile) :=
  match (kernel.process group).descriptors.get? fd with
  | none => .error Errno.ebadf
  | some descriptor =>
    match kernel.openFiles.get? descriptor.openFile with
    | none => .error Errno.ebadf
    | some file => .ok (descriptor.openFile, file)

def inodeOf (kernel : Kernel) (number : Nat) : Result Inode :=
  match kernel.inodes.get? number with
  | some inode => .ok inode
  | none => .error Errno.eio

/-- The bytes of a file from `offset`, up to `count`. -/
def readAt (data : ByteArray) (offset count : Nat) : ByteArray :=
  data.extract offset (offset + count)

/-- A file with `bytes` at `offset`, and zeros in what it skips. -/
def writeAt (data : ByteArray) (offset : Nat) (bytes : ByteArray) : ByteArray :=
  let filled := if data.size < offset then data ++ Bap.zeroBytes (offset - data.size) else data
  filled.extract 0 offset ++ bytes ++ filled.extract (offset + bytes.size) filled.size

def oCreat : Nat := 0x40
def oExcl : Nat := 0x80
def oTrunc : Nat := 0x200
def oAppend : Nat := 0x400
def oDirectory : Nat := 0x10000
def oNofollow : Nat := 0x20000
def oCloexec : Nat := 0x80000

private def has (flags flag : Nat) : Bool := flags &&& flag != 0

private def writable (flags : Nat) : Bool := flags &&& 3 != 0

private def parentIsDirectory (kernel : Kernel) (path : String) : Bool :=
  match kernel.paths.get? (Path.parent path) with
  | some number =>
    match kernel.inodes.get? number with
    | some { content := .directory, .. } => true
    | _ => false
  | none => false

/-- `open`. -/
def openPath (kernel : Kernel) (group : Nat) (base path : String) (flags mode : Nat) : Result (Kernel × Nat) := do
  if path == "" then .error Errno.enoent
  let (normal, found) ← kernel.resolve base path (follow := !has flags oNofollow)
  let (kernel, number) ← match found with
    | some number =>
      if has flags oCreat && has flags oExcl then .error Errno.eexist
      .ok (kernel, number)
    | none =>
      if !has flags oCreat then .error Errno.enoent
      if !parentIsDirectory kernel normal then .error Errno.enoent
      let umask := (kernel.process group).umask
      .ok (addInode kernel normal (.file ByteArray.empty) (0o100000 ||| (mode &&& 0o7777 &&& (0o7777 - umask))))
  let inode ← inodeOf kernel number
  let kernel ← match inode.content with
    | .directory =>
      if writable flags then .error Errno.eisdir
      .ok kernel
    | .symlink _ => .error Errno.eloop
    -- `Machine` opens these, with what they see, which this doesn't know.
    | .generated _ => .error Errno.eacces
    | .file _ =>
      if has flags oDirectory then .error Errno.enotdir
      if has flags oTrunc && writable flags then
        .ok { kernel with inodes := kernel.inodes.insert number { inode with content := .file ByteArray.empty } }
      else .ok kernel
    | .console _ =>
      if has flags oDirectory then .error Errno.enotdir
      .ok kernel
  let openFile := kernel.nextOpenFile
  let kernel := { kernel with
    openFiles := kernel.openFiles.insert openFile { inode := number, flags }
    nextOpenFile := openFile + 1 }
  .ok (kernel.addDescriptor group openFile (has flags oCloexec))

/-- `read`, at the offset of the file, which moves. -/
def read (kernel : Kernel) (group fd count : Nat) : Result (Kernel × ByteArray) := do
  let (id, file) ← openFileOf kernel group fd
  if file.flags &&& 3 == 1 then .error Errno.ebadf
  let inode ← inodeOf kernel file.inode
  let data ← match inode.content with
    | .file data | .console data => .ok data
    | .directory => .error Errno.eisdir
    | .symlink _ | .generated _ => .error Errno.einval
  let bytes := readAt data file.offset count
  .ok ({ kernel with openFiles := kernel.openFiles.insert id { file with offset := file.offset + bytes.size } }, bytes)

/-- `pread`, which leaves the offset. -/
def readFrom (kernel : Kernel) (group fd count offset : Nat) : Result ByteArray := do
  let (_, file) ← openFileOf kernel group fd
  if file.flags &&& 3 == 1 then .error Errno.ebadf
  let inode ← inodeOf kernel file.inode
  match inode.content with
  | .file data => .ok (readAt data offset count)
  | .console _ => .error Errno.espipe
  | .directory => .error Errno.eisdir
  | .symlink _ | .generated _ => .error Errno.einval

/-- `write`, at the offset of the file, or at its end if it was opened to append. -/
def write (kernel : Kernel) (group fd : Nat) (bytes : ByteArray) : Result (Kernel × Nat) := do
  let (id, file) ← openFileOf kernel group fd
  if !writable file.flags then .error Errno.ebadf
  let inode ← inodeOf kernel file.inode
  match inode.content with
  | .console _ => .ok ({ kernel with output := kernel.output ++ bytes }, bytes.size)
  | .file data =>
    let offset := if has file.flags oAppend then data.size else file.offset
    .ok ({ kernel with
      inodes := kernel.inodes.insert file.inode { inode with content := .file (writeAt data offset bytes) }
      openFiles := kernel.openFiles.insert id { file with offset := offset + bytes.size } }, bytes.size)
  | .directory => .error Errno.eisdir
  | .symlink _ | .generated _ => .error Errno.einval

/-- `pwrite`, which leaves the offset. -/
def writeTo (kernel : Kernel) (group fd : Nat) (bytes : ByteArray) (offset : Nat) : Result (Kernel × Nat) := do
  let (_, file) ← openFileOf kernel group fd
  if !writable file.flags then .error Errno.ebadf
  let inode ← inodeOf kernel file.inode
  match inode.content with
  | .file data =>
    .ok ({ kernel with inodes := kernel.inodes.insert file.inode { inode with content := .file (writeAt data offset bytes) } },
      bytes.size)
  | .console _ => .error Errno.espipe
  | .directory => .error Errno.eisdir
  | .symlink _ | .generated _ => .error Errno.einval

/-- `lseek`. A signed offset comes as `(negative, size)`. -/
def seek (kernel : Kernel) (group fd : Nat) (negative : Bool) (distance whence : Nat) : Result (Kernel × Nat) := do
  let (id, file) ← openFileOf kernel group fd
  let inode ← inodeOf kernel file.inode
  let size ← match inode.content with
    | .file data => .ok data.size
    | .directory => .ok 0
    | .console _ => .error Errno.espipe
    | .symlink _ | .generated _ => .error Errno.einval
  let start ← match whence with
    | 0 => .ok 0
    | 1 => .ok file.offset
    | 2 => .ok size
    | _ => .error Errno.einval
  if negative && distance > start then .error Errno.einval
  let offset := if negative then start - distance else start + distance
  .ok ({ kernel with openFiles := kernel.openFiles.insert id { file with offset } }, offset)

/-- `close`. -/
def close (kernel : Kernel) (group fd : Nat) : Result Kernel := do
  let process := kernel.process group
  if !process.descriptors.contains fd then .error Errno.ebadf
  .ok (kernel.setProcess group { process with descriptors := process.descriptors.erase fd })

/-- `dup`, and `fcntl` with `F_DUPFD`: the lowest free from `from_`, on the same open file. -/
def dup (kernel : Kernel) (group fd : Nat) (from_ : Nat := 0) (closeOnExec : Bool := false) : Result (Kernel × Nat) := do
  let process := kernel.process group
  match process.descriptors.get? fd with
  | none => .error Errno.ebadf
  | some descriptor => .ok (kernel.addDescriptor group descriptor.openFile closeOnExec from_)

/-- `dup2` and `dup3`: `target` is closed if it is open, and now the same open file as `fd`. -/
def dupTo (kernel : Kernel) (group fd target : Nat) (closeOnExec : Bool := false) : Result (Kernel × Nat) := do
  let process := kernel.process group
  match process.descriptors.get? fd with
  | none => .error Errno.ebadf
  | some descriptor =>
    .ok (kernel.setProcess group
      { process with descriptors := process.descriptors.insert target { openFile := descriptor.openFile, closeOnExec } }, target)

/-- `fcntl` with `F_GETFD`. -/
def getCloseOnExec (kernel : Kernel) (group fd : Nat) : Result Bool :=
  match (kernel.process group).descriptors.get? fd with
  | some descriptor => .ok descriptor.closeOnExec
  | none => .error Errno.ebadf

/-- `fcntl` with `F_SETFD`. -/
def setCloseOnExec (kernel : Kernel) (group fd : Nat) (value : Bool) : Result Kernel := do
  let process := kernel.process group
  match process.descriptors.get? fd with
  | none => .error Errno.ebadf
  | some descriptor =>
    .ok (kernel.setProcess group
      { process with descriptors := process.descriptors.insert fd { descriptor with closeOnExec := value } })

/-- `fcntl` with `F_GETFL`. -/
def getFlags (kernel : Kernel) (group fd : Nat) : Result Nat := do
  pure (← openFileOf kernel group fd).2.flags

/-- `fcntl` with `F_SETFL`, of which only `O_APPEND` and `O_NONBLOCK` can change. -/
def setFlags (kernel : Kernel) (group fd flags : Nat) : Result Kernel := do
  let (id, file) ← openFileOf kernel group fd
  let changing := 0x400 ||| 0x800
  let kept := file.flags - (file.flags &&& changing)
  .ok { kernel with openFiles := kernel.openFiles.insert id { file with flags := kept ||| (flags &&& changing) } }

/-- What `stat` says. -/
structure Stat where
  inode : Nat
  mode : Nat
  size : Nat
  links : Nat
  time : Nat
  deriving DecidableEq, Repr

private def statOf (kernel : Kernel) (inode : Inode) : Stat :=
  let (size, links) := match inode.content with
    | .file data => (data.size, 1)
    | .directory => (4096, 2)
    | .symlink target => (target.utf8ByteSize, 1)
    | .console _ | .generated _ => (0, 1)
  { inode := inode.number, mode := inode.mode, size, links, time := kernel.clock }

/-- `stat` and `lstat`. -/
def statPath (kernel : Kernel) (base path : String) (follow : Bool := true) : Result Stat := do
  if path == "" then .error Errno.enoent
  let (_, found) ← kernel.resolve base path follow
  match found with
  | none => .error Errno.enoent
  | some number => .ok (statOf kernel (← inodeOf kernel number))

/-- `fstat`. -/
def statDescriptor (kernel : Kernel) (group fd : Nat) : Result Stat := do
  let (_, file) ← openFileOf kernel group fd
  .ok (statOf kernel (← inodeOf kernel file.inode))

/-- The path of what is open, for a directory. -/
private def pathOfInode (kernel : Kernel) (number : Nat) : Option String :=
  (kernel.paths.toList.find? fun entry => entry.2 == number).map (·.1)

/-- The base that a path of the `*at` calls is relative to: the working directory for `AT_FDCWD`, or that directory. -/
def baseOf (kernel : Kernel) (group directory : Nat) (atCwd : Bool) : Result String := do
  if atCwd then .ok (kernel.process group).cwd
  else
    let (_, file) ← openFileOf kernel group directory
    match pathOfInode kernel file.inode, (← inodeOf kernel file.inode).content with
    | some path, .directory => .ok path
    | _, _ => .error Errno.enotdir

/-- What is in a directory, sorted, without `.` and `..`. -/
def children (kernel : Kernel) (path : String) : List (String × Nat) :=
  let inside := Path.parts "/" path
  let entries := kernel.paths.toList.filterMap fun entry =>
    let parts := Path.parts "/" entry.1
    if parts.length == inside.length + 1 && parts.take inside.length == inside then
      some ((parts.getLast?.getD ""), entry.2)
    else none
  (entries.toArray.qsort fun left right => left.1 < right.1).toList

/-- The entries of `getdents64` for a directory from where it has been read, each as number, type and name, with the open file
and that place: the kernel gives them in one order, as the offset of the open file counts them. -/
def directoryEntries (kernel : Kernel) (group fd : Nat) : Result (Nat × Nat × List (Nat × Nat × String)) := do
  let (id, file) ← openFileOf kernel group fd
  let inode ← inodeOf kernel file.inode
  match inode.content, pathOfInode kernel file.inode with
  | .directory, some path =>
    let typeOf (number : Nat) : Nat :=
      match kernel.inodes.get? number with
      | some { content := .directory, .. } => 4
      | some { content := .symlink _, .. } => 10
      | some { content := .file _, .. } => 8
      | some { content := .console _, .. } => 2
      | some { content := .generated _, .. } => 8
      | none => 0
    let parentNumber := (kernel.paths.get? (Path.parent path)).getD inode.number
    let all := [(inode.number, 4, "."), (parentNumber, 4, "..")] ++
      (children kernel path).map fun entry => (entry.2, typeOf entry.2, entry.1)
    .ok (id, file.offset, all.drop file.offset)
  | .directory, none => .error Errno.eio
  | _, _ => .error Errno.enotdir

/-- The directory has been read this far. -/
def advance (kernel : Kernel) (id count : Nat) : Kernel :=
  match kernel.openFiles.get? id with
  | some file => { kernel with openFiles := kernel.openFiles.insert id { file with offset := file.offset + count } }
  | none => kernel

/-- `mkdir`. -/
def mkdir (kernel : Kernel) (group : Nat) (base path : String) (mode : Nat) : Result Kernel := do
  let (normal, found) ← kernel.resolve base path (follow := false)
  if found.isSome then .error Errno.eexist
  if !parentIsDirectory kernel normal then .error Errno.enoent
  let umask := (kernel.process group).umask
  .ok (addInode kernel normal .directory (0o40000 ||| (mode &&& 0o7777 &&& (0o7777 - umask)))).1

/-- `unlink`, and `rmdir` with `directory`. What is open stays open: its inode is still there. -/
def remove (kernel : Kernel) (base path : String) (directory : Bool) : Result Kernel := do
  let (normal, found) ← kernel.resolve base path (follow := false)
  match found with
  | none => .error Errno.enoent
  | some number =>
    let inode ← inodeOf kernel number
    match inode.content, directory with
    | .directory, true =>
      if normal == "/" then .error Errno.eperm
      if !(children kernel normal).isEmpty then .error Errno.enotempty
    | .directory, false => .error Errno.eisdir
    | _, true => .error Errno.enotdir
    | _, false => pure ()
    .ok { kernel with paths := kernel.paths.erase normal }

/-- `rename`: what was at the target is replaced, and all under a directory moves with it. -/
def rename (kernel : Kernel) (base source target : String) : Result Kernel := do
  let (from_, found) ← kernel.resolve base source (follow := false)
  let some _ := found | .error Errno.enoent
  let (to_, existing) ← kernel.resolve base target (follow := false)
  if !parentIsDirectory kernel to_ then .error Errno.enoent
  if from_ == to_ then return kernel
  if (to_ ++ "/").startsWith (from_ ++ "/") then .error Errno.einval
  if let some number := existing then
    let inode ← inodeOf kernel number
    if let .directory := inode.content then
      if !(children kernel to_).isEmpty then .error Errno.enotempty
  let moved := kernel.paths.toList.foldl (init := kernel.paths.erase to_) fun paths entry =>
    if entry.1 == from_ then (paths.erase entry.1).insert to_ entry.2
    else if entry.1.startsWith (from_ ++ "/") then
      (paths.erase entry.1).insert (to_ ++ (entry.1.drop from_.length).toString) entry.2
    else paths
  .ok { kernel with paths := moved }

/-- `symlink`. -/
def symlink (kernel : Kernel) (base target path : String) : Result Kernel := do
  let (normal, found) ← kernel.resolve base path (follow := false)
  if found.isSome then .error Errno.eexist
  if !parentIsDirectory kernel normal then .error Errno.enoent
  .ok (addInode kernel normal (.symlink target) 0o120777).1

/-- `readlink`. -/
def readlink (kernel : Kernel) (base path : String) : Result String := do
  let (_, found) ← kernel.resolve base path (follow := false)
  match found with
  | none => .error Errno.enoent
  | some number =>
    match (← inodeOf kernel number).content with
    | .symlink target => .ok target
    | _ => .error Errno.einval

/-- `chdir`. -/
def chdir (kernel : Kernel) (group : Nat) (path : String) : Result Kernel := do
  let process := kernel.process group
  let (normal, found) ← kernel.resolve process.cwd path
  match found with
  | none => .error Errno.enoent
  | some number =>
    match (← inodeOf kernel number).content with
    | .directory => .ok (kernel.setProcess group { process with cwd := normal })
    | _ => .error Errno.enotdir

/-- `truncate` of a file at its inode: cut, or filled with zeros. -/
def truncateInode (kernel : Kernel) (number size : Nat) : Result Kernel := do
  let inode ← inodeOf kernel number
  match inode.content with
  | .file data =>
    let data := if size ≤ data.size then data.extract 0 size
      else data ++ Bap.zeroBytes (size - data.size)
    .ok { kernel with inodes := kernel.inodes.insert number { inode with content := .file data } }
  | .directory => .error Errno.eisdir
  | _ => .error Errno.einval

/-- `ftruncate`. -/
def truncateDescriptor (kernel : Kernel) (group fd size : Nat) : Result Kernel := do
  let (_, file) ← openFileOf kernel group fd
  if !writable file.flags then .error Errno.einval
  kernel.truncateInode file.inode size

/-- `truncate`. -/
def truncatePath (kernel : Kernel) (base path : String) (size : Nat) : Result Kernel := do
  match (← kernel.resolve base path).2 with
  | none => .error Errno.enoent
  | some number => kernel.truncateInode number size

/-- `chmod`. -/
def chmod (kernel : Kernel) (base path : String) (mode : Nat) : Result Kernel := do
  match (← kernel.resolve base path).2 with
  | none => .error Errno.enoent
  | some number =>
    let inode ← inodeOf kernel number
    let kept := inode.mode - (inode.mode &&& 0o7777)
    .ok { kernel with inodes := kernel.inodes.insert number { inode with mode := kept ||| (mode &&& 0o7777) } }

/-- The bytes that a file mapping of `fd` holds, whole pages at most, with zeros after the end of the file. -/
def mappedBytes (kernel : Kernel) (group fd offset size : Nat) : Result ByteArray := do
  let (_, file) ← openFileOf kernel group fd
  match (← inodeOf kernel file.inode).content with
  | .file data =>
    let bytes := readAt data offset size
    .ok (bytes ++ Bap.zeroBytes (size - bytes.size))
  | .directory => .error Errno.eisdir
  | _ => .error Errno.einval

/-- Now, and a tick: a program that waits for the time to change doesn't wait forever. -/
def tick (kernel : Kernel) : Kernel × Nat :=
  ({ kernel with clock := kernel.clock + 1000 }, kernel.clock)

/-- What was written to the console, which is then gone from here. -/
def takeOutput (kernel : Kernel) : Kernel × ByteArray :=
  ({ kernel with output := ByteArray.empty }, kernel.output)

end Kernel

/-! ### What the calls write to memory -/

namespace Abi

def bytesOf (size value : Nat) : ByteArray :=
  ByteArray.mk ((List.range size).map fun index => (value >>> (8 * index)).toUInt8).toArray

/-- A field of a structure, in the order of the guest. -/
def field (big : Bool) (size value : Nat) : ByteArray :=
  let bytes := bytesOf size value
  if big then ByteArray.mk bytes.data.reverse else bytes

/-- `struct stat` of x86-64 and 64-bit PowerPC. -/
def stat (value : Kernel.Stat) (big : Bool := false) : ByteArray :=
  let get := field big
  let seconds := value.time / 1000000000
  let nanos := value.time % 1000000000
  let time := get 8 seconds ++ get 8 nanos
  get 8 1 ++ get 8 value.inode ++ get 8 value.links ++ get 4 value.mode ++ get 4 0 ++ get 4 0 ++
    get 4 0 ++ get 8 0 ++ get 8 value.size ++ get 8 4096 ++ get 8 ((value.size + 511) / 512) ++
    time ++ time ++ time ++ bytesOf 24 0

/-- `struct stat` of `asm-generic/stat.h`, which has the order of the fields of 32-bit systems and is smaller. -/
def genericStat (value : Kernel.Stat) : ByteArray :=
  let seconds := value.time / 1000000000
  let nanos := value.time % 1000000000
  let time := bytesOf 8 seconds ++ bytesOf 8 nanos
  bytesOf 8 1 ++ bytesOf 8 value.inode ++ bytesOf 4 value.mode ++ bytesOf 4 value.links ++ bytesOf 4 0 ++ bytesOf 4 0 ++
    bytesOf 8 0 ++ bytesOf 8 0 ++ bytesOf 8 value.size ++ bytesOf 4 4096 ++ bytesOf 4 0 ++ bytesOf 8 ((value.size + 511) / 512) ++
    time ++ time ++ time ++ bytesOf 8 0

/-- `struct stat` of 64-bit MIPS, which holds its times in 32 bits. -/
def mips64Stat (value : Kernel.Stat) (big : Bool) : ByteArray :=
  let get := field big
  let time := get 4 (value.time / 1000000000) ++ get 4 (value.time % 1000000000)
  get 4 1 ++ bytesOf 12 0 ++ get 8 value.inode ++ get 4 value.mode ++ get 4 value.links ++ get 4 0 ++ get 4 0 ++ get 4 0 ++
    bytesOf 12 0 ++ get 8 value.size ++ time ++ time ++ time ++ get 4 4096 ++ bytesOf 4 0 ++ get 8 ((value.size + 511) / 512) ++
    bytesOf 56 0

/-- `struct statx`. -/
def statx (value : Kernel.Stat) (big : Bool := false) : ByteArray :=
  let get := field big
  let seconds := value.time / 1000000000
  let nanos := value.time % 1000000000
  let time := get 8 seconds ++ get 4 nanos ++ get 4 0
  -- STATX_BASIC_STATS
  get 4 0x7ff ++ get 4 4096 ++ get 8 0 ++ get 4 value.links ++ get 4 0 ++ get 4 0 ++
    get 2 value.mode ++ get 2 0 ++ get 8 value.inode ++ get 8 value.size ++
    get 8 ((value.size + 511) / 512) ++ get 8 0 ++ time ++ time ++ time ++ time ++ get 128 0

/-- One `struct linux_dirent64`, aligned to 8. -/
def dirent (number : Nat) (next : Nat) (kind : Nat) (name : String) (big : Bool := false) : ByteArray :=
  let text := name.toUTF8
  let size := (19 + text.size + 1 + 7) / 8 * 8
  field big 8 number ++ field big 8 next ++ field big 2 size ++ bytesOf 1 kind ++ text ++ bytesOf (size - 19 - text.size) 0

/-- As many entries as fit in `room`, and how many that is. -/
def dirents (entries : List (Nat × Nat × String)) (first room : Nat) (big : Bool := false) : ByteArray × Nat :=
  let rec go : List (Nat × Nat × String) → Nat → ByteArray → Nat → ByteArray × Nat
    | [], _, out, count => (out, count)
    | (number, kind, name) :: rest, index, out, count =>
      let entry := dirent number (index + 1) kind name big
      if out.size + entry.size > room then (out, count)
      else go rest (index + 1) (out ++ entry) (count + 1)
  go entries first ByteArray.empty 0

/-- `struct timespec`, or `struct timeval` with `scale` 1000, of fields of `size` bytes. -/
def time (now scale : Nat) (big : Bool := false) (size : Nat := 8) : ByteArray :=
  field big size (now / 1000000000) ++ field big size (now % 1000000000 / scale)

/-- `struct utsname`, of six fields of 65 bytes. -/
def utsname (nodename machine : String) : ByteArray :=
  let field (text : String) : ByteArray :=
    let bytes := text.toUTF8
    bytes ++ bytesOf (65 - bytes.size) 0
  field "Linux" ++ field nodename ++ field "6.1.0" ++ field "#1 SMP" ++ field machine ++ field "(none)"

end Abi

end Bap.Linux
