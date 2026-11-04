import Std.Data.HashMap
import Bap.Core.Zeros

/-! # A virtual Linux kernel

What a program sees of Linux besides its memory and its tasks: files, directories, descriptors, the working directory, the
program break and a clock. This is pure and it is all there is: nothing here touches the machine that this runs on, so a run
is the same wherever and whenever it happens, and a program can do no harm. A file of the host is in here only if somebody put
it in before the run.

Everyone is root, and modes are kept but not enforced. Times come from a clock that ticks when it is read. -/

namespace Bap.Linux

/-! The numbers of errors, as Linux has them on x86-64 and on most others: what a call fails with here, and what `Architecture.errno`
gives MIPS its own numbers of, which differ above 34. -/

namespace Errno
def eperm : Nat := 1
def eacces : Nat := 13
def enoent : Nat := 2
def enoexec : Nat := 8
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
def eagain : Nat := 11
def epipe : Nat := 32
def erange : Nat := 34
def enosys : Nat := 38
def enotempty : Nat := 39
def eloop : Nat := 40
def enxio : Nat := 6
def enotsock : Nat := 88
def emsgsize : Nat := 90
def eprototype : Nat := 91
def enoprotoopt : Nat := 92
def eprotonosupport : Nat := 93
def esocktnosupport : Nat := 94
def eopnotsupp : Nat := 95
def eafnosupport : Nat := 97
def eaddrinuse : Nat := 98
def econnreset : Nat := 104
def eisconn : Nat := 106
def enotconn : Nat := 107
def econnrefused : Nat := 111
def edestaddrreq : Nat := 89
def eaddrnotavail : Nat := 99
def enetunreach : Nat := 101
end Errno

/-- What came to a socket and hasn't been read: its bytes, the name of the socket that sent it if it had one, and the open files that
it hands over. -/
structure Message where
  data : ByteArray
  sender : Option String := none
  rights : List Nat := []
  deriving Inhabited

/-- A socket of the Unix domain. -/
structure Socket where
  /-- `SOCK_STREAM`, `SOCK_DGRAM` or `SOCK_SEQPACKET`, as 1, 2 and 5. -/
  type : Nat
  /-- The name that it was bound to, as it was given: a path, or a name of its own that starts with a zero byte. -/
  name : Option String := none
  /-- The socket at the other end, by its inode, or where datagrams go when a send doesn't say. -/
  peer : Option Nat := none
  listening : Bool := false
  /-- The connections that `accept` hasn't taken yet, by the inodes of their ends here. -/
  pending : List Nat := []
  /-- That it is a connection that nothing has accepted yet, which is there although no descriptor has it. -/
  waiting : Bool := false
  incoming : Array Message := #[]
  /-- What `shutdown` said: that nothing more is to be read of it, or written. -/
  readShut : Bool := false
  writeShut : Bool := false
  /-- The process that made it, or for the end of a connection that a listener accepts, the one that listens: what `SO_PEERCRED` says of
  it to the other end. -/
  owner : Nat := 0
  /-- `AF_UNIX`, `AF_INET` or `AF_INET6`, as 1, 2 and 10. -/
  family : Nat := 1
  /-- Where datagrams of the Internet go when a send doesn't say: the address that it was connected to, whoever has it then. -/
  remote : Option String := none

/-- What an epoll instance watches of a descriptor: the descriptor that it was given, its open file, which is what is watched, the
events that it asks for, the data that it gives back with them, and whether it was told of and hasn't been ready since, of
`EPOLLET`, or is told of no more until it is changed, of `EPOLLONESHOT`. -/
structure EpollItem where
  fd : Nat
  file : Nat
  events : Nat
  data : Nat
  told : Bool := false
  deriving Repr

/-- A pseudo-terminal, as its master has it: its number under `/dev/pts`, its `termios` and window, what its slave has to read, as a
line at a time in canonical mode, the line that is being edited, how many ends of file are to be read, what its master has to read,
its foreground process group and its session, whether its slave is locked, as `unlockpt` undoes, and whether its slave was opened. -/
structure Terminal where
  index : Nat
  iflag : Nat := 0x500
  oflag : Nat := 0x5
  cflag : Nat := 0xbf
  lflag : Nat := 0x8a3b
  /-- VINTR, VQUIT, VERASE, VKILL, VEOF, VTIME, VMIN, VSWTC, VSTART, VSTOP, VSUSP, VEOL, VREPRINT, VDISCARD, VWERASE, VLNEXT,
  VEOL2. -/
  cc : List Nat := [3, 28, 127, 21, 4, 0, 1, 0, 17, 19, 26, 0, 18, 15, 23, 22, 0, 0, 0]
  rows : Nat := 24
  cols : Nat := 80
  input : List ByteArray := []
  line : ByteArray := ByteArray.empty
  ends : Nat := 0
  output : ByteArray := ByteArray.empty
  foreground : Nat := 0
  session : Nat := 0
  locked : Bool := true
  opened : Bool := false

/-- What an inode has of itself besides what it holds: when it was last read, written and changed, by the kernel's clock, whose it is,
its extended attributes, and the seals of `memfd_create`. -/
structure Meta where
  accessed : Nat := 1700000000 * 1000000000
  modified : Nat := 1700000000 * 1000000000
  changed : Nat := 1700000000 * 1000000000
  uid : Nat := 0
  gid : Nat := 0
  attributes : List (String × ByteArray) := []
  seals : Nat := 0

/-- What an inode is and holds. -/
inductive Content where
  | file (data : ByteArray)
  | directory
  | symlink (target : String)
  /-- What reads get from it, in order, and writes go to the output of the kernel. It can't seek. -/
  | console (input : ByteArray)
  /-- What a generator of this name makes when it is opened, as the files of `/proc` are: see `addGenerated`. -/
  | generated (name : String)
  /-- What has been written to a pipe, from where it hasn't been read yet, and how much has been read of all that was ever written. It lets go of what is read once that is half of it. -/
  | pipe (buffer : ByteArray) (head consumed : Nat)
  /-- A socket, with all that it holds: see `Bap.Linux.Sockets`. -/
  | socket (socket : Socket)
  /-- Of `eventfd`: its count, and whether a read takes one of it, as `EFD_SEMAPHORE` has it, rather than all of it. -/
  | eventfd (count : Nat) (semaphore : Bool)
  /-- Of `timerfd_create`: when it next expires, if it is armed, by the kernel's clock, and every how long after. -/
  | timerfd (expiry : Option Nat) (interval : Nat)
  /-- Of `signalfd`: the signals that it reads. -/
  | signalfd (mask : Nat)
  /-- Of `epoll_create`: what it watches. -/
  | epoll (items : List EpollItem)
  /-- The master of a pseudo-terminal, as `/dev/ptmx` opens it, which has the terminal. -/
  | ptyMaster (terminal : Terminal)
  /-- The slave of a pseudo-terminal, `/dev/pts/N`, of the master at that inode. -/
  | ptySlave (master : Nat)
  /-- A device of `/dev`: 0 is `null`, 1 `zero`, 2 `full`, 3 `random` and `urandom`, and 4 `tty` and 5 `ptmx`, which opening asks of
  `Bap.Linux.Tty`. -/
  | device (kind : Nat)

/-- A file of any kind: its number, what it holds, and its type and permissions as `st_mode` has them. -/
structure Inode where
  number : Nat
  content : Content
  mode : Nat
  details : Meta := {}

/-- An inode that was written at a time, and so changed then. -/
def Inode.written (inode : Inode) (clock : Nat) : Inode :=
  { inode with details := { inode.details with modified := clock, changed := clock } }

/-- What `open` makes: `dup` and `fork` share it, and with it the offset. -/
structure OpenFile where
  inode : Nat
  offset : Nat := 0
  flags : Nat

/-- A descriptor of a process: which open file it is, and whether `execve` closes it. -/
structure Descriptor where
  openFile : Nat
  closeOnExec : Bool := false

/-- A part of the memory of a process that has a file behind it, or for memory that processes share, an inode with no path. What a
shared one holds is what the file holds, and the file is what is written to it. -/
structure FileMapping where
  start : Nat
  size : Nat
  inode : Nat
  offset : Nat
  shared : Bool
  /-- Whether the file was opened so that this can write to it, which it needn't do yet. -/
  mayWrite : Bool
  deriving DecidableEq, Repr

namespace FileMapping

/-- What is left of a mapping without `lower`..`upper`. -/
def without (mapping : FileMapping) (lower upper : Nat) : List FileMapping :=
  let stop := mapping.start + mapping.size
  if stop ≤ lower || upper ≤ mapping.start then [mapping]
  else
    (if mapping.start < lower then [{ mapping with size := lower - mapping.start }] else []) ++
    (if upper < stop then [{ mapping with start := upper, size := stop - upper, offset := mapping.offset + (upper - mapping.start) }] else [])

/-- Whether it has any of `lower`..`upper`, which `upper` isn't in. -/
def overlaps (mapping : FileMapping) (lower upper : Nat) : Bool :=
  mapping.start < upper && lower < mapping.start + mapping.size

end FileMapping

/-- Who a process is, as `setuid` and its kin have it: of users and of groups, the real, the effective, the saved and that of the
filesystem, and the groups that it is in besides. Everyone starts as root. -/
structure Credentials where
  uid : Nat := 0
  euid : Nat := 0
  suid : Nat := 0
  fsuid : Nat := 0
  gid : Nat := 0
  egid : Nat := 0
  sgid : Nat := 0
  fsgid : Nat := 0
  groups : List Nat := []
  deriving DecidableEq, Repr

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
  /-- The auxiliary vector that it started with, as a type and a value by turns. -/
  auxiliary : List Nat := []
  /-- What of its memory has a file behind it, which a child has too and `execve` ends. -/
  mappings : List FileMapping := []
  /-- Its process group and its session, of which 0 is its own id: see `pgidOf` and `sidOf`. -/
  pgid : Nat := 0
  sid : Nat := 0
  /-- The terminal that it has as its controlling terminal, by the inode of its end that a process has. -/
  terminal : Option Nat := none
  credentials : Credentials := {}
  /-- What `setrlimit` and `prlimit` set, by resource as Linux numbers them besides MIPS: soft and hard. -/
  limits : List (Nat × Nat × Nat) := []
  /-- Its nice value, as 20 more than it, from 0 to 39. -/
  nice : Nat := 20
  /-- That it is over: only its process group and session are kept, which a wait of a group goes by until it is reaped. -/
  ended : Bool := false

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
  auxiliary : List Nat := []
  big : Bool := false
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
  /-- Who it is, its process group and session, and its limits of the stack and of descriptors, soft and hard. -/
  credentials : Credentials := {}
  pgid : Nat := 0
  sid : Nat := 0
  stack : Nat × Nat := (8 * 1024 * 1024, 2 ^ 64 - 1)
  files : Nat × Nat := (1024, 4096)
  /-- The descriptors that it has, as `/proc/PID/fdinfo` says of them: each, its offset and its flags. -/
  descriptors : List (Nat × Nat × Nat) := []

/-- What makes the bytes of a generated file. -/
abbrev Generator := ProcessView → ByteArray

/-- All that the kernel is: its files, what is open of them, its processes, what was written to the console and its clock. A socket that
is bound to a name of its own, or to an address of the Internet, has that name among the paths, which don't start with `/`. -/
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

/-- The absolute path of these parts. -/
def ofParts (parts : List String) : String := "/" ++ "/".intercalate parts

/-- Without its last part. -/
def parent (path : String) : String := ofParts (parts "/" path).dropLast

/-- Its last part, which for the root is `/`. -/
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
      inodes := kernel.inodes.insert number
        { number, content, mode, details := { accessed := kernel.clock, modified := kernel.clock, changed := kernel.clock } }
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

/-- The directory at a path, as the kernel finds it, through the links of its parts: made, with each part before it that isn't there,
with `mode`. That a part is something other than a directory is `ENOTDIR`. -/
private def directoryAt (kernel : Kernel) (path : String) (mode : Nat) : Result (Kernel × String) :=
  -- It is mostly there, which one walk finds; a part at a time otherwise.
  match kernel.resolve "/" path with
  | .ok (found, some number) =>
    match kernel.inodes.get? number with
    | some { content := .directory, .. } => .ok (kernel, found)
    | _ => .error Errno.enotdir
  | _ =>
  (Path.parts "/" path).foldlM (init := (kernel, "/")) fun (kernel, at_) part => do
    match ← kernel.resolve at_ part with
    | (found, some number) =>
      match kernel.inodes.get? number with
      | some { content := .directory, .. } => pure (kernel, found)
      | _ => throw Errno.enotdir
    | (found, none) => pure ((addInode kernel found .directory mode).1, found)

/-- Makes a directory, with each one before it that isn't there, whose parts may be links, as `mkdir -p` does: one that is there
already is kept as it is, and something else there is `EEXIST`, or `ENOTDIR` before the last part. It can be called on the kernel of a
machine that runs, by `Machine.addDirectory`. -/
def putDirectory (kernel : Kernel) (path : String) (mode : Nat := 0o40755) : Result Kernel := do
  let parts := Path.parts "/" path
  let some name := parts.getLast? | pure kernel
  let (kernel, parent) ← directoryAt kernel (Path.ofParts parts.dropLast) 0o40755
  match ← kernel.resolve parent name with
  | (_, some number) =>
    match kernel.inodes.get? number with
    | some { content := .directory, .. } => pure kernel
    | _ => throw Errno.eexist
  | (found, none) => pure (addInode kernel found .directory (0o40000 ||| mode % 0o10000)).1

/-- Puts a file in, with each directory before it that isn't there, whose parts may be links: a file that is there, or the file
that a link there points to, has these bytes now and this mode, and keeps its number, so that what has it open reads them; a
directory there is `EISDIR`, and anything but a directory before it `ENOTDIR`. It can be called on the kernel of a machine that runs,
by `Machine.addFile`; what is mapped of the file keeps what it had. -/
def putFile (kernel : Kernel) (path : String) (data : ByteArray) (mode : Nat := 0o100644) : Result Kernel := do
  let parts := Path.parts "/" path
  let some name := parts.getLast? | throw Errno.eisdir
  let (kernel, parent) ← directoryAt kernel (Path.ofParts parts.dropLast) 0o40755
  let mode := 0o100000 ||| mode % 0o10000
  match ← kernel.resolve parent name with
  | (_, some number) =>
    match kernel.inodes.get? number with
    | some { content := .file _, .. } => pure { kernel with inodes := kernel.inodes.insert number { number, content := .file data, mode } }
    | some { content := .directory, .. } => throw Errno.eisdir
    | _ => throw Errno.eexist
  | (found, none) => pure (addInode kernel found (.file data) mode).1

/-- A process by the id of its thread group, or one with nothing yet. -/
def process (kernel : Kernel) (group : Nat) : Process := kernel.processes.getD group {}

/-- What a process is now. -/
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

/-- The process group of a process. -/
def pgidOf (kernel : Kernel) (group : Nat) : Nat :=
  let process := kernel.process group
  if process.pgid == 0 then group else process.pgid

/-- The session of a process. -/
def sidOf (kernel : Kernel) (group : Nat) : Nat :=
  let process := kernel.process group
  if process.sid == 0 then group else process.sid

/-- A process made by another: it has copies of the descriptors, which share the open files with its parent, and the rest of its
parent's state, in its process group and session. -/
def fork (kernel : Kernel) (parent child : Nat) : Kernel :=
  kernel.setProcess child { kernel.process parent with pgid := kernel.pgidOf parent, sid := kernel.sidOf parent }

/-- A process is over, and what only it had open with it: of it, its process group and session stay. -/
def exitProcess (kernel : Kernel) (group : Nat) : Kernel :=
  kernel.setProcess group { pgid := kernel.pgidOf group, sid := kernel.sidOf group, ended := true }

/-- The soft and hard limits of a resource of a process, as Linux numbers them besides MIPS. -/
def limitOf (kernel : Kernel) (group resource : Nat) : Nat × Nat :=
  match (kernel.process group).limits.find? (·.1 == resource) with
  | some (_, soft, hard) => (soft, hard)
  | none =>
    let unlimited := 2 ^ 64 - 1
    match resource with
    | 3 => (8 * 1024 * 1024, unlimited)
    | 7 => (1024, 4096)
    | 4 => (0, unlimited)
    | 8 => (8 * 1024 * 1024, 8 * 1024 * 1024)
    | 13 | 14 => (0, 0)
    | _ => (unlimited, unlimited)

/-- The open file of a descriptor of a process, with its id, or `EBADF`. -/
def openFileOf (kernel : Kernel) (group fd : Nat) : Result (Nat × OpenFile) :=
  match (kernel.process group).descriptors.get? fd with
  | none => .error Errno.ebadf
  | some descriptor =>
    match kernel.openFiles.get? descriptor.openFile with
    | none => .error Errno.ebadf
    | some file => .ok (descriptor.openFile, file)

/-- An inode by its number. -/
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

/-! The flags of `open` as the kernel has them, which are those of x86-64: `Architecture.openFlags` gives them from a guest's. -/

def oCreat : Nat := 0x40
def oExcl : Nat := 0x80
def oTrunc : Nat := 0x200
def oAppend : Nat := 0x400
def oDirectory : Nat := 0x10000
def oNofollow : Nat := 0x20000
def oCloexec : Nat := 0x80000
def oNonblock : Nat := 0x800

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
        .ok { kernel with inodes := kernel.inodes.insert number ({ inode with content := .file ByteArray.empty }.written kernel.clock) }
      else .ok kernel
    | .console _ =>
      if has flags oDirectory then .error Errno.enotdir
      .ok kernel
    -- `/dev/pts/N`: `Bap.Linux.Tty` says whether it may be opened.
    | .ptySlave _ | .device _ => .ok kernel
    -- It has no path.
    | .pipe .. | .eventfd .. | .timerfd .. | .signalfd _ | .epoll _ | .ptyMaster _ => .error Errno.einval
    -- What is bound to a path is connected to, not opened.
    | .socket _ => .error Errno.enxio
  let openFile := kernel.nextOpenFile
  let kernel := { kernel with
    openFiles := kernel.openFiles.insert openFile { inode := number, flags }
    nextOpenFile := openFile + 1 }
  .ok (kernel.addDescriptor group openFile (has flags oCloexec))

/-- `read`, at the offset of the file, which moves. Of a pipe, what is first in it, which goes. -/
def read (kernel : Kernel) (group fd count : Nat) : Result (Kernel × ByteArray) := do
  let (id, file) ← openFileOf kernel group fd
  if file.flags &&& 3 == 1 then .error Errno.ebadf
  let inode ← inodeOf kernel file.inode
  if let .pipe buffer head consumed := inode.content then
    let bytes := buffer.extract head (head + count)
    let next := head + bytes.size
    let content := if next * 2 ≥ buffer.size then Content.pipe (buffer.extract next buffer.size) 0 (consumed + bytes.size)
      else .pipe buffer next (consumed + bytes.size)
    return ({ kernel with inodes := kernel.inodes.insert file.inode { inode with content } }, bytes)
  -- What a device gives: nothing of `null`, zeros of `zero` and `full`, and of `random`, bytes that are the same each time.
  if let .device kind := inode.content then
    let bytes := match kind with
      | 1 | 2 => Bap.zeroBytes count
      | 3 => ByteArray.mk ((List.range count).map fun index => ((file.offset + index) * 167 + 13).toUInt8).toArray
      | _ => ByteArray.empty
    return ({ kernel with openFiles := kernel.openFiles.insert id { file with offset := file.offset + bytes.size } }, bytes)
  let data ← match inode.content with
    | .file data | .console data => .ok data
    | .directory => .error Errno.eisdir
    | .symlink _ | .generated _ | .pipe .. | .socket _ | .eventfd .. | .timerfd .. | .signalfd _ | .epoll _ | .ptyMaster _ | .ptySlave _ | .device _ => .error Errno.einval
  let bytes := readAt data file.offset count
  .ok ({ kernel with openFiles := kernel.openFiles.insert id { file with offset := file.offset + bytes.size } }, bytes)

/-- `pread`, which leaves the offset. -/
def readFrom (kernel : Kernel) (group fd count offset : Nat) : Result ByteArray := do
  let (_, file) ← openFileOf kernel group fd
  if file.flags &&& 3 == 1 then .error Errno.ebadf
  let inode ← inodeOf kernel file.inode
  match inode.content with
  | .file data => .ok (readAt data offset count)
  | .console _ | .pipe .. | .socket _ | .eventfd .. | .timerfd .. | .signalfd _ | .epoll _ | .ptyMaster _ | .ptySlave _ | .device _ => .error Errno.espipe
  | .directory => .error Errno.eisdir
  | .symlink _ | .generated _ => .error Errno.einval

/-- `write`, at the offset of the file, or at its end if it was opened to append. -/
def write (kernel : Kernel) (group fd : Nat) (bytes : ByteArray) : Result (Kernel × Nat) := do
  let (id, file) ← openFileOf kernel group fd
  if !writable file.flags then .error Errno.ebadf
  let inode ← inodeOf kernel file.inode
  match inode.content with
  | .console _ => .ok ({ kernel with output := kernel.output ++ bytes }, bytes.size)
  -- `full` has no room, and the others take all of it.
  | .device 2 => .error 28
  | .device _ => .ok (kernel, bytes.size)
  | .pipe buffer head consumed =>
    .ok ({ kernel with inodes := kernel.inodes.insert file.inode { inode with content := .pipe (buffer ++ bytes) head consumed } }, bytes.size)
  | .file data =>
    let offset := if has file.flags oAppend then data.size else file.offset
    .ok ({ kernel with
      inodes := kernel.inodes.insert file.inode ({ inode with content := .file (writeAt data offset bytes) }.written kernel.clock)
      openFiles := kernel.openFiles.insert id { file with offset := offset + bytes.size } }, bytes.size)
  | .directory => .error Errno.eisdir
  -- `Machine` sends to a socket, and counts what is written to an `eventfd`.
  | .symlink _ | .generated _ | .socket _ | .eventfd .. | .timerfd .. | .signalfd _ | .epoll _ | .ptyMaster _ | .ptySlave _ => .error Errno.einval

/-- `writeAt`, in the same bytes if nothing else holds them. -/
def writeInto (data : ByteArray) (offset : Nat) (bytes : ByteArray) : ByteArray :=
  let filled := if data.size < offset then data ++ Bap.zeroBytes (offset - data.size) else data
  bytes.copySlice 0 filled offset bytes.size false

/-- Why `write` can't go ahead, if it can't, for `writeKnown`. -/
def writeError (kernel : Kernel) (group fd : Nat) : Option Nat :=
  match kernel.openFileOf group fd with
  | .error errno => some errno
  | .ok (_, file) =>
    if !writable file.flags then some Errno.ebadf
    else
      match kernel.inodes.get? file.inode with
      | none => some Errno.eio
      | some { content := .directory, .. } => some Errno.eisdir
      | some { content := .symlink _, .. } | some { content := .generated _, .. } | some { content := .socket _, .. } => some Errno.einval
      -- `/dev/full` has no room.
      | some { content := .device 2, .. } => some 28
      | _ => none

/-- `write` for what `writeError` has nothing against, which changes all it can in place: one that takes the kernel as it is the only holder of it makes as many small
writes as it likes for the size of each, however much is already there. -/
def writeKnown (kernel : Kernel) (group fd : Nat) (bytes : ByteArray) : Kernel :=
  match kernel.openFileOf group fd with
  | .error _ => kernel
  | .ok (id, file) =>
    let number := file.inode
    let isConsole := match kernel.inodes.get? number with
      | some { content := .console _, .. } => true
      | _ => false
    if isConsole then { kernel with output := kernel.output ++ bytes }
    else
      let size := match kernel.inodes.get? number with
        | some { content := .file data, .. } => data.size
        | _ => 0
      let offset := if has file.flags oAppend then size else file.offset
      let isFile := match kernel.inodes.get? number with
        | some { content := .file _, .. } => true
        | _ => false
      { kernel with
        openFiles := if isFile then kernel.openFiles.insert id { file with offset := offset + bytes.size } else kernel.openFiles
        inodes := kernel.inodes.alter number (·.map fun inode =>
          match inode with
          | inode@{ content := .file data, .. } => { inode with content := .file (writeInto data offset bytes) }.written kernel.clock
          | inode@{ content := .pipe buffer head consumed, .. } => { inode with content := .pipe (buffer ++ bytes) head consumed }
          | other => other) }

/-- `pwrite`, which leaves the offset. -/
def writeTo (kernel : Kernel) (group fd : Nat) (bytes : ByteArray) (offset : Nat) : Result (Kernel × Nat) := do
  let (_, file) ← openFileOf kernel group fd
  if !writable file.flags then .error Errno.ebadf
  let inode ← inodeOf kernel file.inode
  match inode.content with
  | .file data =>
    .ok ({ kernel with inodes := kernel.inodes.insert file.inode ({ inode with content := .file (writeAt data offset bytes) }.written kernel.clock) },
      bytes.size)
  | .console _ | .pipe .. | .socket _ | .eventfd .. | .timerfd .. | .signalfd _ | .epoll _ | .ptyMaster _ | .ptySlave _ | .device _ => .error Errno.espipe
  | .directory => .error Errno.eisdir
  | .symlink _ | .generated _ => .error Errno.einval

/-- `lseek`. A signed offset comes as `(negative, size)`. -/
def seek (kernel : Kernel) (group fd : Nat) (negative : Bool) (distance whence : Nat) : Result (Kernel × Nat) := do
  let (id, file) ← openFileOf kernel group fd
  let inode ← inodeOf kernel file.inode
  let size ← match inode.content with
    | .file data => .ok data.size
    | .directory => .ok 0
    | .console _ | .pipe .. | .socket _ | .eventfd .. | .timerfd .. | .signalfd _ | .epoll _ | .ptyMaster _ | .ptySlave _ | .device _ => .error Errno.espipe
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

/-- `pipe2`: a pipe, and its descriptors, to read and to write. -/
def pipe (kernel : Kernel) (group flags : Nat) : Kernel × Nat × Nat :=
  let number := kernel.nextInode
  let reading := kernel.nextOpenFile
  let writing := reading + 1
  let kept := flags &&& oNonblock
  let kernel := { kernel with
    inodes := kernel.inodes.insert number { number, content := .pipe ByteArray.empty 0 0, mode := 0o10600 }
    nextInode := number + 1
    openFiles := (kernel.openFiles.insert reading { inode := number, flags := kept }).insert writing { inode := number, flags := 1 ||| kept }
    nextOpenFile := writing + 1 }
  let (kernel, readFd) := kernel.addDescriptor group reading (flags &&& oCloexec != 0)
  let (kernel, writeFd) := kernel.addDescriptor group writing (flags &&& oCloexec != 0)
  (kernel, readFd, writeFd)

/-- A descriptor of something that has no path, as `eventfd` and `epoll_create` make: on a new inode of `content`, opened to read and
write with `flags` of `O_NONBLOCK` and `O_CLOEXEC`. -/
def addObject (kernel : Kernel) (group : Nat) (content : Content) (flags : Nat) : Kernel × Nat :=
  let number := kernel.nextInode
  let openFile := kernel.nextOpenFile
  let kernel := { kernel with
    inodes := kernel.inodes.insert number { number, content, mode := 0o600 }
    nextInode := number + 1
    openFiles := kernel.openFiles.insert openFile { inode := number, flags := 2 ||| (flags &&& oNonblock) }
    nextOpenFile := openFile + 1 }
  kernel.addDescriptor group openFile (flags &&& oCloexec != 0)

/-- What a descriptor is on, of the open file and the inode. -/
def objectOf (kernel : Kernel) (group fd : Nat) : Result (Nat × OpenFile × Inode) := do
  let (_, file) ← openFileOf kernel group fd
  pure (file.inode, file, ← inodeOf kernel file.inode)

/-- A file of a device at a path, with the directories that it needs, which `Bap.Linux.Tty` and the devices make as they are asked for. -/
def addDevice (kernel : Kernel) (path : String) (content : Content) (mode : Nat) : Kernel × Nat :=
  let kernel := addDirectories kernel (Path.parent path)
  addInode kernel path content mode

/-- What an inode holds now. -/
def setContent (kernel : Kernel) (number : Nat) (content : Content) : Kernel :=
  match kernel.inodes.get? number with
  | some inode => { kernel with inodes := kernel.inodes.insert number { inode with content } }
  | none => kernel

/-- The inode of a descriptor, if that is a pipe. -/
def pipeOf (kernel : Kernel) (group fd : Nat) : Option Nat :=
  match kernel.openFileOf group fd with
  | .ok (_, file) =>
    match kernel.inodes.get? file.inode with
    | some { content := .pipe .., .. } => some file.inode
    | _ => none
  | .error _ => none

/-- Whether a descriptor of one of these processes reads a pipe, or writes it. -/
def pipeHeld (kernel : Kernel) (number : Nat) (groups : List Nat) (toWrite : Bool) : Bool :=
  groups.any fun group =>
    (kernel.process group).descriptors.toList.any fun (_, descriptor) =>
      match kernel.openFiles.get? descriptor.openFile with
      | some file => file.inode == number && writable file.flags == toWrite
      | none => false

/-- Whether a descriptor was opened not to wait. -/
def nonblocking (kernel : Kernel) (group fd : Nat) : Bool :=
  match kernel.openFileOf group fd with
  | .ok (_, file) => file.flags &&& oNonblock != 0
  | .error _ => false

/-- How much a pipe has to read. -/
def pipeWaiting (kernel : Kernel) (number : Nat) : Nat :=
  match kernel.inodes.get? number with
  | some { content := .pipe buffer head _, .. } => buffer.size - head
  | _ => 0

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
  accessed : Nat
  modified : Nat
  changed : Nat
  uid : Nat := 0
  gid : Nat := 0
  deriving DecidableEq, Repr

private def statOf (inode : Inode) : Stat :=
  let (size, links) := match inode.content with
    | .file data => (data.size, 1)
    | .directory => (4096, 2)
    | .symlink target => (target.utf8ByteSize, 1)
    | .console _ | .generated _ | .pipe .. | .socket _ | .eventfd .. | .timerfd .. | .signalfd _ | .epoll _ | .ptyMaster _ | .ptySlave _ | .device _ => (0, 1)
  { inode := inode.number, mode := inode.mode, size, links, accessed := inode.details.accessed, modified := inode.details.modified
    changed := inode.details.changed, uid := inode.details.uid, gid := inode.details.gid }

/-- `stat` and `lstat`. -/
def statPath (kernel : Kernel) (base path : String) (follow : Bool := true) : Result Stat := do
  if path == "" then .error Errno.enoent
  let (_, found) ← kernel.resolve base path follow
  match found with
  | none => .error Errno.enoent
  | some number => .ok (statOf (← inodeOf kernel number))

/-- `fstat`. -/
def statDescriptor (kernel : Kernel) (group fd : Nat) : Result Stat := do
  let (_, file) ← openFileOf kernel group fd
  .ok (statOf (← inodeOf kernel file.inode))

/-- The path of what is open, for a directory. -/
private def pathOfInode (kernel : Kernel) (number : Nat) : Option String :=
  (kernel.paths.toList.find? fun entry => entry.2 == number && entry.1.startsWith "/").map (·.1)

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
    -- A name of a socket of its own isn't in a directory.
    if entry.1.startsWith "/" && parts.length == inside.length + 1 && parts.take inside.length == inside then
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
      | some { content := .pipe .., .. } => 1
      | some { content := .generated _, .. } => 8
      | some { content := .socket _, .. } => 12
      | some _ | none => 0
    let parentNumber := (kernel.paths.get? (Path.parent path)).getD inode.number
    let all := [(inode.number, 4, "."), (parentNumber, 4, "..")] ++
      (children kernel path).map fun entry => (entry.2, typeOf entry.2, entry.1)
    .ok (id, file.offset, all.drop file.offset)
  | .directory, none => .error Errno.eio
  | _, _ => .error Errno.enotdir

/-- All of the entries of a directory that a descriptor has open, in that order. -/
def directoryListing (kernel : Kernel) (group fd : Nat) : Result (Array (Nat × Nat × String)) := do
  let (id, file) ← openFileOf kernel group fd
  -- From the start, wherever it has been read to.
  let from_ := { kernel with openFiles := kernel.openFiles.insert id { file with offset := 0 } }
  let (_, _, entries) ← directoryEntries from_ group fd
  .ok entries.toArray

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

/-- Another path of an inode, as `linkat` of `AT_EMPTY_PATH` gives one to what a descriptor is open on. -/
def linkInode (kernel : Kernel) (number : Nat) (base target : String) : Result Kernel := do
  let inode ← inodeOf kernel number
  if let .directory := inode.content then .error Errno.eperm
  let (normal, existing) ← kernel.resolve base target (follow := false)
  if existing.isSome then .error Errno.eexist
  if !parentIsDirectory kernel normal then .error Errno.enoent
  .ok { kernel with
    paths := kernel.paths.insert normal number
    inodes := kernel.inodes.insert number { inode with details := { inode.details with changed := kernel.clock } } }

/-- `link`: another path of the inode of `source`, which isn't a directory, followed through a link at its end if `follow`. -/
def link (kernel : Kernel) (base source target : String) (follow : Bool) : Result Kernel := do
  let (_, found) ← kernel.resolve base source (follow := follow)
  let some number := found | .error Errno.enoent
  kernel.linkInode number base target

/-- `renameat2`: of `RENAME_NOREPLACE`, not over what is there, and of `RENAME_EXCHANGE`, the two trade places, with all under them. -/
def renameWith (kernel : Kernel) (base source target : String) (flags : Nat) : Result Kernel := do
  if flags &&& 3 == 3 || flags &&& 4 != 0 && flags &&& 2 != 0 then .error Errno.einval
  let (from_, found) ← kernel.resolve base source (follow := false)
  let some _ := found | .error Errno.enoent
  let (to_, existing) ← kernel.resolve base target (follow := false)
  if flags &&& 1 != 0 && existing.isSome then .error Errno.eexist
  if flags &&& 2 == 0 then return ← kernel.rename base source target
  let some _ := existing | .error Errno.enoent
  if (to_ ++ "/").startsWith (from_ ++ "/") || (from_ ++ "/").startsWith (to_ ++ "/") then .error Errno.einval
  let swap (path : String) : String :=
    if path == from_ then to_ else if path == to_ then from_
    else if path.startsWith (from_ ++ "/") then to_ ++ (path.drop from_.length).toString
    else if path.startsWith (to_ ++ "/") then from_ ++ (path.drop to_.length).toString
    else path
  .ok { kernel with paths := kernel.paths.fold (init := {}) fun paths path number => paths.insert (swap path) number }

/-- The devices of `/dev` and what is around them: `null`, `zero`, `full`, `random`, `urandom`, `tty` and `ptmx`, the directories
`pts` and `shm`, and `stdin`, `stdout`, `stderr` and `fd` of `/proc/self/fd`. Nothing replaces what is already there. -/
def installDevices (kernel : Kernel) : Kernel :=
  let kernel := [("/dev/null", 0), ("/dev/zero", 1), ("/dev/full", 2), ("/dev/random", 3), ("/dev/urandom", 3), ("/dev/tty", 4),
      ("/dev/ptmx", 5)].foldl (init := kernel) fun kernel (path, kind) =>
    if kernel.paths.contains path then kernel else (addInode (addDirectories kernel "/dev") path (.device kind) 0o20666).1
  let kernel := addDirectories (addDirectories kernel "/dev/pts") "/dev/shm"
  [("/dev/stdin", "/proc/self/fd/0"), ("/dev/stdout", "/proc/self/fd/1"), ("/dev/stderr", "/proc/self/fd/2"),
    ("/dev/fd", "/proc/self/fd")].foldl (init := kernel) fun kernel (path, target) =>
    if kernel.paths.contains path then kernel else kernel.addSymlink path target

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
    .ok { kernel with inodes := kernel.inodes.insert number ({ inode with content := .file data }.written kernel.clock) }
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
    .ok { kernel with inodes := kernel.inodes.insert number { inode with mode := kept ||| (mode &&& 0o7777), details := { inode.details with changed := kernel.clock } } }

/-- Where a byte of an inode is, to what goes by address spaces, of which there are as many as tasks: this and the inode, and its offset. -/
def fileSpace : Nat := 2 ^ 62

/-- The bytes of `size` that a mapping of an inode holds, with zeros after the end of the file. -/
def inodeBytes (kernel : Kernel) (number offset size : Nat) : ByteArray :=
  match kernel.inodes.get? number with
  | some { content := .file data, .. } =>
    let bytes := readAt data offset size
    bytes ++ Bap.zeroBytes (size - bytes.size)
  | _ => Bap.zeroBytes size

/-- What of a mapping of an inode is in the file, as the file doesn't grow by a write to memory. -/
def inodeExtent (kernel : Kernel) (number offset size : Nat) : Nat :=
  match kernel.inodes.get? number with
  | some { content := .file data, .. } => min size (data.size - offset)
  | _ => 0

/-- A file with the bytes in `memory` at `offset` where they aren't those of `before`, which leaves what others changed. -/
def writeChanges (kernel : Kernel) (number offset : Nat) (before memory : ByteArray) : Kernel :=
  match kernel.inodes.get? number with
  | some inode =>
    match inode.content with
    | .file data =>
      let data := (List.range (min before.size memory.size)).foldl (init := data) fun data index =>
        if before[index]! != memory[index]! then data.set! (offset + index) memory[index]! else data
      { kernel with inodes := kernel.inodes.insert number ({ inode with content := .file data }.written kernel.clock) }
    | _ => kernel
  | none => kernel

/-- An inode of what is given, zeros, that no path leads to, which is what memory that processes share is. -/
def anonymousInode (kernel : Kernel) (data : ByteArray) : Kernel × Nat :=
  let number := kernel.nextInode
  ({ kernel with
    inodes := kernel.inodes.insert number { number, content := .file data, mode := 0o100600 }
    nextInode := number + 1 }, number)

/-- The inode of a descriptor and how it was opened: whether it can be read, and whether written. -/
def mappingSource (kernel : Kernel) (group fd : Nat) : Result (Nat × Bool × Bool) := do
  let (_, file) ← openFileOf kernel group fd
  .ok (file.inode, file.flags &&& 3 != 1, file.flags &&& 3 == 2)

/-- A process without what it had mapped in `lower`..`upper`. -/
def dropMappings (kernel : Kernel) (group lower upper : Nat) : Kernel :=
  let process := kernel.process group
  if process.mappings.isEmpty then kernel
  else kernel.setProcess group { process with mappings := process.mappings.flatMap (·.without lower upper) }

/-- A process has a mapping of a file now. -/
def addMapping (kernel : Kernel) (group : Nat) (mapping : FileMapping) : Kernel :=
  let process := kernel.process group
  kernel.setProcess group { process with mappings := mapping :: process.mappings }

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

/-- The low `size` bytes of a number, the least significant first. -/
def bytesOf (size value : Nat) : ByteArray :=
  ByteArray.mk ((List.range size).map fun index => (value >>> (8 * index)).toUInt8).toArray

/-- A field of a structure, in the order of the guest. -/
def field (big : Bool) (size value : Nat) : ByteArray :=
  let bytes := bytesOf size value
  if big then ByteArray.mk bytes.data.reverse else bytes

/-- `struct stat` of x86-64 and 64-bit PowerPC. -/
def stat (value : Kernel.Stat) (big : Bool := false) : ByteArray :=
  let get := field big
  let time (at_ : Nat) : ByteArray := get 8 (at_ / 1000000000) ++ get 8 (at_ % 1000000000)
  get 8 1 ++ get 8 value.inode ++ get 8 value.links ++ get 4 value.mode ++ get 4 value.uid ++ get 4 value.gid ++
    get 4 0 ++ get 8 0 ++ get 8 value.size ++ get 8 4096 ++ get 8 ((value.size + 511) / 512) ++
    time value.accessed ++ time value.modified ++ time value.changed ++ bytesOf 24 0

/-- `struct stat` of `asm-generic/stat.h`, which has the order of the fields of 32-bit systems and is smaller. -/
def genericStat (value : Kernel.Stat) : ByteArray :=
  let time (at_ : Nat) : ByteArray := bytesOf 8 (at_ / 1000000000) ++ bytesOf 8 (at_ % 1000000000)
  bytesOf 8 1 ++ bytesOf 8 value.inode ++ bytesOf 4 value.mode ++ bytesOf 4 value.links ++ bytesOf 4 value.uid ++ bytesOf 4 value.gid ++
    bytesOf 8 0 ++ bytesOf 8 0 ++ bytesOf 8 value.size ++ bytesOf 4 4096 ++ bytesOf 4 0 ++ bytesOf 8 ((value.size + 511) / 512) ++
    time value.accessed ++ time value.modified ++ time value.changed ++ bytesOf 8 0

/-- `struct stat` of 64-bit MIPS, which holds its times in 32 bits. -/
def mips64Stat (value : Kernel.Stat) (big : Bool) : ByteArray :=
  let get := field big
  let time (at_ : Nat) : ByteArray := get 4 (at_ / 1000000000) ++ get 4 (at_ % 1000000000)
  get 4 1 ++ bytesOf 12 0 ++ get 8 value.inode ++ get 4 value.mode ++ get 4 value.links ++ get 4 value.uid ++ get 4 value.gid ++
    get 4 0 ++ bytesOf 12 0 ++ get 8 value.size ++ time value.accessed ++ time value.modified ++ time value.changed ++ get 4 4096 ++
    bytesOf 4 0 ++ get 8 ((value.size + 511) / 512) ++ bytesOf 56 0

/-- `struct stat64` of i686, which is packed. -/
def stat64 (value : Kernel.Stat) : ByteArray :=
  let time (at_ : Nat) : ByteArray := bytesOf 4 (at_ / 1000000000) ++ bytesOf 4 (at_ % 1000000000)
  bytesOf 8 1 ++ bytesOf 4 0 ++ bytesOf 4 (value.inode % 2 ^ 32) ++ bytesOf 4 value.mode ++ bytesOf 4 value.links ++
    bytesOf 4 value.uid ++ bytesOf 4 value.gid ++ bytesOf 8 0 ++ bytesOf 4 0 ++ bytesOf 8 value.size ++ bytesOf 4 4096 ++
    bytesOf 8 ((value.size + 511) / 512) ++ time value.accessed ++ time value.modified ++ time value.changed ++ bytesOf 8 value.inode

/-- `struct stat64` of ARM, whose wide fields are aligned. -/
def armStat64 (value : Kernel.Stat) : ByteArray :=
  let time (at_ : Nat) : ByteArray := bytesOf 4 (at_ / 1000000000) ++ bytesOf 4 (at_ % 1000000000)
  bytesOf 8 1 ++ bytesOf 4 0 ++ bytesOf 4 (value.inode % 2 ^ 32) ++ bytesOf 4 value.mode ++ bytesOf 4 value.links ++
    bytesOf 4 value.uid ++ bytesOf 4 value.gid ++ bytesOf 8 0 ++ bytesOf 8 0 ++ bytesOf 8 value.size ++ bytesOf 4 4096 ++ bytesOf 4 0 ++
    bytesOf 8 ((value.size + 511) / 512) ++ time value.accessed ++ time value.modified ++ time value.changed ++ bytesOf 8 value.inode

/-- `struct stat64` of 32-bit PowerPC. -/
def powerpcStat64 (value : Kernel.Stat) (big : Bool) : ByteArray :=
  let get := field big
  let time (at_ : Nat) : ByteArray := get 4 (at_ / 1000000000) ++ get 4 (at_ % 1000000000)
  get 8 1 ++ get 8 value.inode ++ get 4 value.mode ++ get 4 value.links ++ get 4 value.uid ++ get 4 value.gid ++ bytesOf 8 0 ++
    bytesOf 8 0 ++ get 8 value.size ++ get 4 4096 ++ bytesOf 4 0 ++ get 8 ((value.size + 511) / 512) ++ time value.accessed ++
    time value.modified ++ time value.changed ++ bytesOf 8 0

/-- `struct stat64` of the o32 ABI of MIPS. -/
def mipsStat64 (value : Kernel.Stat) (big : Bool) : ByteArray :=
  let get := field big
  let time (at_ : Nat) : ByteArray := get 4 (at_ / 1000000000) ++ get 4 (at_ % 1000000000)
  get 4 1 ++ bytesOf 12 0 ++ get 8 value.inode ++ get 4 value.mode ++ get 4 value.links ++ get 4 value.uid ++ get 4 value.gid ++
    bytesOf 4 0 ++ bytesOf 12 0 ++ get 8 value.size ++ time value.accessed ++ time value.modified ++ time value.changed ++ get 4 4096 ++
    bytesOf 4 0 ++ get 8 ((value.size + 511) / 512)

/-- What `statfs` says of the file system that all files are on, a tmpfs of 4 GiB with all of it free. Its type, block size and the three at the end of it are of the word, so that `statfs` and `statfs64` of a 64-bit system
are the same. MIPS has its fields in another order. -/
def statfs (wide big mips : Bool) : ByteArray :=
  let get := field big
  let word := if wide then get 8 else get 4
  let tmpfs := 0x01021994
  let blocks := 1048576
  if mips then
    word tmpfs ++ word 4096 ++ word 4096 ++ (if wide then bytesOf 0 0 else bytesOf 4 0) ++ get 8 blocks ++ get 8 blocks ++
      get 8 blocks ++ get 8 blocks ++ get 8 blocks ++ bytesOf 8 0 ++ word 255 ++ word 0 ++ bytesOf (if wide then 40 else 20) 0
  else
    word tmpfs ++ word 4096 ++ get 8 blocks ++ get 8 blocks ++ get 8 blocks ++ get 8 blocks ++ get 8 blocks ++ bytesOf 8 0 ++
      word 255 ++ word 4096 ++ word 0 ++ bytesOf (if wide then 32 else 16) 0

/-- `struct sysinfo`: 2 GiB of memory, all free, in units of a byte. -/
def sysinfo (wide big : Bool) (uptime processes : Nat) : ByteArray :=
  let get := field big
  let word := if wide then get 8 else get 4
  let memory := 0x7fffffff
  word uptime ++ word 0 ++ word 0 ++ word 0 ++ word memory ++ word memory ++ word 0 ++ word 0 ++ word 0 ++ word 0 ++
    get 2 processes ++ bytesOf (if wide then 6 else 2) 0 ++ word 0 ++ word 0 ++ get 4 1 ++
    bytesOf (if wide then 4 else 8) 0

/-- `struct statx`. -/
def statx (value : Kernel.Stat) (big : Bool := false) : ByteArray :=
  let get := field big
  let time (at_ : Nat) : ByteArray := get 8 (at_ / 1000000000) ++ get 4 (at_ % 1000000000) ++ get 4 0
  -- STATX_BASIC_STATS: of the times, read, born, changed and written.
  get 4 0x7ff ++ get 4 4096 ++ get 8 0 ++ get 4 value.links ++ get 4 value.uid ++ get 4 value.gid ++
    get 2 value.mode ++ get 2 0 ++ get 8 value.inode ++ get 8 value.size ++
    get 8 ((value.size + 511) / 512) ++ get 8 0 ++ time value.accessed ++ time value.changed ++ time value.changed ++
    time value.modified ++ get 128 0

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
