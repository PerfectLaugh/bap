import Std.Data.HashMap
import Bap.Core.Zeros

/-! # A virtual Linux kernel

What a program sees of Linux besides its memory and its tasks: files, directories, descriptors, the working directory, the
program break and a clock. This is pure and it is all there is: nothing here touches the machine that this runs on, so a run
is the same wherever and whenever it happens, and a program can do no harm. A file of the host is in here only if somebody put
it in before the run, or gave a machine a directory of the host to see (`Machine.mountHost`), which it never writes.

Everyone is root, and modes are kept but not enforced. Times come from a clock that ticks when it is read.

What is mounted is seen where it is mounted as `resolve` walks a path: a bind mount is what it mounts, and a file system of its own
is a directory that no name reaches. A path that goes through one is the path of what is there, so that `..` of a bind mount is the
parent of what it mounts. A process may have a root of its own, which `pathIn` puts the paths that it gives within. A read-only
mount keeps what is on a file system of its own from changing, but not what a bind mount mounts. -/

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
def enodev : Nat := 19
def enotdir : Nat := 20
def eisdir : Nat := 21
def einval : Nat := 22
def emfile : Nat := 24
def enotty : Nat := 25
def efbig : Nat := 27
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
events that it asks for, the data that it gives back with them, and if it was told of and has been ready since, the events that it
was told of and how many times what it watches had changed then: of `EPOLLET`, it is told of again once either is other, and of
`EPOLLONESHOT`, no more until it is changed. -/
structure EpollItem where
  fd : Nat
  file : Nat
  events : Nat
  data : Nat
  told : Option (Nat × Nat) := none
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

/-- Whose a lock of a file is: a process's, that `F_SETLK` took, an open file's, that `F_OFD_SETLK` took, which the same ranges as
those of a process are in the way of, or an open file's of `flock`, which only other such are in the way of. -/
inductive LockOwner where
  | process (group : Nat)
  | openFile (id : Nat)
  | flock (id : Nat)
  deriving DecidableEq, Repr

/-- A lock of the bytes of a file from `start` up to `stop`, which `lockEnd` is the end of all of, shared or not. -/
structure FileLock where
  owner : LockOwner
  start : Nat
  stop : Nat
  exclusive : Bool
  deriving DecidableEq, Repr

/-- Where a lock of a file to its end ends, past what an offset can be. -/
def lockEnd : Nat := 2 ^ 63

/-- What an inode has of itself besides what it holds: when it was last read, written and changed, by the kernel's clock, whose it is,
its extended attributes, the seals of `memfd_create`, its locks, of which those whose owner is gone are let go of as it is locked
again, how many times what it holds was set by `Kernel.setContent`, which an item of epoll with `EPOLLET` goes by, and what
`/proc/PID/fd` says it is while it has no path: the path that it was removed from, or what made it, with ` (deleted)`; and of a file of
`O_TMPFILE` without `O_EXCL`, that `linkat` may give it a name though it has none, until it has had one. -/
structure Meta where
  accessed : Nat := 1700000000 * 1000000000
  modified : Nat := 1700000000 * 1000000000
  changed : Nat := 1700000000 * 1000000000
  uid : Nat := 0
  gid : Nat := 0
  attributes : List (String × ByteArray) := []
  seals : Nat := 0
  locks : List FileLock := []
  changes : Nat := 0
  name : String := ""
  linkable : Bool := false

/-- A watch of `inotify_add_watch`: its number, the inode that it watches, and what it is to hear of. -/
structure Watch where
  wd : Nat
  inode : Nat
  mask : Nat
  deriving DecidableEq, Repr

/-- What `inotify` has to say, as a read gives it, of the name of what was in a directory, or of the inode itself if it has none. -/
structure Notice where
  wd : Nat
  mask : Nat
  cookie : Nat := 0
  name : String := ""
  deriving DecidableEq, Repr

/-- What an inode is and holds. -/
inductive Content where
  | file (data : ByteArray)
  | directory
  | symlink (target : String)
  /-- What reads get from it, in order, and writes go to the output of the kernel. It can't seek. -/
  | console (input : ByteArray)
  /-- What a generator of this name makes when it is opened, as the files of `/proc` are: see `addGenerated`. -/
  | generated (name : String)
  /-- What has been written to a pipe, from where it hasn't been read yet, how much has been read of all that was ever written, and how
  many bytes it holds at most, which `F_SETPIPE_SZ` sets. It lets go of what is read once that is half of it. -/
  | pipe (buffer : ByteArray) (head consumed capacity : Nat)
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
  /-- A device of `/dev`: 0 is `null`, 1 `zero`, 2 `full`, 3 `random`, 6 `urandom`, and 4 `tty` and 5 `ptmx`, which opening asks of
  `Bap.Linux.Tty`. -/
  | device (kind : Nat)
  /-- Of `inotify_init`: its watches, what it has to say and hasn't been read, and the number of the next watch and of the next move
  that it pairs the two sides of. -/
  | inotify (watches : List Watch) (notices : Array Notice) (next cookies : Nat)
  /-- A queue of `mq_open`: its messages, of the highest priority first, how many it holds and how big each is at most, and of
  `mq_notify`, the process that it tells when a message comes to it empty, how, with which signal and what value. -/
  | mqueue (messages : List (Nat × ByteArray)) (capacity size : Nat) (notify : Option (Nat × Nat × Nat × Nat))

/-- A file of any kind: its number, what it holds, and its type and permissions as `st_mode` has them. -/
structure Inode where
  number : Nat
  content : Content
  mode : Nat
  details : Meta := {}

/-- An inode that was written at a time, and so changed then. -/
def Inode.written (inode : Inode) (clock : Nat) : Inode :=
  { inode with details := { inode.details with modified := clock, changed := clock } }

/-- Of a file that `memfd_create` makes, which can have seals: this is among them, which `F_GET_SEALS` doesn't say. -/
def sealable : Nat := 2 ^ 31

/-- Why the seals of a file keep `count` bytes from being written to it at `offset`, if they do: `F_SEAL_WRITE` and
`F_SEAL_FUTURE_WRITE` keep all, and `F_SEAL_GROW` what goes past its end. -/
def Inode.sealedAgainst (inode : Inode) (size offset count : Nat) : Option Nat :=
  let seals := inode.details.seals
  if seals &&& 0x18 != 0 || (seals &&& 4 != 0 && offset + count > size) then some 1 else none

/-- The most bytes that a file can have here, 1 GiB. Linux has files of up to 2^63 bytes, with nothing where nothing was written, but
a file here is all of its bytes in the memory of the host, so a program could have it make as many zeros as it liked before an offset
that it gives. This is more than programs run here have in a file, and few enough to make: what would go past it is `EFBIG`. -/
def maximumFileSize : Nat := 2 ^ 30

/-- Whether an offset that a call gives, of 64 bits, is negative, which is `EINVAL`. -/
def negativeOffset (offset : Nat) : Bool := offset ≥ 2 ^ 63

/-- Why `count` bytes can't be written to a file at `offset`, if they can't: that they would end past 2^63 bytes, which is `EINVAL`, its
seals, as `Inode.sealedAgainst` has them, or that it would be more than `maximumFileSize`. -/
def Inode.writeRefused (inode : Inode) (size offset count : Nat) : Option Nat :=
  if negativeOffset (offset + count) then some Errno.einval
  else if let some errno := inode.sealedAgainst size offset count then some errno
  else if offset + count > maximumFileSize then some Errno.efbig
  else none

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

/-- What `madvise` said of a range of a process's memory for a child of `fork`: that it is zeros there, of `MADV_WIPEONFORK`, or that it
isn't there at all, of `MADV_DONTFORK`. It is of the mapping, as Linux has it, which `munmap` ends. -/
structure ForkAdvice where
  start : Nat
  size : Nat
  wipe : Bool
  deriving DecidableEq, Repr

namespace ForkAdvice

/-- What is left of advice without `lower`..`upper`. -/
def without (advice : ForkAdvice) (lower upper : Nat) : List ForkAdvice :=
  let stop := advice.start + advice.size
  if stop ≤ lower || upper ≤ advice.start then [advice]
  else
    (if advice.start < lower then [{ advice with size := lower - advice.start }] else []) ++
    (if upper < stop then [{ advice with start := upper, size := stop - upper }] else [])

end ForkAdvice

/-! The capabilities, as Linux numbers them: a set of them is a number with the bit of each. -/

namespace Capability
def chown : Nat := 0
def dacOverride : Nat := 1
def dacReadSearch : Nat := 2
def fowner : Nat := 3
def fsetid : Nat := 4
def setgid : Nat := 6
def setuid : Nat := 7
def setpcap : Nat := 8
def sysChroot : Nat := 18
def sysAdmin : Nat := 21
def sysNice : Nat := 23
def sysResource : Nat := 24
/-- All of them, up to `CAP_CHECKPOINT_RESTORE`, the last. -/
def all : Nat := 2 ^ 41 - 1
/-- Those that go by the user of the filesystem: `CAP_CHOWN`, `CAP_DAC_OVERRIDE`, `CAP_DAC_READ_SEARCH`, `CAP_FOWNER`, `CAP_FSETID`,
`CAP_LINUX_IMMUTABLE`, `CAP_MKNOD` and `CAP_MAC_OVERRIDE`. -/
def files : Nat := 0x1f ||| 2 ^ 9 ||| 2 ^ 27 ||| 2 ^ 32
end Capability

/-- Who a process is, as `setuid` and its kin have it: of users and of groups, the real, the effective, the saved and that of the
filesystem, and the groups that it is in besides, and its capabilities: the effective ones, which it may use, the permitted ones,
which it may make effective, the inheritable ones, and those that its bounding set has, which a program that root runs gets. Everyone
starts as root, with all of them but the inheritable. -/
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
  effective : Nat := Capability.all
  permitted : Nat := Capability.all
  inheritable : Nat := 0
  bounding : Nat := Capability.all
  deriving DecidableEq, Repr

namespace Credentials

/-- Whether a process has a capability effective. -/
def capable (credentials : Credentials) (capability : Nat) : Bool := credentials.effective.testBit capability

/-- Credentials whose users `setuid` and its kin changed from those of `old`, with the capabilities that Linux leaves them: when none of
the real, effective and saved users is root any more, there are none permitted or effective, when the effective one stops being root
there are none effective, and when it becomes root, the permitted ones are effective. -/
def ofUsers (next old : Credentials) : Credentials :=
  let next := if (old.uid == 0 || old.euid == 0 || old.suid == 0) && next.uid != 0 && next.euid != 0 && next.suid != 0 then
      { next with permitted := 0, effective := 0 }
    else next
  if old.euid == 0 && next.euid != 0 then { next with effective := 0 }
  else if old.euid != 0 && next.euid == 0 then { next with effective := next.permitted }
  else next

/-- Credentials with `fsuid` as the user of the filesystem, as `setfsuid` sets it: when it stops being root, the capabilities of files
aren't effective, and when it becomes root, those that are permitted are. -/
def withFsuid (credentials : Credentials) (fsuid : Nat) : Credentials :=
  let effective :=
    if credentials.fsuid == 0 && fsuid != 0 then credentials.effective &&& (Capability.all - Capability.files)
    else if credentials.fsuid != 0 && fsuid == 0 then credentials.effective ||| (credentials.permitted &&& Capability.files)
    else credentials.effective
  { credentials with fsuid, effective }

/-- What `execve` of a program that isn't set-user-ID leaves: the saved and filesystem ids are the effective ones, and the
capabilities are recomputed: when the real or the effective user is root, those of the bounding set and the inheritable ones are
permitted, and effective too if it is the effective one; else there are none. -/
def executed (credentials : Credentials) : Credentials :=
  let permitted := if credentials.uid == 0 || credentials.euid == 0 then credentials.bounding ||| credentials.inheritable else 0
  { credentials with suid := credentials.euid, fsuid := credentials.euid, sgid := credentials.egid, fsgid := credentials.egid
                     permitted, effective := if credentials.euid == 0 then permitted else 0 }

end Credentials

/-- A directory that a process has, as its working directory or its root: its inode, and its path, which `rename` keeps up with. Once
the tree has no longer got the inode there it was removed, and the path is where it was. -/
structure Place where
  inode : Nat := 1
  path : String := "/"
  deriving DecidableEq, Repr

/-- What belongs to a process. -/
structure Process where
  descriptors : Std.HashMap Nat Descriptor := {}
  cwd : Place := {}
  umask : Nat := 0o022
  /-- Where the heap starts and where it ends now. -/
  breakStart : Nat := 0
  breakEnd : Nat := 0
  /-- What it was started with, as `/proc` says. A child has what its parent has. -/
  command : List String := []
  environment : List String := []
  /-- The file that it runs, by its path, as `/proc/PID/exe` has it. -/
  program : String := ""
  /-- The path that it was run by, as it was given, of which the last part is its name, as `/proc/PID/comm` has it. -/
  name : String := ""
  /-- The auxiliary vector that it started with, as a type and a value by turns. -/
  auxiliary : List Nat := []
  /-- What of its memory has a file behind it, which a child has too and `execve` ends. -/
  mappings : List FileMapping := []
  /-- What `madvise` said of its memory for a child, which a child of `fork` has too, but for what it left out, and `execve` ends. -/
  forkAdvice : List ForkAdvice := []
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
  /-- What `chroot` made `/` of its paths. -/
  root : Place := {}
  /-- What `membarrier` it registered for, as the bits of the commands that register. -/
  barriers : Nat := 0

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
  name : String := ""
  auxiliary : List Nat := []
  big : Bool := false
  cwd : String := "/"
  /-- What is mounted, the last first: where, of what file system, what was mounted, and with which flags of `mount`. -/
  mounts : List (String × String × String × Nat) := []
  ranges : List MappedRange := []
  breakStart : Nat := 0
  umask : Nat := 0o022
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

/-- A file system mounted at a path of the tree: what is seen there is what the tree has at `source`, which for one of its own, as
`tmpfs` is, is a directory that no name of the tree reaches, under `hiddenRoot`. -/
structure Mount where
  target : String
  source : String
  fstype : String
  /-- What `mount` was given as what it mounts, which `/proc/self/mountinfo` says. -/
  device : String
  flags : Nat
  deriving DecidableEq, Repr

/-- Where the directories of mounts of their own are, which a listing of `/` doesn't show. -/
def hiddenRoot : String := "/\x01mounts"

/-- Who a SysV object is of and who may use it, as `struct ipc_perm` has it: its key, owner, creator and mode. -/
structure IpcPerm where
  key : Nat
  uid : Nat
  gid : Nat
  cuid : Nat
  cgid : Nat
  mode : Nat
  deriving DecidableEq, Repr

/-- A segment of `shmget`: the inode that holds it, which an attachment maps, how big it is, who made it and attached or detached
last, and when, and whether `IPC_RMID` took it away, after which it lasts as long as something has it attached. -/
structure Segment where
  id : Nat
  perm : IpcPerm
  inode : Nat
  size : Nat
  cpid : Nat
  lpid : Nat := 0
  atime : Nat := 0
  dtime : Nat := 0
  ctime : Nat
  removed : Bool := false
  deriving DecidableEq, Repr

/-- A set of semaphores of `semget`: their values, the process that changed each last, and when one was changed and the set was. -/
structure SemaphoreSet where
  id : Nat
  perm : IpcPerm
  values : List Nat
  pids : List Nat
  otime : Nat := 0
  ctime : Nat
  deriving DecidableEq, Repr

/-- A queue of `msgget`: its messages, each of a type, how many bytes it holds at most, who sent and received last, and when. -/
structure MessageQueue where
  id : Nat
  perm : IpcPerm
  messages : List (Nat × ByteArray) := []
  qbytes : Nat := 16384
  stime : Nat := 0
  rtime : Nat := 0
  ctime : Nat
  lspid : Nat := 0
  lrpid : Nat := 0

/-- What SysV IPC has: segments, sets of semaphores and queues, how many of each were ever made, which numbers them, and what
`SEM_UNDO` takes back of a process when it ends, by process, set and semaphore. -/
structure Ipc where
  segments : List Segment := []
  sets : List SemaphoreSet := []
  queues : List MessageQueue := []
  made : Nat × Nat × Nat := (0, 0, 0)
  undo : List (Nat × Nat × Nat × Int) := []

/-- All that the kernel is: its files, what is open of them, its processes, what was written to the console and its clock. A socket that
is bound to a name of its own, or to an address of the Internet, has that name among the paths, which don't start with `/`. -/
structure Kernel where
  /-- From an absolute path without `.`, `..` or a trailing slash to its inode. -/
  paths : Std.HashMap String Nat := {}
  /-- How many names each inode has in the tree of `paths`, and of a directory, as many more as the directories that are in it: what
  `stat` says of its links, which this keeps as `paths` changes. An inode that has none isn't here. -/
  links : Std.HashMap Nat Nat := {}
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
  /-- How many bytes `getrandom` has given, which is where the next of them are in `randomBytes`. -/
  randomGiven : Nat := 0
  /-- What makes the generated files that aren't those of `/proc`, by name. A function can't go in a checkpoint: only the names do,
  and these are given again to go on from it. -/
  generators : Std.HashMap String Generator := {}
  /-- What is mounted, the last first. -/
  mounts : List Mount := []
  /-- What SysV IPC has. -/
  ipc : Ipc := {}

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

/-- How a path ends: in a name, in a name and a slash, or in `.` or `..`. What ends in other than a name is of a directory, as Linux has
it, and `parts` loses how it ends. -/
inductive Ending where
  | name | slash | dot | dotdot
  deriving DecidableEq

/-- How a path ends. The root ends in a name. -/
def ending (path : String) : Ending :=
  match ((path.splitOn "/").filter (· != "")).getLast? with
  | some "." => .dot
  | some ".." => .dotdot
  | some _ => if path.endsWith "/" then .slash else .name
  | none => .name

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
    links := ({} : Std.HashMap Nat Nat).insert 1 1
    inodes := ({} : Std.HashMap Nat Inode).insert 1 { number := 1, content := .directory, mode := 0o40755 } }

/-- `links` with one more name at a path of an inode, or of `more` false, one less: of the inode, and of the directory that the name is
in if the inode is a directory, as `paths` has that now. A name of a socket of its own isn't in the tree, nor does a directory where
mounts keep their own count in its directory. -/
def countName (kernel : Kernel) (path : String) (number : Nat) (more : Bool) : Kernel :=
  if !path.startsWith "/" then kernel
  else
    let change (links : Std.HashMap Nat Nat) (number : Nat) : Std.HashMap Nat Nat :=
      match links.getD number 0, more with
      | count, true => links.insert number (count + 1)
      | 0, false | 1, false => links.erase number
      | count + 1, false => links.insert number count
    let links := change kernel.links number
    let inDirectory := kernel.inodes.get? number matches some { content := .directory, .. } && path != "/" &&
      !(Path.name path).startsWith "\x01"
    { kernel with links := match if inDirectory then kernel.paths.get? (Path.parent path) else none with
      | some parent => change links parent
      | none => links }

/-- With a name at a path of an inode, in place of what was there. -/
def bindPath (kernel : Kernel) (path : String) (number : Nat) : Kernel :=
  let kernel := match kernel.paths.get? path with
    | some other => kernel.countName path other false
    | none => kernel
  { kernel.countName path number true with paths := kernel.paths.insert path number }

/-- Without the name at a path. -/
def unbindPath (kernel : Kernel) (path : String) : Kernel :=
  match kernel.paths.get? path with
  | some number => { kernel.countName path number false with paths := kernel.paths.erase path }
  | none => kernel

/-- With `links` as the names of `paths` have them, as a checkpoint leaves them out. -/
def countLinks (kernel : Kernel) : Kernel :=
  kernel.paths.fold (init := { kernel with links := {} }) fun kernel path number => kernel.countName path number true

/-- What a new inode that a process of `owner` makes has of itself: it was made now, and is of the user and the group of the process's
filesystem. -/
def madeBy (kernel : Kernel) (owner : Credentials) : Meta :=
  { accessed := kernel.clock, modified := kernel.clock, changed := kernel.clock, uid := owner.fsuid, gid := owner.fsgid }

/-- The group of a new inode in a directory that a process of `owner` makes with `mode`, and the mode that it has then: that of the
process's filesystem, but in a directory with `S_ISGID` that of the directory, and a directory made there has `S_ISGID` too. Something
else keeps `S_ISGID` with `S_IXGRP` only if one in its group makes it, or one with `CAP_FSETID`, as Linux has it. -/
def newGroup (kernel : Kernel) (directory : String) (owner : Credentials) (mode : Nat) : Nat × Nat :=
  match (kernel.paths.get? directory).bind kernel.inodes.get? with
  | some parent =>
    let gid := parent.details.gid
    if parent.mode &&& 0o2000 == 0 then (owner.fsgid, mode)
    else if mode &&& 0o170000 == 0o40000 then (gid, mode ||| 0o2000)
    else if mode &&& 0o2010 == 0o2010 && !owner.capable Capability.fsetid && gid != owner.fsgid && !owner.groups.contains gid then
      (gid, mode - 0o2000)
    else (gid, mode)
  | none => (owner.fsgid, mode)

/-- A new inode at a path, which a process of `owner` makes, as `madeBy` and `newGroup` say: root, of what is set up. -/
private def addInode (kernel : Kernel) (path : String) (content : Content) (mode : Nat) (owner : Credentials := {}) : Kernel × Nat :=
  let number := kernel.nextInode
  let (gid, mode) := kernel.newGroup (Path.parent path) owner mode
  (({ kernel with
      inodes := kernel.inodes.insert number { number, content, mode, details := { kernel.madeBy owner with gid } }
      nextInode := number + 1 }.bindPath path number), number)

/-- The path of what is open, for a directory, or of what `/proc/PID/fd/N` is of. -/
def pathOfInode (kernel : Kernel) (number : Nat) : Option String :=
  (kernel.paths.toList.find? fun entry => entry.2 == number && entry.1.startsWith "/").map (·.1)

/-- The path of a place, if it still has one. -/
def pathOf (kernel : Kernel) (place : Place) : Option String :=
  if kernel.paths.get? place.path == some place.inode then some place.path else none

/-- The name that stands for a directory that was removed, which no path that a program gives has: `resolve` finds the directory as
the last part of a path, and nothing in it. -/
def removedName (number : Nat) : String := "\x00" ++ toString number

/-- The base of relative paths in a place: its path, or once it was removed, a name in its parent that stands for it, so that nothing
is found or made in it while `..` is still its parent, as Linux has it. -/
def baseIn (kernel : Kernel) (place : Place) : String :=
  match kernel.pathOf place with
  | some path => path
  | none => Path.parent place.path ++ "/" ++ removedName place.inode

/-- The inode that a descriptor is open on, by the parts of its path in `/proc`, `proc`, `PID`, `fd` and `N`, if there is one. -/
private def inodeOfDescriptorPath (kernel : Kernel) : List String → Option Nat
  | ["proc", pid, "fd", fd] => do
    let descriptor ← (← kernel.processes.get? (← pid.toNat?)).descriptors.get? (← fd.toNat?)
    pure (← kernel.openFiles.get? descriptor.openFile).inode
  | _ => none

/-- Follows a path, and its last part if `follow`, up to 40 links as Linux does. Each part before the last must be a directory,
and the last doesn't have to be there: the result says whether it is. A link of `/proc/PID/fd` leads to what the descriptor is open on
itself, as Linux has it, whether that has a path or not: a file that was removed, or a pipe. A path that ends in a slash is of a
directory, which the link at its end is followed to, and anything else there is `ENOTDIR`; but of `exact`, for the calls that make,
remove or move what is there, which say themselves what a slash is, its last part is what is there. One that ends in `.` or `..` is of
the directory before it, which must be there. -/
def resolve (kernel : Kernel) (base path : String) (follow : Bool := true) (links : Nat := 40) (mounted : Bool := true)
    (exact : Bool := false) : Result (String × Option Nat) :=
  let ending := Path.ending path
  let slash := ending == .slash && !exact
  let follow := follow || slash
  let rec walk (done : List String) (todo : List String) : Nat → Nat → Result (String × Option Nat)
    | 0, _ => .error Errno.eloop
    | fuel + 1, links =>
      match todo with
      | [] =>
        let path := Path.ofParts done.reverse
        .ok (path, kernel.paths.get? path)
      | part :: rest =>
        let path := Path.ofParts (part :: done).reverse
        -- Where something is mounted, what is seen is what it mounted, but for the place itself when `mounted` says not.
        match if kernel.mounts.isEmpty || (rest.isEmpty && !mounted) then none else kernel.mounts.find? (·.target == path) with
        | some mount => walk (Path.parts "/" mount.source).reverse rest fuel links
        | none =>
        match kernel.paths.get? path with
        | none =>
          if !rest.isEmpty then .error Errno.enoent
          else if part.startsWith "\x00" then .ok (path, (part.drop 1).toString.toNat?)
          else .ok (path, none)
        | some number =>
          match kernel.inodes.get? number with
          | none => .error Errno.eio
          | some inode =>
            match inode.content with
            | .symlink target =>
              if rest.isEmpty && !follow then .ok (path, some number)
              else if links == 0 then .error Errno.eloop
              else match kernel.inodeOfDescriptorPath (part :: done).reverse with
                | some number =>
                  match rest, kernel.pathOfInode number, kernel.inodes.get? number with
                  | [], at_, _ => .ok (at_.getD path, some number)
                  | _, some at_, some { content := .directory, .. } => walk (Path.parts "/" at_).reverse rest fuel (links - 1)
                  | _, _, _ => .error Errno.enotdir
                | none =>
                  let from_ := if target.startsWith "/" then [] else done.reverse
                  walk [] (Path.parts (Path.ofParts from_) target ++ rest) fuel (links - 1)
            | .directory => walk (part :: done) rest fuel links
            | _ => if rest.isEmpty then .ok (path, some number) else .error Errno.enotdir
  match walk [] (Path.parts base path) (links * 256 + 4096) links with
  | .ok (path, none) => if ending == .dot || ending == .dotdot then .error Errno.enoent else .ok (path, none)
  | .ok (path, some number) =>
    if (slash || ending == .dot || ending == .dotdot) && !(kernel.inodes.get? number matches some { content := .directory, .. }) then
      .error Errno.enotdir
    else .ok (path, some number)
  | .error errno => .error errno

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
    -- What it has of itself stays: who it is of, its locks, and the rest, and it was written now.
    let details := ((kernel.inodes.get? number).map (·.details)).getD {}
    { kernel with inodes := kernel.inodes.insert number ({ number, content := .file data, mode, details : Inode }.written kernel.clock) }
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
  -- Each is counted out while all of them are there, to find the directory that it is in.
  let kernel := gone.foldl (init := kernel) fun kernel entry => kernel.countName entry.1 entry.2 false
  gone.foldl (init := kernel) fun kernel entry =>
    { kernel with
      paths := kernel.paths.erase entry.1
      links := kernel.links.erase entry.2
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
    | some inode@{ content := .file _, .. } =>
      -- What it has of itself stays, and it was written now.
      pure { kernel with inodes := kernel.inodes.insert number ({ inode with content := .file data, mode }.written kernel.clock) }
    | some { content := .directory, .. } => throw Errno.eisdir
    | _ => throw Errno.eexist
  | (found, none) => pure (addInode kernel found (.file data) mode).1

/-- A process by the id of its thread group, or one with nothing yet. -/
def process (kernel : Kernel) (group : Nat) : Process := kernel.processes.getD group {}

/-- What a process is now. -/
def setProcess (kernel : Kernel) (group : Nat) (process : Process) : Kernel :=
  { kernel with processes := kernel.processes.insert group process }

def lowestFree (descriptors : Std.HashMap Nat Descriptor) (from_ : Nat) : Nat :=
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

/-- Whether a path of the tree is within a file system of its own that is mounted read-only, which nothing changes: `EROFS`. -/
def readOnly (kernel : Kernel) (path : String) : Bool :=
  !kernel.mounts.isEmpty && kernel.mounts.any fun mount =>
    mount.flags &&& 1 != 0 && mount.source.startsWith hiddenRoot && (path == mount.source || path.startsWith (mount.source ++ "/"))

private def erofs : Nat := 30

/-- Whether something is mounted at a path of the tree, which can't be removed or moved then: `EBUSY`. -/
def mountedAt (kernel : Kernel) (path : String) : Bool := kernel.mounts.any (·.target == path)

private def ebusy : Nat := 16

/-- `open`. -/
def openPath (kernel : Kernel) (group : Nat) (base path : String) (flags mode : Nat) : Result (Kernel × Nat) := do
  if path == "" then .error Errno.enoent
  -- What `O_CREAT` makes isn't a directory, whatever is there: once the parts before are found, a slash at the end is `EISDIR`.
  if has flags oCreat && Path.ending path == .slash then
    let _ ← kernel.resolve base path (follow := false) (exact := true)
    .error Errno.eisdir
  -- What `O_CREAT` and `O_EXCL` make is the last part itself, which isn't followed if it is a link: that is there too, `EEXIST`.
  let exclusive := has flags oCreat && has flags oExcl
  let (normal, found) ← kernel.resolve base path (follow := !has flags oNofollow && !exclusive)
  let (kernel, number) ← match found with
    | some number =>
      if exclusive then .error Errno.eexist
      .ok (kernel, number)
    | none =>
      if !has flags oCreat then .error Errno.enoent
      if !parentIsDirectory kernel normal then .error Errno.enoent
      if kernel.readOnly normal then .error erofs
      let process := kernel.process group
      .ok (addInode kernel normal (.file ByteArray.empty) (0o100000 ||| (mode &&& 0o7777 &&& (0o7777 - process.umask)))
        process.credentials)
  let inode ← inodeOf kernel number
  let kernel ← match inode.content with
    | .directory =>
      if writable flags || has flags oCreat then .error Errno.eisdir
      .ok kernel
    | .symlink _ => .error Errno.eloop
    -- `Machine` opens these, with what they see, which this doesn't know.
    | .generated _ => .error Errno.eacces
    | .file _ =>
      if has flags oDirectory then .error Errno.enotdir
      -- `O_TRUNC` empties it however it is opened, to read too.
      if (writable flags || has flags oTrunc) && kernel.readOnly normal then .error erofs
      if has flags oTrunc then
        .ok { kernel with inodes := kernel.inodes.insert number ({ inode with content := .file ByteArray.empty }.written kernel.clock) }
      else .ok kernel
    | .console _ =>
      if has flags oDirectory then .error Errno.enotdir
      .ok kernel
    -- `/dev/pts/N`: `Bap.Linux.Tty` says whether it may be opened.
    | .ptySlave _ | .device _ => if has flags oDirectory then .error Errno.enotdir else .ok kernel
    -- What has no path is opened through `/proc/PID/fd/N`: a pipe to read or write it, as a FIFO is.
    | .pipe .. => if has flags oDirectory then .error Errno.enotdir else .ok kernel
    -- An anonymous inode lets no one open it.
    | .eventfd .. | .timerfd .. | .signalfd _ | .epoll _ | .inotify .. => .error Errno.eacces
    | .ptyMaster _ | .mqueue .. => .error Errno.einval
    -- What is bound to a path is connected to, not opened.
    | .socket _ => .error Errno.enxio
  let openFile := kernel.nextOpenFile
  let kernel := { kernel with
    -- What only opening had isn't kept: `O_CREAT`, `O_EXCL`, `O_NOCTTY`, `O_TRUNC` and `O_CLOEXEC`.
    openFiles := kernel.openFiles.insert openFile { inode := number, flags := flags - (flags &&& (oCreat ||| oExcl ||| 0x100 ||| oTrunc ||| oCloexec)) }
    nextOpenFile := openFile + 1 }
  .ok (kernel.addDescriptor group openFile (has flags oCloexec))

/-- What random bytes are here, the same each time, from the `start`th: as bytes, without a list of them first. -/
def randomBytes (start count : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity count
  for index in [0:count] do
    out := out.push ((start + index) * 167 + 13).toUInt8
  pure out

/-- `read`, at the offset of the file, which moves. Of a pipe, what is first in it, which goes. -/
def read (kernel : Kernel) (group fd count : Nat) : Result (Kernel × ByteArray) := do
  let (id, file) ← openFileOf kernel group fd
  if file.flags &&& 3 == 1 then .error Errno.ebadf
  let inode ← inodeOf kernel file.inode
  if let .pipe buffer head consumed capacity := inode.content then
    let bytes := buffer.extract head (head + count)
    let next := head + bytes.size
    let content := if next * 2 ≥ buffer.size then Content.pipe (buffer.extract next buffer.size) 0 (consumed + bytes.size) capacity
      else .pipe buffer next (consumed + bytes.size) capacity
    return ({ kernel with inodes := kernel.inodes.insert file.inode { inode with content } }, bytes)
  -- What a device gives: nothing of `null`, zeros of `zero` and `full`, and of `random`, bytes that are the same each time.
  if let .device kind := inode.content then
    let bytes := match kind with
      | 1 | 2 => Bap.zeroBytes count
      | 3 | 6 => randomBytes file.offset count
      | _ => ByteArray.empty
    return ({ kernel with openFiles := kernel.openFiles.insert id { file with offset := file.offset + bytes.size } }, bytes)
  let data ← match inode.content with
    | .file data | .console data => .ok data
    | .directory => .error Errno.eisdir
    | .symlink _ | .generated _ | .pipe .. | .socket _ | .eventfd .. | .timerfd .. | .signalfd _ | .epoll _ | .ptyMaster _ | .ptySlave _ | .device _ | .inotify .. | .mqueue .. => .error Errno.einval
  let bytes := readAt data file.offset count
  .ok ({ kernel with openFiles := kernel.openFiles.insert id { file with offset := file.offset + bytes.size } }, bytes)

/-- `pread`, which leaves the offset: what would end past 2^63 bytes is `EINVAL`. -/
def readFrom (kernel : Kernel) (group fd count offset : Nat) : Result ByteArray := do
  if negativeOffset (offset + count) then .error Errno.einval
  let (_, file) ← openFileOf kernel group fd
  if file.flags &&& 3 == 1 then .error Errno.ebadf
  let inode ← inodeOf kernel file.inode
  match inode.content with
  | .file data => .ok (readAt data offset count)
  | .console _ | .pipe .. | .socket _ | .eventfd .. | .timerfd .. | .signalfd _ | .epoll _ | .ptyMaster _ | .ptySlave _ | .device _ | .inotify .. | .mqueue .. => .error Errno.espipe
  | .directory => .error Errno.eisdir
  | .symlink _ | .generated _ => .error Errno.einval

/-- `write`, at the offset of the file, or at its end if it was opened to append, and to a pipe, as much as it has room for. -/
def write (kernel : Kernel) (group fd : Nat) (bytes : ByteArray) : Result (Kernel × Nat) := do
  let (id, file) ← openFileOf kernel group fd
  if !writable file.flags then .error Errno.ebadf
  let inode ← inodeOf kernel file.inode
  match inode.content with
  | .console _ => .ok ({ kernel with output := kernel.output ++ bytes }, bytes.size)
  -- `full` has no room, and the others take all of it.
  | .device 2 => .error 28
  | .device _ => .ok (kernel, bytes.size)
  | .pipe buffer head consumed capacity =>
    let bytes := bytes.extract 0 (capacity - (buffer.size - head))
    .ok ({ kernel with inodes := kernel.inodes.insert file.inode { inode with content := .pipe (buffer ++ bytes) head consumed capacity } },
      bytes.size)
  | .file data =>
    let offset := if has file.flags oAppend then data.size else file.offset
    if let some errno := inode.writeRefused data.size offset bytes.size then .error errno
    .ok ({ kernel with
      inodes := kernel.inodes.insert file.inode ({ inode with content := .file (writeAt data offset bytes) }.written kernel.clock)
      openFiles := kernel.openFiles.insert id { file with offset := offset + bytes.size } }, bytes.size)
  | .directory => .error Errno.eisdir
  -- `Machine` sends to a socket, and counts what is written to an `eventfd`.
  | .symlink _ | .generated _ | .socket _ | .eventfd .. | .timerfd .. | .signalfd _ | .epoll _ | .ptyMaster _ | .ptySlave _ | .inotify .. | .mqueue .. => .error Errno.einval

/-- `writeAt`, in the same bytes if nothing else holds them. -/
def writeInto (data : ByteArray) (offset : Nat) (bytes : ByteArray) : ByteArray :=
  let filled := if data.size < offset then data ++ Bap.zeroBytes (offset - data.size) else data
  bytes.copySlice 0 filled offset bytes.size false

/-- Why `write` of `count` bytes can't go ahead, if it can't, for `writeKnown`. -/
def writeError (kernel : Kernel) (group fd count : Nat) : Option Nat :=
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
      | some inode@{ content := .file data, .. } =>
        inode.writeRefused data.size (if has file.flags oAppend then data.size else file.offset) count
      -- What `Kernel.write` doesn't take: these have calls of their own, and the rest nothing.
      | some { content := .timerfd .., .. } | some { content := .signalfd _, .. } | some { content := .epoll _, .. }
      | some { content := .inotify .., .. } | some { content := .mqueue .., .. } | some { content := .eventfd .., .. }
      | some { content := .ptyMaster _, .. } | some { content := .ptySlave _, .. } => some Errno.einval
      | _ => none

/-- `write` for what `writeError` has nothing against, which changes all it can in place: one that takes the kernel as it is the only holder of it makes as many small
writes as it likes for the size of each, however much is already there. -/
def writeKnown (kernel : Kernel) (group fd : Nat) (bytes : ByteArray) : Kernel :=
  match kernel.openFileOf group fd with
  | .error _ => kernel
  | .ok (id, file) =>
    let number := file.inode
    -- What it is, of one look, which holds nothing of it after: the clock too is taken first, so that no function holds the kernel.
    let (isConsole, size) := match kernel.inodes.get? number with
      | some { content := .console _, .. } => (true, none)
      | some { content := .file data, .. } => (false, some data.size)
      | _ => (false, none)
    if isConsole then { kernel with output := kernel.output ++ bytes }
    else
      let offset := if has file.flags oAppend then size.getD 0 else file.offset
      let clock := kernel.clock
      { kernel with
        openFiles := if size.isSome then kernel.openFiles.insert id { file with offset := offset + bytes.size } else kernel.openFiles
        inodes := kernel.inodes.alter number (·.map fun inode =>
          match inode with
          | inode@{ content := .file data, .. } => { inode with content := .file (writeInto data offset bytes) }.written clock
          | inode@{ content := .pipe buffer head consumed capacity, .. } => { inode with content := .pipe (buffer ++ bytes) head consumed capacity }
          | other => other) }

/-- Where `pwrite` writes in a file of `size` bytes: at `offset`, or at its end if it was opened to append, as Linux has it, which
keeps that for what has come to depend on it. -/
private def pwriteOffset (file : OpenFile) (size offset : Nat) : Nat := if has file.flags oAppend then size else offset

/-- Why `pwrite` of `count` bytes at `offset` can't go ahead, if it can't, for `writeKnownAt`: only a file is written where a call says. -/
def writeAtError (kernel : Kernel) (group fd count offset : Nat) : Option Nat :=
  if negativeOffset offset then some Errno.einval else
  match kernel.openFileOf group fd with
  | .error errno => some errno
  | .ok (_, file) =>
    if !writable file.flags then some Errno.ebadf
    else
      match kernel.inodes.get? file.inode with
      | some inode@{ content := .file data, .. } => inode.writeRefused data.size (pwriteOffset file data.size offset) count
      | some { content := .directory, .. } => some Errno.eisdir
      | some { content := .symlink _, .. } | some { content := .generated _, .. } => some Errno.einval
      | some _ => some Errno.espipe
      | none => some Errno.eio

/-- `pwrite` for what `writeAtError` has nothing against, in the bytes of the file if nothing else holds them, as `writeKnown`. -/
def writeKnownAt (kernel : Kernel) (group fd : Nat) (bytes : ByteArray) (offset : Nat) : Kernel :=
  match kernel.openFileOf group fd with
  | .error _ => kernel
  | .ok (_, file) =>
    let clock := kernel.clock
    { kernel with inodes := kernel.inodes.alter file.inode (·.map fun inode =>
        match inode with
        | inode@{ content := .file data, .. } =>
          { inode with content := .file (writeInto data (pwriteOffset file data.size offset) bytes) }.written clock
        | other => other) }

/-- `pwrite`, which leaves the offset. -/
def writeTo (kernel : Kernel) (group fd : Nat) (bytes : ByteArray) (offset : Nat) : Result (Kernel × Nat) := do
  if negativeOffset offset then .error Errno.einval
  let (_, file) ← openFileOf kernel group fd
  if !writable file.flags then .error Errno.ebadf
  let inode ← inodeOf kernel file.inode
  match inode.content with
  | .file data =>
    let offset := pwriteOffset file data.size offset
    if let some errno := inode.writeRefused data.size offset bytes.size then .error errno
    .ok ({ kernel with inodes := kernel.inodes.insert file.inode ({ inode with content := .file (writeAt data offset bytes) }.written kernel.clock) },
      bytes.size)
  | .console _ | .pipe .. | .socket _ | .eventfd .. | .timerfd .. | .signalfd _ | .epoll _ | .ptyMaster _ | .ptySlave _ | .device _ | .inotify .. | .mqueue .. => .error Errno.espipe
  | .directory => .error Errno.eisdir
  | .symlink _ | .generated _ => .error Errno.einval

/-- `lseek`. A signed offset comes as `(negative, size)`. -/
def seek (kernel : Kernel) (group fd : Nat) (negative : Bool) (distance whence : Nat) : Result (Kernel × Nat) := do
  let (id, file) ← openFileOf kernel group fd
  let inode ← inodeOf kernel file.inode
  let size ← match inode.content with
    | .file data => .ok data.size
    | .directory => .ok 0
    | .console _ | .pipe .. | .socket _ | .eventfd .. | .timerfd .. | .signalfd _ | .epoll _ | .ptyMaster _ | .ptySlave _ | .device _ | .inotify .. | .mqueue .. => .error Errno.espipe
    | .symlink _ | .generated _ => .error Errno.einval
  -- `SEEK_DATA` and `SEEK_HOLE` of a file, which has no holes here: all before its end is data, and the hole is at its end, and from
  -- there on, or before its start, there is neither, `ENXIO`.
  if (whence == 3 || whence == 4) && inode.content matches .file _ then
    if negative || distance ≥ size then .error Errno.enxio
    let offset := if whence == 3 then distance else size
    return ({ kernel with openFiles := kernel.openFiles.insert id { file with offset } }, offset)
  let start ← match whence with
    | 0 => .ok 0
    | 1 => .ok file.offset
    | 2 => .ok size
    | _ => .error Errno.einval
  if negative && distance > start then .error Errno.einval
  let offset := if negative then start - distance else start + distance
  if negativeOffset offset then .error Errno.einval
  .ok ({ kernel with openFiles := kernel.openFiles.insert id { file with offset } }, offset)

/-- What a process had locked of the file of an open file, which closing any descriptor of that file lets go of. Nothing else changes. -/
def releaseLocks (kernel : Kernel) (group openFile : Nat) : Kernel :=
  match (kernel.openFiles.get? openFile).bind fun file => kernel.inodes.get? file.inode with
  | some inode =>
    if inode.details.locks.any (·.owner == .process group) then
      let locks := inode.details.locks.filter (·.owner != .process group)
      { kernel with inodes := kernel.inodes.insert inode.number { inode with details := { inode.details with locks } } }
    else kernel
  | none => kernel

/-- `close`. -/
def close (kernel : Kernel) (group fd : Nat) : Result Kernel := do
  let process := kernel.process group
  let some descriptor := process.descriptors.get? fd | .error Errno.ebadf
  .ok ((kernel.setProcess group { process with descriptors := process.descriptors.erase fd }).releaseLocks group descriptor.openFile)

/-- How many bytes a new pipe holds at most, as Linux has it: 16 pages. -/
def pipeCapacity : Nat := 65536

/-- `PIPE_BUF`: a write to a pipe of at most this many bytes goes in all at once or not at all. -/
def pipeBuf : Nat := 4096

/-- `pipe2`: a pipe, and its descriptors, to read and to write. -/
def pipe (kernel : Kernel) (group flags : Nat) : Kernel × Nat × Nat :=
  let number := kernel.nextInode
  let reading := kernel.nextOpenFile
  let writing := reading + 1
  let kept := flags &&& oNonblock
  let kernel := { kernel with
    inodes := kernel.inodes.insert number
      { number, content := .pipe ByteArray.empty 0 0 pipeCapacity, mode := 0o10600, details := kernel.madeBy (kernel.process group).credentials }
    nextInode := number + 1
    openFiles := (kernel.openFiles.insert reading { inode := number, flags := kept }).insert writing { inode := number, flags := 1 ||| kept }
    nextOpenFile := writing + 1 }
  let (kernel, readFd) := kernel.addDescriptor group reading (flags &&& oCloexec != 0)
  let (kernel, writeFd) := kernel.addDescriptor group writing (flags &&& oCloexec != 0)
  (kernel, readFd, writeFd)

/-- A descriptor of something that has no path, as `eventfd` and `epoll_create` make: on a new inode of `content`, opened to read and
write with `flags` of `O_NONBLOCK` and `O_CLOEXEC`, which `/proc/PID/fd` says is `name` if it is a file. It is of `uid` and `gid`, or
root's, as the inode that Linux has for all of what is anonymous is. -/
def addObject (kernel : Kernel) (group : Nat) (content : Content) (flags : Nat) (mode : Nat := 0o600) (seals : Nat := 0) (access : Nat := 2)
    (name : String := "") (uid : Nat := 0) (gid : Nat := 0) : Kernel × Nat :=
  let number := kernel.nextInode
  let openFile := kernel.nextOpenFile
  let clock := kernel.clock
  let kernel := { kernel with
    inodes := kernel.inodes.insert number
      { number, content, mode, details := { accessed := clock, modified := clock, changed := clock, uid, gid, seals, name } }
    nextInode := number + 1
    openFiles := kernel.openFiles.insert openFile { inode := number, flags := access ||| (flags &&& oNonblock) }
    nextOpenFile := openFile + 1 }
  kernel.addDescriptor group openFile (flags &&& oCloexec != 0)

/-- What a descriptor is on, of the open file and the inode. -/
def objectOf (kernel : Kernel) (group fd : Nat) : Result (Nat × OpenFile × Inode) := do
  let (_, file) ← openFileOf kernel group fd
  pure (file.inode, file, ← inodeOf kernel file.inode)

/-- A file of a device at a path, with the directories that it needs, which `Bap.Linux.Tty` and the devices make as they are asked for. -/
def addDevice (kernel : Kernel) (path : String) (content : Content) (mode : Nat) (owner : Credentials := {}) : Kernel × Nat :=
  let kernel := addDirectories kernel (Path.parent path)
  addInode kernel path content mode owner

/-- What an inode holds now, which is one more change of it. -/
def setContent (kernel : Kernel) (number : Nat) (content : Content) : Kernel :=
  match kernel.inodes.get? number with
  | some inode =>
    { kernel with inodes := kernel.inodes.insert number { inode with content, details.changes := inode.details.changes + 1 } }
  | none => kernel

/-- The inode of a descriptor, if that is a pipe. -/
def pipeOf (kernel : Kernel) (group fd : Nat) : Option Nat :=
  match kernel.openFileOf group fd with
  | .ok (_, file) =>
    match kernel.inodes.get? file.inode with
    | some { content := .pipe .., .. } => some file.inode
    | _ => none
  | .error _ => none

/-- The open files that these processes hold, which are open yet as Linux has it: those of their descriptors, and those that a message
waiting in a socket that they hold hands over, or in a connection that such a socket listens with and has to accept, as far as that goes.
A file that is only in a message to a socket that nothing holds is closed, as Linux closes it with that socket. -/
def heldFiles (kernel : Kernel) (groups : List Nat) : Std.HashSet Nat := Id.run do
  let mut files : Std.HashSet Nat := {}
  let mut sockets : Std.HashSet Nat := {}
  let mut fileWork : List Nat := groups.flatMap fun group => (kernel.process group).descriptors.toList.map (·.2.openFile)
  let mut socketWork : List Nat := []
  -- As far as what is held holds more, each once.
  for _ in [0:kernel.openFiles.size + kernel.inodes.size + 1] do
    if fileWork.isEmpty && socketWork.isEmpty then break
    for id in fileWork do
      if !files.contains id then
        files := files.insert id
        if let some file := kernel.openFiles.get? id then socketWork := file.inode :: socketWork
    fileWork := []
    let pending := socketWork
    socketWork := []
    for number in pending do
      if sockets.contains number then continue
      sockets := sockets.insert number
      if let some { content := .socket socket, .. } := kernel.inodes.get? number then
        socketWork := socket.pending ++ socketWork
        for message in socket.incoming do fileWork := message.rights ++ fileWork
  pure files

/-- Whether one of these processes holds an open file of an inode, as `heldFiles` has it, and that opened to write, or not. -/
def pipeHeld (kernel : Kernel) (number : Nat) (groups : List Nat) (toWrite : Bool) : Bool :=
  (kernel.heldFiles groups).fold (init := false) fun found id =>
    found || (kernel.openFiles.get? id).any fun file => file.inode == number && writable file.flags == toWrite

/-- Whether one of these processes holds an open file of an inode, as `heldFiles` has it. -/
def inodeHeld (kernel : Kernel) (groups : List Nat) (number : Nat) : Bool :=
  (kernel.heldFiles groups).fold (init := false) fun found id => found || (kernel.openFiles.get? id).any (·.inode == number)

/-- Whether a descriptor was opened not to wait. -/
def nonblocking (kernel : Kernel) (group fd : Nat) : Bool :=
  match kernel.openFileOf group fd with
  | .ok (_, file) => file.flags &&& oNonblock != 0
  | .error _ => false

/-- How much a pipe has to read. -/
def pipeWaiting (kernel : Kernel) (number : Nat) : Nat :=
  match kernel.inodes.get? number with
  | some { content := .pipe buffer head _ _, .. } => buffer.size - head
  | _ => 0

/-- How much more a pipe has room for. -/
def pipeRoom (kernel : Kernel) (number : Nat) : Nat :=
  match kernel.inodes.get? number with
  | some { content := .pipe buffer head _ capacity, .. } => capacity - (buffer.size - head)
  | _ => 0

/-- `fcntl` with `F_GETPIPE_SZ`: how many bytes the pipe of a descriptor holds at most. What isn't a pipe is `EBADF`. -/
def pipeSize (kernel : Kernel) (group fd : Nat) : Result Nat := do
  let (_, file) ← openFileOf kernel group fd
  match (← inodeOf kernel file.inode).content with
  | .pipe _ _ _ capacity => .ok capacity
  | _ => .error Errno.ebadf

/-- `fcntl` with `F_SETPIPE_SZ`: the pipe of a descriptor holds at most `size` bytes, made a power of two of pages, as Linux has it, and
gives that. More than 2^31 is `EINVAL`, more than `/proc/sys/fs/pipe-max-size`, 1 MiB, `EPERM` without `CAP_SYS_RESOURCE`, and less than
what it holds `EBUSY`. -/
def setPipeSize (kernel : Kernel) (group fd size : Nat) (privileged : Bool) : Result (Kernel × Nat) := do
  let (_, file) ← openFileOf kernel group fd
  let inode ← inodeOf kernel file.inode
  let .pipe buffer head consumed _ := inode.content | .error Errno.ebadf
  let size := size % 2 ^ 32
  if size > 2 ^ 31 then .error Errno.einval
  let size := (max size 4096).nextPowerOfTwo
  if size > 1048576 && !privileged then .error Errno.eperm
  if buffer.size - head > size then .error ebusy
  .ok ({ kernel with inodes := kernel.inodes.insert file.inode { inode with content := .pipe buffer head consumed size } }, size)

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
    -- Of itself, it is as it was.
    if fd == target then return (kernel, target)
    let next := kernel.setProcess group
      { process with descriptors := process.descriptors.insert target { openFile := descriptor.openFile, closeOnExec } }
    -- What was there is closed, with what the process had locked of its file.
    match process.descriptors.get? target with
    | some replaced => .ok (next.releaseLocks group replaced.openFile, target)
    | none => .ok (next, target)

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
  /-- Of a device, its major and minor numbers. -/
  device : Nat × Nat := (0, 0)
  deriving DecidableEq, Repr

/-- The major and minor numbers of a device, as Linux has them: `null`, `zero`, `full`, `random` and `urandom` are of 1, the console,
`tty` and `ptmx` of 5, and a slave of a pseudo-terminal of 136, by its number. -/
private def deviceOf (kernel : Kernel) : Content → Nat × Nat
  | .device kind => match kind with
    | 0 => (1, 3)
    | 1 => (1, 5)
    | 2 => (1, 7)
    | 3 => (1, 8)
    | 6 => (1, 9)
    | 4 => (5, 0)
    | _ => (5, 2)
  | .console _ => (5, 1)
  | .ptyMaster _ => (5, 2)
  | .ptySlave master => match kernel.inodes.get? master with
    | some { content := .ptyMaster terminal, .. } => (136, terminal.index)
    | _ => (136, 0)
  | _ => (0, 0)

/-- What `stat` says of an inode. Its links are its names, as `links` counts them; a directory has one more, for itself, unless it was
removed; and what isn't a file, a directory or a symbolic link has one, as Linux has it, with a name or without. -/
private def statOf (kernel : Kernel) (inode : Inode) : Stat :=
  let names := kernel.links.getD inode.number 0
  let (size, links) := match inode.content with
    | .file data => (data.size, names)
    | .directory => (4096, if names == 0 then 0 else names + 1)
    | .symlink target => (target.utf8ByteSize, names)
    | .console _ | .generated _ | .pipe .. | .socket _ | .eventfd .. | .timerfd .. | .signalfd _ | .epoll _ | .ptyMaster _ | .ptySlave _ | .device _ | .inotify .. | .mqueue .. => (0, 1)
  { inode := inode.number, mode := inode.mode, size, links, accessed := inode.details.accessed, modified := inode.details.modified
    changed := inode.details.changed, uid := inode.details.uid, gid := inode.details.gid, device := kernel.deviceOf inode.content }

/-- `stat` and `lstat`. -/
def statPath (kernel : Kernel) (base path : String) (follow : Bool := true) : Result Stat := do
  if path == "" then .error Errno.enoent
  let (_, found) ← kernel.resolve base path follow
  match found with
  | none => .error Errno.enoent
  | some number => .ok (statOf kernel (← inodeOf kernel number))

/-- Whether a process may read, write and run an inode, as `want` asks of each with 4, 2 and 1, by the user and the group that it goes
by on files, or of `real`, its real ones, as `access` has it: by the bits of the owner if it is that user, else by those of the group if
it is in that, else by those of everyone. With `CAP_DAC_OVERRIDE` it may read and write anything, search any directory and run what
anyone may run, and with `CAP_DAC_READ_SEARCH` read anything and search any directory. Of its real ones, its capabilities are those
permitted if that user is root, and none else. -/
def permits (inode : Inode) (credentials : Credentials) (real : Bool) (want : Nat) : Bool :=
  let (uid, gid) := if real then (credentials.uid, credentials.gid) else (credentials.fsuid, credentials.fsgid)
  let capabilities := if !real then credentials.effective else if uid == 0 then credentials.permitted else 0
  let directory := inode.content matches .directory
  let shift := if uid == inode.details.uid then 6
    else if gid == inode.details.gid || credentials.groups.contains inode.details.gid then 3
    else 0
  (inode.mode >>> shift) &&& want == want ||
    capabilities.testBit Capability.dacOverride && (want &&& 1 == 0 || directory || inode.mode &&& 0o111 != 0) ||
    capabilities.testBit Capability.dacReadSearch && want &&& 2 == 0 && (want &&& 1 == 0 || directory)

/-- Whether a process may search each directory that a path of the tree is in, as `permits` has it, which it has to to find what is
there. -/
def searchable (kernel : Kernel) (credentials : Credentials) (real : Bool) (path : String) : Bool :=
  let parts := Path.parts "/" path
  (List.range parts.length).all fun count =>
    match (kernel.paths.get? (Path.ofParts (parts.take count))).bind kernel.inodes.get? with
    | some inode => permits inode credentials real 1
    | none => true

/-- `access`, `faccessat` and `faccessat2` of a process: that a path is there, of a `mode` of 0, or that the process may read, write and
run it, as `mode` asks of each with `R_OK`, `W_OK` and `X_OK`, by its real user and group, or of `effective`, those that it goes by on
files, and of the link at its end itself unless `follow`. What is in a directory that it may not search is `EACCES`, and to write what
is on a read-only mount `EROFS`. -/
def accessPath (kernel : Kernel) (group : Nat) (base path : String) (mode : Nat) (follow effective : Bool) : Result Unit := do
  let credentials := (kernel.process group).credentials
  let (normal, found) ← kernel.resolve base path follow
  if !kernel.searchable credentials (!effective) normal then .error Errno.eacces
  let some number := found | .error Errno.enoent
  let inode ← inodeOf kernel number
  let stored := match inode.content with
    | .file _ | .directory | .symlink _ => true
    | _ => false
  if mode &&& 2 != 0 && stored && kernel.readOnly normal then .error erofs
  if !permits inode credentials (!effective) mode then .error Errno.eacces

/-- What a file holds that `execve` of a process runs, or runs a program with: one that the process may run, in directories that it may
search. Anything else is `EACCES`. -/
def executable (kernel : Kernel) (group : Nat) (path : String) : Result ByteArray := do
  let credentials := (kernel.process group).credentials
  let (normal, found) ← kernel.resolve "/" path
  if !kernel.searchable credentials false normal then .error Errno.eacces
  let some number := found | .error Errno.enoent
  let inode ← inodeOf kernel number
  match inode.content with
  | .file data => if permits inode credentials false 1 then .ok data else .error Errno.eacces
  | _ => .error Errno.eacces

/-- `fstat`. -/
def statDescriptor (kernel : Kernel) (group fd : Nat) : Result Stat := do
  let (_, file) ← openFileOf kernel group fd
  .ok (statOf kernel (← inodeOf kernel file.inode))

/-- The base of the paths that a process gives relative to its working directory. -/
def cwdOf (kernel : Kernel) (group : Nat) : String := kernel.baseIn (kernel.process group).cwd

/-- The base that a path of the `*at` calls is relative to: the working directory for `AT_FDCWD`, or that directory. -/
def baseOf (kernel : Kernel) (group directory : Nat) (atCwd : Bool) : Result String := do
  if atCwd then .ok (kernel.cwdOf group)
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
    -- A name of a socket of its own isn't in a directory, nor is where mounts keep their own.
    if entry.1.startsWith "/" && parts.length == inside.length + 1 && parts.take inside.length == inside &&
        !(parts.getLast?.getD "").startsWith "\x01" then
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
  let (normal, found) ← kernel.resolve base path (follow := false) (exact := true)
  if found.isSome then .error Errno.eexist
  if !parentIsDirectory kernel normal then .error Errno.enoent
  if kernel.readOnly normal then .error erofs
  let process := kernel.process group
  .ok (addInode kernel normal .directory (0o40000 ||| (mode &&& 0o7777 &&& (0o7777 - process.umask))) process.credentials).1

/-- `unlink`, and `rmdir` with `directory`. What is open stays open: its inode is still there. A slash at the end is of a directory,
and the link that it may be isn't followed: `ENOTDIR` of anything else. Of a path that ends in `.`, `rmdir` is `EINVAL`, and in `..`,
`ENOTEMPTY`, and `unlink` of either `EISDIR`. -/
def remove (kernel : Kernel) (base path : String) (directory : Bool) : Result Kernel := do
  let (normal, found) ← kernel.resolve base path (follow := false) (mounted := false) (exact := true)
  match found with
  | none => .error Errno.enoent
  | some number =>
    match Path.ending path, directory with
    | .dot, true => .error Errno.einval
    | .dotdot, true => .error Errno.enotempty
    | .dot, false | .dotdot, false => .error Errno.eisdir
    | _, _ => pure ()
    if kernel.mountedAt normal then .error ebusy
    let inode ← inodeOf kernel number
    match inode.content, directory with
    | .directory, true =>
      if normal == "/" then .error Errno.eperm
      if !(children kernel normal).isEmpty then .error Errno.enotempty
    | .directory, false => .error Errno.eisdir
    | _, true => .error Errno.enotdir
    | _, false => if Path.ending path == .slash then .error Errno.enotdir
    if kernel.readOnly normal then .error erofs
    .ok { kernel.unbindPath normal with
      inodes := kernel.inodes.insert number { inode with details := { inode.details with name := normal ++ " (deleted)" } } }

/-- The working directories and roots of the processes, after `move` gave the paths of the tree new ones: those that were there are
where they were moved to. -/
def movePlaces (kernel : Kernel) (move : String → String) : Kernel :=
  let moved (place : Place) : Place :=
    if kernel.paths.get? place.path == some place.inode then { place with path := move place.path } else place
  { kernel with processes := kernel.processes.map fun _ process => { process with cwd := moved process.cwd, root := moved process.root } }

/-- `rename`: what was at the target is replaced, and all under a directory moves with it. Neither path may end in `.` or `..`,
which is `EBUSY`, and of a slash at the end of either, what moves must be a directory, which is `ENOTDIR` otherwise. -/
def rename (kernel : Kernel) (base source target : String) : Result Kernel := do
  let (from_, found) ← kernel.resolve base source (follow := false) (mounted := false) (exact := true)
  let (to_, existing) ← kernel.resolve base target (follow := false) (mounted := false) (exact := true)
  let dots (path : String) : Bool := Path.ending path matches .dot | .dotdot
  if dots source || dots target then .error ebusy
  let some number := found | .error Errno.enoent
  if (Path.ending source == .slash || Path.ending target == .slash) && !((← inodeOf kernel number).content matches .directory) then
    .error Errno.enotdir
  if !parentIsDirectory kernel to_ then .error Errno.enoent
  -- Two names of the same file stay as they are.
  if from_ == to_ || existing == some number then return kernel
  if kernel.mountedAt from_ || kernel.mountedAt to_ then .error ebusy
  if (to_ ++ "/").startsWith (from_ ++ "/") then .error Errno.einval
  if let some other := existing then
    let isDirectory (number : Nat) : Result Bool := do pure ((← inodeOf kernel number).content matches .directory)
    match ← isDirectory number, ← isDirectory other with
    | true, false => .error Errno.enotdir
    | false, true => .error Errno.eisdir
    | true, true => if !(children kernel to_).isEmpty then .error Errno.enotempty
    | false, false => pure ()
  if kernel.readOnly from_ || kernel.readOnly to_ then .error erofs
  -- What isn't a directory has nothing under it: its own path is all that moves.
  if !((← inodeOf kernel number).content matches .directory) then
    return (kernel.unbindPath from_).bindPath to_ number
  let move (path : String) : String :=
    if path == from_ then to_
    else if path.startsWith (from_ ++ "/") then to_ ++ (path.drop from_.length).toString
    else path
  let moved := kernel.paths.toList.foldl (init := kernel.paths.erase to_) fun paths entry =>
    if entry.1 == from_ || entry.1.startsWith (from_ ++ "/") then (paths.erase entry.1).insert (move entry.1) entry.2
    else paths
  -- Of all that moves, only the directory itself changes what is counted: it leaves one directory for another, in place of what was there.
  let kernel := match existing with
    | some other => kernel.countName to_ other false
    | none => kernel
  .ok { ((kernel.countName from_ number false).countName to_ number true).movePlaces move with paths := moved }

/-- Another path of an inode, as `linkat` of `AT_EMPTY_PATH` gives one to what a descriptor is open on. -/
def linkInode (kernel : Kernel) (number : Nat) (base target : String) : Result Kernel := do
  let inode ← inodeOf kernel number
  if let .directory := inode.content then .error Errno.eperm
  let (normal, existing) ← kernel.resolve base target (follow := false) (mounted := false) (exact := true)
  if existing.isSome then .error Errno.eexist
  if Path.ending target == .slash then .error Errno.enoent
  if !parentIsDirectory kernel normal then .error Errno.enoent
  if kernel.readOnly normal then .error erofs
  -- A file that has no name gets none, unless it is one of `O_TMPFILE` that may.
  if inode.content matches .file _ && kernel.links.getD number 0 == 0 && !inode.details.linkable then .error Errno.enoent
  .ok { kernel.bindPath normal number with
    inodes := kernel.inodes.insert number { inode with details := { inode.details with changed := kernel.clock, linkable := false } } }

/-- `link`: another path of the inode of `source`, which isn't a directory, followed through a link at its end if `follow`. -/
def link (kernel : Kernel) (base source target : String) (follow : Bool) : Result Kernel := do
  let (_, found) ← kernel.resolve base source (follow := follow)
  let some number := found | .error Errno.enoent
  kernel.linkInode number base target

/-- `renameat2`: of `RENAME_NOREPLACE`, not over what is there, and of `RENAME_EXCHANGE`, the two trade places, with all under them.
A flag that there isn't, past `RENAME_WHITEOUT`, is `EINVAL`. -/
def renameWith (kernel : Kernel) (base source target : String) (flags : Nat) : Result Kernel := do
  if flags ≥ 8 || flags &&& 3 == 3 || flags &&& 4 != 0 && flags &&& 2 != 0 then .error Errno.einval
  let (from_, found) ← kernel.resolve base source (follow := false) (mounted := false) (exact := true)
  let some number := found | .error Errno.enoent
  let (to_, existing) ← kernel.resolve base target (follow := false) (mounted := false) (exact := true)
  if flags &&& 1 != 0 && existing.isSome then .error Errno.eexist
  if flags &&& 2 == 0 then return ← kernel.rename base source target
  if kernel.mountedAt from_ || kernel.mountedAt to_ then .error ebusy
  let some other := existing | .error Errno.enoent
  if (to_ ++ "/").startsWith (from_ ++ "/") || (from_ ++ "/").startsWith (to_ ++ "/") then .error Errno.einval
  if kernel.readOnly from_ || kernel.readOnly to_ then .error erofs
  let swap (path : String) : String :=
    if path == from_ then to_ else if path == to_ then from_
    else if path.startsWith (from_ ++ "/") then to_ ++ (path.drop from_.length).toString
    else if path.startsWith (to_ ++ "/") then from_ ++ (path.drop to_.length).toString
    else path
  let kernel := (((kernel.countName from_ number false).countName to_ other false).countName from_ other true).countName to_ number true
  .ok { kernel.movePlaces swap with paths := kernel.paths.fold (init := {}) fun paths path number => paths.insert (swap path) number }

/-- The devices of `/dev` and what is around them: `null`, `zero`, `full`, `random`, `urandom`, `tty` and `ptmx`, `console` for the
console if there is one, the directories `pts` and `shm`, and `stdin`, `stdout`, `stderr` and `fd` of `/proc/self/fd`. Nothing replaces
what is already there. -/
def installDevices (kernel : Kernel) : Kernel :=
  let kernel := [("/dev/null", 0), ("/dev/zero", 1), ("/dev/full", 2), ("/dev/random", 3), ("/dev/urandom", 6), ("/dev/tty", 4),
      ("/dev/ptmx", 5)].foldl (init := kernel) fun kernel (path, kind) =>
    if kernel.paths.contains path then kernel else (addInode (addDirectories kernel "/dev") path (.device kind) 0o20666).1
  let kernel := addDirectories (addDirectories kernel "/dev/pts") "/dev/shm"
  let kernel := match kernel.inodes.toList.find? (·.2.content matches .console _) with
    | some (number, _) => if kernel.paths.contains "/dev/console" then kernel else kernel.bindPath "/dev/console" number
    | none => kernel
  [("/dev/stdin", "/proc/self/fd/0"), ("/dev/stdout", "/proc/self/fd/1"), ("/dev/stderr", "/proc/self/fd/2"),
    ("/dev/fd", "/proc/self/fd")].foldl (init := kernel) fun kernel (path, target) =>
    if kernel.paths.contains path then kernel else kernel.addSymlink path target

/-- `symlink`, to a target that is something: an empty one is `ENOENT`, as an empty path is. -/
def symlink (kernel : Kernel) (group : Nat) (base target path : String) : Result Kernel := do
  if target.isEmpty then .error Errno.enoent
  let (normal, found) ← kernel.resolve base path (follow := false) (exact := true)
  if found.isSome then .error Errno.eexist
  if Path.ending path == .slash then .error Errno.enoent
  if !parentIsDirectory kernel normal then .error Errno.enoent
  if kernel.readOnly normal then .error erofs
  .ok (addInode kernel normal (.symlink target) 0o120777 (kernel.process group).credentials).1

/-- `readlink`. -/
def readlink (kernel : Kernel) (base path : String) : Result String := do
  let (_, found) ← kernel.resolve base path (follow := false)
  match found with
  | none => .error Errno.enoent
  | some number =>
    match (← inodeOf kernel number).content with
    | .symlink target => .ok target
    | _ => .error Errno.einval

/-- A path that a process gives, as the tree has it, with the base that a relative one is from: one from `/` is from its root, and `..`
of its root stays there, as long as `base` is within it. -/
def pathIn (kernel : Kernel) (group : Nat) (base path : String) : String × String :=
  let root := kernel.baseIn (kernel.process group).root
  if root == "/" then (base, path)
  else if path.startsWith "/" then
    -- Within the root, and ending as it did.
    let ending := match Path.ending path with | .slash => "/" | .dot => "/." | _ => ""
    ("/", root ++ Path.ofParts (Path.parts "/" path) ++ ending)
  else
    let inside (at_ : String) : Bool := at_ == root || at_.startsWith (root ++ "/")
    if inside base && !inside (Path.ofParts (Path.parts base path)) then ("/", root) else (base, path)

/-- A path of the tree as a process sees it: within a mount of its own, from where that is mounted, and from its root. -/
def shownPath (kernel : Kernel) (group : Nat) (path : String) : String :=
  let within (path prefix_ : String) : Bool := path == prefix_ || path.startsWith (prefix_ ++ "/")
  let mounted (path : String) : String := kernel.mounts.length.fold (init := path) fun _ _ path =>
    match kernel.mounts.find? fun mount => mount.source.startsWith hiddenRoot && within path mount.source with
    | some mount => Path.ofParts (Path.parts "/" (mount.target ++ "/" ++ (path.drop mount.source.length).toString))
    | none => path
  let path := mounted path
  let root := mounted (kernel.baseIn (kernel.process group).root)
  if root == "/" || !within path root then path else Path.ofParts (Path.parts "/" (path.drop root.length).toString)

/-- `mount` of a file system of `fstype` at `target`, or with `MS_BIND`, of what `source` is, or with `MS_REMOUNT`, `MS_MOVE` and those
of how mounts are shared, of a mount that is there. A file system of its own is an empty directory: `proc`, `sysfs` and `devtmpfs`
are what the tree has of them. -/
def mount (kernel : Kernel) (group : Nat) (base source target fstype : String) (flags : Nat) : Result Kernel := do
  if !(kernel.process group).credentials.capable Capability.sysAdmin then .error Errno.eperm
  let (normal, found) ← kernel.resolve base target (mounted := false)
  let some number := found | .error Errno.enoent
  let here := kernel.mounts.find? (·.target == normal)
  -- `MS_REMOUNT`, and `MS_UNBINDABLE`, `MS_PRIVATE`, `MS_SLAVE` and `MS_SHARED`, are of what is mounted there, as `/` is.
  if flags &&& 32 != 0 || flags &&& 0x1e0000 != 0 then
    if here.isNone && normal != "/" then .error Errno.einval
    if flags &&& 32 == 0 then return kernel
    return { kernel with mounts := kernel.mounts.map fun mount => if some mount == here then { mount with flags } else mount }
  -- `MS_MOVE`.
  if flags &&& 8192 != 0 then
    let (from_, _) ← kernel.resolve base source (mounted := false)
    let some moving := kernel.mounts.find? (·.target == from_) | .error Errno.einval
    return { kernel with mounts := kernel.mounts.map fun mount => if mount == moving then { mount with target := normal } else mount }
  let isDirectory (inode : Inode) : Bool := inode matches { content := .directory, .. }
  let inode ← inodeOf kernel number
  -- `MS_BIND`, of a directory on a directory or of anything else on anything else.
  if flags &&& 4096 != 0 then
    let (from_, found) ← kernel.resolve base source
    let some other := found | .error Errno.enoent
    if isDirectory (← inodeOf kernel other) != isDirectory inode then .error Errno.enotdir
    return { kernel with mounts := { target := normal, source := from_, fstype := "none", device := source, flags } :: kernel.mounts }
  if !isDirectory inode then .error Errno.enotdir
  let tree := match fstype with
    | "proc" => some "/proc"
    | "sysfs" => some "/sys"
    | "devtmpfs" => some "/dev"
    | _ => none
  let ownKinds := ["tmpfs", "ramfs", "mqueue", "devpts", "cgroup", "cgroup2", "debugfs", "tracefs", "securityfs", "bpf", "hugetlbfs",
    "fusectl", "configfs", "pstore", "binfmt_misc", "autofs"]
  if tree.isNone && !ownKinds.contains fstype then .error 19
  let (kernel, from_) := match tree with
    | some path => if kernel.paths.contains path then (kernel, path) else (addDirectories kernel path, path)
    | none =>
      let hidden := hiddenRoot ++ "/" ++ toString kernel.nextInode
      let kernel := addDirectories kernel hiddenRoot
      ((addInode kernel hidden .directory (if fstype == "tmpfs" then 0o41777 else 0o40755)).1, hidden)
  .ok { kernel with mounts := { target := normal, source := from_, fstype, device := source, flags } :: kernel.mounts }

/-- `umount2`: what was mounted last at `target` isn't. What a file system of its own had is gone once nothing mounts it. -/
def unmount (kernel : Kernel) (group : Nat) (base target : String) (flags : Nat) : Result Kernel := do
  if !(kernel.process group).credentials.capable Capability.sysAdmin then .error Errno.eperm
  if flags ≥ 16 then .error Errno.einval
  let (normal, _) ← kernel.resolve base target (follow := flags &&& 8 == 0) (mounted := false)
  let some mount := kernel.mounts.find? (·.target == normal) | .error Errno.einval
  let mounts := kernel.mounts.erase mount
  if !mount.source.startsWith hiddenRoot || mounts.any (·.source == mount.source) then return { kernel with mounts }
  let within (path : String) : Bool := path == mount.source || path.startsWith (mount.source ++ "/")
  -- What a process is in keeps it, unless `MNT_DETACH` lets it go later, which here is now.
  if flags &&& 2 == 0 && kernel.processes.fold (fun busy _ process => busy || (!process.ended && (within process.cwd.path || within process.root.path))) false then
    .error 16
  let kernel := kernel.paths.fold (init := kernel) fun kernel path number =>
    if within path then kernel.countName path number false else kernel
  .ok { kernel with mounts, paths := kernel.paths.filter fun path _ => !within path }

/-- `chroot`: what a process has as `/` is a directory of the tree. -/
def chroot (kernel : Kernel) (group : Nat) (base path : String) : Result Kernel := do
  let process := kernel.process group
  if !process.credentials.capable Capability.sysChroot then .error Errno.eperm
  let (normal, found) ← kernel.resolve base path
  let some number := found | .error Errno.enoent
  let .directory := (← inodeOf kernel number).content | .error Errno.enotdir
  .ok (kernel.setProcess group { process with root := { inode := number, path := normal } })

/-- `pivot_root`: what is mounted at `newRoot` is `/` of the processes whose `/` was the tree's, and in their working directory if they
were there, and what was `/` is seen at `putOld`, which is within it. -/
def pivotRoot (kernel : Kernel) (group : Nat) (base newRoot putOld : String) : Result Kernel := do
  let process := kernel.process group
  if !process.credentials.capable Capability.sysAdmin then .error Errno.eperm
  if process.root != {} then .error Errno.einval
  let (target, found) ← kernel.resolve base newRoot (mounted := false)
  let some targetInode := found | .error Errno.enoent
  let some mount := kernel.mounts.find? (·.target == target) | .error Errno.einval
  let (old, found) ← kernel.resolve base putOld (mounted := false)
  let some number := found | .error Errno.enoent
  let .directory := (← inodeOf kernel number).content | .error Errno.enotdir
  if !(old == mount.source || old.startsWith (mount.source ++ "/")) then .error Errno.einval
  let kernel := { kernel with mounts := { target := old, source := "/", fstype := "rootfs", device := "rootfs", flags := 0 } :: kernel.mounts }
  .ok { kernel with processes := kernel.processes.map fun _ other =>
    if other.root != {} then other
    else
      let root : Place := { inode := targetInode, path := target }
      { other with root, cwd := if other.cwd == {} then root else other.cwd } }

/-- `chdir`. -/
def chdir (kernel : Kernel) (group : Nat) (path : String) : Result Kernel := do
  let (normal, found) ← kernel.resolve (kernel.cwdOf group) path
  match found with
  | none => .error Errno.enoent
  | some number =>
    match (← inodeOf kernel number).content with
    | .directory => .ok (kernel.setProcess group { kernel.process group with cwd := { inode := number, path := normal } })
    | _ => .error Errno.enotdir

/-- `fchdir`: into the directory that a descriptor has open, wherever it is now, or if it was removed, where it was. -/
def fchdir (kernel : Kernel) (group fd : Nat) : Result Kernel := do
  let (_, file) ← openFileOf kernel group fd
  let inode ← inodeOf kernel file.inode
  let .directory := inode.content | .error Errno.enotdir
  let path := (kernel.pathOfInode file.inode).getD (inode.details.name.dropEnd " (deleted)".length).toString
  .ok (kernel.setProcess group { kernel.process group with cwd := { inode := file.inode, path } })

/-- `truncate` of a file at its inode: cut, or filled with zeros up to `maximumFileSize` at most. -/
def truncateInode (kernel : Kernel) (number size : Nat) : Result Kernel := do
  let inode ← inodeOf kernel number
  match inode.content with
  | .file data =>
    -- `F_SEAL_SHRINK` and `F_SEAL_GROW`.
    if inode.details.seals &&& (if size < data.size then 2 else if size > data.size then 4 else 0) != 0 then .error Errno.eperm
    if size > maximumFileSize then .error Errno.efbig
    let data := if size ≤ data.size then data.extract 0 size
      else data ++ Bap.zeroBytes (size - data.size)
    .ok { kernel with inodes := kernel.inodes.insert number ({ inode with content := .file data }.written kernel.clock) }
  | .directory => .error Errno.eisdir
  | _ => .error Errno.einval

/-- `ftruncate`. -/
def truncateDescriptor (kernel : Kernel) (group fd size : Nat) : Result Kernel := do
  if negativeOffset size then .error Errno.einval
  let (_, file) ← openFileOf kernel group fd
  if !writable file.flags then .error Errno.einval
  kernel.truncateInode file.inode size

/-- `fallocate`, of `mode` `FALLOC_FL_KEEP_SIZE` and `FALLOC_FL_PUNCH_HOLE`, which are all that tmpfs has: as there is no disk to have
room on, a file grows to the end of what it is given room for, with zeros, unless it keeps its size, and a hole is zeros in what of it
the file has. Its other modes are `EOPNOTSUPP`, and what isn't a file is `ESPIPE` of a pipe and otherwise `ENODEV`. -/
def allocate (kernel : Kernel) (group fd mode offset size : Nat) : Result Kernel := do
  let (_, file) ← openFileOf kernel group fd
  if negativeOffset offset || size == 0 || negativeOffset size then .error Errno.einval
  -- A hole has to keep the size.
  if mode > 3 || mode == 2 then .error Errno.eopnotsupp
  if !writable file.flags then .error Errno.ebadf
  let inode ← inodeOf kernel file.inode
  match inode.content with
  | .file data =>
    if offset + size > maximumFileSize then .error Errno.efbig
    if mode == 3 then
      if let some errno := inode.sealedAgainst data.size offset 0 then .error errno
      let stop := min (offset + size) data.size
      if stop ≤ offset then return kernel
      let punched := { inode with content := .file (writeAt data offset (Bap.zeroBytes (stop - offset))) }.written kernel.clock
      .ok { kernel with inodes := kernel.inodes.insert file.inode punched }
    -- `F_SEAL_GROW` holds even of room that keeps the size.
    else if inode.details.seals &&& 4 != 0 && offset + size > data.size then .error Errno.eperm
    else if mode == 0 && offset + size > data.size then kernel.truncateInode file.inode (offset + size)
    else .ok kernel
  | .pipe .. => .error Errno.espipe
  | .directory => .error Errno.eisdir
  | _ => .error Errno.enodev

/-- `truncate`. -/
def truncatePath (kernel : Kernel) (base path : String) (size : Nat) : Result Kernel := do
  if negativeOffset size then .error Errno.einval
  match ← kernel.resolve base path with
  | (_, none) => .error Errno.enoent
  | (normal, some number) => if kernel.readOnly normal then .error erofs else kernel.truncateInode number size

/-- Whether the owner of a lock of the inode `number` is there yet, of the processes `live`: a process that has it open, or an open
file that they hold, as `heldFiles` has it. -/
def lockHeld (kernel : Kernel) (live : List Nat) (number : Nat) (lock : FileLock) : Bool :=
  match lock.owner with
  | .process group =>
    live.contains group && (kernel.process group).descriptors.toList.any fun (_, descriptor) =>
      (kernel.openFiles.get? descriptor.openFile).any (·.inode == number)
  | .openFile id | .flock id => (kernel.heldFiles live).contains id

/-- The locks of an inode whose owners are there yet. -/
def locksOf (kernel : Kernel) (live : List Nat) (number : Nat) : List FileLock :=
  ((kernel.inodes.get? number).map fun inode => inode.details.locks.filter (kernel.lockHeld live number)).getD []

/-- Whether `owner` had a lock of an inode, which then may have been let go of. -/
def hadLock (kernel : Kernel) (number : Nat) (owner : LockOwner) : Bool :=
  (kernel.inodes.get? number).any (·.details.locks.any (·.owner == owner))

/-- A lock of another that is in the way of one of `owner` of `start`..`stop`, if there is one. -/
def lockConflict (locks : List FileLock) (owner : LockOwner) (start stop : Nat) (exclusive : Bool) : Option FileLock :=
  let isFlock : LockOwner → Bool | .flock _ => true | _ => false
  locks.find? fun lock => lock.owner != owner && isFlock lock.owner == isFlock owner && lock.start < stop && start < lock.stop &&
    (exclusive || lock.exclusive)

/-- The locks of `owner` without `start`..`stop`, and with a lock of it there if `kind` says whether it is exclusive, which takes in
those of its own of the same kind that it touches. They are in the order of where they start, which is that `F_GETLK` finds them in. -/
def withLock (locks : List FileLock) (owner : LockOwner) (start stop : Nat) (kind : Option Bool) : List FileLock :=
  let cut := locks.flatMap fun lock =>
    if lock.owner != owner || lock.stop ≤ start || stop ≤ lock.start then [lock]
    else (if lock.start < start then [{ lock with stop := start }] else []) ++ (if stop < lock.stop then [{ lock with start := stop }] else [])
  let locks := match kind with
    | none => cut
    | some exclusive =>
      let (touching, rest) := cut.partition fun (lock : FileLock) => lock.owner == owner && lock.exclusive == exclusive && lock.start ≤ stop && start ≤ lock.stop
      let first := touching.foldl (fun least (lock : FileLock) => min least lock.start) start
      let last := touching.foldl (fun most (lock : FileLock) => max most lock.stop) stop
      { owner, start := first, stop := last, exclusive } :: rest
  locks.mergeSort fun first second => first.start ≤ second.start

/-- A lock of `owner` of an inode, or none there if `kind` is none, unless one of another is in the way, which it then gives. What
`flock` had first goes even then, as Linux has it. -/
def lockRange (kernel : Kernel) (live : List Nat) (number : Nat) (owner : LockOwner) (start stop : Nat) (kind : Option Bool) :
    Kernel × Option FileLock :=
  match kernel.inodes.get? number with
  | none => (kernel, none)
  | some inode =>
    let locks := inode.details.locks.filter (kernel.lockHeld live number)
    let set (locks : List FileLock) : Kernel :=
      { kernel with inodes := kernel.inodes.insert number { inode with details := { inode.details with locks } } }
    let conflict := kind.bind (lockConflict locks owner start stop)
    match conflict, owner with
    | some lock, .flock _ => (set (withLock locks owner start stop none), some lock)
    | some lock, _ => (set locks, some lock)
    | none, _ => (set (withLock locks owner start stop kind), none)

/-- `fcntl` with `F_GET_SEALS`, of a file that can have them. -/
def seals (kernel : Kernel) (group fd : Nat) : Result Nat := do
  let (_, file) ← openFileOf kernel group fd
  let held := (← inodeOf kernel file.inode).details.seals
  if held &&& sealable == 0 then .error Errno.einval
  .ok (held - sealable)

/-- `fcntl` with `F_ADD_SEALS`, by a descriptor that writes, unless `F_SEAL_SEAL` is there. `F_SEAL_WRITE` waits for no mapping to
write the file. -/
def addSeals (kernel : Kernel) (group fd seals : Nat) : Result Kernel := do
  let (_, file) ← openFileOf kernel group fd
  let inode ← inodeOf kernel file.inode
  let held := inode.details.seals
  if held &&& sealable == 0 || seals ≥ 0x40 then .error Errno.einval
  if !writable file.flags || held &&& 1 != 0 then .error Errno.eperm
  if seals &&& 8 != 0 &&
      kernel.processes.fold (fun found _ process => found || process.mappings.any fun mapping =>
        mapping.inode == file.inode && mapping.shared && mapping.mayWrite) false then
    .error 16
  .ok { kernel with inodes := kernel.inodes.insert file.inode { inode with details := { inode.details with seals := held ||| seals } } }

/-- `open` with `O_TMPFILE`: a file of no name in a directory, which only `linkat` gives one, to write. -/
def openTmpfile (kernel : Kernel) (group : Nat) (base path : String) (flags mode : Nat) : Result (Kernel × Nat) := do
  if !writable flags then .error Errno.einval
  let (normal, some number) ← kernel.resolve base path | .error Errno.enoent
  let .directory := (← inodeOf kernel number).content | .error Errno.enotdir
  let made := kernel.nextInode
  let process := kernel.process group
  let (gid, mode) := kernel.newGroup normal process.credentials (0o100000 ||| (mode &&& 0o7777 &&& (0o7777 - process.umask)))
  let (kernel, fd) := kernel.addObject group (.file ByteArray.empty) flags mode (access := flags &&& 3)
    (name := s!"{if normal == "/" then "" else normal}/#{made} (deleted)") (uid := process.credentials.fsuid) (gid := gid)
  -- Without `O_EXCL`, `linkat` may give it a name.
  let kernel := if has flags oExcl then kernel
    else { kernel with inodes := kernel.inodes.modify made fun inode => { inode with details := { inode.details with linkable := true } } }
  .ok (kernel, fd)

/-- Of `chmod` and `fchmod`, the permissions of an inode, as a process of `group` sets them: only its owner or root may, which is
`EPERM` to anyone else, and `S_ISGID` goes from what one sets who isn't root and isn't in the group of the inode: what root may do
here is of `CAP_FOWNER` and of `CAP_FSETID`. -/
def chmodInode (kernel : Kernel) (group number mode : Nat) : Result Kernel := do
  let inode ← inodeOf kernel number
  let credentials := (kernel.process group).credentials
  if !credentials.capable Capability.fowner && credentials.fsuid != inode.details.uid then .error Errno.eperm
  let gid := inode.details.gid
  let mode := if credentials.capable Capability.fsetid || gid == credentials.fsgid || credentials.groups.contains gid then mode &&& 0o7777 else mode &&& 0o5777
  let kept := inode.mode - (inode.mode &&& 0o7777)
  .ok { kernel with inodes := kernel.inodes.insert number { inode with mode := kept ||| mode, details := { inode.details with changed := kernel.clock } } }

/-- `chmod`. -/
def chmod (kernel : Kernel) (group : Nat) (base path : String) (mode : Nat) : Result Kernel := do
  match ← kernel.resolve base path with
  | (_, none) => .error Errno.enoent
  | (normal, some number) =>
    if kernel.readOnly normal then .error erofs
    kernel.chmodInode group number mode

/-- `fchmod`, of what a descriptor has open, whatever it is. -/
def fchmod (kernel : Kernel) (group fd mode : Nat) : Result Kernel := do
  let (_, file) ← openFileOf kernel group fd
  kernel.chmodInode group file.inode mode

/-- `fsync` and `fdatasync`: nothing has to reach a disk, so of a file or a directory it is done, but what isn't on one, a pipe, a
socket, a device or what the kernel makes of its own, is `EINVAL`. -/
def syncDescriptor (kernel : Kernel) (group fd : Nat) : Result Unit := do
  let (_, file) ← openFileOf kernel group fd
  match (← inodeOf kernel file.inode).content with
  | .file _ | .directory => .ok ()
  | _ => .error Errno.einval

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

/-- A process without what it had mapped in `lower`..`upper`, and what it advised of it for a child. -/
def dropMappings (kernel : Kernel) (group lower upper : Nat) : Kernel :=
  let process := kernel.process group
  if process.mappings.isEmpty && process.forkAdvice.isEmpty then kernel
  else kernel.setProcess group { process with mappings := process.mappings.flatMap (·.without lower upper)
                                              forkAdvice := process.forkAdvice.flatMap (·.without lower upper) }

/-- A process has `MADV_WIPEONFORK` or `MADV_DONTFORK`, as `wipe` says, in `lower`..`upper` if `on`, and otherwise hasn't, of
`MADV_KEEPONFORK` and `MADV_DOFORK`. -/
def adviseFork (kernel : Kernel) (group lower upper : Nat) (wipe on : Bool) : Kernel :=
  let process := kernel.process group
  let kept := process.forkAdvice.flatMap fun advice => if advice.wipe == wipe then advice.without lower upper else [advice]
  kernel.setProcess group { process with forkAdvice := if on && lower < upper then { start := lower, size := upper - lower, wipe } :: kept else kept }

/-- What a process advised of `lower`..`lower + size` for a child, at `start` instead, as `mremap` moves it. -/
def movedAdvice (kernel : Kernel) (group lower size start : Nat) : List ForkAdvice :=
  (kernel.process group).forkAdvice.filterMap fun advice =>
    let first := max advice.start lower
    let stop := min (advice.start + advice.size) (lower + size)
    if first < stop then some { advice with start := start + (first - lower), size := stop - first } else none

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

/-- What nothing holds any more goes: open files that no descriptor has, nor a message to a socket that hands it over, and inodes that
no path, open file, mapping or segment has, nor a socket that listens and has it as a connection to accept, nor the slave of a terminal.
An epoll keeps nothing, as Linux has it, and what is left of an inode elsewhere, by its number, finds none. -/
def collect (kernel : Kernel) : Kernel := Id.run do
  let mut files : Std.HashSet Nat := {}
  let mut inodes : Std.HashSet Nat := {}
  let mut fileWork : List Nat := []
  let mut inodeWork : List Nat := []
  for (_, process) in kernel.processes do
    for (_, descriptor) in process.descriptors do
      fileWork := descriptor.openFile :: fileWork
    for mapping in process.mappings do
      inodeWork := mapping.inode :: inodeWork
  for (_, number) in kernel.paths do
    inodeWork := number :: inodeWork
  for segment in kernel.ipc.segments do
    inodeWork := segment.inode :: inodeWork
  -- As far as what is held holds more, each once.
  for _ in [0:kernel.openFiles.size + kernel.inodes.size + 1] do
    if fileWork.isEmpty && inodeWork.isEmpty then break
    for id in fileWork do
      if !files.contains id then
        files := files.insert id
        if let some file := kernel.openFiles.get? id then inodeWork := file.inode :: inodeWork
    fileWork := []
    let pending := inodeWork
    inodeWork := []
    for number in pending do
      if inodes.contains number then continue
      inodes := inodes.insert number
      match kernel.inodes.get? number with
      | some { content := .socket socket, .. } =>
        inodeWork := socket.pending ++ inodeWork
        for message in socket.incoming do fileWork := message.rights ++ fileWork
      | some { content := .ptySlave master, .. } => inodeWork := master :: inodeWork
      | _ => pure ()
  pure { kernel with openFiles := kernel.openFiles.filter fun id _ => files.contains id
                     inodes := kernel.inodes.filter fun number _ => inodes.contains number }

end Kernel

/-! ### What the calls write to memory -/

namespace Abi

/-- A number of a device as `stat` has it, of its major and minor numbers, as `new_encode_dev` of Linux makes it. -/
def deviceNumber (device : Nat × Nat) : Nat :=
  let (major, minor) := device
  minor % 256 ||| major <<< 8 ||| (minor - minor % 256) <<< 12

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
    get 4 0 ++ get 8 (deviceNumber value.device) ++ get 8 value.size ++ get 8 4096 ++ get 8 ((value.size + 511) / 512) ++
    time value.accessed ++ time value.modified ++ time value.changed ++ bytesOf 24 0

/-- `struct stat` of `asm-generic/stat.h`, which has the order of the fields of 32-bit systems and is smaller. -/
def genericStat (value : Kernel.Stat) : ByteArray :=
  let time (at_ : Nat) : ByteArray := bytesOf 8 (at_ / 1000000000) ++ bytesOf 8 (at_ % 1000000000)
  bytesOf 8 1 ++ bytesOf 8 value.inode ++ bytesOf 4 value.mode ++ bytesOf 4 value.links ++ bytesOf 4 value.uid ++ bytesOf 4 value.gid ++
    bytesOf 8 (deviceNumber value.device) ++ bytesOf 8 0 ++ bytesOf 8 value.size ++ bytesOf 4 4096 ++ bytesOf 4 0 ++ bytesOf 8 ((value.size + 511) / 512) ++
    time value.accessed ++ time value.modified ++ time value.changed ++ bytesOf 8 0

/-- `struct stat` of 64-bit MIPS, which holds its times in 32 bits. -/
def mips64Stat (value : Kernel.Stat) (big : Bool) : ByteArray :=
  let get := field big
  let time (at_ : Nat) : ByteArray := get 4 (at_ / 1000000000) ++ get 4 (at_ % 1000000000)
  get 4 1 ++ bytesOf 12 0 ++ get 8 value.inode ++ get 4 value.mode ++ get 4 value.links ++ get 4 value.uid ++ get 4 value.gid ++
    get 4 (deviceNumber value.device) ++ bytesOf 12 0 ++ get 8 value.size ++ time value.accessed ++ time value.modified ++
    time value.changed ++ get 4 4096 ++ bytesOf 4 0 ++ get 8 ((value.size + 511) / 512) ++ bytesOf 56 0

/-- `struct stat64` of i686, which is packed. -/
def stat64 (value : Kernel.Stat) : ByteArray :=
  let time (at_ : Nat) : ByteArray := bytesOf 4 (at_ / 1000000000) ++ bytesOf 4 (at_ % 1000000000)
  bytesOf 8 1 ++ bytesOf 4 0 ++ bytesOf 4 (value.inode % 2 ^ 32) ++ bytesOf 4 value.mode ++ bytesOf 4 value.links ++
    bytesOf 4 value.uid ++ bytesOf 4 value.gid ++ bytesOf 8 (deviceNumber value.device) ++ bytesOf 4 0 ++ bytesOf 8 value.size ++
    bytesOf 4 4096 ++
    bytesOf 8 ((value.size + 511) / 512) ++ time value.accessed ++ time value.modified ++ time value.changed ++ bytesOf 8 value.inode

/-- `struct stat64` of ARM, whose wide fields are aligned. -/
def armStat64 (value : Kernel.Stat) : ByteArray :=
  let time (at_ : Nat) : ByteArray := bytesOf 4 (at_ / 1000000000) ++ bytesOf 4 (at_ % 1000000000)
  bytesOf 8 1 ++ bytesOf 4 0 ++ bytesOf 4 (value.inode % 2 ^ 32) ++ bytesOf 4 value.mode ++ bytesOf 4 value.links ++
    bytesOf 4 value.uid ++ bytesOf 4 value.gid ++ bytesOf 8 (deviceNumber value.device) ++ bytesOf 8 0 ++ bytesOf 8 value.size ++
    bytesOf 4 4096 ++ bytesOf 4 0 ++
    bytesOf 8 ((value.size + 511) / 512) ++ time value.accessed ++ time value.modified ++ time value.changed ++ bytesOf 8 value.inode

/-- `struct stat64` of 32-bit PowerPC. -/
def powerpcStat64 (value : Kernel.Stat) (big : Bool) : ByteArray :=
  let get := field big
  let time (at_ : Nat) : ByteArray := get 4 (at_ / 1000000000) ++ get 4 (at_ % 1000000000)
  get 8 1 ++ get 8 value.inode ++ get 4 value.mode ++ get 4 value.links ++ get 4 value.uid ++ get 4 value.gid ++
    get 8 (deviceNumber value.device) ++ bytesOf 8 0 ++ get 8 value.size ++ get 4 4096 ++ bytesOf 4 0 ++ get 8 ((value.size + 511) / 512) ++ time value.accessed ++
    time value.modified ++ time value.changed ++ bytesOf 8 0

/-- `struct stat64` of the o32 ABI of MIPS. -/
def mipsStat64 (value : Kernel.Stat) (big : Bool) : ByteArray :=
  let get := field big
  let time (at_ : Nat) : ByteArray := get 4 (at_ / 1000000000) ++ get 4 (at_ % 1000000000)
  get 4 1 ++ bytesOf 12 0 ++ get 8 value.inode ++ get 4 value.mode ++ get 4 value.links ++ get 4 value.uid ++ get 4 value.gid ++
    get 4 (deviceNumber value.device) ++ bytesOf 12 0 ++ get 8 value.size ++ time value.accessed ++ time value.modified ++ time value.changed ++ get 4 4096 ++
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
    time value.modified ++ get 4 value.device.1 ++ get 4 value.device.2 ++ get 120 0

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
