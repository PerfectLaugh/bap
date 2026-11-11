import Bap.Linux.Poll
import Bap.Linux.Identity

/-! # What a file has of itself

Hard links (`link`, `linkat`), `renameat2`, files of memory (`memfd_create`), what goes from one file to another
(`sendfile`, `splice`, `tee`, `copy_file_range`), locks (`flock`, and `fcntl` of `serveLock`), the times of a file (`utimensat`, `utimes`, `futimesat`, `utime`), whose it is (`chown` and
its kin), and its extended attributes (`setxattr`, `getxattr`, `listxattr`, `removexattr` and their kin of a link and of a
descriptor).

A file has the times that a write, a truncation or `chmod` gave it, which `stat` says, and these set. Only root gives a file to
another, or to a group that it isn't in. An extended attribute's name has a namespace, as `user.`, of at most 255 bytes, and its value
at most 64 KiB. A file of `memfd_create` can have seals, which `fcntl` adds and `Kernel` keeps to. What goes from a file to another
goes at most 1 MiB at a time, and from a pipe or a socket that has nothing yet, waits for it. Locks of files, of `flock` and of
`fcntl`, are those of `Kernel.lockRange`, and one that something is in the way of waits for it to go, with no deadlock found. -/

namespace Bap.Linux

open Bap.Emu Bap.Tasks

namespace Files

private def numberOf (big : Bool) (bytes : ByteArray) : Nat :=
  let ordered := if big then bytes.toList else bytes.toList.reverse
  ordered.foldl (fun value byte => value * 256 + byte.toNat) 0

/-- A string of the guest, to its zero, which doesn't read past the page where it ends. -/
def readString (emu : Emu) (address : Nat) : IO String := do
  let mut out := ByteArray.empty
  let mut at_ := address
  while out.size < 4096 do
    let chunk ← read emu at_ (min 256 (4096 - at_ % 4096))
    match chunk.toList.findIdx? (· == 0) with
    | some index => return textOf (out ++ chunk.extract 0 index)
    | none =>
      out := out ++ chunk
      at_ := at_ + chunk.size
  -- No zero in `PATH_MAX`: that much of it, which the kernel makes `ENAMETOOLONG` of.
  pure (textOf (out.extract 0 4096))

/-- An inode of a kernel as it is now: its times set, or its owner, or its attributes. -/
private def alter (kernel : Kernel) (number : Nat) (change : Meta → Meta) : Kernel :=
  match kernel.inodes.get? number with
  | some inode => { kernel with inodes := kernel.inodes.insert number { inode with details := change inode.details } }
  | none => kernel

/-- Up to `count` bytes of a descriptor, as `sendfile` and `splice` take them: from `offset` if it says, and otherwise from where the
file is, which moves, or what a pipe or a socket has first, which goes; `none` while that has nothing and more may come. -/
private def take (kernel : Kernel) (group fd count : Nat) (offset : Option Nat) (live : List Nat) : Result (Kernel × Option ByteArray) := do
  if let some at_ := offset then return (kernel, some (← kernel.readFrom group fd count at_))
  if kernel.isSocket group fd then
    let (kernel, received) ← kernel.receive group fd count false (kernel.socketAlive · live)
    return (kernel, received.map (·.data))
  if let some number := kernel.pipeOf group fd then
    if kernel.pipeWaiting number == 0 && kernel.pipeHeld number live true then return (kernel, none)
  let (kernel, bytes) ← kernel.read group fd count
  pure (kernel, some bytes)

/-- Bytes to a descriptor, as `sendfile` and `splice` give them: at `offset` if it says, and otherwise where the file is, or to the
other end of a socket, or to a pipe that something reads, as much as it has room for. -/
private def put (kernel : Kernel) (group fd : Nat) (bytes : ByteArray) (offset : Option Nat) (live : List Nat) : Result (Kernel × Nat) := do
  if let some at_ := offset then return ← kernel.writeTo group fd bytes at_
  if kernel.isSocket group fd then return ← kernel.send group fd { data := bytes } none (kernel.socketAlive · live)
  if let some number := kernel.pipeOf group fd then
    if !kernel.pipeHeld number live false then .error Errno.epipe
  kernel.write group fd bytes

/-- The calls of this module, if the call is one of them. -/
def serve (poller : Poller) (emu : Emu) (call : Call) (args : List Nat) : IO (Option SyscallAction) := do
  let architecture := poller.architecture
  let big := architecture.big
  let word := architecture.bits / 8
  let arg (index : Nat) : Nat := args.getD index 0
  let group := (← currentTask emu).group
  let kernel ← poller.kernel.get
  let now := kernel.clock
  let fail (errno : Nat) : IO (Option SyscallAction) := do pure (some (.returnValue (2 ^ 64 - errno)))
  let succeed (value : Nat := 0) : IO (Option SyscallAction) := do pure (some (.returnValue value))
  let fromResult (result : Result Kernel) : IO (Option SyscallAction) := do
    match result with
    | .ok next => poller.kernel.set next; succeed
    | .error errno => fail errno
  let (eopnotsupp, enodata, erange, e2big) := (95, 61, 34, 7)
  let atCwd (value : Nat) : Bool := value == 2 ^ 64 - 100 || value == 2 ^ 32 - 100
  -- A path from an address, as an absolute one, of the directory that the call says, which ends as it does.
  let pathAt (directory address : Nat) : IO (Result String) := do
    match kernel.baseOf group directory (atCwd directory) with
    | .error errno => pure (.error errno)
    | .ok base =>
      let given ← readString emu address
      if given.isEmpty then return .error Errno.enoent
      let (base, path) := kernel.pathIn group base given
      pure (.ok (if path.startsWith "/" then path else base ++ "/" ++ path))
  -- Of what has no path that it was found by, whether it is on what is mounted read-only, by the path that it has.
  let readOnlyInode (number : Nat) : Bool := (kernel.pathOfInode number).any kernel.readOnly
  -- The inode of a path, or of what a descriptor has of `AT_EMPTY_PATH` with an empty path, and whether it is on what is mounted
  -- read-only, as what writes to it is `EROFS`.
  let placeAt (directory address : Nat) (follow empty : Bool) : IO (Result (Nat × Bool)) := do
    if empty && (← readString emu address).isEmpty then
      -- Of `AT_FDCWD`, the working directory.
      if atCwd directory then
        return match kernel.resolveVia "/" (kernel.cwdOf group) with
          | .ok (normal, some number, via) => .ok (number, kernel.readOnlyVia via normal)
          | .ok (_, none, _) => .error Errno.enoent
          | .error errno => .error errno
      return (kernel.openFileOf group directory).map fun (_, file) => (file.inode, readOnlyInode file.inode)
    match ← pathAt directory address with
    | .error errno => pure (.error errno)
    | .ok path =>
      match kernel.resolveVia "/" path follow with
      | .ok (normal, some number, via) => pure (.ok (number, kernel.readOnlyVia via normal))
      | .ok (_, none, _) => pure (.error Errno.enoent)
      | .error errno => pure (.error errno)
  let inodeAt (directory address : Nat) (follow empty : Bool) : IO (Result Nat) := do
    pure ((← placeAt directory address follow empty).map (·.1))
  let ofFd (fd : Nat) : Result Nat := (kernel.openFileOf group fd).map (·.2.inode)
  let placeOfFd (fd : Nat) : Result (Nat × Bool) := (ofFd fd).map fun number => (number, readOnlyInode number)
  -- Whether a descriptor that may be written isn't a pipe and was opened to append.
  let appends (fd : Nat) : Bool := (kernel.pipeOf group fd).isNone && match kernel.openFileOf group fd with
    | .ok (_, file) => file.flags &&& 3 != 0 && file.flags &&& Kernel.oAppend != 0
    | .error _ => false
  let credentials := (kernel.process group).credentials
  -- Times of `timespec`, or of `timeval` of `scale` 1000, two of them, of which `UTIME_NOW` and `UTIME_OMIT` are now and none, or
  -- `EINVAL` of a fraction that is negative or of a second or more.
  -- Each is of a time that was given, which is `TIMES_SET_FLAGS` of Linux, or not.
  let times (address field scale : Nat) : IO (Result ((Option Nat × Bool) × (Option Nat × Bool))) := do
    if address == 0 then return .ok ((some now, false), (some now, false))
    let one (at_ : Nat) : IO (Result (Option Nat × Bool)) := do
      let seconds := numberOf big (← read emu at_ field)
      let (_, fraction) ← readTime emu at_ field
      if scale == 1 && fraction == 0x3fffffff then return .ok (some now, false)
      if scale == 1 && fraction == 0x3ffffffe then return .ok (none, false)
      if fraction < 0 || fraction * scale ≥ 1000000000 then return .error Errno.einval
      pure (.ok (some (seconds * 1000000000 + fraction.toNat * scale), true))
    let first ← one address
    let second ← one (address + 2 * field)
    pure (do pure (← first, ← second))
  -- Of the file, or why there is none, and then of the times.
  -- As `vfs_utimes` and `setattr_prepare` have it: times that are given, or now of one and not the other, only of the owner or with
  -- `CAP_FOWNER`, else `EPERM`; now of both, of them or of one that may write it, else `EACCES`; and neither, nothing at all.
  let setTimes (place : Result (Nat × Bool)) (given : Result ((Option Nat × Bool) × (Option Nat × Bool))) : IO (Option SyscallAction) := do
    match place, given with
    | .error errno, _ | _, .error errno => fail errno
    | .ok (number, readOnly), .ok ((accessed, givenAccessed), (modified, givenModified)) =>
      let some inode := kernel.inodes.get? number | return ← fail Errno.enoent
      if accessed.isNone && modified.isNone then return ← succeed
      if readOnly then return ← fail 30
      let owner := credentials.fsuid == inode.details.uid || credentials.capable Capability.fowner
      if (givenAccessed || givenModified || accessed.isNone || modified.isNone) && !owner then return ← fail Errno.eperm
      if !owner && !Kernel.permits inode credentials false 2 then return ← fail Errno.eacces
      poller.kernel.set (alter kernel number fun details =>
        { details with accessed := accessed.getD details.accessed, modified := modified.getD details.modified, changed := now })
      succeed
  -- Of `chown`, as `chown_ok` and `chgrp_ok` have it: -1 leaves either as it is, which anyone may; else its owner, by the user that it
  -- goes by on files, may leave its owner as it is and give it to a group that it is in or that it has; and with `CAP_CHOWN`, anything.
  let chown (place : Result (Nat × Bool)) (uid gid : Nat) : IO (Option SyscallAction) := do
    let unset := 2 ^ 32 - 1
    let (uid, gid) := (uid % 2 ^ 32, gid % 2 ^ 32)
    match place with
    | .error errno => fail errno
    | .ok (number, readOnly) =>
      let some inode := kernel.inodes.get? number | return ← fail Errno.enoent
      if readOnly then return ← fail 30
      let owner := credentials.fsuid == inode.details.uid
      let mayGive := credentials.capable Capability.chown ||
        (uid == unset || owner && uid == inode.details.uid) &&
        (gid == unset || owner && (gid == inode.details.gid || gid == credentials.fsgid || credentials.groups.contains gid))
      if !mayGive then return ← fail 1
      -- What loses setuid or setgid has its mode changed, which only its owner may, or with `CAP_FOWNER`, as `setattr_prepare` has it
      -- of what `chown_common` asks: of -1 and -1 too.
      let killed := !(inode.content matches .directory) &&
        (inode.mode &&& 0o4000 != 0 || inode.mode &&& 0o2010 == 0o2010)
      if killed && !owner && !credentials.capable Capability.fowner then return ← fail 1
      let kernel := alter kernel number fun details =>
        { details with uid := if uid == unset then details.uid else uid, gid := if gid == unset then details.gid else gid
                       changed := now }
      -- What isn't a directory loses setuid, and setgid if its group may run it, whoever changes its owner, as Linux's
      -- `chown_common` and `notify_change` have it: setgid without that is of locking, and stays.
      let kept (mode : Nat) : Nat :=
        let mode := mode - (mode &&& 0o4000)
        if mode &&& 0o010 != 0 then mode - (mode &&& 0o2000) else mode
      let kernel := match kernel.inodes.get? number with
        | some { content := .directory, .. } => kernel
        | some inode => { kernel with inodes := kernel.inodes.insert number { inode with mode := kept inode.mode } }
        | none => kernel
      poller.kernel.set kernel
      succeed
  -- Extended attributes: a name of a namespace, set of `XATTR_CREATE` only if it isn't there and of `XATTR_REPLACE` only if it is.
  let named (address : Nat) : IO (Except Nat String) := do
    let name ← readString emu address
    if name.isEmpty || name.utf8ByteSize > 255 then return .error erange
    if !["user.", "trusted.", "security.", "system."].any fun space => name.startsWith space then return .error eopnotsupp
    pure (.ok name)
  let onNumber (number : Result Nat) (action : Nat → IO (Option SyscallAction)) : IO (Option SyscallAction) := do
    match number with
    | .ok number =>
      match kernel.inodes.get? number with
      | some _ => action number
      | none => fail Errno.enoent
    | .error errno => fail errno
  let onName (nameAt : Nat) (action : String → IO (Option SyscallAction)) : IO (Option SyscallAction) := do
    match ← named nameAt with
    | .ok name => action name
    | .error errno => fail errno
  -- As Linux's `xattr_permission` has it: `trusted.` is of `CAP_SYS_ADMIN`, and `user.` of a file or a directory that it may read, or write
  -- to change; what it may not see is as if it weren't there.
  let denied (number : Nat) (name : String) (writing : Bool) : Option Nat :=
    match kernel.inodes.get? number with
    | none => none
    | some inode =>
      if name.startsWith "trusted." && !credentials.capable Capability.sysAdmin then
        some (if writing then Errno.eperm else enodata)
      else if name.startsWith "user." then
        if !(inode.content matches .file _ | .directory) then some (if writing then Errno.eperm else enodata)
        else if !Kernel.permits inode credentials false (if writing then 2 else 4) then some Errno.eacces
        else none
      else none
  let attributesOf (number : Nat) : List (String × ByteArray) := ((kernel.inodes.get? number).map (·.details.attributes)).getD []
  let setAttribute (place : Result (Nat × Bool)) (nameAt valueAt size flags : Nat) : IO (Option SyscallAction) :=
    onNumber (place.map (·.1)) fun number => onName nameAt fun name => do
      if size > 65536 then return ← fail e2big
      if place.toOption.any (·.2) then return ← fail 30
      if let some errno := denied number name true then return ← fail errno
      let there := (attributesOf number).any (·.1 == name)
      if flags &&& 1 != 0 && there then return ← fail Errno.eexist
      if flags &&& 2 != 0 && !there then return ← fail enodata
      let value ← read emu valueAt size
      poller.kernel.set (alter kernel number fun details =>
        { details with attributes := details.attributes.filter (·.1 != name) ++ [(name, value)], changed := now })
      succeed
  let getAttribute (number : Result Nat) (nameAt valueAt size : Nat) : IO (Option SyscallAction) :=
    onNumber number fun number => onName nameAt fun name => do
      if let some errno := denied number name false then return ← fail errno
      let some (_, value) := (attributesOf number).find? (·.1 == name) | return ← fail enodata
      if size == 0 then return ← succeed value.size
      if size < value.size then return ← fail erange
      write emu valueAt value
      succeed value.size
  let listAttributes (number : Result Nat) (listAt size : Nat) : IO (Option SyscallAction) :=
    onNumber number fun number => do
      -- Of what it may see: `trusted.` only of `CAP_SYS_ADMIN`.
      let seen := (attributesOf number).filter fun (name, _) => !name.startsWith "trusted." || credentials.capable Capability.sysAdmin
      let names := seen.foldl (fun out (name, _) => (out ++ name.toUTF8).push 0) ByteArray.empty
      if size == 0 then return ← succeed names.size
      if size < names.size then return ← fail erange
      write emu listAt names
      succeed names.size
  let removeAttribute (place : Result (Nat × Bool)) (nameAt : Nat) : IO (Option SyscallAction) :=
    onNumber (place.map (·.1)) fun number => onName nameAt fun name => do
      if place.toOption.any (·.2) then return ← fail 30
      if let some errno := denied number name true then return ← fail errno
      if !(attributesOf number).any (·.1 == name) then return ← fail enodata
      poller.kernel.set (alter kernel number fun details =>
        { details with attributes := details.attributes.filter (·.1 != name), changed := now })
      succeed
  let here := 2 ^ 64 - 100
  -- An offset of `size` bytes that a call is given the address of, if it is, as 64 bits with its sign, and that address with how far it
  -- went.
  let offsetAt (address size : Nat) : IO (Option Nat) := do
    if address == 0 then return none
    let value := numberOf big (← read emu address size)
    pure (some (if value ≥ 2 ^ (8 * size - 1) then value + 2 ^ 64 - 2 ^ (8 * size) else value))
  let moveOffset (address size : Nat) (start : Option Nat) (count : Nat) : IO Unit := do
    if let some start := start then write emu address (Abi.field big size (start + count))
  -- Of a pipe that a call writes to, whether it is full, as it then gives `EAGAIN` or waits: not one that nothing reads, which is
  -- `EPIPE` of `put`.
  let full (number : Nat) (live : List Nat) : Bool := kernel.pipeRoom number == 0 && kernel.pipeHeld number live false
  -- Of `sendfile`, `splice` and `copy_file_range`: what goes from one to the other, at most 1 MiB at a time and what a pipe has room
  -- for, from and to the offsets that the call gives, which then move; or, while there is nothing yet or no room, `EAGAIN` or a wait.
  let transfer (source target count : Nat) (from_ to : Option Nat) (nonblocking : Bool) (moved : Nat → IO Unit) :
      IO (Option SyscallAction) := do
    let live ← poller.live
    let room ← match to, kernel.pipeOf group target with
      | none, some number =>
        if full number live then
          if nonblocking || kernel.nonblocking group target then return ← fail Errno.eagain
          return some (← poller.timers.waitUntil emu readySpace 0 none true)
        pure (kernel.pipeRoom number)
      | _, _ => pure 0x100000
    match take kernel group source (min count (min room 0x100000)) from_ live with
    | .error errno => fail errno
    | .ok (_, none) => if nonblocking then fail Errno.eagain else pure (some (← poller.timers.waitUntil emu readySpace 0 none true))
    | .ok (taken, some bytes) =>
      if bytes.isEmpty then
        return ← match kernel.openFileOf group target with
          | .ok (_, file) => if file.flags &&& 3 == 0 then fail Errno.ebadf else succeed
          | .error errno => fail errno
      match put taken group target bytes to live with
      | .error errno => fail errno
      | .ok (next, count) =>
        poller.kernel.set next
        moved count
        poller.wake emu
        succeed count
  let pipeOf := kernel.pipeOf group
  try
    match call with
    | .link =>
      let source ← match ← pathAt here (arg 0) with
        | .ok path => pure path
        | .error errno => return ← fail errno
      let target ← match ← pathAt here (arg 1) with
        | .ok path => pure path
        | .error errno => return ← fail errno
      fromResult (kernel.link group "/" source target false)
    | .linkat =>
      -- AT_EMPTY_PATH of a descriptor, and AT_SYMLINK_FOLLOW.
      let target ← match ← pathAt (arg 2) (arg 3) with
        | .ok path => pure path
        | .error errno => return ← fail errno
      if arg 4 &&& 0x1000 != 0 && (← readString emu (arg 1)).isEmpty then
        match ofFd (arg 0) with
        | .ok number => fromResult (kernel.linkInode group number "/" target)
        | .error errno => fail errno
      else
        let source ← match ← pathAt (arg 0) (arg 1) with
        | .ok path => pure path
        | .error errno => return ← fail errno
        fromResult (kernel.link group "/" source target (arg 4 &&& 0x400 != 0))
    | .renameat2 =>
      let source ← match ← pathAt (arg 0) (arg 1) with
        | .ok path => pure path
        | .error errno => return ← fail errno
      let target ← match ← pathAt (arg 2) (arg 3) with
        | .ok path => pure path
        | .error errno => return ← fail errno
      fromResult (kernel.renameWith group "/" source target (arg 4))
    | .utimensat | .utimensat64 =>
      let field := if call == .utimensat64 then 8 else word
      -- Times that aren't are `EINVAL` first, and then, of a path, flags but `AT_SYMLINK_NOFOLLOW` and `AT_EMPTY_PATH`, and of a
      -- descriptor without one, any, as `do_utimes` has them.
      let given ← times (arg 2) field 1
      if let .error errno := given then return ← fail errno
      let flags := arg 3 % 2 ^ 32
      if (if arg 1 == 0 && !atCwd (arg 0) then flags != 0 else flags &&& (2 ^ 32 - 1 - 0x1100) != 0) then return ← fail Errno.einval
      let place ← if arg 1 == 0 then pure (placeOfFd (arg 0)) else placeAt (arg 0) (arg 1) (flags &&& 0x100 == 0) (flags &&& 0x1000 != 0)
      setTimes place given
    -- Of a `timeval`, `EINVAL` is before the file is looked for.
    | .utimes | .futimesat =>
      let (directory, path, address) := if call == .utimes then (here, arg 0, arg 1) else (arg 0, arg 1, arg 2)
      let given ← times address word 1000
      if let .error errno := given then return ← fail errno
      setTimes (← placeAt directory path true false) given
    | .utime =>
      let given ← if arg 1 == 0 then pure ((some now, false), (some now, false)) else do
        pure ((some ((numberOf big (← read emu (arg 1) word)) * 1000000000), true),
          (some ((numberOf big (← read emu (arg 1 + word) word)) * 1000000000), true))
      setTimes (← placeAt here (arg 0) true false) (.ok given)
    | .chown => chown (← placeAt here (arg 0) true false) (arg 1) (arg 2)
    | .lchown => chown (← placeAt here (arg 0) false false) (arg 1) (arg 2)
    | .fchown => chown (placeOfFd (arg 0)) (arg 1) (arg 2)
    | .fchownat => chown (← placeAt (arg 0) (arg 1) (arg 4 &&& 0x100 == 0) (arg 4 &&& 0x1000 != 0)) (arg 2) (arg 3)
    | .setxattr => setAttribute (← placeAt here (arg 0) true false) (arg 1) (arg 2) (arg 3) (arg 4)
    | .lsetxattr => setAttribute (← placeAt here (arg 0) false false) (arg 1) (arg 2) (arg 3) (arg 4)
    | .fsetxattr => setAttribute (placeOfFd (arg 0)) (arg 1) (arg 2) (arg 3) (arg 4)
    | .getxattr => getAttribute (← inodeAt here (arg 0) true false) (arg 1) (arg 2) (arg 3)
    | .lgetxattr => getAttribute (← inodeAt here (arg 0) false false) (arg 1) (arg 2) (arg 3)
    | .fgetxattr => getAttribute (ofFd (arg 0)) (arg 1) (arg 2) (arg 3)
    | .listxattr => listAttributes (← inodeAt here (arg 0) true false) (arg 1) (arg 2)
    | .llistxattr => listAttributes (← inodeAt here (arg 0) false false) (arg 1) (arg 2)
    | .flistxattr => listAttributes (ofFd (arg 0)) (arg 1) (arg 2)
    | .removexattr => removeAttribute (← placeAt here (arg 0) true false) (arg 1)
    | .lremovexattr => removeAttribute (← placeAt here (arg 0) false false) (arg 1)
    | .fremovexattr => removeAttribute (placeOfFd (arg 0)) (arg 1)
    | .flock =>
      -- `LOCK_SH`, `LOCK_EX` or `LOCK_UN`, and `LOCK_NB`, of all of the file, for the open file.
      let operation := arg 1 - (arg 1 &&& 4)
      let kind ← match operation with
        | 1 => pure (some false)
        | 2 => pure (some true)
        | 8 => pure none
        | _ => return ← fail Errno.einval
      let .ok (id, file) := kernel.openFileOf group (arg 0) | fail Errno.ebadf
      let (next, conflict) := kernel.lockRange (← poller.live) file.inode (.flock id) 0 lockEnd kind
      poller.kernel.set next
      if kernel.hadLock file.inode (.flock id) then poller.wake emu
      match conflict with
      | none => succeed
      | some _ => if arg 1 &&& 4 != 0 then fail Errno.eagain else pure (some (← poller.timers.waitUntil emu readySpace 0 none true))
    | .memfdCreate =>
      -- `MFD_CLOEXEC`, `MFD_ALLOW_SEALING`, `MFD_HUGETLB`, and `MFD_NOEXEC_SEAL` or `MFD_EXEC`, of which the first seals that it
      -- runs nothing, and so has seals.
      let flags := arg 1
      let name ← readString emu (arg 0)
      if flags ≥ 0x20 || flags &&& 0x18 == 0x18 || name.utf8ByteSize > 249 then
        return ← fail Errno.einval
      let noexec := flags &&& 8 != 0
      let seals := sealable ||| (if noexec then 0x20 else if flags &&& 2 != 0 then 0 else 1)
      -- It is of who makes it, as a file is.
      let credentials := (kernel.process group).credentials
      let (next, fd) := kernel.addObject group (.file ByteArray.empty) (if flags &&& 1 != 0 then Kernel.oCloexec else 0)
        (if noexec then 0o100666 else 0o100777) seals (name := s!"/memfd:{name} (deleted)") (uid := credentials.fsuid)
        (gid := credentials.fsgid)
      poller.kernel.set next
      succeed fd
    | .sendfile | .sendfile64 =>
      let size := if call == .sendfile64 then 8 else word
      -- What isn't a pipe and was opened to append is `EINVAL` to send to, as `do_splice_direct` has it, once both may be read and
      -- written.
      if appends (arg 0) && (kernel.openFileOf group (arg 1)).toOption.any (·.2.flags &&& 3 != 1) then return ← fail Errno.einval
      let start ← offsetAt (arg 2) size
      transfer (arg 1) (arg 0) (arg 3) start none (kernel.nonblocking group (arg 1)) (moveOffset (arg 2) size start)
    | .splice =>
      let (input, output) := (pipeOf (arg 0), pipeOf (arg 2))
      if input.isNone && output.isNone then return ← fail Errno.einval
      if (input.isSome && arg 1 != 0) || (output.isSome && arg 3 != 0) then return ← fail Errno.espipe
      -- And to what was opened to append, as `do_splice` has it.
      if output.isNone && appends (arg 2) then return ← fail Errno.einval
      let (from_, to) := (← offsetAt (arg 1) 8, ← offsetAt (arg 3) 8)
      transfer (arg 0) (arg 2) (arg 4) from_ to (arg 5 &&& 2 != 0 || kernel.nonblocking group (arg 0)) fun count => do
        moveOffset (arg 1) 8 from_ count
        moveOffset (arg 3) 8 to count
    | .tee =>
      -- What one pipe has, to another, which the first keeps.
      let (some input, some output) := (pipeOf (arg 0), pipeOf (arg 1)) | return ← fail Errno.einval
      if input == output then return ← fail Errno.einval
      let live ← poller.live
      let waiting := kernel.pipeWaiting input
      if waiting == 0 then
        if !kernel.pipeHeld input live true then return ← succeed
        if arg 3 &&& 2 != 0 || kernel.nonblocking group (arg 0) then return ← fail Errno.eagain
        return some (← poller.timers.waitUntil emu readySpace 0 none true)
      if full output live then
        if arg 3 &&& 2 != 0 || kernel.nonblocking group (arg 0) || kernel.nonblocking group (arg 1) then return ← fail Errno.eagain
        return some (← poller.timers.waitUntil emu readySpace 0 none true)
      let .some { content := .pipe buffer head _ _, .. } := kernel.inodes.get? input | fail Errno.einval
      match put kernel group (arg 1) (buffer.extract head (head + min (arg 2) 0x100000)) none live with
      | .error errno => fail errno
      | .ok (next, count) =>
        poller.kernel.set next
        poller.wake emu
        succeed count
    | .copyFileRange =>
      if arg 5 != 0 then return ← fail Errno.einval
      let regular (fd : Nat) : Result (Nat × OpenFile) := do
        let (_, file) ← kernel.openFileOf group fd
        match (← kernel.inodeOf file.inode).content with
        | .file _ => pure (file.inode, file)
        | .directory => .error Errno.eisdir
        | _ => .error Errno.einval
      match regular (arg 0), regular (arg 2) with
      | .error errno, _ | _, .error errno => fail errno
      | .ok (source, input), .ok (target, output) =>
        if input.flags &&& 3 == 1 || output.flags &&& 3 == 0 || output.flags &&& Kernel.oAppend != 0 then return ← fail Errno.ebadf
        let (from_, to) := (← offsetAt (arg 1) 8, ← offsetAt (arg 3) 8)
        -- An offset that the count takes past the end of 64 bits is `EOVERFLOW`, and another negative one `EINVAL`, as `transfer` has it.
        if [from_, to].any (·.any (· + arg 4 ≥ 2 ^ 64)) then return ← fail 75
        let (first, second) := (from_.getD input.offset, to.getD output.offset)
        -- What overlaps is of what there is to copy, as `generic_copy_file_checks` has it: no more than is there from where it starts.
        let size := match kernel.inodes.get? source with
          | some { content := .file data, .. } => data.size
          | _ => 0
        let count := min (arg 4) (size - min size first)
        if source == target && first < second + count && second < first + count then return ← fail Errno.einval
        transfer (arg 0) (arg 2) (arg 4) from_ to false fun count => do
          moveOffset (arg 1) 8 from_ count
          moveOffset (arg 3) 8 to count
    | _ => pure none
  catch _ => fail 14

/-- `fcntl` of the locks of a range of a file, if the command is one of those: `F_GETLK`, `F_SETLK` and `F_SETLKW` as the libc of the
guest numbers them, which on 32 bits are those of `struct flock64`, and `F_OFD_GETLK`, `F_OFD_SETLK` and `F_OFD_SETLKW`. -/
def serveLock (poller : Poller) (emu : Emu) (args : List Nat) : IO (Option SyscallAction) := do
  let architecture := poller.architecture
  let big := architecture.big
  let arg (index : Nat) : Nat := args.getD index 0
  let (get, set, wait) := match architecture with
    | .mips 64 _ _ => (14, 6, 7)
    | .mips .. => (33, 34, 35)
    | other => if other.bits == 64 then (5, 6, 7) else (12, 13, 14)
  let command := arg 1
  let ofd := 36 ≤ command && command ≤ 38
  if !ofd && ![get, set, wait].contains command then return none
  let group := (← currentTask emu).group
  let kernel ← poller.kernel.get
  let fail (errno : Nat) : IO (Option SyscallAction) := do pure (some (.returnValue (2 ^ 64 - errno)))
  let succeed : IO (Option SyscallAction) := do pure (some (.returnValue 0))
  -- `struct flock`: its type and whence, of two bytes, then where it starts and how long it is, which i386 doesn't align, and the
  -- process.
  let startAt := if architecture matches .i686 then 4 else 8
  try
    let bytes ← read emu (arg 2) (startAt + 20)
    let field (offset size : Nat) : Nat := numberOf big (bytes.extract offset (offset + size))
    let signed (value : Nat) : Int := if value ≥ 2 ^ 63 then (value : Int) - 2 ^ 64 else value
    let (type, whence, start, length) := (field 0 2, field 2 2, signed (field startAt 8), signed (field (startAt + 8) 8))
    if type > 2 || (ofd && field (startAt + 16) 4 != 0) then return ← fail Errno.einval
    let .ok (id, file) := kernel.openFileOf group (arg 0) | return ← fail Errno.ebadf
    let size := match kernel.inodes.get? file.inode with
      | some { content := .file data, .. } => data.size
      | _ => 0
    let base : Int ← match whence with
      | 0 => pure 0
      | 1 => pure file.offset
      | 2 => pure size
      | _ => return ← fail Errno.einval
    let (first, last) := if length < 0 then (base + start + length, base + start) else (base + start, base + start + length)
    if first < 0 then return ← fail Errno.einval
    let (first, last) := (first.toNat, if length == 0 then lockEnd else last.toNat)
    let owner := if ofd then LockOwner.openFile id else .process group
    let live ← poller.live
    if command == get || command == 36 then
      if type == 2 then return ← fail Errno.einval
      match Kernel.lockConflict (kernel.locksOf live file.inode) owner first last (type == 1) with
      | none => write emu (arg 2) (Abi.field big 2 2)
      | some lock =>
        let pid := match lock.owner with
          | .process holder => holder
          | _ => 2 ^ 32 - 1
        write emu (arg 2) (Abi.field big 2 (if lock.exclusive then 1 else 0) ++ Abi.field big 2 0)
        write emu (arg 2 + startAt) (Abi.field big 8 lock.start ++ Abi.field big 8 (if lock.stop == lockEnd then 0 else lock.stop - lock.start) ++
          Abi.field big 4 pid)
      return ← succeed
    -- A lock to read is of a file opened to read, and one to write of one opened to write.
    let access := file.flags &&& 3
    if (type == 0 && access == 1) || (type == 1 && access == 0) then return ← fail Errno.ebadf
    let (next, conflict) := kernel.lockRange live file.inode owner first last (if type == 2 then none else some (type == 1))
    poller.kernel.set next
    match conflict with
    | none =>
      -- What waits may go on once something was let go of.
      if kernel.hadLock file.inode owner then poller.wake emu
      succeed
    | some _ =>
      if command == wait || command == 38 then pure (some (← poller.timers.waitUntil emu readySpace 0 none true))
      else fail Errno.eagain
  catch _ => fail Errno.efault

end Files

end Bap.Linux
