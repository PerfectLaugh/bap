import Bap.Linux.Poll
import Bap.Linux.Identity

/-! # What a file has of itself

Hard links (`link`, `linkat`), `renameat2`, the times of a file (`utimensat`, `utimes`, `futimesat`, `utime`), whose it is (`chown` and
its kin), and its extended attributes (`setxattr`, `getxattr`, `listxattr`, `removexattr` and their kin of a link and of a
descriptor).

A file has the times that a write, a truncation or `chmod` gave it, which `stat` says, and these set. Only root gives a file to
another, or to a group that it isn't in. An extended attribute's name has a namespace, as `user.`, of at most 255 bytes, and its value
at most 64 KiB. -/

namespace Bap.Linux

open Bap.Emu Bap.Tasks

namespace Files

private def numberOf (big : Bool) (bytes : ByteArray) : Nat :=
  let ordered := if big then bytes.toList else bytes.toList.reverse
  ordered.foldl (fun value byte => value * 256 + byte.toNat) 0

/-- A string of the guest, to its zero, which doesn't read past the page where it ends. -/
private def readString (emu : Emu) (address : Nat) : IO String := do
  let mut out := ByteArray.empty
  let mut at_ := address
  while out.size < 4096 do
    let chunk ← read emu at_ (min 256 (4096 - at_ % 4096))
    match chunk.toList.findIdx? (· == 0) with
    | some index => return String.fromUTF8! (out ++ chunk.extract 0 index)
    | none =>
      out := out ++ chunk
      at_ := at_ + chunk.size
  pure (String.fromUTF8! out)

/-- An inode of a kernel as it is now: its times set, or its owner, or its attributes. -/
private def alter (kernel : Kernel) (number : Nat) (change : Meta → Meta) : Kernel :=
  match kernel.inodes.get? number with
  | some inode => { kernel with inodes := kernel.inodes.insert number { inode with details := change inode.details } }
  | none => kernel

/-- The calls of this module, if the call is one of them. -/
def serve (poller : Poller) (emu : Emu) (call : Call) (args : List Nat) : IO (Option SyscallAction) := do
  let architecture := poller.architecture
  let big := architecture.big
  let word := architecture.bits / 8
  let mips := architecture matches .mips ..
  let arg (index : Nat) : Nat := args.getD index 0
  let group := (← currentTask emu).group
  let kernel ← poller.kernel.get
  let now := kernel.clock
  let fail (errno : Nat) : IO (Option SyscallAction) := do pure (some (← syscallReturn emu (.error errno)))
  let succeed (value : Nat := 0) : IO (Option SyscallAction) := do pure (some (← syscallReturn emu (.ok value)))
  let fromResult (result : Result Kernel) : IO (Option SyscallAction) := do
    match result with
    | .ok next => poller.kernel.set next; succeed
    | .error errno => fail errno
  let (eopnotsupp, enodata, erange, e2big) := (if mips then 122 else 95, 61, 34, 7)
  let atCwd (value : Nat) : Bool := value == 2 ^ 64 - 100 || value == 2 ^ 32 - 100
  -- A path from an address, as an absolute one, of the directory that the call says.
  let pathAt (directory address : Nat) : IO (Result String) := do
    match kernel.baseOf group directory (atCwd directory) with
    | .error errno => pure (.error errno)
    | .ok base => pure (.ok (Path.ofParts (Path.parts base (← readString emu address))))
  -- The inode of a path, or of what a descriptor has of `AT_EMPTY_PATH` with an empty path.
  let inodeAt (directory address : Nat) (follow empty : Bool) : IO (Result Nat) := do
    if empty && (← readString emu address).isEmpty then
      return (kernel.openFileOf group directory).map (·.2.inode)
    match ← pathAt directory address with
    | .error errno => pure (.error errno)
    | .ok path =>
      match kernel.resolve "/" path follow with
      | .ok (_, some number) => pure (.ok number)
      | .ok (_, none) => pure (.error Errno.enoent)
      | .error errno => pure (.error errno)
  let ofFd (fd : Nat) : Result Nat := (kernel.openFileOf group fd).map (·.2.inode)
  let credentials := (kernel.process group).credentials
  -- Times of `timespec`, or of `timeval` of `scale` 1000, two of them, of which `UTIME_NOW` and `UTIME_OMIT` are now and none.
  let times (address field scale : Nat) : IO (Option Nat × Option Nat) := do
    if address == 0 then return (some now, some now)
    let one (at_ : Nat) : IO (Option Nat) := do
      let seconds ← do pure (numberOf big (← read emu at_ field))
      let fraction ← do pure (numberOf big (← read emu (at_ + field) field))
      pure (if scale == 1 && fraction == 0x3fffffff then some now else if scale == 1 && fraction == 0x3ffffffe then none
        else some (seconds * 1000000000 + fraction * scale))
    pure (← one address, ← one (address + 2 * field))
  let setTimes (number : Result Nat) (given : Option Nat × Option Nat) : IO (Option SyscallAction) := do
    match number with
    | .error errno => fail errno
    | .ok number =>
      poller.kernel.set (alter kernel number fun details =>
        { details with accessed := given.1.getD details.accessed, modified := given.2.getD details.modified, changed := now })
      succeed
  -- Of `chown`: -1 leaves either as it is, and only root gives a file to another, or to a group that it isn't in.
  let chown (number : Result Nat) (uid gid : Nat) : IO (Option SyscallAction) := do
    let unset := 2 ^ 32 - 1
    let (uid, gid) := (uid % 2 ^ 32, gid % 2 ^ 32)
    match number with
    | .error errno => fail errno
    | .ok number =>
      let some inode := kernel.inodes.get? number | return ← fail Errno.enoent
      let mayGive := credentials.euid == 0 ||
        ((uid == unset || uid == inode.details.uid) && credentials.euid == inode.details.uid &&
          (gid == unset || gid == credentials.egid || credentials.groups.contains gid))
      if !mayGive then return ← fail 1
      poller.kernel.set (alter kernel number fun details =>
        { details with uid := if uid == unset then details.uid else uid, gid := if gid == unset then details.gid else gid
                       changed := now })
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
  let attributesOf (number : Nat) : List (String × ByteArray) := ((kernel.inodes.get? number).map (·.details.attributes)).getD []
  let setAttribute (number : Result Nat) (nameAt valueAt size flags : Nat) : IO (Option SyscallAction) :=
    onNumber number fun number => onName nameAt fun name => do
      if size > 65536 then return ← fail e2big
      let there := (attributesOf number).any (·.1 == name)
      if flags &&& 1 != 0 && there then return ← fail Errno.eexist
      if flags &&& 2 != 0 && !there then return ← fail enodata
      let value ← read emu valueAt size
      poller.kernel.set (alter kernel number fun details =>
        { details with attributes := details.attributes.filter (·.1 != name) ++ [(name, value)], changed := now })
      succeed
  let getAttribute (number : Result Nat) (nameAt valueAt size : Nat) : IO (Option SyscallAction) :=
    onNumber number fun number => onName nameAt fun name => do
      let some (_, value) := (attributesOf number).find? (·.1 == name) | return ← fail enodata
      if size == 0 then return ← succeed value.size
      if size < value.size then return ← fail erange
      write emu valueAt value
      succeed value.size
  let listAttributes (number : Result Nat) (listAt size : Nat) : IO (Option SyscallAction) :=
    onNumber number fun number => do
      let names := (attributesOf number).foldl (fun out (name, _) => (out ++ name.toUTF8).push 0) ByteArray.empty
      if size == 0 then return ← succeed names.size
      if size < names.size then return ← fail erange
      write emu listAt names
      succeed names.size
  let removeAttribute (number : Result Nat) (nameAt : Nat) : IO (Option SyscallAction) :=
    onNumber number fun number => onName nameAt fun name => do
      if !(attributesOf number).any (·.1 == name) then return ← fail enodata
      poller.kernel.set (alter kernel number fun details =>
        { details with attributes := details.attributes.filter (·.1 != name), changed := now })
      succeed
  let here := 2 ^ 64 - 100
  try
    match call with
    | .link =>
      let .ok source ← pathAt here (arg 0) | return ← fail Errno.enoent
      let .ok target ← pathAt here (arg 1) | return ← fail Errno.enoent
      fromResult (kernel.link "/" source target false)
    | .linkat =>
      -- AT_EMPTY_PATH of a descriptor, and AT_SYMLINK_FOLLOW.
      let .ok target ← pathAt (arg 2) (arg 3) | return ← fail Errno.enoent
      if arg 4 &&& 0x1000 != 0 && (← readString emu (arg 1)).isEmpty then
        match ofFd (arg 0) with
        | .ok number => fromResult (kernel.linkInode number "/" target)
        | .error errno => fail errno
      else
        let .ok source ← pathAt (arg 0) (arg 1) | return ← fail Errno.enoent
        fromResult (kernel.link "/" source target (arg 4 &&& 0x400 != 0))
    | .renameat2 =>
      let .ok source ← pathAt (arg 0) (arg 1) | return ← fail Errno.enoent
      let .ok target ← pathAt (arg 2) (arg 3) | return ← fail Errno.enoent
      fromResult (kernel.renameWith "/" source target (arg 4))
    | .utimensat | .utimensat64 =>
      let field := if call == .utimensat64 then 8 else word
      let number ← if arg 1 == 0 then pure (ofFd (arg 0)) else inodeAt (arg 0) (arg 1) (arg 3 &&& 0x100 == 0) (arg 3 &&& 0x1000 != 0)
      setTimes number (← times (arg 2) field 1)
    | .utimes => setTimes (← inodeAt here (arg 0) true false) (← times (arg 1) word 1000)
    | .futimesat => setTimes (← inodeAt (arg 0) (arg 1) true false) (← times (arg 2) word 1000)
    | .utime =>
      let given ← if arg 1 == 0 then pure (some now, some now) else do
        pure (some ((numberOf big (← read emu (arg 1) word)) * 1000000000), some ((numberOf big (← read emu (arg 1 + word) word)) * 1000000000))
      setTimes (← inodeAt here (arg 0) true false) given
    | .chown => chown (← inodeAt here (arg 0) true false) (arg 1) (arg 2)
    | .lchown => chown (← inodeAt here (arg 0) false false) (arg 1) (arg 2)
    | .fchown => chown (ofFd (arg 0)) (arg 1) (arg 2)
    | .fchownat => chown (← inodeAt (arg 0) (arg 1) (arg 4 &&& 0x100 == 0) (arg 4 &&& 0x1000 != 0)) (arg 2) (arg 3)
    | .setxattr => setAttribute (← inodeAt here (arg 0) true false) (arg 1) (arg 2) (arg 3) (arg 4)
    | .lsetxattr => setAttribute (← inodeAt here (arg 0) false false) (arg 1) (arg 2) (arg 3) (arg 4)
    | .fsetxattr => setAttribute (ofFd (arg 0)) (arg 1) (arg 2) (arg 3) (arg 4)
    | .getxattr => getAttribute (← inodeAt here (arg 0) true false) (arg 1) (arg 2) (arg 3)
    | .lgetxattr => getAttribute (← inodeAt here (arg 0) false false) (arg 1) (arg 2) (arg 3)
    | .fgetxattr => getAttribute (ofFd (arg 0)) (arg 1) (arg 2) (arg 3)
    | .listxattr => listAttributes (← inodeAt here (arg 0) true false) (arg 1) (arg 2)
    | .llistxattr => listAttributes (← inodeAt here (arg 0) false false) (arg 1) (arg 2)
    | .flistxattr => listAttributes (ofFd (arg 0)) (arg 1) (arg 2)
    | .removexattr => removeAttribute (← inodeAt here (arg 0) true false) (arg 1)
    | .lremovexattr => removeAttribute (← inodeAt here (arg 0) false false) (arg 1)
    | .fremovexattr => removeAttribute (ofFd (arg 0)) (arg 1)
    | _ => pure none
  catch _ => fail 14

end Files

end Bap.Linux
