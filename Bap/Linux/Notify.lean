import Bap.Linux.Files

/-! # inotify

`inotify_init`, `inotify_init1`, `inotify_add_watch`, `inotify_rm_watch`, and `read` and `FIONREAD` of what they make.

What an instance has to say is found after each call, from what the call changed of the kernel: an inode whose bytes or times
changed was written (`IN_MODIFY`) or had what it is changed (`IN_ATTRIB`), a name that a directory has that it hadn't was made
(`IN_CREATE`) or moved there (`IN_MOVED_TO`, with the `IN_MOVED_FROM` of where it was), and one that went was deleted (`IN_DELETE`).
An inode that no path has any more was deleted itself (`IN_DELETE_SELF`), and its watch goes (`IN_IGNORED`). A call says what the
changes don't: that a file was opened (`IN_OPEN`), read (`IN_ACCESS`), or closed for the last time (`IN_CLOSE_WRITE` and
`IN_CLOSE_NOWRITE`). As Linux has it, a directory hears of what happens to what is in it, with its name, before the inode hears of it
itself, and what is said again before it is read is said once.

That a write changed a file is that its bytes are others: while an instance has a watch, a write doesn't change them in place. -/

namespace Bap.Linux

open Bap.Emu Bap.Tasks

namespace Notify

private unsafe def sameObjectImpl {α : Type} (left right : α) : Bool := ptrAddrUnsafe left == ptrAddrUnsafe right

/-- Whether two values are the same object, which is that nothing changed one into the other. -/
@[implemented_by sameObjectImpl] private def sameObject {α : Type} (_ _ : α) : Bool := false

def inAccess : Nat := 0x1
def inModify : Nat := 0x2
def inAttrib : Nat := 0x4
def inCloseWrite : Nat := 0x8
def inCloseNowrite : Nat := 0x10
def inOpen : Nat := 0x20
def inMovedFrom : Nat := 0x40
def inMovedTo : Nat := 0x80
def inCreate : Nat := 0x100
def inDelete : Nat := 0x200
def inDeleteSelf : Nat := 0x400
def inMoveSelf : Nat := 0x800
def inOverflow : Nat := 0x4000
def inIgnored : Nat := 0x8000
def inIsdir : Nat := 0x40000000
def inOneshot : Nat := 0x80000000

/-- What an instance has unread at most, past which it says that there was more. -/
def queueLimit : Nat := 16384

/-- What finds out what instances have to say: the inodes of those that there are, once they have been looked for, and of each
directory that is watched, its path and what is in it, as of the paths of the kernel that they were found in. -/
structure Notifier where
  instances : IO.Ref (Option (List Nat))
  entries : IO.Ref (Std.HashMap Nat (Std.HashMap String Nat × Option String × List (String × Nat)))

def make : IO Notifier := do pure { instances := ← IO.mkRef none, entries := ← IO.mkRef {} }

/-- The instances of a kernel, from what was found of them before, if it was. -/
def instancesOf (notifier : Notifier) (kernel : Kernel) : IO (List Nat) := do
  if let some found ← notifier.instances.get then return found
  let found := kernel.inodes.fold (init := []) fun found number inode =>
    match inode.content with
    | .inotify .. => number :: found
    | _ => found
  notifier.instances.set (some found)
  pure found

/-- What is known of the instances is not of the kernel there is now, as a checkpoint was restored. -/
def forget (notifier : Notifier) : IO Unit := do
  notifier.instances.set none
  notifier.entries.set {}

/-- An instance has this to say of what one of its watches watches, unless the watch isn't to hear of it. A watch of `IN_ONESHOT` goes
once it has said something. -/
def tell (kernel : Kernel) (listener : Nat) (inode mask : Nat) (name : String := "") (cookie : Nat := 0) : Kernel :=
  match kernel.inodes.get? listener with
  | some entry@{ content := .inotify watches notices next cookies, .. } =>
    let (watches, notices) := watches.foldl (init := (([] : List Watch), notices)) fun (kept, notices) watch =>
      if watch.inode != inode || (watch.mask &&& mask &&& 0xfff == 0 && mask != inIgnored) then (kept ++ [watch], notices)
      else
        let add (notices : Array Notice) (notice : Notice) : Array Notice :=
          if notices.back? == some notice then notices
          else if notices.size ≥ queueLimit then
            if notices.back?.any (·.mask == inOverflow) then notices else notices.push { wd := 2 ^ 32 - 1, mask := inOverflow }
          else notices.push notice
        let notices := add notices { wd := watch.wd, mask, cookie, name }
        if watch.mask &&& inOneshot != 0 && mask != inIgnored then (kept, add notices { wd := watch.wd, mask := inIgnored })
        else (kept ++ [watch], notices)
    { kernel with inodes := kernel.inodes.insert listener { entry with content := .inotify watches notices next cookies } }
  | _ => kernel

/-- An instance has no watch of an inode any more, which it says. -/
def unwatch (kernel : Kernel) (listener inode : Nat) : Kernel :=
  let kernel := tell kernel listener inode inIgnored
  match kernel.inodes.get? listener with
  | some entry@{ content := .inotify watches notices next cookies, .. } =>
    let content := Content.inotify (watches.filter (·.inode != inode)) notices next cookies
    { kernel with inodes := kernel.inodes.insert listener { entry with content } }
  | _ => kernel

private def watchesOf (kernel : Kernel) (listener : Nat) : List Watch :=
  match kernel.inodes.get? listener with
  | some { content := .inotify watches .., .. } => watches
  | _ => []

private def isDirectory (inode : Option Inode) : Bool :=
  match inode with
  | some { content := .directory, .. } => true
  | _ => false

/-- What changed of an inode from one kernel to the other: its bytes or when it was written, which is `IN_MODIFY`, or else what it
is, which is `IN_ATTRIB`, or nothing. -/
private def changeOf (before after : Option Inode) : Nat :=
  match before, after with
  | some old, some new =>
    if sameObject old new then 0
    else
      let written := match old.content, new.content with
        | .file data, .file data' => !sameObject data data'
        | _, _ => false
      if written || old.details.modified != new.details.modified then inModify
      else if old.mode != new.mode || old.details.uid != new.details.uid || old.details.gid != new.details.gid ||
          old.details.changed != new.details.changed || old.details.accessed != new.details.accessed ||
          old.details.attributes.length != new.details.attributes.length ||
          (old.details.attributes.zip new.details.attributes).any (fun ((name, value), (name', value')) => name != name' || value.data != value'.data) then
        inAttrib
      else 0
  | _, _ => 0

/-- The path and the entries of a directory, from what was found of them before if the paths are those that they were found in. -/
private def entriesOf (notifier : Notifier) (kernel : Kernel) (directory : Nat) : IO (Option String × List (String × Nat)) := do
  if let some (paths, path, entries) := (← notifier.entries.get).get? directory then
    if sameObject paths kernel.paths then return (path, entries)
  let path := kernel.pathOfInode directory
  let entries := match path with
    | some path => kernel.children path
    | none => []
  notifier.entries.modify (·.insert directory (kernel.paths, path, entries))
  pure (path, entries)

/-- How many paths each inode has. -/
private def linkCounts (kernel : Kernel) : Std.HashMap Nat Nat :=
  kernel.paths.fold (init := {}) fun counts path number =>
    if path.startsWith "/" then counts.insert number (counts.getD number 0 + 1) else counts

/-- What the instances have to say of what a call did, from the kernel before it to that after it, as `after`. -/
def after (notifier : Notifier) (kernelRef : IO.Ref Kernel) (group : Nat) (call : Call) (args : List Nat) (before : Kernel)
    (action : SyscallAction) (live : List Nat) : IO Bool := do
  let after ← kernelRef.get
  let instances ← instancesOf notifier after
  if instances.isEmpty then return false
  -- An instance that no descriptor has is gone, with its watches.
  let instances ← if [Call.close, .dup2, .dup3, .execve].contains call then do
      let held := instances.filter fun listener => live.any fun owner =>
        (after.process owner).descriptors.toList.any fun (_, descriptor) =>
          (after.openFiles.get? descriptor.openFile).any (·.inode == listener)
      notifier.instances.set (some held)
      pure held
    else pure instances
  let watches := instances.flatMap fun listener => (watchesOf after listener).map (listener, ·)
  if watches.isEmpty then return false
  let pathsChanged := !sameObject before.paths after.paths
  let inodesChanged := !sameObject before.inodes after.inodes
  let result := match action with
    | .returnValue value => if value < 2 ^ 63 then some value else none
    | _ => none
  let arg (index : Nat) : Nat := args.getD index 0
  -- The inode that the call is about, and what it says of it: of a descriptor that it made, read, or closed for the last time.
  let ofCall : Option (Nat × Nat) := match call, result with
    | .open_, some fd | .openat, some fd =>
      (after.openFileOf group fd).toOption.map fun (_, file) => (file.inode, inOpen)
    | .read, some count | .readv, some count | .pread, some count =>
      if count == 0 then none else (after.openFileOf group (arg 0)).toOption.map fun (_, file) => (file.inode, inAccess)
    | .close, some _ =>
      (before.openFileOf group (arg 0)).toOption.bind fun (id, file) =>
        let open_ := live.any fun owner => (after.process owner).descriptors.toList.any (·.2.openFile == id)
        if open_ then none else some (file.inode, if file.flags &&& 3 != 0 then inCloseWrite else inCloseNowrite)
    | _, _ => none
  if !pathsChanged && !inodesChanged && ofCall.isNone then return false
  let directories := (watches.filter fun (_, watch) => isDirectory (after.inodes.get? watch.inode) || isDirectory (before.inodes.get? watch.inode)).map
    (·.2.inode) |>.eraseDups
  -- What was found of directories that aren't watched any more isn't kept.
  if (← notifier.entries.get).size > directories.length then
    notifier.entries.modify (·.filter fun directory _ => directories.contains directory)
  let mut entriesBefore : Std.HashMap Nat (List (String × Nat)) := {}
  let mut entriesAfter : Std.HashMap Nat (List (String × Nat)) := {}
  for directory in directories do
    entriesAfter := entriesAfter.insert directory (← entriesOf notifier after directory).2
    entriesBefore := entriesBefore.insert directory (if pathsChanged then before.children ((before.pathOfInode directory).getD "") else entriesAfter.getD directory [])
  let mut kernel := after
  -- What happens to an inode is said to each directory that has it, with its name, and then to the inode.
  let say (kernel : Kernel) (inode mask : Nat) (entries : Std.HashMap Nat (List (String × Nat))) (toParents : Bool) : Kernel :=
    let mask := if isDirectory (after.inodes.get? inode) || isDirectory (before.inodes.get? inode) then mask ||| inIsdir else mask
    let kernel := if !toParents then kernel else
      directories.foldl (init := kernel) fun kernel directory =>
        ((entries.getD directory []).filter (·.2 == inode)).foldl (init := kernel) fun kernel (name, _) =>
          instances.foldl (init := kernel) fun kernel listener => tell kernel listener directory mask name
    instances.foldl (init := kernel) fun kernel listener => tell kernel listener inode mask
  -- What changed of the inodes that are watched or in a directory that is.
  let (counts, counts') := if pathsChanged then (linkCounts before, linkCounts after) else ({}, {})
  if inodesChanged || pathsChanged then
    let candidates := (watches.map (·.2.inode) ++ directories.flatMap fun directory =>
      ((entriesBefore.getD directory []) ++ (entriesAfter.getD directory [])).map (·.2)).eraseDups
    for inode in candidates do
      let change := if inodesChanged then changeOf (before.inodes.get? inode) (after.inodes.get? inode) else 0
      if change != 0 then kernel := say kernel inode change entriesAfter true
      -- A link more or less is said to the inode alone.
      else if pathsChanged && counts.getD inode 0 != counts'.getD inode 0 &&
          !isDirectory (after.inodes.get? inode) && !(call == .rename || call == .renameat || call == .renameat2) then
        kernel := say kernel inode inAttrib entriesAfter false
  -- What is watched and has no path any more was deleted, and isn't watched, before its directory hears that its name went.
  if pathsChanged then
    for inode in (watches.map (·.2.inode)).eraseDups do
      if counts'.getD inode 0 == 0 && counts.getD inode 0 > 0 then
        kernel := say kernel inode inDeleteSelf {} false
        kernel := instances.foldl (init := kernel) fun kernel listener => unwatch kernel listener inode
  -- Names that directories have that they hadn't, and that they had that they haven't: of `rename`, the two sides of a move, after which
  -- what moved and is watched hears of it.
  if pathsChanged then
    let moving := call == .rename || call == .renameat || call == .renameat2
    let cookie := after.clock % 2 ^ 32
    let mut moved : List Nat := []
    for directory in directories do
      let old := entriesBefore.getD directory []
      let new := entriesAfter.getD directory []
      for (name, inode) in old do
        if !new.contains (name, inode) then
          let isDir := if isDirectory (before.inodes.get? inode) then inIsdir else 0
          let elsewhere := moving && directories.any fun other => ((entriesAfter.getD other []).any (·.2 == inode)) ||
            counts'.getD inode 0 > 0
          if elsewhere && moving then
            moved := inode :: moved
            kernel := instances.foldl (init := kernel) fun kernel listener => tell kernel listener directory (inMovedFrom ||| isDir) name cookie
          else kernel := instances.foldl (init := kernel) fun kernel listener => tell kernel listener directory (inDelete ||| isDir) name
    for directory in directories do
      let old := entriesBefore.getD directory []
      let new := entriesAfter.getD directory []
      for (name, inode) in new do
        if !old.contains (name, inode) then
          let isDir := if isDirectory (after.inodes.get? inode) then inIsdir else 0
          let wasThere := counts.getD inode 0 > 0
          if moving && wasThere then
            kernel := instances.foldl (init := kernel) fun kernel listener => tell kernel listener directory (inMovedTo ||| isDir) name cookie
          else kernel := instances.foldl (init := kernel) fun kernel listener => tell kernel listener directory (inCreate ||| isDir) name
    if moving then
      for inode in (watches.map (·.2.inode)).eraseDups do
        if counts'.getD inode 0 > 0 && before.pathOfInode inode != after.pathOfInode inode then
          kernel := say kernel inode inMoveSelf {} false
  if let some (inode, mask) := ofCall then kernel := say kernel inode mask entriesAfter true
  let told := instances.any fun listener =>
    match before.inodes.get? listener, kernel.inodes.get? listener with
    | some { content := .inotify _ notices .., .. }, some { content := .inotify _ notices' .., .. } => notices.size != notices'.size
    | _, _ => true
  kernelRef.set kernel
  pure told

/-- The bytes of what an instance says, as `struct inotify_event`, whose name is padded with zeros to a multiple of 16. -/
private def noticeBytes (big : Bool) (notice : Notice) : ByteArray :=
  let name := notice.name.toUTF8
  let length := if name.isEmpty then 0 else (name.size + 1 + 15) / 16 * 16
  Abi.field big 4 notice.wd ++ Abi.field big 4 notice.mask ++ Abi.field big 4 notice.cookie ++ Abi.field big 4 length ++ name ++
    Bap.zeroBytes (length - name.size)

/-- The calls of this module, and `read` and `FIONREAD` of what they make, if the call is one of them. -/
def serve (notifier : Notifier) (poller : Poller) (emu : Emu) (call : Call) (args : List Nat) : IO (Option SyscallAction) := do
  let architecture := poller.architecture
  let big := architecture.big
  let arg (index : Nat) : Nat := args.getD index 0
  let group := (← currentTask emu).group
  let kernel ← poller.kernel.get
  let fail (errno : Nat) : IO (Option SyscallAction) := do pure (some (← syscallReturn emu (.error errno)))
  let succeed (value : Nat := 0) : IO (Option SyscallAction) := do pure (some (← syscallReturn emu (.ok value)))
  let listener (fd : Nat) : Except Nat (Nat × List Watch × Array Notice × Nat × Nat) :=
    match kernel.objectOf group fd with
    | .ok (number, _, { content := .inotify watches notices next cookies, .. }) => .ok (number, watches, notices, next, cookies)
    | .ok _ => .error Errno.einval
    | .error errno => .error errno
  match call with
  | .inotifyInit | .inotifyInit1 =>
    -- `IN_NONBLOCK` and `IN_CLOEXEC`, which are those of `open`.
    let flags := architecture.openFlags (if call == .inotifyInit then 0 else arg 0)
    if flags - (flags &&& (Kernel.oNonblock ||| Kernel.oCloexec)) != 0 then return ← fail Errno.einval
    let (next, fd) := kernel.addObject group (.inotify [] #[] 1 1) flags
    poller.kernel.set next
    notifier.instances.modify (·.map ((next.nextInode - 1) :: ·))
    succeed fd
  | .inotifyAddWatch =>
    let .ok (number, watches, notices, next, cookies) := listener (arg 0) | return ← fail (match listener (arg 0) with | .error e => e | _ => 22)
    let mask := arg 2 % 2 ^ 32
    -- `IN_MASK_ADD` and `IN_MASK_CREATE` don't go together, and something is to be heard of.
    if mask &&& 0xfff == 0 || (mask &&& 0x20000000 != 0 && mask &&& 0x10000000 != 0) then return ← fail Errno.einval
    let path ← try pure (some (← Files.readString emu (arg 1))) catch _ => pure none
    let some path := path | return ← fail Errno.efault
    let found := kernel.resolve (kernel.process group).cwd path (follow := mask &&& 0x02000000 == 0)
    let inode ← match found with
      | .ok (_, some inode) => pure inode
      | .ok (_, none) => return ← fail Errno.enoent
      | .error errno => return ← fail errno
    if mask &&& 0x01000000 != 0 && !isDirectory (kernel.inodes.get? inode) then return ← fail Errno.enotdir
    let kept := mask &&& (0xfff ||| inOneshot)
    match watches.find? (·.inode == inode) with
    | some watch =>
      if mask &&& 0x10000000 != 0 then return ← fail Errno.eexist
      let mask := if mask &&& 0x20000000 != 0 then watch.mask ||| kept else kept
      poller.kernel.set (kernel.setContent number (.inotify (watches.map fun other => if other.wd == watch.wd then { other with mask } else other)
        notices next cookies))
      succeed watch.wd
    | none =>
      poller.kernel.set (kernel.setContent number (.inotify (watches ++ [{ wd := next, inode, mask := kept }]) notices (next + 1) cookies))
      notifier.instances.modify fun found => found.map fun found => if found.contains number then found else number :: found
      succeed next
  | .inotifyRmWatch =>
    let .ok (number, watches, _, _, _) := listener (arg 0) | return ← fail (match listener (arg 0) with | .error e => e | _ => 22)
    let some watch := watches.find? (·.wd == arg 1 % 2 ^ 32) | return ← fail Errno.einval
    poller.kernel.set (unwatch kernel number watch.inode)
    poller.wake emu
    succeed
  | .read =>
    let .ok (number, watches, notices, next, cookies) := listener (arg 0) | return none
    if notices.isEmpty then
      if kernel.nonblocking group (arg 0) then return ← fail Errno.eagain
      return some (← poller.timers.waitUntil emu readySpace 0 none true)
    let mut out := ByteArray.empty
    let mut taken := 0
    for notice in notices do
      let bytes := noticeBytes big notice
      if out.size + bytes.size > arg 2 then break
      out := out ++ bytes
      taken := taken + 1
    if taken == 0 then return ← fail Errno.einval
    write emu (arg 1) out
    poller.kernel.set (kernel.setContent number (.inotify watches (notices.extract taken notices.size) next cookies))
    succeed out.size
  | .ioctl =>
    let fionread := match architecture with
      | .mips .. => 0x467f
      | .powerpc .. => 0x4004667f
      | _ => 0x541b
    if arg 1 % 2 ^ 32 != fionread then return none
    let .ok (_, _, notices, _, _) := listener (arg 0) | return none
    write emu (arg 2) (Abi.field big 4 (notices.foldl (fun total notice => total + (noticeBytes big notice).size) 0))
    succeed
  | _ => pure none

end Notify

end Bap.Linux
