import Bap.Linux.Poll

/-! # SysV IPC

Shared memory (`shmget`, `shmat`, `shmdt`, `shmctl`), semaphores (`semget`, `semop`, `semtimedop`, `semctl`) and message queues
(`msgget`, `msgsnd`, `msgrcv`, `msgctl`), and `ipc`, which is all of them where the libc calls that.

A segment is an inode that each attachment is a shared mapping of, as `mmap` of `MAP_SHARED` has it, and it lasts after `IPC_RMID`
as long as something has it attached. `semop` does all of what it is given or none of it, and waits until it can, as `msgsnd` waits
for room and `msgrcv` for a message; none of them runs again after a handler of a signal. What `SEM_UNDO` did is taken back when its
process ends. `IPC_STAT` and `IPC_SET` have the structures of the generic 64-bit and 32-bit layouts, with x86-64's own of
semaphores; those of MIPS and PowerPC are not these. Modes are kept and not enforced. -/

namespace Bap.Linux

open Bap.Emu Bap.Tasks

namespace SysV

def ipcCreat : Nat := 0o1000
def ipcExcl : Nat := 0o2000
def ipcNowait : Nat := 0o4000

/-- How many attachments a segment has: the mappings of its inode that processes have. -/
def attached (kernel : Kernel) (segment : Segment) : Nat :=
  kernel.processes.fold (init := 0) fun count _ process => count + (process.mappings.filter (·.inode == segment.inode)).length

/-- A kernel without the segments that `IPC_RMID` took away that nothing has attached, nor their inodes. -/
def collect (kernel : Kernel) : Kernel :=
  if !kernel.ipc.segments.any (·.removed) then kernel
  else
    let (gone, kept) := kernel.ipc.segments.partition fun segment => segment.removed && attached kernel segment == 0
    { kernel with ipc := { kernel.ipc with segments := kept }, inodes := gone.foldl (fun inodes segment => inodes.erase segment.inode) kernel.inodes }

/-- What a process takes back of what `SEM_UNDO` did, as it ends. -/
def exited (kernel : Kernel) (group : Nat) : Kernel :=
  let (mine, others) := kernel.ipc.undo.partition (·.1 == group)
  if mine.isEmpty then collect kernel
  else
    let sets := kernel.ipc.sets.map fun set =>
      let values := (List.range set.values.length).map fun number =>
        let change := mine.foldl (fun total (_, id, which, change) => if id == set.id && which == number then total + change else total) 0
        let value : Int := (set.values.getD number 0 : Int) + change
        (max 0 (min value 32767)).toNat
      { set with values }
    collect { kernel with ipc := { kernel.ipc with sets, undo := others } }

/-- Of `*get`: the object of `key` that there is, or none to make one, or why neither. -/
private def keyed (key flags : Nat) (known : List (Nat × Nat)) : Except Nat (Option Nat) :=
  if key == 0 then .ok none
  else
    match known.find? (·.1 == key) with
    | some (_, id) => if flags &&& ipcCreat != 0 && flags &&& ipcExcl != 0 then .error Errno.eexist else .ok (some id)
    | none => if flags &&& ipcCreat != 0 then .ok none else .error Errno.enoent

private def numberOf (big : Bool) (bytes : ByteArray) : Nat :=
  let ordered := if big then bytes.toList else bytes.toList.reverse
  ordered.foldl (fun value byte => value * 256 + byte.toNat) 0

/-- The calls of SysV IPC, if the call is one of them. -/
partial def serve (poller : Poller) (emu : Emu) (call : Call) (args : List Nat) : IO (Option SyscallAction) := do
  let architecture := poller.architecture
  let big := architecture.big
  let wide := architecture.bits == 64
  let word := if wide then 8 else 4
  let arg (index : Nat) : Nat := args.getD index 0
  let tid ← thread emu
  let group := (← currentTask emu).group
  let kernel := collect (← poller.kernel.get)
  let ipc := kernel.ipc
  let now := kernel.clock
  let seconds := now / 1000000000
  let fail (errno : Nat) : IO (Option SyscallAction) := do pure (some (.returnValue (2 ^ 64 - errno)))
  let succeed (value : Nat := 0) : IO (Option SyscallAction) := do pure (some (.returnValue value))
  let save (ipc : Ipc) (kernel : Kernel := kernel) : IO Unit := poller.kernel.set { kernel with ipc }
  let number (address size : Nat) : IO Nat := do pure (numberOf big (← read emu address size))
  let field := Abi.field big
  let credentials := (kernel.process group).credentials
  let permOf (key flags : Nat) : IpcPerm :=
    { key, uid := credentials.euid, gid := credentials.egid, cuid := credentials.euid, cgid := credentials.egid, mode := flags &&& 0o777 }
  -- `struct ipc64_perm`, of 48 bytes on 64 bits and of 36 on 32, with what is added to its mode.
  let permBytes (perm : IpcPerm) (more : Nat) : ByteArray :=
    let ids := field 4 perm.key ++ field 4 perm.uid ++ field 4 perm.gid ++ field 4 perm.cuid ++ field 4 perm.cgid
    if wide then ids ++ field 4 (perm.mode ||| more) ++ field 2 0 ++ field 2 0 ++ field 4 0 ++ field 8 0 ++ field 8 0
    else ids ++ field 2 (perm.mode ||| more) ++ field 2 0 ++ field 2 0 ++ field 2 0 ++ field 4 0 ++ field 4 0
  let permSize := if wide then 48 else 36
  -- A time of seconds, which 32 bits have in two words.
  let time (value : Nat) : ByteArray := if wide then field 8 value else field 4 value ++ field 4 (value / 2 ^ 32)
  let long (value : Nat) : ByteArray := field word value
  -- What `IPC_SET` sets of a perm: the owner, and the bits of the mode that are for anyone.
  let setPerm (address : Nat) (perm : IpcPerm) : IO IpcPerm := do
    let mode ← number (address + 20) (if wide then 4 else 2)
    pure { perm with uid := ← number (address + 4) 4, gid := ← number (address + 8) 4, mode := mode &&& 0o777 }
  -- A timeout of a `timespec`, of which none is none, or none at all of one that Linux doesn't take.
  let timeout (address : Nat) (size : Nat := word) : IO (Option (Option Nat)) := do
    if address == 0 then return some none
    let some span ← readSpan emu address size | return none
    pure (some (some (← poller.timers.deadlineOf tid (pure (now + span)))))
  let wait (due : Option Nat) : IO (Option SyscallAction) := do
    pure (some (← poller.timers.waitUntil emu readySpace 0 due false))
  -- What isn't there any more, to a call that waited for it, was taken away: `EIDRM`.
  let gone : IO (Option SyscallAction) := do
    let removed ← poller.timers.again emu
    poller.timers.finish tid
    fail (if removed then 43 else Errno.einval)
  let shmget (key size flags : Nat) : IO (Option SyscallAction) := do
    match keyed key flags (ipc.segments.filter (!·.removed) |>.map fun segment => (segment.perm.key, segment.id)) with
    | .error errno => fail errno
    | .ok (some id) =>
      let some segment := ipc.segments.find? (·.id == id) | fail Errno.einval
      if size > segment.size then fail Errno.einval else succeed id
    | .ok none =>
      if size == 0 || size ≥ 2 ^ 48 then return ← fail Errno.einval
      let (kernel, inode) := kernel.anonymousInode (Bap.zeroBytes ((size + 4095) / 4096 * 4096))
      let id := ipc.made.1
      save { ipc with segments := ipc.segments ++ [{ id, perm := permOf key flags, inode, size, cpid := group, ctime := seconds }]
                      made := (id + 1, ipc.made.2) } kernel
      succeed id
  let shmat (id address flags : Nat) : IO (Except Nat Nat) := do
    let some segment := ipc.segments.find? (·.id == id) | return .error Errno.einval
    -- `SHM_RND` rounds down to a page, and otherwise what isn't on one is wrong.
    let address ← if address % 4096 == 0 then pure address
      else if flags &&& 0x2000 != 0 then pure (address - address % 4096) else return .error Errno.einval
    let readOnly := flags &&& 0x1000 != 0
    let size := (segment.size + 4095) / 4096 * 4096
    let bits := 1 ||| (if readOnly then 0 else 2) ||| (if flags &&& 0x8000 != 0 then 4 else 0)
    try
      let start ← placeMapping emu address (address != 0) (kernel.inodeBytes segment.inode 0 size) bits
      let kernel := (kernel.dropMappings group start (start + size)).addMapping group
        { start, size, inode := segment.inode, offset := 0, shared := true, mayWrite := !readOnly }
      save { ipc with segments := ipc.segments.map fun other => if other.id == id then { other with atime := seconds, lpid := group } else other } kernel
      pure (.ok start)
    catch _ => pure (.error Errno.enomem)
  let shmdt (address : Nat) : IO (Option SyscallAction) := do
    let mappings := (kernel.process group).mappings
    let some first := mappings.find? fun mapping => mapping.start == address && ipc.segments.any (·.inode == mapping.inode)
      | fail Errno.einval
    let some segment := ipc.segments.find? (·.inode == first.inode) | fail Errno.einval
    let stop := address + (segment.size + 4095) / 4096 * 4096
    let mut kernel := kernel
    for mapping in mappings do
      if mapping.inode == segment.inode && address ≤ mapping.start && mapping.start < stop then
        unmap emu mapping.start mapping.size
        kernel := kernel.dropMappings group mapping.start (mapping.start + mapping.size)
    let ipc := { ipc with segments := ipc.segments.map fun other => if other.id == segment.id then { other with dtime := seconds, lpid := group } else other }
    poller.kernel.set (collect { kernel with ipc })
    succeed
  let shmctl (id command address : Nat) : IO (Option SyscallAction) := do
    let some segment := ipc.segments.find? (·.id == id) | fail Errno.einval
    match command % 256 with
    | 0 =>
      save { ipc with segments := ipc.segments.map fun other =>
        if other.id == id then { other with removed := true, perm := { other.perm with key := 0 }, ctime := seconds } else other }
      poller.kernel.modify collect
      succeed
    | 1 =>
      let perm ← setPerm address segment.perm
      save { ipc with segments := ipc.segments.map fun other => if other.id == id then { other with perm, ctime := seconds } else other }
      succeed
    | 2 =>
      -- `SHM_DEST` of what `IPC_RMID` took away.
      write emu address (permBytes segment.perm (if segment.removed then 0o1000 else 0) ++ long segment.size ++ time segment.atime ++
        time segment.dtime ++ time segment.ctime ++ field 4 segment.cpid ++ field 4 segment.lpid ++ long (attached kernel segment) ++
        long 0 ++ long 0)
      succeed
    | 11 | 12 => succeed
    | _ => fail Errno.einval
  let semget (key count flags : Nat) : IO (Option SyscallAction) := do
    match keyed key flags (ipc.sets.map fun set => (set.perm.key, set.id)) with
    | .error errno => fail errno
    | .ok (some id) =>
      let some set := ipc.sets.find? (·.id == id) | fail Errno.einval
      if count > set.values.length then fail Errno.einval else succeed id
    | .ok none =>
      if count == 0 || count > 32000 then return ← fail Errno.einval
      let id := ipc.made.2.1
      save { ipc with sets := ipc.sets ++ [{ id, perm := permOf key flags, values := List.replicate count 0, pids := List.replicate count 0
                                             ctime := seconds }]
                      made := (ipc.made.1, id + 1, ipc.made.2.2) }
      succeed id
  -- Of a timeout that Linux doesn't take, `EINVAL`, once the operations are read and before the set is looked for.
  let semop (id address count : Nat) (due : Option (Option Nat)) : IO (Option SyscallAction) := do
    if count == 0 then return ← fail Errno.einval
    if count > 500 then return ← fail 7
    let bytes ← read emu address (6 * count)
    let some due := due | fail Errno.einval
    let some set := ipc.sets.find? (·.id == id) | gone
    let operations := (List.range count).map fun index =>
      let at_ := 6 * index
      let signed (value : Nat) : Int := if value ≥ 2 ^ 15 then (value : Int) - 2 ^ 16 else value
      (numberOf big (bytes.extract at_ (at_ + 2)), signed (numberOf big (bytes.extract (at_ + 2) (at_ + 4))),
        numberOf big (bytes.extract (at_ + 4) (at_ + 6)) % 2 ^ 16)
    if operations.any (·.1 ≥ set.values.length) then return ← fail 27
    -- All of them, from the values that there are, or the first that has to wait, and whether it waits.
    let mut values := set.values
    let mut blocked : Option Bool := none
    for (which, change, flags) in operations do
      let value := values.getD which 0
      if change > 0 then
        if value + change.toNat > 32767 then return ← fail Errno.erange
        values := values.set which (value + change.toNat)
      else if change == 0 then
        if value != 0 then
          blocked := some (flags &&& ipcNowait != 0)
          break
      else if value ≥ change.natAbs then values := values.set which (value - change.natAbs)
      else
        blocked := some (flags &&& ipcNowait != 0)
        break
    match blocked with
    | some true =>
      poller.timers.finish tid
      fail Errno.eagain
    | some false =>
      if due.any (· ≤ now) then
        poller.timers.finish tid
        fail Errno.eagain
      else wait due
    | none =>
      poller.timers.finish tid
      let touched := operations.map (·.1)
      let pids := set.pids.zipIdx.map fun (pid, which) => if touched.contains which then group else pid
      let undo := operations.foldl (init := ipc.undo) fun undo (which, change, flags) =>
        if flags &&& 0x1000 == 0 || change == 0 then undo
        else
          match undo.find? fun (owner, setId, number, _) => owner == group && setId == id && number == which with
          | some entry => undo.map fun other => if other == entry then (group, id, which, entry.2.2.2 - change) else other
          | none => undo ++ [(group, id, which, -change)]
      save { ipc with sets := ipc.sets.map (fun other => if other.id == id then { other with values, pids, otime := seconds } else other), undo }
      poller.wake emu
      succeed
  let semctl (id which command value : Nat) : IO (Option SyscallAction) := do
    let some set := ipc.sets.find? (·.id == id) | fail Errno.einval
    let update (change : SemaphoreSet → SemaphoreSet) (undo : List (Nat × Nat × Nat × Int) := ipc.undo) : IO Unit :=
      save { ipc with sets := ipc.sets.map (fun other => if other.id == id then change other else other), undo }
    let single : IO Bool := pure (which < set.values.length)
    match command % 256 with
    | 0 =>
      save { ipc with sets := ipc.sets.filter (·.id != id), undo := ipc.undo.filter (·.2.1 != id) }
      poller.wake emu
      succeed
    | 1 =>
      let perm ← setPerm value set.perm
      update fun other => { other with perm, ctime := seconds }
      succeed
    | 2 =>
      let x86 := architecture matches .x86_64
      write emu value (permBytes set.perm 0 ++
        (if x86 then time set.otime ++ long 0 ++ time set.ctime ++ long 0 else time set.otime ++ time set.ctime) ++
        long set.values.length ++ long 0 ++ long 0)
      succeed
    | 11 => if ← single then succeed (set.pids.getD which 0) else fail Errno.einval
    | 12 => if ← single then succeed (set.values.getD which 0) else fail Errno.einval
    | 13 =>
      write emu value (set.values.foldl (fun out value => out ++ field 2 value) ByteArray.empty)
      succeed
    | 14 | 15 => if ← single then succeed 0 else fail Errno.einval
    | 16 =>
      if !(← single) then return ← fail Errno.einval
      let value := value % 2 ^ 32
      if value > 32767 then return ← fail Errno.erange
      update (fun other => { other with values := other.values.set which value, pids := other.pids.set which group, ctime := seconds })
        (ipc.undo.filter fun (_, setId, number, _) => setId != id || number != which)
      poller.wake emu
      succeed
    | 17 =>
      let bytes ← read emu value (2 * set.values.length)
      let values := (List.range set.values.length).map fun index => numberOf big (bytes.extract (2 * index) (2 * index + 2))
      if values.any (· > 32767) then return ← fail Errno.erange
      update (fun other => { other with values, pids := other.pids.map fun _ => group, ctime := seconds }) (ipc.undo.filter (·.2.1 != id))
      poller.wake emu
      succeed
    | _ => fail Errno.einval
  let msgget (key flags : Nat) : IO (Option SyscallAction) := do
    match keyed key flags (ipc.queues.map fun queue => (queue.perm.key, queue.id)) with
    | .error errno => fail errno
    | .ok (some id) => succeed id
    | .ok none =>
      let id := ipc.made.2.2
      save { ipc with queues := ipc.queues ++ [{ id, perm := permOf key flags, ctime := seconds }], made := (ipc.made.1, ipc.made.2.1, id + 1) }
      succeed id
  let msgsnd (id address size flags : Nat) : IO (Option SyscallAction) := do
    let some queue := ipc.queues.find? (·.id == id) | gone
    if size > 8192 then return ← fail Errno.einval
    let type ← number address word
    if type == 0 || type ≥ 2 ^ (8 * word - 1) then return ← fail Errno.einval
    let held := queue.messages.foldl (fun total (_, text) => total + text.size) 0
    if held + size > queue.qbytes then
      if flags &&& ipcNowait != 0 then return ← fail Errno.eagain
      return ← wait none
    let text ← read emu (address + word) size
    save { ipc with queues := ipc.queues.map fun other =>
      if other.id == id then { other with messages := other.messages ++ [(type, text)], stime := seconds, lspid := group } else other }
    poller.wake emu
    succeed
  let msgrcv (id address size type flags : Nat) : IO (Option SyscallAction) := do
    let some queue := ipc.queues.find? (·.id == id) | gone
    if size ≥ 2 ^ (8 * word - 1) then return ← fail Errno.einval
    let signed : Int := if type ≥ 2 ^ (8 * word - 1) then (type : Int) - 2 ^ (8 * word) else type
    let except := flags &&& 0o20000 != 0
    -- `MSG_COPY` takes a copy of the message at that place, which stays.
    let copy := flags &&& 0o40000 != 0
    if copy && (except || flags &&& ipcNowait == 0) then return ← fail Errno.einval
    let indexed := queue.messages.zipIdx
    let chosen : Option ((Nat × ByteArray) × Nat) :=
      if copy then indexed[signed.toNat]?
      else if signed == 0 then indexed.head?
      else if signed > 0 then indexed.find? fun ((kind, _), _) => if except then kind != signed.toNat else kind == signed.toNat
      else
        -- The lowest type up to the bound, the first of it.
        let fitting := indexed.filter fun ((kind, _), _) => kind ≤ signed.natAbs
        fitting.foldl (fun best entry => match best with
          | some current => if entry.1.1 < current.1.1 then some entry else best
          | none => some entry) none
    match chosen with
    | none =>
      -- `ENOMSG`.
      if flags &&& ipcNowait != 0 then return ← fail 42
      wait none
    | some ((kind, text), index) =>
      if text.size > size && flags &&& 0o10000 == 0 then return ← fail 7
      let taken := text.extract 0 size
      write emu address (field word kind ++ taken)
      if !copy then
        save { ipc with queues := ipc.queues.map fun other =>
          if other.id == id then { other with messages := other.messages.eraseIdx index, rtime := seconds, lrpid := group } else other }
        poller.wake emu
      succeed taken.size
  let msgctl (id command address : Nat) : IO (Option SyscallAction) := do
    let some queue := ipc.queues.find? (·.id == id) | fail Errno.einval
    match command % 256 with
    | 0 =>
      save { ipc with queues := ipc.queues.filter (·.id != id) }
      poller.wake emu
      succeed
    | 1 =>
      let perm ← setPerm address queue.perm
      let qbytes ← number (address + permSize + (if wide then 40 else 32)) word
      if qbytes > 16384 && !credentials.capable Capability.sysResource then return ← fail Errno.eperm
      save { ipc with queues := ipc.queues.map fun other => if other.id == id then { other with perm, qbytes, ctime := seconds } else other }
      -- What waits for room may have it now.
      poller.wake emu
      succeed
    | 2 =>
      let held := queue.messages.foldl (fun total (_, text) => total + text.size) 0
      write emu address (permBytes queue.perm 0 ++ time queue.stime ++ time queue.rtime ++ time queue.ctime ++ long held ++
        long queue.messages.length ++ long queue.qbytes ++ field 4 queue.lspid ++ field 4 queue.lrpid ++ long 0 ++ long 0)
      succeed
    | _ => fail Errno.einval
  try
    match call with
    | .shmget => shmget (arg 0) (arg 1) (arg 2)
    | .shmat =>
      match ← shmat (arg 0) (arg 1) (arg 2) with
      | .ok start => succeed start
      | .error errno => fail errno
    | .shmdt => shmdt (arg 0)
    | .shmctl => shmctl (arg 0) (arg 1) (arg 2)
    | .semget => semget (arg 0) (arg 1) (arg 2)
    | .semop => semop (arg 0) (arg 1) (arg 2) (some none)
    | .semtimedop => semop (arg 0) (arg 1) (arg 2) (← timeout (arg 3))
    | .semtimedop64 => semop (arg 0) (arg 1) (arg 2) (← timeout (arg 3) 8)
    | .semctl => semctl (arg 0) (arg 1) (arg 2) (arg 3)
    | .msgget => msgget (arg 0) (arg 1)
    | .msgsnd => msgsnd (arg 0) (arg 1) (arg 2) (arg 3)
    | .msgrcv => msgrcv (arg 0) (arg 1) (arg 2) (arg 3) (arg 4)
    | .msgctl => msgctl (arg 0) (arg 1) (arg 2)
    | .ipc =>
      -- What it is is in the low 16 bits of the first, and the arguments of each are where they are, but for those of `msgrcv` of
      -- version 0, which are in memory, and `shmat`, which gives where it attached in memory.
      let (first, second, third, pointer, fifth) := (arg 1, arg 2, arg 3, arg 4, arg 5)
      match arg 0 % 2 ^ 16 with
      | 1 => semop first pointer second (some none)
      | 2 => semget first second third
      | 3 => semctl first second third (← number pointer word)
      | 4 => semop first pointer second (← timeout fifth)
      | 11 => msgsnd first pointer second third
      | 12 =>
        if arg 0 / 2 ^ 16 == 0 then msgrcv first (← number pointer word) second (← number (pointer + word) word) third
        else msgrcv first pointer second fifth third
      | 13 => msgget first second
      | 14 => msgctl first second pointer
      | 21 =>
        match ← shmat first pointer second with
        | .ok start =>
          write emu third (field word start)
          succeed
        | .error errno => fail errno
      | 22 => shmdt pointer
      | 23 => shmget first second third
      | 24 => shmctl first second pointer
      | _ => fail Errno.enosys
    | _ => pure none
  catch _ => fail Errno.efault

end SysV

end Bap.Linux
