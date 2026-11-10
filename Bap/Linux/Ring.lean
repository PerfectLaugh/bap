import Bap.Linux.Poll
import Bap.Linux.Wire

/-! # Asynchronous I/O: AIO and io_uring

`io_setup`, `io_submit`, `io_getevents`, `io_pgetevents`, `io_cancel` and `io_destroy`, and `io_uring_setup`, `io_uring_enter` and
`io_uring_register`, with `mmap` of the rings of an io_uring.

What AIO is given is done as it is submitted, at its offset, and its events wait for `io_getevents`. A context is a page of zeros where
its id says, so that a libc that reads events from there finds none of its own and asks. An io_uring has its rings and entries in
memory that `mmap` of its descriptor gives, as Linux has them, without `IORING_FEAT_SINGLE_MMAP`. `io_uring_enter` does what was
submitted in order, by the system calls of the machine, each as it can: one that would wait for a descriptor waits among those
pending, and is tried again at each `io_uring_enter`, as a timeout of `IORING_OP_TIMEOUT` is looked at, until it is done. A chain of
`IOSQE_IO_LINK` ends with what fails, the rest of it `ECANCELED`. What is pending is also done, as it can be, after each call of the
process that made the io_uring and between turns, as Linux does it without `io_uring_enter`: its completions are posted then, and an
`eventfd` that was registered counts them. Its descriptor is ready to read while its ring of completions has some. A call that waits
for completions waits for something to change, or for the first timeout. Without a thread of the kernel, `IORING_SETUP_SQPOLL` isn't
there. -/

namespace Bap.Linux

open Bap.Emu Bap.Tasks

namespace Ring

/-- A context of `io_setup`: whose, its id, which is where its page is, how many events it holds, and those that it has. -/
structure Context where
  group : Nat
  id : Nat
  capacity : Nat
  events : List (Nat × Nat × Nat) := []

/-- An entry of an io_uring that is not done: its bytes, and of a timeout, when, how many completions it waits for, and how many
there had been when it came. -/
structure Pending where
  entry : ByteArray
  deadline : Option Nat := none
  count : Nat := 0
  start : Nat := 0

/-- An io_uring: its inode, the process that made it, the sizes of its rings, where `mmap` put them, the head of its submissions and
the tail of its completions as the kernel has them, how many completions it has made, those that don't fit yet, what is pending, and
what `io_uring_register` gave it: buffers, files and an `eventfd`. -/
structure Uring where
  inode : Nat
  group : Nat := 0
  entries : Nat
  completions : Nat
  sq : Nat := 0
  cq : Nat := 0
  sqes : Nat := 0
  head : Nat := 0
  tail : Nat := 0
  posted : Nat := 0
  overflow : List (Nat × Nat) := []
  pending : List Pending := []
  buffers : List (Nat × Nat) := []
  files : List Nat := []
  eventfd : Option Nat := none

structure State where
  contexts : List Context := []
  rings : List Uring := []
  /-- Of a thread whose `io_uring_enter` waits for completions, where the call is and how many it submitted, which it gives when it is
  done. -/
  submitted : List (Nat × Nat × Nat) := []

/-- What serves these: the machine's own calls, of which `perform` does one as a program would, as it would give it. -/
structure Rings where
  poller : Poller
  state : IO.Ref State
  perform : Call → List Nat → IO SyscallAction

def modelId : String := "bap.rings"

open Wire in
def save (state : IO.Ref State) : IO ByteArray := do
  let state ← state.get
  let numbers := putList putNat
  let out := putList (fun out (context : Context) =>
    putList (fun out (data, object, result) => numbers out [data, object, result]) (numbers out [context.group, context.id, context.capacity])
      context.events) ByteArray.empty state.contexts
  let out := putList (fun out (ring : Uring) =>
    let out := numbers out [ring.inode, ring.entries, ring.completions, ring.sq, ring.cq, ring.sqes, ring.head, ring.tail, ring.posted,
      ring.group]
    let out := putList (fun out (data, result) => numbers out [data, result]) out ring.overflow
    let out := putList (fun out (pending : Pending) =>
      numbers (putOption putNat (putBytes out pending.entry) pending.deadline) [pending.count, pending.start]) out ring.pending
    let out := putList (fun out (address, size) => numbers out [address, size]) out ring.buffers
    putOption putNat (numbers out ring.files) ring.eventfd) out state.rings
  pure (putList (fun out (tid, at_, count) => numbers out [tid, at_, count]) out state.submitted)

open Wire in
def load (state : IO.Ref State) (data : ByteArray) : IO Unit := do
  let numbers : Decoder (List Nat) := getList getNat
  let decoded : Except String State := do
    let (contexts, at_) ← getList (fun data at_ => do
      let (fields, at_) ← numbers data at_
      let (events, at_) ← getList (fun data at_ => do
        let (event, at_) ← numbers data at_
        .ok ((event.getD 0 0, event.getD 1 0, event.getD 2 0), at_)) data at_
      .ok ({ group := fields.getD 0 0, id := fields.getD 1 0, capacity := fields.getD 2 0, events : Context }, at_)) data 0
    let (rings, at_) ← getList (fun data at_ => do
      let (fields, at_) ← numbers data at_
      let (overflow, at_) ← getList (fun data at_ => do
        let (pair, at_) ← numbers data at_
        .ok ((pair.getD 0 0, pair.getD 1 0), at_)) data at_
      let (pending, at_) ← getList (fun data at_ => do
        let (entry, at_) ← getBytes data at_
        let (deadline, at_) ← getOption getNat data at_
        let (more, at_) ← numbers data at_
        .ok ({ entry, deadline, count := more.getD 0 0, start := more.getD 1 0 : Pending }, at_)) data at_
      let (buffers, at_) ← getList (fun data at_ => do
        let (pair, at_) ← numbers data at_
        .ok ((pair.getD 0 0, pair.getD 1 0), at_)) data at_
      let (files, at_) ← numbers data at_
      let (eventfd, at_) ← getOption getNat data at_
      let field (index : Nat) : Nat := fields.getD index 0
      .ok ({ inode := field 0, entries := field 1, completions := field 2, sq := field 3, cq := field 4, sqes := field 5, head := field 6
             tail := field 7, posted := field 8, group := field 9, overflow, pending, buffers, files, eventfd : Uring }, at_)) data at_
    let (submitted, at_) ← getList (fun data at_ => do
      let (fields, at_) ← numbers data at_
      .ok ((fields.getD 0 0, fields.getD 1 0, fields.getD 2 0), at_)) data at_
    expectEnd data at_
    pure { contexts, rings, submitted }
  match decoded with
  | .ok decoded => state.set decoded
  | .error message => throw (IO.userError s!"the state of AIO and io_uring can't be read: {message}")

private def numberOf (big : Bool) (bytes : ByteArray) : Nat :=
  let ordered := if big then bytes.toList else bytes.toList.reverse
  ordered.foldl (fun value byte => value * 256 + byte.toNat) 0

/-- What a call gave, as a signed result of 64 bits, from what the machine's calls give. -/
private def resultOf (action : SyscallAction) : Nat :=
  match action with
  | .returnValue value => value
  | _ => 0

/-- `mmap` of an io_uring: at offset 0 its ring of submissions, at `IORING_OFF_CQ_RING` that of completions, and at `IORING_OFF_SQES`
its entries, each zeros but for the mask and the size of a ring. Of anything else, nothing. -/
def map (rings : Rings) (emu : Emu) (group address size bits flags fd offset : Nat) : IO (Option SyscallAction) := do
  let kernel ← rings.poller.kernel.get
  let .ok (_, file) := kernel.openFileOf group fd | return none
  let state ← rings.state.get
  let some ring := state.rings.find? (·.inode == file.inode) | return none
  let big := rings.poller.architecture.big
  let fixed := flags &&& 0x10 != 0
  let (needed, mask, count) := match offset with
    | 0 => (64 + 4 * ring.entries, ring.entries - 1, ring.entries)
    | 0x8000000 => (64 + 16 * ring.completions, ring.completions - 1, ring.completions)
    | _ => (64 * ring.entries, 0, 0)
  if !(offset == 0 || offset == 0x8000000 || offset == 0x10000000) || size < needed || (fixed && address % 4096 != 0) then
    return some (.returnValue (2 ^ 64 - Errno.einval))
  try
    let start ← placeZeros emu address fixed ((size + 4095) / 4096 * 4096) bits
    if offset != 0x10000000 then write emu (start + 8) (Abi.field big 4 mask ++ Abi.field big 4 count)
    rings.state.set { state with rings := state.rings.map fun other =>
      if other.inode != ring.inode then other
      else if offset == 0 then { other with sq := start } else if offset == 0x8000000 then { other with cq := start } else { other with sqes := start } }
    pure (some (.returnValue start))
  catch _ => pure (some (.returnValue (2 ^ 64 - Errno.enomem)))

/-- The operations of io_uring that are here, by their numbers. -/
def operations : List Nat := [0, 1, 2, 3, 4, 5, 6, 9, 10, 11, 13, 14, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 34, 35, 36, 37, 38, 39]

private def negative (errno : Nat) : Nat := 2 ^ 64 - errno

/-- A number of `size` bytes at `address` of the memory of the process that runs. -/
private def numberAt (rings : Rings) (emu : Emu) (address size : Nat) : IO Nat := do
  pure (numberOf rings.poller.architecture.big (← read emu address size))

/-- The pieces that `count` `iovec`s at `address` say. -/
private def iovecs (rings : Rings) (emu : Emu) (address count : Nat) : IO (List (Nat × Nat)) := do
  let word := rings.poller.architecture.bits / 8
  (List.range count).mapM fun index => do
    pure (← numberAt rings emu (address + 2 * word * index) word, ← numberAt rings emu (address + 2 * word * index + word) word)

/-- What a read or a write at an offset of a file of the process `group` gives, of pieces of memory, as a result of 64 bits. -/
private def atOffset (rings : Rings) (emu : Emu) (group fd : Nat) (pieces : List (Nat × Nat)) (offset : Nat) (writing : Bool) :
    IO Nat := do
  let poller := rings.poller
  let mut done := 0
  for (address, length) in pieces do
    let kernel ← poller.kernel.get
    if writing then
      match kernel.writeTo group fd (← read emu address length) (offset + done) with
      | .ok (next, count) =>
        poller.kernel.set next
        done := done + count
      | .error errno => return if done > 0 then done else negative errno
    else
      match kernel.readFrom group fd length (offset + done) with
      | .ok bytes =>
        write emu address bytes
        done := done + bytes.size
        if bytes.size < length then return done
      | .error errno => return if done > 0 then done else negative errno
  pure done

/-- The io_urings of the process that runs, by their inodes, that have completions for it to take: those whose ring of completions
isn't empty at the head that it has, or that have more than fit. -/
def completed (state : IO.Ref State) (big : Bool) (emu : Emu) : IO (List Nat) := do
  let group := (← currentTask emu).group
  (← state.get).rings.filterMapM fun ring => do
    if ring.group != group || ring.cq == 0 then return none
    if !ring.overflow.isEmpty then return some ring.inode
    try
      let head := numberOf big (← read emu ring.cq 4)
      pure (if head != ring.tail then some ring.inode else none)
    catch _ => pure none

/-- What is ready of a descriptor of the process `group`, as `poll` says it. -/
private def readiness (rings : Rings) (emu : Emu) (group fd : Nat) : IO (Option Ready) := do
  let poller := rings.poller
  let kernel ← poller.kernel.get
  match kernel.openFileOf group fd with
  | .error _ => pure none
  | .ok (id, _) => pure (some (Poller.readiness kernel (← poller.live) (← poller.completed emu) kernel.clock 0 id 4))

/-- Whether a descriptor of the process `group` is ready to be read or written, so that a call doesn't wait. -/
private def ready (rings : Rings) (emu : Emu) (group fd : Nat) (writing : Bool) : IO Bool := do
  match ← readiness rings emu group fd with
  | none => pure true
  | some state =>
    pure (if writing then state.write || state.error || state.hangup else state.read || state.error || state.hangup || state.readHangup)

/-- An io_uring with a completion of the entry of `data`, whose result a completion has as 32 bits: of an error, the guest's own number
of it, negative. -/
private def complete (architecture : Architecture) (ring : Uring) (data result : Nat) : Uring :=
  let result := if result ≥ 2 ^ 63 then 2 ^ 32 - architecture.errno (2 ^ 64 - result) % 2 ^ 32 else result % 2 ^ 32
  { ring with overflow := ring.overflow ++ [(data, result)], posted := ring.posted + 1 }

/-- What an entry of an io_uring does, of the process `group`: its result, or none if it would wait. A read or a write at an offset of
what has none, as a pipe, is as one at none; of a socket, only at 0, as Linux has it. -/
private def perform (rings : Rings) (emu : Emu) (group : Nat) (ring : Uring) (entry : ByteArray) : IO (Option Nat) := do
  let poller := rings.poller
  let take (offset size : Nat) : Nat := numberOf poller.architecture.big (entry.extract offset (offset + size))
  let (opcode, entryFlags, fd, offset, address, length, opFlags) :=
    (take 0 1, take 1 1, take 4 4, take 8 8, take 16 8, take 24 4, take 28 4)
  -- `IOSQE_FIXED_FILE`: the descriptor of what was registered at that place.
  let fd := if entryFlags &&& 1 != 0 then ring.files.getD fd (2 ^ 32 - 1) else fd
  let fd := if fd ≥ 2 ^ 31 then 2 ^ 64 - (2 ^ 32 - fd) else fd
  let (positional, socket) := match (← poller.kernel.get).objectOf group fd with
    | .ok (_, _, { content := .file _, .. }) | .ok (_, _, { content := .directory, .. }) | .ok (_, _, { content := .symlink _, .. })
    | .ok (_, _, { content := .generated _, .. }) | .error _ => (true, false)
    | .ok (_, _, { content := .socket _, .. }) => (false, true)
    | .ok _ => (false, false)
  let sequential := offset == 2 ^ 64 - 1 || !positional
  let system (call : Call) (args : List Nat) : IO (Option Nat) := do pure (some (resultOf (← rings.perform call args)))
  let whenReady (writing : Bool) (action : IO (Option Nat)) : IO (Option Nat) := do
    if ← ready rings emu group fd writing then action else pure none
  match opcode with
  | 0 => pure (some 0)
  | 1 | 2 | 22 | 23 | 4 | 5 =>
    let writing := opcode == 2 || opcode == 23 || opcode == 5
    let vectored := opcode == 1 || opcode == 2
    if socket && offset != 0 && offset != 2 ^ 64 - 1 then pure (some (negative Errno.espipe))
    else if sequential then
      whenReady writing (system (match vectored, writing with
        | true, true => .writev | true, false => .readv | false, true => .write | false, false => .read) [fd, address, length])
    else
      let pieces ← if vectored then iovecs rings emu address length else pure [(address, length)]
      pure (some (← atOffset rings emu group fd pieces offset writing))
  | 3 | 17 | 24 | 25 =>
    let known := ((← poller.kernel.get).openFileOf group fd).toOption.isSome
    pure (some (if known || opcode == 25 then 0 else negative Errno.ebadf))
  | 6 =>
    -- What of the events asked for is ready, as `poll` says it.
    match ← readiness rings emu group fd with
    | none => pure (some (negative Errno.ebadf))
    | some state =>
      -- `poll32_events`, whose halves a big-endian machine has swapped, as liburing puts them and the kernel's `io_poll_parse_events`
      -- swaps them back: the mask is its low half after that.
      let events := if poller.architecture.big then (opFlags >>> 16) ||| (opFlags % 2 ^ 16 <<< 16) else opFlags
      let revents := Poller.bits state 0x100 &&& (events % 2 ^ 16 ||| 0x18)
      pure (if revents == 0 then none else some revents)
  | 9 => whenReady true (system .sendmsg [fd, address, opFlags])
  | 10 => whenReady false (system .recvmsg [fd, address, opFlags])
  | 13 => whenReady false (system .accept4 [fd, address, offset, opFlags])
  | 16 => system .connect [fd, address, offset]
  | 18 => system .openat [fd, address, opFlags, length]
  | 19 => system .close [fd]
  | 21 => system .statx [fd, address, opFlags, length, offset]
  | 26 => whenReady true (system .sendto [fd, address, length, opFlags, 0, 0])
  | 27 => whenReady false (system .recvfrom [fd, address, length, opFlags, 0, 0])
  | 34 => system .shutdown [fd, length]
  | 35 => system .renameat2 [fd, address, length, offset, opFlags]
  | 36 => system .unlinkat [fd, address, opFlags]
  | 37 => system .mkdirat [fd, address, length]
  | 38 => system .symlinkat [address, fd, offset]
  | 39 => system .linkat [fd, address, length, offset, opFlags]
  | _ => pure (some (negative Errno.einval))

/-- What is pending of an io_uring, in order, done as far as it can be: a chain that one of them is in waits behind it. -/
private def attempt (rings : Rings) (emu : Emu) (group : Nat) (ring : Uring) (pending : List Pending) : IO Uring := do
  let architecture := rings.poller.architecture
  let big := architecture.big
  let now := (← rings.poller.kernel.get).clock
  let mut ring := { ring with pending := [] }
  let mut blocked := false
  let mut cancelling := false
  for item in pending do
    let data := numberOf big (item.entry.extract 32 40)
    let linked := item.entry[1]! &&& 4 != 0
    if cancelling then
      ring := complete architecture ring data (negative 125)
      cancelling := linked
      continue
    -- What comes after what waits in its chain waits too, to the end of the chain, which is the first that isn't linked.
    if blocked then
      ring := { ring with pending := ring.pending ++ [item] }
      blocked := linked
      continue
    if item.entry[0]! == 11 then
      -- A timeout: done with its count of completions, or, at its time, with `ETIME`, which fails what is linked after it unless it
      -- has `IORING_TIMEOUT_ETIME_SUCCESS`; and until then, what is linked after it waits.
      if item.count > 0 && ring.posted - item.start ≥ item.count then ring := complete architecture ring data 0
      else if item.deadline.any (· ≤ now) then
        ring := complete architecture ring data (negative 62)
        cancelling := linked && numberOf big (item.entry.extract 28 32) &&& 0x20 == 0
      else
        ring := { ring with pending := ring.pending ++ [item] }
        blocked := linked
      continue
    if item.entry[0]! == 14 then
      -- What `IORING_OP_ASYNC_CANCEL` cancels: what is pending of that number.
      let target := numberOf big (item.entry.extract 16 24)
      let found := ring.pending.find? fun other => numberOf big (other.entry.extract 32 40) == target
      match found with
      | some other =>
        ring := complete architecture { ring with pending := ring.pending.filter fun entry => entry.entry != other.entry } data 0
        ring := complete architecture ring target (negative 125)
      | none => ring := complete architecture ring data (negative Errno.enoent)
      continue
    match ← perform rings emu group ring item.entry with
    | none =>
      ring := { ring with pending := ring.pending ++ [item] }
      blocked := linked
    | some result =>
      ring := complete architecture ring data result
      -- What failed, and a read or a write of less than it asked for, as `__io_complete_rw_common` has it, cancels what it is linked to.
      let opcode := item.entry[0]!.toNat
      let length := numberOf big (item.entry.extract 24 28)
      let asked ← if [22, 23, 4, 5].contains opcode then pure (some length)
        else if opcode == 1 || opcode == 2 then do
          let word := architecture.bits / 8
          let vectors := numberOf big (item.entry.extract 16 24)
          let sizes ← (List.range (min length 1024)).mapM fun index => numberAt rings emu (vectors + index * 2 * word + word) word
          pure (some (sizes.foldl (· + ·) 0))
        else pure none
      cancelling := linked && (result ≥ 2 ^ 63 || asked.any (result < ·))
  pure ring

/-- The completions of an io_uring go to its ring, as many as there is room for, which the `eventfd` of the process `group` that was
registered counts; its descriptor has changed, and what waits looks again. -/
private def post (rings : Rings) (emu : Emu) (group : Nat) (ring : Uring) : IO Uring := do
  let poller := rings.poller
  let field := Abi.field poller.architecture.big
  let cqHead ← numberAt rings emu ring.cq 4
  let room := ring.completions - (ring.tail + 2 ^ 32 - cqHead) % 2 ^ 32
  let posting := ring.overflow.take room
  let mut ring := ring
  for (data, result) in posting do
    write emu (ring.cq + 64 + 16 * (ring.tail % ring.completions)) (field 8 data ++ field 4 result ++ field 4 0)
    ring := { ring with tail := (ring.tail + 1) % 2 ^ 32 }
  ring := { ring with overflow := ring.overflow.drop posting.length }
  write emu (ring.cq + 4) (field 4 ring.tail)
  if !posting.isEmpty then
    poller.kernel.modify (·.setContent ring.inode (.generated "io_uring"))
    if let some fd := ring.eventfd then
      let kernel ← poller.kernel.get
      if let .ok (number_, _, { content := .eventfd value semaphore, .. }) := kernel.objectOf group fd then
        poller.kernel.set (kernel.setContent number_ (.eventfd (value + posting.length) semaphore))
    poller.wake emu
  pure ring

/-- What the io_urings of the process `group`, which runs, have pending is done as far as it can be, and their completions posted, as
Linux does without a call of `io_uring_enter`. -/
def settle (rings : Rings) (emu : Emu) (group : Nat) : IO Unit := do
  for ring in (← rings.state.get).rings do
    if ring.group != group || (ring.pending.isEmpty && ring.overflow.isEmpty) || ring.sq == 0 || ring.cq == 0 || ring.sqes == 0 then
      continue
    try
      let ring ← post rings emu group (← attempt rings emu group ring ring.pending)
      rings.state.modify fun state => { state with rings := state.rings.map fun other => if other.inode == ring.inode then ring else other }
    catch _ => pure ()

/-- The calls of AIO and io_uring, if the call is one of them. -/
partial def serve (rings : Rings) (emu : Emu) (call : Call) (args : List Nat) : IO (Option SyscallAction) := do
  let poller := rings.poller
  let architecture := poller.architecture
  let big := architecture.big
  let word := architecture.bits / 8
  let arg (index : Nat) : Nat := args.getD index 0
  let tid ← thread emu
  let group := (← currentTask emu).group
  let fail (errno : Nat) : IO (Option SyscallAction) := do pure (some (.returnValue (2 ^ 64 - errno)))
  let succeed (value : Nat := 0) : IO (Option SyscallAction) := do pure (some (.returnValue value))
  let number := numberAt rings emu
  let field := Abi.field big
  let now := (← poller.kernel.get).clock
  -- What is of processes that are gone, or of an io_uring that no descriptor has, goes as something new is made.
  let forget : IO Unit := do
    let kernel ← poller.kernel.get
    let live ← poller.live
    let held := live.foldl (init := ({} : Std.HashSet Nat)) fun held owner =>
      (kernel.process owner).descriptors.fold (init := held) fun held _ descriptor =>
        match kernel.openFiles.get? descriptor.openFile with
        | some file => held.insert file.inode
        | none => held
    rings.state.modify fun state => { state with contexts := state.contexts.filter (live.contains ·.group)
                                                 rings := state.rings.filter (held.contains ·.inode) }
  try
  match call with
  | .ioSetup =>
    forget
    let capacity := arg 0 % 2 ^ 32
    if capacity == 0 || capacity > 65536 || (← number (arg 1) word) != 0 then return ← fail Errno.einval
    let id ← try placeZeros emu 0 false 4096 1 catch _ => return ← fail Errno.enomem
    write emu (arg 1) (field word id)
    rings.state.modify fun state => { state with contexts := state.contexts ++ [{ group, id, capacity }] }
    succeed
  | .ioDestroy =>
    let state ← rings.state.get
    let some context := state.contexts.find? fun context => context.group == group && context.id == arg 0 | fail Errno.einval
    rings.state.set { state with contexts := state.contexts.filter fun other => other.id != context.id || other.group != group }
    unmap emu context.id 4096
    succeed
  | .ioCancel =>
    let state ← rings.state.get
    if !state.contexts.any fun context => context.group == group && context.id == arg 0 then return ← fail Errno.einval
    -- What was submitted is done already.
    fail Errno.eagain
  | .ioSubmit =>
    let state ← rings.state.get
    let some context := state.contexts.find? fun context => context.group == group && context.id == arg 0 | fail Errno.einval
    let count := arg 1
    if count ≥ 2 ^ (8 * word - 1) then return ← fail Errno.einval
    let mut events := context.events
    let mut done := 0
    for index in List.range count do
      if events.length ≥ context.capacity then break
      let at_ ← number (arg 2 + word * index) word
      let iocb ← read emu at_ 64
      let take (offset size : Nat) : Nat := numberOf big (iocb.extract offset (offset + size))
      let (data, opcode, fd, buffer, length, offset, flags, resfd) :=
        (take 0 8, take 16 2, take 20 4, take 24 8, take 32 8, take 40 8, take 56 4, take 60 4)
      if ((← poller.kernel.get).openFileOf group fd).toOption.isNone then
        if done == 0 then return ← fail Errno.ebadf else break
      let result ← match opcode with
        | 0 => atOffset rings emu group fd [(buffer, length)] offset false
        | 1 => atOffset rings emu group fd [(buffer, length)] offset true
        | 2 | 3 | 6 => pure 0
        | 7 => atOffset rings emu group fd (← iovecs rings emu buffer length) offset false
        | 8 => atOffset rings emu group fd (← iovecs rings emu buffer length) offset true
        | _ => if done == 0 then return ← fail Errno.einval else break
      -- An error is the guest's own number of it, negative.
      let result := if result ≥ 2 ^ 63 then 2 ^ 64 - architecture.errno (2 ^ 64 - result) else result
      events := events ++ [(data, at_, result)]
      done := done + 1
      -- `IOCB_FLAG_RESFD`: what an `eventfd` counts.
      if flags &&& 1 != 0 then
        let kernel ← poller.kernel.get
        if let .ok (number_, _, { content := .eventfd value semaphore, .. }) := kernel.objectOf group resfd then
          poller.kernel.set (kernel.setContent number_ (.eventfd (value + 1) semaphore))
    rings.state.set { state with contexts := state.contexts.map fun other =>
      if other.id == context.id && other.group == group then { other with events } else other }
    poller.wake emu
    if done == 0 && count > 0 then fail Errno.eagain else succeed done
  | .ioGetevents | .ioPgetevents | .ioPgetevents64 =>
    let state ← rings.state.get
    let some context := state.contexts.find? fun context => context.group == group && context.id == arg 0 | fail Errno.einval
    let (least, most) := (arg 1, arg 2)
    if least > most then return ← fail Errno.einval
    let size := if call == .ioPgetevents64 then 8 else word
    let due ← if arg 4 == 0 then pure none else do
      let span := (← number (arg 4) size) * 1000000000 + (← number (arg 4 + size) size)
      pure (some (← poller.timers.deadlineOf tid (pure (now + span))))
    if context.events.length < least && !due.any (· ≤ now) then
      return some (← poller.timers.waitUntil emu readySpace 0 due false)
    poller.timers.finish tid
    let taken := context.events.take most
    write emu (arg 3) (taken.foldl (fun out (data, object, result) => out ++ field 8 data ++ field 8 object ++ field 8 result ++ field 8 0)
      ByteArray.empty)
    rings.state.set { state with contexts := state.contexts.map fun other =>
      if other.id == context.id && other.group == group then { other with events := other.events.drop taken.length } else other }
    succeed taken.length
  | .ioUringSetup =>
    forget
    let requested := arg 0
    let flags ← number (arg 1 + 8) 4
    -- `IORING_SETUP_CQSIZE` and `IORING_SETUP_CLAMP`, and those that only say how it is to run.
    if flags &&& 0x3ffff - (8 ||| 16 ||| 128 ||| 256 ||| 512 ||| 4096 ||| 8192) != 0 then return ← fail Errno.einval
    if requested == 0 || (requested > 32768 && flags &&& 16 == 0) then return ← fail Errno.einval
    let power (value : Nat) : Nat := (List.range 17).foldl (fun found bits => if found ≥ value then found else 2 ^ bits) 1
    let entries := power (min requested 32768)
    let completions ← if flags &&& 8 == 0 then pure (2 * entries) else do
      let given ← number (arg 1 + 4) 4
      if given == 0 || (given > 65536 && flags &&& 16 == 0) then return ← fail Errno.einval
      pure (max entries (power (min given 65536)))
    let kernel ← poller.kernel.get
    let (kernel, fd) := kernel.addObject group (.generated "io_uring") Kernel.oCloexec
    poller.kernel.set kernel
    let inode := kernel.nextInode - 1
    rings.state.modify fun state => { state with rings := state.rings ++ [{ inode, group, entries, completions }] }
    -- `struct io_uring_params`: the sizes, what it has, and where in its rings each part of them is.
    let features := 2 ||| 4 ||| 8
    write emu (arg 1) (field 4 entries ++ field 4 completions)
    write emu (arg 1 + 20) (field 4 features)
    write emu (arg 1 + 40) ([0, 4, 8, 12, 16, 20, 64].foldl (fun out value => out ++ field 4 value) ByteArray.empty)
    write emu (arg 1 + 80) ([0, 4, 8, 12, 16, 64, 20].foldl (fun out value => out ++ field 4 value) ByteArray.empty)
    succeed fd
  | .ioUringRegister =>
    let kernel ← poller.kernel.get
    let .ok (_, file) := kernel.openFileOf group (arg 0) | fail Errno.ebadf
    let state ← rings.state.get
    let some ring := state.rings.find? (·.inode == file.inode) | fail Errno.einval
    let update (change : Uring → Uring) : IO Unit :=
      rings.state.set { state with rings := state.rings.map fun other => if other.inode == ring.inode then change other else other }
    match arg 1 with
    | 0 =>
      if !ring.buffers.isEmpty then return ← fail 16
      update fun other => { other with buffers := [] }
      let buffers ← iovecs rings emu (arg 2) (arg 3)
      update fun other => { other with buffers }
      succeed
    | 1 => if ring.buffers.isEmpty then fail Errno.enxio else do update fun other => { other with buffers := [] }; succeed
    | 2 =>
      if !ring.files.isEmpty then return ← fail 16
      let files ← (List.range (arg 3)).mapM fun index => number (arg 2 + 4 * index) 4
      update fun other => { other with files }
      succeed
    | 3 => if ring.files.isEmpty then fail Errno.enxio else do update fun other => { other with files := [] }; succeed
    | 4 | 7 =>
      if ring.eventfd.isSome then return ← fail 16
      let fd ← number (arg 2) 4
      update fun other => { other with eventfd := some fd }
      succeed
    | 5 => if ring.eventfd.isNone then fail Errno.enxio else do update fun other => { other with eventfd := none }; succeed
    | 8 =>
      -- `struct io_uring_probe`, of what operations there are.
      let ops := (List.range (arg 3)).foldl (fun out op => out ++ field 1 op ++ field 1 0 ++ field 2 (if operations.contains op then 1 else 0) ++ field 4 0)
        ByteArray.empty
      write emu (arg 2) (field 1 39 ++ field 1 (min (arg 3) 40) ++ field 2 0 ++ field 4 0 ++ field 4 0 ++ field 4 0 ++ ops)
      succeed
    | _ => fail Errno.einval
  | .ioUringEnter =>
    let kernel ← poller.kernel.get
    let .ok (_, file) := kernel.openFileOf group (arg 0) | fail Errno.ebadf
    let some ring := (← rings.state.get).rings.find? (·.inode == file.inode) | fail Errno.eopnotsupp
    let flags := arg 3
    if flags &&& (8 ||| 16) != 0 then return ← fail Errno.einval
    if ring.sq == 0 || ring.cq == 0 || ring.sqes == 0 then return ← fail Errno.efault
    let mut ring ← attempt rings emu group ring ring.pending
    -- What was submitted: from the head that the kernel has to the tail that the program wrote.
    let tail ← number (ring.sq + 4) 4
    let count := min (arg 1) ((tail + 2 ^ 32 - ring.head) % 2 ^ 32)
    let mut submitted : List Pending := []
    for index in List.range count do
      let slot ← number (ring.sq + 64 + 4 * ((ring.head + index) % ring.entries)) 4
      let entry ← read emu (ring.sqes + 64 * (slot % ring.entries)) 64
      let item : Pending := if entry[0]! == 11 then { entry, count := numberOf big (entry.extract 8 16), start := ring.posted } else { entry }
      submitted := submitted ++ [item]
    -- Of a timeout, its time, absolute with `IORING_TIMEOUT_ABS`. One of negative seconds or nanoseconds, which Linux doesn't take,
    -- is as an entry of no operation, which fails with `EINVAL`; nanoseconds of a second or more are seconds.
    submitted ← submitted.mapM fun item => do
      if item.entry[0]! != 11 then return item
      let address := numberOf big (item.entry.extract 16 24)
      let (seconds, nanoseconds) ← readTime emu address 8
      if seconds < 0 || nanoseconds < 0 then return { item with entry := item.entry.set! 0 255 }
      let span := seconds.toNat * 1000000000 + nanoseconds.toNat
      let absolute := numberOf big (item.entry.extract 28 32) &&& 1 != 0
      pure { item with deadline := some (if absolute then span else now + span) }
    ring := { ring with head := (ring.head + count) % 2 ^ 32 }
    write emu ring.sq (field 4 ring.head)
    let finished ← post rings emu group (← attempt rings emu group ring (ring.pending ++ submitted))
    let cqHead ← number finished.cq 4
    let state ← rings.state.get
    -- Of a thread that waited here, what it submitted before it did; one that a signal ended is of another call.
    let next ← emu.nextPc.get
    let earlier := (state.submitted.find? fun (thread, at_, _) => thread == tid && at_ == next).map (·.2.2) |>.getD 0
    let total := earlier + count
    rings.state.set { state with rings := state.rings.map (fun other => if other.inode == finished.inode then finished else other)
                                 submitted := state.submitted.filter (·.1 != tid) }
    -- `IORING_ENTER_GETEVENTS`: as many as it asks for, or something to change, or the first timeout.
    let available := (finished.tail + 2 ^ 32 - cqHead) % 2 ^ 32
    if flags &&& 1 != 0 && available < arg 2 then
      rings.state.modify fun state => { state with submitted := state.submitted ++ [(tid, next, total)] }
      let due := (finished.pending.filterMap (·.deadline)).min?
      return some (← poller.timers.waitUntil emu readySpace 0 due false)
    succeed total
  | _ => pure none
  catch _ => fail Errno.efault

end Ring

end Bap.Linux
