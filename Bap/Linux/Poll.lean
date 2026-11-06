import Bap.Linux.Timers
import Bap.Linux.Sockets

/-! # Waiting for descriptors

`poll`, `ppoll`, `select`, `pselect6` and the `epoll` calls, and what they wait for besides pipes and sockets: `eventfd`, `timerfd` and
`signalfd`.

What is ready of a descriptor goes by what it is on: a file is always ready, a pipe to read when it has something or nothing writes
it, to write when something reads it; a socket to read when it has something, a connection to accept or nothing more is to come, to
write when what it sends to is there; an `eventfd` to read when its count isn't 0; a `timerfd` when it expired; a `signalfd` when a
signal of its mask is pending for the thread; and an epoll instance when what it watches is.

A call that has nothing ready waits until something changes, which has it run again, or until its deadline, its timeout or when a
`timerfd` that it watches expires. A signal has it give `EINTR`, as Linux has it, with the mask that `ppoll`, `pselect6` and
`epoll_pwait` give while it waits.

An item of epoll with `EPOLLET` is told of when it becomes ready, and again when what it watches changes or is ready of more than it
was told, rather than each time that it is waited for; one of `EPOLLONESHOT` is told of once until `EPOLL_CTL_MOD`. An item goes when
nothing has its open file any more. -/

namespace Bap.Linux

open Bap.Emu Bap.Tasks

/-- Where what waits for a descriptor to be ready waits: whatever changes, it looks again. It is the first space of those of pipes. -/
def readySpace : Nat := 2 ^ 61

/-- Text of bytes of a guest, as a path or a name: of UTF-8 if they are, and otherwise a character of each byte, so that the same bytes
are the same text. -/
def textOf (bytes : ByteArray) : String :=
  (String.fromUTF8? bytes).getD (String.ofList (bytes.toList.map fun byte => Char.ofNat byte.toNat))

/-- What is ready of an open file. -/
structure Ready where
  read : Bool := false
  write : Bool := false
  error : Bool := false
  hangup : Bool := false
  readHangup : Bool := false

/-- What the calls of this module need of a machine: its kernel, its timers and signals, the processes that are alive, and what
has those that wait for something to be ready look again. -/
structure Poller where
  architecture : Architecture
  kernel : IO.Ref Kernel
  timers : Timers
  signals : Signals
  live : IO (List Nat)
  wake : Emu → IO Unit
  /-- The io_urings of the process that runs, by their inodes, that have completions for it to take. -/
  completed : Emu → IO (List Nat)

/-- How many bytes the slave of a terminal has to read. -/
def Terminal.waiting (terminal : Terminal) : Nat := terminal.input.foldl (· + ·.size) 0

/-- Whether the slave of a terminal has something to read, of `poll`: a line or an end of file in canonical mode, and otherwise `VMIN`
bytes, or one of `VMIN` of 0 or of `VTIME`, as Linux has it. -/
def Terminal.readable (terminal : Terminal) : Bool :=
  if terminal.lflag &&& 2 != 0 then !terminal.input.isEmpty || terminal.ends > 0
  else
    let least := terminal.cc.getD 6 1
    terminal.waiting ≥ (if least == 0 || terminal.cc.getD 5 0 != 0 then 1 else least)

namespace Poller

/-- What is ready of an open file, with the io_urings that have completions to take, by their inodes, and what is pending for the
thread that asks as bits, of a `signalfd`. -/
def readiness (kernel : Kernel) (live completed : List Nat) (now pending file : Nat) : Nat → Ready
  | 0 => {}
  | depth + 1 =>
    match kernel.openFiles.get? file with
    | none => { error := true }
    | some opened =>
      match kernel.inodes.get? opened.inode with
      | none => { error := true }
      | some inode =>
        match inode.content with
        -- An io_uring is to be read when its ring of completions has some.
        | .generated "io_uring" => { read := completed.contains opened.inode, write := true }
        | .file _ | .directory | .symlink _ | .generated _ | .console _ | .device _ => { read := true, write := true }
        | .pipe .. =>
          if opened.flags &&& 3 == 0 then
            let writers := kernel.pipeHeld opened.inode live true
            -- With nothing to read and nothing that writes it, it is POLLHUP alone, which select takes as ready to read.
            { read := kernel.pipeWaiting opened.inode > 0, hangup := !writers }
          else
            let readers := kernel.pipeHeld opened.inode live false
            -- It has room once a page of it is free, which Linux, which keeps a pipe in pages, has as a free one.
            { write := readers && kernel.pipeRoom opened.inode ≥ Kernel.pipeBuf, error := !readers }
        | .socket socket =>
          if socket.listening then { read := !socket.pending.isEmpty }
          else if socket.type == 2 then { read := !socket.incoming.isEmpty, write := true }
          else
            -- A connection is ready to be written to whatever its ends are, as Linux has it: what goes wrong is what the write says.
            match socket.peer with
            | none => { write := true, hangup := true }
            | some peer =>
              let other := kernel.socketAt peer
              let gone := !kernel.socketAlive peer live
              let ended := socket.readShut || gone || other.any (·.writeShut)
              { read := !socket.incoming.isEmpty || ended, readHangup := ended, write := true
                error := kernel.wasReset socket (kernel.socketAlive · live), hangup := gone || (ended && socket.writeShut) }
        | .eventfd count _ => { read := count > 0, write := count < 2 ^ 64 - 2 }
        | .timerfd expiry _ => { read := expiry.any (· ≤ now) }
        | .signalfd mask => { read := mask &&& pending != 0 }
        | .ptyMaster terminal =>
          -- Once nothing has the slave open, after it was, it hangs up.
          let slave := kernel.paths.getD s!"/dev/pts/{terminal.index}" 0
          { read := terminal.output.size > 0, write := true, hangup := terminal.opened && !kernel.inodeHeld live slave }
        | .inotify _ notices _ _ => { read := !notices.isEmpty }
        | .mqueue messages capacity _ _ => { read := !messages.isEmpty, write := messages.length < capacity }
        | .ptySlave master =>
          match kernel.inodes.get? master with
          | some { content := .ptyMaster terminal, .. } =>
            if kernel.inodeHeld live master then { read := terminal.readable, write := true }
            -- Once nothing has the master open, it is hung up, which Linux has as all of these.
            else { read := true, write := true, error := true, hangup := true }
          | _ => { read := true, write := true, error := true, hangup := true }
        | .epoll items =>
          { read := items.any fun item =>
              let ready := readiness kernel live completed now pending item.file depth
              (ready.read && item.events &&& 1 != 0) || (ready.write && item.events &&& 4 != 0) || ready.error || ready.hangup }

/-- How many times what an open file is ready of has changed, which `EPOLLET` goes by: of the end of a pipe that reads, all that was
ever written to it, and of one that writes, all that was ever read of it; of the slave of a pseudo-terminal, the changes of its master;
and otherwise the changes of its inode. -/
def changes (kernel : Kernel) (file : Nat) : Nat :=
  match kernel.openFiles.get? file with
  | none => 0
  | some opened =>
    match kernel.inodes.get? opened.inode with
    | some { content := .pipe buffer head consumed _, .. } => if opened.flags &&& 3 == 0 then consumed + (buffer.size - head) else consumed
    | some { content := .ptySlave master, .. } => ((kernel.inodes.get? master).map (·.details.changes)).getD 0
    | some inode => inode.details.changes
    | none => 0

/-- The bits of what is ready, of `poll` or of `epoll`, whose `POLLWRNORM` is `POLLOUT` on MIPS. -/
def bits (ready : Ready) (wrnorm : Nat) : Nat :=
  (if ready.read then 0x1 ||| 0x40 else 0) ||| (if ready.write then 0x4 ||| wrnorm else 0) ||| (if ready.error then 0x8 else 0) |||
    (if ready.hangup then 0x10 else 0) ||| (if ready.readHangup then 0x2000 else 0)

/-- When a `timerfd` of these open files that isn't ready expires, which a call that watches it waits due. -/
private def expiries (kernel : Kernel) (now : Nat) (files : List Nat) (depth : Nat := 4) : List Nat :=
  files.flatMap fun file =>
    match kernel.openFiles.get? file with
    | some opened =>
      match kernel.inodes.get? opened.inode, depth with
      | some { content := .timerfd (some expiry) _, .. }, _ => if expiry > now then [expiry] else []
      -- Of one that an epoll watches, which `readiness` goes into as deep.
      | some { content := .epoll items, .. }, depth + 1 => expiries kernel now (items.map (·.file)) depth
      | _, _ => []
    | none => []

private def numberOf (big : Bool) (bytes : ByteArray) : Nat :=
  let ordered := if big then bytes.toList else bytes.toList.reverse
  ordered.foldl (fun value byte => value * 256 + byte.toNat) 0

private def numberBytes (big : Bool) (size value : Nat) : ByteArray :=
  let little := (List.range size).map fun index => (value >>> (8 * index)).toUInt8
  ByteArray.mk (if big then little.reverse else little).toArray

/-- The open files that a descriptor of a live process has. -/
private def referenced (kernel : Kernel) (live : List Nat) : Std.HashSet Nat :=
  live.foldl (init := {}) fun files group =>
    (kernel.process group).descriptors.fold (init := files) fun files _ entry => files.insert entry.openFile

/-- The calls of this module, and `read` and `write` of what they make, if the call is one of them. -/
def serve (poller : Poller) (emu : Emu) (call : Call) (args : List Nat) : IO (Option SyscallAction) := do
  let architecture := poller.architecture
  let big := architecture.big
  let width := architecture.bits
  let word := width / 8
  let mips := architecture matches .mips ..
  let arg (index : Nat) : Nat := args.getD index 0
  let tid ← thread emu
  let group := (← currentTask emu).group
  let timers := poller.timers
  let now ← timers.now
  let number (address size : Nat) : IO Nat := do pure (numberOf big (← read emu address size))
  let fail (errno : Nat) : IO (Option SyscallAction) := do pure (some (.returnValue (2 ^ 64 - errno)))
  let succeed (value : Nat := 0) : IO (Option SyscallAction) := do pure (some (.returnValue value))
  let einval := 22
  let eintr := 4
  let ebadf := 9
  let eagain := if mips then 11 else 11
  -- A timeout as a deadline, the same each time that the call runs again: none waits as long as it takes.
  let deadline (span : Option Nat) : IO (Option Nat) := do
    match span with
    | none => pure none
    | some span => pure (some (← timers.deadlineOf tid (pure (now + span))))
  -- What has nothing ready waits: until something changes, its deadline, or a `timerfd` that it watches expires.
  let wait (due : Option Nat) (files : List Nat) : IO (Option SyscallAction) := do
    let deadlines := due.toList ++ expiries (← poller.kernel.get) now files
    pure (some (← timers.waitUntil emu readySpace 0 deadlines.min? false))
  -- What is alive and pending is the same for each descriptor of a call.
  let live ← poller.live
  let completed ← poller.completed emu
  let pending ← poller.signals.pendingBits tid group
  let ready (file : Nat) : IO Ready := do pure (readiness (← poller.kernel.get) live completed now pending file 4)
  let fileOf (fd : Nat) : IO (Option Nat) := do
    match (← poller.kernel.get).openFileOf group fd with
    | .ok (id, _) => pure (some id)
    | .error _ => pure none
  let nonblocking (fd : Nat) : IO Bool := do pure ((← poller.kernel.get).nonblocking group fd)
  -- The mask that the call waits with, a word at a time, and whether that lets through a signal that is pending, which ends it now.
  let mask (address size : Nat) : IO Bool := do
    if address == 0 then return false
    poller.signals.suspendWith tid (← poller.signals.readMask emu address (min size 16 / word * word))
    if ← poller.signals.unblockedPending tid group then
      timers.finish tid
      return true
    pure false
  let flags (given : Nat) : Nat := architecture.openFlags given
  let eventSize := if architecture == .x86_64 || architecture == .i686 then 12 else 16
  let eventData := if eventSize == 12 then 4 else 8
  -- The descriptors of `poll`, with what each asks for: what is ready of each, how many are, and the files to watch.
  let pollOnce (address count : Nat) : IO (Nat × List Nat) := do
    let mut readyCount := 0
    let mut files := []
    for index in [0:count] do
      let at_ := address + index * 8
      let fd := (← number at_ 4)
      let events ← number (at_ + 4) 2
      let revents ← if fd ≥ 2 ^ 31 then pure 0 else
        match ← fileOf fd with
        | none => pure 0x20
        | some file =>
          files := file :: files
          pure (bits (← ready file) (if mips then 0 else 0x100) &&& (events ||| 0x8 ||| 0x10))
      write emu (at_ + 6) (numberBytes big 2 revents)
      if revents != 0 then readyCount := readyCount + 1
    pure (readyCount, files)
  let poll (address count : Nat) (timeout : Option Nat) : IO (Option SyscallAction) := do
    let due ← deadline timeout
    let (found, files) ← pollOnce address count
    if found > 0 || timeout == some 0 || due.any (· ≤ now) then
      timers.finish tid
      succeed found
    else wait due files
  -- The sets of `select`: what is ready of each, as sets that say only that, how many, and the files to watch.
  let select (count : Nat) (sets : List Nat) (timeout : Option Nat) : IO (Option SyscallAction) := do
    let due ← deadline timeout
    let words := (count + width - 1) / width
    let readSet (address : Nat) : IO (List Nat) := do
      if address == 0 then pure [] else (List.range words).mapM fun index => number (address + index * word) word
    let given ← sets.mapM readSet
    let mut results : List (List Nat) := []
    let mut found := 0
    let mut files := []
    for (which, set) in given.zipIdx.map (fun (set, which) => (which, set)) do
      let mut out : List Nat := []
      for index in [0:set.length] do
        let mut kept := 0
        for bit in [0:width] do
          let fd := index * width + bit
          if fd < count && set[index]! >>> bit &&& 1 != 0 then
            let some file ← fileOf fd | return ← fail ebadf
            files := file :: files
            let state ← ready file
            let yes := match which with
              | 0 => state.read || state.hangup || state.error
              | 1 => state.write || state.error
              | _ => false
            if yes then
              kept := kept ||| (1 <<< bit)
              found := found + 1
        out := out ++ [kept]
      results := results ++ [out]
    if found > 0 || timeout == some 0 || due.any (· ≤ now) then
      timers.finish tid
      for (address, set) in sets.zip results do
        if address != 0 then
          for (value, index) in set.zipIdx do write emu (address + index * word) (numberBytes big word value)
      succeed found
    else wait due files
  -- What an epoll instance has ready, up to `limit`, which goes to `address`, and its items as they are after.
  let epollWait (epfd address limit : Nat) (timeout : Option Nat) : IO (Option SyscallAction) := do
    let kernel ← poller.kernel.get
    let .ok (number_, _, inode) := kernel.objectOf group epfd | return ← fail ebadf
    let .epoll items := inode.content | return ← fail einval
    if limit == 0 || limit > 2 ^ 31 then return ← fail einval
    let due ← deadline timeout
    let open_ := referenced kernel live
    let mut kept : List EpollItem := []
    -- What is told of without EPOLLET or EPOLLONESHOT goes after the rest, as Linux puts it at the end of what is ready, so that
    -- waits that take fewer than are ready go round all of them.
    let mut reported : List EpollItem := []
    let mut events : List (Nat × Nat) := []
    for item in items do
      if !open_.contains item.file then continue
      let state ← ready item.file
      let revents := bits state 0x100 &&& (item.events ||| 0x8 ||| 0x10) &&& 0x3fff
      let edge := item.events &&& 0x80000000 != 0
      let once := item.events &&& 0x40000000 != 0
      let seen := changes kernel item.file
      -- Of EPOLLET, what changed or is ready of more since it was told of is told of again; one of EPOLLONESHOT waits for EPOLL_CTL_MOD.
      let fresh := match item.told with
        | none => true
        | some (told, before) => edge && !once && (revents ||| told != told || seen != before)
      if revents != 0 && fresh && events.length < limit then
        events := events ++ [(revents, item.data)]
        if edge || once then kept := kept ++ [{ item with told := some (revents, seen) }]
        else reported := reported ++ [{ item with told := none }]
      else
        -- What isn't ready is told of again once it is, of EPOLLET.
        kept := kept ++ [if revents == 0 && edge && !once then { item with told := none } else item]
    kept := kept ++ reported
    poller.kernel.modify (·.setContent number_ (.epoll kept))
    if !events.isEmpty || timeout == some 0 || due.any (· ≤ now) then
      timers.finish tid
      for ((revents, data), index) in events.zipIdx do
        let at_ := address + index * eventSize
        write emu at_ (numberBytes big 4 revents)
        write emu (at_ + eventData) (numberBytes big 8 data)
      succeed events.length
    else wait due (kept.map (·.file))
  -- A timeout in milliseconds, of which less than 0 is none.
  let millis (value : Nat) : Option Nat :=
    if value % 2 ^ 32 ≥ 2 ^ 31 then none else some (value % 2 ^ 32 * 1000000)
  -- A timeout of a `timespec`, of which none is none, or none at all of one that Linux doesn't take, which fails with `EINVAL`.
  let timespec (address field : Nat) : IO (Option (Option Nat)) := do
    if address == 0 then return some none
    pure ((← readSpan emu address field).map some)
  try
    match call with
    | .poll => poll (arg 0) (arg 1) (millis (arg 2))
    | .ppoll | .ppoll64 =>
      let some timeout ← timespec (arg 2) (if call == .ppoll64 then 8 else word) | fail einval
      if ← mask (arg 3) (arg 4) then return ← fail eintr
      poll (arg 0) (arg 1) timeout
    | .select =>
      -- Microseconds of a second or more are seconds, and of a negative time, `EINVAL`.
      let timeout ← if arg 4 == 0 then pure none else do
        let (seconds, micros) ← readTime emu (arg 4) word
        let some span := timeSpan (seconds + micros.tdiv 1000000, micros.tmod 1000000) 1000 | return ← fail einval
        pure (some span)
      select (arg 0) [arg 1, arg 2, arg 3] timeout
    | .pselect6 | .pselect664 =>
      let some timeout ← timespec (arg 4) (if call == .pselect664 then 8 else word) | fail einval
      if arg 5 != 0 then
        if ← mask (← number (arg 5) word) (← number (arg 5 + word) word) then return ← fail eintr
      select (arg 0) [arg 1, arg 2, arg 3] timeout
    | .epollCreate =>
      if arg 0 == 0 || arg 0 ≥ 2 ^ 31 then return ← fail einval
      let (kernel, fd) := (← poller.kernel.get).addObject group (.epoll []) 0
      poller.kernel.set kernel
      succeed fd
    | .epollCreate1 =>
      let given := flags (arg 0)
      if given &&& 0x80000 != given then return ← fail einval
      let (kernel, fd) := (← poller.kernel.get).addObject group (.epoll []) given
      poller.kernel.set kernel
      succeed fd
    | .epollCtl =>
      let kernel ← poller.kernel.get
      let .ok (epollNumber, _, inode) := kernel.objectOf group (arg 0) | return ← fail ebadf
      let .epoll items := inode.content | return ← fail einval
      let .ok (file, target) := kernel.openFileOf group (arg 2) | return ← fail ebadf
      if arg 0 == arg 2 || target.inode == epollNumber then return ← fail einval
      -- A file is always ready, which epoll doesn't take, as Linux has it.
      match kernel.inodes.get? target.inode with
      | some { content := .file _, .. } | some { content := .directory, .. } => return ← fail 1
      | _ => pure ()
      let existing := items.find? fun item => item.fd == arg 2 && item.file == file
      let event : IO (Nat × Nat) := do pure (← number (arg 3) 4, ← number (arg 3 + eventData) 8)
      let changed ← match arg 1, existing with
        | 1, none => do let (events, data) ← event; pure (items ++ [{ fd := arg 2, file, events, data }])
        | 1, some _ => return ← fail 17
        | 2, some _ => pure (items.filter fun item => !(item.fd == arg 2 && item.file == file))
        | 3, some _ => do
          let (events, data) ← event
          pure (items.map fun item => if item.fd == arg 2 && item.file == file then { item with events, data, told := none } else item)
        | 2, none | 3, none => return ← fail 2
        | _, _ => return ← fail einval
      poller.kernel.set (kernel.setContent epollNumber (.epoll changed))
      poller.wake emu
      succeed
    | .epollWait => epollWait (arg 0) (arg 1) (arg 2) (millis (arg 3))
    | .epollPwait =>
      if ← mask (arg 4) (arg 5) then return ← fail eintr
      epollWait (arg 0) (arg 1) (arg 2) (millis (arg 3))
    | .epollPwait2 =>
      let some timeout ← timespec (arg 3) 8 | fail einval
      if ← mask (arg 4) (arg 5) then return ← fail eintr
      epollWait (arg 0) (arg 1) (arg 2) timeout
    | .eventfd | .eventfd2 =>
      let given := if call == .eventfd then 0 else arg 1
      let semaphore := given &&& 1 != 0
      let given := flags (given &&& (2 ^ 32 - 2))
      if given &&& (0x80000 ||| 0x800) != given then return ← fail einval
      let (kernel, fd) := (← poller.kernel.get).addObject group (.eventfd (arg 0 % 2 ^ 32) semaphore) given
      poller.kernel.set kernel
      succeed fd
    | .timerfdCreate =>
      let given := flags (arg 1)
      if arg 0 > 11 || given &&& (0x80000 ||| 0x800) != given then return ← fail einval
      let (kernel, fd) := (← poller.kernel.get).addObject group (.timerfd none 0) given
      poller.kernel.set kernel
      succeed fd
    | .timerfdSettime | .timerfdSettime64 | .timerfdGettime | .timerfdGettime64 =>
      let field := if call == .timerfdSettime64 || call == .timerfdGettime64 then 8 else word
      let setting := call == .timerfdSettime || call == .timerfdSettime64
      -- What it sets, which fails with `EINVAL` before its descriptor is looked at, of a time that Linux doesn't take.
      let (some every, some value) ← if setting then pure (← readSpan emu (arg 2) field, ← readSpan emu (arg 2 + 2 * field) field)
        else pure (some 0, some 0) | fail einval
      let kernel ← poller.kernel.get
      let .ok (number_, _, inode) := kernel.objectOf group (arg 0) | return ← fail ebadf
      let .timerfd expiry interval := inode.content | return ← fail einval
      let spanBytes (nanoseconds : Nat) : ByteArray :=
        numberBytes big field (nanoseconds / 1000000000) ++ numberBytes big field (nanoseconds % 1000000000)
      let current := spanBytes interval ++ spanBytes ((expiry.map fun at_ => at_ - min at_ now).getD 0)
      if !setting then
        write emu (arg 1) current
        return ← succeed
      if arg 3 != 0 then write emu (arg 3) current
      let expiry := if value == 0 then none else some (if arg 1 &&& 1 != 0 then value else now + value)
      poller.kernel.set (kernel.setContent number_ (.timerfd expiry every))
      poller.wake emu
      succeed
    | .signalfd | .signalfd4 =>
      let given := if call == .signalfd then 0 else flags (arg 3)
      if given &&& (0x80000 ||| 0x800) != given then return ← fail einval
      let signals ← number (arg 1) (min (arg 2) 16)
      let kernel ← poller.kernel.get
      if arg 0 % 2 ^ 32 == 2 ^ 32 - 1 then
        let (kernel, fd) := kernel.addObject group (.signalfd signals) given
        poller.kernel.set kernel
        succeed fd
      else
        let .ok (number_, _, inode) := kernel.objectOf group (arg 0) | return ← fail ebadf
        let .signalfd _ := inode.content | return ← fail einval
        poller.kernel.set (kernel.setContent number_ (.signalfd signals))
        succeed (arg 0)
    | .read | .write =>
      let kernel ← poller.kernel.get
      let .ok (number_, _, inode) := kernel.objectOf group (arg 0) | return none
      let blocking ← do pure !(← nonblocking (arg 0))
      let waitFor (due : Option Nat) : IO (Option SyscallAction) := do
        if !blocking then fail eagain else pure (some (← timers.waitUntil emu readySpace 0 due true))
      match inode.content, call with
      | .eventfd count semaphore, .read =>
        if arg 2 < 8 then return ← fail einval
        if count == 0 then return ← waitFor none
        let taken := if semaphore then 1 else count
        write emu (arg 1) (numberBytes big 8 taken)
        poller.kernel.set (kernel.setContent number_ (.eventfd (count - taken) semaphore))
        poller.wake emu
        succeed 8
      | .eventfd count semaphore, .write =>
        if arg 2 < 8 then return ← fail einval
        let value ← number (arg 1) 8
        if value == 2 ^ 64 - 1 then return ← fail einval
        if count + value > 2 ^ 64 - 2 then return ← waitFor none
        poller.kernel.set (kernel.setContent number_ (.eventfd (count + value) semaphore))
        poller.wake emu
        succeed 8
      | .timerfd expiry interval, .read =>
        if arg 2 < 8 then return ← fail einval
        match expiry with
        | some at_ =>
          if at_ > now then return ← waitFor (some at_)
          let times := if interval > 0 then (now - at_) / interval + 1 else 1
          write emu (arg 1) (numberBytes big 8 times)
          poller.kernel.set (kernel.setContent number_ (.timerfd (if interval > 0 then some (at_ + times * interval) else none) interval))
          succeed 8
        | none => waitFor none
      | .signalfd signalMask, .read =>
        if arg 2 < 128 then return ← fail einval
        let mut taken := 0
        for index in [0:arg 2 / 128] do
          let some info ← poller.signals.takePending tid group signalMask | break
          let (pid, uid, status, value, address) := match info.detail with
            | .sent pid uid value => (pid, uid, 0, value, 0)
            | .child pid uid status => (pid, uid, status, 0, 0)
            | .fault address => (0, 0, 0, 0, address)
            | .seccomp address _ _ _ => (0, 0, 0, 0, address)
            | .timer _ _ value => (0, 0, 0, value, 0)
          let overrun := match info.detail with
            | .timer _ overrun _ => overrun
            | _ => 0
          let entry := numberBytes big 4 info.signal ++ numberBytes big 4 0 ++ numberBytes big 4 info.code ++ numberBytes big 4 pid ++
            numberBytes big 4 uid ++ numberBytes big 4 0 ++ numberBytes big 4 0 ++ numberBytes big 4 0 ++ numberBytes big 4 overrun ++
            numberBytes big 4 0 ++ numberBytes big 4 status ++ numberBytes big 4 value ++ numberBytes big 8 value ++
            numberBytes big 8 0 ++ numberBytes big 8 0 ++ numberBytes big 8 address
          write emu (arg 1 + index * 128) (entry ++ ByteArray.mk (Array.replicate (128 - entry.size) 0))
          taken := taken + 1
        if taken == 0 then waitFor none else succeed (taken * 128)
      | .timerfd .., .write | .signalfd _, .write | .epoll _, _ => fail einval
      | _, _ => pure none
    | _ => pure none
  catch _ => fail 14

end Poller

end Bap.Linux
