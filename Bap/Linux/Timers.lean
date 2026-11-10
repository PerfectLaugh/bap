import Bap.Linux.Ptrace
import Bap.Linux.Calls

/-! # Time that goes on

The clock of a machine is the kernel's, in nanoseconds: it goes on by a microsecond each time that it is read, and, when nothing can
run, to what happens next: a deadline of a call that waits with a timeout, or a timer. That is all that makes it go on, so that a run
is the same each time, however it is cut into turns, stopped, checkpointed or stepped back, and a sleep of a second takes a second of
the machine's time and none of the host's. A loop that waits for a timer without reading the clock or waiting for anything doesn't
see it come.

A sleep waits with its result, 0, which a signal makes `EINTR`, as Linux has it. A call that waits for something to be ready runs
again when it is woken, with the deadline that it had: see `Timers.waitUntil`. A futex gives `ETIMEDOUT` at its deadline.

The timers are those of `setitimer` and `alarm`, of each process, and those of `timer_create`. `ITIMER_VIRTUAL` and `ITIMER_PROF` go by
the same clock, as the machine's time is that of what it runs. A process that `fork` makes has none of them, and `execve` ends those of
`timer_create`. -/

namespace Bap.Linux

open Bap.Emu Bap.Tasks

/-- An interval timer of `setitimer`, or a timer of `timer_create`: the process and thread that hear of it, by what signal and with
what, when it next expires, if it is armed, and every how long after, and how many times it expired that the last of its signals
that was taken didn't say, or, of `SIGEV_NONE`, that it didn't count. -/
structure Timer where
  group : Nat
  thread : Option Nat := none
  /-- None, of `SIGEV_NONE`. -/
  signal : Option Nat
  code : Nat
  id : Nat := 0
  value : Nat := 0
  expiry : Option Nat := none
  interval : Nat := 0
  overrun : Nat := 0
  deriving Repr

/-- Of a call that waits and runs again when it is woken: where it ends, what its result register had at its start, which it has
again to run again, and whether a handler of `SA_RESTART` has it run again, as a read does, rather than give `EINTR`, as `poll`
does. -/
structure Site where
  next : Nat
  result : Nat
  restartable : Bool
  /-- Of MIPS, what `a3` had, which is an argument of the call and where an error is said, as the call runs again. -/
  flag : Nat := 0
  /-- Of a write to a pipe that waits for room for the rest, how much of it it wrote, which it doesn't again and gives if it ends here. -/
  written : Nat := 0
  /-- Of `semop`, the set, the semaphore and how much it waits to take of that, or 0 of one that waits for it to be 0, which `GETNCNT`
  and `GETZCNT` count. -/
  semaphore : Option (Nat × Nat × Nat) := none
  deriving Repr

/-- The timers, by the process and which they are: 0 to 2 of `setitimer` and `3 + id` of `timer_create`, the next id of
`timer_create` of each process, the deadline of each thread that waits with a timeout, and where the call of each that waits to run
again is. -/
structure TimeState where
  timers : Std.HashMap (Nat × Nat) Timer := {}
  nextTimer : Std.HashMap Nat Nat := {}
  deadlines : Std.HashMap Nat Nat := {}
  sites : Std.HashMap Nat Site := {}
  /-- Of a thread that sleeps, or waits with a timeout that `select`, `pselect6` and `ppoll` give back, with a `timespec` or a
  `timeval` for what is left: until when, where that is, of what size its fields are and of how many nanoseconds its fraction is, and,
  once a signal ended the wait, how long was left then, which it gets when it runs again. -/
  sleeps : Std.HashMap Nat (Nat × Nat × Nat × Nat × Option Nat) := {}

/-- Where a thread waits until its deadline, by its id. A signal ends that wait. -/
def sleepSpace : Nat := 2 ^ 60

/-- Whether a wait in a space has its result already, rather than `ETIMEDOUT` of a futex at its deadline: of a sleep, and of a call
that runs again when it is woken, which waits for a pipe, a socket or a descriptor to be ready, from `2 ^ 61` to the space of shared
futexes. -/
private def hasResult (space : Nat) : Bool := space == sleepSpace || (2 ^ 61 ≤ space && space < Kernel.fileSpace)

structure Timers where
  architecture : Architecture
  kernel : IO.Ref Kernel
  signals : Signals
  state : IO.Ref TimeState

namespace Timers

def modelId : String := "bap.timers"

def make (architecture : Architecture) (kernel : IO.Ref Kernel) (signals : Signals) : IO Timers := do
  pure { architecture, kernel, signals, state := ← IO.mkRef {} }

def now (timers : Timers) : IO Nat := do pure (← timers.kernel.get).clock

private def mips (timers : Timers) : Bool := timers.architecture matches .mips ..

/-- The signal of `setitimer` of each of its timers: SIGALRM, SIGVTALRM and SIGPROF. -/
private def itimerSignal (timers : Timers) (which : Nat) : Nat :=
  match which, timers.mips with
  | 0, _ => 14
  | 1, false => 26
  | 1, true => 28
  | _, false => 27
  | _, true => 29

/-- The timers that are due: each signals, once for however many times it expired, and is armed again by its interval. A timer of
`timer_create` whose signal is still pending has that signal say that it expired again, rather than send another. Whether any was
due. -/
private def fire (timers : Timers) (emu : Emu) : IO Bool := do
  let now ← timers.now
  let state ← timers.state.get
  let due := state.timers.toList.filter fun (_, timer) => timer.expiry.any (· ≤ now)
  if due.isEmpty then return false
  let table ← emu.taskTable.get
  for (key, timer) in due do
    let some expiry := timer.expiry | continue
    let periods := if timer.interval > 0 then (now - expiry) / timer.interval + 1 else 1
    let alive := table.tasks.any fun task => task.group == timer.group && task.status.isNone
    if !alive then
      timers.state.modify fun state => { state with timers := state.timers.erase key }
      continue
    timers.state.modify fun state => { state with timers := state.timers.insert key { timer with
      expiry := if timer.interval > 0 then some (expiry + periods * timer.interval) else none
      overrun := if timer.signal.isNone then periods - 1 else timer.overrun } }
    if let some signal := timer.signal then
      if key.2 ≥ 3 && (← timers.signals.addOverrun emu timer.group signal timer.id periods) then continue
      let detail : SignalDetail := if key.2 < 3 then .sent 0 0 0 else .timer timer.id (periods - 1) timer.value
      let thread := timer.thread.filter fun tid => table.tasks.any fun task => task.tid == tid && task.status.isNone
      timers.signals.send emu thread timer.group ⟨signal, timer.code, detail⟩
  pure true

/-- A signal of a process was taken: of a timer of `timer_create`, what it said that the timer expired and it didn't say is what
`timer_getoverrun` gives, until the next is taken. -/
def taken (timers : Timers) (group : Nat) (info : SignalInfo) : IO Unit := do
  let .timer id overrun _ := info.detail | return
  timers.state.modify fun state => { state with timers := state.timers.modify (group, 3 + id) ({ · with overrun }) }

/-- What waits until a time that has come goes on: a call that runs again, which finds that its time has come, and a futex, which
gives `ETIMEDOUT`. Whether anything did. -/
private def wakeDue (timers : Timers) (emu : Emu) : IO Bool := do
  let now ← timers.now
  let table ← emu.taskTable.get
  let due := table.futexes.filter fun waiter => waiter.deadline.any (· ≤ now)
  if due.isEmpty then return false
  emu.taskTable.set { table with futexes := table.futexes.filter fun waiter => !waiter.deadline.any (· ≤ now) }
  for waiter in due do
    unless hasResult waiter.space do
      setSyscallResult emu waiter.thread (.error (if timers.mips then 145 else 110))
    wakeThread emu waiter.thread
  pure true

/-- What is due happens, of the time that reads of the clock made go on. -/
def tick (timers : Timers) (emu : Emu) : IO Unit := do
  let _ ← timers.fire emu
  let _ ← timers.wakeDue emu

/-- How late a thread that nothing but time woke runs, in nanoseconds: Linux's `timer_slack_ns` of a thread, 50 µs, by which a sleep may
end late, which is more than a wake from an interrupt takes. What it ran before it slept, as what it timed from, is then before the time
that it asked for, as on a device. -/
def wakeLatency : Nat := 50000

/-- Nothing can run: time goes on to what happens next, a deadline or a timer, if anything does, and `wakeLatency` after it. Whether
anything changed. -/
def idle (timers : Timers) (emu : Emu) : IO Bool := do
  let deadlines := (← emu.taskTable.get).futexes.filterMap (·.deadline)
  let expiries := (← timers.state.get).timers.toList.filterMap (·.2.expiry)
  let some next := (deadlines ++ expiries).min? | return false
  if next > (← timers.now) then timers.kernel.modify fun kernel => { kernel with clock := next + wakeLatency }
  let fired ← timers.fire emu
  let woke ← timers.wakeDue emu
  pure (fired || woke)

/-- The deadline of the call of a thread that waits with a timeout: the one that it had, as it runs again, or this one. -/
def deadlineOf (timers : Timers) (tid : Nat) (deadline : IO Nat) : IO Nat := do
  if let some known := (← timers.state.get).deadlines.get? tid then return known
  let deadline ← deadline
  timers.state.modify fun state => { state with deadlines := state.deadlines.insert tid deadline }
  pure deadline

/-- The call of a thread is over, and with it its deadline. -/
def finish (timers : Timers) (tid : Nat) : IO Unit :=
  timers.state.modify fun state => { state with deadlines := state.deadlines.erase tid, sites := state.sites.erase tid }

/-- A call starts: what a thread has of one before it, a deadline that a call kept as it failed before it waited, or the site of one
that ended without `finish`, is gone, but for the call that runs again where it waited. -/
def entered (timers : Timers) (emu : Emu) : IO Unit := do
  let tid ← thread emu
  let state ← timers.state.get
  if !state.deadlines.contains tid && !state.sites.contains tid then return
  let next ← emu.nextPc.get
  if !(state.sites.get? tid).any (·.next == next) then timers.finish tid

/-- Whether the call that runs is one that waited and runs again where it waited. -/
def again (timers : Timers) (emu : Emu) : IO Bool := do
  let next ← emu.nextPc.get
  pure (((← timers.state.get).sites.get? (← thread emu)).any (·.next == next))

/-- How much the write that runs again where it waited wrote before, as `waitUntil` was told, or 0. -/
def written (timers : Timers) (emu : Emu) : IO Nat := do
  let next ← emu.nextPc.get
  pure ((((← timers.state.get).sites.get? (← thread emu)).filter (·.next == next)).map (·.written) |>.getD 0)

/-- The thread that runs waits in `space`, for `address`, until something wakes it there or its deadline comes, if it has one, and
then runs its call again, with its registers as they were, having `written` bytes of a write already. A signal that comes first has it
run again or give `EINTR`, as `restartable` says of a handler of `SA_RESTART`, or give what it wrote: see `interrupted`. -/
def waitUntil (timers : Timers) (emu : Emu) (space address : Nat) (deadline : Option Nat) (restartable : Bool) (written : Nat := 0)
    (semaphore : Option (Nat × Nat × Nat) := none) : IO SyscallAction := do
  let tid ← thread emu
  let action ← Ptrace.again emu
  let result := match action with
    | .returnValue value => value
    | .default => 0
  let next ← emu.nextPc.get
  let flag ← if timers.mips then do
      match Value.asBits (← reg emu ⟨"R7", .imm timers.architecture.bits, 0, false⟩) with
      | .ok bits => pure bits.2.toNat
      | .error _ => pure 0
    else pure 0
  timers.state.modify fun state => { state with sites := state.sites.insert tid { next, result, restartable, flag, written, semaphore } }
  emu.taskTable.modify (·.futexWait { thread := tid, space, address, bitset := 2 ^ 32 - 1, deadline })
  emu.stopped.set true
  pure action

/-- A signal woke a thread from what it waited in. Of a call that runs again, which waited from `2 ^ 61` to the space of shared
futexes: a write that wrote some of what it was given goes on past the call with that, and otherwise it runs again with the registers
that it had, of a handler of `SA_RESTART` and a call that it restarts, or goes on past the call with `EINTR`, which the signals gave it,
and its deadline is gone either way. -/
def interrupted (timers : Timers) (emu : Emu) (tid : Nat) (restart : Bool) (spaces : List Nat) (traced : Bool := false) : IO Unit := do
  -- Of a tracee, the call runs again as it was, to the deadline that it had, as no handler ends it.
  if traced then
    timers.state.modify fun state => { state with sites := state.sites.erase tid }
    return
  -- A sleep, or a wait with a timeout to give back, that a signal ended has what was left of it then.
  if spaces.any hasResult then
    let now ← timers.now
    timers.state.modify fun state => { state with sleeps := state.sleeps.modify tid fun (deadline, address, field, scale, _) =>
      (deadline, address, field, scale, some (deadline - min deadline now)) }
  unless spaces.any fun space => 2 ^ 61 ≤ space && space < Kernel.fileSpace do return
  let some site := (← timers.state.get).sites.get? tid | return
  timers.finish tid
  if site.written > 0 then
    setSyscallResult emu tid (.ok site.written)
    setThreadPc emu tid site.next
  else if restart && site.restartable then
    let width := timers.architecture.bits
    let (_, _, register) := syscallRegisters emu.config.syscallAbi
    setThreadReg emu tid ⟨register, .imm width, 0, false⟩ (.bits (BitVec.ofNat width site.result))
    if timers.mips then setThreadReg emu tid ⟨"R7", .imm width, 0, false⟩ (.bits (BitVec.ofNat width site.flag))
  else setThreadPc emu tid site.next

/-- What is left, in nanoseconds, goes to `address` as a `timespec`, or a `timeval` of `scale` 1000, of fields of `field` bytes; a
fault there leaves the call as it is, as Linux has it. -/
private def writeLeft (timers : Timers) (emu : Emu) (address field scale left : Nat) : IO Unit := do
  let big := timers.architecture.big
  try write emu address (Abi.field big field (left / 1000000000) ++ Abi.field big field (left % 1000000000 / scale)) catch _ => pure ()

/-- The thread that runs again after a sleep or a wait: of one that a signal ended, what was left of it goes where the call said. -/
def resumed (timers : Timers) (emu : Emu) : IO Unit := do
  let tid ← thread emu
  let some (_, address, field, scale, left) := (← timers.state.get).sleeps.get? tid | return
  timers.state.modify fun state => { state with sleeps := state.sleeps.erase tid }
  if let some left := left then timers.writeLeft emu address field scale left

/-- What is left until `deadline` of the timeout of the call of the thread that runs goes to `address`, as `writeLeft` has it, as
`select`, `pselect6` and `ppoll` give it back: now, as the call ends, or, of one that `waits`, once a signal ends the wait. -/
def giveBack (timers : Timers) (emu : Emu) (deadline address field scale : Nat) (waits : Bool) : IO Unit := do
  let tid ← thread emu
  if waits then
    timers.state.modify fun state => { state with sleeps := state.sleeps.insert tid (deadline, address, field, scale, none) }
  else
    timers.state.modify fun state => { state with sleeps := state.sleeps.erase tid }
    timers.writeLeft emu address field scale (deadline - min deadline (← timers.now))

/-- A process is over, and with it its timers, and what threads that are gone waited with. -/
def exited (timers : Timers) (emu : Emu) (group : Nat) : IO Unit := do
  let live := ((← emu.taskTable.get).tasks.filter (·.status.isNone)).map (·.tid)
  timers.state.modify fun state => { state with
    timers := state.timers.filter fun (owner, _) _ => owner != group
    nextTimer := state.nextTimer.erase group
    deadlines := state.deadlines.filter fun tid _ => live.contains tid
    sites := state.sites.filter fun tid _ => live.contains tid
    sleeps := state.sleeps.filter fun tid _ => live.contains tid }

/-- A process that `fork` made has no timers of its parent, and `execve` ends those of `timer_create` of a process. -/
def executed (timers : Timers) (group : Nat) : IO Unit :=
  timers.state.modify fun state => { state with timers := state.timers.filter fun (owner, which) _ => owner != group || which < 3 }

private def numberOf (big : Bool) (bytes : ByteArray) : Nat :=
  let ordered := if big then bytes.toList else bytes.toList.reverse
  ordered.foldl (fun value byte => value * 256 + byte.toNat) 0

private def numberBytes (big : Bool) (size value : Nat) : ByteArray :=
  let little := (List.range size).map fun index => (value >>> (8 * index)).toUInt8
  ByteArray.mk (if big then little.reverse else little).toArray

/-- `nanosleep`, `clock_nanosleep`, `setitimer`, `getitimer`, `alarm` and those of `timer_create`, if the call is one of them. -/
def serve (timers : Timers) (emu : Emu) (call : Call) (args : List Nat) : IO (Option SyscallAction) := do
  let architecture := timers.architecture
  let big := architecture.big
  let word := architecture.bits / 8
  let arg (index : Nat) : Nat := args.getD index 0
  let tid ← thread emu
  let group := (← currentTask emu).group
  let number (address size : Nat) : IO Nat := do pure (numberOf big (← read emu address size))
  let einval : Nat := 22
  let fail (errno : Nat) : IO (Option SyscallAction) := do pure (some (.returnValue (2 ^ 64 - errno)))
  let succeed (value : Nat := 0) : IO (Option SyscallAction) := do pure (some (.returnValue value))
  let spanBytes (nanoseconds field scale : Nat) : ByteArray :=
    numberBytes big field (nanoseconds / 1000000000) ++ numberBytes big field (nanoseconds % 1000000000 / scale)
  let now ← timers.now
  let remaining (timer : Timer) : Nat := (timer.expiry.map fun expiry => expiry - min expiry now).getD 0
  -- A sleep until a deadline, which gives 0 then, or `EINTR` if a signal comes first.
  -- A sleep, and where what is left of it goes if a signal ends it, with the size of the fields there.
  let sleep (deadline : Nat) (remaining : Option (Nat × Nat) := none) : IO (Option SyscallAction) := do
    if deadline > now then
      emu.taskTable.modify (·.futexWait { thread := tid, space := sleepSpace, address := tid, bitset := 2 ^ 32 - 1, deadline })
      emu.stopped.set true
      if let some (address, field) := remaining.filter (·.1 != 0) then
        timers.state.modify fun state => { state with sleeps := state.sleeps.insert tid (deadline, address, field, 1, none) }
    succeed
  -- What a timer is now, as `itimerval` or `itimerspec`: the interval, then what is left of it.
  let current (timer : Option Timer) (field scale : Nat) : ByteArray :=
    match timer with
    | some timer => spanBytes timer.interval field scale ++ spanBytes (remaining timer) field scale
    | none => spanBytes 0 field scale ++ spanBytes 0 field scale
  let setTimer (key : Nat × Nat) (fresh : Timer) (value : Nat) (interval : Nat) (absolute : Bool) : IO Unit :=
    timers.state.modify fun state =>
      let timer := (state.timers.get? key).getD fresh
      { state with timers := state.timers.insert key { timer with
          expiry := if value == 0 then none else some (if absolute then value else now + value), interval, overrun := 0 } }
  let itimer (which : Nat) : Timer := { group, signal := some (timers.itimerSignal which), code := 0x80 }
  try
    match call with
    | .nanosleep =>
      let some given ← readSpan emu (arg 0) word | fail einval
      sleep (now + given) (some (arg 1, word))
    | .clockNanosleep | .clockNanosleep64 =>
      if arg 0 > 11 || arg 0 == 10 then return ← fail einval
      -- Of the thread's time and of the clocks that are coarse or raw, there is no sleep.
      if 3 ≤ arg 0 && arg 0 ≤ 6 then return ← fail Errno.eopnotsupp
      let field := if call == .clockNanosleep64 then 8 else word
      let some given ← readSpan emu (arg 2) field | fail einval
      -- What is left of a sleep until a time is nothing to say.
      sleep (if arg 1 &&& 1 != 0 then given else now + given) (if arg 1 &&& 1 != 0 then none else some (arg 3, field))
    | .setitimer =>
      -- Of no value, none: the timer is disarmed, as Linux has it of a NULL.
      let given ← if arg 1 == 0 then pure (some (0, 0)) else do
        let (some interval, some value) := (← readSpan emu (arg 1) word 1000, ← readSpan emu (arg 1 + 2 * word) word 1000)
          | return ← fail einval
        pure (some (interval, value))
      if arg 0 > 2 then return ← fail einval
      let key := (group, arg 0)
      if arg 2 != 0 then write emu (arg 2) (current ((← timers.state.get).timers.get? key) word 1000)
      if let some (interval, value) := given then setTimer key (itimer (arg 0)) value interval false
      succeed
    | .getitimer =>
      if arg 0 > 2 then return ← fail einval
      write emu (arg 1) (current ((← timers.state.get).timers.get? (group, arg 0)) word 1000)
      succeed
    | .alarm =>
      let left := ((← timers.state.get).timers.get? (group, 0)).map remaining |>.getD 0
      setTimer (group, 0) (itimer 0) (arg 0 * 1000000000) 0 false
      -- To the nearest second, as `alarm_setitimer` has it, but none of what is left isn't 0.
      let seconds := (left + 500000000) / 1000000000
      succeed (if seconds == 0 && left > 0 then 1 else seconds)
    | .timerCreate =>
      if arg 0 > 11 then return ← fail einval
      let id := ((← timers.state.get).nextTimer.get? group).getD 0
      -- `struct sigevent`: the value, the signal, how it is told, and the thread of SIGEV_THREAD_ID; without one, SIGALRM with the id.
      let (signal, value, thread, notify) ← if arg 1 == 0 then pure (some 14, id, none, 0) else do
        let notify ← number (arg 1 + word + 4) 4
        let signal ← number (arg 1 + word) 4
        let value ← number (arg 1) word
        let thread ← if notify == 4 then some <$> number (arg 1 + word + 8) 4 else pure none
        pure (if notify == 1 then none else some signal, value, thread, notify)
      if notify != 0 && notify != 1 && notify != 4 then return ← fail einval
      -- As `good_sigevent` has it: a signal that there is, and a thread of the process.
      if notify != 1 && arg 1 != 0 && (signal.getD 0 == 0 || signal.getD 0 > (if timers.mips then 128 else 64)) then
        return ← fail einval
      if let some tid := thread then
        unless (← emu.taskTable.get).tasks.any fun task => task.tid == tid && task.group == group && task.status.isNone do
          return ← fail einval
      write emu (arg 2) (numberBytes big 4 id)
      timers.state.modify fun state => { state with
        nextTimer := state.nextTimer.insert group (id + 1)
        timers := state.timers.insert (group, 3 + id) { group, thread, signal, code := 2 ^ 32 - 2, id, value } }
      succeed
    | .timerSettime | .timerSettime64 =>
      let field := if call == .timerSettime64 then 8 else word
      let (some interval, some value) := (← readSpan emu (arg 2) field, ← readSpan emu (arg 2 + 2 * field) field) | fail einval
      let key := (group, 3 + arg 0)
      let some timer := (← timers.state.get).timers.get? key | return ← fail einval
      if arg 3 != 0 then write emu (arg 3) (current (some timer) field 1)
      setTimer key timer value interval (arg 1 &&& 1 != 0)
      timers.signals.forgetTimer emu group timer.id
      succeed
    | .timerGettime | .timerGettime64 =>
      let field := if call == .timerGettime64 then 8 else word
      let some timer := (← timers.state.get).timers.get? (group, 3 + arg 0) | return ← fail einval
      write emu (arg 1) (current (some timer) field 1)
      succeed
    | .timerGetoverrun =>
      let some timer := (← timers.state.get).timers.get? (group, 3 + arg 0) | return ← fail einval
      succeed timer.overrun
    | .timerDelete =>
      let key := (group, 3 + arg 0)
      let some timer := (← timers.state.get).timers.get? key | return ← fail einval
      timers.state.modify fun state => { state with timers := state.timers.erase key }
      timers.signals.forgetTimer emu group timer.id
      succeed
    | _ => pure none
  catch _ => fail 14

open Wire in
private def putTimer (out : ByteArray) (entry : (Nat × Nat) × Timer) : ByteArray :=
  let ((group, which), timer) := entry
  let out := putOption putNat (putNat (putNat (putNat out group) which) timer.group) timer.thread
  let out := putOption putNat out timer.signal
  let out := putNat (putNat (putNat out timer.code) timer.id) timer.value
  putNat (putNat (putOption putNat out timer.expiry) timer.interval) timer.overrun

open Wire in
private def getTimer : Decoder ((Nat × Nat) × Timer) := fun data at_ => do
  let (key, at_) ← getNat data at_
  let (which, at_) ← getNat data at_
  let (group, at_) ← getNat data at_
  let (thread, at_) ← getOption getNat data at_
  let (signal, at_) ← getOption getNat data at_
  let (code, at_) ← getNat data at_
  let (id, at_) ← getNat data at_
  let (value, at_) ← getNat data at_
  let (expiry, at_) ← getOption getNat data at_
  let (interval, at_) ← getNat data at_
  let (overrun, at_) ← getNat data at_
  .ok (((key, which), { group, thread, signal, code, id, value, expiry, interval, overrun }), at_)

open Wire in
/-- What a checkpoint has of the timers and the deadlines: the same state makes the same bytes. -/
def save (timers : Timers) : IO ByteArray := do
  let state ← timers.state.get
  let out := putSorted putTimer ByteArray.empty state.timers.toList
  let pair (out : ByteArray) (entry : Nat × Nat) : ByteArray := putNat (putNat out entry.1) entry.2
  let out := putSorted pair out state.nextTimer.toList
  let out := putSorted pair out state.deadlines.toList
  let semaphore (out : ByteArray) (entry : Nat × Nat × Nat) : ByteArray := putNat (putNat (putNat out entry.1) entry.2.1) entry.2.2
  let out := putSorted (fun out (tid, site) =>
    putOption semaphore (putNat (putNat (putFlag (putNat (putNat (putNat out tid) site.next) site.result) site.restartable) site.flag)
      site.written) site.semaphore) out state.sites.toList
  pure (putSorted (fun out (tid, deadline, address, field, scale, left) =>
    putOption putNat (putNat (putNat (putNat (putNat (putNat out tid) deadline) address) field) scale) left) out state.sleeps.toList)

open Wire in
def load (timers : Timers) (data : ByteArray) : IO Unit := do
  let pair : Decoder (Nat × Nat) := fun data at_ => do
    let (first, at_) ← getNat data at_
    let (second, at_) ← getNat data at_
    .ok ((first, second), at_)
  let decoded : Except String TimeState := do
    let (entries, at_) ← getList getTimer data 0
    let (nextTimer, at_) ← getList pair data at_
    let (deadlines, at_) ← getList pair data at_
    let (sites, at_) ← getList (fun data at_ => do
      let (tid, at_) ← getNat data at_
      let (next, at_) ← getNat data at_
      let (result, at_) ← getNat data at_
      let (restartable, at_) ← getFlag data at_
      let (flag, at_) ← getNat data at_
      let (written, at_) ← getNat data at_
      let (semaphore, at_) ← getOption (fun data at_ => do
        let (set, at_) ← getNat data at_
        let (which, at_) ← getNat data at_
        let (amount, at_) ← getNat data at_
        .ok ((set, which, amount), at_)) data at_
      .ok ((tid, { next, result, restartable, flag, written, semaphore }), at_)) data at_
    let (sleeps, at_) ← getList (fun data at_ => do
      let (tid, at_) ← getNat data at_
      let (deadline, at_) ← getNat data at_
      let (address, at_) ← getNat data at_
      let (field, at_) ← getNat data at_
      let (scale, at_) ← getNat data at_
      let (left, at_) ← getOption getNat data at_
      .ok ((tid, (deadline, address, field, scale, left)), at_)) data at_
    expectEnd data at_
    pure { timers := Std.HashMap.ofList entries, nextTimer := Std.HashMap.ofList nextTimer, deadlines := Std.HashMap.ofList deadlines
           sites := Std.HashMap.ofList sites, sleeps := Std.HashMap.ofList sleeps }
  timers.state.set (← IO.ofExcept decoded)

end Timers

end Bap.Linux
