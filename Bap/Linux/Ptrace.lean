import Bap.Linux.Signals

/-! # ptrace, stopped processes, and waiting for them

What a process can see of another and do to it: `ptrace`, which makes one the tracer of another, the tracee, that stops for each
signal that is to be delivered to it, for a fault, after `execve`, at `PTRACE_INTERRUPT`, after a step and at system calls, until its
tracer lets it go on, with a signal or without; and in a stop, the tracer reads and writes its memory and its registers. Stops that
aren't of a tracee are those of a process that SIGSTOP or SIGTSTP stops, as a shell's job control has them, until SIGCONT.

`wait4`, `waitpid` and `waitid` are served here, as they say what a process stopped for as well as how it ended: a stop of a tracee
to its tracer, a stop or a continue of a child to its parent when asked for, and an exit, of a child or of a tracee. A wait that has to
wait waits until something happens to what it waits for, and asks again.

A stopped thread is blocked as a futex has it, so that the others go on. What is traced, stopped or not yet reported is in a checkpoint,
as the model `bap.ptrace`. -/

namespace Bap.Linux

open Bap.Emu Bap.Tasks

/-- A traced thread, of what its tracer said of it. -/
structure Tracee where
  /-- The process that traces it. -/
  tracer : Nat
  options : Nat := 0
  seized : Bool := false
  /-- Whether it stops at the start and the end of each system call, as `PTRACE_SYSCALL` has it, and whether it is in one. -/
  syscalls : Bool := false
  inSyscall : Bool := false
  deriving DecidableEq, Repr

/-- A thread that is stopped: what `wait` says of it, whether that is of a tracee, whether it was said, and the `siginfo_t` of what stopped
it, as its signal, code and the address or the process that it is of. A stop of a fault is gone on from by the fault coming again. -/
structure Stop where
  status : Nat
  traced : Bool
  reported : Bool := false
  signal : Nat
  code : Nat := 0
  detail : Nat := 0
  fault : Bool := false
  deriving DecidableEq, Repr

/-- A wait that waits: of what, for what, and where what it finds goes, as `wait4` (its status and usage) or `waitid` has it. -/
structure WaitRequest where
  target : Option Nat
  exited : Bool
  stopped : Bool
  continued : Bool
  keep : Bool
  waitid : Bool
  /-- `__WCLONE`, which has it see only clone children, and `__WALL`, which has it see all children: see `Tasks.Entry.exitSignal`. -/
  clones : Bool := false
  all : Bool := false
  status : Nat
  usage : Nat
  deriving DecidableEq, Repr

structure PtraceTable where
  /-- The waits that wait, by thread. -/
  waiting : Std.HashMap Nat WaitRequest := {}
  tracees : Std.HashMap Nat Tracee := {}
  stops : Std.HashMap Nat Stop := {}
  /-- Processes that SIGCONT let go on and that no wait said so of. -/
  continued : List Nat := []
  /-- The signal that a tracer let a thread have, which goes through to it rather than stopping it. -/
  injected : Std.HashMap Nat Nat := {}
  /-- What `PTRACE_GETEVENTMSG` says of a thread. -/
  messages : Std.HashMap Nat Nat := {}
  /-- Exits of tracees that a tracer that isn't their parent has yet to be told of, oldest first: by tracer, tracee and how it ended.
  They are kept here, as the tracee is gone from what is traced when its process is. -/
  untold : List (Nat × Nat × Nat) := []
  /-- Where a thread that steps went on from, which it stops after running. -/
  stepping : Std.HashMap Nat Nat := {}
  /-- The stops that a thread has yet to make, one each time that its tracer lets it go on: `PTRACE_EVENT_VFORK_DONE` after
  `PTRACE_EVENT_VFORK`. -/
  pending : Std.HashMap Nat (List Stop) := {}
  /-- The threads that stopped for `PTRACE_EVENT_EXIT`, whose call to end goes through when it is made again. -/
  exiting : List Nat := []
  /-- Of each traced thread, the number and the first argument of the system call that it last started, which `orig_rax` and the like
  are: the registers have its result once it is made. -/
  calls : Std.HashMap Nat (Nat × Nat) := {}
  /-- Of a thread stopped at the start of a system call, of a target whose result is in the register of its number: the number that it
  is to make and what it gives if that is none, which `orig_rax` and `rax` are there, as Linux has it, until it goes on. -/
  entries : Std.HashMap Nat (Nat × Nat) := {}
  /-- The threads whose next call is not made, as their tracer said, with what it gives. -/
  skipping : Std.HashMap Nat Nat := {}
  /-- Processes that are over whose parent doesn't wait for them, as it ignores `SIGCHLD` or has `SA_NOCLDWAIT`: no wait reports them,
  and they go once they don't run. -/
  reaping : List Nat := []

/-- The ptrace and the stops of a machine. -/
structure Ptrace where
  architecture : Architecture
  signals : Signals
  table : IO.Ref PtraceTable
  /-- The hooks of threads that step, by thread. -/
  stepHooks : IO.Ref (Std.HashMap Nat HookId)
  /-- What gives each wait that waits what it waits for, if it is there now. -/
  settle : IO.Ref (Emu → IO Unit)
  /-- Whether anything happened since the waits were last given what they wait for: a wait has nothing new to find otherwise, and isn't
  asked again, as asking takes as long as there are tasks. -/
  changed : IO.Ref Bool
  /-- What a wait says of the process that it reports, from its id here: the same, unless the host gives the guest ids of its own.
  It is a function, which isn't in a checkpoint: the host gives it again to a machine that goes on from one. -/
  resultOf : IO.Ref (Nat → Nat)
  /-- Of each thread in a call that makes a process or a thread, which a tracer is to hear of: the event, and the first id that the
  call can give. Nothing is in the middle of a call when a checkpoint is made. -/
  cloning : IO.Ref (Std.HashMap Nat (Nat × Nat))
  /-- What decides of a call of a thread, by its number and its arguments, after its tracer saw it start and before anything serves
  it: what `Bap.Linux.Seccomp` makes of it, if anything. -/
  screen : IO.Ref (Emu → Nat → Nat → List Nat → IO (Option SyscallAction))

namespace Ptrace

private structure Numbers where
  ptrace : Nat
  wait4 : Nat
  waitpid : Option Nat
  waitid : Nat
  stop : Nat
  cont : Nat
  chld : Nat
  trap : Nat := 5
  kill : Nat := 9
  /-- The calls that make a process or a thread, and those that end one. -/
  clone : Nat
  clone3 : Nat := 435
  fork : Option Nat := none
  vfork : Option Nat := none
  exit : Nat
  exitGroup : Nat

private def numbersOf : Architecture → Numbers
  | .x86_64 => { ptrace := 101, wait4 := 61, waitpid := none, waitid := 247, stop := 19, cont := 18, chld := 17, clone := 56,
                 fork := some 57, vfork := some 58, exit := 60, exitGroup := 231 }
  | .aarch64 | .riscv64 | .riscv32 => { ptrace := 117, wait4 := 260, waitpid := none, waitid := 95, stop := 19, cont := 18, chld := 17,
                                         clone := 220, exit := 93, exitGroup := 94 }
  | .arm => { ptrace := 26, wait4 := 114, waitpid := none, waitid := 280, stop := 19, cont := 18, chld := 17, clone := 120, fork := some 2,
              vfork := some 190, exit := 1, exitGroup := 248 }
  | .i686 => { ptrace := 26, wait4 := 114, waitpid := some 7, waitid := 284, stop := 19, cont := 18, chld := 17, clone := 120,
               fork := some 2, vfork := some 190, exit := 1, exitGroup := 252 }
  | .mips 32 _ _ => { ptrace := 4026, wait4 := 4114, waitpid := some 4007, waitid := 4278, stop := 23, cont := 25, chld := 18,
                      clone := 4120, clone3 := 4435, fork := some 4002, exit := 4001, exitGroup := 4246 }
  | .mips _ _ _ => { ptrace := 5099, wait4 := 5059, waitpid := none, waitid := 5237, stop := 23, cont := 25, chld := 18, clone := 5055,
                     clone3 := 5435, fork := some 5056, exit := 5058, exitGroup := 5205 }
  | .powerpc _ _ => { ptrace := 26, wait4 := 114, waitpid := some 7, waitid := 272, stop := 19, cont := 18, chld := 17, clone := 120,
                      fork := some 2, vfork := some 189, exit := 1, exitGroup := 234 }

/-- The events of `PTRACE_O_TRACE*`, each of which has the option `1 <<< event`. -/
private def forkEvent : Nat := 1
private def vforkEvent : Nat := 2
private def cloneEvent : Nat := 3
private def vforkDoneEvent : Nat := 5
private def exitEvent : Nat := 6
private def seccompEvent : Nat := 7

/-- Whether an event is of a call that was made, after which its end comes, rather than before it is made: `PTRACE_EVENT_EXIT` and
`PTRACE_EVENT_SECCOMP` stop a call that is made when the tracee goes on. -/
private def afterCall (event : Nat) : Bool := event ≥ forkEvent && event ≤ vforkDoneEvent

/-- Which event a call that makes a process or a thread is, of its flags, as Linux has it: none of one that says `CLONE_UNTRACED`,
`PTRACE_EVENT_VFORK` of `CLONE_VFORK`, `PTRACE_EVENT_CLONE` of one that signals other than `SIGCHLD` when it ends, as a thread
doesn't, and `PTRACE_EVENT_FORK` otherwise. -/
private def eventOfClone (chld flags : Nat) : Nat :=
  if flags &&& 0x800000 != 0 then 0
  else if flags &&& 0x4000 != 0 then vforkEvent
  else if flags % 256 != chld then cloneEvent
  else forkEvent

private def esrch : Nat := 3
private def eio : Nat := 5
private def echild : Nat := 10
private def efault : Nat := 14
private def einval : Nat := 22
private def eperm : Nat := 1

/-- Where stopped threads wait, by thread, and where waits wait, by process: no guest can wake them, as this isn't memory that it has. -/
private def waitSpace : Nat := 2 ^ 58 + 2 ^ 48

private def stoppedStatus (signal : Nat) (event : Nat := 0) : Nat := 0x7f ||| (signal <<< 8) ||| (event <<< 16)

private def numbers (ptrace : Ptrace) : Numbers := numbersOf ptrace.architecture

private def groupOf (emu : Emu) (tid : Nat) : IO Nat := do
  pure (((← emu.taskTable.get).find? tid).map (·.group) |>.getD tid)

/-- Whether a thread waits for its child of `vfork`. -/
private def vforkWaiting (table : TaskTable) (tid : Nat) : Bool :=
  table.futexes.any fun waiter => waiter.thread == tid && waiter.space == vforkSpace

/-- Blocks a thread where nothing but its tracer or SIGCONT lets it go: the thread that runs, or another, which the scheduler would
pick otherwise, as it goes by what is stopped, until `release`. -/
private def block (emu : Emu) (tid : Nat) : IO Unit := do
  emu.taskTable.modify fun table =>
    if table.futexes.any fun waiter => waiter.thread == tid && waiter.space == stopSpace then table
    else table.futexWait { thread := tid, space := stopSpace, address := tid, bitset := 2 ^ 32 - 1 }
  Bap.Emu.stopThread emu tid

/-- Lets a stopped thread go on. -/
private def release (ptrace : Ptrace) (emu : Emu) (tid : Nat) : IO Unit := do
  ptrace.table.modify fun table => { table with stops := table.stops.erase tid }
  emu.taskTable.modify fun table =>
    { table with futexes := table.futexes.filter fun waiter => !(waiter.thread == tid && waiter.space == stopSpace) }
  -- The parent of `vfork` waits for its child still.
  wakeThread emu tid

/-- Something has happened that a wait may be waiting for, which it is given between turns, when what made it happen is over: a
process that exited has left all that it wrote where others see it. -/
private def wakeWaits (ptrace : Ptrace) : IO Unit := ptrace.changed.set true

/-- The processes that are over that no one waits for go, of those that can: not one that runs, which needs its memory until it is left,
nor one that a tracer has yet to hear of. -/
private def reapUnwaited (ptrace : Ptrace) (emu : Emu) : IO Unit := do
  let table ← ptrace.table.get
  if table.reaping.isEmpty then return
  let running ← groupOf emu (← thread emu)
  let (now, later) := table.reaping.partition fun pid => pid != running && !table.untold.any (·.2.1 == pid)
  if now.isEmpty then return
  ptrace.table.set { table with reaping := later }
  emu.taskTable.modify fun tasks => now.foldl TaskTable.reap tasks
  collectGone emu
  wakeWaits ptrace

/-- A process that is over goes without a wait if it sends SIGCHLD to a parent that doesn't wait for its children, as Linux has it, once
the parent has heard of it. -/
private def markUnwaited (ptrace : Ptrace) (emu : Emu) (group : Nat) : IO Unit := do
  let some task := (← emu.taskTable.get).find? group | return
  if task.parent != 0 && task.exitSignal.isNone && (← ptrace.signals.reapsChildren task.parent) then
    ptrace.table.modify fun table => { table with reaping := table.reaping ++ [group] }

/-- The exit of a thread that a tracer that isn't its parent was to hear of is no longer for that one, as it waited for it or is over: if
the thread is the leader of its process, its parent hears of it now, as Linux has it, and it may go without a wait. -/
private def toldTracer (ptrace : Ptrace) (emu : Emu) (tid status : Nat) : IO Unit := do
  if ((← emu.taskTable.get).find? tid).any (·.group == tid) then
    ptrace.signals.notifyParent emu tid status
    markUnwaited ptrace emu tid

/-- A thread stops, which its tracer hears of, or its parent of a process that stopped. -/
private def stopThread (ptrace : Ptrace) (emu : Emu) (tid : Nat) (stop : Stop) : IO Unit := do
  ptrace.table.modify fun table => { table with stops := table.stops.insert tid stop }
  block emu tid
  let numbers := ptrace.numbers
  let group ← groupOf emu tid
  let notified ← if stop.traced then pure (((← ptrace.table.get).tracees.get? tid).map (·.tracer))
    else pure (((← emu.taskTable.get).find? group).map (·.parent))
  if let some to := notified then
    if to != 0 then
      ptrace.signals.send emu none to ⟨numbers.chld, if stop.traced then 4 else 5, .child group 0 stop.signal⟩
  wakeWaits ptrace

/-- The process tracing a thread, if it is traced. -/
def tracerOf (ptrace : Ptrace) (tid : Nat) : IO (Option Nat) := do
  pure (((← ptrace.table.get).tracees.get? tid).map (·.tracer))

/-- A signal that is to be delivered to a tracee, or a fault of one, stops it instead, unless its tracer let it have it. -/
def intercept (ptrace : Ptrace) (emu : Emu) (tid : Nat) (info : SignalInfo) : IO Bool := do
  let table ← ptrace.table.get
  if !table.tracees.contains tid || info.signal == ptrace.numbers.kill then return false
  if table.injected.get? tid == some info.signal then
    ptrace.table.modify fun table => { table with injected := table.injected.erase tid }
    return false
  let (detail, fault) := match info.detail with
    | .fault address => (address, true)
    | .sent pid _ _ => (pid, false)
    | .child pid _ _ => (pid, false)
    -- Not a fault, which comes again by itself: what a tracer lets it have is sent again.
    | .seccomp address _ _ _ => (address, false)
    | .timer id _ _ => (id, false)
  stopThread ptrace emu tid { status := stoppedStatus info.signal, traced := true, signal := info.signal, code := info.code, detail, fault }
  pure true

/-- SIGSTOP or the like stops a process, as its threads are, and SIGCONT lets one go on. -/
def jobControl (ptrace : Ptrace) (emu : Emu) (group signal : Nat) : IO Unit := do
  let numbers := ptrace.numbers
  let threads := ((← emu.taskTable.get).tasks.filter fun task => task.group == group && task.status.isNone).map (·.tid)
  if signal == numbers.cont then
    let stopped := (← ptrace.table.get).stops
    let held := threads.filter fun tid => (stopped.get? tid).any (!·.traced)
    if held.isEmpty then return
    for tid in held do release ptrace emu tid
    ptrace.table.modify fun table => { table with continued := group :: table.continued.erase group }
    let parent := (((← emu.taskTable.get).find? group).map (·.parent)).getD 0
    if parent != 0 then ptrace.signals.send emu none parent ⟨numbers.chld, 6, .child group 0 numbers.cont⟩
    wakeWaits ptrace
  else
    let stopped := (← ptrace.table.get).stops
    for tid in threads do
      unless stopped.contains tid do
        ptrace.table.modify fun table =>
          { table with stops := table.stops.insert tid { status := stoppedStatus signal, traced := false, signal, reported := tid != group } }
        block emu tid
    ptrace.table.modify fun table => { table with continued := table.continued.erase group }
    let parent := (((← emu.taskTable.get).find? group).map (·.parent)).getD 0
    if parent != 0 then ptrace.signals.send emu none parent ⟨numbers.chld, 5, .child group 0 signal⟩
    wakeWaits ptrace

/-- A tracee that `execve` went to a new program stops, as `PTRACE_TRACEME` and `PTRACE_O_TRACEEXEC` have it, of which
`PTRACE_GETEVENTMSG` says the id that it had before. -/
def executed (ptrace : Ptrace) (emu : Emu) (former : Nat) : IO Unit := do
  let tid ← thread emu
  let some tracee := (← ptrace.table.get).tracees.get? tid | return
  let numbers := ptrace.numbers
  if tracee.options &&& 0x10 != 0 then
    ptrace.table.modify fun table => { table with messages := table.messages.insert tid former }
    stopThread ptrace emu tid { status := stoppedStatus numbers.trap 4, traced := true, signal := numbers.trap }
  else if !tracee.seized then
    stopThread ptrace emu tid { status := stoppedStatus numbers.trap, traced := true, signal := numbers.trap }

/-- A tracee made `child`, by a call that is `event`, which its tracer asked to hear of: the child is traced as it is, and stops
before it runs, by `SIGSTOP` or, if it was seized, as `PTRACE_INTERRUPT` has it; and the tracee stops, which `PTRACE_GETEVENTMSG` says
the child of. -/
def cloned (ptrace : Ptrace) (emu : Emu) (tid child event : Nat) : IO Unit := do
  let some tracee := (← ptrace.table.get).tracees.get? tid | return
  let numbers := ptrace.numbers
  let eventStop (event : Nat) : Stop := { status := stoppedStatus numbers.trap event, traced := true, signal := numbers.trap }
  ptrace.table.modify fun table =>
    { table with
      messages := table.messages.insert tid child
      tracees := table.tracees.insert child { tracer := tracee.tracer, options := tracee.options, seized := tracee.seized } }
  if tracee.seized then stopThread ptrace emu child (eventStop 128)
  else ptrace.signals.send emu (some child) (← groupOf emu child) ⟨numbers.stop, 0, .sent (← groupOf emu tid) 0 0⟩
  stopThread ptrace emu tid (eventStop event)

/-- A tracee that `vfork` made wait goes on, as its child ran a program or ended: it stops for that if its tracer asked to hear of it,
after the stop that it is in if it is in one, and otherwise for the end of the call if it is traced at those. -/
def vforkReleased (ptrace : Ptrace) (emu : Emu) (tid child : Nat) : IO Unit := do
  let table ← ptrace.table.get
  let some tracee := table.tracees.get? tid | return
  let numbers := ptrace.numbers
  if tracee.options &&& (1 <<< vforkDoneEvent) != 0 then
    let done : Stop := { status := stoppedStatus numbers.trap vforkDoneEvent, traced := true, signal := numbers.trap }
    ptrace.table.modify fun table => { table with messages := table.messages.insert tid child }
    if table.stops.contains tid then
      ptrace.table.modify fun table => { table with pending := table.pending.insert tid (table.pending.getD tid [] ++ [done]) }
    else stopThread ptrace emu tid done
  else if tracee.syscalls && tracee.inSyscall && !table.stops.contains tid then
    ptrace.table.modify fun table => { table with tracees := table.tracees.insert tid { tracee with inSyscall := false } }
    let signal := numbers.trap ||| (if tracee.options &&& 1 != 0 then 0x80 else 0)
    stopThread ptrace emu tid { status := stoppedStatus signal, traced := true, signal := numbers.trap }

/-- A thread that was let step doesn't stop after its next instruction after all: its tracer let it go, or it is gone. -/
private def disarmStep (ptrace : Ptrace) (emu : Emu) (tid : Nat) : IO Unit := do
  ptrace.table.modify fun table => { table with stepping := table.stepping.erase tid }
  if let some hook := (← ptrace.stepHooks.get).get? tid then
    ptrace.stepHooks.modify (·.erase tid)
    removeHook emu hook

/-- A process is over, which ended with `status`: what it traced goes on, or is killed if it asked for that; a tracer of its that isn't
its parent hears of it, by `SIGCHLD` and a wait, before its parent does, or it goes without a wait if it isn't traced and its parent
doesn't wait for it, as Linux has it; the parents of what it was yet to hear of hear of that now; and what waits asks again. -/
def processExited (ptrace : Ptrace) (emu : Emu) (group status : Nat) : IO Unit := do
  let table ← ptrace.table.get
  let tasks ← emu.taskTable.get
  let gone := (tasks.tasks.filter (·.group == group)).map (·.tid)
  -- Its tracers that live on, other than its parent, which hears of it as a parent does.
  let parent := ((tasks.find? group).map (·.parent)).getD 0
  let alive (process : Nat) : Bool := (tasks.find? process).any (·.status.isNone)
  if !table.tracees.contains group then markUnwaited ptrace emu group
  let told := gone.filterMap fun tid => match table.tracees.get? tid with
    | some tracee => if tracee.tracer != group && tracee.tracer != parent && alive tracee.tracer then some (tracee.tracer, tid, status) else none
    | none => none
  unless told.isEmpty do
    ptrace.table.modify fun table => { table with untold := table.untold ++ told }
    let signaled := status % 128 != 0
    for tracer in (told.map (·.1)).eraseDups do
      ptrace.signals.send emu none tracer
        ⟨ptrace.numbers.chld, if signaled then 2 else 1, .child group 0 (if signaled then status % 128 else status / 256 % 256)⟩
  for (tid, tracee) in table.tracees.toList do
    if tracee.tracer == group then
      ptrace.table.modify fun table => { table with tracees := table.tracees.erase tid }
      disarmStep ptrace emu tid
      if tracee.options &&& 0x100000 != 0 then
        match (← emu.taskTable.get).find? tid with
        | some { status := none, .. } => kill emu tid ptrace.numbers.kill
        | _ => pure ()
      else if (table.stops.get? tid).any (·.traced) then
        -- A call that it is stopped at the start of is made as it started, as no tracer says otherwise now.
        ptrace.table.modify fun table => { table with entries := table.entries.erase tid }
        release ptrace emu tid
  for tid in gone do disarmStep ptrace emu tid
  ptrace.table.modify fun table =>
    { table with
      tracees := table.tracees.filter fun tid _ => !gone.contains tid
      stops := table.stops.filter fun tid _ => !gone.contains tid
      injected := table.injected.filter fun tid _ => !gone.contains tid
      pending := table.pending.filter fun tid _ => !gone.contains tid
      exiting := table.exiting.filter (!gone.contains ·)
      calls := table.calls.filter fun tid _ => !gone.contains tid
      entries := table.entries.filter fun tid _ => !gone.contains tid
      skipping := table.skipping.filter fun tid _ => !gone.contains tid
      untold := table.untold.filter (·.1 != group) }
  for (tracer, tid, status) in table.untold do
    if tracer == group then toldTracer ptrace emu tid status
  reapUnwaited ptrace emu
  wakeWaits ptrace

/-! ### Waiting -/

/-- What a wait says: of which, its status as `wait4` has it, and as `waitid` has it, its code and status. -/
private structure Report where
  pid : Nat
  status : Nat
  code : Nat
  value : Nat

/-- Of a wait's target, a process group, which is above the ids of processes. -/
private def groupTarget (pgid : Nat) : Nat := 2 ^ 32 + pgid

/-- What a wait in the process that runs finds, of `target` or of any, with these options of `waitid`: `WEXITED`, `WSTOPPED`,
`WCONTINUED`, `WNOWAIT`, `__WCLONE` and `__WALL`. `none` is that there is nothing that it could ever find. -/
private def find (ptrace : Ptrace) (emu : Emu) (group : Nat) (target : Option Nat) (exited stopped continued keep clones all : Bool) :
    IO (Option (Option Report)) := do
  let tasks ← emu.taskTable.get
  let table ← ptrace.table.get
  -- A target above the ids of processes is a process group: see `groupTarget`.
  let pgidOf ← ptrace.signals.pgidOf.get
  let wanted (tid : Nat) : IO Bool := do
    match target with
    | none => pure true
    | some wantedTarget => if wantedTarget ≥ 2 ^ 32 then pure ((← pgidOf tid) == wantedTarget - 2 ^ 32) else pure (tid == wantedTarget)
  -- Of its children, the clone children or the others, as it asked, and those that it traces.
  let eligible (task : Entry) : Bool := all || task.exitSignal.isSome == clones || (table.tracees.get? task.tid).any (·.tracer == group)
  let children ← (tasks.tasks.filter fun task => task.tid == task.group && task.parent == group && eligible task).filterM fun task =>
    wanted task.tid
  -- What a tracer that isn't its parent is yet to hear the exit of hasn't exited to its parent.
  let untoldExit (task : Entry) : Bool := table.untold.any (·.2.1 == task.tid)
  let tracees ← (table.tracees.toList.filter fun (_, tracee) => tracee.tracer == group).filterM fun (tid, _) => wanted tid
  let untold ← (table.untold.filter (·.1 == group)).filterM fun (_, tid, _) => wanted tid
  if children.isEmpty && tracees.isEmpty && untold.isEmpty then return none
  -- A tracee that stopped, to its tracer.
  for (tid, _) in tracees do
    if let some stop := table.stops.get? tid then
      if stop.traced && !stop.reported then
        unless keep do ptrace.table.modify fun table => { table with stops := table.stops.insert tid { stop with reported := true } }
        return some (some { pid := tid, status := stop.status, code := 4, value := stop.signal })
  -- A child that stopped or went on, to its parent that asked.
  for child in children do
    if stopped then
      if let some stop := table.stops.get? child.tid then
        if !stop.traced && !stop.reported then
          unless keep do ptrace.table.modify fun table => { table with stops := table.stops.insert child.tid { stop with reported := true } }
          return some (some { pid := child.tid, status := stop.status, code := 5, value := stop.signal })
    if continued && table.continued.contains child.tid then
      unless keep do ptrace.table.modify fun table => { table with continued := table.continued.erase child.tid }
      return some (some { pid := child.tid, status := 0xffff, code := 6, value := ptrace.numbers.cont })
  if exited then
    let ofStatus (pid status : Nat) : Report :=
      if status % 128 != 0 then { pid, status, code := 2, value := status % 128 } else { pid, status, code := 1, value := status / 256 % 256 }
    -- Of a process group, the first of its children that ended.
    let target := match target with
      | some wantedTarget => if wantedTarget ≥ 2 ^ 32 then
          (children.find? fun child => child.status.isSome && !table.reaping.contains child.tid && !untoldExit child).map (·.tid)
            |>.orElse fun _ => children.head?.map (·.tid)
        else some wantedTarget
      | none => none
    -- Not of what goes without a wait, nor of what it doesn't ask for.
    let seen := tasks.tasks.filterMap fun task =>
      if table.reaping.contains task.group || (task.parent == group && !eligible task) then none
      else if untoldExit task then some { task with status := none }
      else some task
    match { tasks with tasks := seen }.poll group target with
    | .exited child status =>
      unless keep do
        emu.taskTable.set (tasks.reap child)
        collectGone emu
      return some (some (ofStatus child status))
    | _ => pure ()
    -- A tracee that isn't a child is told of to its tracer once.
    if let some (_, tid, status) := untold.head? then
      unless keep do
        ptrace.table.modify fun table => { table with untold := table.untold.erase (group, tid, status) }
        toldTracer ptrace emu tid status
        reapUnwaited ptrace emu
      return some (some (ofStatus tid status))
  pure (some none)

private def numberBytes (big : Bool) (size value : Nat) : ByteArray :=
  let little := (List.range size).map fun index => (value >>> (8 * index)).toUInt8
  ByteArray.mk (if big then little.reverse else little).toArray

/-- What a wait asks for of its first argument, a `pid_t`, of which the kernel takes the low 32 bits: any, or one. A process group
is any, as there is one. -/
private def targetOf (value own : Nat) : Option Nat :=
  let pid := value % 2 ^ 32
  if pid == 0 then some (groupTarget own)
  else if pid == 2 ^ 32 - 1 then none
  else if pid ≥ 2 ^ 31 then some (groupTarget (2 ^ 32 - pid))
  else some pid

/-! ### Registers -/

/-- What is in the registers of a target as `user_regs_struct` has them, which `PTRACE_GETREGS` and `PTRACE_GETREGSET` give. -/
private inductive Slot where
  | register (name : String)
  | pc
  | flags
  | constant (value : Nat)
  /-- What `orig_rax` and `orig_eax` are: the number of the system call that the thread last started, or -1 if none. -/
  | callNumber
  /-- What `ARM_ORIG_r0` is: the first argument of the system call that the thread last started, or `R0` if none. -/
  | callArgument
  /-- A register that has the number of a system call at its start and its result at its end, as `rax` does. -/
  | result (name : String)

private def slotsOf : Architecture → Option (List Slot)
  | .x86_64 => some ((["R15", "R14", "R13", "R12", "RBP", "RBX", "R11", "R10", "R9", "R8"].map .register) ++ [.result "RAX"] ++
      (["RCX", "RDX", "RSI", "RDI"].map .register) ++
      [.callNumber, .pc, .constant 0x33, .flags, .register "RSP", .constant 0x2b, .register "FS_BASE", .register "GS_BASE",
       .constant 0, .constant 0, .constant 0, .constant 0])
  | .i686 => some ((["EBX", "ECX", "EDX", "ESI", "EDI", "EBP"].map .register) ++ [.result "EAX"] ++
      [.constant 0x2b, .constant 0x2b, .constant 0, .constant 0x63, .callNumber, .pc, .constant 0x23, .flags, .register "ESP", .constant 0x2b])
  | .aarch64 => some (((List.range 31).map fun index => .register s!"X{index}") ++ [.register "SP", .pc, .flags])
  | .riscv64 | .riscv32 => some (.pc :: (List.range 31).map fun index => .register s!"X{index + 1}")
  | .arm => some (((List.range 13).map fun index => .register s!"R{index}") ++ [.register "SP", .register "LR", .pc, .flags, .callArgument])
  | _ => none

/-- How big the kernel's `struct user` of a target is, which `PTRACE_PEEKUSER` and `PTRACE_POKEUSER` go into: none of a target that has
neither, as AArch64 and RISC-V don't. -/
private def userSize : Architecture → Option Nat
  | .x86_64 => some 912
  | .i686 => some 284
  | .arm => some 296
  | _ => none

/-- The flags of a target, as its status word has them, by where each is. -/
private def flagBits : Architecture → List (String × Nat)
  | .x86_64 | .i686 => [("CF", 0), ("PF", 2), ("AF", 4), ("ZF", 6), ("SF", 7), ("DF", 10), ("OF", 11)]
  | .aarch64 | .arm => [("NF", 31), ("ZF", 30), ("CF", 29), ("VF", 28)]
  | _ => []

private def threadValue (emu : Emu) (tid : Nat) (name : String) (width : Nat) : IO Nat := do
  match ← (threadReg emu tid ⟨name, .imm width, 0, false⟩).toBaseIO with
  | .ok value => match Value.asBits value with
    | .ok bits => pure bits.2.toNat
    | .error _ => pure 0
  | .error _ => pure 0

private def pcOf (emu : Emu) (tid : Nat) : IO Nat := do
  if (← thread emu) == tid then emu.pc.get
  else pure (((← threads emu).find? (·.id == tid)).map (·.pc) |>.getD 0)

/-- The registers of a thread, by slot. -/
private def readSlots (ptrace : Ptrace) (emu : Emu) (tid : Nat) (slots : List Slot) : IO (List Nat) := do
  let width ← wordWidth emu
  slots.mapM fun slot => match slot with
    | .register name => threadValue emu tid name width
    | .result name => do
      match ((← ptrace.table.get).entries.get? tid).map (·.2) with
      | some result => pure result
      | none => threadValue emu tid name width
    | .callNumber => do
      match ((← ptrace.table.get).entries.get? tid).map (·.1) with
      | some number => pure number
      | none => pure ((((← ptrace.table.get).calls.get? tid).map (·.1)).getD (2 ^ width - 1))
    | .callArgument => do
      match ((← ptrace.table.get).calls.get? tid).map (·.2) with
      | some argument => pure argument
      | none => threadValue emu tid "R0" width
    | .pc => pcOf emu tid
    | .constant value => pure value
    | .flags => do
      let mut word := if ptrace.architecture matches .x86_64 | .i686 then 0x202 else if ptrace.architecture matches .arm then 0x10 else 0
      for (name, bit) in flagBits ptrace.architecture do
        if (← threadValue emu tid name 1) != 0 then word := word ||| (1 <<< bit)
      if ptrace.architecture matches .arm then
        if (← threadValue emu tid "ISET" 1) != 0 then word := word ||| 0x20
      pure word

/-- Sets the registers of a thread from what its slots have, but those that are what they are. -/
private def writeSlots (ptrace : Ptrace) (emu : Emu) (tid : Nat) (slots : List Slot) (values : List Nat) : IO Unit := do
  let width ← wordWidth emu
  for (slot, value) in slots.zip values do
    match slot with
    | .register name => setThreadReg emu tid ⟨name, .imm width, 0, false⟩ (.bits (BitVec.ofNat width value))
    -- At the start of a call, what it is to be and what it gives if it isn't one, until it goes on: see `leaveEntry`.
    | .result name =>
      match (← ptrace.table.get).entries.get? tid with
      | some (number, _) => ptrace.table.modify fun table => { table with entries := table.entries.insert tid (number, value) }
      | none => setThreadReg emu tid ⟨name, .imm width, 0, false⟩ (.bits (BitVec.ofNat width value))
    | .callNumber =>
      match (← ptrace.table.get).entries.get? tid with
      | some (_, result) => ptrace.table.modify fun table => { table with entries := table.entries.insert tid (value, result) }
      | none => pure ()
    | .pc =>
      if (← thread emu) == tid then setPc emu value
      else emu.threadsRef.modify fun contexts => contexts.map fun context =>
        if context.id == tid then { context with pc := value, pending := none, skip := none } else context
    | .flags =>
      for (name, bit) in flagBits ptrace.architecture do
        setThreadReg emu tid ⟨name, .imm 1, 0, false⟩ (.bits (BitVec.ofNat 1 ((value >>> bit) &&& 1)))
    | _ => pure ()

/-- A thread goes on from the start of a system call, as its tracer left `orig_rax` and `rax`: the call that it says is made, or if it
says none, as -1 and any other below 0 are, none is, and the call gives what `rax` says. -/
private def leaveEntry (ptrace : Ptrace) (emu : Emu) (tid : Nat) : IO Unit := do
  let some (number, result) := (← ptrace.table.get).entries.get? tid | return
  ptrace.table.modify fun table => { table with entries := table.entries.erase tid, calls := table.calls.insert tid (number, ((table.calls.get? tid).map (·.2)).getD 0) }
  let width ← wordWidth emu
  if number ≥ 2 ^ (width - 1) then
    ptrace.table.modify fun table => { table with skipping := table.skipping.insert tid result }
  else
    match slotsOf ptrace.architecture |>.bind (·.findSome? fun slot => match slot with | .result name => some name | _ => none) with
    | some name => setThreadReg emu tid ⟨name, .imm width, 0, false⟩ (.bits (BitVec.ofNat width number))
    | none => pure ()

/-! ### Memory of a tracee -/

/-- The native memory of a thread's address space, if it isn't that of the thread that runs, with what is mapped there. -/
private def spaceMemory (emu : Emu) (tid : Nat) : IO (Option (Option Jit.Memory × List Region)) := do
  let table ← emu.taskTable.get
  let space := table.spaceOf tid
  if space == table.spaceOf (← thread emu) then return none
  let native := (← emu.processMemory.get).get? space
  let native := native.or (← emu.sharedMemory.get)
  pure (some (native, (← emu.parkedRegions.get).getD space []))

/-- The memory of a thread's address space as its threads' states have it, which is what it is while it has no native memory: as a
process has after a checkpoint is restored, until it runs compiled code. -/
private def stateMemory (emu : Emu) (tid : Nat) : IO (Option (Nat → Nat → ByteArray)) := do
  let table ← emu.taskTable.get
  let space := table.spaceOf tid
  pure ((← emu.threadsRef.get).findSome? fun context =>
    if table.spaceOf context.id != space then none
    else match Bil.lookup context.state.env emu.config.memory with
      | .ok (.memory memory) => some (Bap.Memory.readRegion memory)
      | _ => none)

private def readTracee (emu : Emu) (tid address size : Nat) : IO ByteArray := do
  match ← spaceMemory emu tid with
  | none => read emu address size
  | some (native, regions) =>
    if !(regions.any fun region => region.contains address && region.contains (address + size - 1)) then
      throw <| IO.userError s!"unmapped address {address} of thread {tid}"
    match native with
    | some memory => Jit.readMemoryRange memory (UInt64.ofNat address) size
    | none =>
      match ← stateMemory emu tid with
      | some readRegion => pure (readRegion address size)
      | none => throw <| IO.userError s!"no memory of thread {tid}"

/-- Writes to a tracee as a debugger does, whatever it may do with its memory there, as a breakpoint is written to its code. -/
private def writeTracee (emu : Emu) (tid address : Nat) (data : ByteArray) (asProgram : Bool := false) : IO Unit := do
  match ← spaceMemory emu tid with
  | none => if asProgram then write emu address data else poke emu address data
  | some (native, regions) =>
    if !(regions.any fun region => region.contains address && region.contains (address + data.size - 1)) then
      throw <| IO.userError s!"unmapped address {address} of thread {tid}"
    match native with
    | some memory => Jit.writeMemory memory ((Array.range data.size).map fun offset => UInt64.ofNat (address + offset)) data.data
    -- Without native memory, the states have all of it, which is what it is made of when it is next needed.
    | none => if (← stateMemory emu tid).isNone then throw <| IO.userError s!"no memory of thread {tid}"
    invalidateCode emu address (address + data.size - 1)
    -- And the memory of the state of each thread there, which is what it has when it runs in the interpreter.
    let table ← emu.taskTable.get
    let space := table.spaceOf tid
    let memoryVar := emu.config.memory
    emu.threadsRef.modify fun contexts => contexts.map fun context =>
      if table.spaceOf context.id != space then context
      else match Bil.lookup context.state.env memoryVar with
        | .ok (@Value.memory _ memory) =>
          { context with state := { env := Bil.bind context.state.env memoryVar (.memory (Bap.Memory.writeRegion memory address data)) } }
        | _ => context

/-! ### Waits -/

/-- What a wait of a thread finds now, written where it asked: none if there is nothing yet, or what the call gives. -/
private def complete (ptrace : Ptrace) (emu : Emu) (tid : Nat) (request : WaitRequest) : IO (Option (Except Nat Nat)) := do
  let width ← wordWidth emu
  let big := emu.config.endian == .big
  let mips := ptrace.architecture matches .mips ..
  let group ← groupOf emu tid
  let put (address : Nat) (data : ByteArray) : IO Unit := writeTracee emu tid address data (asProgram := true)
  let siginfo (report : Option Report) : ByteArray := Id.run do
    let field (bytes : ByteArray) (offset value : Nat) : ByteArray := (numberBytes big 4 value).copySlice 0 bytes offset 4
    let union := if width == 64 then 16 else 12
    let mut bytes := ByteArray.mk (Array.replicate 128 0)
    if let some report := report then
      bytes := field bytes 0 ptrace.numbers.chld
      bytes := field bytes (if mips then 4 else 8) report.code
      bytes := field bytes union report.pid
      bytes := field bytes (union + 8) report.value
    pure bytes
  match ← find ptrace emu group request.target request.exited request.stopped request.continued request.keep request.clones
      request.all with
  | none => pure (some (.error echild))
  | some none => pure none
  | some (some report) =>
    -- As the guest knows it, whether it is reported at once or to a wait that waited.
    let report := { report with pid := (← ptrace.resultOf.get) report.pid }
    try
      if request.waitid then
        if request.status != 0 then put request.status (siginfo (some report))
        pure (some (.ok 0))
      else
        if request.status != 0 then put request.status (numberBytes big 4 report.status)
        if request.usage != 0 then put request.usage (ByteArray.mk (Array.replicate (if width == 64 then 144 else 72) 0))
        pure (some (.ok report.pid))
    catch _ => pure (some (.error efault))

/-- Gives each wait that waits what it waits for, of those that have it now, and lets it go on. One that a signal took is gone. -/
private def settleWaits (ptrace : Ptrace) (emu : Emu) : IO Unit := do
  -- A process that is over that no one waits for is left, for a thread of its parent if there is one, and goes.
  if let some running := (← emu.taskTable.get).find? (← thread emu) then
    if (← ptrace.table.get).reaping.contains running.group then
      let tasks := (← emu.taskTable.get).tasks.filter (·.status.isNone)
      if let some other := (tasks.find? (·.group == running.parent)).orElse fun _ => tasks.head? then switchThread emu other.tid
  reapUnwaited ptrace emu
  if !(← ptrace.changed.get) then return
  ptrace.changed.set false
  let blocked := ((← emu.taskTable.get).futexes.filter (·.space == waitSpace)).map (·.thread)
  if blocked.isEmpty then return
  -- What runs may be what exited, which leaves what it wrote to shared memory where others see it when it is left, as it is still
  -- in the table: before a wait reaps it.
  if let some first := blocked.head? then
    match (← emu.taskTable.get).find? (← thread emu) with
    | some { status := some _, .. } | none => switchThread emu first
    | _ => pure ()
  let table ← ptrace.table.get
  ptrace.table.modify fun table => { table with waiting := table.waiting.filter fun tid _ => blocked.contains tid }
  for tid in blocked do
    if let some request := table.waiting.get? tid then
      if let some result := ← complete ptrace emu tid request then
        ptrace.table.modify fun table => { table with waiting := table.waiting.erase tid }
        emu.taskTable.modify fun table =>
          { table with futexes := table.futexes.filter fun waiter => !(waiter.thread == tid && waiter.space == waitSpace) }
        setSyscallResult emu tid result
        resumeThread emu tid

/-- A wait of the thread that runs: what it finds now, or, unless it may not wait, it waits, and a signal may interrupt it. -/
private def serveRequest (ptrace : Ptrace) (emu : Emu) (request : WaitRequest) (noHang : Bool) : IO SyscallAction := do
  let tid ← thread emu
  match ← complete ptrace emu tid request with
  | some result => syscallReturn emu result
  | none =>
    if noHang then
      if request.waitid && request.status != 0 then
        match ← (write emu request.status (ByteArray.mk (Array.replicate 128 0))).toBaseIO with
        | .ok () => syscallReturn emu (.ok 0)
        | .error _ => syscallReturn emu (.error efault)
      else syscallReturn emu (.ok 0)
    else
      ptrace.table.modify fun table => { table with waiting := table.waiting.insert tid request }
      emu.taskTable.modify (·.futexWait { thread := tid, space := waitSpace, address := tid, bitset := 2 ^ 32 - 1 })
      emu.stopped.set true
      syscallReturn emu (.ok 0)

/-- `wait4` and `waitpid`, which always say how a process ended, and how it stopped or went on if asked. Like each `serve` here, it is
for what serves a system call of the thread that runs, and what it gives is what that gives back: one that waits stops the thread,
which the call is made again for, or given its result, when it goes on. -/
def serveWait (ptrace : Ptrace) (emu : Emu) (target status options usage : Nat) : IO SyscallAction := do
  let own ← (← ptrace.signals.pgidOf.get) (← groupOf emu (← thread emu))
  serveRequest ptrace emu { target := targetOf target own, exited := true, stopped := options &&& 2 != 0, continued := options &&& 8 != 0
                            keep := false, waitid := false, clones := options &&& 0x80000000 != 0, all := options &&& 0x40000000 != 0
                            status, usage } (options &&& 1 != 0)

/-- `waitid`, of all (0), a process (1) or a group (2), which is all, as there is one. -/
private def serveWaitid (ptrace : Ptrace) (emu : Emu) (kind id info options : Nat) : IO SyscallAction := do
  if kind > 2 || options &&& (4 ||| 2 ||| 8) == 0 then return ← syscallReturn emu (.error einval)
  -- P_PID, P_PGID, of which 0 is its own, and P_ALL.
  let own ← (← ptrace.signals.pgidOf.get) (← groupOf emu (← thread emu))
  let target := match kind with
    | 1 => some id
    | 2 => some (groupTarget (if id == 0 then own else id))
    | _ => none
  serveRequest ptrace emu { target, exited := options &&& 4 != 0, stopped := options &&& 2 != 0
                            continued := options &&& 8 != 0, keep := options &&& 0x1000000 != 0, waitid := true
                            clones := options &&& 0x80000000 != 0, all := options &&& 0x40000000 != 0, status := info, usage := 0 }
    (options &&& 1 != 0)

/-! ### ptrace -/

/-- The hook of a thread that `stepping` says steps, which stops it once it ran one instruction. -/
private def hookStep (ptrace : Ptrace) (emu : Emu) (tid : Nat) : IO Unit := do
  let width ← wordWidth emu
  let hook ← onCode emu (0, 2 ^ width - 1) fun current address => do
    if (← thread current) != tid then return
    let table ← ptrace.table.get
    match table.stepping.get? tid with
    | some start =>
      -- The first is where it goes on from, and the next is after it ran that.
      if address == start then
        ptrace.table.modify fun table => { table with stepping := table.stepping.insert tid (2 ^ width) }
      else
        ptrace.table.modify fun table => { table with stepping := table.stepping.erase tid }
        disarmStep ptrace current tid
        stopThread ptrace current tid { status := stoppedStatus ptrace.numbers.trap, traced := true, signal := ptrace.numbers.trap, code := 2 }
    | none => pure ()
  ptrace.stepHooks.modify (·.insert tid hook)

/-- Stops a thread after it runs one instruction from where it is. -/
private def armStep (ptrace : Ptrace) (emu : Emu) (tid : Nat) : IO Unit := do
  let from_ ← pcOf emu tid
  ptrace.table.modify fun table => { table with stepping := table.stepping.insert tid from_ }
  hookStep ptrace emu tid

/-- `ptrace`, for what serves the system call of the thread that runs, as `serveWait` is. -/
def servePtrace (ptrace : Ptrace) (emu : Emu) (request pid address data : Nat) : IO SyscallAction := do
  let numbers := ptrace.numbers
  let width ← wordWidth emu
  let word := width / 8
  let big := emu.config.endian == .big
  let me ← thread emu
  let group := (← currentTask emu).group
  let table ← ptrace.table.get
  let fail (errno : Nat) : IO SyscallAction := syscallReturn emu (.error errno)
  let ok (value : Nat := 0) : IO SyscallAction := syscallReturn emu (.ok value)
  let tasks ← emu.taskTable.get
  -- A tracee of this process, and whether it is stopped for its tracer.
  let mine : Option Tracee := (table.tracees.get? pid).filter (·.tracer == group)
  let stoppedHere := (table.stops.get? pid).any (·.traced)
  let goOn (syscalls : Bool) (step : Bool) : IO SyscallAction := do
    let some tracee := mine | return ← fail esrch
    if !stoppedHere then return ← fail esrch
    let stop := table.stops.get? pid
    -- A step that a stop of something else came before is over: it steps again only if it is told to now.
    disarmStep ptrace emu pid
    ptrace.table.modify fun table => { table with tracees := table.tracees.insert pid { tracee with syscalls } }
    -- A stop of an event has no signal to go on with, as Linux has it.
    let event := stop.any (·.status >>> 16 % 256 != 0)
    let madeCall := stop.any fun stop => afterCall (stop.status >>> 16 % 256)
    if data != 0 && !event then
      ptrace.table.modify fun table => { table with injected := table.injected.insert pid data }
      -- A fault comes again by itself, with its own signal; anything else, as another signal that a fault goes on with, is sent, to go
      -- through, and the fault comes again after it.
      unless stop.any (fun stop => stop.fault && stop.signal == data) do
        ptrace.signals.send emu (some pid) (← groupOf emu pid) ⟨data, 0, .sent group 0 0⟩
    -- What it has yet to stop for, it stops for now: the next of an event, and then the end of the call that the event was in.
    match table.pending.getD pid [] with
    | next :: rest =>
      ptrace.table.modify fun table => { table with pending := if rest.isEmpty then table.pending.erase pid else table.pending.insert pid rest }
      stopThread ptrace emu pid next
      return ← ok
    | [] => pure ()
    if madeCall && tracee.inSyscall && !vforkWaiting (← emu.taskTable.get) pid then
      ptrace.table.modify fun table => { table with tracees := table.tracees.insert pid { tracee with syscalls, inSyscall := false } }
      if syscalls then
        let signal := numbers.trap ||| (if tracee.options &&& 1 != 0 then 0x80 else 0)
        stopThread ptrace emu pid { status := stoppedStatus signal, traced := true, signal := numbers.trap }
        return ← ok
    leaveEntry ptrace emu pid
    release ptrace emu pid
    if step then armStep ptrace emu pid
    ok
  -- All but these are of a tracee that is stopped for its tracer, as Linux has it: of one that runs, there is none.
  if ![0, 16, 0x4206, 0x4207, 8].contains request && mine.isSome && !stoppedHere then return ← fail esrch
  let withRegisters (action : List Slot → IO SyscallAction) : IO SyscallAction := do
    if mine.isNone then return ← fail esrch
    match slotsOf ptrace.architecture with
    | some slots => action slots
    | none => fail eio
  match request with
  | 0 =>
    -- PTRACE_TRACEME: by the parent.
    if table.tracees.contains me then return ← fail eperm
    let parent := ((tasks.find? group).map (·.parent)).getD 0
    if parent == 0 then return ← fail eperm
    ptrace.table.modify fun table => { table with tracees := table.tracees.insert me { tracer := parent } }
    ok
  | 16 | 0x4206 =>
    -- PTRACE_ATTACH, which stops it, and PTRACE_SEIZE, which doesn't.
    match tasks.find? pid with
    | some { status := none, group := target, .. } =>
      if target == group || table.tracees.contains pid then return ← fail eperm
      ptrace.table.modify fun table =>
        { table with tracees := table.tracees.insert pid { tracer := group, seized := request != 16, options := if request != 16 then data else 0 } }
      if request == 16 then ptrace.signals.send emu (some pid) target ⟨numbers.stop, 0, .sent group 0 0⟩
      ok
    | _ => fail esrch
  | 0x4207 =>
    -- PTRACE_INTERRUPT
    let some tracee := mine | return ← fail esrch
    if !tracee.seized then return ← fail eio
    unless table.stops.contains pid do
      stopThread ptrace emu pid { status := stoppedStatus numbers.trap 128, traced := true, signal := numbers.trap }
    ok
  | 0x4208 => if mine.isSome then ok else fail esrch
  | 17 =>
    -- PTRACE_DETACH, with a signal to go on with.
    if mine.isNone then return ← fail esrch
    ptrace.table.modify fun table =>
      { table with tracees := table.tracees.erase pid, pending := table.pending.erase pid, calls := table.calls.erase pid }
    disarmStep ptrace emu pid
    leaveEntry ptrace emu pid
    if data != 0 then ptrace.signals.send emu (some pid) (← groupOf emu pid) ⟨data, 0, .sent group 0 0⟩
    release ptrace emu pid
    ok
  | 7 => goOn false false
  | 24 => goOn true false
  | 9 => goOn false true
  | 8 =>
    -- PTRACE_KILL
    if mine.isNone then return ← fail esrch
    disarmStep ptrace emu pid
    kill emu pid numbers.kill
    ok
  | 1 | 2 =>
    -- PTRACE_PEEKTEXT and PTRACE_PEEKDATA: the word goes where `data` says.
    if mine.isNone then return ← fail esrch
    match ← (readTracee emu pid address word).toBaseIO with
    | .ok bytes =>
      match ← (write emu data bytes).toBaseIO with
      | .ok () => ok
      | .error _ => fail efault
    | .error _ => fail eio
  | 4 | 5 =>
    -- PTRACE_POKETEXT and PTRACE_POKEDATA
    if mine.isNone then return ← fail esrch
    match ← (writeTracee emu pid address (numberBytes big word data)).toBaseIO with
    | .ok () => ok
    | .error _ => fail eio
  | 3 | 6 =>
    -- PTRACE_PEEKUSER and PTRACE_POKEUSER, of the registers at the start of the user area, and nothing after them, which reads as 0
    -- and takes nothing, up to its end: past it, or not at a word, there is nothing.
    withRegisters fun slots => do
      match userSize ptrace.architecture with
      | some size => if address % word != 0 || address ≥ size then return ← fail eio
      | none => return ← fail eio
      let index := address / word
      let values ← readSlots ptrace emu pid slots
      if request == 3 then
        match ← (write emu data (numberBytes big word (values.getD index 0))).toBaseIO with
        | .ok () => ok
        | .error _ => fail efault
      else
        if index < slots.length then writeSlots ptrace emu pid slots (values.set index data)
        ok
  | 12 | 13 =>
    -- PTRACE_GETREGS and PTRACE_SETREGS, of the targets that have them.
    if ptrace.architecture matches .aarch64 | .riscv64 | .riscv32 then return ← fail eio
    withRegisters fun slots => do
      if request == 12 then
        let values ← readSlots ptrace emu pid slots
        match ← (write emu data (values.foldl (fun out value => out ++ numberBytes big word value) ByteArray.empty)).toBaseIO with
        | .ok () => ok
        | .error _ => fail efault
      else
        match ← (read emu data (slots.length * word)).toBaseIO with
        | .ok bytes =>
          let values := (List.range slots.length).map fun index =>
            let piece := bytes.extract (index * word) (index * word + word)
            (if big then piece.toList else piece.toList.reverse).foldl (fun value byte => value * 256 + byte.toNat) 0
          writeSlots ptrace emu pid slots values
          ok
        | .error _ => fail efault
  | 0x4204 | 0x4205 =>
    -- PTRACE_GETREGSET and PTRACE_SETREGSET of NT_PRSTATUS, by a `struct iovec`.
    if address != 1 then return ← fail einval
    withRegisters fun slots => do
      match ← (read emu data (2 * word)).toBaseIO with
      | .error _ => fail efault
      | .ok vector =>
        let number (bytes : ByteArray) : Nat := (if big then bytes.toList else bytes.toList.reverse).foldl (fun value byte => value * 256 + byte.toNat) 0
        let base := number (vector.extract 0 word)
        let length := number (vector.extract word (2 * word))
        let size := min length (slots.length * word)
        if request == 0x4204 then
          let values ← readSlots ptrace emu pid slots
          let bytes := values.foldl (fun out value => out ++ numberBytes big word value) ByteArray.empty
          match ← (do write emu base (bytes.extract 0 size); write emu (data + word) (numberBytes big word size)).toBaseIO with
          | .ok () => ok
          | .error _ => fail efault
        else
          match ← (read emu base size).toBaseIO with
          | .ok bytes =>
            let current ← readSlots ptrace emu pid slots
            let values := (List.range slots.length).map fun index =>
              if (index + 1) * word ≤ size then
                let piece := bytes.extract (index * word) (index * word + word)
                (if big then piece.toList else piece.toList.reverse).foldl (fun value byte => value * 256 + byte.toNat) 0
              else current.getD index 0
            writeSlots ptrace emu pid slots values
            ok
          | .error _ => fail efault
  | 0x4200 =>
    -- PTRACE_SETOPTIONS
    let some tracee := mine | return ← fail esrch
    ptrace.table.modify fun table => { table with tracees := table.tracees.insert pid { tracee with options := data } }
    ok
  | 0x4201 =>
    -- PTRACE_GETEVENTMSG
    if mine.isNone then return ← fail esrch
    match ← (write emu data (numberBytes big word (table.messages.getD pid 0))).toBaseIO with
    | .ok () => ok
    | .error _ => fail efault
  | 0x4202 =>
    -- PTRACE_GETSIGINFO: of what it stopped for.
    if mine.isNone then return ← fail esrch
    let some stop := table.stops.get? pid | return ← fail einval
    let mips := ptrace.architecture matches .mips ..
    let union := if width == 64 then 16 else 12
    let put (bytes : ByteArray) (offset size value : Nat) : ByteArray := (numberBytes big size value).copySlice 0 bytes offset size
    let bytes := ByteArray.mk (Array.replicate 128 0)
    let bytes := put bytes 0 4 stop.signal
    let bytes := put bytes (if mips then 4 else 8) 4 stop.code
    let bytes := if stop.fault then put bytes union word stop.detail else put bytes union 4 stop.detail
    match ← (write emu data bytes).toBaseIO with
    | .ok () => ok
    | .error _ => fail efault
  | 0x4203 => if mine.isSome then ok else fail esrch
  | _ => fail eio

/-- What a call that isn't made gives, with its registers as they were: the register of the result keeps what it had. -/
def unmade (emu : Emu) : IO SyscallAction := do
  let width ← wordWidth emu
  let (_, _, register) := syscallRegisters emu.config.syscallAbi
  match Value.asBits (← reg emu ⟨register, .imm width, 0, false⟩) with
  | .ok bits => pure (.returnValue bits.2.toNat)
  | .error _ => pure .default

/-- A call that is made again when the thread goes on, with its registers as they were. -/
def again (emu : Emu) : IO SyscallAction := do
  emu.redirect.set (some (← emu.pc.get))
  unmade emu

/-- A filter of seccomp said `SECCOMP_RET_TRACE` of a call of a tracee: it stops for that if its tracer asked to hear of it, as
`PTRACE_O_TRACESECCOMP` has it, which `PTRACE_GETEVENTMSG` says `data` of, and the call is decided again when it goes on. Whether it
stopped. -/
def seccompStop (ptrace : Ptrace) (emu : Emu) (tid data : Nat) : IO Bool := do
  let some tracee := (← ptrace.table.get).tracees.get? tid | return false
  if tracee.options &&& (1 <<< seccompEvent) == 0 then return false
  let numbers := ptrace.numbers
  ptrace.table.modify fun table => { table with messages := table.messages.insert tid data }
  stopThread ptrace emu tid { status := stoppedStatus numbers.trap seccompEvent, traced := true, signal := numbers.trap }
  pure true

/-- Serves `ptrace` and the waits, and has a tracee that traces its system calls stop at their start; `syscallEnds` has it stop at
their end. -/
def serve (ptrace : Ptrace) (emu : Emu) : IO Unit := do
  let numbers := ptrace.numbers
  let _ ← onSyscall emu fun current number args => do
    let arg (index : Nat) : Nat := args.getD index 0
    let tid ← thread current
    -- Where a wait that a signal interrupts starts again from, which the signals would have noted had they served it.
    -- A call that its tracer said not to make, at its start: it gives what the tracer said, and is over.
    if let some result := (← ptrace.table.get).skipping.get? tid then
      ptrace.table.modify fun table => { table with skipping := table.skipping.erase tid }
      return .returnValue result
    ptrace.signals.noteCall current number
    if (← ptrace.table.get).tracees.contains tid then
      ptrace.table.modify fun table => { table with calls := table.calls.insert tid (number, arg 0) }
    -- The start of a system call of a tracee that is traced at them: it stops, and makes the call when it goes on.
    if let some tracee := (← ptrace.table.get).tracees.get? tid then
      if tracee.syscalls && !tracee.inSyscall then
        ptrace.table.modify fun table => { table with tracees := table.tracees.insert tid { tracee with inSyscall := true } }
        let signal := numbers.trap ||| (if tracee.options &&& 1 != 0 then 0x80 else 0)
        stopThread ptrace current tid { status := stoppedStatus signal, traced := true, signal := numbers.trap }
        -- Where the number and the result are one register, it says -ENOSYS until the tracer says otherwise.
        if slotsOf ptrace.architecture |>.any (·.any fun slot => slot matches .result _) then
          let width ← wordWidth current
          ptrace.table.modify fun table => { table with entries := table.entries.insert tid (number, 2 ^ width - 38) }
        return ← again current
    -- What seccomp makes of the call, which it decides once a tracer saw it start, as Linux has it.
    if let some action := ← (← ptrace.screen.get) current tid number args then return action
    if let some tracee := (← ptrace.table.get).tracees.get? tid then
      -- A call that makes a process or a thread, which its tracer hears of once it is made, if it asked to.
      let flags ← if some number == numbers.fork then pure (some numbers.chld)
        else if some number == numbers.vfork then pure (some (0x4000 ||| 0x100 ||| numbers.chld))
        else if number == numbers.clone then pure (some (arg 0))
        -- Of `clone3`, its flags and exit signal, of `struct clone_args`.
        else if number == numbers.clone3 then do
          let big := current.config.endian == .big
          let read64 (address : Nat) : IO Nat := do
            let bytes ← read current address 8
            pure ((if big then bytes.toList else bytes.toList.reverse).foldl (fun value byte => value * 256 + byte.toNat) 0)
          match ← (do pure ((← read64 (arg 0)) ||| (← read64 (arg 0 + 32)) % 256) : IO Nat).toBaseIO with
          | .ok flags => pure (some flags)
          | .error _ => pure none
        else pure none
      if let some flags := flags then
        let event := eventOfClone numbers.chld flags
        if event != 0 && tracee.options &&& (1 <<< event) != 0 then
          ptrace.cloning.modify (·.insert tid (event, ← current.nextThreadRef.get))
      -- A call that ends it stops it first, with the status that it ends with, and goes through when it is made again.
      if (number == numbers.exit || number == numbers.exitGroup) && tracee.options &&& (1 <<< exitEvent) != 0 then
        if (← ptrace.table.get).exiting.contains tid then
          ptrace.table.modify fun table => { table with exiting := table.exiting.erase tid }
        else
          ptrace.table.modify fun table =>
            { table with exiting := tid :: table.exiting, messages := table.messages.insert tid ((arg 0 % 256) <<< 8) }
          stopThread ptrace current tid { status := stoppedStatus numbers.trap exitEvent, traced := true, signal := numbers.trap }
          return ← again current
    if number == numbers.ptrace then servePtrace ptrace current (arg 0) (arg 1) (arg 2) (arg 3)
    else if number == numbers.wait4 then serveWait ptrace current (arg 0) (arg 1) (arg 2) (arg 3)
    else if some number == numbers.waitpid then serveWait ptrace current (arg 0) (arg 1) (arg 2) 0
    else if number == numbers.waitid then serveWaitid ptrace current (arg 0) (arg 1) (arg 2) (arg 3)
    else pure .default
  emu.syscallEnds.modify ((fun result => do
    let tid ← thread emu
    if let some (event, first) := (← ptrace.cloning.get).get? tid then
      ptrace.cloning.modify (·.erase tid)
      -- What the call gave is the child if it made one: on MIPS an error is a small number too, and isn't a new thread.
      if let some child := result then
        if child ≥ first && ((← emu.taskTable.get).find? child).isSome then cloned ptrace emu tid child event
    if let some tracee := (← ptrace.table.get).tracees.get? tid then
      -- An event that it stopped for in the call comes before the end of the call, which it stops for once it goes on from that, and
      -- the parent of `vfork` comes to the end once its child lets it: see `vforkReleased`.
      if tracee.syscalls && tracee.inSyscall && !(← ptrace.table.get).stops.contains tid && !(vforkWaiting (← emu.taskTable.get) tid) then
        ptrace.table.modify fun table => { table with tracees := table.tracees.insert tid { tracee with inSyscall := false } }
        let signal := numbers.trap ||| (if tracee.options &&& 1 != 0 then 0x80 else 0)
        stopThread ptrace emu tid { status := stoppedStatus signal, traced := true, signal := numbers.trap }) :: ·)

/-! ### Checkpoints -/

def modelId : String := "bap.ptrace"

open Wire in
private def putTracee (out : ByteArray) (entry : Nat × Tracee) : ByteArray :=
  let (tid, tracee) := entry
  putFlag (putFlag (putFlag (putNat (putNat (putNat out tid) tracee.tracer) tracee.options) tracee.seized) tracee.syscalls) tracee.inSyscall

open Wire in
private def getTracee : Decoder (Nat × Tracee) := fun data at_ => do
  let (tid, at_) ← getNat data at_
  let (tracer, at_) ← getNat data at_
  let (options, at_) ← getNat data at_
  let (seized, at_) ← getFlag data at_
  let (syscalls, at_) ← getFlag data at_
  let (inSyscall, at_) ← getFlag data at_
  .ok ((tid, { tracer, options, seized, syscalls, inSyscall }), at_)

open Wire in
private def putStop (out : ByteArray) (entry : Nat × Stop) : ByteArray :=
  let (tid, stop) := entry
  let out := putNat (putNat (putNat out tid) stop.status) stop.signal
  putFlag (putNat (putNat (putFlag (putFlag out stop.traced) stop.reported) stop.code) stop.detail) stop.fault

open Wire in
private def getStop : Decoder (Nat × Stop) := fun data at_ => do
  let (tid, at_) ← getNat data at_
  let (status, at_) ← getNat data at_
  let (signal, at_) ← getNat data at_
  let (traced, at_) ← getFlag data at_
  let (reported, at_) ← getFlag data at_
  let (code, at_) ← getNat data at_
  let (detail, at_) ← getNat data at_
  let (fault, at_) ← getFlag data at_
  .ok ((tid, { status, signal, traced, reported, code, detail, fault }), at_)

open Wire in
private def putPair (out : ByteArray) (entry : Nat × Nat) : ByteArray := putNat (putNat out entry.1) entry.2

open Wire in
private def getPair : Decoder (Nat × Nat) := fun data at_ => do
  let (first, at_) ← getNat data at_
  let (second, at_) ← getNat data at_
  .ok ((first, second), at_)

open Wire in
private def putWait (out : ByteArray) (entry : Nat × WaitRequest) : ByteArray :=
  let (tid, request) := entry
  let out := putOption putNat (putNat out tid) request.target
  let out := putFlag (putFlag (putFlag (putFlag (putFlag out request.exited) request.stopped) request.continued) request.keep) request.waitid
  let out := putFlag (putFlag out request.clones) request.all
  putNat (putNat out request.status) request.usage

open Wire in
private def getWait : Decoder (Nat × WaitRequest) := fun data at_ => do
  let (tid, at_) ← getNat data at_
  let (target, at_) ← getOption getNat data at_
  let (exited, at_) ← getFlag data at_
  let (stopped, at_) ← getFlag data at_
  let (continued, at_) ← getFlag data at_
  let (keep, at_) ← getFlag data at_
  let (waitid, at_) ← getFlag data at_
  let (clones, at_) ← getFlag data at_
  let (all, at_) ← getFlag data at_
  let (status, at_) ← getNat data at_
  let (usage, at_) ← getNat data at_
  .ok ((tid, { target, exited, stopped, continued, keep, waitid, clones, all, status, usage }), at_)

open Wire in
def save (ptrace : Ptrace) : IO ByteArray := do
  let table ← ptrace.table.get
  let out := putSorted putWait ByteArray.empty table.waiting.toList
  let out := putSorted putTracee out table.tracees.toList
  let out := putSorted putStop out table.stops.toList
  let out := putList putNat out table.continued
  let out := putSorted putPair out table.injected.toList
  let out := putSorted putPair out table.messages.toList
  let out := putList (fun out (tracer, tid, status) => putNat (putPair out (tracer, tid)) status) out table.untold
  let out := putSorted (fun out (tid, stops) => putList (fun out stop => putStop out (tid, stop)) (putNat out tid) stops) out
    table.pending.toList
  let out := putList putNat out table.exiting
  let out := putSorted putPair out table.stepping.toList
  let out := putSorted (fun out (tid, call) => putPair (putNat out tid) call) out table.calls.toList
  let out := putSorted (fun out (tid, entry) => putPair (putNat out tid) entry) out table.entries.toList
  let out := putSorted putPair out table.skipping.toList
  pure (putList putNat out table.reaping)

open Wire in
def load (ptrace : Ptrace) (emu : Emu) (data : ByteArray) : IO Unit := do
  let decoded : Except String PtraceTable := do
    let (waiting, at_) ← getList getWait data 0
    let (tracees, at_) ← getList getTracee data at_
    let (stops, at_) ← getList getStop data at_
    let (continued, at_) ← getList getNat data at_
    let (injected, at_) ← getList getPair data at_
    let (messages, at_) ← getList getPair data at_
    let (untold, at_) ← getList (fun data at_ => do
      let ((tracer, tid), at_) ← getPair data at_
      let (status, at_) ← getNat data at_
      .ok ((tracer, tid, status), at_)) data at_
    let (pending, at_) ← getList (fun data at_ => do
      let (tid, at_) ← getNat data at_
      let (stops, at_) ← getList getStop data at_
      .ok ((tid, stops.map (·.2)), at_)) data at_
    let (exiting, at_) ← getList getNat data at_
    let (stepping, at_) ← getList getPair data at_
    let (calls, at_) ← getList (fun data at_ => do
      let (tid, at_) ← getNat data at_
      let (call, at_) ← getPair data at_
      .ok ((tid, call), at_)) data at_
    let (entries, at_) ← getList (fun data at_ => do
      let (tid, at_) ← getNat data at_
      let (entry, at_) ← getPair data at_
      .ok ((tid, entry), at_)) data at_
    let (skipping, at_) ← getList getPair data at_
    let (reaping, at_) ← getList getNat data at_
    expectEnd data at_
    .ok { waiting := Std.HashMap.ofList waiting, tracees := Std.HashMap.ofList tracees, stops := Std.HashMap.ofList stops, continued, injected := Std.HashMap.ofList injected
          messages := Std.HashMap.ofList messages, untold, pending := Std.HashMap.ofList pending, exiting
          stepping := Std.HashMap.ofList stepping, calls := Std.HashMap.ofList calls
          entries := Std.HashMap.ofList entries, skipping := Std.HashMap.ofList skipping, reaping }
  let table ← IO.ofExcept decoded
  -- The steps that were armed are those of the table, each with its hook, which isn't in the bytes.
  for (_, hook) in (← ptrace.stepHooks.get).toList do removeHook emu hook
  ptrace.stepHooks.set {}
  ptrace.table.set table
  for (tid, _) in table.stepping.toList do hookStep ptrace emu tid
  -- What waits may have what it waits for already.
  ptrace.changed.set true

/-- A machine's ptrace, put in its signals and its system calls: before the signals, as it serves `waitid`, and what it stops. -/
def make (architecture : Architecture) (signals : Signals) : IO Ptrace := do
  let ptrace : Ptrace := {
    architecture, signals, table := ← IO.mkRef {}, stepHooks := ← IO.mkRef {}, settle := ← IO.mkRef (fun _ => pure ())
    changed := ← IO.mkRef true, resultOf := ← IO.mkRef id, cloning := ← IO.mkRef {}, screen := ← IO.mkRef fun _ _ _ _ => pure none }
  ptrace.settle.set (settleWaits ptrace)
  pure ptrace

/-- A thread that runs a program took the id of `leader`: what was traced and stopped of the leader is gone, and what was of the
thread is of that id, with the step that it was let take. -/
private def leaderTaken (ptrace : Ptrace) (emu : Emu) (former leader : Nat) : IO Unit := do
  let stepping := (← ptrace.table.get).stepping.get? former
  disarmStep ptrace emu leader
  disarmStep ptrace emu former
  ptrace.table.modify fun table =>
    { table with
      waiting := moveThread table.waiting former leader, tracees := moveThread table.tracees former leader
      stops := moveThread table.stops former leader, injected := moveThread table.injected former leader
      messages := moveThread table.messages former leader, pending := moveThread table.pending former leader
      calls := moveThread table.calls former leader, entries := moveThread table.entries former leader
      skipping := moveThread table.skipping former leader
      exiting := (table.exiting.filter (· != leader)).map fun tid => if tid == former then leader else tid }
  ptrace.cloning.modify (moveThread · former leader)
  if let some from_ := stepping then
    ptrace.table.modify fun table => { table with stepping := table.stepping.insert leader from_ }
    hookStep ptrace emu leader

/-- Puts what `make` made on the emulator: the hooks of its system calls, its waits between turns, and what the signals ask of it. -/
def install (ptrace : Ptrace) (emu : Emu) : IO Unit := do
  let signals := ptrace.signals
  emu.betweenTurns.modify (· ++ [settleWaits ptrace emu])
  signals.intercept.set (intercept ptrace)
  signals.tracer.set (tracerOf ptrace)
  signals.jobControl.set (jobControl ptrace)
  emu.vforkReleased.modify (· ++ [vforkReleased ptrace emu])
  emu.leaderTaken.modify (· ++ [leaderTaken ptrace emu])
  ptrace.serve emu

end Ptrace

end Bap.Linux
