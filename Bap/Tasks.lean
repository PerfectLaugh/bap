namespace Bap.Tasks

/-! # Tasks

The model of Linux: what runs is a task, and a thread and a process are tasks that differ only in what they share. Tasks of
a group are the threads of a process, whose id is that of the group's first task, its leader, and tasks of a space share
their memory. `clone` says what a new one shares. In Windows terms a process is a group with its space, and a thread is a
task in it.

This is the table of the tasks, what `waitpid` sees of it and who waits on a futex. It is about ids and nothing else:
registers, memory and the running of tasks are what `Bap.Emu` and `Bap.Primus` do with it. -/

/-- The status that `waitpid` reports for a process that called `exit` with `code`. -/
def exitedStatus (code : Nat) : Nat := (code % 256) * 256

/-- The status that `waitpid` reports for a process that a signal killed. -/
def signaledStatus (signal : Nat) : Nat := signal % 128

structure Entry where
  tid : Nat
  /-- The id of its process: `getpid` says this, and `gettid` says `tid`. -/
  group : Nat
  /-- The group that waits for this one, and 0 for the first, which has none. -/
  parent : Nat
  /-- The address space, which is the `tid` of the task that it was made for. -/
  space : Nat
  /-- Set when it has exited. For a leader, it is what `waitpid` reports: it stays, as a zombie, until its group is over and
  something has waited for it. Another task goes once it isn't the one that runs, as what runs needs its space. -/
  status : Option Nat := none
  /-- Where its exit writes 0 and wakes a futex, as `set_tid_address` and `CLONE_CHILD_CLEARTID` say: this is what
  `pthread_join` waits on. -/
  clearTid : Option Nat := none
  /-- The signal that its parent is sent when its process ends, if `clone` asked for one other than SIGCHLD, which `fork` has: 0 is
  none. Such a process is a clone child, which a wait sees only if it asks for those, as Linux has it. -/
  exitSignal : Option Nat := none
  /-- How many programs it has run, as Linux's `self_exec_id`: a new task has the count of the task that made it. -/
  selfExecId : Nat := 0
  /-- The `selfExecId` that its parent had when it was made, as Linux's `parent_exec_id`, which a thread has of its process. If the parent
  has run a program since, it is sent SIGCHLD for this one and not its `exitSignal`. -/
  parentExecId : Nat := 0
  deriving DecidableEq, Repr

/-- A task blocked on a futex, which is the word at `address` of `space`. -/
structure FutexWaiter where
  thread : Nat
  space : Nat
  address : Nat
  bitset : Nat
  /-- Whether it asked for a timeout. Without a clock, it times out when nothing else can run. -/
  timed : Bool := false
  /-- When it times out, by the clock of the machine, if it has one: see `Emu.now`. -/
  deadline : Option Nat := none
  deriving DecidableEq, Repr

/-- A task blocked in `waitpid`. -/
structure Waiter where
  thread : Nat
  /-- The process it waits for, or any child of its group. -/
  target : Option Nat
  /-- Where the status goes. -/
  statusAddress : Option Nat := none
  deriving DecidableEq, Repr

structure TaskTable where
  tasks : List Entry := []
  waiters : List Waiter := []
  futexes : List FutexWaiter := []
  deriving DecidableEq, Repr

/-- What waiting finds. -/
inductive WaitResult where
  /-- No child is what was asked for, and none ever will be. -/
  | noChild
  /-- The children asked for are all still running. -/
  | running
  | exited (pid status : Nat)
  deriving DecidableEq, Repr

namespace TaskTable

/-- The first task, which is a process with its memory. -/
def initial (tid : Nat) : TaskTable := { tasks := [{ tid, group := tid, parent := 0, space := tid }] }

def find? (table : TaskTable) (tid : Nat) : Option Entry := table.tasks.find? (·.tid == tid)

/-- The address space of a task. One the table doesn't have is on its own. -/
def spaceOf (table : TaskTable) (tid : Nat) : Nat :=
  match table.find? tid with
  | some task => task.space
  | none => tid

def addTask (table : TaskTable) (task : Entry) : TaskTable := { table with tasks := table.tasks ++ [task] }

def setSpace (table : TaskTable) (tid space : Nat) : TaskTable :=
  { table with tasks := table.tasks.map fun task => if task.tid == tid then { task with space } else task }

/-- Whether `leader` is the only one of its group that may still be running. -/
def alone (table : TaskTable) (leader : Entry) : Bool :=
  table.tasks.all fun other => other.group != leader.group || other.tid == leader.tid || other.status.isSome

/-- Whether `task` is the leader of a child of `parent` that `target` asks for. -/
def asked (parent : Nat) (target : Option Nat) (task : Entry) : Bool :=
  task.tid == task.group && task.parent == parent && (match target with | some pid => task.tid == pid | none => true)

/-- What can be reported of a leader: its group is over. -/
def report (table : TaskTable) (leader : Entry) : Option (Nat × Nat) :=
  if table.alone leader then leader.status.map (leader.tid, ·) else none

/-- The result of `waitpid` in the process `parent`, which changes nothing. -/
def poll (table : TaskTable) (parent : Nat) (target : Option Nat) : WaitResult :=
  let children := table.tasks.filter (asked parent target)
  match children.findSome? table.report with
  | some (pid, status) => .exited pid status
  | none => if children.isEmpty then .noChild else .running

/-- The signal that the parent of `task` is sent when its process ends, as Linux's `do_notify_parent` has it: its `exitSignal`, unless its
parent has run a program since it made it, and then SIGCHLD, which is `none`. -/
def exitSignalOf (table : TaskTable) (task : Entry) : Option Nat :=
  if (table.find? task.parent).any (·.selfExecId != task.parentExecId) then none else task.exitSignal

/-- The children of a group that is over go to `init`, as it can't wait for them, and send it SIGCHLD. -/
def reparent (table : TaskTable) (group init : Nat) : TaskTable :=
  { table with tasks := table.tasks.map fun task =>
      if task.parent == group then { task with parent := init, exitSignal := none } else task }

/-- The task has exited, and its group is over if it was the last. -/
def exitTask (table : TaskTable) (tid status init : Nat) : TaskTable :=
  match table.find? tid with
  | none => table
  | some task =>
    let left : TaskTable :=
      { tasks := table.tasks.map fun other => if other.tid == tid then { other with status := some status } else other
        waiters := table.waiters.filter (·.thread != tid)
        futexes := table.futexes.filter (·.thread != tid) }
    match left.find? task.group with
    | some leader => if leader.status.isSome && left.alone leader then left.reparent task.group init else left
    | none => left

/-- What `exitGroup` makes of a task. -/
def exited (group status init : Nat) (task : Entry) : Entry :=
  if task.group == group then { task with status := some status }
  else if task.parent == group then { task with parent := init, exitSignal := none }
  else task

/-- All of a group has exited, its leader is a zombie and its children go to `init`. -/
def exitGroup (table : TaskTable) (group status init : Nat) : TaskTable :=
  { tasks := table.tasks.map (exited group status init)
    waiters := table.waiters.filter fun waiter =>
      match table.find? waiter.thread with
      | some task => task.group != group
      | none => true
    futexes := table.futexes.filter fun waiter =>
      match table.find? waiter.thread with
      | some task => task.group != group
      | none => true }

/-- The child has been reported, and it is gone. -/
def reap (table : TaskTable) (pid : Nat) : TaskTable :=
  { table with tasks := table.tasks.filter (·.group != pid) }

/-- The tasks that a signal can be sent to: those that run, and the leaders that are zombies until they are reaped, which take
nothing that is sent. -/
def present (table : TaskTable) : List Entry :=
  table.tasks.filter fun task => task.tid == task.group || task.status.isNone

/-- Without the tasks that have exited, other than leaders and the one that runs. -/
def sweep (table : TaskTable) (running : Nat) : TaskTable :=
  { table with tasks := table.tasks.filter fun task =>
      task.tid == task.group || task.status.isNone || task.tid == running }

/-- What a waiter waits for has happened, or will never happen. Each exit is for one waiter, the first to ask. -/
def settleOne (current : TaskTable × List (Waiter × WaitResult)) (waiter : Waiter) :
    TaskTable × List (Waiter × WaitResult) :=
  let (table, woken) := current
  let parent := match table.find? waiter.thread with
    | some task => task.group
    | none => 0
  match table.poll parent waiter.target with
  | .running => ({ table with waiters := table.waiters ++ [waiter] }, woken)
  | .noChild => (table, woken ++ [(waiter, .noChild)])
  | .exited pid status => (table.reap pid, woken ++ [(waiter, .exited pid status)])

/-- The waiters that can go on, each with what it found, and the table without them or what they reaped. -/
def settle (table : TaskTable) : TaskTable × List (Waiter × WaitResult) :=
  table.waiters.foldl settleOne ({ table with waiters := [] }, [])

/-- Whether the task is blocked, in `waitpid` or on a futex. -/
def blocked (table : TaskTable) (tid : Nat) : Bool :=
  table.waiters.any (·.thread == tid) || table.futexes.any (·.thread == tid)

/-- The tasks that are blocked. -/
def blockedTasks (table : TaskTable) : List Nat :=
  table.waiters.map (·.thread) ++ table.futexes.map (·.thread)

def setClearTid (table : TaskTable) (tid address : Nat) : TaskTable :=
  { table with tasks := table.tasks.map fun task => if task.tid == tid then { task with clearTid := some address } else task }

/-- `execve` of the task, once the others of its group are over: it has run one more program, it has no `clearTid`, which was of the
program that it ran, and if it isn't the leader, it takes the leader's id, which is the process's, and its place, with SIGCHLD to send,
and the leader is gone. -/
def executed (table : TaskTable) (tid : Nat) : TaskTable :=
  match table.find? tid with
  | none => table
  | some task =>
    let exitSignal := if tid == task.group then task.exitSignal else none
    let selfExecId := task.selfExecId + 1
    { table with tasks := table.tasks.filterMap fun other =>
        if other.tid == task.group then some { task with tid := task.group, parent := other.parent, clearTid := none, exitSignal, selfExecId }
        else if other.tid == tid then none
        else some other }

def futexWait (table : TaskTable) (waiter : FutexWaiter) : TaskTable :=
  { table with futexes := table.futexes ++ [waiter] }

/-- Whether a wake of the word, with this mask, is for `waiter`. -/
def futexAsked (space address bitset : Nat) (waiter : FutexWaiter) : Bool :=
  waiter.space == space && waiter.address == address && waiter.bitset &&& bitset != 0

/-- One waiter on the way through a wake, with who stays and who woke. -/
def wakeStep (space address bitset count : Nat) (current : List FutexWaiter × List Nat) (waiter : FutexWaiter) :
    List FutexWaiter × List Nat :=
  if futexAsked space address bitset waiter && current.2.length < count then (current.1, current.2 ++ [waiter.thread])
  else (current.1 ++ [waiter], current.2)

/-- Wakes up to `count` of those that wait on the word, the first to wait first. -/
def futexWake (table : TaskTable) (space address bitset count : Nat) : TaskTable × List Nat :=
  let (kept, woken) := table.futexes.foldl (wakeStep space address bitset count) ([], [])
  ({ table with futexes := kept }, woken)

/-- Wakes up to `wake` of those that wait on `source`, and moves up to `move` of the others to `target`. -/
def futexRequeue (table : TaskTable) (space source target wake move : Nat) (targetSpace : Nat := space) : TaskTable × List Nat × Nat :=
  let (table, woken) := table.futexWake space source (2 ^ 32 - 1) wake
  let (kept, moved) := table.futexes.foldl (init := (([] : List FutexWaiter), 0)) fun current waiter =>
    if waiter.space == space && waiter.address == source && current.2 < move then
      (current.1 ++ [{ waiter with space := targetSpace, address := target }], current.2 + 1)
    else (current.1 ++ [waiter], current.2)
  ({ table with futexes := kept }, woken, moved)

/-- Those whose timeout is up, since nothing else can run. -/
def timedOut (table : TaskTable) : TaskTable × List Nat :=
  ({ table with futexes := table.futexes.filter (!·.timed) }, (table.futexes.filter (·.timed)).map (·.thread))

end TaskTable

/-- The highest address below `top` with `size` free up to it, of what is taken, as start and size, from the highest down. -/
def gapBelow (size : Nat) : Nat → List (Nat × Nat) → Nat
  | top, [] => top - size
  | top, (start, length) :: rest =>
    if start + length + size ≤ top then top - size
    else gapBelow size (min top start) rest

/-- The convention of a result: the word in the result register, and on MIPS, the register that says whether it is an
error. Elsewhere an error is the negated number. -/
def syscallWord (mips : Bool) (width : Nat) : Except Nat Nat → Nat × Option Nat
  | .ok value => (value, if mips then some 0 else none)
  | .error errno => if mips then (errno, some 1) else (2 ^ width - errno, none)

/-- What `wait4` is asked for by its first argument, a `pid_t`, of which the kernel takes the low 32 bits: a 64-bit register has -1
with all its bits or only the low 32 of them. Any child, one of them, or a process group, which isn't modelled. -/
def waitTarget (target : Nat) : Option (Option Nat) :=
  let pid := target % 2 ^ 32
  if pid == 2 ^ 32 - 1 then some none
  else if 0 < pid && pid < 2 ^ 31 then some (some pid)
  else none

/-- How a run of tasks ended. -/
inductive ScheduleOutcome where
  /-- Nothing can run, and the first process ended with this status. -/
  | finished (status : Nat)
  /-- Nothing can run, and these threads wait for what never happens. -/
  | deadlock (waiting : List Nat)
  /-- The thread stopped for a reason of its own, such as a breakpoint, and it is the current one. -/
  | stopped (id : Nat)
  | outOfFuel
  deriving DecidableEq, Repr

/-- What the scheduler does next. -/
inductive ScheduleStep where
  | run
  | switch (id : Nat)
  | done (outcome : ScheduleOutcome)
  deriving DecidableEq, Repr

/-- The decision of the scheduler: `blocked` says that the thread that runs waits or is over, `next` is the next that can run,
`waiting` are the waiters and `first` is the status of the first process. -/
def scheduleStep (current fuel : Nat) (stopped blocked : Bool) (next : Option Nat) (waiting : List Nat)
    (first : Option Nat) : ScheduleStep :=
  if stopped then
    if !blocked then .done (.stopped current)
    else
      match next with
      | some id => .switch id
      | none =>
        if !waiting.isEmpty then .done (.deadlock waiting)
        else
          match first with
          | some status => .done (.finished status)
          | none => .done (.stopped current)
  else if fuel == 0 then .done .outOfFuel
  else .run

end Bap.Tasks
