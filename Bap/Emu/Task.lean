namespace Bap.Emu

/-! # Tasks

The model of Linux: what runs is a task, and a thread and a process are tasks that differ only in what they share. Tasks of
a group are the threads of a process, whose id is that of the group's first task, its leader, and tasks of a space share
their memory. `clone` says what a new one shares. In Windows terms a process is a group with its space, and a thread is a
task in it.

This is the table of the tasks and what `waitpid` sees of it. It is about ids and nothing else: registers, memory and the
running of tasks are what `Bap.Emu` does with it. -/

/-- The status that `waitpid` reports for a process that called `exit` with `code`. -/
def exitedStatus (code : Nat) : Nat := (code % 256) * 256

/-- The status that `waitpid` reports for a process that a signal killed. -/
def signaledStatus (signal : Nat) : Nat := signal % 128

structure Task where
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
  tasks : List Task := []
  waiters : List Waiter := []
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

def find? (table : TaskTable) (tid : Nat) : Option Task := table.tasks.find? (·.tid == tid)

/-- The address space of a task. One the table doesn't have is on its own. -/
def spaceOf (table : TaskTable) (tid : Nat) : Nat :=
  match table.find? tid with
  | some task => task.space
  | none => tid

def addTask (table : TaskTable) (task : Task) : TaskTable := { table with tasks := table.tasks ++ [task] }

def setSpace (table : TaskTable) (tid space : Nat) : TaskTable :=
  { table with tasks := table.tasks.map fun task => if task.tid == tid then { task with space } else task }

/-- Whether `leader` is the only one of its group that may still be running. -/
def alone (table : TaskTable) (leader : Task) : Bool :=
  table.tasks.all fun other => other.group != leader.group || other.tid == leader.tid || other.status.isSome

/-- Whether `task` is the leader of a child of `parent` that `target` asks for. -/
def asked (parent : Nat) (target : Option Nat) (task : Task) : Bool :=
  task.tid == task.group && task.parent == parent && (match target with | some pid => task.tid == pid | none => true)

/-- What can be reported of a leader: its group is over. -/
def report (table : TaskTable) (leader : Task) : Option (Nat × Nat) :=
  if table.alone leader then leader.status.map (leader.tid, ·) else none

/-- The result of `waitpid` in the process `parent`, which changes nothing. -/
def poll (table : TaskTable) (parent : Nat) (target : Option Nat) : WaitResult :=
  let children := table.tasks.filter (asked parent target)
  match children.findSome? table.report with
  | some (pid, status) => .exited pid status
  | none => if children.isEmpty then .noChild else .running

/-- The children of a group that is over go to `init`, as it can't wait for them. -/
def reparent (table : TaskTable) (group init : Nat) : TaskTable :=
  { table with tasks := table.tasks.map fun task =>
      if task.parent == group then { task with parent := init } else task }

/-- The task has exited, and its group is over if it was the last. -/
def exitTask (table : TaskTable) (tid status init : Nat) : TaskTable :=
  match table.find? tid with
  | none => table
  | some task =>
    let left : TaskTable :=
      { tasks := table.tasks.map fun other => if other.tid == tid then { other with status := some status } else other
        waiters := table.waiters.filter (·.thread != tid) }
    match left.find? task.group with
    | some leader => if leader.status.isSome && left.alone leader then left.reparent task.group init else left
    | none => left

/-- What `exitGroup` makes of a task. -/
def exited (group status init : Nat) (task : Task) : Task :=
  if task.group == group then { task with status := some status }
  else if task.parent == group then { task with parent := init }
  else task

/-- All of a group has exited, its leader is a zombie and its children go to `init`. -/
def exitGroup (table : TaskTable) (group status init : Nat) : TaskTable :=
  { tasks := table.tasks.map (exited group status init)
    waiters := table.waiters.filter fun waiter =>
      match table.find? waiter.thread with
      | some task => task.group != group
      | none => true }

/-- The child has been reported, and it is gone. -/
def reap (table : TaskTable) (pid : Nat) : TaskTable :=
  { table with tasks := table.tasks.filter (·.group != pid) }

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

end TaskTable

/-- What `wait4` is asked for by its first argument, a signed word: any child, one of them, or a process group, which isn't
modelled. -/
def waitTarget (width target : Nat) : Option (Option Nat) :=
  if target == 2 ^ width - 1 then some none
  else if 0 < target && target < 2 ^ (width - 1) then some (some target)
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

end Bap.Emu
