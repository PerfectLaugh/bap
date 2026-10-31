import Bap.Emu

/-! Tasks in the emulator, as `Bap.Tasks` has them: `clone`, what a process and a thread are, the system calls of Linux that
processes and pthreads need, and the scheduler that runs them. -/

namespace Bap.Emu

open Bap.Tasks

private def wordVar (width : Nat) (name : String) : Bap.Var := ⟨name, .imm width, 0, false⟩
private def wordOf (width value : Nat) : Bap.Value := .bits (BitVec.ofNat width value)

/-- The process that runs: the id of its group. -/
def pid (emu : Emu) : IO Nat := do pure (← currentTask emu).group

/-- The parent of the process that runs, or 0 for the first. -/
def parentPid (emu : Emu) : IO Nat := do pure (← currentTask emu).parent

def tasks (emu : Emu) : IO (List Entry) := do pure (← emu.taskTable.get).tasks

/-- What a new task shares, as the flags of `clone(2)` say it. -/
structure CloneOptions where
  start : Nat
  /-- The stack it runs on. Without one it keeps the stack pointer of its parent, and tasks with the same memory then
  overwrite each other's frames. -/
  stack : Option Nat := none
  threadPointer : Option Nat := none
  /-- `CLONE_VM`: the same address space, and otherwise a copy of it. -/
  shareMemory : Bool := false
  /-- `CLONE_THREAD`: a thread of the same process, and otherwise a process of its own. -/
  sameGroup : Bool := false

/-- A new task, which runs at once with a copy of the registers and sees 0 in the result register. A thread and a process
are this, with different options. -/
def clone (emu : Emu) (options : CloneOptions) : IO ThreadId := do
  if options.sameGroup && !options.shareMemory then
    throw <| IO.userError "a thread of a process shares its memory"
  let task ← currentTask emu
  saveCurrentThread emu
  let id ← emu.nextThreadRef.get
  emu.nextThreadRef.set (id + 1)
  let group := if options.sameGroup then task.group else id
  let parent := if options.sameGroup then task.parent else task.group
  emu.taskTable.modify (·.addTask { tid := id, group, parent, space := task.space })
  let width ← wordWidth emu
  let (_, _, result) := syscallRegisters emu.config.syscallAbi
  let (stackRegister, threadRegister) := threadRegisters emu.config.syscallAbi
  let current ← emu.state.get
  let bindIn (env : Bil.Env) (name : String) : Option Nat → Bil.Env
    | some value => Bil.bind env (wordVar width name) (wordOf width value)
    | none => env
  let env := bindIn (bindIn current.env stackRegister options.stack) threadRegister options.threadPointer
  emu.threadsRef.modify (spawnContext id { env } (wordVar width result) (wordOf width 0) options.start :: ·)
  if !options.shareMemory then cloneProcessMemory emu id
  pure id

/-- A new process at `childPc`, with a copy of the memory. -/
def fork (emu : Emu) (childPc : Nat) : IO ThreadId := clone emu { start := childPc }

/-- The first task, which takes in the children of a process that is over. -/
private def initTask (table : TaskTable) (fallback : Nat) : Nat :=
  match table.tasks.head? with
  | some first => first.tid
  | none => fallback

/-- All of the process has exited: its threads stop, its children go to the first process and it waits as a zombie. -/
private def markExited (emu : Emu) (group status : Nat) : IO Unit := do
  let table ← emu.taskTable.get
  emu.taskTable.set (table.exitGroup group status (initTask table group))
  let current ← thread emu
  for task in table.tasks do
    if task.group == group then
      if task.tid == current then emu.stopped.set true
      else emu.threadsRef.modify (setThreadStopped · task.tid true)

/-- The process that runs calls `exit_group` with `code`. -/
def exitProcess (emu : Emu) (code : Nat) : IO Unit := do
  markExited emu (← currentTask emu).group (exitedStatus code)

/-- 32 bits, in the order of the target. -/
private def word32 (emu : Emu) (value : Nat) : ByteArray :=
  let bytes := [0, 1, 2, 3].map fun index => (value >>> (8 * index)).toUInt8
  ByteArray.mk (if emu.config.endian == .big then bytes.reverse else bytes).toArray

private def readWord32 (emu : Emu) (address : Nat) : IO Nat := do
  let bytes ← read emu address 4
  let bytes := if emu.config.endian == .big then bytes.toList.reverse else bytes.toList
  pure (bytes.foldr (fun byte value => value * 256 + byte.toNat) 0)

/-- The threads go on, each where it stopped. -/
private def wakeThreads (emu : Emu) (threads : List ThreadId) : IO Unit :=
  threads.forM (resumeThread emu)

/-- The thread that runs is over, and its process if that was the last of it. As the kernel does for `pthread_join`, it
writes 0 where `set_tid_address` says and wakes whoever waits there. -/
def exitThread (emu : Emu) (code : Nat) : IO Unit := do
  let task ← currentTask emu
  if let some address := task.clearTid then
    try
      write emu address (word32 emu 0)
      let (table, woken) := (← emu.taskTable.get).futexWake task.space address (2 ^ 32 - 1) 1
      emu.taskTable.set table
      wakeThreads emu woken
    catch _ => pure ()
  let table ← emu.taskTable.get
  emu.taskTable.set (table.exitTask (← thread emu) (exitedStatus code) (initTask table 0))
  emu.stopped.set true

/-- A signal ends the process. Nothing else of signals is modelled. -/
def kill (emu : Emu) (target signal : Nat) : IO Unit := do
  match (← emu.taskTable.get).find? target with
  | some { status := none, group, .. } => markExited emu group (signaledStatus signal)
  | _ => throw <| IO.userError s!"no running Emu process {target}"

/-- Forgets the threads and the memory of what is no longer in the table. What runs stays until it switches away, since
switching keeps the memory it leaves. -/
private def collectGone (emu : Emu) : IO Unit := do
  let current ← thread emu
  emu.taskTable.modify (·.sweep current)
  let table ← emu.taskTable.get
  emu.threadsRef.modify (·.filter fun context => context.id == current || (table.find? context.id).isSome)
  emu.processMemory.modify (·.filter fun space _ => table.tasks.any (·.space == space))

/-- What `waitpid` reports now, in the process that runs, without blocking. What it reports is gone from the table. -/
def waitpid (emu : Emu) (target : Option Nat := none) : IO WaitResult := do
  let table ← emu.taskTable.get
  let result := table.poll (← currentTask emu).group target
  if let .exited child _ := result then
    emu.taskTable.set (table.reap child)
    collectGone emu
  pure result

private def isMips (emu : Emu) : Bool := emu.config.syscallAbi == .mips

/-- The flag of a result, on MIPS, in the register after the arguments. -/
private def setErrorFlag (emu : Emu) (id : ThreadId) (width : Nat) : Option Nat → IO Unit
  | some flag => setThreadReg emu id (wordVar width "R7") (wordOf width flag)
  | none => pure ()

/-- Gives a thread that isn't the one that runs the result of its system call. -/
private def setSyscallResult (emu : Emu) (id : ThreadId) (result : Except Nat Nat) : IO Unit := do
  let width ← wordWidth emu
  let (_, _, register) := syscallRegisters emu.config.syscallAbi
  let (word, flag) := syscallWord (isMips emu) width result
  setErrorFlag emu id width flag
  setThreadReg emu id (wordVar width register) (wordOf width word)

/-- The action of a result of the system call of the thread that runs. -/
private def syscallReturn (emu : Emu) (result : Except Nat Nat) : IO SyscallAction := do
  let width ← wordWidth emu
  let (word, flag) := syscallWord (isMips emu) width result
  setErrorFlag emu (← thread emu) width flag
  pure (.returnValue word)

private def eagain : Nat := 11
private def echild : Nat := 10
private def enomem : Nat := 12
private def efault : Nat := 14
private def einval : Nat := 22
private def esrch : Nat := 3
/-- The numbers of MIPS differ for these. -/
private def enosys (emu : Emu) : Nat := if isMips emu then 89 else 38
private def etimedout (emu : Emu) : Nat := if isMips emu then 145 else 110

/-- Writes the 32 bits of a status, and says whether that address could take them. -/
private def writeStatus (emu : Emu) (address status : Nat) : IO Bool := do
  try
    write emu address (word32 emu status)
    pure true
  catch _ => pure false

/-- The waiters that can go on, each with its status written in its memory and its result in its registers. Not during a
step: this switches threads. A zombie that runs and that one of them reaps stops being what runs first, as what runs needs
its address space. -/
private def settleWaiters (emu : Emu) : IO Unit := do
  let (table, woken) := (← emu.taskTable.get).settle
  if let some (first, _) := woken.head? then
    if (table.find? (← thread emu)).isNone then switchThread emu first.thread
  emu.taskTable.set table
  for (waiter, found) in woken do
    let result : Except Nat Nat ← match found with
      | .exited child status =>
        match waiter.statusAddress with
        | some address =>
          let home ← thread emu
          switchThread emu waiter.thread
          let written ← writeStatus emu address status
          switchThread emu home
          pure (if written then .ok child else .error efault)
        | none => pure (.ok child)
      | _ => pure (.error echild)
    setSyscallResult emu waiter.thread result
    resumeThread emu waiter.thread
  if !woken.isEmpty then collectGone emu

/-- The numbers of the system calls that this serves, as in Linux. -/
private structure Calls where
  fork : Option Nat := none
  vfork : Option Nat := none
  clone : Nat
  clone3 : Nat
  wait4 : Nat
  waitpid : Option Nat := none
  exit : Nat
  exitGroup : Nat
  getpid : Nat
  getppid : Nat
  gettid : Nat
  schedYield : Nat
  futex : Nat
  futexTime64 : Option Nat := none
  setTidAddress : Nat
  setRobustList : Nat
  rseq : Nat
  sigprocmask : Nat
  sigaction : Nat
  tgkill : Nat
  mmap : Nat
  munmap : Nat
  mprotect : Nat
  madvise : Nat
  archPrctl : Option Nat := none

private def callsOf (abi : SyscallAbi) (width : Nat) : Calls :=
  match abi with
  | .x86_64 =>
    { fork := some 57, vfork := some 58, clone := 56, clone3 := 435, wait4 := 61, exit := 60, exitGroup := 231, getpid := 39,
      getppid := 110, gettid := 186, schedYield := 24, futex := 202, setTidAddress := 218, setRobustList := 273, rseq := 334,
      sigprocmask := 14, sigaction := 13, tgkill := 234, mmap := 9, munmap := 11, mprotect := 10, madvise := 28,
      archPrctl := some 158 }
  | .riscv | .aarch64 =>
    { clone := 220, clone3 := 435, wait4 := 260, exit := 93, exitGroup := 94, getpid := 172, getppid := 173, gettid := 178,
      schedYield := 124, futex := 98, futexTime64 := if width == 32 then some 422 else none, setTidAddress := 96,
      setRobustList := 99, rseq := 293, sigprocmask := 135, sigaction := 134, tgkill := 131, mmap := 222, munmap := 215,
      mprotect := 226, madvise := 233 }
  | .mips =>
    if width == 32 then
      { fork := some 4002, clone := 4120, clone3 := 4435, wait4 := 4114, waitpid := some 4007, exit := 4001, exitGroup := 4246,
        getpid := 4020, getppid := 4064, gettid := 4222, schedYield := 4162, futex := 4238, futexTime64 := some 4422,
        setTidAddress := 4252, setRobustList := 4309, rseq := 4367, sigprocmask := 4195, sigaction := 4194, tgkill := 4266,
        mmap := 4090, munmap := 4091, mprotect := 4125, madvise := 4218 }
    else
      { fork := some 5056, vfork := some 5057, clone := 5055, clone3 := 5435, wait4 := 5059, exit := 5058, exitGroup := 5205,
        getpid := 5038, getppid := 5108, gettid := 5178, schedYield := 5023, futex := 5194, setTidAddress := 5212,
        setRobustList := 5268, rseq := 5327, sigprocmask := 5014, sigaction := 5013, tgkill := 5225, mmap := 5009,
        munmap := 5011, mprotect := 5010, madvise := 5027 }

/-- `wait4` without the usage of what it reports, and process groups, which aren't modelled. A thread that has to wait
stops here, and `runProcesses` gives it its result. -/
private def serveWait (emu : Emu) (target status options usage : Nat) : IO SyscallAction := do
  let width ← wordWidth emu
  match waitTarget width target with
  | none => syscallReturn emu (.error einval)
  | some wanted =>
    if usage != 0 then syscallReturn emu (.error einval) else
    let table ← emu.taskTable.get
    match table.poll (← currentTask emu).group wanted with
    | .noChild => syscallReturn emu (.error echild)
    | .exited child value =>
      if status != 0 then
        if !(← writeStatus emu status value) then
          return ← syscallReturn emu (.error efault)
      emu.taskTable.set (table.reap child)
      collectGone emu
      syscallReturn emu (.ok child)
    | .running =>
      -- WNOHANG
      if options &&& 1 != 0 then syscallReturn emu (.ok 0)
      else
        emu.taskTable.set { table with waiters := table.waiters ++ [{
          thread := ← thread emu, target := wanted, statusAddress := if status != 0 then some status else none }] }
        emu.stopped.set true
        syscallReturn emu (.ok 0)

/-- `clone`. `CLONE_VFORK` isn't taken. -/
private def serveClone (emu : Emu) (flags stack parentTid threadPointer childTid : Nat) : IO SyscallAction := do
  let cloneVm := 0x100
  let cloneThreadFlag := 0x10000
  let setTls := 0x80000
  let setParentTid := 0x100000
  let clearChildTid := 0x200000
  let setChildTid := 0x1000000
  let known := 0xff ||| cloneVm ||| 0x200 ||| 0x400 ||| 0x800 ||| cloneThreadFlag ||| 0x40000 ||| setTls ||| setParentTid |||
    clearChildTid ||| setChildTid
  let has (flag : Nat) : Bool := flags &&& flag != 0
  if flags ||| known != known then
    syscallReturn emu (.error (enosys emu))
  else if has cloneThreadFlag && !has cloneVm then
    syscallReturn emu (.error einval)
  else
    let options : CloneOptions := {
      start := ← emu.nextPc.get
      stack := if stack != 0 then some stack else none
      threadPointer := if has setTls then some threadPointer else none
      shareMemory := has cloneVm
      sameGroup := has cloneThreadFlag }
    let id ← if has cloneVm || !has setChildTid then do
        let id ← clone emu options
        if has setChildTid then write emu childTid (word32 emu id)
        pure id
      else do
        -- The copy holds the id of the child, and the parent keeps what was there.
        let before ← read emu childTid 4
        write emu childTid (word32 emu (← emu.nextThreadRef.get))
        let id ← clone emu options
        write emu childTid before
        pure id
    if has setParentTid then write emu parentTid (word32 emu id)
    if has clearChildTid then emu.taskTable.modify (·.setClearTid id childTid)
    syscallReturn emu (.ok id)

/-- `futex`, for the word at `address` of the space of the thread that runs. Waits and wakes, with masks, and requeues,
which is what `pthread_join`, mutexes and condition variables use: no priority inheritance and no `FUTEX_WAKE_OP`. There is no
clock, so a thread with a timeout times out when nothing else can run. -/
private def serveFutex (emu : Emu) (address operation value timeout target compare : Nat) : IO SyscallAction := do
  let space := (← currentTask emu).space
  -- Without FUTEX_PRIVATE_FLAG and FUTEX_CLOCK_REALTIME. Tasks share a word only through their space.
  let command := operation &&& 0x7f
  let all := 2 ^ 32 - 1
  let wait (bitset : Nat) : IO SyscallAction := do
    if bitset == 0 then return ← syscallReturn emu (.error einval)
    match ← (readWord32 emu address).toBaseIO with
    | .error _ => syscallReturn emu (.error efault)
    | .ok word =>
      if word != value % 2 ^ 32 then syscallReturn emu (.error eagain)
      else
        let waiter : FutexWaiter := { thread := ← thread emu, space, address, bitset, timed := timeout != 0 }
        emu.taskTable.modify (·.futexWait waiter)
        emu.stopped.set true
        syscallReturn emu (.ok 0)
  let wake (bitset : Nat) : IO SyscallAction := do
    if bitset == 0 then return ← syscallReturn emu (.error einval)
    let (table, woken) := (← emu.taskTable.get).futexWake space address bitset value
    emu.taskTable.set table
    wakeThreads emu woken
    syscallReturn emu (.ok woken.length)
  let requeue : IO SyscallAction := do
    let (table, woken, moved) := (← emu.taskTable.get).futexRequeue space address target value timeout
    emu.taskTable.set table
    wakeThreads emu woken
    syscallReturn emu (.ok (woken.length + moved))
  match command with
  | 0 => wait all
  | 1 => wake all
  | 3 => requeue
  | 4 =>
    match ← (readWord32 emu address).toBaseIO with
    | .error _ => syscallReturn emu (.error efault)
    | .ok word => if word != compare % 2 ^ 32 then syscallReturn emu (.error eagain) else requeue
  | 9 => wait (compare % 2 ^ 32)
  | 10 => wake (compare % 2 ^ 32)
  | _ => syscallReturn emu (.error (enosys emu))

/-- Where a mapping goes that doesn't say: above everything, page aligned. -/
private def freeAddress (emu : Emu) : IO Nat := do
  let top := (← emu.regions.get).foldl (fun top region => max top (region.address + region.data.size)) 0x10000
  pure ((top + 4095) / 4096 * 4096)

private def protectionOf (bits : Nat) : Primus.Protection := ⟨bits &&& 1 != 0, bits &&& 2 != 0, bits &&& 4 != 0⟩

/-- `mmap` of anonymous memory, which is what the stacks of threads are. Mappings are for the whole emulator: a space sees
zeros where another mapped and wrote. -/
private def serveMmap (emu : Emu) (address size bits flags : Nat) : IO SyscallAction := do
  let fixed := flags &&& 0x10 != 0
  let anonymous := flags &&& (if isMips emu then 0x800 else 0x20) != 0
  if !anonymous then
    syscallReturn emu (.error (enosys emu))
  else if size == 0 then
    syscallReturn emu (.error einval)
  else
    let start ← if fixed then pure address else freeAddress emu
    let pages := (size + 4095) / 4096 * 4096
    try
      map emu ⟨start, ByteArray.mk (Array.replicate pages 0), protectionOf bits⟩
      syscallReturn emu (.ok start)
    catch _ => syscallReturn emu (.error enomem)

/-- `mprotect`, and `munmap`, which takes away all access and keeps the addresses, since an emulator has few threads to run
out of them. -/
private def serveProtect (emu : Emu) (address size bits : Nat) : IO SyscallAction := do
  try
    protect emu address ((size + 4095) / 4096 * 4096) (protectionOf bits)
    syscallReturn emu (.ok 0)
  catch _ => syscallReturn emu (.error enomem)

/-- The system calls of processes and of pthreads, as Linux has them, for programs that `runProcesses` runs: `fork`, `vfork`,
which is `fork` as the standard allows, `clone`, `wait4`, `waitpid`, `exit`, `exit_group`, `getpid`, `getppid`, `gettid`,
`sched_yield`, which goes on until the quantum ends, `futex`, `set_tid_address`, `set_robust_list`, which keeps nothing, so a
mutex isn't released for a thread that dies with it, `rt_sigprocmask` and `rt_sigaction`, which change nothing, as no signal
is delivered, `tgkill`, which ends the process, `mmap`, `munmap`, `mprotect`, `madvise`, which is advice, so `MADV_DONTNEED`
doesn't zero, and `arch_prctl`. `clone3` and `rseq` say they aren't there, which libc falls back from.

Parallel rounds can't serve them, since a worker has no table of threads to block in, and a call from one fails. -/
def serveTaskCalls (emu : Emu) : IO HookId := do
  let width ← wordWidth emu
  let calls := callsOf emu.config.syscallAbi width
  let x86 := emu.config.syscallAbi == .x86_64
  onSyscall emu fun current number args => do
    let arg (index : Nat) : Nat := args.getD index 0
    let is (call : Nat) : Bool := number == call
    let isSome (call : Option Nat) : Bool := some number == call
    let known := is calls.clone || is calls.clone3 || is calls.wait4 || isSome calls.waitpid || isSome calls.fork ||
      isSome calls.vfork || is calls.exit || is calls.exitGroup || is calls.getpid || is calls.getppid || is calls.gettid ||
      is calls.schedYield || is calls.futex || isSome calls.futexTime64 || is calls.setTidAddress || is calls.setRobustList ||
      is calls.rseq || is calls.sigprocmask || is calls.sigaction || is calls.tgkill || is calls.mmap || is calls.munmap ||
      is calls.mprotect || is calls.madvise || isSome calls.archPrctl
    if !known then
      pure .default
    else
      if current.engine.deferMemorySync then
        throw <| IO.userError "the system calls of tasks need runProcesses, not a parallel round"
      if isSome calls.fork || isSome calls.vfork then
        syscallReturn current (.ok (← fork current (← current.nextPc.get)))
      else if is calls.clone then
        serveClone current (arg 0) (arg 1) (arg 2) (if x86 then arg 4 else arg 3) (if x86 then arg 3 else arg 4)
      else if is calls.clone3 || is calls.rseq then
        syscallReturn current (.error (enosys current))
      else if is calls.wait4 then
        serveWait current (arg 0) (arg 1) (arg 2) (arg 3)
      else if isSome calls.waitpid then
        serveWait current (arg 0) (arg 1) (arg 2) 0
      else if is calls.exit then
        exitThread current (arg 0)
        syscallReturn current (.ok 0)
      else if is calls.exitGroup then
        exitProcess current (arg 0)
        syscallReturn current (.ok 0)
      else if is calls.getpid then
        syscallReturn current (.ok (← pid current))
      else if is calls.getppid then
        syscallReturn current (.ok (← parentPid current))
      else if is calls.gettid then
        syscallReturn current (.ok (← thread current))
      else if is calls.futex || isSome calls.futexTime64 then
        serveFutex current (arg 0) (arg 1) (arg 2) (arg 3) (arg 4) (arg 5)
      else if is calls.setTidAddress then
        current.taskTable.modify (·.setClearTid (← thread current) (arg 0))
        syscallReturn current (.ok (← thread current))
      else if is calls.sigprocmask || is calls.sigaction then
        -- The old mask or action, if it asks for one, has nothing in it. Sizes are 8 bytes of a mask, or an action's.
        let old := arg 2
        if old != 0 then
          let size := if is calls.sigprocmask then arg 3 else 32
          try write current old (ByteArray.mk (Array.replicate size 0))
          catch _ => return ← syscallReturn current (.error efault)
        syscallReturn current (.ok 0)
      else if is calls.tgkill then
        match (← current.taskTable.get).find? (arg 1) with
        | some { status := none, group, .. } =>
          if group != arg 0 then syscallReturn current (.error esrch)
          else
            if arg 2 != 0 then kill current group (arg 2)
            syscallReturn current (.ok 0)
        | _ => syscallReturn current (.error esrch)
      else if is calls.mmap then
        serveMmap current (arg 0) (arg 1) (arg 2) (arg 3)
      else if is calls.munmap then
        serveProtect current (arg 0) (arg 1) 0
      else if is calls.mprotect then
        serveProtect current (arg 0) (arg 1) (arg 2)
      else if isSome calls.archPrctl then
        let fsBase := wordVar width "FS_BASE"
        match arg 0 with
        | 0x1002 =>
          setReg current fsBase (wordOf width (arg 1))
          syscallReturn current (.ok 0)
        | 0x1003 =>
          let value ← reg current fsBase
          match Value.asBits value with
          | .ok bits =>
            try write current (arg 1) (ByteArray.mk ((List.range 8).map fun index => (bits.2.toNat >>> (8 * index)).toUInt8).toArray)
            catch _ => return ← syscallReturn current (.error efault)
            syscallReturn current (.ok 0)
          | .error _ => syscallReturn current (.error einval)
        | _ => syscallReturn current (.error einval)
      else
        -- sched_yield, set_robust_list and madvise
        syscallReturn current (.ok 0)

/-- Whether the thread stopped because it waits or is over, which is for the scheduler to deal with. -/
private def blockedOrOver (emu : Emu) (id : ThreadId) : IO Bool := do
  let table ← emu.taskTable.get
  if table.blocked id then pure true
  else
    match table.find? id with
    | some task => pure task.status.isSome
    | none => pure true

/-- A guest that faults gets SIGSEGV, which ends its process and not the others. Anything else isn't the guest's doing. -/
private def runGuest (emu : Emu) (quantum fuel : Nat) : IO Nat := do
  try
    runPreemptive emu quantum fuel
  catch error =>
    if (← failure emu).isSome then
      markExited emu (← currentTask emu).group (signaledStatus 11)
      emu.lastFault.set none
      pure 1
    else
      throw error

private def scheduleLoop (emu : Emu) (quantum : Nat) : Nat → Nat → IO ScheduleOutcome
  | 0, _ => pure .outOfFuel
  | rounds + 1, fuel => do
    settleWaiters emu
    saveCurrentThread emu
    let current ← thread emu
    let table ← emu.taskTable.get
    let first := match table.tasks.head? with
      | some task => task.status
      | none => none
    let next := pickNext (← emu.threadsRef.get) current
    let halted ← stopped emu
    let blocked ← blockedOrOver emu current
    let (table, timed) := table.timedOut
    if halted && blocked && next.isNone && !timed.isEmpty then
      emu.taskTable.set table
      for id in timed do
        setSyscallResult emu id (.error (etimedout emu))
        resumeThread emu id
      scheduleLoop emu quantum rounds fuel
    else
      match scheduleStep current fuel halted blocked next (← emu.taskTable.get).blockedTasks first with
      | .done outcome => pure outcome
      | .switch id =>
        switchThread emu id
        collectGone emu
        scheduleLoop emu quantum rounds fuel
      | .run => scheduleLoop emu quantum rounds (fuel - (← runGuest emu quantum fuel))

/-- Runs the tasks in turns of `quantum` instructions, until nothing can run, a thread stops for a reason of its own or `fuel`
instructions have run. A blocked thread goes on when what it waits for has happened. A process that faults ends with SIGSEGV.
Each turn runs at least one instruction or moves on from a thread that can't, so that the rounds are enough. -/
def runProcesses (emu : Emu) (quantum : Nat := 100) (fuel : Nat := 100000) : IO ScheduleOutcome := do
  if quantum = 0 then
    throw <| IO.userError "Emu thread quantum must be positive"
  scheduleLoop emu quantum (2 * fuel + 2 * (← emu.threadsRef.get).length + 8) fuel

end Bap.Emu
