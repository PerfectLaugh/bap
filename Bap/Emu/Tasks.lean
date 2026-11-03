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

/-- The bit of the condition register that a system call of PowerPC says that it failed in: SO of CR0, which has a register of its
own, as the other bits do. -/
private def errorBit : Bap.Var := wordVar 1 "CR0UN"

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
  -- On MIPS, a result that isn't an error has the flag in the register after the arguments clear, whatever that held.
  let env := bindIn env "R7" (if emu.config.syscallAbi == .mips then some 0 else none)
  let env := if emu.config.syscallAbi == .powerpc || emu.config.syscallAbi == .powerpc64 then Bil.bind env errorBit (wordOf 1 0) else env
  emu.threadsRef.modify (spawnContext id { env } (wordVar width result) (wordOf width 0) options.start :: ·)
  if !options.shareMemory then cloneProcessMemory emu id
  if !options.sameGroup then
    for hook in ← emu.processHooks.get do hook task.group id
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
  if let some heard := ← emu.processExited.get then heard group status

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
  -- The last of its process ends the process, which what hears of that hears of as of `exit_group`.
  let left ← emu.taskTable.get
  if let some leader := left.find? task.group then
    if let some status := leader.status then
      if left.alone leader then
        if let some heard := ← emu.processExited.get then heard task.group status

/-- A signal ends the process. Nothing else of signals is modelled. -/
def kill (emu : Emu) (target signal : Nat) : IO Unit := do
  match (← emu.taskTable.get).find? target with
  | some { status := none, group, .. } => markExited emu group (signaledStatus signal)
  | _ => throw <| IO.userError s!"no running Emu process {target}"

/-- Forgets the threads and the memory of what is no longer in the table. What runs stays until it switches away, since
switching keeps the memory it leaves. -/
def collectGone (emu : Emu) : IO Unit := do
  let current ← thread emu
  emu.taskTable.modify (·.sweep current)
  let table ← emu.taskTable.get
  emu.threadsRef.modify (·.filter fun context => context.id == current || (table.find? context.id).isSome)
  emu.processMemory.modify (·.filter fun space _ => table.tasks.any (·.space == space))
  emu.parkedRegions.modify (·.filter fun space _ => table.tasks.any (·.space == space))

/-- What `waitpid` reports now, in the process that runs, without blocking. What it reports is gone from the table. -/
def waitpid (emu : Emu) (target : Option Nat := none) : IO WaitResult := do
  let table ← emu.taskTable.get
  let result := table.poll (← currentTask emu).group target
  if let .exited child _ := result then
    emu.taskTable.set (table.reap child)
    collectGone emu
  pure result

private def isMips (emu : Emu) : Bool := emu.config.syscallAbi == .mips

private def isPowerPC (emu : Emu) : Bool := emu.config.syscallAbi == .powerpc || emu.config.syscallAbi == .powerpc64

/-- Whether a target says that a call failed apart from its result: an error is then the number itself. -/
private def flagsErrors (emu : Emu) : Bool := isMips emu || isPowerPC emu

/-- The flag of a result: on MIPS, in the register after the arguments, and on PowerPC, in SO of CR0. -/
private def setErrorFlag (emu : Emu) (id : ThreadId) (width : Nat) : Option Nat → IO Unit
  | some flag =>
    if isPowerPC emu then setThreadReg emu id errorBit (wordOf 1 flag)
    else setThreadReg emu id (wordVar width "R7") (wordOf width flag)
  | none => pure ()

/-- Gives a thread that isn't the one that runs the result of its system call. -/
def setSyscallResult (emu : Emu) (id : ThreadId) (result : Except Nat Nat) : IO Unit := do
  let width ← wordWidth emu
  let (_, _, register) := syscallRegisters emu.config.syscallAbi
  let (word, flag) := syscallWord (flagsErrors emu) width result
  setErrorFlag emu id width flag
  setThreadReg emu id (wordVar width register) (wordOf width word)

/-- The action of a result of the system call of the thread that runs. -/
def syscallReturn (emu : Emu) (result : Except Nat Nat) : IO SyscallAction := do
  let width ← wordWidth emu
  let (word, flag) := syscallWord (flagsErrors emu) width result
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
  -- These switches are to write to their memory, and nothing runs for them: a thread is switched to when it has its result.
  let arrived ← emu.switchedIn.get
  emu.switchedIn.set none
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
  emu.switchedIn.set arrived
  -- What runs from here may be one of those, and wouldn't be switched to.
  if !woken.isEmpty then
    if let some arrived := arrived then arrived

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
  mmap2 : Option Nat := none
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
  | .arm =>
    { fork := some 2, vfork := some 190, clone := 120, clone3 := 435, wait4 := 114, exit := 1, exitGroup := 248, getpid := 20,
      getppid := 64, gettid := 224, schedYield := 158, futex := 240, futexTime64 := some 422, setTidAddress := 256,
      setRobustList := 338, rseq := 398, sigprocmask := 175, sigaction := 174, tgkill := 268, mmap := 192, munmap := 91,
      mprotect := 125, madvise := 220 }
  | .x86_32 =>
    { fork := some 2, vfork := some 190, clone := 120, clone3 := 435, wait4 := 114, waitpid := some 7, exit := 1, exitGroup := 252,
      getpid := 20, getppid := 64, gettid := 224, schedYield := 158, futex := 240, futexTime64 := some 422, setTidAddress := 258,
      setRobustList := 311, rseq := 386, sigprocmask := 175, sigaction := 174, tgkill := 270, mmap := 192, munmap := 91,
      mprotect := 125, madvise := 219 }
  | .powerpc | .powerpc64 =>
    { fork := some 2, vfork := some 189, clone := 120, clone3 := 435, wait4 := 114, waitpid := some 7, exit := 1, exitGroup := 234,
      getpid := 20, getppid := 64, gettid := 207, schedYield := 158, futex := 221, futexTime64 := if width == 32 then some 422 else none,
      setTidAddress := 232, setRobustList := 300, rseq := 387, sigprocmask := 174, sigaction := 173, tgkill := 250, mmap := 90,
      mmap2 := if width == 32 then some 192 else none, munmap := 91, mprotect := 125, madvise := 205 }
  | .mips =>
    if width == 32 then
      { fork := some 4002, clone := 4120, clone3 := 4435, wait4 := 4114, waitpid := some 4007, exit := 4001, exitGroup := 4246,
        getpid := 4020, getppid := 4064, gettid := 4222, schedYield := 4162, futex := 4238, futexTime64 := some 4422,
        setTidAddress := 4252, setRobustList := 4309, rseq := 4367, sigprocmask := 4195, sigaction := 4194, tgkill := 4266,
        mmap := 4090, mmap2 := some 4210, munmap := 4091, mprotect := 4125, madvise := 4218 }
    else
      { fork := some 5056, vfork := some 5057, clone := 5055, clone3 := 5435, wait4 := 5059, exit := 5058, exitGroup := 5205,
        getpid := 5038, getppid := 5108, gettid := 5178, schedYield := 5023, futex := 5194, setTidAddress := 5212,
        setRobustList := 5268, rseq := 5327, sigprocmask := 5014, sigaction := 5013, tgkill := 5225, mmap := 5009,
        munmap := 5011, mprotect := 5010, madvise := 5027 }

/-- Whether a system call is one of those that say nothing about the world a program looks at, such as where memory went and what became of
a lock, as opposed to what could tell it that it is being watched. -/
def bookkeepingCall (emu : Emu) (number : Nat) : IO Bool := do
  let calls := callsOf emu.config.syscallAbi (← wordWidth emu)
  let is (call : Nat) : Bool := number == call
  let isSome (call : Option Nat) : Bool := some number == call
  pure (is calls.clone || is calls.clone3 || isSome calls.fork || isSome calls.vfork || is calls.exit || is calls.exitGroup ||
    is calls.schedYield || is calls.futex || isSome calls.futexTime64 || is calls.setTidAddress || is calls.setRobustList || is calls.rseq ||
    is calls.sigprocmask || is calls.sigaction || is calls.tgkill || is calls.mmap || isSome calls.mmap2 || is calls.munmap ||
    is calls.mprotect || is calls.madvise || isSome calls.archPrctl)

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
  -- `CLONE_DETACHED`, 0x400000, has been ignored since Linux 2.6.2, and musl still passes it.
  let known := 0xff ||| cloneVm ||| 0x200 ||| 0x400 ||| 0x800 ||| cloneThreadFlag ||| 0x40000 ||| setTls ||| setParentTid |||
    clearChildTid ||| 0x400000 ||| setChildTid
  let has (flag : Nat) : Bool := flags &&& flag != 0
  -- On i686 it is a `struct user_desc`, with the base at 4, as for `set_thread_area`.
  let threadBase ← if emu.config.syscallAbi == .x86_32 && has setTls then readWord32 emu (threadPointer + 4) else pure threadPointer
  if flags ||| known != known then
    syscallReturn emu (.error (enosys emu))
  else if has cloneThreadFlag && !has cloneVm then
    syscallReturn emu (.error einval)
  else
    let options : CloneOptions := {
      start := ← emu.nextPc.get
      stack := if stack != 0 then some stack else none
      threadPointer := if has setTls then some threadBase else none
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

/-- `futex`, for the word at `address` of the space of the thread that runs, or, without `FUTEX_PRIVATE_FLAG`, of what `futexKey` says
it is shared as. Waits and wakes, with masks, and requeues, which is what `pthread_join`, mutexes and condition variables use: no
priority inheritance and no `FUTEX_WAKE_OP`. There is no clock, so a thread with a timeout times out when nothing else can run. -/
private def serveFutex (emu : Emu) (address operation value timeout target compare : Nat) : IO SyscallAction := do
  let own := (← currentTask emu).space
  -- Where a word is to whoever else waits on it.
  let keyOf (word : Nat) : IO (Nat × Nat) := do
    if operation &&& 0x80 == 0 then
      if let some key := ← emu.futexKey.get then
        if let some found := ← key word then return found
    pure (own, word)
  -- Without FUTEX_PRIVATE_FLAG and FUTEX_CLOCK_REALTIME.
  let command := operation &&& 0x7f
  let all := 2 ^ 32 - 1
  let wait (bitset : Nat) : IO SyscallAction := do
    if bitset == 0 then return ← syscallReturn emu (.error einval)
    match ← (readWord32 emu address).toBaseIO with
    | .error _ => syscallReturn emu (.error efault)
    | .ok word =>
      if word != value % 2 ^ 32 then syscallReturn emu (.error eagain)
      else
        let (space, word) ← keyOf address
        let waiter : FutexWaiter := { thread := ← thread emu, space, address := word, bitset, timed := timeout != 0 }
        emu.taskTable.modify (·.futexWait waiter)
        emu.stopped.set true
        syscallReturn emu (.ok 0)
  let wake (bitset : Nat) : IO SyscallAction := do
    if bitset == 0 then return ← syscallReturn emu (.error einval)
    let (space, word) ← keyOf address
    let (table, woken) := (← emu.taskTable.get).futexWake space word bitset value
    emu.taskTable.set table
    wakeThreads emu woken
    syscallReturn emu (.ok woken.length)
  let requeue : IO SyscallAction := do
    let (space, word) ← keyOf address
    let (targetSpace, targetWord) ← keyOf target
    let (table, woken, moved) := (← emu.taskTable.get).futexRequeue space word targetWord value timeout targetSpace
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

/-- Where a mapping goes that doesn't say: below the others, from the top down, as in Linux. -/
private def mappingBase (width : Nat) : Nat := if width == 32 then 0x70000000 else 0x7f0000000000

/-- The highest address below where mappings start with `size` free up to it, which is `gapBelow` of the regions from the top down. It goes from what is known to be all mapped, as a program that
maps much has that in one piece, down to where there is room: otherwise each mapping would take longer than the one before. -/
def freeAddress (emu : Emu) (size : Nat) : IO Nat := do
  let tree ← regionTree emu
  let base := mappingBase (← wordWidth emu)
  let rec go : Nat → Nat → Nat → Bool → IO Nat
    | 0, _, top, _ => pure (top - size)
    | fuel + 1, cursor, top, whole => do
      match tree.getEntryLT? cursor with
      | none => pure (top - size)
      | some (start, region) =>
        let stop := start + region.data.size
        let whole := whole && stop ≥ top
        if whole then emu.mappingTop.set (some (min top start))
        if stop + size ≤ top then pure (top - size)
        else go fuel start (min top start) whole
  let top := (← emu.mappingTop.get).getD base
  go (tree.size + 1) top top true

private def protectionOf (bits : Nat) : Primus.Protection := ⟨bits &&& 1 != 0, bits &&& 2 != 0, bits &&& 4 != 0⟩

/-- Places a mapping of `pages` of `data`: at `address` if it is fixed, over what was there, and anywhere else if not. -/
def placeMapping (emu : Emu) (address : Nat) (fixed : Bool) (data : ByteArray) (bits : Nat) : IO Nat := do
  let start ← if fixed then pure address else freeAddress emu data.size
  if fixed then unmap emu start data.size
  map emu ⟨start, data, protectionOf bits⟩
  pure start

/-- `placeMapping` of zeros, which takes nothing of the host until it is written. -/
def placeZeros (emu : Emu) (address : Nat) (fixed : Bool) (size bits : Nat) : IO Nat := do
  let start ← if fixed then pure address else freeAddress emu size
  if fixed then unmap emu start size
  mapZeros emu start size (protectionOf bits)
  pure start

/-- `mmap` of anonymous memory, which is what the stacks of threads are. -/
private def serveMmap (emu : Emu) (address size bits flags : Nat) : IO SyscallAction := do
  let fixed := flags &&& 0x10 != 0
  let anonymous := flags &&& (if isMips emu then 0x800 else 0x20) != 0
  if !anonymous then
    syscallReturn emu (.error (enosys emu))
  else if size == 0 then
    syscallReturn emu (.error einval)
  else
    let pages := (size + 4095) / 4096 * 4096
    try
      syscallReturn emu (.ok (← placeZeros emu address fixed pages bits))
    catch _ => syscallReturn emu (.error enomem)

/-- `mprotect`. -/
private def serveProtect (emu : Emu) (address size bits : Nat) : IO SyscallAction := do
  try
    protect emu address ((size + 4095) / 4096 * 4096) (protectionOf bits)
    syscallReturn emu (.ok 0)
  catch _ => syscallReturn emu (.error enomem)

/-- `madvise`, which is advice, but for what a program can tell, as `MADV_DONTNEED` is: what it had there reads as zeros from then on. -/
private def serveAdvice (emu : Emu) (address size advice : Nat) : IO SyscallAction := do
  let pages := (size + 4095) / 4096 * 4096
  if address % 4096 != 0 then
    syscallReturn emu (.error einval)
  else if advice != 4 then
    syscallReturn emu (.ok 0)
  else if !coversRange (← emu.regions.get) address (address + pages) then
    syscallReturn emu (.error enomem)
  else
    clearMapped emu address pages
    syscallReturn emu (.ok 0)

/-- The system calls of processes and of pthreads, as Linux has them, for programs that `runProcesses` runs: `fork`, `vfork`,
which is `fork` as the standard allows, `clone`, `wait4`, `waitpid`, `exit`, `exit_group`, `getpid`, `getppid`, `gettid`,
`sched_yield`, which goes on until the quantum ends, `futex`, `set_tid_address`, `set_robust_list`, which keeps nothing, so a
mutex isn't released for a thread that dies with it, `rt_sigprocmask` and `rt_sigaction`, which change nothing here, as no signal
is delivered by an emulator alone, `tgkill`, which ends the process, `mmap`, `munmap`, `mprotect`, `madvise` and `arch_prctl`. `clone3` and `rseq` say they aren't there, which libc falls back from.

Parallel rounds can't serve them, since a worker has no table of threads to block in, and a call from one fails.

A Linux machine has `Bap.Linux.Signals` serve the calls of signals before these, as it is attached first, so that there they are delivered,
with handlers, masks and `sigreturn`, and these are only what an emulator without a machine has. -/
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
      is calls.rseq || is calls.sigprocmask || is calls.sigaction || is calls.tgkill || is calls.mmap || isSome calls.mmap2 || is calls.munmap ||
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
        -- The old mask or action, if it asks for one, has nothing in it. Sizes are those of a mask, which it says, or of an action:
        -- a handler, flags and a mask, and a restorer on x86, PowerPC and 32-bit ARM.
        let old := arg 2
        if old != 0 then
          let size := if is calls.sigprocmask then arg 3 else (if x86 || isPowerPC current || current.config.syscallAbi == .x86_32 || current.config.syscallAbi == .arm then 3 else 2) * (width / 8) + arg 3
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
      else if is calls.mmap || isSome calls.mmap2 then
        serveMmap current (arg 0) (arg 1) (arg 2) (arg 3)
      else if is calls.munmap then
        unmap current (current.config.untag (arg 0)) ((arg 1 + 4095) / 4096 * 4096)
        syscallReturn current (.ok 0)
      else if is calls.mprotect then
        serveProtect current (current.config.untag (arg 0)) (arg 1) (arg 2)
      else if is calls.madvise then
        serveAdvice current (current.config.untag (arg 0)) (arg 1) (arg 2)
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
        -- sched_yield and set_robust_list
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
    if let some fault := ← failure emu then
      -- Unless something takes it, which runs a handler there.
      let taken ← match ← emu.faultHandler.get with
        | some handler => handler fault
        | none => pure false
      unless taken do markExited emu (← currentTask emu).group (signaledStatus 11)
      emu.lastFault.set none
      pure 1
    else
      throw error

/-- `runGuest`, which `executed` counts. -/
private def ran (emu : Emu) (quantum fuel : Nat) : IO Nat := do
  let used ← runGuest emu quantum fuel
  emu.executed.modify (· + used)
  pure used

private def scheduleLoop (emu : Emu) (quantum : Nat) : Nat → Nat → IO ScheduleOutcome
  | 0, _ => pure .outOfFuel
  | rounds + 1, fuel => do
    -- In the middle of a turn nothing has happened yet that the scheduler should look at: it looks when the turn ends, as it would
    -- have if the fuel hadn't run out here.
    if (← emu.turnUsed.get) > 0 then
      if fuel = 0 then pure .outOfFuel
      else scheduleLoop emu quantum rounds (fuel - (← ran emu quantum fuel))
    else
    settleWaiters emu
    for hook in ← emu.betweenTurns.get do hook
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
      | .run => scheduleLoop emu quantum rounds (fuel - (← ran emu quantum fuel))

/-- Runs the tasks in turns of `quantum` instructions, until nothing can run, a thread stops for a reason of its own or `fuel`
instructions have run. A blocked thread goes on when what it waits for has happened. A process that faults ends with SIGSEGV.
Each turn runs at least one instruction or moves on from a thread that can't, so that the rounds are enough. -/
def runProcesses (emu : Emu) (quantum : Nat := 100) (fuel : Nat := 100000) : IO ScheduleOutcome := do
  if quantum = 0 then
    throw <| IO.userError "Emu thread quantum must be positive"
  scheduleLoop emu quantum (2 * fuel + 2 * (← emu.threadsRef.get).length + 8) fuel

end Bap.Emu
