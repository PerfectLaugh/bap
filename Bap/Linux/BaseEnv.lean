import Bap.Linux.Library

/-! # A base environment that libraries link against

What a library needs of a libc, served by the host, for a machine that has none, as one that runs the native code of an Android
application from outside it has: the allocator of the machine (`malloc`, `calloc`, `realloc`, `free`, `posix_memalign` and the like),
pthreads (threads with a stack and thread-local storage of their own, `join`, `detach`, `exit`, mutexes, condition variables, `once`,
keys, `self`, `pthread_sigmask`), the routines of memory and strings, `errno`, what a stack protector and `atexit` need, and `abort` and `exit`.

`Machine.baseEnvironment` makes the stubs, once, and says where each name is. A library is linked against it by `Machine.loadWithBase`,
which has it before anything that is loaded: what it has is had from it even when a libc that is loaded, such as glibc, has the same name,
and the libc's for the rest. `Machine.linkBase` does the same to what is loaded already, by its imports.

What blocks, `pthread_join`, `pthread_mutex_lock` and `pthread_cond_wait`, waits as a futex does, on a word of the guest, so that the
threads of the guest and those that its own libc made wait for each other; a call is asked again when it is woken.

The environment is a `RuntimeModel`: what it keeps of threads, keys, aligned blocks and `errno` is in a checkpoint, and a machine goes on
from one with `baseModel`, which puts its functions at the stubs where they were without writing to the guest. -/

namespace Bap.Linux

open Bap.Emu

/-- What a function of the base environment comes to: what it gives back, to wait on the word at an address until it is woken and is
asked again, or that the thread is over. -/
inductive BaseResult where
  | value (value : Nat)
  | wait (address : Nat)
  | finished

/-- A function of the base environment: of the machine as it is at the call, its arguments, and whether it is asked again after it
waited. -/
abbrev BaseFunction := Machine → List Nat → Bool → IO BaseResult

/-- What the environment keeps of the threads that it made, their keys, the blocks that it aligned and the `errno` of each thread. -/
structure BaseState where
  results : Std.HashMap Nat Nat := {}
  joinWords : Std.HashMap Nat Nat := {}
  nextKey : Nat := 1
  specific : Std.HashMap (Nat × Nat) Nat := {}
  aligned : Std.HashMap Nat Nat := {}
  errno : Std.HashMap Nat Nat := {}
  /-- Of each thread in `pthread_once`, where it returns to after the routine. -/
  onceReturns : Std.HashMap Nat Nat := {}
  /-- The stack of each thread that it made, which goes when the thread is joined. -/
  stacks : Std.HashMap Nat (Nat × Nat) := {}
  /-- What else was allocated for each thread that it made, its thread-local storage, which goes with its stack. -/
  blocks : Std.HashMap Nat Nat := {}
  /-- The threads that it made that nothing joins, which go once they are over. -/
  detached : Std.HashSet Nat := {}

/-- The base environment of a machine: where each of its names is. -/
structure BaseEnvironment where
  symbols : List (String × Nat)
  state : IO.Ref BaseState

/-- What resolves the names of the environment, for `loadLibrary`. -/
def BaseEnvironment.resolve (base : BaseEnvironment) (name : String) : Option Nat := base.symbols.lookup name

private def numberBytes (big : Bool) (size value : Nat) : ByteArray :=
  let little := (List.range size).map fun index => (value >>> (8 * index)).toUInt8
  ByteArray.mk (if big then little.reverse else little).toArray

private def numberOf (big : Bool) (bytes : ByteArray) : Nat :=
  (if big then bytes.toList else bytes.toList.reverse).foldl (fun value byte => value * 256 + byte.toNat) 0

/-- Wakes up to `count` of the threads that wait on the word at an address, in the address space of the thread that runs. -/
private def wake (emu : Emu) (address count : Nat) : IO Unit := do
  let space := (← currentTask emu).space
  let (table, woken) := (← emu.taskTable.get).futexWake space address (2 ^ 32 - 1) count
  emu.taskTable.set table
  for tid in woken do resumeThread emu tid

/-- What runs at an address of a stub: the function, its name and where its stub starts. -/
private abbrev Dispatch := Std.HashMap Nat (BaseFunction × String × Nat)

/-- Puts a function at its stub: the first of the stub is where it is called, and the two after it where a call that waited is asked
again, by turns, so that what serves them comes each time. One hook serves them all, by where it is: see `serveStubs`. -/
private def install (machine : Machine) (table : IO.Ref Dispatch) (name : String) (function : BaseFunction) : IO Nat := do
  let entry ← machine.stubFor name
  table.modify fun table => [entry, entry + 4, entry + 8].foldl (fun table at_ => table.insert at_ (function, name, entry)) table
  pure entry

/-- The one hook of the stubs of the environment, from the first to the last: what is called there is found by where it is, which a
hook of each would have to look through all those of the page for. -/
private def serveStubs (machine : Machine) (table : IO.Ref Dispatch) : IO Unit := do
  let dispatch ← table.get
  let addresses : List Nat := dispatch.toList.map (·.1)
  let some first := addresses.min? | return
  let some last := addresses.max? | return
  let _ ← onCode machine.emu (first, last) fun emu at_ => do
    let some (function, name, entry) := dispatch.get? at_ | return
    if (← emu.pc.get) != at_ then return
    let here := { machine with emu }
    let arguments ← callArguments here emu
    for starts in ← emu.hostStarts.get do starts s!"base {name}"
    match ← function here arguments (at_ != entry) with
    | .value value =>
      returnFromCall here emu value
      for ends in ← emu.hostEnds.get do ends none
    | .wait address =>
      let thread ← Bap.Emu.thread emu
      let space := (← currentTask emu).space
      emu.taskTable.modify (·.futexWait { thread, space, address, bitset := 2 ^ 32 - 1 })
      setPc emu (if at_ == entry + 8 then entry + 4 else entry + 8)
      emu.stopped.set true
    | .finished => pure ()

/-- All that a thread that the environment made had, once it is over and nothing is to join it: its stack, its thread-local storage,
the word that `pthread_join` waits on and its `errno`. -/
private def reapThread (machine : Machine) (state : IO.Ref BaseState) (tid : Nat) : IO Unit := do
  let current ← state.get
  if let some (base, size) := current.stacks.get? tid then unmap machine.emu base size
  for block in [current.blocks.get? tid, current.joinWords.get? tid, current.errno.get? tid] do
    if let some block := block then machine.free block
  state.set { current with
    results := current.results.erase tid, joinWords := current.joinWords.erase tid, stacks := current.stacks.erase tid
    blocks := current.blocks.erase tid, errno := current.errno.erase tid, detached := current.detached.erase tid }

/-- A thread that the environment made is over, with what it gives: one that is detached goes at once. -/
private def finishThread (machine : Machine) (state : IO.Ref BaseState) (tid result : Nat) : IO BaseResult := do
  state.modify fun state => { state with results := state.results.insert tid result }
  exitThread machine.emu 0
  if (← state.get).detached.contains tid then reapThread machine state tid
  pure .finished

/-- The functions of the environment, by name, of a machine and what the environment keeps. -/
private def functions (machine : Machine) (state : IO.Ref BaseState) (exitStub : IO.Ref Nat) (onceStub : IO.Ref Nat) :
    List (String × BaseFunction) :=
  let architecture := machine.architecture
  let width := architecture.bits
  let word := width / 8
  let big := architecture.big
  let wrap (value : Int) : Nat := (value % (2 ^ width : Int)).toNat
  let value (number : Nat) : IO BaseResult := pure (.value number)
  let readBytes (machine : Machine) (address size : Nat) : IO ByteArray := Bap.Emu.read machine.emu address size
  let writeBytes (machine : Machine) (address : Nat) (bytes : ByteArray) : IO Unit := Bap.Emu.write machine.emu address bytes
  let read32 (machine : Machine) (address : Nat) : IO Nat := do pure (numberOf big (← readBytes machine address 4))
  let write32 (machine : Machine) (address value : Nat) : IO Unit := writeBytes machine address (numberBytes big 4 value)
  let writeWord (machine : Machine) (address value : Nat) : IO Unit := writeBytes machine address (numberBytes big word value)
  -- A string of C, read a page at a time.
  let stringAt (machine : Machine) (address : Nat) (limit : Nat := 2 ^ 32) : IO ByteArray := do
    let mut out := ByteArray.empty
    let mut at_ := address
    while out.size < limit do
      let chunk := min (4096 - at_ % 4096) (limit - out.size)
      let bytes ← readBytes machine at_ chunk
      match bytes.toList.findIdx? (· == 0) with
      | some index => return out ++ bytes.extract 0 index
      | none =>
        out := out ++ bytes
        at_ := at_ + chunk
    pure out
  let tidOf (machine : Machine) : IO Nat := Bap.Emu.thread machine.emu
  let mutexLock (machine : Machine) (mutex : Nat) (try_ : Bool) : IO BaseResult := do
    let me ← tidOf machine
    let owner ← read32 machine mutex
    if owner == 0 then
      write32 machine mutex me
      write32 machine (mutex + 4) 1
      value 0
    else if owner == me then
      -- As a recursive mutex has it, of which the others don't come here twice.
      write32 machine (mutex + 4) ((← read32 machine (mutex + 4)) + 1)
      value 0
    else if try_ then value 16
    else pure (.wait mutex)
  let mutexUnlock (machine : Machine) (mutex : Nat) : IO BaseResult := do
    let count ← read32 machine (mutex + 4)
    if count > 1 then
      write32 machine (mutex + 4) (count - 1)
    else
      write32 machine mutex 0
      write32 machine (mutex + 4) 0
      wake machine.emu mutex 1
    value 0
  let allocate (machine : Machine) (alignment size : Nat) : IO Nat := do
    if alignment ≤ 16 then machine.malloc (max size 1)
    else
      let block ← machine.malloc (size + alignment)
      let aligned := (block + alignment - 1) / alignment * alignment
      state.modify fun state => { state with aligned := state.aligned.insert aligned block }
      pure aligned
  let release (machine : Machine) (address : Nat) : IO Unit := do
    if address == 0 then return
    match (← state.get).aligned.get? address with
    | some block =>
      state.modify fun state => { state with aligned := state.aligned.erase address }
      machine.free block
    | none => machine.free address
  let compare (left right : ByteArray) : Nat :=
    match (left.toList.zip right.toList).find? fun (a, b) => a != b with
    | some (a, b) => wrap (Int.ofNat a.toNat - Int.ofNat b.toNat)
    | none => wrap (Int.ofNat left.size - Int.ofNat right.size)
  let find (haystack needle : ByteArray) : Option Nat :=
    (List.range (haystack.size + 1 - min needle.size (haystack.size + 1))).find? fun at_ => haystack.extract at_ (at_ + needle.size) == needle
  let errnoOf (machine : Machine) : IO Nat := do
    let me ← tidOf machine
    match (← state.get).errno.get? me with
    | some address => pure address
    | none =>
      let address ← machine.calloc 1 8
      state.modify fun state => { state with errno := state.errno.insert me address }
      pure address
  let reap (machine : Machine) (tid : Nat) : IO Unit := reapThread machine state tid
  let finish (machine : Machine) (tid result : Nat) : IO BaseResult := finishThread machine state tid result
  -- `pthread_sigmask`, or `sigprocmask` with `failed` for what it gives back of an error. It returns to where it was called from
  -- itself, so that what it unblocks and is pending is delivered there, as Linux does where the system call ends.
  let changeMask (machine : Machine) (arguments : List Nat) (failed : Nat → IO Nat) : IO BaseResult := do
    let emu := machine.emu
    let result ← match ← machine.signals.changeMask emu (← tidOf machine) (arguments.headD 0) (arguments.getD 1 0) (arguments.getD 2 0) with
      | none => pure 0
      | some error => failed error
    returnFromCall machine emu result
    for ends in ← emu.hostEnds.get do ends none
    machine.signals.deliverPending emu
    pure .finished
  let (stack, _) := threadRegisters machine.emu.config.syscallAbi
  let register (name : String) : Bap.Var := ⟨name, .imm width, 0, false⟩
  [ -- The allocator of the machine.
    ("malloc", show BaseFunction from fun machine arguments _ => do value (← allocate machine 16 (arguments.headD 0))),
    ("calloc", show BaseFunction from fun machine arguments _ => do value (← machine.calloc (arguments.headD 0) (arguments.getD 1 0))),
    ("realloc", show BaseFunction from fun machine arguments _ => do value (← machine.realloc (arguments.headD 0) (arguments.getD 1 0))),
    ("free", show BaseFunction from fun machine arguments _ => do release machine (arguments.headD 0); value 0),
    ("memalign", show BaseFunction from fun machine arguments _ => do value (← allocate machine (arguments.headD 0) (arguments.getD 1 0))),
    ("aligned_alloc", show BaseFunction from fun machine arguments _ => do value (← allocate machine (arguments.headD 0) (arguments.getD 1 0))),
    ("posix_memalign", show BaseFunction from fun machine arguments _ => do
      writeWord machine (arguments.headD 0) (← allocate machine (arguments.getD 1 0) (arguments.getD 2 0))
      value 0),
    -- Memory and strings.
    ("memcpy", show BaseFunction from fun machine arguments _ => do
      let size := arguments.getD 2 0
      if size > 0 then writeBytes machine (arguments.headD 0) (← readBytes machine (arguments.getD 1 0) size)
      value (arguments.headD 0)),
    ("memmove", show BaseFunction from fun machine arguments _ => do
      let size := arguments.getD 2 0
      if size > 0 then writeBytes machine (arguments.headD 0) (← readBytes machine (arguments.getD 1 0) size)
      value (arguments.headD 0)),
    ("memset", show BaseFunction from fun machine arguments _ => do
      let size := arguments.getD 2 0
      if size > 0 then writeBytes machine (arguments.headD 0) (ByteArray.mk (Array.replicate size (arguments.getD 1 0).toUInt8))
      value (arguments.headD 0)),
    ("memcmp", show BaseFunction from fun machine arguments _ => do
      let size := arguments.getD 2 0
      value (compare (← readBytes machine (arguments.headD 0) size) (← readBytes machine (arguments.getD 1 0) size))),
    ("memchr", show BaseFunction from fun machine arguments _ => do
      let bytes ← readBytes machine (arguments.headD 0) (arguments.getD 2 0)
      value ((bytes.toList.findIdx? (·.toNat == (arguments.getD 1 0) % 256)).map ((arguments.headD 0) + ·) |>.getD 0)),
    ("strlen", show BaseFunction from fun machine arguments _ => do value (← stringAt machine (arguments.headD 0)).size),
    ("strnlen", show BaseFunction from fun machine arguments _ => do value (← stringAt machine (arguments.headD 0) (arguments.getD 1 0)).size),
    ("strcmp", show BaseFunction from fun machine arguments _ => do
      value (compare (← stringAt machine (arguments.headD 0)) (← stringAt machine (arguments.getD 1 0)))),
    ("strncmp", show BaseFunction from fun machine arguments _ => do
      let limit := arguments.getD 2 0
      value (compare (← stringAt machine (arguments.headD 0) limit) (← stringAt machine (arguments.getD 1 0) limit))),
    ("strcpy", show BaseFunction from fun machine arguments _ => do
      writeBytes machine (arguments.headD 0) ((← stringAt machine (arguments.getD 1 0)).push 0)
      value (arguments.headD 0)),
    ("strncpy", show BaseFunction from fun machine arguments _ => do
      let limit := arguments.getD 2 0
      let text ← stringAt machine (arguments.getD 1 0) limit
      if limit > 0 then writeBytes machine (arguments.headD 0) (text ++ ByteArray.mk (Array.replicate (limit - text.size) 0))
      value (arguments.headD 0)),
    ("strcat", show BaseFunction from fun machine arguments _ => do
      let start := (arguments.headD 0) + (← stringAt machine (arguments.headD 0)).size
      writeBytes machine start ((← stringAt machine (arguments.getD 1 0)).push 0)
      value (arguments.headD 0)),
    ("strchr", show BaseFunction from fun machine arguments _ => do
      let text ← stringAt machine (arguments.headD 0)
      let wanted := (arguments.getD 1 0) % 256
      if wanted == 0 then value ((arguments.headD 0) + text.size)
      else value ((text.toList.findIdx? (·.toNat == wanted)).map ((arguments.headD 0) + ·) |>.getD 0)),
    ("strrchr", show BaseFunction from fun machine arguments _ => do
      let text ← stringAt machine (arguments.headD 0)
      let wanted := (arguments.getD 1 0) % 256
      if wanted == 0 then value ((arguments.headD 0) + text.size)
      else
        let last := (List.range text.size).reverse.find? fun index => text[index]!.toNat == wanted
        value ((last.map ((arguments.headD 0) + ·)).getD 0)),
    ("strstr", show BaseFunction from fun machine arguments _ => do
      let haystack ← stringAt machine (arguments.headD 0)
      value (((find haystack (← stringAt machine (arguments.getD 1 0))).map ((arguments.headD 0) + ·)).getD 0)),
    ("strdup", show BaseFunction from fun machine arguments _ => do
      let text ← stringAt machine (arguments.headD 0)
      let copy ← machine.malloc (text.size + 1)
      writeBytes machine copy (text.push 0)
      value copy),
    ("strndup", show BaseFunction from fun machine arguments _ => do
      let text ← stringAt machine (arguments.headD 0) (arguments.getD 1 0)
      let copy ← machine.malloc (text.size + 1)
      writeBytes machine copy (text.push 0)
      value copy),
    -- What is of the process.
    ("__errno_location", show BaseFunction from fun machine _ _ => do value (← errnoOf machine)),
    ("__errno", show BaseFunction from fun machine _ _ => do value (← errnoOf machine)),
    ("__cxa_atexit", show BaseFunction from fun _ _ _ => value 0),
    ("__cxa_finalize", show BaseFunction from fun _ _ _ => value 0),
    ("atexit", show BaseFunction from fun _ _ _ => value 0),
    ("abort", show BaseFunction from fun machine _ _ => do kill machine.emu (← tidOf machine) 6; pure .finished),
    ("__stack_chk_fail", show BaseFunction from fun machine _ _ => do kill machine.emu (← tidOf machine) 6; pure .finished),
    ("exit", show BaseFunction from fun machine arguments _ => do exitProcess machine.emu (arguments.headD 0); pure .finished),
    ("_exit", show BaseFunction from fun machine arguments _ => do exitProcess machine.emu (arguments.headD 0); pure .finished),
    -- The mask of signals of the thread, as the kernel has it.
    ("pthread_sigmask", show BaseFunction from fun machine arguments _ => changeMask machine arguments pure),
    ("sigprocmask", show BaseFunction from fun machine arguments _ =>
      changeMask machine arguments fun error => do
        write32 machine (← errnoOf machine) error
        pure (2 ^ width - 1)),
    ("getpid", show BaseFunction from fun machine _ _ => do value (← currentTask machine.emu).group),
    ("gettid", show BaseFunction from fun machine _ _ => do value (← tidOf machine)),
    ("sched_yield", show BaseFunction from fun _ _ _ => value 0),
    ("usleep", show BaseFunction from fun _ _ _ => value 0),
    ("sleep", show BaseFunction from fun _ _ _ => value 0),
    -- Threads.
    ("pthread_create", show BaseFunction from fun machine arguments _ => do
      let emu := machine.emu
      let (out, start, argument) := (arguments.headD 0, arguments.getD 2 0, arguments.getD 3 0)
      let tid ← spawnThread emu start argument
      -- A stack of its own, and where it goes when its routine returns.
      let stackSize := 1024 * 1024
      let base ← placeZeros emu 0 false stackSize 3
      state.modify fun state => { state with stacks := state.stacks.insert tid (base, stackSize) }
      let top := (base + stackSize - 64) / 16 * 16
      let exitAt ← exitStub.get
      let setRegister (name : String) (value : Nat) : IO Unit :=
        setThreadReg emu tid (register name) (.bits (BitVec.ofNat width value))
      match architecture with
      | .x86_64 =>
        writeWord machine (top - 8) exitAt
        setRegister stack (top - 8)
      | .i686 =>
        writeWord machine (top - 16) exitAt
        writeWord machine (top - 12) argument
        setRegister stack (top - 16)
      | _ =>
        setRegister stack top
        let link := match architecture with
          | .aarch64 => "X30"
          | .arm => "LR"
          | .riscv64 | .riscv32 => "X1"
          | .mips .. => "R31"
          | _ => "LR"
        setRegister link exitAt
        if architecture matches .mips .. then setRegister "R25" start
        if architecture matches .powerpc 64 _ then setRegister "R12" start
      if architecture matches .arm then
        setThreadReg emu tid ⟨"ISET", .imm 1, 0, false⟩ (.bits (BitVec.ofNat 1 (start % 2)))
        emu.threadsRef.modify fun contexts => contexts.map fun context =>
          if context.id == tid then { context with pc := start - start % 2 } else context
      let (block, _) ← machine.threadTlsBlock (thread := some tid)
      state.modify fun state => { state with blocks := state.blocks.insert tid block }
      -- What is cleared and woken when it is over, which `pthread_join` waits on.
      let joinWord ← machine.calloc 1 8
      write32 machine joinWord tid
      emu.taskTable.modify (·.setClearTid tid joinWord)
      state.modify fun state => { state with joinWords := state.joinWords.insert tid joinWord }
      writeWord machine out tid
      value 0),
    ("pthread_join", show BaseFunction from fun machine arguments _ => do
      let (tid, out) := (arguments.headD 0, arguments.getD 1 0)
      let table ← machine.emu.taskTable.get
      let over := match table.find? tid with
        | some task => task.status.isSome
        | none => true
      if !over then
        match (← state.get).joinWords.get? tid with
        | some joinWord => return .wait joinWord
        | none => return .value 3
      if out != 0 then writeWord machine out ((← state.get).results.getD tid 0)
      -- What it had goes with it, as nothing of it runs any more.
      reap machine tid
      value 0),
    ("pthread_detach", show BaseFunction from fun machine arguments _ => do
      let tid := arguments.headD 0
      if !(← state.get).joinWords.contains tid then return ← value 3
      let over := match (← machine.emu.taskTable.get).find? tid with
        | some task => task.status.isSome
        | none => true
      if over then reap machine tid
      else state.modify fun state => { state with detached := state.detached.insert tid }
      value 0),
    ("pthread_exit", show BaseFunction from fun machine arguments _ => do finish machine (← tidOf machine) (arguments.headD 0)),
    ("pthread_self", show BaseFunction from fun machine _ _ => do value (← tidOf machine)),
    ("pthread_equal", show BaseFunction from fun _ arguments _ => value (if arguments.headD 0 == arguments.getD 1 0 then 1 else 0)),
    ("pthread_attr_init", show BaseFunction from fun _ _ _ => value 0),
    ("pthread_attr_destroy", show BaseFunction from fun _ _ _ => value 0),
    ("pthread_attr_setdetachstate", show BaseFunction from fun _ _ _ => value 0),
    ("pthread_attr_setstacksize", show BaseFunction from fun _ _ _ => value 0),
    ("pthread_mutexattr_init", show BaseFunction from fun _ _ _ => value 0),
    ("pthread_mutexattr_settype", show BaseFunction from fun _ _ _ => value 0),
    ("pthread_mutexattr_destroy", show BaseFunction from fun _ _ _ => value 0),
    ("pthread_condattr_init", show BaseFunction from fun _ _ _ => value 0),
    ("pthread_condattr_destroy", show BaseFunction from fun _ _ _ => value 0),
    ("pthread_mutex_init", show BaseFunction from fun machine arguments _ => do writeBytes machine (arguments.headD 0) (ByteArray.mk (Array.replicate 8 0)); value 0),
    ("pthread_mutex_destroy", show BaseFunction from fun _ _ _ => value 0),
    ("pthread_mutex_lock", show BaseFunction from fun machine arguments _ => mutexLock machine (arguments.headD 0) false),
    ("pthread_mutex_trylock", show BaseFunction from fun machine arguments _ => mutexLock machine (arguments.headD 0) true),
    ("pthread_mutex_unlock", show BaseFunction from fun machine arguments _ => mutexUnlock machine (arguments.headD 0)),
    ("pthread_cond_init", show BaseFunction from fun machine arguments _ => do writeBytes machine (arguments.headD 0) (ByteArray.mk (Array.replicate 4 0)); value 0),
    ("pthread_cond_destroy", show BaseFunction from fun _ _ _ => value 0),
    ("pthread_cond_wait", show BaseFunction from fun machine arguments again => do
      let (cond, mutex) := (arguments.headD 0, arguments.getD 1 0)
      -- It lets the mutex go and waits, and when it is woken it has the mutex again, waiting for that if it has to.
      if again then mutexLock machine mutex false
      else
        let _ ← mutexUnlock machine mutex
        pure (.wait cond)),
    ("pthread_cond_timedwait", show BaseFunction from fun machine arguments again => do
      let (cond, mutex) := (arguments.headD 0, arguments.getD 1 0)
      if again then mutexLock machine mutex false
      else
        let _ ← mutexUnlock machine mutex
        pure (.wait cond)),
    ("pthread_cond_signal", show BaseFunction from fun machine arguments _ => do
      let cond := arguments.headD 0
      write32 machine cond ((← read32 machine cond) + 1)
      wake machine.emu cond 1
      value 0),
    ("pthread_cond_broadcast", show BaseFunction from fun machine arguments _ => do
      let cond := arguments.headD 0
      write32 machine cond ((← read32 machine cond) + 1)
      wake machine.emu cond (2 ^ 32)
      value 0),
    ("pthread_key_create", show BaseFunction from fun machine arguments _ => do
      let key := (← state.get).nextKey
      state.modify fun state => { state with nextKey := key + 1 }
      write32 machine (arguments.headD 0) key
      value 0),
    ("pthread_key_delete", show BaseFunction from fun _ _ _ => value 0),
    ("pthread_setspecific", show BaseFunction from fun machine arguments _ => do
      let me ← tidOf machine
      state.modify fun state => { state with specific := state.specific.insert (me, arguments.headD 0) (arguments.getD 1 0) }
      value 0),
    ("pthread_getspecific", show BaseFunction from fun machine arguments _ => do
      value ((← state.get).specific.getD (← tidOf machine, arguments.headD 0) 0)),
    ("pthread_once", show BaseFunction from fun machine arguments _ => do
      let (once, routine) := (arguments.headD 0, arguments.getD 1 0)
      if (← read32 machine once) != 0 then return .value 0
      write32 machine once 1
      -- The routine runs as if it were called from here, and comes back to a stub that gives 0 to the caller.
      let emu := machine.emu
      let me ← tidOf machine
      let back ← onceStub.get
      match architecture with
      | .x86_64 | .i686 =>
        let sp ← match Value.asBits (← reg emu (register stack)) with
          | .ok bits => pure bits.2.toNat
          | .error _ => pure 0
        writeWord machine (sp - word) back
        setReg emu (register stack) (.bits (BitVec.ofNat width (sp - word)))
      | _ =>
        let link := match architecture with
          | .aarch64 => "X30"
          | .riscv64 | .riscv32 => "X1"
          | .mips .. => "R31"
          | _ => "LR"
        match Value.asBits (← reg emu (register link)) with
        | .ok bits => state.modify fun state => { state with onceReturns := state.onceReturns.insert me bits.2.toNat }
        | .error _ => pure ()
        setReg emu (register link) (.bits (BitVec.ofNat width back))
        if architecture matches .mips .. then setReg emu (register "R25") (.bits (BitVec.ofNat width routine))
      if architecture matches .arm then
        setReg emu ⟨"ISET", .imm 1, 0, false⟩ (.bits (BitVec.ofNat 1 (routine % 2)))
        setPc emu (routine - routine % 2)
      else setPc emu routine
      pure .finished) ]

/-- The functions of the base environment at their stubs, with what it keeps in `state`, and the data that it has, `__stack_chk_guard`,
which is written once: the stubs of a machine that goes on from a checkpoint are where they were, and what they have, already. -/
private def attachBase (machine : Machine) (state : IO.Ref BaseState) : IO BaseEnvironment := do
  let exitStub ← IO.mkRef 0
  let onceStub ← IO.mkRef 0
  let architecture := machine.architecture
  let width := architecture.bits
  -- Where a thread that `pthread_create` made goes when its routine returns: it is over, with what the routine gave.
  let dispatch ← IO.mkRef ({} : Dispatch)
  let exitAt ← install machine dispatch "base:thread-exit" fun machine _ _ => do
    let emu := machine.emu
    let tid ← Bap.Emu.thread emu
    let (_, _, result) := callAbiOf architecture
    let given ← match Value.asBits (← reg emu ⟨result, .imm width, 0, false⟩) with
      | .ok bits => pure bits.2.toNat
      | .error _ => pure 0
    finishThread machine state tid given
  exitStub.set exitAt
  -- Where the routine of `pthread_once` comes back to: `pthread_once` gives 0, to where it was called from.
  let onceAt ← install machine dispatch "base:once-return" fun machine _ _ => do
    let emu := machine.emu
    let tid ← Bap.Emu.thread emu
    match architecture with
    | .x86_64 | .i686 => pure ()
    | _ =>
      let link := match architecture with
        | .aarch64 => "X30"
        | .riscv64 | .riscv32 => "X1"
        | .mips .. => "R31"
        | _ => "LR"
      if let some back := (← state.get).onceReturns.get? tid then
        setReg emu ⟨link, .imm width, 0, false⟩ (.bits (BitVec.ofNat width back))
        state.modify fun state => { state with onceReturns := state.onceReturns.erase tid }
    pure (.value 0)
  onceStub.set onceAt
  let mut symbols : List (String × Nat) := []
  for (name, function) in functions machine state exitStub onceStub do
    symbols := (name, ← install machine dispatch s!"base:{name}" function) :: symbols
  serveStubs machine dispatch
  -- What a stack protector compares with.
  let guard ← machine.stubFor "base:__stack_chk_guard"
  if (← peek machine.emu (guard + 8) 8).toList.all (· == 0) then
    poke machine.emu (guard + 8) (ByteArray.mk #[0x00, 0x5a, 0xa5, 0x3c, 0x00, 0x00, 0x00, 0x00])
  pure { symbols := ("__stack_chk_guard", guard + 8) :: symbols.reverse, state }
where
  /-- The result register of a call. -/
  callAbiOf : Architecture → String × String × String
    | .x86_64 => ("", "", "RAX")
    | .i686 => ("", "", "EAX")
    | .aarch64 => ("", "", "X0")
    | .arm => ("", "", "R0")
    | .riscv64 | .riscv32 => ("", "", "X10")
    | .mips .. => ("", "", "R2")
    | .powerpc .. => ("", "", "R3")

namespace BaseState

private def putTable (out : ByteArray) (table : Std.HashMap Nat Nat) : ByteArray :=
  Wire.putSorted (fun out (key, value) => Wire.putNat (Wire.putNat out key) value) out table.toList

private def getTable : Wire.Decoder (Std.HashMap Nat Nat) := fun data at_ => do
  let (entries, at_) ← Wire.getList (fun data at_ => do
    let (key, at_) ← Wire.getNat data at_
    let (value, at_) ← Wire.getNat data at_
    .ok ((key, value), at_)) data at_
  .ok (Std.HashMap.ofList entries, at_)

/-- What the environment keeps, as bytes: the same state makes the same bytes. -/
def encode (state : BaseState) : ByteArray :=
  let out := putTable (putTable (Wire.putNat ByteArray.empty state.nextKey) state.results) state.joinWords
  let out := Wire.putSorted (fun out ((key, tid), value) => Wire.putNat (Wire.putNat (Wire.putNat out key) tid) value) out
    state.specific.toList
  let out := putTable (putTable (putTable out state.aligned) state.errno) state.onceReturns
  let out := Wire.putSorted (fun out (tid, (base, size)) => Wire.putNat (Wire.putNat (Wire.putNat out tid) base) size) out
    state.stacks.toList
  Wire.putSorted Wire.putNat (putTable out state.blocks) state.detached.toList

def decode (data : ByteArray) : Except String BaseState := do
  let (nextKey, at_) ← Wire.getNat data 0
  let (results, at_) ← getTable data at_
  let (joinWords, at_) ← getTable data at_
  let (specific, at_) ← Wire.getList (fun data at_ => do
    let (key, at_) ← Wire.getNat data at_
    let (tid, at_) ← Wire.getNat data at_
    let (value, at_) ← Wire.getNat data at_
    .ok (((key, tid), value), at_)) data at_
  let (aligned, at_) ← getTable data at_
  let (errno, at_) ← getTable data at_
  let (onceReturns, at_) ← getTable data at_
  let (stacks, at_) ← Wire.getList (fun data at_ => do
    let (tid, at_) ← Wire.getNat data at_
    let (base, at_) ← Wire.getNat data at_
    let (size, at_) ← Wire.getNat data at_
    .ok ((tid, (base, size)), at_)) data at_
  let (blocks, at_) ← getTable data at_
  let (detached, at_) ← Wire.getList Wire.getNat data at_
  Wire.expectEnd data at_
  pure { nextKey, results, joinWords, specific := Std.HashMap.ofList specific, aligned, errno, onceReturns,
         stacks := Std.HashMap.ofList stacks, blocks, detached := Std.HashSet.ofList detached }

end BaseState

/-- What a checkpoint knows the base environment by. -/
def baseModelId : String := "bap.base"

/-- The base environment as a model of the runtime, for `start` or `Machine.ofCheckpoint`, which leaves it in `cell`: what it keeps is
in a checkpoint, and is put back, all of it or, if the bytes aren't of it, none. -/
def baseModel (cell : IO.Ref (Option BaseEnvironment)) : RuntimeModel where
  id := baseModelId
  -- 2: with the thread-local storage of threads, and those that are detached.
  version := 2
  attach := fun machine => do
    let state ← IO.mkRef ({} : BaseState)
    let base ← attachBase machine state
    cell.set (some base)
    pure { save := do pure (← state.get).encode, load := fun data => do state.set (← IO.ofExcept (BaseState.decode data)) }

/-- The base environment of a machine, made once, as the model `baseModel` is attached: its functions at their stubs, and the data
that it has, `__stack_chk_guard`. A machine that goes on from a checkpoint of it is given `baseModel`. -/
def Machine.baseEnvironment (machine : Machine) : IO BaseEnvironment := do
  let cell ← IO.mkRef none
  let _ ← machine.attachModel (baseModel cell)
  let some base ← cell.get | throw <| IO.userError "the base environment wasn't attached"
  pure base

/-- Loads a library linked against the base environment, which it has before anything that is loaded, a libc among them. -/
def Machine.loadWithBase (machine : Machine) (base : BaseEnvironment) (path : String) (search : List String := [])
    (resolve : String → Option Nat := fun _ => none) (runInitializers : Bool := true) : IO LoadedLibrary :=
  machine.loadLibrary path search resolve (runInitializers := runInitializers) (prefer := base.resolve)

/-- Has what is loaded already import the names of the base environment from it, rather than from where they were found: what is called
of them goes to the environment's. It says how many slots there were. -/
def Machine.linkBase (machine : Machine) (base : BaseEnvironment) : IO Nat := do
  let mut count := 0
  for library in ← machine.loadedLibraries do
    for (name, address) in base.symbols do
      count := count + (← machine.redirectImport library name address)
  pure count

end Bap.Linux
