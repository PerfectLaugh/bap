import Bap.Target.RISCV
import Bap.Target.RISCV32
import Bap.Target.X86
import Bap.Target.X8632
import Bap.Target.AArch64
import Bap.Target.PowerPC
import Bap.Target.ARM32
import Bap.Target.Thumb
import Bap.Target.MIPS
import Bap.Target.MIPS32
import Bap.Primus.Lifted
import Bap.Primus.Memory
import Bap.Emu.Core
import Std.Sync.Mutex
import Std.Data.HashSet

namespace Bap.Emu

/-- Which registers a system call and a call of C use, by the family of the target. -/
inductive SyscallAbi where
  | riscv | x86_64 | aarch64 | mips | powerpc | powerpc64 | x86_32 | arm
  deriving DecidableEq, Repr

/-- Whether branches have delay slots, as those of MIPS do but for the compact ones of release 6. -/
inductive DelayPolicy where
  | none | mips (release6 : Bool)
  deriving DecidableEq, Repr

/-- How an emulator decodes, where its memory is, and the limits of what it compiles. -/
structure Config where
  disassembler : Disasm.Disassembler
  /-- The decoder of code that starts at another base, such as a library's, if the target needs to know it. -/
  disassemblerAt : Option (Nat → IO Disasm.Disassembler) := none
  /-- The decoder of Thumb, if the target has it as well as the other: `ISET` says which of them comes next. -/
  thumbAt : Option (Nat → IO Disasm.Disassembler) := none
  /-- The variable of memory that the lifted code loads and stores in. -/
  memory : Bap.Var
  endian : Endian := .little
  syscallAbi : SyscallAbi := .riscv
  delayPolicy : DelayPolicy := .none
  /-- How many times an instruction runs in the interpreter, which takes microseconds, before it is compiled, which takes
  hundreds of them: most of a program runs a few times at most. -/
  hotThreshold : Nat := 16
  /-- Whether what is at the entry is compiled as the emulator is made, with what it loops optimized on other threads then, rather
  than as it runs: what is done before the first run, such as mapping its memory, is then done while that compiles, as an ahead
  of time translator does it before a program starts. -/
  compileAtLoad : Bool := true
  /-- How many instructions what is lifted and compiled is kept of, of which the least used go. -/
  cacheLimit : Nat := 4096
  /-- How many compiled ranges are kept, of which the least used go; `none` is `cacheLimit`. -/
  rangeCacheLimit : Option Nat := none
  /-- How much native code is kept, of blocks and ranges and the versions of them that writes to code leave, each tens of kilobytes:
  past it what ran least goes. `none` is 4 times `cacheLimit`. -/
  nativeLimit : Option Nat := none
  /-- Whether a block that gets hot may run a range that has it from the middle, see `Lifted.Engine.rangeEntries`. The variable
  `BAP_RANGE_ENTRIES` of the environment says so too. -/
  rangeEntries : Bool := false
  /-- How many blocks a compiled range holds. 16 runs tight loops whole, and the cost of compiling a range grows faster than its
  size. A step of 1 has no ranges. -/
  rangeLimit : Nat := 16
  /-- How many steps after a write to code nothing is compiled, for code that writes itself all the time. -/
  jitCooldown : Nat := 0
  /-- Where an address that the guest gives is in memory, which on AArch64 ignores its top byte, as a kernel does of what a program
  gives it once the program asks with `PR_SET_TAGGED_ADDR_CTRL`. -/
  untag : Nat → Nat := id

/-- What `removeHook` takes to take a hook off. -/
abbrev HookId := Nat

/-- How instructions run: by compiling those that get hot, or all of them in the interpreter, which never starts the compiler. The same things happen either way. It is what
a host wants of a run and not a thing about a guest, so that it isn't in a checkpoint. -/
inductive ExecutionMode where
  | jit | interpret
  deriving DecidableEq, Repr, Inhabited

/-- What a hook of a system call does with it: leaves it to the next one, or gives it this result. -/
inductive SyscallAction where
  | default | returnValue (value : Nat)

/-- What a hook of an intrinsic does with it: leaves it to the next one, or has the instruction go on as served. -/
inductive IntrinsicAction where
  | default | proceed

/-- An access to memory that a trace kept: of which instruction of the run, where, how much, and what was written. -/
structure TraceAccess where
  insn : Nat
  pc : Nat
  address : Nat
  size : Nat
  write : Bool
  value : Option Nat
  thread : ThreadId
  deriving DecidableEq, Repr

/-- The pcs of a trace, the last `capacity` of them or all if that is 0, in order: those of `front`, then those of `back` from the last.
Of each instruction it also has the bytes that it ran as, by when they were new: what was at a pc is what it was the last time that it
changed before then, which a program that writes its own code changes, and which disassembling it later wouldn't say. -/
private structure TraceRing where
  front : List Nat := []
  back : List Nat := []
  retained : Nat := 0
  /-- How many it saw, kept or not. -/
  count : Nat := 0
  dropped : Nat := 0
  capacity : Nat := 0
  /-- Each time that the bytes at a pc were new, newest first: which of what it saw, from 0, was the first to run as them, where, and the
  bytes. -/
  code : List (Nat × Nat × ByteArray) := []
  /-- How many there are of `code`, and how many there may be before what no pc kept needs any more goes. -/
  codeSize : Nat := 0
  codeLimit : Nat := 64
  /-- The bytes that each pc had the last time that it ran, which also say how long the instruction there is, while they stay. -/
  known : Std.HashMap Nat ByteArray := {}

/-- What a trace keeps: of which threads, if not all, and whether each has a ring of its own, so that what one does isn't lost among what
the others do. -/
structure TraceOptions where
  /-- How many pcs a ring keeps, the last of them, or all if 0. -/
  pcCapacity : Nat := 0
  /-- How many accesses to memory are kept, the last of them. -/
  accessCapacity : Nat := 0
  /-- Only the accesses that touch this range, if there is one. -/
  watch : Option (Nat × Nat) := none
  /-- Ranges, each with a ring of its own of the last `accessCapacity` accesses that touch it, so that what touches one isn't lost
  among what touches the others or anything else: `traceWatchAccesses`. With these and no `watch`, the one ring of accesses keeps
  nothing. -/
  watches : List (Nat × Nat) := []
  /-- Only what these threads do, if they are given. -/
  threads : Option (List ThreadId) := none
  /-- Each thread with a ring of its own, of `pcCapacity` each. -/
  perThread : Bool := false
  deriving DecidableEq, Repr

/-- What a trace says of a thread: how many of its instructions it saw, how many of them it keeps, and how many it let go of. -/
structure TraceThread where
  thread : ThreadId
  count : Nat
  kept : Nat
  dropped : Nat
  deriving DecidableEq, Repr

/-- The ring of a range that a trace watches on its own: the accesses that touched it, the last first, how many did, and how many it
has, which are let go of when they are twice what is kept. -/
private structure WatchRing where
  range : Nat × Nat
  accesses : List TraceAccess := []
  count : Nat := 0
  retained : Nat := 0

/-- What a trace says of a range that it watches on its own: how many accesses touched it, how many of them it keeps, and how many it let
go of. -/
structure TraceWatch where
  range : Nat × Nat
  count : Nat
  kept : Nat
  dropped : Nat
  deriving DecidableEq, Repr

private structure TraceState where
  options : TraceOptions := {}
  /-- How many instructions it saw, of all threads that it keeps. -/
  count : Nat := 0
  /-- The ring of all threads, or of each. -/
  ring : TraceRing := {}
  rings : Std.HashMap ThreadId TraceRing := {}
  accesses : List TraceAccess := []
  accessCount : Nat := 0
  /-- How many there are of `accesses`, which are let go of when they are twice what is kept. -/
  accessRetained : Nat := 0
  /-- A ring of each of `options.watches`, in their order. -/
  watched : Array WatchRing := #[]
  /-- How many accesses it kept in any ring, each once, however many rings kept it. -/
  accessesHeard : Nat := 0


/-- Whether a trace keeps what a thread does. -/
private def TraceState.keeps (state : TraceState) (thread : ThreadId) : Bool :=
  state.options.threads.all (·.contains thread)

/-- The traces of an emulator: the one of `traceStart` and `traceStop`, which is anyone's, and each that a `TraceSession` opened, by its
name, which only that session stops or starts again, so that one piece of instrumentation can't undo what another captures. -/
private structure TraceSet where
  default : Option TraceState := none
  /-- Each by its name, with the token of the session that owns it. -/
  named : List (String × Nat × TraceState) := []
  nextToken : Nat := 0

/-- Whether anything is traced. -/
private def TraceSet.active (set : TraceSet) : Bool :=
  set.default.isSome || !set.named.isEmpty

/-- The trace of a name, or the default one of the empty name. -/
private def TraceSet.find? (set : TraceSet) (name : String) : Option TraceState :=
  if name.isEmpty then set.default else (set.named.find? (·.1 == name)).map (·.2.2)

/-- Each trace changed by `change`. -/
private def TraceSet.mapStates (set : TraceSet) (change : TraceState → TraceState) : TraceSet :=
  { set with default := set.default.map change, named := set.named.map fun (name, token, state) => (name, token, change state) }

/-- The state of the thread that runs, as a reference to it is, but for one that a code site of a compiled range says: what reads
it first has it said, which a hook that reads nothing of it never does, and setting it forgets it. -/
structure StateCell where
  ref : IO.Ref Bil.State
  pending : IO.Ref (Option (IO Bil.State))

def StateCell.new (state : Bil.State) : BaseIO StateCell := do
  pure { ref := ← IO.mkRef state, pending := ← IO.mkRef none }

def StateCell.get (cell : StateCell) : IO Bil.State := do
  match ← cell.pending.swap none with
  | some say =>
    let state ← say
    cell.ref.set state
    pure state
  | none => cell.ref.get

def StateCell.set (cell : StateCell) (state : Bil.State) : BaseIO Unit := do
  cell.pending.set none
  cell.ref.set state

def StateCell.modify (cell : StateCell) (change : Bil.State → Bil.State) : IO Unit := do
  cell.set (change (← cell.get))

/-- The state that `say` says from now on, said when it is first read. -/
def StateCell.defer (cell : StateCell) (say : IO Bil.State) : BaseIO Unit :=
  cell.pending.set (some say)

/-- Whether what `defer` gave is yet to be said. -/
def StateCell.deferred (cell : StateCell) : BaseIO Bool := do
  pure (← cell.pending.get).isSome

private structure CodeHookContext where
  engine : Primus.Lifted.Engine
  state : StateCell
  pc : IO.Ref Nat
  stopped : IO.Ref Bool
  currentThreadRef : IO.Ref ThreadId
  trace : IO.Ref TraceSet
  lastFault : IO.Ref (Option MemoryFault)
  skipCode : IO.Ref (Option Nat)
  pendingRef : IO.Ref (Option PendingBranch)

/-- A hook of loads in a range of addresses. -/
structure ReadHook where
  id : HookId
  first : Nat
  last : Nat
  action : CodeHookContext → Nat → Nat → IO Unit

/-- A hook of stores in a range of addresses. -/
structure WriteHook where
  id : HookId
  first : Nat
  last : Nat
  action : CodeHookContext → Nat → Nat → Nat → IO Unit

/-- A hook of an intrinsic, by its name. -/
structure IntrinsicHook where
  id : HookId
  name : String
  action : CodeHookContext → Nat → IO IntrinsicAction

/-- A hook of each instruction in a range of addresses, before it runs. -/
structure CodeHook where
  id : HookId
  first : Nat
  last : Nat
  action : CodeHookContext → Nat → IO Unit

/-- A hook of system calls, which has the number and the arguments. -/
structure SyscallHook where
  id : HookId
  action : CodeHookContext → Nat → List Nat → IO SyscallAction

/-- How steps were taken back, and why: a fault of memory, an access to something watched that a range couldn't stop for, or anything
else, such as a hook that threw. A range that faults counts twice, as it goes back and comes again as one step, which faults as well. Of those that have a memory of their own or kept one, `patched` took back what the step wrote, and
`rebuilt` made it again from all of the state, which takes as long as the process is big. A worker of a parallel round does neither. -/
structure RollbackStats where
  faults : Nat := 0
  restarts : Nat := 0
  others : Nat := 0
  patched : Nat := 0
  rebuilt : Nat := 0
  bytesRestored : Nat := 0
  deriving Repr, Inhabited

/-- A patch that was applied: where, in which address space, what was there before and what was put, and the hook that counts loads
of its bytes while it is the last patch there. -/
structure PatchRecord where
  address : Nat
  space : Nat
  original : ByteArray
  replacement : ByteArray
  readHook : Option HookId := none
  deriving Inhabited

/-- How many loads the instruction at `pc` made of the bytes of the patch at `patch`, as a check of a program's own code makes. -/
structure PatchRead where
  pc : Nat
  patch : Nat
  count : Nat
  deriving Repr, DecidableEq, Inhabited

/-- An emulator: its configuration, the engine that runs lifted code, the thread that runs and the others, memory, hooks, traces, and
the tasks of Linux that a kernel needs. Everything in it is a reference, so that a copy of it is the same emulator. -/
structure Emu where
  config : Config
  engine : Primus.Lifted.Engine
  state : StateCell
  pc : IO.Ref Nat
  regions : IO.Ref (List Region)
  stopped : IO.Ref Bool
  hooks : IO.Ref (List CodeHook)
  /-- The hooks of each page that code has run on, which is what an instruction goes by. All that changes `hooks` empties it. -/
  hooksByPage : IO.Ref (Std.HashMap Nat (List CodeHook))
  /-- The hooks that cover each address that code has run at, so that an instruction doesn't test the others of its page again. All
  that changes `hooks` empties it. -/
  hooksExact : IO.Ref (Std.HashMap Nat (List CodeHook))
  readHooks : IO.Ref (List ReadHook)
  writeHooks : IO.Ref (List WriteHook)
  syscallHooks : IO.Ref (List SyscallHook)
  intrinsicHooks : IO.Ref (List IntrinsicHook)
  nextHook : IO.Ref HookId
  trace : IO.Ref TraceSet
  lastFault : IO.Ref (Option MemoryFault)
  skipCode : IO.Ref (Option Nat)
  /-- Of a thread that stopped where hooks fired, and that a hook came to afterwards: where, and the hooks that fired there, which don't
  fire again when it goes on, as the one that came after does. -/
  suppressed : IO.Ref (List (ThreadId × Nat × List HookId))
  breakpointsRef : IO.Ref (List (HookId × Nat))
  /-- Whether breakpoints don't stop anything, as when what has run is run again. -/
  breakpointsMuted : IO.Ref Bool
  /-- How many instructions `runProcesses` has run, as its fuel counts them. -/
  executed : IO.Ref Nat
  /-- How many instructions have run, counted as each step ends, before a system call or an intrinsic that ends it is served, so
  that what serves it knows how many ran up to and with it, which `executed` says only once a run is over. A step that fails and is
  taken back isn't counted. Workers of a parallel round count here too. -/
  retired : IO.Ref Nat
  /-- How many of `retired` the step that runs counted, which it takes back if it is taken back: rolled back, or stopped at a special
  that nothing serves, whose step runs again from its start. Each worker of a parallel round has its own. -/
  stepRetired : IO.Ref Nat
  threadsRef : IO.Ref (List ThreadContext)
  currentThreadRef : IO.Ref ThreadId
  nextThreadRef : IO.Ref ThreadId
  pendingRef : IO.Ref (Option PendingBranch)
  parallelLock : IO.Ref (Option Std.BaseMutex)
  parallelWorkers : IO.Ref (List (ThreadId × Primus.Lifted.Engine))
  /-- The memory of each address space other than the first, by the id of the space. -/
  processMemory : IO.Ref (Std.HashMap ThreadId Jit.Memory)
  threadControl : IO.Ref (Std.HashMap ThreadId Bool)
  /-- The memory of the threads without their own, while a thread with its own runs. -/
  sharedMemory : IO.Ref (Option Jit.Memory)
  /-- The ranges that a parallel worker wrote. Workers leave the memory of their state behind. -/
  journal : Option (IO.Ref (List (Nat × Nat))) := none
  /-- How many blocks the last step could chain, which says whether its failure is the fault itself. -/
  lastBudget : IO.Ref Nat
  /-- Whether the compiled range that runs started with nothing to observe it: no trace, and no code hook in what it has. -/
  rangeQuiet : IO.Ref Bool
  /-- How many times the code hooks changed, and how many it was when the range that runs started, so that a hook that comes
  while it runs unobserved ends it. -/
  hookChanges : IO.Ref Nat
  rangeHooks : IO.Ref Nat
  /-- Whether the filter of the native memory is to be made again, as what it lets through has changed, and whether reads and writes
  were heard of when it was made, which a change of the regions alone keeps to. -/
  memoryFilterStale : IO.Ref Bool
  memoryFilterHeard : IO.Ref (Bool × Bool)
  /-- How many instructions the next step may run after its first, for `run`: a step on its own runs one. -/
  budget : IO.Ref Nat
  /-- Whether the step that just failed did so to run again as one instruction, at a hook of an access. -/
  restarting : IO.Ref Bool
  /-- The address of the running step until it reaches a code site. -/
  rangeStart : IO.Ref (Option Nat)
  /-- The addresses whose steps met a hook of an access, which run as one instruction from then on. Nothing else depends on
  it: which steps chain changes how fast the emulator runs and not what it does. -/
  watchedSteps : IO.Ref (Std.HashSet Nat)
  /-- The tasks, and which are blocked waiting for others. -/
  taskTable : IO.Ref Tasks.TaskTable
  /-- What is mapped in the address spaces other than that of the thread that runs, whose map is `regions`. -/
  parkedRegions : IO.Ref (Std.HashMap Nat (List Region))
  /-- For a page that instructions came from, the executable region that had them, which saves `fetch` going through the
  regions. All that changes `regions` empties it, by `setRegions`. -/
  fetchPages : IO.Ref (Std.HashMap Nat (Nat × Nat))
  /-- The regions by where they start, as every access looks for its own, and there may be as many as a program has mapped. It is made from `regions` when it is
  needed after they are all replaced. -/
  regionIndex : IO.Ref (Option (Std.TreeMap Nat Region))
  /-- That all from here up to where mappings start from is mapped, so that the next goes below it. -/
  mappingTop : IO.Ref (Option Nat)
  /-- What serves intrinsics in the code that names them: the bits of what is computed from the name and the bits of the
  operands, as its width and its bits. Lifted code runs up to an intrinsic, and what comes after it wouldn't run. -/
  intrinsicServer : IO.Ref (Option (String → List Nat → Option (Nat × Nat)))
  /-- What an intrinsic comes to on a state, for one that goes by the rounding mode of the machine. -/
  intrinsicName : IO.Ref (Bil.Env → String → String)
  /-- What an intrinsic that gave a result changes of a state besides: the flags that it raises. -/
  intrinsicRaises : IO.Ref (Bil.Env → String → List Nat → Nat → List (Bap.Var × Bap.Value))
  /-- What the controls of the machine make of the operands and of the result of an intrinsic. -/
  intrinsicControls : IO.Ref (Bil.Env → String → (List Nat → List Nat) × (Nat → Nat))
  /-- The programs of the instructions that have such an intrinsic, each by the number that its `served:` special says. -/
  servedPrograms : IO.Ref (Std.HashMap Nat Bil.Program)
  /-- What wants to know of a new process: of the one that made it, and of it. -/
  processHooks : IO.Ref (List (Nat → Nat → IO Unit))
  /-- What wants to know that the parent of `vfork` goes on, as its child runs a program or ends: of the parent, and of the child. -/
  vforkReleased : IO.Ref (List (Nat → Nat → IO Unit))
  /-- What wants to know that a thread that runs a program took the id of its process, which was its leader's, which is over: of the
  id that it had, and of that one. What is kept of a thread by its id is to go with it, and what was the leader's to go. -/
  leaderTaken : IO.Ref (List (Nat → Nat → IO Unit))
  /-- The clock of the machine, in nanoseconds, which a wait with a timeout has its deadline by, if it has one. -/
  now : IO.Ref (Option (IO Nat))
  /-- What the scheduler asks when nothing can run: that time goes on to what happens next, as a deadline or a timer, which may let
  something run. Whether anything changed. -/
  idle : IO.Ref (Option (IO Bool))
  /-- Where the instruction that runs goes next, for a system call to know where a new thread starts. -/
  nextPc : IO.Ref Nat
  /-- Where the instruction that runs goes after all, for a program that a system call has replaced. -/
  redirect : IO.Ref (Option Nat)
  /-- What the hooks of a code site in the middle of a native run left the state as, where they changed what the run goes on with,
  which the run stopped there for: the state that the step leaves, rather than the run's. -/
  siteState : IO.Ref (Option Bil.State)
  /-- The sites in the middle of the native run that goes on whose hooks fired, in order, and, of a run that was taken back to be run
  again a step at a time, those of them that it hasn't come to again, whose hooks don't fire again where it does. -/
  firedSites : IO.Ref (Array Nat)
  replaySites : IO.Ref (List Nat)
  /-- How much of its turn the thread that runs had had when the fuel ran out, or 0 between turns. -/
  turnUsed : IO.Ref Nat
  /-- What runs when a system call has its result, which may send the thread somewhere else. -/
  afterSyscall : IO.Ref (Option (IO Unit))
  /-- What runs when a thread has been switched to and before it goes on. -/
  switchedIn : IO.Ref (Option (IO Unit))
  /-- What sees a system call before it is served, with its number and arguments, and after, with its result if something served it. -/
  syscallStarts : IO.Ref (List (Nat → List Nat → IO Unit))
  syscallEnds : IO.Ref (List (Option Nat → IO Unit))
  /-- What runs between turns of `runProcesses`, where nothing is in the middle of anything: as a wait is given what it waits for. -/
  betweenTurns : IO.Ref (List (IO Unit))
  /-- What hears of bytes of a guest that no instruction of it changed: where and how many, and whether they became zeros because of nothing. -/
  memoryChanged : IO.Ref (List (Nat → Nat → Bool → IO Unit))
  /-- The patches that were applied, the last first, and the loads of their bytes by the instruction that made them and the patch. -/
  patched : IO.Ref (List PatchRecord)
  patchReads : IO.Ref (Std.HashMap (Nat × Nat) Nat)
  /-- What hears that the host moved bytes of a guest from one place to another, from, to and how many. -/
  memoryCopied : IO.Ref (List (Nat → Nat → Nat → IO Unit))
  /-- What hears that the host is serving a call of the guest that isn't a system call, such as one of JNI, by name, and then that it has
  left what it returns in a register, by name of that, if it returns something. -/
  hostStarts : IO.Ref (List (String → IO Unit))
  hostEnds : IO.Ref (List (Option String → IO Unit))
  /-- What hears of the bytes of the guest that the host reads as it serves a call, by address and size, as what it gives back comes from
  them. -/
  hostReads : IO.Ref (List (Nat → Nat → IO Unit))
  /-- What runs before a thread of another address space takes over, in the one that it leaves, and after, in the one that it is in. -/
  leavingSpace : IO.Ref (Option (IO Unit))
  enteredSpace : IO.Ref (Option (IO Unit))
  /-- What a word of memory that address spaces share is to `futex`, as what they wait on there isn't an address of any of them. -/
  futexKey : IO.Ref (Option (Nat → IO (Option (Nat × Nat))))
  /-- What may take a fault of a guest of `runProcesses`, and says whether it did. -/
  faultHandler : IO.Ref (Option (MemoryFault → IO Bool))
  /-- What hears that a process is over, with its status. -/
  processExited : IO.Ref (Option (Nat → Nat → IO Unit))
  /-- Whether a hook runs in the middle of an instruction: of a system call, an intrinsic or an access. -/
  serving : IO.Ref Bool
  /-- Whether a fault has been recorded since the last rollback, which says why that one came. -/
  faultFresh : IO.Ref Bool
  /-- The native memory that the step that runs began with. -/
  stepNative : IO.Ref (Option Jit.Memory)
  /-- Whether the native memory has been replaced since then, when what was written to the old one is no help. -/
  memorySwitched : IO.Ref Bool
  rollbacks : IO.Ref RollbackStats
  /-- Whether this is a worker of a parallel round that stops before what has to be atomic. -/
  atomicGated : IO.Ref Bool
  /-- Whether it has stopped there, and hasn't run it. -/
  atomicReached : IO.Ref Bool
  /-- Whether the instruction that was these bytes at an address has to be atomic, as finding out takes lifting it. -/
  atomicSites : IO.Ref (Std.HashMap Nat (ByteArray × Bool))

/-- Compiled ranges chain blocks along their branches, which leaves delay slots out. -/
private def rangeLimitOf (config : Config) : Nat :=
  if config.delayPolicy == .none then config.rangeLimit else 1

private def memoryWidth (config : Config) : Except String Nat :=
  match config.memory.typ with
  | .mem width 8 => .ok width
  | _ => .error "Emu memory must have byte-wide cells"

private def overlaps (left right : Region) : Bool :=
  left.address < right.address + right.data.size &&
    right.address < left.address + left.data.size

/-- Whether every byte of `region` is addressable with `width` address bits. -/
def regionInSpace (width : Nat) (region : Region) : Bool :=
  region.address + region.data.size ≤ 2 ^ width

/-- Whether `region` can overlay `mapped`: it replaces a same-sized region at its own address and
touches no other. -/
def overlayConflict (mapped : List Region) (region : Region) : Bool :=
  mapped.any fun current =>
    if current.address = region.address then current.data.size != region.data.size
    else overlaps current region

private def initializeMemory (config : Config) (regions : List Region) : Except String Bil.State := do
  let width ← memoryWidth config
  if regions.any fun left => regions.any fun right => left != right && overlaps left right then
    .error "Emu regions overlap"
  if !regions.all (regionInSpace width) then
    .error "Emu region exceeds the address space"
  let cells := regions.foldl (init := Bap.Memory.empty width) fun cells region =>
    Bap.Memory.writeRegion cells region.address region.data
  .ok { env := Bil.bind {} config.memory (.memory cells) }

/-- An engine for the emulator. Its memory is native from the start, its observer is `notifyMemory`, which rejects
an access past the end of the address space, and a block that runs off its end goes on with the next one. -/
private def createEngine (config : Config) (deferMemorySync : Bool) : IO Primus.Lifted.Engine := do
  let asked := (← IO.getEnv "BAP_RANGE_ENTRIES").isSome
  Primus.Lifted.Engine.create config.hotThreshold config.cacheLimit (rangeLimitOf config)
    (config.rangeCacheLimit.getD config.cacheLimit) config.jitCooldown deferMemorySync
    (nativeLimit := config.nativeLimit.getD (4 * config.cacheLimit)) (persistentFrom := 0) (wrapFaults := true) (chainFallthrough := true)
    (rangeEntries := config.rangeEntries || asked)

/-- An emulator with these regions mapped and these registers, that starts at `entry` in one thread. -/
def create (config : Config) (mapped : List Region) (initial : Bil.State) (entry : Nat) : IO Emu := do
  let initial ← match initializeMemory config mapped with
    | .ok memory => pure { env := memory.env ++ initial.env }
    | .error error => throw <| IO.userError error
  pure {
    config
    engine := ← createEngine config false
    state := ← StateCell.new initial
    pc := ← IO.mkRef entry
    regions := ← IO.mkRef mapped
    stopped := ← IO.mkRef false
    hooks := ← IO.mkRef []
    hooksByPage := ← IO.mkRef {}
    hooksExact := ← IO.mkRef {}
    readHooks := ← IO.mkRef []
    writeHooks := ← IO.mkRef []
    syscallHooks := ← IO.mkRef []
    intrinsicHooks := ← IO.mkRef []
    nextHook := ← IO.mkRef 0
    trace := ← IO.mkRef {}
    lastFault := ← IO.mkRef none
    skipCode := ← IO.mkRef none
    suppressed := ← IO.mkRef []
    breakpointsRef := ← IO.mkRef []
    breakpointsMuted := ← IO.mkRef false
    executed := ← IO.mkRef 0
    retired := ← IO.mkRef 0
    stepRetired := ← IO.mkRef 0
    threadsRef := ← IO.mkRef [⟨1, initial, entry, false, none, none⟩]
    currentThreadRef := ← IO.mkRef 1
    nextThreadRef := ← IO.mkRef 2
    pendingRef := ← IO.mkRef none
    parallelLock := ← IO.mkRef none
    parallelWorkers := ← IO.mkRef []
    processMemory := ← IO.mkRef {}
    threadControl := ← IO.mkRef {}
    sharedMemory := ← IO.mkRef none
    lastBudget := ← IO.mkRef 0
    rangeQuiet := ← IO.mkRef false
    hookChanges := ← IO.mkRef 0
    rangeHooks := ← IO.mkRef 0
    memoryFilterStale := ← IO.mkRef true
    memoryFilterHeard := ← IO.mkRef (true, true)
    budget := ← IO.mkRef 0
    restarting := ← IO.mkRef false
    rangeStart := ← IO.mkRef none
    watchedSteps := ← IO.mkRef {}
    taskTable := ← IO.mkRef (Tasks.TaskTable.initial 1)
    parkedRegions := ← IO.mkRef {}
    fetchPages := ← IO.mkRef {}
    regionIndex := ← IO.mkRef none
    mappingTop := ← IO.mkRef none
    intrinsicServer := ← IO.mkRef none
    intrinsicName := ← IO.mkRef fun _ name => name
    intrinsicRaises := ← IO.mkRef fun _ _ _ _ => []
    intrinsicControls := ← IO.mkRef fun _ _ => (id, id)
    servedPrograms := ← IO.mkRef {}
    processHooks := ← IO.mkRef []
    vforkReleased := ← IO.mkRef []
    leaderTaken := ← IO.mkRef []
    now := ← IO.mkRef none
    idle := ← IO.mkRef none
    nextPc := ← IO.mkRef 0
    redirect := ← IO.mkRef none
    siteState := ← IO.mkRef none
    firedSites := ← IO.mkRef #[]
    replaySites := ← IO.mkRef []
    turnUsed := ← IO.mkRef 0
    serving := ← IO.mkRef false
    afterSyscall := ← IO.mkRef none
    switchedIn := ← IO.mkRef none
    syscallStarts := ← IO.mkRef []
    syscallEnds := ← IO.mkRef []
    betweenTurns := ← IO.mkRef []
    memoryChanged := ← IO.mkRef []
    patched := ← IO.mkRef []
    patchReads := ← IO.mkRef {}
    memoryCopied := ← IO.mkRef []
    hostStarts := ← IO.mkRef []
    hostEnds := ← IO.mkRef []
    hostReads := ← IO.mkRef []
    leavingSpace := ← IO.mkRef none
    enteredSpace := ← IO.mkRef none
    futexKey := ← IO.mkRef none
    faultHandler := ← IO.mkRef none
    processExited := ← IO.mkRef none
    faultFresh := ← IO.mkRef false
    stepNative := ← IO.mkRef none
    memorySwitched := ← IO.mkRef false
    rollbacks := ← IO.mkRef {}
    atomicGated := ← IO.mkRef false
    atomicReached := ← IO.mkRef false
    atomicSites := ← IO.mkRef {}
  }

/-- The address space of a thread. -/
def spaceOf (emu : Emu) (id : ThreadId) : IO Nat := do pure ((← emu.taskTable.get).spaceOf id)

/-- Puts what the thread that runs is now in its context, for when another runs. -/
def saveCurrentThread (emu : Emu) : IO Unit := do
  let context : ThreadContext := {
    id := ← emu.currentThreadRef.get
    state := ← emu.state.get
    pc := ← emu.pc.get
    stopped := ← emu.stopped.get
    pending := ← emu.pendingRef.get
    skip := ← emu.skipCode.get
  }
  emu.threadsRef.modify (saveContext · context)

private def captureThreads (emu : Emu) : IO (List ThreadContext) := do
  saveCurrentThread emu
  let state ← emu.state.get
  let memory := match Bil.lookup state.env emu.config.memory with
    | .ok value => some value
    | .error _ => none
  let threads ← emu.threadsRef.get
  let table ← emu.taskTable.get
  let space := table.spaceOf (← emu.currentThreadRef.get)
  pure (threads.map fun thread =>
    if table.spaceOf thread.id != space then thread else
      match memory with
      | some memory => { thread with state := { env := Bil.bind thread.state.env emu.config.memory memory } }
      | none => thread)

private def persistentRegionData (cells : List (Nat × UInt8)) (address size : Nat)
    (output : Array UInt8) : Array UInt8 :=
  if _h : output.size ≥ size then output else
    let expected := address + output.size
    match cells with
    | [] => output ++ Array.replicate (size - output.size) 0
    | (current, value) :: rest =>
      if current < expected then persistentRegionData rest address size output
      else if current = expected then persistentRegionData rest address size (output.push value)
      else persistentRegionData ((current, value) :: rest) address size (output.push 0)
termination_by cells.length + (size - output.size)
decreasing_by
  all_goals simp only [List.length_cons, Array.size_push]
  all_goals omega

/-- `persistentRegionData` in bytes, without the array that holds a boxed value for each of them. -/
private def regionBytesFast (cells : List (Nat × UInt8)) (address size : Nat) (output : ByteArray) : ByteArray :=
  if _h : output.size ≥ size then output else
    let expected := address + output.size
    match cells with
    | [] => output ++ zeroBytes (size - output.size)
    | (current, value) :: rest =>
      if current < expected then regionBytesFast rest address size output
      else if current = expected then regionBytesFast rest address size (output.push value)
      else regionBytesFast ((current, value) :: rest) address size (output.push 0)
termination_by cells.length + (size - output.size)
decreasing_by
  all_goals simp only [List.length_cons, ByteArray.size_push]
  all_goals omega

private theorem regionBytesFast_data (cells : List (Nat × UInt8)) (address size : Nat) (output : ByteArray) :
    (regionBytesFast cells address size output).data = persistentRegionData cells address size output.data := by
  induction cells, output using regionBytesFast.induct address size with
  | case1 cells output h =>
    rw [regionBytesFast, persistentRegionData]
    simp [h]
  | case2 output h =>
    rw [regionBytesFast, persistentRegionData]
    have h' : ¬ output.data.size ≥ size := h
    simp only [h, h', ↓reduceDIte, ByteArray.data_append]
    rfl
  | case3 output h expected current value rest hless ih =>
    rw [regionBytesFast, persistentRegionData]
    have h' : ¬ output.data.size ≥ size := h
    have hl : current < address + output.size := hless
    have hl' : current < address + output.data.size := hless
    simp only [h, h', ↓reduceDIte, hl, hl', ↓reduceIte, ih]
  | case4 output h expected value rest hless ih =>
    rw [regionBytesFast, persistentRegionData]
    have h' : ¬ output.data.size ≥ size := h
    have hl : ¬ expected < address + output.size := hless
    have hl' : ¬ expected < address + output.data.size := hless
    have he : expected = address + output.size := rfl
    have he' : expected = address + output.data.size := rfl
    simp only [h, h', ↓reduceDIte]
    rw [ite_eq_right hl, ite_eq_left he, ite_eq_right hl', ite_eq_left he', ih]
    rfl
  | case5 output h expected current value rest hless heq ih =>
    rw [regionBytesFast, persistentRegionData]
    have h' : ¬ output.data.size ≥ size := h
    have hl : ¬ current < address + output.size := hless
    have hl' : ¬ current < address + output.data.size := hless
    have he : ¬ current = address + output.size := heq
    have he' : ¬ current = address + output.data.size := heq
    simp only [h, h', ↓reduceDIte, hl, hl', he, he', ↓reduceIte, ih]
    rfl

/-- The bytes of a region of a memory that holds these cells. -/
private def regionBytes (cells : List (Nat × UInt8)) (address size : Nat) : ByteArray :=
  ByteArray.mk (persistentRegionData cells address size #[])

private theorem regionBytes_eq (cells : List (Nat × UInt8)) (address size : Nat) :
    regionBytes cells address size = regionBytesFast cells address size ByteArray.empty :=
  ByteArray.ext (regionBytesFast_data cells address size ByteArray.empty).symm

/-- The fast path of `regionBytes`, which is what the theorems about `persistentRegionData` speak of. -/
private def regionBytesRun (cells : List (Nat × UInt8)) (address size : Nat) : ByteArray :=
  regionBytesFast cells address size ByteArray.empty

@[csimp] private theorem regionBytes_csimp : @regionBytes = @regionBytesRun := by
  funext cells address size
  exact regionBytes_eq cells address size

/-- The space of the first task, whose memory has no entry in `processMemory`. -/
private def firstSpace (table : Tasks.TaskTable) : Nat :=
  match table.tasks.head? with
  | some first => first.space
  | none => 1

/-- The regions with what the memory has in them, which take memory of the host for the pages that it has, and not for those that a program
mapped and hasn't written. -/
private def regionsFromNative (mapped : List Region) (native : Jit.Memory) : IO (List Region) :=
  mapped.mapM fun region => do pure { region with data := ← Jit.regionBytes native (UInt64.ofNat region.address) region.data.size }

/-- The space whose regions a snapshot has as `regions`. -/
def snapshotSpace (saved : Snapshot) : Nat := firstSpace saved.table

/-- All that the emulator is, of every thread and address space, as plain data: what `restore` and a checkpoint take. -/
def snapshot (emu : Emu) : IO Snapshot := do
  let processes ← emu.processMemory.get
  let table ← emu.taskTable.get
  let mapped ← emu.regions.get
  let parked ← emu.parkedRegions.get
  let space := table.spaceOf (← emu.currentThreadRef.get)
  let mapOf (id : Nat) : List Region := if id == space then mapped else parked.getD id mapped
  -- In order of id, as what a table gives depends on what was done to it.
  let processMemory ← (processes.toList.mergeSort fun left right => left.1 ≤ right.1).mapM fun (id, memory) => do
    let regions ← regionsFromNative (mapOf id) memory
    pure (id, regions)
  pure {
    state := ← emu.state.get
    pc := ← emu.pc.get
    regions := mapOf (firstSpace table)
    stopped := ← emu.stopped.get
    threads := ← captureThreads emu
    currentThread := ← emu.currentThreadRef.get
    nextThread := ← emu.nextThreadRef.get
    pending := ← emu.pendingRef.get
    processMemory
    skip := ← emu.skipCode.get
    table := ← emu.taskTable.get
  }

private def snapshotBlock (emu : Emu) : IO Snapshot := do
  pure {
    state := ← emu.state.get
    pc := ← emu.pc.get
    regions := ← emu.regions.get
    stopped := ← emu.stopped.get
    threads := ← emu.threadsRef.get
    currentThread := ← emu.currentThreadRef.get
    nextThread := ← emu.nextThreadRef.get
    pending := ← emu.pendingRef.get
    skip := ← emu.skipCode.get
    table := ← emu.taskTable.get
  }

/-- Lets go of the filter of the native memory, which no run uses from now on, until it is made again of what is so then. -/
private def forgetMemoryFilter (emu : Emu) : IO Unit := do
  emu.memoryFilterStale.set true
  emu.engine.memoryFilter.set none
  -- What the chain goes on to was compiled of bytes that a change of where the regions are, or of what may be done there, may have
  -- let change unseen.
  Primus.Lifted.clearChain emu.engine

/-- Makes the filter of the native memory again if it is stale: what the memory observer, `notifyMemory`, lets through doing nothing,
of the regions, the hooks of accesses, the trace and the journal, as obligation 16 of `Bap.Jit` asks. -/
private def ensureMemoryFilter (emu : Emu) : IO Unit := do
  if !(← emu.memoryFilterStale.get) then return
  emu.memoryFilterStale.set false
  let traced := (← emu.trace.get).active
  let readsHeard := traced || !(← emu.readHooks.get).isEmpty
  let writesHeard := traced || !(← emu.writeHooks.get).isEmpty || emu.journal.isSome
  emu.memoryFilterHeard.set (readsHeard, writesHeard)
  match quietRanges (← emu.regions.get) readsHeard writesHeard with
  | some ranges =>
    let filter ← Jit.createMemoryFilter (ranges.map (UInt64.ofNat ·.1)) (ranges.map (UInt64.ofNat ·.2.1)) (ranges.map (·.2.2))
    emu.engine.memoryFilter.set (some filter)
  | none => emu.engine.memoryFilter.set none

/-- What the filter of the native memory has of a region. -/
private def regionShape (region : Region) : Nat × Nat × Primus.Protection := (region.address, region.data.size, region.protection)

/-- Changes what is mapped. Only where the regions are and their protection are of the filter of the native memory, which most changes,
of the bytes that the regions hold, keep. -/
def setRegions (emu : Emu) (regions : List Region) : IO Unit := do
  if (← emu.regions.get).map regionShape != regions.map regionShape then forgetMemoryFilter emu
  emu.regions.set regions
  emu.fetchPages.set {}
  emu.regionIndex.set none
  emu.mappingTop.set none

/-- The regions by where they start. -/
def regionTree (emu : Emu) : IO (Std.TreeMap Nat Region) := do
  match ← emu.regionIndex.get with
  | some tree => pure tree
  | none =>
    let tree := (← emu.regions.get).foldl (init := ({} : Std.TreeMap Nat Region)) fun tree region =>
      if region.data.size == 0 then tree else tree.insert region.address region
    emu.regionIndex.set (some tree)
    pure tree

/-- The regions that bytes in a row are in, which is all that has to do with an access to them. -/
def regionsTouching (emu : Emu) (address size : Nat) : IO (List Region) := do
  let tree ← regionTree emu
  let upper := address + max size 1
  let first := match tree.getEntryLE? address with
    | some (_, region) => if region.address + region.data.size > address then [region] else []
    | none => []
  let rec later : Nat → Nat → List Region → List Region
    | 0, _, out => out
    | fuel + 1, from_, out =>
      match tree.getEntryGT? from_ with
      | some (start, region) => if start < upper then later fuel start (region :: out) else out
      | none => out
  pure (later tree.size address first)

/-- All the regions but those in a range are as they were, and those have been replaced by these. -/
private def replaceRegions (emu : Emu) (regions : List Region) (touched replaced : List Region) : IO Unit := do
  Primus.Lifted.clearChain emu.engine
  -- The filter changes where the regions did, as the index does, rather than being made again of all of them.
  match ← emu.engine.memoryFilter.get, ← emu.memoryFilterStale.get with
  | some filter, false =>
    let (readsHeard, writesHeard) ← emu.memoryFilterHeard.get
    let removed := ((touched.filter (0 < ·.data.size)).map (UInt64.ofNat ·.address)).toArray
    let added := (replaced.filter (0 < ·.data.size)).toArray
    let apart ← Jit.updateMemoryFilter filter removed (added.map (UInt64.ofNat ·.address))
      (added.map fun region => UInt64.ofNat (region.address + region.data.size - 1))
      (added.map (quietBits ·.protection readsHeard writesHeard))
    if !apart then forgetMemoryFilter emu
  | _, _ => forgetMemoryFilter emu
  emu.regions.set regions
  emu.fetchPages.set {}
  emu.regionIndex.modify (·.map fun tree =>
    let tree := touched.foldl (fun tree region => tree.erase region.address) tree
    replaced.foldl (fun tree region => if region.data.size == 0 then tree else tree.insert region.address region) tree)

private def restoreThreads (emu : Emu) (snapshot : Snapshot) : IO Unit := do
  emu.state.set snapshot.state
  emu.pc.set snapshot.pc
  setRegions emu snapshot.regions
  emu.stopped.set snapshot.stopped
  emu.threadsRef.set snapshot.threads
  emu.currentThreadRef.set snapshot.currentThread
  emu.nextThreadRef.set snapshot.nextThread
  emu.pendingRef.set snapshot.pending
  emu.skipCode.set snapshot.skip
  emu.taskTable.set snapshot.table

/-- A native memory with the bytes of the memory variable of `state`. -/
private def nativeFromState (emu : Emu) (state : Bil.State) : IO Jit.Memory := do
  match Bil.lookup state.env emu.config.memory with
  | .ok (.memory memory) => Primus.Lifted.nativeOfMemory memory
  | .ok _ => throw <| IO.userError "Emu memory is not a memory value"
  | .error error => throw <| IO.userError error

/-- Makes `native` the memory of the thread that runs. -/
private def attachMemory (emu : Emu) (native : Jit.Memory) : IO Unit := do
  emu.memorySwitched.set true
  emu.engine.persistentMemory.set (some native)
  emu.engine.persistentVariable.set (some emu.config.memory)

/-- A step begins: what it writes to the native memory is remembered, to take back if it fails. A worker of a parallel round leaves
that to the rollback of its round. -/
private def beginStepMemory (emu : Emu) : IO Unit := do
  if emu.engine.deferMemorySync then return
  emu.memorySwitched.set false
  match ← emu.engine.persistentMemory.get, ← emu.engine.persistentVariable.get with
  | some native, some var =>
    if var == emu.config.memory then
      Jit.beginMemoryStep native
      emu.stepNative.set (some native)
    else emu.stepNative.set none
  | _, _ => emu.stepNative.set none

/-- Takes back what a failed step wrote to the native memory that it began with, from the memory of the state, which is exact: a
memory that a process has made of all its bytes takes as long as they do, and this as long as what was written. Whether it could. -/
private def undoStepMemory (emu : Emu) (live : Option Jit.Memory) (snapshot : Snapshot) : IO Bool := do
  if ← emu.memorySwitched.get then return false
  -- The step may be what made the memory, of what the state had when it started, and that keeps a log from then on.
  let some native := (← emu.stepNative.get) <|> live | return false
  let some written ← Jit.memoryStepWrites native | return false
  match Bil.lookup snapshot.state.env emu.config.memory with
  | .ok (@Value.memory width memory) =>
    Jit.writeMemory native written (written.map fun address => Bap.Memory.readByte memory (BitVec.ofNat width address.toNat))
    emu.rollbacks.modify fun stats => { stats with bytesRestored := stats.bytesRestored + written.size }
    let space := snapshot.table.spaceOf snapshot.currentThread
    if (← emu.processMemory.get).contains space then emu.processMemory.modify (·.insert space native)
    attachMemory emu native
    return true
  | _ => return false

/-- Undo a failed step. The memory of the state is exact, and a failed block may have written to the
native memory, which is made to agree with the state. Threads created since the step started are gone again, and so
is their memory. A parallel worker leaves all of this to the rollback of its round. -/
private def rollbackBlock (emu : Emu) (snapshot : Snapshot) : IO Unit := do
  let restarting ← emu.restarting.get
  -- What is in `lastFault` may be of an earlier step, which isn't why this one failed.
  let faulted ← emu.faultFresh.get
  emu.faultFresh.set false
  emu.rollbacks.modify fun stats =>
    if restarting then { stats with restarts := stats.restarts + 1 }
    else if faulted then { stats with faults := stats.faults + 1 }
    else { stats with others := stats.others + 1 }
  let created ← emu.nextThreadRef.get
  let live ← match ← emu.engine.persistentVariable.get with
    | some var => if var == emu.config.memory then emu.engine.persistentMemory.get else pure none
    | none => pure none
  restoreThreads emu snapshot
  Primus.Lifted.discardMemory emu.engine
  if !emu.engine.deferMemorySync then
    if created != snapshot.nextThread then
      emu.processMemory.modify fun processes => processes.filter fun id _ => id < snapshot.nextThread
      emu.parkedRegions.modify fun parked => parked.filter fun id _ => id < snapshot.nextThread
    if ← undoStepMemory emu live snapshot then
      emu.rollbacks.modify fun stats => { stats with patched := stats.patched + 1 }
    else
      let space := snapshot.table.spaceOf snapshot.currentThread
      if (← emu.processMemory.get).contains space then
        let native ← nativeFromState emu snapshot.state
        emu.processMemory.modify (·.insert space native)
        attachMemory emu native
        emu.rollbacks.modify fun stats => { stats with rebuilt := stats.rebuilt + 1 }

/-- How steps have been taken back so far. -/
def rollbackStats (emu : Emu) : IO RollbackStats := emu.rollbacks.get

/-- What a thread of a snapshot waits for, as it would go on from it: nothing, whoever runs it to let it go on, a futex, a child, or
nothing any more, as it has exited. -/
inductive ThreadWait where
  | runs
  | stopped
  | futex (address : Nat) (timed : Bool)
  | child (target : Option Nat)
  | exited (status : Nat)
  deriving DecidableEq, Repr

/-- A thread of a snapshot: where it goes on and what it waits for. -/
structure ThreadSummary where
  id : Nat
  pc : Nat
  wait : ThreadWait
  deriving DecidableEq, Repr

/-- Each thread of a snapshot, by id, with where it goes on and what it waits for. -/
def Snapshot.threadSummaries (snapshot : Snapshot) : List ThreadSummary :=
  let contexts := if snapshot.threads.any (·.id == snapshot.currentThread) then snapshot.threads.map fun context => (context.id, context.pc, context.stopped)
    else (snapshot.currentThread, snapshot.pc, snapshot.stopped) :: snapshot.threads.map fun context => (context.id, context.pc, context.stopped)
  let table := snapshot.table
  let summaries := contexts.map fun (id, pc, stopped) =>
    let wait : ThreadWait :=
      match (table.tasks.find? (·.tid == id)).bind (·.status) with
      | some status => .exited status
      | none =>
        match table.futexes.find? (·.thread == id) with
        | some waiter => .futex waiter.address waiter.timed
        | none =>
          match table.waiters.find? (·.thread == id) with
          | some waiter => .child waiter.target
          | none => if stopped then .stopped else .runs
    { id, pc, wait : ThreadSummary }
  summaries.mergeSort fun left right => left.id ≤ right.id

/-- Why no thread of a snapshot can go on, if none can: every pc is 0 and nothing is mapped there, as of a snapshot that is zeros. -/
def Snapshot.unrunnable (snapshot : Snapshot) : Option String :=
  let mapsZero := (snapshot.regions :: snapshot.processMemory.map (·.2)).any fun regions =>
    regions.any fun region => region.address == 0 && region.data.size > 0
  if (snapshot.pc :: snapshot.threads.map (·.pc)).all (· == 0) && !mapsZero then
    some "a snapshot whose every thread is at 0, where nothing is mapped, so that none can go on"
  else none

/-- Puts the emulator back to a snapshot, with the memory of each address space. What was compiled stays, but for ranges, which are
compiled again as they get hot. A snapshot that no thread can go on from is refused, and the emulator stays as it was. -/
def restore (emu : Emu) (snapshot : Snapshot) : IO Unit := do
  if let some problem := snapshot.unrunnable then throw <| IO.userError problem
  restoreThreads emu snapshot
  -- What is there already fired before the stop that this was saved at; what comes after it hasn't. A step that is rolled back keeps
  -- what other threads have of it, which a step of one thread has nothing to do with.
  emu.suppressed.set []
  emu.memorySwitched.set true
  -- A compiled range holds the code of all of its blocks. A version of it stays, for when those come back.
  Primus.Lifted.forgetRanges emu.engine
  emu.parallelWorkers.set []
  emu.processMemory.set {}
  emu.sharedMemory.set none
  emu.parkedRegions.set {}
  -- The regions of a snapshot are those of the first space, and the others come with their memory.
  let space := snapshot.table.spaceOf snapshot.currentThread
  if let some mapped := snapshot.processMemory.lookup space then
    emu.parkedRegions.modify (·.insert (firstSpace snapshot.table) snapshot.regions)
    setRegions emu mapped
  snapshot.processMemory.forM fun (id, regions) => do
    if id != space then emu.parkedRegions.modify (·.insert id regions)
    let memory ← Jit.createMemoryChunks (regions.map fun region => UInt64.ofNat region.address).toArray (regions.map (·.data)).toArray
    emu.processMemory.modify (·.insert id memory)
  Primus.Lifted.discardMemory emu.engine
  match (← emu.processMemory.get).get? (snapshot.table.spaceOf snapshot.currentThread) with
  | some native => attachMemory emu native
  | none => pure ()

/-- The thread that runs. -/
def thread (emu : Emu) : IO ThreadId := emu.currentThreadRef.get

/-- All threads, by id. -/
def threads (emu : Emu) : IO (List ThreadInfo) := do
  let contexts ← captureThreads emu
  pure ((contexts.map fun context => ⟨context.id, context.pc, context.stopped⟩).mergeSort
    (fun left right => left.id ≤ right.id))

/-- Gives the engine the native memory of thread `next`, when it is not the one of `current`. -/
private def switchNativeMemory (emu : Emu) (current next : ThreadId) : IO Unit := do
  let currentSpace ← spaceOf emu current
  let nextSpace ← spaceOf emu next
  if currentSpace != nextSpace then
    -- What was compiled of ranges goes by the bytes of their first block only, and another space may have others after it: they are
    -- versions, then, which are taken again only where all that they were made of is as it was.
    Primus.Lifted.forgetRanges emu.engine
    let mapped ← emu.regions.get
    let parked ← emu.parkedRegions.get
    setRegions emu (parked.getD nextSpace mapped)
    emu.parkedRegions.set (parked.insert currentSpace mapped)
    let processes ← emu.processMemory.get
    let native ← emu.engine.persistentMemory.get
    match native with
    | some native =>
      if processes.contains currentSpace then emu.processMemory.modify (·.insert currentSpace native)
      else emu.sharedMemory.set (some native)
    | none => pure ()
    let processes ← emu.processMemory.get
    match nativeFor processes (← emu.sharedMemory.get) nextSpace with
    | some native => attachMemory emu native
    | none =>
      emu.memorySwitched.set true
      Primus.Lifted.discardMemory emu.engine

/-- The exclusive monitor of a thread, of targets that have it in their semantics: see `semantics/arm/aarch64-atomic.lisp` and
`semantics/riscv/riscv.lisp`. -/
def exclusiveMonitor (width : Nat) : Bap.Var := ⟨"EXCLUSIVE_MONITOR", .imm width, 0, false⟩

/-- A state without a monitor, for a target that has one. -/
private def clearMonitor (config : Config) (env : Bil.Env) : Bil.Env :=
  match config.syscallAbi, memoryWidth config with
  | .aarch64, .ok width | .riscv, .ok width | .mips, .ok width | .powerpc, .ok width | .powerpc64, .ok width | .arm, .ok width => Bil.bind env (exclusiveMonitor width) (.bits (BitVec.ofNat width 0))
  | _, _ => env

/-- Makes another thread the one that runs, with the memory of its address space. -/
def switchThread (emu : Emu) (id : ThreadId) : IO Unit := do
  emu.turnUsed.set 0
  saveCurrentThread emu
  let table ← emu.taskTable.get
  let leaving ← thread emu
  let leavingSpace := table.spaceOf leaving
  if table.spaceOf id != leavingSpace then
    if let some leave := ← emu.leavingSpace.get then leave
    match Bil.lookup (← emu.state.get).env emu.config.memory with
    | .ok memory =>
      emu.threadsRef.modify (parkShared · (fun other => table.spaceOf other != leavingSpace) emu.config.memory memory)
    | .error _ => pure ()
  let contexts ← emu.threadsRef.get
  match contexts.find? fun context => context.id == id with
  | none => throw <| IO.userError s!"unknown Emu thread {id}"
  | some context =>
    let current ← emu.state.get
    let env := if table.spaceOf id != leavingSpace then context.state.env else
      match Bil.lookup current.env emu.config.memory with
      | .ok memory => Bil.bind context.state.env emu.config.memory memory
      | .error _ => context.state.env
    switchNativeMemory emu leaving id
    -- As a kernel does when it switches: what a thread loaded exclusively may have changed, so its exclusive store has to fail.
    emu.state.set { env := clearMonitor emu.config env }
    emu.pc.set context.pc
    emu.stopped.set context.stopped
    emu.currentThreadRef.set id
    emu.pendingRef.set context.pending
    emu.skipCode.set context.skip
    if table.spaceOf id != leavingSpace then
      if let some entered := ← emu.enteredSpace.get then entered
    if let some arrived := ← emu.switchedIn.get then arrived

def resumeThread (emu : Emu) (id : ThreadId) : IO Unit := do
  emu.threadControl.modify (·.insert id false)
  emu.threadsRef.modify (setThreadStopped · id false)
  if (← thread emu) == id then
    emu.stopped.set false

/-- Stops a thread until `resumeThread`. -/
def stopThread (emu : Emu) (id : ThreadId) : IO Unit := do
  emu.threadControl.modify (·.insert id true)
  if (← thread emu) == id then
    emu.stopped.set true
  else
    emu.threadsRef.modify (setThreadStopped · id true)

private def hookContext (emu : Emu) : CodeHookContext := {
  engine := emu.engine
  state := emu.state
  pc := emu.pc
  stopped := emu.stopped
  currentThreadRef := emu.currentThreadRef
  trace := emu.trace
  lastFault := emu.lastFault
  skipCode := emu.skipCode
  pendingRef := emu.pendingRef
}

private unsafe def sameObjectImpl {α : Type} (left right : α) : Bool := ptrAddrUnsafe left == ptrAddrUnsafe right

/-- Whether two things are one object, as a hook's context and the emulator's own references are, or a state that a hook left as it was given. It may say no when they are only equal. -/
@[implemented_by sameObjectImpl] private def sameObject {α : Type} (_ _ : α) : Bool := false

/-- The emulator a hook sees: its registers, memory and thread are of the thread that runs it. It is the emulator itself where the
context is of its own references, as it is but in a worker of a parallel round, rather than a copy of it. -/
private def withContext (emu : Emu) (context : CodeHookContext) : Emu :=
  if sameObject context.engine emu.engine && sameObject context.state emu.state && sameObject context.pc emu.pc &&
      sameObject context.stopped emu.stopped && sameObject context.currentThreadRef emu.currentThreadRef &&
      sameObject context.trace emu.trace && sameObject context.lastFault emu.lastFault && sameObject context.skipCode emu.skipCode &&
      sameObject context.pendingRef emu.pendingRef then emu
  else {
  emu with
    engine := context.engine
    state := context.state
    pc := context.pc
    stopped := context.stopped
    currentThreadRef := context.currentThreadRef
    trace := context.trace
    lastFault := context.lastFault
    skipCode := context.skipCode
    pendingRef := context.pendingRef
}

private def nextHookId (emu : Emu) : IO HookId := do
  let id ← emu.nextHook.get
  emu.nextHook.set (id + 1)
  pure id

/-- The hooks that cover an address, in the order they came, found among those of its page once and then kept for it. -/
private def hooksNear (emu : Emu) (address : Nat) : IO (List CodeHook) := do
  if let some here := (← emu.hooksExact.get)[address]? then return here
  let page := address / 4096
  let hooks ← match (← emu.hooksByPage.get)[page]? with
    | some hooks => pure hooks
    | none =>
      let hooks := hooksOnPage (·.first) (·.last) (← emu.hooks.get) page
      emu.hooksByPage.modify (·.insert page hooks)
      pure hooks
  let here := hooks.filter fun hook => hook.first ≤ address && address ≤ hook.last
  emu.hooksExact.modify (·.insert address here)
  pure here

/-- Calls `action emu address` before each instruction of the range. A thread that has stopped in it, where the hooks that were there
fired, has this one fire when it goes on, and not those, unless `late` is false, as for a breakpoint, which stops it when it comes back. -/
def onCode (emu : Emu) (range : Nat × Nat) (action : Emu → Nat → IO Unit) (late : Bool := true) : IO HookId := do
  if range.1 > range.2 then
    throw <| IO.userError "invalid Emu code-hook range"
  let id ← nextHookId emu
  let before ← emu.hooks.get
  emu.hooks.modify (· ++ [⟨id, range.1, range.2, fun context => action (withContext emu context)⟩])
  -- What is optimized from now on leaves its slots at the sites that hooks read the state at.
  -- It is asked at each checkpoint of each block that is optimized, so it looks at the hooks of the page of `pc` rather than at all of them.
  emu.engine.codeHooked.set fun pc => do pure ((← hooksNear emu pc).any fun hook => hook.first ≤ pc && pc ≤ hook.last)
  emu.hooksByPage.set {}
  emu.hooksExact.set {}
  emu.hookChanges.modify (· + 1)
  let inside (address : Nat) : Bool := range.1 ≤ address && address ≤ range.2
  if !late then
    emu.suppressed.modify (·.map fun (thread, address, ids) => (thread, address, if inside address then id :: ids else ids))
    return id
  -- What fired at an address before a thread stopped there.
  let fired (address : Nat) : List HookId := (before.filter fun hook => hook.first ≤ address && address ≤ hook.last).map (·.id)
  let current ← emu.currentThreadRef.get
  if let some address := ← emu.skipCode.get then
    if inside address then
      emu.skipCode.set none
      emu.suppressed.modify ((current, address, fired address) :: ·)
  let threads ← emu.threadsRef.get
  for context in threads do
    if let some address := context.skip then
      if context.id != current && inside address then
        emu.suppressed.modify ((context.id, address, fired address) :: ·)
  emu.threadsRef.set (threads.map fun context =>
    match context.skip with
    | some address => if context.id != current && inside address then { context with skip := none } else context
    | none => context)
  pure id

/-- Calls `action emu address size` before each load of the range. -/
def onRead (emu : Emu) (range : Nat × Nat) (action : Emu → Nat → Nat → IO Unit) : IO HookId := do
  if range.1 > range.2 then
    throw <| IO.userError "invalid Emu read-hook range"
  let id ← nextHookId emu
  forgetMemoryFilter emu
  emu.readHooks.modify (· ++ [⟨id, range.1, range.2, fun context => action (withContext emu context)⟩])
  -- What a run that goes on has of the filter of the native memory is of the hooks that there were.
  emu.hookChanges.modify (· + 1)
  pure id

/-- Calls `action emu address size value` before each store of the range. -/
def onWrite (emu : Emu) (range : Nat × Nat) (action : Emu → Nat → Nat → Nat → IO Unit) : IO HookId := do
  if range.1 > range.2 then
    throw <| IO.userError "invalid Emu write-hook range"
  let id ← nextHookId emu
  forgetMemoryFilter emu
  emu.writeHooks.modify (· ++ [⟨id, range.1, range.2, fun context => action (withContext emu context)⟩])
  emu.hookChanges.modify (· + 1)
  pure id

/-- Calls `action emu number arguments` at each system call. -/
def onSyscall (emu : Emu) (action : Emu → Nat → List Nat → IO SyscallAction) : IO HookId := do
  let id ← nextHookId emu
  emu.syscallHooks.modify (· ++ [⟨id, fun context => action (withContext emu context)⟩])
  pure id

/-- Calls `action emu address` at each intrinsic with this name, or at all of them with `"*"`. -/
def onIntrinsic (emu : Emu) (name : String) (action : Emu → Nat → IO IntrinsicAction) : IO HookId := do
  if name.isEmpty then
    throw <| IO.userError "intrinsic hook name is empty"
  let id ← nextHookId emu
  emu.intrinsicHooks.modify (· ++ [⟨id, name, fun context => action (withContext emu context)⟩])
  pure id

/-- Takes a hook off, of whatever kind. -/
def removeHook (emu : Emu) (id : HookId) : IO Unit := do
  emu.hooks.modify fun hooks => hooks.filter fun hook => hook.id != id
  emu.hooksByPage.set {}
  emu.hooksExact.set {}
  emu.hookChanges.modify (· + 1)
  forgetMemoryFilter emu
  emu.readHooks.modify fun hooks => hooks.filter fun hook => hook.id != id
  emu.writeHooks.modify fun hooks => hooks.filter fun hook => hook.id != id
  emu.watchedSteps.set {}
  emu.syscallHooks.modify fun hooks => hooks.filter fun hook => hook.id != id
  emu.intrinsicHooks.modify fun hooks => hooks.filter fun hook => hook.id != id
  emu.breakpointsRef.modify fun breakpoints => breakpoints.filter fun breakpoint => breakpoint.1 != id

/-- Takes every hook off. -/
def clearHooks (emu : Emu) : IO Unit := do
  emu.hooks.set []
  emu.hooksByPage.set {}
  emu.hooksExact.set {}
  emu.hookChanges.modify (· + 1)
  forgetMemoryFilter emu
  emu.readHooks.set []
  emu.writeHooks.set []
  emu.watchedSteps.set {}
  emu.syscallHooks.set []
  emu.intrinsicHooks.set []
  emu.breakpointsRef.set []

/-- Stops the thread that comes to `address`, before it runs it. Going on from there doesn't stop it there again. -/
def addBreakpoint (emu : Emu) (address : Nat) : IO HookId := do
  -- A thread that stopped here has stopped here: it goes on, and a breakpoint stops it when it comes back.
  let id ← onCode emu (address, address) (late := false) fun current _ => do
    unless ← emu.breakpointsMuted.get do current.stopped.set true
  emu.breakpointsRef.modify fun breakpoints => (id, address) :: breakpoints
  pure id

/-- Takes the breakpoints at an address off. -/
def removeBreakpoint (emu : Emu) (address : Nat) : IO Unit := do
  let breakpoints ← emu.breakpointsRef.get
  (breakpoints.filter fun breakpoint => breakpoint.2 == address).forM fun breakpoint =>
    removeHook emu breakpoint.1

/-- Where there are breakpoints. -/
def breakpoints (emu : Emu) : IO (List Nat) := do
  let current ← emu.breakpointsRef.get
  pure (current.map Prod.snd).reverse

/-- A trace that has nothing yet, which keeps what `options` say. -/
private def freshTrace (options : TraceOptions) : IO TraceState := do
  for range in options.watch.toList ++ options.watches do
    if range.1 > range.2 then throw <| IO.userError "invalid Emu trace watch range"
  pure { options, ring := { capacity := options.pcCapacity }, watched := options.watches.toArray.map ({ range := · }) }

/-- Starts the default trace afresh, which keeps what `options` say. -/
def traceStartWith (emu : Emu) (options : TraceOptions) : IO Unit := do
  let state ← freshTrace options
  forgetMemoryFilter emu
  emu.trace.modify ({ · with default := some state })

/-- Starts keeping each pc that runs, all of them. -/
def traceStart (emu : Emu) : IO Unit := traceStartWith emu {}

/-- Starts keeping the last `capacity` pcs that run. -/
def traceStartCapacity (emu : Emu) (capacity : Nat) : IO Unit := traceStartWith emu { pcCapacity := capacity }

/-- Starts keeping the pcs and the last `capacity` accesses to memory. -/
def traceStartAccesses (emu : Emu) (capacity : Nat) : IO Unit := traceStartWith emu { accessCapacity := capacity }

/-- Starts keeping the last `capacity` accesses to a range, and the pcs. -/
def traceStartWatch (emu : Emu) (range : Nat × Nat) (capacity : Nat) : IO Unit :=
  traceStartWith emu { accessCapacity := capacity, watch := some range }

private def TraceRing.pcs (ring : TraceRing) : List Nat :=
  ring.front ++ ring.back.reverse

/-- The rings of a trace by thread, in order of thread. -/
private def TraceState.threadRings (state : TraceState) : List (ThreadId × TraceRing) :=
  (state.rings.toArray.qsort fun left right => left.1 < right.1).toList

/-- The pcs of a trace: of a ring for each thread, those of each thread in order of thread. -/
private def pcList (state : TraceState) : List Nat :=
  if state.options.perThread then state.threadRings.flatMap (·.2.pcs) else state.ring.pcs

/-- Each pc that a ring kept, with the bytes that it ran as: the last that were new at it by then. -/
private def TraceRing.instructions (ring : TraceRing) : List (Nat × ByteArray) := Id.run do
  let pcs := ring.pcs
  let versions := ring.code.reverse.toArray
  let mut current : Std.HashMap Nat ByteArray := {}
  let mut next := 0
  let mut out : Array (Nat × ByteArray) := Array.mkEmpty pcs.length
  for (pc, index) in pcs.zipIdx (ring.count - pcs.length) do
    while h : next < versions.size do
      let (at_, where_, bytes) := versions[next]
      if at_ > index then break
      current := current.insert where_ bytes
      next := next + 1
    out := out.push (pc, current.getD pc ByteArray.empty)
  pure out.toList

/-- Stops the default trace, and gives the pcs that it kept. -/
def traceStop (emu : Emu) : IO (List Nat) := do
  let current ← emu.trace.get
  forgetMemoryFilter emu
  emu.trace.set { current with default := none }
  pure (pcList (current.default.getD {}))

/-- A trace that a session opened, which only that session stops or starts again: its name, and what says that it is the one that
opened it. -/
structure TraceSession where
  name : String
  token : Nat
  deriving DecidableEq, Repr

/-- Opens a trace of a name of its own, which keeps what `options` say, for whoever is given the session. A name that is open already is
someone else's, and the empty name is that of the default trace. -/
def traceOpen (emu : Emu) (name : String) (options : TraceOptions := {}) : IO TraceSession := do
  if name.isEmpty then throw <| IO.userError "a trace of a session has a name, and the empty name is the default trace's"
  let state ← freshTrace options
  let set ← emu.trace.get
  if set.named.any (·.1 == name) then
    throw <| IO.userError s!"the trace {name} is open already, and is the session's that opened it"
  forgetMemoryFilter emu
  emu.trace.set { set with named := set.named ++ [(name, set.nextToken, state)], nextToken := set.nextToken + 1 }
  pure { name, token := set.nextToken }

/-- The trace of a session, which has to be the one that opened it. -/
private def ownedTrace (emu : Emu) (session : TraceSession) : IO TraceSet := do
  let set ← emu.trace.get
  match set.named.find? (·.1 == session.name) with
  | some (_, token, _) =>
    if token != session.token then throw <| IO.userError s!"the trace {session.name} is another session's"
    pure set
  | none => throw <| IO.userError s!"there is no trace {session.name} open"

/-- Closes a session's trace, and gives the pcs that it kept. -/
def traceClose (emu : Emu) (session : TraceSession) : IO (List Nat) := do
  let set ← ownedTrace emu session
  forgetMemoryFilter emu
  emu.trace.set { set with named := set.named.filter (·.1 != session.name) }
  pure (pcList ((set.find? session.name).getD {}))

/-- Starts a session's trace afresh, with what it keeps, or with `options` if they are given. -/
def traceRestart (emu : Emu) (session : TraceSession) (options : Option TraceOptions := none) : IO Unit := do
  let set ← ownedTrace emu session
  let state ← freshTrace (options.getD ((set.find? session.name).getD {}).options)
  forgetMemoryFilter emu
  emu.trace.set { set with named := set.named.map fun (name, token, current) =>
    if name == session.name then (name, token, state) else (name, token, current) }

/-- Runs `action` with a trace of its own, of a name, which is closed when it is done, however it ends. -/
def withTrace (emu : Emu) (name : String) (options : TraceOptions) (action : TraceSession → IO α) : IO α := do
  let session ← traceOpen emu name options
  try action session finally
    try let _ ← traceClose emu session catch _ => pure ()

/-- The names of the traces that sessions have open, in the order they were opened. -/
def traceNames (emu : Emu) : IO (List String) := do
  pure ((← emu.trace.get).named.map (·.1))

/-- A trace by its name, the default one of the empty name, or one with nothing if there is none. -/
private def traceState (emu : Emu) (trace : String) : IO TraceState := do
  pure (((← emu.trace.get).find? trace).getD {})

/-- The pcs that a trace kept so far, of the default trace unless a name is given. -/
def tracePcs (emu : Emu) (trace : String := "") : IO (List Nat) := do
  pure (pcList (← traceState emu trace))

/-- Each pc that the trace kept so far, with the bytes of the instruction that ran there then, which may not be what is there now. Empty
bytes are of an instruction that couldn't be fetched and decoded. -/
def traceInstructions (emu : Emu) (trace : String := "") : IO (List (Nat × ByteArray)) := do
  let state ← traceState emu trace
  pure (if state.options.perThread then state.threadRings.flatMap (·.2.instructions) else state.ring.instructions)

/-- How many pcs the trace let go of for its capacity, of all threads. -/
def traceDroppedPcs (emu : Emu) (trace : String := "") : IO Nat := do
  let state ← traceState emu trace
  pure (if state.options.perThread then state.threadRings.foldl (· + ·.2.dropped) 0 else state.ring.dropped)

/-- The ring of a thread, of a trace with one for each. -/
private def threadRing (emu : Emu) (thread : ThreadId) (trace : String) : IO TraceRing := do
  let state ← traceState emu trace
  if !state.options.perThread then throw <| IO.userError "the trace has no ring of each thread: start it with perThread"
  pure (state.rings.getD thread {})

/-- The pcs that a thread ran, in order, of what its ring kept. -/
def traceThreadPcs (emu : Emu) (thread : ThreadId) (trace : String := "") : IO (List Nat) := do
  pure (← threadRing emu thread trace).pcs

/-- Each pc that a thread ran, of what its ring kept, with the bytes that it ran as. -/
def traceThreadInstructions (emu : Emu) (thread : ThreadId) (trace : String := "") : IO (List (Nat × ByteArray)) := do
  pure (← threadRing emu thread trace).instructions

/-- How many pcs a thread's ring let go of for its capacity. -/
def traceThreadDroppedPcs (emu : Emu) (thread : ThreadId) (trace : String := "") : IO Nat := do
  pure (← threadRing emu thread trace).dropped

/-- What the trace says of each thread that it has a ring of, in order of thread: of a trace of one ring, nothing. -/
def traceThreads (emu : Emu) (trace : String := "") : IO (List TraceThread) := do
  let state ← traceState emu trace
  pure (state.threadRings.map fun (thread, ring) =>
    { thread, count := ring.count, kept := ring.count - ring.dropped, dropped := ring.dropped })

/-- What the trace keeps. -/
def traceOptions (emu : Emu) (trace : String := "") : IO (Option TraceOptions) := do
  pure (((← emu.trace.get).find? trace).map (·.options))

/-- The accesses that the trace kept. -/
def traceAccesses (emu : Emu) (trace : String := "") : IO (List TraceAccess) := do
  let state ← traceState emu trace
  pure (state.accesses.take state.options.accessCapacity).reverse

/-- How many accesses the trace saw, kept or not. -/
def traceAccessesCount (emu : Emu) (trace : String := "") : IO Nat := do
  pure (← traceState emu trace).accessCount

/-- How many accesses the trace let go of for its capacity. -/
def traceDroppedAccesses (emu : Emu) (trace : String := "") : IO Nat := do
  let state ← traceState emu trace
  pure (state.accessCount - min state.accessRetained state.options.accessCapacity)

/-- Each range that the trace watches on its own, in the order of `watches`, with how many accesses touched it, kept and let go. -/
def traceWatches (emu : Emu) (trace : String := "") : IO (List TraceWatch) := do
  let state ← traceState emu trace
  pure (state.watched.toList.map fun ring =>
    let kept := min ring.retained state.options.accessCapacity
    { range := ring.range, count := ring.count, kept, dropped := ring.count - kept })

/-- The accesses that the trace kept of the `index`th range that it watches on its own, the oldest first. -/
def traceWatchAccesses (emu : Emu) (index : Nat) (trace : String := "") : IO (List TraceAccess) := do
  let state ← traceState emu trace
  let some ring := state.watched[index]? | throw <| IO.userError s!"the trace watches no range {index} on its own"
  pure (ring.accesses.take state.options.accessCapacity).reverse

/-- What a trace has, all at once: what it keeps, how many pcs it saw, kept and let go of for its capacity, of all threads, and so of
accesses, how many versions of code it keeps, and its rings of threads. One that let none go has every pc since it started; one that
`wrapped` has the last of them only, and says how many it let go. -/
structure TraceSummary where
  options : TraceOptions
  seen : Nat
  kept : Nat
  dropped : Nat
  /-- Whether the one ring of accesses keeps any, which it doesn't where there are `watches` and no `watch`: those of each range are
  in `watches` then, and the counts of accesses below are of the one ring only. -/
  sharedAccesses : Bool
  /-- How many accesses it kept in any ring, each once, however many rings kept it. -/
  accessesHeard : Nat
  accessesSeen : Nat
  accessesKept : Nat
  accessesDropped : Nat
  codeVersions : Nat
  threads : List TraceThread
  /-- Each range that it watches on its own. -/
  watches : List TraceWatch := []
  deriving Repr

/-- Whether a trace let pcs go for its capacity, so that it keeps the last of what it saw only. -/
def TraceSummary.wrapped (summary : TraceSummary) : Bool := summary.dropped > 0

/-- What a trace has, of the default trace unless a name is given: none if there is no such trace, and one that saw nothing yet if it
hasn't. -/
def traceSummary (emu : Emu) (trace : String := "") : IO (Option TraceSummary) := do
  let some state := (← emu.trace.get).find? trace | return none
  let rings := if state.options.perThread then state.threadRings.map (·.2) else [state.ring]
  let accessesKept := min state.accessRetained state.options.accessCapacity
  pure (some {
    options := state.options
    seen := state.count
    kept := (pcList state).length
    dropped := rings.foldl (· + ·.dropped) 0
    sharedAccesses := state.options.accessCapacity > 0 && (state.options.watch.isSome || state.options.watches.isEmpty)
    accessesHeard := state.accessesHeard
    accessesSeen := state.accessCount
    accessesKept
    accessesDropped := state.accessCount - accessesKept
    codeVersions := rings.foldl (· + ·.codeSize) 0
    threads := ← traceThreads emu trace
    watches := ← traceWatches emu trace })

/-- All of the trace as bytes, for a checkpoint: what it keeps, its rings with their pcs in order and the bytes that they ran as, its
accesses, and what it counts and keeps of each, which `traceLoad` makes the same again, so that a machine of a checkpoint has the trace
that the one it was of had. -/
def traceSave (emu : Emu) : IO ByteArray := do
  -- Each part is pushed onto the one array: an array made of each word and appended copied all that came before it, and a division
  -- and a power for each byte, made a checkpoint of a long trace take longer than the trace.
  let word (out : ByteArray) (value : Nat) : ByteArray :=
    let value := value.toUInt64
    out.push value.toUInt8 |>.push (value >>> 8).toUInt8 |>.push (value >>> 16).toUInt8 |>.push (value >>> 24).toUInt8
      |>.push (value >>> 32).toUInt8 |>.push (value >>> 40).toUInt8 |>.push (value >>> 48).toUInt8 |>.push (value >>> 56).toUInt8
  let option (out : ByteArray) (value : Option Nat) : ByteArray := match value with
    | some value => word (out.push 1) value
    | none => out.push 0
  let ringBytes (out : ByteArray) (ring : TraceRing) : ByteArray := Id.run do
    let pcs := ring.pcs
    let mut out := word out pcs.length
    for pc in pcs do out := word out pc
    out := word (word (word (word out ring.retained) ring.count) ring.dropped) ring.capacity
    let code := ring.code.reverse
    out := word out code.length
    for (at_, pc, bytes) in code do out := word (word (word out at_) pc) bytes.size ++ bytes
    pure out
  let accessBytes (out : ByteArray) (access : TraceAccess) : ByteArray :=
    let out := word (word (word (word out access.insn) access.pc) access.address) access.size
    word (option (out.push (if access.write then 1 else 0)) access.value) access.thread
  let stateBytes (out : ByteArray) (state : Option TraceState) : ByteArray := Id.run do
    match state with
    | none => pure (out.push 0)
    | some state =>
      let options := state.options
      let mut out := word (word (out.push 1) options.pcCapacity) options.accessCapacity
      out := match options.watch with | some (low, high) => word (word (out.push 1) low) high | none => out.push 0
      out := match options.threads with
        | some threads => threads.foldl word (word (out.push 1) threads.length)
        | none => out.push 0
      out := ringBytes (word (out.push (if options.perThread then 1 else 0)) state.count) state.ring
      let rings := state.threadRings
      out := word out rings.length
      for (thread, ring) in rings do out := ringBytes (word out thread) ring
      let accesses := state.accesses.reverse
      out := word out accesses.length
      for access in accesses do out := accessBytes out access
      out := word (word out state.accessCount) state.accessRetained
      -- Each range watched on its own, with its ring, so that a trace loaded again keeps them apart.
      out := word out state.watched.size
      for ring in state.watched do
        out := word (word (word (word out ring.range.1) ring.range.2) ring.count) ring.retained
        let accesses := ring.accesses.reverse
        out := word out accesses.length
        for access in accesses do out := accessBytes out access
      pure (word out state.accessesHeard)
  let set ← emu.trace.get
  let mut out := word (word (stateBytes .empty set.default) set.nextToken) set.named.length
  for (name, token, state) in set.named do
    out := stateBytes (word (word out name.utf8ByteSize ++ name.toUTF8) token) (some state)
  pure out

/-- The trace that `traceSave` gave the bytes of. -/
def traceLoad (emu : Emu) (data : ByteArray) : IO Unit := do
  let at_ ← IO.mkRef 0
  let byte : IO Nat := do
    let index ← at_.get
    if index ≥ data.size then throw <| IO.userError "the trace of a checkpoint ends too soon"
    at_.set (index + 1)
    pure data[index]!.toNat
  let word : IO Nat := do
    let mut value := 0
    for index in List.range 8 do value := value + (← byte) * 256 ^ index
    pure value
  let bytes : IO ByteArray := do
    let size ← word
    let index ← at_.get
    if index + size > data.size then throw <| IO.userError "the trace of a checkpoint ends too soon"
    at_.set (index + size)
    pure (data.extract index (index + size))
  let list {α : Type} (item : IO α) : IO (List α) := do
    let count ← word
    let mut items := #[]
    for _ in List.range count do items := items.push (← item)
    pure items.toList
  let ring : IO TraceRing := do
    let pcs ← list word
    let retained ← word
    let count ← word
    let dropped ← word
    let capacity ← word
    let code ← list do
      let at_ ← word
      let pc ← word
      pure (at_, pc, ← bytes)
    let known := code.foldl (init := {}) fun known (_, pc, bytes) => known.insert pc bytes
    pure { front := pcs, retained, count, dropped, capacity, code := code.reverse, codeSize := code.length
           codeLimit := 2 * code.length + 64, known }
  let trace : IO (Option TraceState) := do match ← byte with
    | 0 => pure none
    | 1 => do
      let pcCapacity ← word
      let accessCapacity ← word
      let watch ← if (← byte) == 1 then do let low ← word; pure (some (low, ← word)) else pure none
      let threads ← if (← byte) == 1 then some <$> list word else pure none
      let perThread := (← byte) == 1
      let count ← word
      let shared ← ring
      let rings ← list do
        let thread ← word
        pure (thread, ← ring)
      let access : IO TraceAccess := do
        let insn ← word
        let pc ← word
        let address ← word
        let size ← word
        let write := (← byte) == 1
        let value ← if (← byte) == 1 then some <$> word else pure none
        let thread ← word
        pure { insn, pc, address, size, write, value, thread }
      let accesses ← list access
      let accessCount ← word
      let accessRetained ← word
      let watched ← list do
        let low ← word
        let high ← word
        let count ← word
        let retained ← word
        let accesses ← list access
        pure ({ range := (low, high), accesses := accesses.reverse, count, retained } : WatchRing)
      let accessesHeard ← word
      let state : TraceState := {
        options := { pcCapacity, accessCapacity, watch, watches := watched.map (·.range), threads, perThread }
        watched := watched.toArray
        accessesHeard
        count
        ring := shared
        rings := rings.foldl (init := {}) fun rings (thread, ring) => rings.insert thread ring
        accesses := accesses.reverse
        accessCount
        accessRetained
      }
      pure (some state)
    | _ => throw <| IO.userError "the trace of a checkpoint is of no kind there is"
  let default ← trace
  let nextToken ← word
  let named ← list do
    let name ← match String.fromUTF8? (← bytes) with
      | some name => pure name
      | none => throw <| IO.userError "the trace of a checkpoint has a name that isn't text"
    let token ← word
    let some state ← trace | throw <| IO.userError "the trace of a checkpoint has a session with no trace"
    pure (name, token, state)
  if (← at_.get) != data.size then throw <| IO.userError "the trace of a checkpoint has bytes after it"
  forgetMemoryFilter emu
  emu.trace.set { default, named, nextToken }

/-- Runs a hook that is in the middle of an instruction, as a checkpoint then couldn't be of anything whole. -/
private def serve (emu : Emu) (action : IO α) : IO α := do
  let before ← emu.serving.get
  emu.serving.set true
  try action finally emu.serving.set before

private def serialize (emu : Emu) (action : IO α) : IO α := do
  match ← emu.parallelLock.get with
  | some mutex =>
    Std.BaseMutex.lock mutex
    try action finally Std.BaseMutex.unlock mutex
  | none => action

/-- An access in front of the last that a ring keeps, of which it lets go of the oldest once it has twice `capacity`: what it has then,
and how many. -/
private def keepAccess (capacity : Nat) (access : TraceAccess) (accesses : List TraceAccess) (retained : Nat) :
    List TraceAccess × Nat :=
  if retained + 1 ≥ 2 * capacity then ((access :: accesses).take capacity, capacity) else (access :: accesses, retained + 1)

private def recordAccess (emu : Emu) (write : Bool) (address size value : Nat) : IO Unit := do
  if !(← emu.trace.get).active then return
  let pc ← emu.pc.get
  let thread ← emu.currentThreadRef.get
  emu.trace.modify fun set => set.mapStates fun state =>
    let options := state.options
    if options.accessCapacity = 0 || !state.keeps thread then state
    else
      let access : TraceAccess := {
        insn := state.count - 1
        pc
        address
        size
        write
        value := if write then some value else none
        thread
      }
      -- Each range that it touches, in the ring of its own.
      let watched := state.watched.map fun ring =>
        if !accessTouches ring.range.1 ring.range.2 address size then ring
        else
          let (accesses, retained) := keepAccess options.accessCapacity access ring.accesses ring.retained
          { ring with accesses, retained, count := ring.count + 1 }
      let shared := match options.watch with
        | some range => accessTouches range.1 range.2 address size
        | none => options.watches.isEmpty
      let heard := shared || options.watches.any fun range => accessTouches range.1 range.2 address size
      let state := { state with watched, accessesHeard := state.accessesHeard + (if heard then 1 else 0) }
      if !shared then state
      else
        let (accesses, accessRetained) := keepAccess options.accessCapacity access state.accesses state.accessRetained
        { state with accesses, accessRetained, accessCount := state.accessCount + 1 }

private def notifyCode (emu : Emu) (address : Nat) : IO Unit := do
  -- Of a run that was taken back, the hooks of a site that fired as it ran don't fire again as it is run again, as long as it comes to
  -- them in the same order.
  match ← emu.replaySites.get with
  | site :: rest =>
    if site == address then
      emu.replaySites.set rest
      return
    -- Of the sites, only those that have a hook count: an instruction between them that has none doesn't end it.
    if (← hooksNear emu address).any fun hook => hook.first ≤ address && address ≤ hook.last then emu.replaySites.set []
  | [] => pure ()
  -- What fired before the thread stopped here doesn't again, the first time that it goes on, and of the first instruction that it runs
  -- after it stopped, wherever that is: one that was sent elsewhere, by `setPc` or a signal, comes back to where it stopped later, where
  -- what is there fires. That goes even with no hooks left, so that one that comes later finds none of it.
  let thread ← emu.currentThreadRef.get
  let held := (← emu.suppressed.get).filter fun (owner, _, _) => owner == thread
  let suppressed := held.find? fun (_, at_, _) => at_ == address
  if !held.isEmpty then emu.suppressed.modify (·.filter fun (owner, _, _) => owner != thread)
  if (← emu.hooks.get).isEmpty then return
  let near ← hooksNear emu address
  let fires (hook : CodeHook) : Bool := hook.first ≤ address && address ≤ hook.last &&
    !(suppressed.any fun (_, _, ids) => ids.contains hook.id)
  if !near.any fires then return
  serialize emu <| do
  let context := hookContext emu
  -- What one that fires takes off doesn't fire after it.
  let changes ← emu.hookChanges.get
  for hook in near do
    if fires hook then
      if (← emu.hookChanges.get) == changes || (← emu.hooks.get).any (·.id == hook.id) then hook.action context address

/-- Whether nothing watches the code that runs. -/
private def rangeIsQuiet (emu : Emu) : IO Bool := do
  pure ((← emu.hooks.get).isEmpty && !(← emu.trace.get).active)

/-- The last access that faulted. -/
def failure (emu : Emu) : IO (Option MemoryFault) := emu.lastFault.get

private def recordFault (emu : Emu) (operation : MemoryOperation) (address : Nat) : IO Unit := do
  let pc ← emu.pc.get
  let thread ← emu.currentThreadRef.get
  emu.lastFault.set (some ⟨pc, address, operation, thread⟩)
  emu.faultFresh.set true

private def notifyMemory (emu : Emu) (write : Bool) (address size value : Nat) : IO Unit := do
  -- What an access does depends on the regions that it touches, of which there are few.
  let mapped ← regionsTouching emu address size
  let fault (offset : Nat) : IO Unit := do
    let operation := if write then MemoryOperation.write else MemoryOperation.read
    recordFault emu operation (address + offset)
    throw <| IO.userError s!"Emu {repr operation} fault at {address + offset}"
  let takeBack (hit : Bool) : IO Unit := do
    if accessRestarts hit (← emu.lastBudget.get) emu.engine.deferMemorySync then
      emu.restarting.set true
      throw <| IO.userError s!"Emu step restarts at the watched access at {address}"
  let hooks : IO Unit :=
    if write then do
      match emu.journal with
      | some journal => journal.modify (journalWrite · address size)
      | none => pure ()
      let hit := hooksForAccess (·.first) (·.last) (← emu.writeHooks.get) address size
      takeBack !hit.isEmpty
      -- What one that fires takes off doesn't fire after it.
      hit.forM fun hook => do
        if (← emu.writeHooks.get).any (·.id == hook.id) then
          serialize emu <| serve emu <| hook.action (hookContext emu) address size value
    else do
      let hit := hooksForAccess (·.first) (·.last) (← emu.readHooks.get) address size
      takeBack !hit.isEmpty
      hit.forM fun hook => do
        if (← emu.readHooks.get).any (·.id == hook.id) then
          serialize emu <| serve emu <| hook.action (hookContext emu) address size
  notifyAccess mapped write address size fault
    (Primus.Lifted.markDirtyRange emu.engine address (address + size - 1))
    (recordAccess emu write address size value) hooks

private def cells (emu : Emu) (state : Bil.State) : IO (Σ width, Bap.Memory width) := do
  match Bil.lookup state.env emu.config.memory with
  | .ok (.memory memory) => pure ⟨_, memory⟩
  | .ok _ => throw <| IO.userError "Emu memory is not a memory value"
  | .error error => throw <| IO.userError error

/-- Copies the native memory into the memory of the state and of every thread, for what reads those rather than through `read`. -/
def synchronizePersistentMemory (emu : Emu) : IO Unit := do
  match ← emu.engine.persistentMemory.get with
  | none => pure ()
  | some native =>
    let state ← emu.state.get
    let ⟨width, _⟩ ← cells emu state
    let (addresses, values) ← Jit.dumpMemory native
    let memory := Bap.Memory.writeSortedCells (Bap.Memory.empty width) ((addresses.zip values).toList.map fun cell =>
      (BitVec.ofNat width cell.1.toNat, cell.2))
    let contexts ← captureThreads emu
    emu.threadsRef.set (contexts.map fun context =>
      { context with state := { env := Bil.bind context.state.env emu.config.memory (.memory memory) } })
    emu.state.set { env := Bil.bind state.env emu.config.memory (.memory memory) }

/-- The bytes at an address, of the native memory or else of the state's, all at once. -/
private def rawBytes (emu : Emu) (address size : Nat) : IO ByteArray := do
  match ← emu.engine.persistentMemory.get with
  | some memory => Jit.readMemoryRange memory (UInt64.ofNat address) size
  | none =>
    let state ← emu.state.get
    let ⟨_, memory⟩ ← cells emu state
    pure (Bap.Memory.readRegion memory address size)

/-- Whether every address in `lower`..`upper` lies in a region. -/
def coversRange (regions : List Region) (lower upper : Nat) : Bool :=
  let rec loop (fuel position : Nat) : Bool :=
    if position ≥ upper then true
    else
      match fuel with
      | 0 => false
      | fuel + 1 =>
        match lookupRegion regions position with
        | some region => loop fuel (region.address + region.data.size)
        | none => false
  loop regions.length lower

/-- Starts keeping a profile of what runs, from nothing: by each address that a step starts at, how often it ran compiled and in the
interpreter, the instructions that came to, and the time of each. A range is counted at the address that it was entered at, with all
that it ran. It costs a little on each step until `stopProfile`. -/
def startProfile (emu : Emu) : IO Unit := do
  emu.engine.profile.set (some {})
  for (_, worker) in ← emu.parallelWorkers.get do worker.profile.set (some {})

/-- What the profile has, the addresses where most time went first, with those of the workers of parallel rounds added in. -/
def profile (emu : Emu) : IO (List (Nat × Primus.Lifted.Profile)) := do
  let mut table := (← emu.engine.profile.get).getD {}
  for (_, worker) in ← emu.parallelWorkers.get do
    for (address, entry) in ((← worker.profile.get).getD {}).toList do
      let mine := table.getD address {}
      table := table.insert address { mine with
        nativeRuns := mine.nativeRuns + entry.nativeRuns, interpretedRuns := mine.interpretedRuns + entry.interpretedRuns
        instructions := mine.instructions + entry.instructions, nativeNanos := mine.nativeNanos + entry.nativeNanos
        interpretedNanos := mine.interpretedNanos + entry.interpretedNanos, compileMs := mine.compileMs + entry.compileMs }
  let total (entry : Primus.Lifted.Profile) : Nat := entry.nativeNanos + entry.interpretedNanos
  pure (table.toList.toArray.qsort (fun left right => total left.2 > total right.2 || (total left.2 == total right.2 && left.1 < right.1))).toList

/-- Stops keeping the profile, which is gone. -/
def stopProfile (emu : Emu) : IO Unit := do
  emu.engine.profile.set none
  for (_, worker) in ← emu.parallelWorkers.get do worker.profile.set none

/-- Forgets what was lifted and compiled of the code that has a byte from `first` to `last`, of every version of it, so that it is lifted
and compiled again when it next runs, without its bytes or protections changing: see `Primus.Lifted.invalidateCode`. -/
def invalidateCode (emu : Emu) (first last : Nat) : IO Unit := do
  let first := emu.config.untag first
  let last := emu.config.untag last
  Primus.Lifted.invalidateCode emu.engine first last
  -- A worker of a parallel round has an engine of its own.
  for (_, worker) in ← emu.parallelWorkers.get do
    Primus.Lifted.invalidateCode worker first last

/-- Bytes of memory as a program may read them: what isn't mapped or readable is an error. -/
def read (emu : Emu) (address size : Nat) : IO ByteArray := do
  let address := emu.config.untag address
  -- An absurd size fails right here, instead of allocating before it fails. What fails says where, and how much before it could be
  -- read, for a read across a hole, which `peek` reads as zeros.
  let regions ← regionsTouching emu address size
  let fail (what : String) (position : Nat) : IO Unit :=
    throw <| IO.userError s!"{what} Emu address {position} in {size} bytes at {address}, after {position - address} readable"
  let rec check : Nat → Nat → IO Unit
    | 0, position => if position < address + size then fail "unmapped" position else pure ()
    | fuel + 1, position => do
      if position < address + size then
        match lookupRegion regions position with
        | none => fail "unmapped" position
        | some region =>
          if !region.protection.readable then fail "unreadable" position
          else check fuel (region.address + region.data.size)
  check regions.length address
  -- All at once, as what a worker of a parallel round stores is seen whole.
  rawBytes emu address size

/-- The bytes at an address, whatever a program may do with them there, as a kernel sees them. -/
def peek (emu : Emu) (address size : Nat) : IO ByteArray :=
  rawBytes emu address size

private def synchronizeWrite (emu : Emu) (address : Nat) (data : ByteArray) : IO Unit := do
  let persistent ← emu.engine.persistentMemory.get
  let memoryVar ← emu.engine.persistentVariable.get
  match persistent, memoryVar with
  | some memory, some var =>
    if var = emu.config.memory then
      if address + data.size ≤ 2 ^ 64 then Jit.writeMemoryBytes memory (UInt64.ofNat address) data
      else
        let addresses := (List.range data.size).map fun offset => UInt64.ofNat (address + offset)
        Jit.writeMemory memory addresses.toArray data.toList.toArray
    else Primus.Lifted.discardMemory emu.engine
  | _, _ => pure ()

private def writeByte (emu : Emu) (address : Nat) (value : UInt8) : IO Unit := do
  let mapped ← emu.regions.get
  match lookupRegion mapped address with
  | none => throw <| IO.userError s!"unmapped Emu address {address}"
  | some region =>
    if !region.protection.writable then
      throw <| IO.userError s!"read-only Emu address {address}"
    let state ← emu.state.get
    let ⟨width, memory⟩ ← cells emu state
    let updated := Bap.Memory.writeByte memory (BitVec.ofNat width address) value
    emu.state.set { env := Bil.bind state.env emu.config.memory (.memory updated) }
    if region.protection.executable then Primus.Lifted.discardRange emu.engine address address
    synchronizeWrite emu address (ByteArray.mk #[value])
    setRegions emu (mapped.map fun current =>
      if current.contains address then
        { current with data := current.data.set! (address - current.address) value }
      else current)

/-- The parts of `address`..`upper` that are in executable regions, first to last, where all of it is mapped and writable, which is
an error otherwise, at the first address that isn't. -/
private def writableCode (regions : List Region) (address upper : Nat) : IO (List (Nat × Nat)) :=
  let rec walk : Nat → Nat → List (Nat × Nat) → IO (List (Nat × Nat))
    | 0, position, code =>
      if position < upper then throw <| IO.userError s!"unmapped Emu address {position}" else pure code
    | fuel + 1, position, code => do
      if position ≥ upper then return code
      match lookupRegion regions position with
      | none => throw <| IO.userError s!"unmapped Emu address {position}"
      | some region =>
        if !region.protection.writable then throw <| IO.userError s!"read-only Emu address {position}"
        let finish := region.address + region.data.size
        walk fuel finish (if region.protection.executable then (position, min finish upper - 1) :: code else code)
  walk regions.length address []

/-- Writes bytes as a program may, in writable regions, which it may go across, and drops what was compiled of code there. Nothing
is written unless all of it can be. What hears of changes hears of it. -/
def write (emu : Emu) (address : Nat) (data : ByteArray) : IO Unit := do
  let address := emu.config.untag address
  if data.size > 0 then
    let code ← writableCode (← regionsTouching emu address data.size) address (address + data.size)
    let state ← emu.state.get
    let ⟨_, memory⟩ ← cells emu state
    let updated := Bap.Memory.writeRegion memory address data
    emu.state.set { env := Bil.bind state.env emu.config.memory (.memory updated) }
    for (first, last) in code do Primus.Lifted.discardRange emu.engine first last
    synchronizeWrite emu address data
    for changed in ← emu.memoryChanged.get do changed address data.size false

/-- Puts bytes at an address, whatever a program may do with them there, as a kernel does. `known` is that they are what they were somewhere else that
what hears of it has been told of, as what a shared mapping has when its file changed. -/
def poke (emu : Emu) (address : Nat) (data : ByteArray) (known : Bool := false) : IO Unit := do
  if data.size > 0 then
    let state ← emu.state.get
    let ⟨_, memory⟩ ← cells emu state
    let updated := Bap.Memory.writeRegion memory address data
    emu.state.set { env := Bil.bind state.env emu.config.memory (.memory updated) }
    Primus.Lifted.discardRange emu.engine address (address + data.size - 1)
    synchronizeWrite emu address data
    if !known then
      for changed in ← emu.memoryChanged.get do changed address data.size false

/-- What a patch does where it doesn't find the bytes it expects: says so, throws, or waits for them, as for text that is still
encrypted. -/
inductive Patch.OnMismatch where
  | skip
  | error
  | wait
  deriving Repr, BEq, Inhabited

/-- What becomes of loads of a patch's bytes, as a program that checks its own code makes: nothing heard of them, or each counted by
the instruction that made it (`Emu.patchReads`), so that a loop that reads a program's own code to check it stands out. -/
inductive Patch.Reads where
  | ignore
  | record
  deriving Repr, BEq, Inhabited

/-- Bytes to put at an address in place of those it expects to find there, as many as those. -/
structure Patch where
  address : Nat
  expected : ByteArray
  replacement : ByteArray
  /-- Whether to read the bytes back after, to say that they are what was put. -/
  readback : Bool := true
  onMismatch : Patch.OnMismatch := .skip
  reads : Patch.Reads := .record

/-- What came of a patch. It is `applied` as well where the replacement is there already. A patch that waits is `pending` on a hook,
which `removeHook` takes off; `found` is what was there. -/
inductive Patch.Result where
  | applied
  | skipped (reason : String)
  | mismatch (found : ByteArray)
  | unverified (found : ByteArray)
  | pending (hook : HookId)
  deriving Inhabited

/-- The address space of the thread that runs. -/
private def currentSpace (emu : Emu) : IO Nat := do spaceOf emu (← thread emu)

/-- Counts loads of a patch's bytes, by the instruction that made each, in the address space where the patch is, in place of what
counted them for a patch before it at the same address there, so that a load is counted once. -/
private def watchPatch (emu : Emu) (address : Nat) (patch : Patch) (space : Nat) : IO (Option HookId) := do
  let records ← emu.patched.get
  if let some previous := records.find? fun record => record.address == address && record.space == space then
    if let some id := previous.readHook then
      removeHook emu id
      emu.patched.set (records.map fun record => if record.readHook == some id then { record with readHook := none } else record)
  if patch.reads == .ignore then return none
  let last := address + patch.expected.size - 1
  some <$> onRead emu (address, last) fun current _ _ => do
    if (← currentSpace current) != space then return
    let pc ← current.pc.get
    current.patchReads.modify fun reads => reads.insert (pc, address) (reads.getD (pc, address) 0 + 1)

/-- Puts a patch's replacement where all of its bytes are mapped and are what it expects, whatever their protection, which it leaves
as it was: code there runs as patched. What was there is kept. -/
private def applyPatch (emu : Emu) (address : Nat) (patch : Patch) : IO Patch.Result := do
  let size := patch.expected.size
  if !coversRange (← emu.regions.get) address (address + size) then
    return .skipped s!"unmapped address in {address}..{address + size}"
  let found ← peek emu address size
  if found == patch.replacement then return .applied
  if found != patch.expected then return .mismatch found
  poke emu address patch.replacement
  let space ← currentSpace emu
  let readHook ← watchPatch emu address patch space
  emu.patched.modify ({ address, space, original := found, replacement := patch.replacement, readHook } :: ·)
  if !patch.readback then return .applied
  let after ← peek emu address size
  pure (if after == patch.replacement then .applied else .unverified after)

/-- How many bytes an instruction is decoded from, at most, which is the most that one has: an IT block of Thumb is decoded whole, its
two bytes and four instructions of up to four, x86 has up to fifteen, and PowerPC has prefixed instructions of eight. -/
private def decodeWindow (config : Config) : Nat :=
  match config.syscallAbi with | .x86_64 | .x86_32 => 16 | .arm => 18 | .powerpc | .powerpc64 => 8 | _ => 4

/-- Applies a patch only where its bytes are what it expects, and says what came of it rather than throwing, but with
`onMismatch := .error`. With `.wait`, a patch that finds other bytes, or memory that isn't mapped yet, is tried again before each
instruction that runs in its range or starts before it near enough to run some of its bytes, in the same address space, until it finds
them and is applied, and its hook is taken off. -/
def patch (emu : Emu) (patch : Patch) : IO Patch.Result := do
  if patch.expected.size != patch.replacement.size then
    throw <| IO.userError s!"patch at {patch.address} expects {patch.expected.size} bytes and has {patch.replacement.size}"
  if patch.expected.size = 0 then return .applied
  let address := emu.config.untag patch.address
  match ← applyPatch emu address patch, patch.onMismatch with
  | .mismatch found, .error =>
    throw <| IO.userError s!"patch at {address} expects {patch.expected.toList} and found {found.toList}"
  | .mismatch _, .wait | .skipped _, .wait =>
    let space ← currentSpace emu
    let hook ← IO.mkRef (none : Option HookId)
    -- From as far before it as an instruction that has some of its bytes may start, or from 0 for a patch nearer to it than that, where
    -- the subtraction of `Nat` stops.
    let first := address - (decodeWindow emu.config - 1)
    let id ← onCode emu (first, address + patch.expected.size - 1) fun current _ => do
      if (← currentSpace current) != space then return
      match ← applyPatch current address patch with
      | .mismatch _ | .skipped _ => pure ()
      | _ => if let some id := ← hook.get then removeHook emu id
    hook.set (some id)
    pure (.pending id)
  | result, _ => pure result

/-- The patches that were applied, the first first, with what was there before. -/
def patches (emu : Emu) : IO (List PatchRecord) := do
  pure (← emu.patched.get).reverse

/-- The loads of patched bytes, by the instruction that made them and the patch, the most first: a loop that sums a program's own
code to check it is where the most are. -/
def patchReads (emu : Emu) : IO (List PatchRead) := do
  let reads := (← emu.patchReads.get).toList.map fun ((pc, patch), count) => { pc, patch, count : PatchRead }
  pure (reads.toArray.qsort (fun a b => a.count > b.count || (a.count == b.count && a.pc < b.pc))).toList

private def synchronizeBatch (emu : Emu) (writes : List (Nat × ByteArray)) : IO Unit := do
  let persistent ← emu.engine.persistentMemory.get
  let memoryVar ← emu.engine.persistentVariable.get
  match persistent, memoryVar with
  | some memory, some var =>
    if var = emu.config.memory then
      let addresses := writes.flatMap fun (address, data) =>
        (List.range data.size).map fun offset => UInt64.ofNat (address + offset)
      let bytes := writes.flatMap fun (_, data) => data.toList
      Jit.writeMemory memory addresses.toArray bytes.toArray
    else Primus.Lifted.discardMemory emu.engine
  | _, _ => pure ()

/-- `write` of each, at once. -/
def writeBatch (emu : Emu) (writes : List (Nat × ByteArray)) : IO Unit := do
  let mapped ← emu.regions.get
  let code ← writes.flatMapM fun (address, data) => writableCode mapped address (address + data.size)
  let state ← emu.state.get
  let ⟨_, memory⟩ ← cells emu state
  let updated := writes.foldl (init := memory) fun memory (address, data) =>
    Bap.Memory.writeRegion memory address data
  emu.state.set { env := Bil.bind state.env emu.config.memory (.memory updated) }
  for (first, last) in code do Primus.Lifted.discardRange emu.engine first last
  synchronizeBatch emu writes
  for changed in ← emu.memoryChanged.get do
    for (address, data) in writes do changed address data.size false
  -- Each region has the part of each write that is in it.
  let updatedRegions := writes.foldl (init := mapped) fun regions (address, data) =>
    regions.map fun current =>
      let low := max address current.address
      let high := min (address + data.size) (current.address + current.data.size)
      if low < high then
        { current with data := current.data.extract 0 (low - current.address) ++ data.extract (low - address) (high - address) ++
          current.data.extract (high - current.address) current.data.size }
      else current
  setRegions emu updatedRegions

private def checkInSpace (emu : Emu) (region : Region) : IO Unit := do
  match memoryWidth emu.config with
  | .ok width =>
    if !regionInSpace width region then
      throw <| IO.userError s!"Emu region at {region.address} exceeds the address space"
  | .error error => throw <| IO.userError error

/-- Maps a region where nothing is. `zeros` says that its bytes are all zeros, which then take no memory of the host. -/
def map (emu : Emu) (region : Region) (zeros : Bool := false) : IO Unit := do
  checkInSpace emu region
  let near ← if region.data.size == 0 then emu.regions.get else regionsTouching emu region.address region.data.size
  if near.any fun current => overlaps current region then
    throw <| IO.userError s!"Emu region overlaps an existing mapping at {region.address}"
  -- Memory holds zeros where nothing was written, and nothing was where nothing was mapped, so a mapping of zeros, such as
  -- the stack of a thread, has nothing to write.
  let written := !zeros && region.data.data.any (· != 0)
  if written then
    let state ← emu.state.get
    let ⟨_, memory⟩ ← cells emu state
    let updated := Bap.Memory.writeRegion memory region.address region.data
    emu.state.set { env := Bil.bind state.env emu.config.memory (.memory updated) }
  if region.protection.executable && region.data.size > 0 then
    Primus.Lifted.discardRange emu.engine region.address (region.address + region.data.size - 1)
  -- A lot of bytes go into the native memory now, made of the memory if there is none yet, as an emulator copies what is mapped
  -- when it is, rather than the first run making it of all of them.
  if written && region.data.size ≥ 65536 && (← emu.engine.persistentMemory.get).isNone && !emu.engine.deferMemorySync &&
      (← emu.processMemory.get).isEmpty then
    attachMemory emu (← nativeFromState emu (← emu.state.get))
  else if written then synchronizeWrite emu region.address region.data
  for changed in ← emu.memoryChanged.get do changed region.address region.data.size (!written)
  replaceRegions emu (region :: (← emu.regions.get)) [] [region]

/-- A mapping of zeros, which takes nothing of the host until it is written, and isn't looked through: what a program maps of memory is. -/
def mapZeros (emu : Emu) (address size : Nat) (protection : Primus.Protection) : IO Unit :=
  map emu ⟨address, Jit.zeros size, protection⟩ (zeros := true)

/-- Puts bytes over a region that is mapped already, of the same size, with its protection. -/
def overlay (emu : Emu) (region : Region) : IO Unit := do
  checkInSpace emu region
  let mapped ← emu.regions.get
  if overlayConflict mapped region then
    throw <| IO.userError s!"Emu overlay size mismatch at {region.address}"
  let state ← emu.state.get
  let ⟨_, memory⟩ ← cells emu state
  let updated := Bap.Memory.writeRegion memory region.address region.data
  emu.state.set { env := Bil.bind state.env emu.config.memory (.memory updated) }
  if region.protection.executable && region.data.size > 0 then
    Primus.Lifted.discardRange emu.engine region.address (region.address + region.data.size - 1)
  synchronizeWrite emu region.address region.data
  for changed in ← emu.memoryChanged.get do changed region.address region.data.size false
  setRegions emu (region :: mapped.filter fun current => current.address != region.address)

private def regionPiece (region : Region) (first last : Nat) (protection : Primus.Protection) : List Region :=
  if first < last then
    [⟨first, Jit.slice region.data (first - region.address) (last - region.address), protection⟩]
  else []

/-- Replace the protection of the bytes of `region` within `lower`..`upper`, keeping the rest. -/
def splitRegion (lower upper : Nat) (protection : Primus.Protection) (region : Region) : List Region :=
  let finish := region.address + region.data.size
  let start := max lower region.address
  let stop := min upper finish
  if stop ≤ start then [region]
  else if start = region.address && stop = finish then [{ region with protection }]
  else
    regionPiece region region.address start region.protection ++ regionPiece region start stop protection ++
      regionPiece region stop finish region.protection

/-- `mprotect`: only the bytes in the range change protection, and all of them must be mapped. -/
def protectRegions (regions : List Region) (address size : Nat) (protection : Primus.Protection) :
    Option (List Region) :=
  if coversRange regions address (address + size) then
    some (regions.flatMap (splitRegion address (address + size) protection))
  else none

/-- Changes what may be done with mapped memory, as `mprotect`, splitting regions where it has to. -/
def protect (emu : Emu) (address size : Nat) (protection : Primus.Protection) : IO Unit := do
  if size = 0 then pure ()
  else
    match protectRegions (← emu.regions.get) address size protection with
    | some regions =>
      let touched ← regionsTouching emu address size
      replaceRegions emu regions touched (touched.flatMap (splitRegion address (address + size) protection))
      -- A compiled range would keep running code that lost its execute permission: what was executable of the range, and nothing
      -- else, as a page made writable again and again for a stub or the GOT had nothing compiled to lose.
      if !protection.executable then
        for region in touched do
          let low := max address region.address
          let high := min (address + size) (region.address + region.data.size)
          if region.protection.executable && low < high then Primus.Lifted.discardRange emu.engine low (high - 1)
    | none => throw <| IO.userError s!"unmapped Emu protection range at {address}"

/-- `MADV_DONTNEED`: the bytes in the range read as zeros, and take no memory of the host until they are written. -/
def clearMapped (emu : Emu) (address size : Nat) : IO Unit := do
  if size > 0 then
    let upper := address + size
    for changed in ← emu.memoryChanged.get do changed address size true
    Primus.Lifted.discardRange emu.engine address (upper - 1)
    let state ← emu.state.get
    let ⟨_, memory⟩ ← cells emu state
    emu.state.set { env := Bil.bind state.env emu.config.memory (.memory (Bap.Memory.clearRange memory address size)) }
    if let some native := ← emu.engine.persistentMemory.get then
      -- What isn't mapped any more needn't take memory of the host, as a program may map and unmap as long as it likes.
      if upper > address then
        Jit.zeroMemory native (UInt64.ofNat address) (UInt64.ofNat (upper - 1))
        Jit.trimMemory native (UInt64.ofNat address) (UInt64.ofNat (upper - 1))

/-- `munmap`: the bytes in the range are gone, and read as zeros if the addresses are mapped again. -/
def unmap (emu : Emu) (address size : Nat) : IO Unit := do
  if size > 0 then
    let upper := address + size
    let pieces (region : Region) : List Region :=
      let finish := region.address + region.data.size
      if finish ≤ address || upper ≤ region.address then [region]
      else regionPiece region region.address (min address finish) region.protection ++
        regionPiece region (max upper region.address) finish region.protection
    let touched ← regionsTouching emu address size
    replaceRegions emu ((← emu.regions.get).flatMap pieces) touched (touched.flatMap pieces)
    if let some top := ← emu.mappingTop.get then
      if upper > top then emu.mappingTop.set none
    clearMapped emu address size

/-- What is mapped: where, how much, and what may be done with it. -/
def regions (emu : Emu) : IO (List (Nat × Nat × Primus.Protection)) := do
  let mapped ← emu.regions.get
  pure (mapped.map fun region => (region.address, region.data.size, region.protection))

/-- A register of the thread that runs. -/
def reg (emu : Emu) (var : Bap.Var) : IO Bap.Value := do
  let state ← emu.state.get
  match Bil.lookup state.env var with
  | .ok value => pure value
  | .error error => throw <| IO.userError error

/-- Sets a register of the thread that runs. -/
def setReg (emu : Emu) (var : Bap.Var) (value : Bap.Value) : IO Unit := do
  if var.typ != value.type then
    throw <| IO.userError s!"register {var.name} has the wrong value type"
  emu.state.modify fun state => { env := Bil.bind state.env var value }
  -- The state now has the memory: what native memory has follows it, on the next access.
  if var == emu.config.memory then
    emu.memorySwitched.set true
    Primus.Lifted.discardMemory emu.engine
    let space ← spaceOf emu (← emu.currentThreadRef.get)
    if (← emu.processMemory.get).contains space then
      let native ← nativeFromState emu (← emu.state.get)
      emu.processMemory.modify (·.insert space native)
      attachMemory emu native

/-- The register of the number of a system call, those of its arguments, and that of its result. -/
def syscallRegisters : SyscallAbi → String × List String × String
  | .riscv => ("X17", ["X10", "X11", "X12", "X13", "X14", "X15"], "X10")
  | .x86_64 => ("RAX", ["RDI", "RSI", "RDX", "R10", "R8", "R9"], "RAX")
  | .aarch64 => ("X8", ["X0", "X1", "X2", "X3", "X4", "X5"], "X0")
  | .mips => ("R2", ["R4", "R5", "R6", "R7", "R8", "R9"], "R2")
  | .powerpc | .powerpc64 => ("R0", ["R3", "R4", "R5", "R6", "R7", "R8"], "R3")
  | .x86_32 => ("EAX", ["EBX", "ECX", "EDX", "ESI", "EDI", "EBP"], "EAX")
  | .arm => ("R7", ["R0", "R1", "R2", "R3", "R4", "R5"], "R0")

/-- How wide addresses are. -/
def wordWidth (emu : Emu) : IO Nat :=
  match memoryWidth emu.config with
  | .ok width => pure width
  | .error error => throw <| IO.userError error

private def readWord (emu : Emu) (name : String) : IO Nat := do
  let width ← wordWidth emu
  let value ← reg emu ⟨name, .imm width, 0, false⟩
  match Value.asBits value with
  | .ok value => pure value.2.toNat
  | .error error => throw <| IO.userError error

/-- The task that runs. -/
def currentTask (emu : Emu) : IO Tasks.Entry := do
  let id ← thread emu
  match (← emu.taskTable.get).find? id with
  | some task => pure task
  | none => throw <| IO.userError s!"Emu thread {id} has no task"

/-- A new thread of the process that runs, in its address space. -/
private def newThread (emu : Emu) : IO ThreadId := do
  let task ← currentTask emu
  saveCurrentThread emu
  let id ← emu.nextThreadRef.get
  emu.nextThreadRef.set (id + 1)
  emu.taskTable.modify (·.addTask { task with tid := id, status := none })
  pure id

/-- A new thread in the address space of the one that runs, with its registers but for `arg` in the first argument register, that starts at
`start`. It has no stack or thread pointer of its own: they are for the host to give it. -/
def spawnThread (emu : Emu) (start : Nat) (arg : Nat) : IO ThreadId := do
  let id ← newThread emu
  let width ← wordWidth emu
  let (_, arguments, _) := syscallRegisters emu.config.syscallAbi
  match arguments.head? with
  | none => throw <| IO.userError "target has no thread argument register"
  | some register =>
    let current ← emu.state.get
    let argument : Bap.Var := ⟨register, .imm width, 0, false⟩
    let context := spawnContext id current argument (.bits (BitVec.ofNat width arg)) start
    emu.threadsRef.modify (context :: ·)
    pure id

/-- A new process, as `fork` makes, that starts at `childPc` with 0 in the result register, stopped until it is let go, in its parent's
address space until `cloneProcessMemory`. -/
def forkThread (emu : Emu) (childPc : Nat) : IO ThreadId := do
  let task ← currentTask emu
  saveCurrentThread emu
  let id ← emu.nextThreadRef.get
  emu.nextThreadRef.set (id + 1)
  -- Its address space is that of its parent, until `cloneProcessMemory` gives it its own.
  emu.taskTable.modify (·.addTask { tid := id, group := id, parent := task.group, space := task.space })
  let width ← wordWidth emu
  let (_, _, register) := syscallRegisters emu.config.syscallAbi
  let current ← emu.state.get
  let result : Bap.Var := ⟨register, .imm width, 0, false⟩
  let context := forkContext id current result (.bits (BitVec.ofNat width 0)) childPc
  emu.threadsRef.modify (context :: ·)
  pure id

/-- The stack pointer and the thread pointer of a target. -/
def threadRegisters : SyscallAbi → String × String
  | .riscv => ("X2", "X4")
  | .x86_64 => ("RSP", "FS_BASE")
  | .aarch64 => ("SP", "TPIDR_EL0")
  | .mips => ("R29", "USERLOCAL")
  | .powerpc => ("R1", "R2")
  | .powerpc64 => ("R1", "R13")
  | .x86_32 => ("ESP", "GS_BASE")
  | .arm => ("SP", "TPIDRURO")

/-- Gives a process that `forkThread` made a copy of its parent's memory, of its own. -/
def cloneProcessMemory (emu : Emu) (child : ThreadId) : IO Unit := do
  let parent ← match ← emu.engine.persistentMemory.get with
    | some parent => pure parent
    | none =>
      let parent ← nativeFromState emu (← emu.state.get)
      attachMemory emu parent
      pure parent
  let childMemory ← Jit.cloneMemory parent
  let mapped ← emu.regions.get
  -- A child that runs leaves the map of the space it was in behind.
  if (← emu.currentThreadRef.get) == child then
    emu.parkedRegions.modify (·.insert ((← emu.taskTable.get).spaceOf child) mapped)
  else
    emu.parkedRegions.modify (·.insert child mapped)
  emu.taskTable.modify (·.setSpace child child)
  emu.processMemory.modify (·.insert child childMemory)
  -- The memory of the child's state follows the clone, whatever ran since the fork. A parallel worker has
  -- it in native memory only, and the rest of the emulator expects the state to be exact.
  let state ← emu.state.get
  let memory ← if emu.engine.deferMemorySync then do
      let ⟨width, _⟩ ← cells emu state
      let (addresses, values) ← Jit.dumpMemory childMemory
      pure (.ok (Value.memory (Bap.Memory.writeSortedCells (Bap.Memory.empty width)
        ((addresses.zip values).toList.map fun cell => (BitVec.ofNat width cell.1.toNat, cell.2)))))
    else pure (Bil.lookup state.env emu.config.memory)
  match memory with
  | .ok memory =>
    emu.threadsRef.modify fun threads => threads.map fun context =>
      if context.id == child then { context with state := { env := Bil.bind context.state.env emu.config.memory memory } }
      else context
  | .error _ => pure ()
  if (← emu.currentThreadRef.get) == child then
    emu.sharedMemory.set (some parent)
    attachMemory emu childMemory

/-- The thread that runs, of a process that has the memory of another, as a child of `vfork` has, goes to memory of its own with
nothing in it, for `execve` to put a program in: the other keeps the memory and its map. What follows memory hears that what was
mapped is gone, and what was compiled of it goes, as if it were unmapped, without a copy of what the other has. -/
def leaveSharedMemory (emu : Emu) : IO Unit := do
  let current ← emu.currentThreadRef.get
  let shared ← match ← emu.engine.persistentMemory.get with
    | some shared => pure shared
    | none =>
      let shared ← nativeFromState emu (← emu.state.get)
      attachMemory emu shared
      pure shared
  let mapped ← emu.regions.get
  emu.parkedRegions.modify (·.insert ((← emu.taskTable.get).spaceOf current) mapped)
  emu.taskTable.modify (·.setSpace current current)
  let own ← Jit.createMemory #[] #[]
  emu.processMemory.modify (·.insert current own)
  for region in mapped do
    if region.data.size > 0 then
      for changed in ← emu.memoryChanged.get do changed region.address region.data.size true
      Primus.Lifted.discardRange emu.engine region.address (region.address + region.data.size - 1)
  let state ← emu.state.get
  let ⟨width, _⟩ ← cells emu state
  emu.state.set { env := Bil.bind state.env emu.config.memory (.memory (Bap.Memory.empty width)) }
  setRegions emu []
  emu.sharedMemory.set (some shared)
  attachMemory emu own

/-- A register of any thread. -/
def threadReg (emu : Emu) (id : ThreadId) (var : Bap.Var) : IO Bap.Value := do
  let contexts ← captureThreads emu
  match contexts.find? fun context => context.id == id with
  | none => throw <| IO.userError s!"unknown Emu thread {id}"
  | some context =>
    match Bil.lookup context.state.env var with
    | .ok value => pure value
    | .error error => throw <| IO.userError error

/-- Sets a register of any thread. -/
def setThreadReg (emu : Emu) (id : ThreadId) (var : Bap.Var) (value : Bap.Value) : IO Unit := do
  if (← thread emu) == id then
    setReg emu var value
  else
    if var.typ != value.type then
      throw <| IO.userError s!"register {var.name} has the wrong value type"
    saveCurrentThread emu
    emu.threadsRef.modify fun threads => threads.map fun context =>
      if context.id == id then { context with state := { env := Bil.bind context.state.env var value } }
      else context

private def dispatchSyscall (emu : Emu) : IO (Option Nat) := serialize emu <| do
  let hooks ← emu.syscallHooks.get
  if hooks.isEmpty then
    pure none
  else
    let width ← wordWidth emu
    let (numberRegister, argumentRegisters, resultRegister) := syscallRegisters emu.config.syscallAbi
    let number ← readWord emu numberRegister
    let args ← argumentRegisters.mapM (readWord emu)
    -- On o32, what is past the four registers of arguments is on the stack of the caller, at 16, as many as `fadvise64` has.
    let args ← if emu.config.syscallAbi == .mips && width == 32 then do
        let stack ← readWord emu "R29"
        let onStack ← [16, 20, 24].mapM fun offset => do
          match ← (read emu (stack + offset) 4).toBaseIO with
          | .ok bytes =>
            let bytes := if emu.config.endian == .big then bytes.toList else bytes.toList.reverse
            pure (bytes.foldl (fun value byte => value * 256 + byte.toNat) 0)
          | .error _ => pure 0
        pure (args.take 4 ++ onStack)
      else pure args
    for starts in ← emu.syscallStarts.get do starts number args
    let context := hookContext emu
    let rec go : List SyscallHook → IO (Option Nat)
      | [] => pure none
      | hook :: rest => do
        match ← hook.action context number args with
        | .returnValue value =>
          setReg emu ⟨resultRegister, .imm width, 0, false⟩ (.bits (BitVec.ofNat width value))
          pure (some value)
        | .default => go rest
    let result ← serve emu (go hooks)
    for ends in ← emu.syscallEnds.get do ends result
    if let some after := ← emu.afterSyscall.get then after
    pure result

private def dispatchIntrinsic (emu : Emu) (name : String) : IO Bool := serialize emu <| serve emu <| do
  let address ← emu.pc.get
  let hooks ← emu.intrinsicHooks.get
  let selected := hooks.filter fun hook => hook.name == "*" || hook.name == name
  let rec serve : List IntrinsicHook → IO Bool
    | [] => pure false
    | hook :: rest => do
      match ← hook.action (hookContext emu) address with
      | .proceed => pure true
      | .default => serve rest
  serve selected

/-- Where the thread that runs is. -/
def pc (emu : Emu) : IO Nat := emu.pc.get

/-- Where the thread that runs goes on from: a branch that it was in the middle of is forgotten, and the hooks there fire. -/
def setPc (emu : Emu) (address : Nat) : IO Unit := do
  emu.pc.set address
  emu.pendingRef.set none
  emu.skipCode.set none

/-- Where a thread goes on from: the next instruction that it runs is at `address`, as `setPc` does for the thread that runs. A branch that it
was in the middle of, whose delay slot it was to run, is forgotten, and the hooks of `address` fire when it runs it, even if they had for where
it was. On 32-bit ARM, whether that is Thumb is still what `ISET` of the thread says. -/
def setThreadPc (emu : Emu) (id : ThreadId) (address : Nat) : IO Unit := do
  if (← thread emu) == id then
    setPc emu address
  else
    unless (← emu.threadsRef.get).any (·.id == id) do
      throw <| IO.userError s!"unknown Emu thread {id}"
    emu.threadsRef.modify fun threads => threads.map fun context =>
      if context.id == id then { context with pc := address, pending := none, skip := none } else context

/-- Where a thread goes on from. -/
def threadPc (emu : Emu) (id : ThreadId) : IO Nat := do
  if (← thread emu) == id then emu.pc.get
  else
    match (← emu.threadsRef.get).find? (·.id == id) with
    | some context => pure context.pc
    | none => throw <| IO.userError s!"unknown Emu thread {id}"

/-- Stops the thread that runs. -/
def stop (emu : Emu) : IO Unit := emu.stopped.set true

/-- Lets the thread that runs go on. -/
def resume (emu : Emu) : IO Unit := emu.stopped.set false

/-- Whether the thread that runs is stopped. -/
def stopped (emu : Emu) : IO Bool := emu.stopped.get

/-- How many bytes from `address` may be fetched, up to `limit`, through adjacent executable regions.
Only execute permission matters: instruction fetch does not read data. -/
def fetchSpan (regions : List Region) (address limit : Nat) : Except String Nat :=
  let rec extend (fuel position : Nat) : Nat :=
    if position ≥ address + limit then limit
    else
      match fuel, lookupRegion regions position with
      | fuel + 1, some region =>
        if region.protection.executable then extend fuel (region.address + region.data.size)
        else position - address
      | _, _ => position - address
  match lookupRegion regions address with
  | none => .error s!"unmapped Emu instruction address {address}"
  | some region =>
    if !region.protection.executable then
      .error s!"non-executable Emu instruction address {address}"
    else
      .ok (extend regions.length (region.address + region.data.size))

/-- `fetchSpan`, which for an instruction inside the region that the page's last one was in is all of it. -/
private def fetchSpanOf (emu : Emu) (address limit : Nat) : IO (Except String Nat) := do
  let page := address / 4096
  if let some (lower, upper) := (← emu.fetchPages.get)[page]? then
    if lower ≤ address && address + limit ≤ upper then return .ok limit
  let regions ← regionsTouching emu address limit
  if let some region := lookupRegion regions address then
    if region.protection.executable then
      emu.fetchPages.modify (·.insert page (region.address, region.address + region.data.size))
  return fetchSpan regions address limit

private def fetch (emu : Emu) (address : Nat) : IO ByteArray := do
  try
    match ← fetchSpanOf emu address (decodeWindow emu.config) with
    | .error error => throw <| IO.userError error
    | .ok span =>
      match ← emu.engine.persistentMemory.get with
      | some memory => Jit.readMemoryRange memory (UInt64.ofNat address) span
      | none =>
        let ⟨_, memory⟩ ← cells emu (← emu.state.get)
        pure (peekBytes memory address span)
  catch error =>
    recordFault emu .fetch address
    throw error

/-- Whether a program calls an intrinsic of floating point, or `virtual-counter`, whose hook sets what the rest of the instruction reads,
to this depth of branches: those run as served programs, which go on after an intrinsic. -/
private def namesFloat : Nat → List Bil.Stmt → Bool
  | 0, _ => false
  | fuel + 1, program => program.any fun stmt =>
    match stmt with
    | .special name => (name.splitOn "ieee754").length > 1 || name == "virtual-counter"
    | .ifElse _ yes no => namesFloat fuel yes || namesFloat fuel no
    | .while _ body => namesFloat fuel body
    | _ => false

/-- Whether what a state runs next is Thumb. -/
private def isThumb (state : Bil.State) : Bool :=
  match Bil.lookup state.env ⟨"ISET", .imm 1, 0, false⟩ with
  | .ok (.bits bits) => bits.toNat == 1
  | _ => false

/-- The bytes that the engine knows code by, of the mode that it runs in: those of Thumb with a byte after them that those of ARM haven't,
so that the same bytes at an address are two blocks, and two versions of one, rather than one lifted in the other mode. -/
private def codeOfMode (thumb : Bool) (code : ByteArray) : ByteArray := if thumb then code.push 1 else code

/-- The bytes of code as they are, of those that the engine knows it by. -/
private def codeWithoutMode (thumb : Bool) (code : ByteArray) : ByteArray := if thumb then code.extract 0 (code.size - 1) else code

private def disassemblerFor (emu : Emu) (thumb : Bool) (address : Nat) :=
  match emu.config.thumbAt, emu.config.disassemblerAt with
  | some create, _ => if thumb then create address else
    match emu.config.disassemblerAt with
    | some arm => arm address
    | none => pure emu.config.disassembler
  | none, some create => create address
  | none, none => pure emu.config.disassembler

private def lift (emu : Emu) (thumb : Bool) (address : Nat) (code : ByteArray) : IO Primus.Lifted.Block := do
  let disassembler ← disassemblerFor emu thumb address
  let decoded ← disassembler.decode address code
  match decoded with
  | .error error => throw <| IO.userError s!"Emu instruction at {address}: {error}"
  | .ok insn =>
    -- An instruction that an intrinsic server serves runs as its program, which `dispatchSpecial` is sent to.
    let served : Bool ← match ← emu.intrinsicServer.get with
      | some _ => pure (namesFloat 64 insn.bil)
      | none => pure false
    if served then
      -- By a number of its own, not its address: a block that is kept, and run again as its bytes come back, runs the program it was
      -- lifted with, rather than the one lifted at that address last. One step takes the number and puts the program there.
      let id ← emu.servedPrograms.modifyGet fun programs => (programs.size, programs.insert programs.size insn.bil)
      pure ⟨insn.address, insn.next, [.special s!"served:{id}"]⟩
    else
      -- What a lifter loads again of the same bytes is loaded once, as the instruction does.
      pure ⟨insn.address, insn.next, Bil.shareLoads insn.bil⟩

/-- The program of the instruction at an address, and how many bytes it was made from at most, as it would run now, without running it or
saying that anything faulted: none if it can't be fetched or decoded. -/
def programAt (emu : Emu) (address : Nat) : IO (Option Bil.Program) := do
  let fault ← emu.lastFault.get
  let fresh ← emu.faultFresh.get
  try
    let block ← lift emu (isThumb (← emu.state.get)) address (← fetch emu address)
    match block.program with
    | [.special name] =>
      if name.startsWith "served:" then
        match (name.drop 7).toString.toNat? with
        | some served => pure ((← emu.servedPrograms.get).get? served)
        | none => pure (some block.program)
      else pure (some block.program)
    | program => pure (some program)
  catch _ =>
    emu.lastFault.set fault
    emu.faultFresh.set fresh
    pure none

/-- Where the instruction after the one at an address is, as it would be decoded now, without running it or saying that anything faulted:
none if it can't be fetched or decoded. -/
def nextInstruction (emu : Emu) (address : Nat) : IO (Option Nat) := do
  let fault ← emu.lastFault.get
  let fresh ← emu.faultFresh.get
  try
    pure (some (← lift emu (isThumb (← emu.state.get)) address (← fetch emu address)).next)
  catch _ =>
    emu.lastFault.set fault
    emu.faultFresh.set fresh
    pure none

/-- Lets go of what no pc that is kept ran as: of what was new before the first that is kept, only what was last at each pc. -/
private def TraceRing.compact (ring : TraceRing) : TraceRing :=
  let oldest := ring.count - ring.retained
  let (kept, _) := ring.code.foldl (init := (([] : List (Nat × Nat × ByteArray)), ({} : Std.HashSet Nat)))
    fun (kept, seen) version =>
      if version.1 ≥ oldest then (version :: kept, seen)
      else if seen.contains version.2.1 then (kept, seen)
      else (version :: kept, seen.insert version.2.1)
  let size := kept.length
  { ring with code := kept.reverse, codeSize := size, codeLimit := 2 * size + 64 }

/-- Whether two byte strings are the same, without unpacking them. -/
private def sameBytes (left right : ByteArray) : Bool :=
  left.size == right.size && Nat.all left.size fun index _ => left.get! index == right.get! index

/-- Notes a pc in a ring. -/
private def TraceRing.advance (ring : TraceRing) (address : Nat) : TraceRing :=
  if ring.capacity = 0 then
    { ring with back := address :: ring.back, count := ring.count + 1 }
  else if ring.retained < ring.capacity then
    { ring with back := address :: ring.back, retained := ring.retained + 1, count := ring.count + 1 }
  else
    let (front, back) := if ring.front.isEmpty then (ring.back.reverse, []) else (ring.front, ring.back)
    match front with
    | [] => { ring with back := [address], count := ring.count + 1, dropped := ring.dropped + 1 }
    | _ :: rest => { ring with front := rest, back := address :: back, count := ring.count + 1, dropped := ring.dropped + 1 }

/-- Notes a pc in a ring with the bytes that it runs as, if they may be new there. -/
private def TraceRing.push (ring : TraceRing) (address : Nat) (bytes : ByteArray) : TraceRing :=
  let same := match ring.known.get? address with
    | some known => sameBytes known bytes
    | none => false
  let ring := if same then ring
    else
      let ring := { ring with code := (ring.count, address, bytes) :: ring.code, codeSize := ring.codeSize + 1
                              known := ring.known.insert address bytes }
      if ring.capacity != 0 && ring.codeSize > ring.codeLimit then ring.compact else ring
  ring.advance address

/-- The bytes of the instruction at an address as they are now, if they may not be `known`, which they were the last time: none if they
are, and empty if it can't be fetched or decoded, without saying that anything faulted. -/
private def changedBytes (emu : Emu) (known : Option ByteArray) (address : Nat) : IO (Option ByteArray) := do
  -- What ran here before is still there, as the native memory says without making anything, which is most of the time.
  if let some known := known then
    if !known.isEmpty then
      if let some native ← emu.engine.persistentMemory.get then
        if ← Jit.memoryMatches native (UInt64.ofNat address) known then return none
  let fault ← emu.lastFault.get
  let fresh ← emu.faultFresh.get
  try
    let window ← fetch emu address
    if let some known := known then
      if !known.isEmpty && window.size ≥ known.size && sameBytes (window.extract 0 known.size) known then return none
    match ← (← disassemblerFor emu (isThumb (← emu.state.get)) address).decode address window with
    | .ok insn => pure (some (window.extract 0 (insn.next - address)))
    | .error _ => pure (some ByteArray.empty)
  catch _ =>
    emu.lastFault.set fault
    emu.faultFresh.set fresh
    pure (some ByteArray.empty)

/-- A trace with a pc of a thread noted, with what `changedBytes` said of it. -/
private def TraceState.record (state : TraceState) (thread : ThreadId) (address : Nat) (changed : Option ByteArray) : TraceState :=
  if !state.keeps thread then state else
  let note (ring : TraceRing) : TraceRing := match changed with
    | some bytes => ring.push address bytes
    | none => ring.advance address
  let state := { state with count := state.count + 1 }
  if state.options.perThread then
    let fresh : TraceRing := { capacity := state.options.pcCapacity }
    { state with rings := state.rings.alter thread fun ring => some (note (ring.getD fresh)) }
  else { state with ring := note state.ring }

/-- The ring that a pc of a thread goes in, of a trace that keeps it. -/
private def TraceState.ringOf (state : TraceState) (thread : ThreadId) : TraceRing :=
  if state.options.perThread then state.rings.getD thread { capacity := state.options.pcCapacity } else state.ring

private def recordTrace (emu : Emu) (address : Nat) : IO Unit := do
  let set ← emu.trace.get
  if !set.active then return
  let thread ← emu.currentThreadRef.get
  -- What is new at the pc, for each trace, as each knows what it was by its own ring.
  let changedFor (state : TraceState) : IO (Option ByteArray) :=
    if state.keeps thread then changedBytes emu ((state.ringOf thread).known.get? address) address else pure none
  let first ← match set.default with
    | some state => changedFor state
    | none => pure none
  let others ← set.named.mapM fun (_, _, state) => changedFor state
  serialize emu <| emu.trace.modify fun set =>
    { set with
      default := set.default.map (·.record thread address first)
      named := (set.named.zip others).map fun ((name, token, state), changed) => (name, token, state.record thread address changed) }

/-- The hooks of a code site in the middle of a native run, on the state that the run has there, `live`, as those of a step that
starts there have: whether they changed what the run goes on with, the state, where it goes or whether the thread stops, for which
the run stops there with what they left, and its hooks don't fire there again (`siteState`, `redirect`, `skipCode`); as it does where
they added or took off hooks. -/
private def hookAtSite (emu : Emu) (address : Nat) (say : IO Bil.State) : IO Bool := do
  let before ← emu.state.get
  let hooks ← emu.hookChanges.get
  -- What the run goes on with besides: the regions and what may be done there, the filter of the native memory, which a trace that
  -- starts forgets, and the code that was compiled, which a write or a change of protection discards.
  let regions ← emu.regions.get
  let filtered := (← emu.engine.memoryFilter.get).isSome
  let invalidations := (← emu.engine.statistics.get).invalidations
  -- The state there, said when a hook first reads it: a hook that reads nothing of it doesn't have it made.
  let said ← IO.mkRef (none : Option Bil.State)
  emu.state.defer do
    let live ← say
    said.set (some live)
    pure live
  -- A hook that fails leaves the state there, said while the run is still there, as it would have read it.
  try notifyCode emu address catch error =>
    let _ ← emu.state.get
    throw error
  emu.firedSites.modify (·.push address)
  let pc ← emu.pc.get
  -- Hooks that a hook added or took off are of what the run goes on with too, as what it has of the native memory's filter is of those
  -- that there were.
  let unchanged := sameObject (← emu.regions.get) regions && (!filtered || (← emu.engine.memoryFilter.get).isSome) &&
    (← emu.engine.statistics.get).invalidations == invalidations
  if pc == address && !(← emu.stopped.get) && (← emu.redirect.get).isNone && (← emu.hookChanges.get) == hooks && unchanged then
    if ← emu.state.deferred then
      emu.state.set before
      return false
    let after ← emu.state.get
    if let some live ← said.get then
      if sameObject after live then
        emu.state.set before
        return false
  let after ← emu.state.get
  emu.siteState.set (some after)
  if pc != address then emu.redirect.set (some pc) else emu.skipCode.set (some address)
  pure true

/-- The code site of a block inside a compiled range, whose first block is the step's. The hooks of a block fire there, on the state
that the run has there, and the range goes on unless they changed what it goes on with. Where that state can't be said, a block with
hooks ends the range, with the block not entered and its hooks not fired: they are the next step's, which has the state that they
read. -/
private def observeRangeCode (emu : Emu) (address : Nat) : IO Bool := do
  emu.pc.set address
  let dirty := (← emu.engine.dirtyCode.get).isSome
  let late := (← emu.rangeQuiet.get) &&
    ((← emu.hookChanges.get) != (← emu.rangeHooks.get) || (← emu.trace.get).active)
  let hooked := (← hooksNear emu address).any fun hook => hook.first ≤ address && address ≤ hook.last
  -- The hooks of a site fire there, on the state that the run has there, where that can be said, and the run goes on unless they
  -- changed what it goes on with; elsewhere the run stops before the site, for a step to fire them on its state.
  let live ← if hooked && !dirty && !late then Primus.Lifted.liveSite emu.engine address else pure none
  let stops ← match live with
    | some state => hookAtSite emu address state
    | none => pure (rangeSiteStops dirty late hooked)
  -- A range that ends at its first site has done no good: where it starts, the step runs its one instruction by itself.
  match ← emu.rangeStart.get with
  | some start =>
    emu.rangeStart.set none
    if hooked && stops then emu.watchedSteps.modify (·.insert start)
  | none => pure ()
  if stops then return true
  recordTrace emu address
  pure false

/-- The bytes that `programAt` makes a program from, as they are now, which is what says whether it still stands. -/
def codeAt (emu : Emu) (address : Nat) : IO ByteArray := do
  peek emu address (decodeWindow emu.config)

/-- How instructions run from the next one on. What was compiled stays, for if it goes back. -/
def setExecutionMode (emu : Emu) (mode : ExecutionMode) : IO Unit :=
  emu.engine.interpretOnly.set (mode == .interpret)

/-- How it runs instructions now. -/
def executionMode (emu : Emu) : IO ExecutionMode := do
  pure (if ← emu.engine.interpretOnly.get then .interpret else .jit)

/-- Gives the regions the bytes of the memory of the state. -/
def refreshRegions (emu : Emu) : IO Unit := do
  let mapped ← emu.regions.get
  let state ← emu.state.get
  let ⟨_, memory⟩ ← cells emu state
  setRegions emu (mapped.map fun region =>
    { region with data := Bap.Memory.readRegion memory region.address region.data.size })

/-- Gives the regions the bytes of the native memory, or of the state if there is none. -/
def refreshPersistentRegions (emu : Emu) : IO Unit := do
  match ← emu.engine.persistentMemory.get with
  | none => refreshRegions emu
  | some native =>
    setRegions emu <| (← regionsFromNative (← emu.regions.get) native)

/-- The regions of an address space as they are now, with what its memory has: of the one that runs, its regions, and of another, those
that it left when it was switched from, with what its own memory has now. -/
def liveRegionsOf (emu : Emu) (space : Nat) : IO (List Region) := do
  if space == (← emu.taskTable.get).spaceOf (← emu.currentThreadRef.get) then
    -- Of the native memory, if there is one, which takes what it has of them rather than how large they are.
    refreshPersistentRegions emu
    return ← emu.regions.get
  let mapped := (← emu.parkedRegions.get).getD space []
  match nativeFor (← emu.processMemory.get) (← emu.sharedMemory.get) space with
  | some memory => regionsFromNative mapped memory
  | none =>
    -- Without native memory, of the state of a thread of it, which has its memory there while another runs.
    let table ← emu.taskTable.get
    match (← emu.threadsRef.get).find? fun context => table.spaceOf context.id == space with
    | some context =>
      match Bil.lookup context.state.env emu.config.memory with
      | .ok (.memory memory) =>
        pure (mapped.map fun region => { region with data := Bap.Memory.readRegion memory region.address region.data.size })
      | _ => pure mapped
    | none => pure mapped

/-- Refreshes the regions with the bytes of the memory that threads without their own memory share. -/
def refreshSharedRegions (emu : Emu) : IO Unit := do
  let processes ← emu.processMemory.get
  let table ← emu.taskTable.get
  if !processes.contains (table.spaceOf (← emu.currentThreadRef.get)) then
    refreshPersistentRegions emu
  else
    let first := firstSpace table
    let mapped := (← emu.parkedRegions.get).getD first []
    let refreshed ← match ← emu.sharedMemory.get with
      | some native => regionsFromNative mapped native
      | none =>
        let threads ← emu.threadsRef.get
        match threads.find? fun context => !processes.contains (table.spaceOf context.id) with
        | some context =>
          let ⟨_, memory⟩ ← cells emu context.state
          pure (mapped.map fun region =>
            { region with data := Bap.Memory.readRegion memory region.address region.data.size })
        | none => pure mapped
    emu.parkedRegions.modify (·.insert first refreshed)

private def mipsWord (code : ByteArray) (address : Nat) : Option Nat :=
  if address + 4 > code.size then none
  else
    some ((List.range 4).foldl (init := 0) fun word offset =>
      word * 256 + code[address + offset]!.toNat)

private def mipsDelayed (release6 : Bool) (word : Nat) : Bool :=
  let op := (word / 2 ^ 26) % 64
  let rs := (word / 2 ^ 21) % 32
  let rt := (word / 2 ^ 16) % 32
  let funct := word % 64
  match op with
  | 0x02 | 0x03 | 0x04 | 0x05 => true
  | 0x06 | 0x07 => !release6 || rt = 0
  | 0x14 | 0x15 | 0x16 | 0x17 => !release6
  | 0x01 =>
    (if release6 then [0x00, 0x01, 0x10, 0x11]
     else [0x00, 0x01, 0x02, 0x03, 0x10, 0x11, 0x12, 0x13]).contains rt
  | 0x00 => funct = 0x08 || funct = 0x09
  | 0x11 => if release6 then rs = 0x09 || rs = 0x0D else rs = 0x08
  | _ => false

private def mipsLikely (release6 : Bool) (word : Nat) : Bool :=
  let op := (word / 2 ^ 26) % 64
  let rs := (word / 2 ^ 21) % 32
  let rt := (word / 2 ^ 16) % 32
  !release6 && match op with
  | 0x14 | 0x15 | 0x16 | 0x17 => true
  | 0x01 => [0x02, 0x03, 0x12, 0x13].contains rt
  | 0x11 => rs = 0x08 && rt &&& 2 != 0
  | _ => false

private def mipsCompact (word : Nat) : Bool :=
  let op := (word / 2 ^ 26) % 64
  let rs := (word / 2 ^ 21) % 32
  let rt := (word / 2 ^ 16) % 32
  match op with
  | 0x06 | 0x07 | 0x16 | 0x17 => rt != 0
  | 0x08 | 0x18 => true
  | 0x36 | 0x3E => rs != 0
  | _ => false

private def delayFor (emu : Emu) (address : Nat) : IO DelayKind := do
  match emu.config.delayPolicy with
  | .none => pure .none
  | .mips release6 =>
    let code ← fetch emu address
    -- `mipsWord` reads the most significant byte first
    let code := if emu.config.endian == .little then ByteArray.mk (code.extract 0 4).toList.reverse.toArray else code
    match mipsWord code 0 with
    | none => pure .none
    | some word =>
      if mipsLikely release6 word then pure .likely
      else if mipsDelayed release6 word then pure .delayed
      else if release6 && mipsCompact word then pure .forbidden
      else pure .none

/-- Runs a program in the state of the emulator, where lifted code can't go past an intrinsic. A loop has to end in `fuel`
turns. What it writes to memory is in the state, and native memory follows it after. -/
private def runServed (emu : Emu) (serve : String → List Nat → Option (Nat × Nat)) (program : Bil.Program) : IO Unit := do
  let evaluate (expression : Bil.Exp) : IO Bap.Value := do
    match Bil.evalExp (← emu.state.get).env expression with
    | .ok value => pure value
    | .error error => throw <| IO.userError error
  let wroteMemory ← IO.mkRef false
  let operands ← IO.mkRef ([] : List Nat)
  let rec go : Nat → Bil.Program → IO Unit
    | 0, _ => throw <| IO.userError "a served program ran out of fuel"
    | _ + 1, [] => pure ()
    | fuel + 1, stmt :: rest => do
      match stmt with
      | .move var value =>
        let value ← evaluate value
        if var == emu.config.memory then wroteMemory.set true
        if var.name.str.startsWith "intrinsic:x" then
          match Value.asBits value with
          | .ok bits => operands.modify (· ++ [bits.2.toNat])
          | .error error => throw <| IO.userError error
        emu.state.modify fun state => { env := Bil.bind state.env var value }
      | .special name =>
        let env := (← emu.state.get).env
        let named := (← emu.intrinsicName.get) env name
        let inputs ← operands.get
        let (controlled, finished) := (← emu.intrinsicControls.get) env named
        match serve named (controlled inputs) with
        | some (width, bits) =>
          let bits := finished bits
          operands.set []
          let raises ← emu.intrinsicRaises.get
          emu.state.modify fun state =>
            let env := Bil.bind state.env ⟨"intrinsic:y0", .imm width, 0, false⟩ (.bits (BitVec.ofNat width bits))
            { env := (raises env named inputs bits).foldl (fun env update => Bil.bind env update.1 update.2) env }
        | none =>
          operands.set []
          if !(← dispatchIntrinsic emu name) then
            throw <| IO.userError s!"nothing serves the intrinsic {name}"
      | .ifElse condition yes no =>
        match Value.asBits (← evaluate condition) with
        | .ok bits => go fuel (if bits.2.toNat != 0 then yes else no)
        | .error error => throw <| IO.userError error
      | .while condition body =>
        match Value.asBits (← evaluate condition) with
        | .ok bits =>
          if bits.2.toNat != 0 then
            go fuel body
            go fuel [stmt]
        | .error error => throw <| IO.userError error
      | .jmp target =>
        match Value.asBits (← evaluate target) with
        | .ok bits => emu.pc.set bits.2.toNat
        | .error error => throw <| IO.userError error
      | .cpuExn number => throw <| IO.userError s!"CPU exception {number}"
      if let .jmp _ := stmt then pure () else go fuel rest
  go 1048576 program
  if ← wroteMemory.get then
    match Bil.lookup (← emu.state.get).env emu.config.memory with
    | .ok memory => setReg emu emu.config.memory memory
    | .error error => throw <| IO.userError error

private def dispatchSpecial (emu : Emu) (name : String) : IO Bool := do
  if name.startsWith "served:" then
    let some address := (name.drop 7).toString.toNat? | throw <| IO.userError s!"bad special {name}"
    let some serve := ← emu.intrinsicServer.get | throw <| IO.userError "no intrinsic server"
    let some program := (← emu.servedPrograms.get).get? address | throw <| IO.userError s!"no served program {address}"
    runServed emu serve program
    pure true
  else if name == "syscall" || name == "svc" || (name == "interrupt" && emu.config.syscallAbi == .x86_32) then
    match ← dispatchSyscall emu with
    | some _ => pure true
    | none => dispatchIntrinsic emu name
  else
    dispatchIntrinsic emu name

/-- The references of a step that may run a range. -/
@[inline] private def rangeCells (emu : Emu) : RangeCells IO where
  budget := emu.budget.get
  setBudget := emu.budget.set
  lastBudget := emu.lastBudget.get
  setLastBudget := emu.lastBudget.set
  chained := emu.engine.chained.get
  setChained := emu.engine.chained.set
  watched := fun address => do pure ((← emu.watchedSteps.get).contains address)
  watch := fun address => emu.watchedSteps.modify (·.insert address)
  restarting := emu.restarting.get
  setRestarting := emu.restarting.set
  pc := emu.pc.get
  pending := emu.pendingRef.get
  accessHooks := do pure !((← emu.readHooks.get).isEmpty && (← emu.writeHooks.get).isEmpty)
  deferred := emu.engine.deferMemorySync

/-- A run of the instruction at `address` that may chain as many as `budget` after it, on the state of the emulator. -/
private def runRange (emu : Emu) (address budget : Nat) : IO (Nat × Bil.Effect) := do
  ensureMemoryFilter emu
  let state ← emu.state.get
  let quiet ← rangeIsQuiet emu
  emu.rangeQuiet.set quiet
  emu.rangeHooks.set (← emu.hookChanges.get)
  emu.rangeStart.set (some address)
  -- A range is observed if a trace is kept, or a code hook is in what it has: one elsewhere is for a step that goes there, as
  -- Unicorn has a hook cost what runs where it is.
  let observedIn (spans : List (Nat × Nat)) : IO Bool := do
    if (← emu.trace.get).active then return true
    let hooks ← emu.hooks.get
    let observed := hooks.any fun hook => spans.any fun (low, high) => hook.first ≤ max low high && min low high ≤ hook.last
    emu.rangeQuiet.set !observed
    pure observed
  -- What only Lean's bookkeeping would come between goes on in native code from range to range: nothing observes code, no address is
  -- one to step at alone, and no branch waits for its delay slot; nor where code may run as ARM and as Thumb, as the chain goes from
  -- range to range by the pc alone, not the mode.
  let chainable := quiet && (← emu.watchedSteps.get).isEmpty && (← emu.pendingRef.get).isNone && emu.config.thumbAt.isNone
  -- Of the mode that it runs in, which the bytes are known by too.
  let thumb := isThumb state
  emu.siteState.set none
  emu.firedSites.set #[]
  -- A run that fails is taken back and run again, a step at a time from its start: the hooks of its sites that fired as it ran don't
  -- fire again there (`notifyCode`).
  let result ← try
      Primus.Lifted.runBlockObserved emu.engine (fun target => do pure (codeOfMode thumb (← fetch emu target)))
        (fun target code => lift emu thumb target (codeWithoutMode thumb code)) state address
        (some (notifyMemory emu)) (some (observeRangeCode emu)) (!quiet) budget observedIn chainable
    catch error =>
      emu.replaySites.set (← emu.firedSites.get).toList
      emu.firedSites.set #[]
      throw error
  emu.firedSites.set #[]
  Primus.Lifted.flushDirtyRange emu.engine
  match ← emu.siteState.get with
  | none => emu.state.set result.state
  | some hooked =>
    -- The hooks of a site changed what the run went on with: their state, with the memory that the run left, or, where they wrote
    -- memory too, with the native memory, which has both.
    emu.siteState.set none
    let wrote := match Bil.lookup hooked.env emu.config.memory, Bil.lookup state.env emu.config.memory with
      | .ok left, .ok right => !sameObject left right
      | _, _ => false
    match Bil.lookup result.state.env emu.config.memory, wrote with
    | .ok memory, false => emu.state.set { env := Bil.bind hooked.env emu.config.memory memory }
    | _, _ =>
      emu.state.set hooked
      synchronizePersistentMemory emu
  emu.lastFault.set none
  pure (result.next, result.effect)

/-- The instruction at `address`, on the state of the emulator. -/
private def executeBlock (emu : Emu) (address : Nat) : IO (Nat × Bil.Effect) :=
  executeRangeM (rangeCells emu) (runRange emu) address

/-- The references that say where the thread of the emulator is. -/
@[inline] private def controlCells (emu : Emu) : ControlCells IO where
  stopped := emu.stopped.get
  setStopped := emu.stopped.set
  pc := emu.pc.get
  skip := emu.skipCode.get
  setSkip := emu.skipCode.set
  pending := emu.pendingRef.get
  setControl := fun pc pending => do
    match ← emu.redirect.get with
    | some target =>
      emu.redirect.set none
      emu.pc.set target
      emu.pendingRef.set none
    | none =>
      emu.pc.set pc
      emu.pendingRef.set pending

/-- A worker of a parallel round stops at an instruction that has to be atomic or that is a fence, as at a breakpoint: `stepM` doesn't run it, and doesn't
fire the hooks of the pc again. What it can't fetch or lift isn't that, and the step says what is wrong with it. -/
private def gateAtomic (emu : Emu) (address : Nat) : IO Unit := do
  if !(← emu.atomicGated.get) then return
  if (← emu.pc.get) != address || (← emu.stopped.get) then return
  try
    let code ← fetch emu address
    let thumb := isThumb (← emu.state.get)
    let classify : IO Bool := do
      let block ← lift emu thumb address code
      let atomic ← if Primus.Lifted.atomicProgram block.program then pure true
        else if !block.program.isEmpty then pure false
        else
          match ← (← disassemblerFor emu thumb address).decode address code with
          | .ok insn => pure (Primus.Lifted.fenceText insn.asm)
          | .error _ => pure false
      emu.atomicSites.modify (·.insert address (code, atomic))
      pure atomic
    let atomic ← match (← emu.atomicSites.get)[address]? with
      | some (bytes, atomic) => if bytes == code then pure atomic else classify
      | none => classify
    if atomic then
      emu.atomicReached.set true
      emu.stopped.set true
  catch _ =>
    emu.lastFault.set none

/-- The references of the emulator as the environment of `stepM`. -/
@[inline] private def stepOps (emu : Emu) : StepOps IO (Snapshot × TraceSet) :=
  stepOpsOf (controlCells emu) (fun address => do notifyCode emu address; gateAtomic emu address)
    (do
      beginStepMemory emu
      -- Nothing of this step is counted yet, so that one that fails before it ran takes back nothing.
      emu.stepRetired.set 0
      pure (← snapshotBlock emu, ← emu.trace.get)) (delayFor emu)
    (recordTrace emu)
    (fun address => do
      let result ← executeBlock emu address
      emu.nextPc.set result.1
      -- A step that could chain ran as many after its first as it says.
      let chained ← if (← emu.lastBudget.get) > 0 then emu.engine.chained.get else pure 0
      emu.stepRetired.set (1 + chained)
      emu.retired.modify (· + 1 + chained)
      pure result)
    (fun name => do
      let handled ← dispatchSpecial emu name
      -- Not served, the step stops where it started, and runs again from there: what it counted is counted then.
      unless handled do emu.retired.modify (· - (← emu.stepRetired.get))
      pure handled)
    (fun before => do
      emu.retired.modify (· - (← emu.stepRetired.get))
      emu.stepRetired.set 0
      rollbackBlock emu before.1
      forgetMemoryFilter emu
      emu.trace.set before.2)
    (fun pc => do
      match ← emu.lastFault.get with
      | some fault => emu.lastFault.set (some { fault with pc })
      | none => pure ())

/-- One instruction, whatever a run that a hook stopped had left for its next step. -/
def step (emu : Emu) : IO Bool := do
  emu.budget.set 0
  stepM (ε := IO.Error) (stepOps emu)

/-- Up to `maxSteps` instructions. Those of a compiled range count as well, and it stops where they run out. A fault in a
range leaves everything as single steps do. A worker of a parallel round leaves that to the rollback of its round. -/
def run (emu : Emu) (maxSteps : Nat := 100000) : IO Nat :=
  if rangeLimitOf emu.config ≤ 1 then
    runM (stepM (ε := IO.Error) (stepOps emu)) maxSteps 0
  else
    runPreciseM (runChainedM (restartM (stepM (ε := IO.Error) (stepOps emu)) (rangeRestartM (rangeCells emu))) (rangeAllowM (rangeCells emu))
        (rangeCells emu).chained maxSteps maxSteps 0)
      (step emu) (rangeAgainM (rangeCells emu)) (maxSteps + 1)

/-- What running some instructions takes, the first time and again: how many ran, how long they took and so how many a second, how many
were lifted and how long that took, of each time, and the most memory of the host that the process has had, in KiB, as Linux says it
(`VmHWM`), if it does. Lean frees memory as it goes, by counting references, so there is no time of a collector to say. -/
structure Measurement where
  instructions : Nat
  coldNanos : Nat
  warmNanos : Nat
  coldLifts : Nat
  warmLifts : Nat
  coldLiftNanos : Nat
  warmLiftNanos : Nat
  peakResidentKiB : Option Nat
  deriving Repr

private def perSecond (instructions nanos : Nat) : Nat := if nanos == 0 then 0 else instructions * 1000000000 / nanos

def Measurement.coldPerSecond (measurement : Measurement) : Nat := perSecond measurement.instructions measurement.coldNanos
def Measurement.warmPerSecond (measurement : Measurement) : Nat := perSecond measurement.instructions measurement.warmNanos

def Measurement.text (measurement : Measurement) : String :=
  s!"instructions: {measurement.instructions}\n" ++
  s!"cold: {measurement.coldPerSecond}/s, {measurement.coldLifts} lifts in {measurement.coldLiftNanos / 1000} us\n" ++
  s!"warm: {measurement.warmPerSecond}/s, {measurement.warmLifts} lifts in {measurement.warmLiftNanos / 1000} us\n" ++
  s!"peak resident: {(measurement.peakResidentKiB.map (s!"{·} KiB")).getD "unknown"}"

/-- The most memory of the host that this process has had, in KiB, as Linux says it, if it does. -/
def peakResidentKiB : IO (Option Nat) := do
  try
    let status ← IO.FS.readFile "/proc/self/status"
    pure <| (status.splitOn "\n").findSome? fun line =>
      if line.startsWith "VmHWM:" then ((line.drop 6).trimAscii.toString.splitOn " ").head?.bind (·.toNat?) else none
  catch _ => pure none

/-- Runs at most `steps` instructions from where the emulator is, twice: the first time, with whatever it has lifted already, and again
from the same place, by a snapshot, with what the first lifted, which a restore keeps. It is left where the second run ended. -/
def measure (emu : Emu) (steps : Nat) : IO Measurement := do
  let saved ← snapshot emu
  let once : IO (Nat × Nat × Nat × Nat) := do
    let before ← Primus.Lifted.stats emu.engine
    let start ← IO.monoNanosNow
    let ran ← run emu steps
    let took := (← IO.monoNanosNow) - start
    let after ← Primus.Lifted.stats emu.engine
    pure (ran, took, after.lifts - before.lifts, after.liftNanos - before.liftNanos)
  let (instructions, coldNanos, coldLifts, coldLiftNanos) ← once
  restore emu saved
  let (_, warmNanos, warmLifts, warmLiftNanos) ← once
  pure { instructions, coldNanos, warmNanos, coldLifts, warmLifts, coldLiftNanos, warmLiftNanos
         peakResidentKiB := ← peakResidentKiB }

private def switchNextThread (emu : Emu) : IO Bool := do
  saveCurrentThread emu
  let current ← thread emu
  -- As `scheduleLoop` has it: a thread blocked where it waits, or over, isn't one to run, whatever its stopped flag
  -- says, or it would run from after the call that blocked it as if the call had returned.
  let table ← emu.taskTable.get
  match pickNext ((← emu.threadsRef.get).filter fun context => runnableIn table context.id) current with
  | some id =>
    switchThread emu id
    pure true
  | none => pure !(← stopped emu)

/-- Turns of `quantum` instructions until a thread stops. `runProcesses` runs this between what it has to do when one stops.
A turn that the fuel ended goes on from there the next time, so that where the fuel runs out, as where a run stops to save itself,
isn't something that the threads can see. -/
def runPreemptive (emu : Emu) (quantum : Nat := 100) (fuel : Nat := 100000) : IO Nat := do
  if quantum = 0 then
    throw <| IO.userError "Emu thread quantum must be positive"
  let carried ← emu.turnUsed.get
  emu.turnUsed.set 0
  -- The fuel ran out at the very end of a turn, where the next thread would have come.
  if carried ≥ quantum then
    unless ← switchNextThread emu do
      return 0
  let taken ← IO.mkRef (if carried ≥ quantum then 0 else carried)
  let turn ← IO.mkRef 0
  let total ← preemptiveM
    (fun count => do
      let before ← taken.get
      taken.set 0
      let steps ← run emu (min count (quantum - before))
      turn.set (before + steps)
      pure steps)
    (stopped emu) (switchNextThread emu) quantum fuel (fuel + 1) fuel 0
  if total == fuel && !(← stopped emu) then emu.turnUsed.set (← turn.get)
  return total

private def workerMemory (emu : Emu) (context : ThreadContext) (fallback : Jit.Memory) : IO Jit.Memory := do
  let memories ← emu.processMemory.get
  pure (memories.getD (← spaceOf emu context.id) fallback)

private def resumeParallelWorker (emu : Emu) (context : ThreadContext) (shared : Jit.Memory) : IO Emu := do
  let existing ← emu.parallelWorkers.get
  let engine ← match existing.find? fun worker => worker.1 = context.id with
    | some (_, engine) => pure engine
    | none =>
      let engine ← createEngine emu.config true
      -- It is counted in the profile that is kept, if one is.
      if (← emu.engine.profile.get).isSome then engine.profile.set (some {})
      pure engine
  let memory ← workerMemory emu context shared
  -- It writes for a round, which isn't a step, and a round takes itself back.
  Jit.endMemoryStep memory
  engine.persistentMemory.set (some memory)
  engine.persistentVariable.set (some emu.config.memory)
  -- Workers of the space of the thread that runs share its map, and those of another have that space's.
  let table ← emu.taskTable.get
  let space := table.spaceOf context.id
  let regions ← if space == table.spaceOf (← emu.currentThreadRef.get) then pure emu.regions
    else IO.mkRef ((← emu.parkedRegions.get).getD space (← emu.regions.get))
  -- What it remembers of a map is of that map.
  let fetchPages ← if space == table.spaceOf (← emu.currentThreadRef.get) then pure emu.fetchPages else IO.mkRef {}
  pure {
    emu with
    engine
    regions
    fetchPages
    regionIndex := ← if space == table.spaceOf (← emu.currentThreadRef.get) then pure emu.regionIndex else IO.mkRef none
    mappingTop := ← IO.mkRef none
    -- What it loaded exclusively before the round may change in it, as when a thread is switched to.
    state := ← StateCell.new { env := clearMonitor emu.config context.state.env }
    stepRetired := ← IO.mkRef 0
    pc := ← IO.mkRef context.pc
    stopped := ← IO.mkRef context.stopped
    currentThreadRef := ← IO.mkRef context.id
    trace := ← IO.mkRef {}
    lastFault := ← IO.mkRef none
    skipCode := ← IO.mkRef context.skip
    suppressed := ← IO.mkRef []
    pendingRef := ← IO.mkRef context.pending
    journal := some (← IO.mkRef [])
    lastBudget := ← IO.mkRef 0
    rangeQuiet := ← IO.mkRef false
    hookChanges := ← IO.mkRef 0
    rangeHooks := ← IO.mkRef 0
    memoryFilterStale := ← IO.mkRef true
    memoryFilterHeard := ← IO.mkRef (true, true)
    budget := ← IO.mkRef 0
    restarting := ← IO.mkRef false
    rangeStart := ← IO.mkRef none
    nextPc := ← IO.mkRef context.pc
    redirect := ← IO.mkRef none
    siteState := ← IO.mkRef none
    firedSites := ← IO.mkRef #[]
    replaySites := ← IO.mkRef []
    atomicGated := ← IO.mkRef true
    atomicReached := ← IO.mkRef false
  }

/-- How many instructions a thread may run alone from an exclusive load to its store. Past that its store fails, which a guest goes
back from, as it may on a machine. -/
private def exclusiveLimit : Nat := 64

/-- Runs what a worker stopped at, with every other worker stopped: then nothing can come between its load and its store, and what it
loaded exclusively stays so up to its exclusive store. -/
private def runAtomic (worker : Emu) : IO Nat := do
  worker.atomicReached.set false
  worker.stopped.set false
  worker.atomicGated.set false
  let held : IO Bool := do
    match memoryWidth worker.config with
    | .error _ => pure false
    | .ok width =>
      match Bil.lookup (← worker.state.get).env (exclusiveMonitor width) with
      | .ok (.bits value) => pure (value.toNat != 0)
      | _ => pure false
  let rec go : Nat → Nat → IO Nat
    | 0, total => pure total
    | fuel + 1, total => do
      if !(← step worker) then pure total
      else if ← held then go fuel (total + 1)
      else pure (total + 1)
  let total ← go exclusiveLimit 0
  if ← held then worker.state.modify fun state => { env := clearMonitor worker.config state.env }
  worker.atomicGated.set true
  pure total

/-- `memory` with the bytes of `native` at the written ranges. -/
private def applyJournal {width : Nat} (memory : Bap.Memory width) (native : Jit.Memory)
    (journal : List (Nat × Nat)) : IO (Bap.Memory width) :=
  applyJournalM (fun address => Jit.readMemory native (UInt64.ofNat address)) memory journal

/-- Workers write to native memories and not to their states, so that the memory of the states follows
after the round. Afterwards it is exact again, which a rollback, and anything else that reads the state's
memory, relies on. -/
private def synchronizeRound (emu : Emu) (merged : List ThreadContext)
    (workers : List (ThreadContext × Emu)) (shared : Jit.Memory) : IO (List ThreadContext) := do
  let processes ← emu.processMemory.get
  let table ← emu.taskTable.get
  let memoryVar := emu.config.memory
  let writesIn (inSpace : ThreadId → Bool) : IO (List (Nat × Nat)) :=
    workers.foldlM (init := []) fun writes worker =>
      match worker.2.journal with
      | some journal => if inSpace worker.1.id then do pure ((← journal.get) ++ writes) else pure writes
      | none => pure writes
  -- One memory value for all threads of the first address space.
  let sharedValue ← (merged.find? fun context => !processes.contains (table.spaceOf context.id)).mapM fun context => do
    let ⟨width, memory⟩ ← cells emu context.state
    let writes ← writesIn fun id => !processes.contains (table.spaceOf id)
    let memory ← applyJournal memory shared writes
    pure (Value.memory (addressWidth := width) memory)
  merged.mapM fun context => do
    let space := table.spaceOf context.id
    match processes.get? space with
    | some native =>
      let ⟨_, memory⟩ ← cells emu context.state
      let memory ← applyJournal memory native (← writesIn fun id => table.spaceOf id == space)
      pure { context with state := { env := Bil.bind context.state.env memoryVar (.memory memory) } }
    | none =>
      match sharedValue with
      | some value => pure { context with state := { env := Bil.bind context.state.env memoryVar value } }
      | none => pure context

/-- A round of `quantum` instructions of each thread that can run, each on a thread of the host, which stops at what has to be atomic
and runs it alone, and is taken back as a whole if a thread of it fails. With one thread that can run, it is `runPreemptive`. It says
how many instructions ran. -/
def runPreemptiveParallel (emu : Emu) (quantum : Nat := 100) : IO Nat := do
  if quantum = 0 then
    throw <| IO.userError "Emu thread quantum must be positive"
  -- A round is turns of its own, and goes on from no other.
  emu.turnUsed.set 0
  if (← emu.parallelLock.get).isNone then
    emu.parallelLock.set (some (← Std.BaseMutex.new))
  let contexts ← captureThreads emu
  let active := activeThreads contexts
  if active.length ≤ 1 then
    -- A stopped thread does not hold up the others of a parallel round.
    match active with
    | [only] => if only.id != (← thread emu) then switchThread emu only.id
    | _ => pure ()
    let total ← runPreemptive emu quantum quantum
    emu.turnUsed.set 0
    pure total
  else
    emu.threadControl.set {}
    roundM (ε := IO.Error) (snapshot emu) (restore emu)
      (do
        let current ← emu.currentThreadRef.get
        let processes ← emu.processMemory.get
        let attached ← emu.engine.persistentMemory.get
        let parked ← emu.sharedMemory.get
        let table ← emu.taskTable.get
        let shared ← match (if processes.contains (table.spaceOf current) then parked else attached) with
          | some memory => pure memory
          | none =>
            match contexts.find? fun context => !processes.contains (table.spaceOf context.id) with
            | some context => nativeFromState emu context.state
            | none => nativeFromState emu (← emu.state.get)
        let workers ← active.mapM fun context => do
          let worker ← resumeParallelWorker emu context shared
          pure (context, worker)
        pure (current, shared, workers))
      (fun (_, _, workers) => do
        -- Workers need threads of their own: once the task manager shuts down, nothing runs queued
        -- tasks, and waiting for one would block the process exit forever.
        let tasks ← workers.tail.mapM fun worker => IO.asTask (prio := .dedicated) (run worker.2 quantum)
        -- The first worker runs here, which saves a thread each round.
        let first ← (workers.head?.elim (pure 0) fun worker => run worker.2 quantum).toBaseIO
        -- Every worker finishes before the round is judged, so none outlives a rollback.
        let results ← tasks.mapM fun task => IO.wait task
        let results := first :: results
        -- With every worker stopped, what they stopped at runs, one at a time. A round that failed is undone anyway.
        if results.any (fun result => match result with | .error _ => true | .ok _ => false) then
          pure results
        else
          (workers.zip results).mapM fun (worker, result) => do
            if !(← worker.2.atomicReached.get) then pure result
            else
              match ← (runAtomic worker.2).toBaseIO, result with
              | .ok more, .ok steps => pure (.ok (steps + more))
              | .error error, _ => pure (.error error)
              | _, other => pure other)
      (fun (_, _, workers) => do
        -- The fault of the first failing worker, whose state the rollback discards.
        let faults ← workers.filterMapM fun worker => worker.2.lastFault.get
        if let some fault := faults.head? then emu.lastFault.set (some fault))
      (fun (current, shared, workers) => do
        let statistics ← workers.mapM fun worker => Primus.Lifted.stats worker.2.engine
        let previous ← emu.engine.statistics.get
        emu.engine.statistics.set (statistics.foldl (init := previous) fun total current => {
          cacheHits := total.cacheHits + current.cacheHits
          lifts := total.lifts + current.lifts
          liftNanos := total.liftNanos + current.liftNanos
          nativeCompilations := total.nativeCompilations + current.nativeCompilations
          nativeRuns := total.nativeRuns + current.nativeRuns
          interpretedRuns := total.interpretedRuns + current.interpretedRuns
          compileMs := total.compileMs + current.compileMs
          versionSaves := total.versionSaves + current.versionSaves
          versionHits := total.versionHits + current.versionHits
          invalidations := total.invalidations + current.invalidations
          evictions := total.evictions + current.evictions
          graphBlocks := total.graphBlocks + current.graphBlocks
          optimized := total.optimized + current.optimized
          entriesReused := total.entriesReused + current.entriesReused
        })
        let control ← emu.threadControl.get
        let workerResults ← workers.mapM fun worker => do
          pure ({
            id := worker.1.id
            state := ← worker.2.state.get
            pc := ← worker.2.pc.get
            stopped := ← worker.2.stopped.get
            pending := ← worker.2.pendingRef.get
            skip := ← worker.2.skipCode.get
          } : WorkerResult)
        let merged := mergeRound contexts (← emu.threadsRef.get) workerResults control
        let merged ← synchronizeRound emu merged workers shared
        let table ← emu.taskTable.get
        for worker in workers do
          let space := table.spaceOf worker.1.id
          if space != table.spaceOf current then
            let mapped ← worker.2.regions.get
            emu.parkedRegions.modify (·.insert space mapped)
        emu.threadsRef.set merged
        match merged.find? fun context => context.id = current with
        | some context =>
          emu.state.set context.state
          emu.pc.set context.pc
          emu.stopped.set context.stopped
          emu.pendingRef.set context.pending
          emu.skipCode.set context.skip
        | none => pure ()
        match (← emu.processMemory.get).get? (← spaceOf emu current) with
        | some native =>
          emu.sharedMemory.set (some shared)
          attachMemory emu native
        | none => attachMemory emu shared
        emu.parallelWorkers.set (workers.map fun worker => (worker.1.id, worker.2.engine))
        let _ ← switchNextThread emu
        pure ())

/-- Steps until the pc is `address`, or the thread stops, up to `fuel` steps, and says how many it took. -/
def runUntil (emu : Emu) (address : Nat) (fuel : Nat := 100000) : IO Nat := do
  let rec loop (remaining : Nat) (total : Nat) : IO Nat :=
    match remaining with
    | 0 => throw <| IO.userError "Emu run-until fuel exhausted"
    | remaining + 1 => do
      if (← pc emu) == address then
        pure total
      else if ← step emu then
        loop remaining (total + 1)
      else pure total
  loop fuel 0

private def restoreRegisters (emu : Emu) (saved : Snapshot) : IO Unit := do
  let current ← emu.state.get
  let memory := current.env.filter fun binding => binding.1 == emu.config.memory
  emu.state.set { env := memory ++ saved.state.env }
  emu.pc.set saved.pc
  emu.stopped.set saved.stopped
  emu.pendingRef.set saved.pending

/-- The stack pointer after an x86-64 push, which wraps like the hardware. -/
def stackAfterPush (sp : Nat) : Nat := (sp + 2 ^ 64 - 8) % 2 ^ 64

private def callAbi : SyscallAbi → List String × String × String × Bool
  | .riscv => (["X10", "X11", "X12", "X13", "X14", "X15", "X16", "X17"], "X1", "X10", false)
  | .aarch64 => (["X0", "X1", "X2", "X3", "X4", "X5", "X6", "X7"], "X30", "X0", false)
  | .mips => (["R4", "R5", "R6", "R7", "R8", "R9", "R10", "R11"], "R31", "R2", false)
  | .powerpc | .powerpc64 => (["R3", "R4", "R5", "R6", "R7", "R8", "R9", "R10"], "LR", "R3", false)
  | .x86_32 => ([], "", "EAX", true)
  | .arm => (["R0", "R1", "R2", "R3"], "LR", "R0", false)
  | .x86_64 => (["RDI", "RSI", "RDX", "RCX", "R8", "R9"], "", "RAX", true)

/-- Calls a function with these arguments, by the convention of the target, until it returns to `returnTo`, and gives its result. Its
registers go back after; what it did to memory stays. Registers are of the width of the target, and on i386 the arguments are on the
stack, the last first, under where it returns to. -/
def call (emu : Emu) (address returnTo : Nat) (args : List UInt64) (fuel : Nat := 100000) :
    IO Bap.Value := do
  let (arguments, link, result, stackReturn) := callAbi emu.config.syscallAbi
  let width ← wordWidth emu
  let word := width / 8
  let onStack := emu.config.syscallAbi matches .x86_32
  if !onStack && args.length > arguments.length then
    throw <| IO.userError "Emu.call has too many integer arguments for the target ABI"
  let saved ← snapshot emu
  let skipped ← emu.skipCode.get
  let bytesOf (value : Nat) : ByteArray := ByteArray.mk ((List.range word).map fun index => UInt8.ofNat (value / 256 ^ index % 256)).toArray
  try
    if !onStack then
      (List.range args.length).forM fun index => do
        setReg emu ⟨arguments[index]!, .imm width, 0, false⟩ (.bits (BitVec.ofNat width args[index]!.toNat))
    if stackReturn then
      let pointer := if width == 64 then "RSP" else "ESP"
      let pushed := if onStack then args.map (·.toNat) else []
      let sp := ((← readWord emu pointer) + 2 ^ width - word * (pushed.length + 1)) % 2 ^ width
      write emu sp (pushed.foldl (fun out value => out ++ bytesOf value) (bytesOf returnTo))
      setReg emu ⟨pointer, .imm width, 0, false⟩ (.bits (BitVec.ofNat width sp))
    else
      setReg emu ⟨link, .imm width, 0, false⟩ (.bits (BitVec.ofNat width returnTo))
    setPc emu address
    let _ ← runUntil emu returnTo fuel
    let reached ← pc emu
    if reached != returnTo then
      throw <| IO.userError s!"Emu.call stopped before returning at {reached}"
    let result ← reg emu ⟨result, .imm width, 0, false⟩
    restoreRegisters emu saved
    emu.skipCode.set skipped
    pure result
  catch error =>
    restoreRegisters emu saved
    emu.skipCode.set skipped
    throw error

/-- Decoding with the semantics loaded once. `lift` decodes at each address, which is the base of the bytes it
fetched, and loading the semantics takes far longer than all that follows it. -/
private def decodeAt (decode : Nat → Nat → ByteArray → IO Disasm.Insn) (base address : Nat) (data : ByteArray) :
    IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← decode base address data))
  catch error =>
    pure (.error (toString error))

/-- A decoder that has a word of 4 bytes that it can't decode, but that `undefined` says the architecture has no instruction of, as an
instruction that raises the exception of undefined instructions, which the semantics call `undefined-instruction`, rather than one that
can't be run. What the decoder is, and what is proved of it, is as it was. -/
def withUndefined (endian : Endian) (undefined : Nat → Bool) (disassembler : Disasm.Disassembler) (base : Nat) : Disasm.Disassembler :=
  { disassembler with
    decode := fun address data => do
      match ← disassembler.decode address data with
      | .ok insn => pure (.ok insn)
      | .error error =>
        let offset := address - base
        if address < base || data.size < offset + 4 then return .error error
        let bytes := (List.range 4).map fun index => data[offset + index]!.toNat
        let word := (match endian with | .big => bytes | .little => bytes.reverse).foldl (fun word byte => word * 256 + byte) 0
        if !undefined word then return .error error
        let hex := String.mk (Nat.toDigits 16 word)
        let insn : Disasm.Insn :=
          { address := address, size := 4, asm := ".inst 0x" ++ hex, flow := .normal, bil := [.special "undefined-instruction"] }
        pure (.ok insn) }

/-- What is at `address` compiled now, rather than as it runs (`Config.compileAtLoad`). -/
def compileAhead (emu : Emu) (address : Nat) : IO Unit := do
  let thumb := isThumb (← emu.state.get)
  Primus.Lifted.prepareAhead emu.engine (fun target => do pure (codeOfMode thumb (← fetch emu target)))
    (fun target code => lift emu thumb target (codeWithoutMode thumb code)) address

/-- An emulator that compiles what is at its entry as it is made, if its configuration says so. -/
private def loaded (emu : Emu) (entry : Nat) : IO Emu := do
  -- An entry where no code is mapped yet is left to the run, which says what is wrong with it.
  let mapped := (← emu.regions.get).any fun region =>
    region.protection.executable && region.address ≤ entry && entry < region.address + region.data.size
  if emu.config.compileAtLoad && mapped then compileAhead emu entry
  pure emu

/-- The decoders at each base for RISC-V 64, which all share their semantics. -/
def riscv64Decoders : IO (Nat → IO Disasm.Disassembler) := do
  let environment ← Target.LLVMLift.riscvEnvironment
  pure fun base => pure
    { name := "riscv64-llvm-primus", decode := decodeAt (Target.LLVMLift.decodeRISCVWith environment) base }

/-- An emulator of RISC-V 64 with `code` at `base`, that starts at `entry`. `adjust` changes its configuration. -/
def riscv64 (code : ByteArray) (base entry : Nat) (adjust : Config → Config := id) : IO Emu := do
  let decoders ← riscv64Decoders
  let disassembler ← decoders base
  let config : Config := {
    disassembler
    disassemblerAt := some decoders
    memory := ⟨"mem", .mem 64 8, 0, false⟩
    endian := .little
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  loaded (← create (adjust config) [region] { env := clearMonitor config {} } entry) entry

/-- An emulator of RISC-V 32, as `riscv64`. -/
def riscv32 (code : ByteArray) (base entry : Nat) (adjust : Config → Config := id) : IO Emu := do
  let environment ← Target.LLVMLift.riscv32Environment
  let decoders (base : Nat) : IO Disasm.Disassembler := pure
    { name := "riscv32-llvm-primus", decode := decodeAt (Target.LLVMLift.decodeRISCV32With environment) base }
  let disassembler ← decoders base
  let config : Config := {
    disassembler
    disassemblerAt := some decoders
    memory := ⟨"mem", .mem 32 8, 0, false⟩
    endian := .little
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  loaded (← create (adjust config) [region] { env := clearMonitor config {} } entry) entry

/-- An emulator of a variant of PowerPC, as `riscv64`. -/
def powerpc (code : ByteArray) (base entry : Nat) (variant : Target.LLVMLift.PowerPCVariant) (adjust : Config → Config := id) : IO Emu := do
  let decoders (base : Nat) : IO Disasm.Disassembler := do
    pure (withUndefined variant.endian Target.LLVMLift.powerpcUndefined (← Target.PowerPC.disassembler base variant) base)
  let disassembler ← decoders base
  let config : Config := {
    disassembler
    disassemblerAt := some decoders
    memory := ⟨"mem", .mem variant.bits 8, 0, false⟩
    endian := variant.endian
    syscallAbi := if variant.bits == 64 then .powerpc64 else .powerpc
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  loaded (← create (adjust config) [region] { env := clearMonitor config {} } entry) entry

/-- ARM and Thumb, of which it starts in Thumb if `thumb`. -/
def arm32 (code : ByteArray) (base entry : Nat) (thumb : Bool := false) (adjust : Config → Config := id) : IO Emu := do
  let disassembler ← Target.ARM32.disassembler base
  let config : Config := {
    disassembler
    disassemblerAt := some (fun base => Target.ARM32.disassembler base)
    thumbAt := some (fun base => Target.Thumb.disassembler base)
    memory := ⟨"mem", .mem 32 8, 0, false⟩
    endian := .little
    syscallAbi := .arm
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  let env := Bil.bind (clearMonitor config {}) ⟨"ISET", .imm 1, 0, false⟩ (.bits (BitVec.ofNat 1 (if thumb then 1 else 0)))
  loaded (← create (adjust config) [region] { env } entry) entry

/-- An emulator of i686, as `riscv64`. -/
def x86_32 (code : ByteArray) (base entry : Nat) (adjust : Config → Config := id) : IO Emu := do
  let disassembler ← Target.X8632.disassembler base
  let config : Config := {
    disassembler
    disassemblerAt := some (fun base => Target.X8632.disassembler base)
    memory := ⟨"mem", .mem 32 8, 0, false⟩
    endian := .little
    syscallAbi := .x86_32
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  loaded (← create (adjust config) [region] {} entry) entry

/-- An emulator of x86-64, as `riscv64`. -/
def x86_64 (code : ByteArray) (base entry : Nat) (adjust : Config → Config := id) : IO Emu := do
  let disassembler ← Target.X86.disassembler base
  let config : Config := {
    disassembler
    disassemblerAt := some (fun base => Target.X86.disassembler base)
    memory := ⟨"mem", .mem 64 8, 0, false⟩
    endian := .little
    syscallAbi := .x86_64
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  loaded (← create (adjust config) [region] {} entry) entry

/-- An emulator of AArch64, as `riscv64`, with the top byte of an address ignored, as Linux has it. -/
def aarch64 (code : ByteArray) (base entry : Nat) (adjust : Config → Config := id) : IO Emu := do
  let disassembler ← Target.AArch64.emulatorDisassembler base
  let config : Config := {
    disassembler
    disassemblerAt := some (fun base => Target.AArch64.emulatorDisassembler base)
    memory := ⟨"mem", .mem 64 8, 0, false⟩
    endian := .little
    syscallAbi := .aarch64
    untag := Target.AArch64.untag
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  loaded (← create (adjust config) [region] { env := clearMonitor config {} } entry) entry

private def mipsOf (variant : Target.LLVMLift.MipsVariant) (code : ByteArray) (base entry : Nat) (adjust : Config → Config) : IO Emu := do
  let environment ← Target.LLVMLift.mipsEnvironmentOf variant
  let decoders (base : Nat) : IO Disasm.Disassembler := pure <| withUndefined variant.endian (Target.LLVMLift.mipsUndefined variant) {
    name := if variant.bits == 64 then "mips64-llvm-primus" else "mips-llvm-primus"
    decode := decodeAt (Target.LLVMLift.decodeMIPSOf variant environment) base
    hasDelaySlot := Target.LLVMLift.mipsHasDelaySlotOf variant
    annulsSlot := Target.LLVMLift.mipsAnnulsSlot } base
  let disassembler ← decoders base
  let config : Config := {
    disassembler
    disassemblerAt := some decoders
    memory := ⟨"mem", .mem variant.bits 8, 0, false⟩
    endian := variant.endian
    syscallAbi := .mips
    delayPolicy := .mips variant.release6
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  loaded (← create (adjust config) [region] { env := clearMonitor config {} } entry) entry

/-- An emulator of MIPS64, of release 6 or not and big-endian or not, as `riscv64`. -/
def mips64 (code : ByteArray) (base entry : Nat) (release6 : Bool := false) (endian : Endian := .big) (adjust : Config → Config := id) : IO Emu :=
  mipsOf { bits := 64, endian, release6 } code base entry adjust

/-- An emulator of MIPS32, as `mips64`. -/
def mips32 (code : ByteArray) (base entry : Nat) (release6 : Bool := false) (endian : Endian := .big) (adjust : Config → Config := id) : IO Emu :=
  mipsOf { bits := 32, endian, release6 } code base entry adjust

end Bap.Emu
