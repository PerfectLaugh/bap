/-! ## The trusted base

`native/bap_jit.cpp` is opaque to Lean: everything `@[extern]` below is an axiom-free `opaque` whose behaviour
nothing can unfold. Every theorem about native execution therefore rests on exactly these obligations of the
C++, and on nothing else of it. `Bap.Proofs.Jit` states them on a model and proves the Lean side against it.

**Compiled programs** (`compile`, `runWithMemoryObservedCode`, `runWithPersistentMemoryObservedCode`)
1. Each `Op` computes what `Bap.Proofs.Primus.step` says on 64-bit slots, `label`, `goto` and `branch` go where
   `Bap.Proofs.Jit.nextCfg` says, and a program leaves its slots as the array it returns, and returns the value of
   the `jump` that ended it. `lowerStatements_run` and `lowerExp_correct` are proved against that model.
2. `memLoad` and `memStore` first call the memory observer, once, with the base address, the size, and, for a
   store, the whole value, and then access `size` consecutive bytes (at most 8) in the order of `bigEndian`, at
   the base plus 0 and so on in 64 bits, as one instruction of the host where obligation 10 says. They do not wrap at the end of a narrower address space. Lowering does not
   let them get there: such a multi-byte access is either the interpreter's (`Lifted.wrapSafe`), or the observer
   rejects it first (`accessFault_past_end`). Any other access is the same on the model whose `view` wraps
   (`denoteLoad_view`, `denoteStore_view`, `wrap_in_range`).
3. `code` calls the code observer once with its pc. When that returns `true`, the program returns that pc at
   once, with 3 in the effect slot, and no op after it has run. When it returns `false`, the program goes on with the next
   op (`Bap.Proofs.Jit.nextCfgAt`).
4. Once an observer has thrown, no further load, store or observer call takes effect, and the runner returns
   that error, whatever the program did next. The memory the failed program wrote before stays written,
   which is why `Lifted.discardMemory` follows every failure.
5. The observers run on the calling thread, and a program does not run them concurrently with itself.

**Runner results**
6. `runWithMemoryObservedCode` returns the final cells of the memory image, and
   `runWithPersistentMemoryObservedCode` the cells its stores changed, each once.

**Persistent memory** (`Memory`, `createMemory`, `createMemoryChunks`, `writeMemory`, `zeroMemory`, `readMemory`, `readMemoryRange`, `dumpMemory`, `cloneMemory`, `trimMemory`)
7. A `Memory` is a total map from `UInt64` to `UInt8`, 0 where nothing was written. `readMemory` reads it,
   `writeMemory` and `createMemory` write pairs in array order, and `createMemory` starts from nothing.
8. `dumpMemory` returns a cell for each address that doesn't hold 0, by ascending address, with no address twice
   (`persistentRegionData_bytes` depends on it), and its bytes are those `readMemory` reads. Where it has no cell,
   `readMemory` reads 0, whether anything was written there or not.
9. `cloneMemory` returns a new map with the same contents, and no later operation on one affects the other.
10. An access that lies within one word of 8 bytes at a multiple of 8 is atomic across threads, whatever its size and
    alignment, with acquire for a load and release for a store. That goes for `memLoad`, `memStore`, `readMemoryRange` and
    `writeMemory`, for each word of what they access: one that crosses words is atomic in each word and not as a whole.
    This takes a host whose accesses of those sizes are atomic, as x86-64 and AArch64 are. Between a store and a later
    load of another address there is no order: a fence of a guest is what gives that, by `Bap.Emu`'s stopping every
    worker of a parallel round at one, which `IO.wait` then orders.
11. `readMemoryRange memory address size` is `size` bytes of what `readMemory` reads, from `address` on.
12. `trimMemory` changes nothing that any operation here can tell. It may let the host have the memory of pages that
    hold only zeros, of those wholly between its bounds, when nothing stores there meanwhile.
14. `createMemoryChunks bases chunks` is `createMemory` of each byte of each chunk at its base plus its offset, in that order,
    without going past the end of the address space. `zeroMemory memory first last` is `writeMemory` of zeros at the
    addresses from `first` to `last`, as obligation 13 knows of them, but that it needn't say those that were already zero.
13. After `beginMemoryStep`, `memoryStepWrites` holds every address that a `writeMemory` or a program wrote to this memory
    since, once each, by ascending address, also for a program that failed: `some`, or `none` when it was too many or
    no step began. It may hold addresses that were written the same as they were. `endMemoryStep` stops it.

Everything else in `Bap.Emu`, from what the code hooks see to what a rollback restores, is proved against
these. No theorem assumes anything of LLVM beyond them, and nothing depends on `memorySize`, which has no obligation.

**What is proved about lowering.** Expressions (`lowerExp_correct`), statements with their branches, loops and stores
(`lowerStatements_correct`), the way into native code (`encodeState_holds`), the way out (`syncState_output`, `syncState_flags`),
and a whole range along its edges and back edges with its budget, code sites and flags (`lowerGraph_correct`, and `lowerGraph_single` for a
block alone): it ends as the blocks do one at a time in the interpreter, with the same state, pc and count, on the terms above. The proof assumes
nothing of the graph: `lowerGraphChecked` checks at compile time what it does not follow through every statement, and a lowering
that failed the check would stay out of native code. The one thing `lowerGraph_correct` leaves out is the interpreter running out of its
fuel: what lowers has a result otherwise, on a state that `encodeState` takes with its memory bound (`graph_progress`). The limit on native loops
is that same bound: on the fuel the interpreter runs with, a loop out of iterations means that the interpreter ran out too (`lowerGraph_interpreterFuel`). `Bap.Emu.Core` lists what stays trusted around all of this, and `Bap.Proofs` all of it for the project. -/

namespace Bap.Jit

inductive BinOp where
  | add | sub | mul | and | or | xor | lshift | rshift
  | eq | neq | lt | le | gt | ge
  | udiv | urem | sdiv | srem | slt | sle | sgt | sge
  deriving Repr

inductive Op where
  | set (dst : Nat) (immediate : UInt64)
  | move (dst src : Nat)
  | add (dst src : Nat) (immediate : UInt64)
  | jump (target : UInt64)
  | jumpSlot (src : Nat)
  | bin (op : BinOp) (dst left right : Nat)
  | andImm (dst src : Nat) (immediate : UInt64)
  | signExtend (width dst src : Nat)
  | select (dst condition yes no : Nat)
  | neg (dst src : Nat)
  | not (dst src : Nat)
  | ashr (width dst left right : Nat)
  | label (id : Nat)
  | goto (id : Nat)
  | branch (condition yes no : Nat)
  | memLoad (dst address size : Nat) (bigEndian : Bool)
  | memStore (address value size : Nat) (bigEndian : Bool)
  | code (effectSlot : Nat) (pc : UInt64)
  deriving Repr

opaque Program : Type

/-! The native functions read their arguments and don't release them, so that they all borrow: an owned argument would never be freed. -/

/-- Compiled quickly, into code that is less quick than `compileOptimized` makes of the same. -/
@[extern "bap_jit_compile"]
opaque compile (ops : @& List Op) : IO Program

@[extern "bap_jit_compile_optimized"]
opaque compileOptimized (ops : @& List Op) : IO Program

/-- A program that starts at the label that the slot `entrySlot` of its state says, as one more than it, of those that are
`entries`, and where it would otherwise when that holds zero. It takes a state that has that slot. -/
@[extern "bap_jit_compile_entries"]
opaque compileEntries (ops : @& List Op) (entries : @& List Nat) (entrySlot : @& Nat) (optimized : Bool) : IO Program

abbrev MemoryObserver := Bool → Nat → Nat → Nat → IO Unit
abbrev CodeObserver := Nat → IO Bool

@[extern "bap_jit_run_memory_code"]
opaque runWithMemoryObservedCode (program : @& Program) (state addresses : @& Array UInt64) (values : @& Array UInt8)
    (observer : @& Option MemoryObserver) (codeObserver : @& Option CodeObserver) :
    IO (Nat × Array UInt64 × Array UInt64 × Array UInt8)

def runWithMemoryObserved (program : Program) (state addresses : Array UInt64) (values : Array UInt8)
    (observer : Option MemoryObserver) : IO (Nat × Array UInt64 × Array UInt64 × Array UInt8) :=
  runWithMemoryObservedCode program state addresses values observer none

def runWithMemory (program : Program) (state addresses : Array UInt64) (values : Array UInt8) :
    IO (Nat × Array UInt64 × Array UInt64 × Array UInt8) :=
  runWithMemoryObserved program state addresses values none

def run (program : Program) (state : Array UInt64) : IO (Nat × Array UInt64) := do
  let (next, state, _, _) ← runWithMemory program state #[] #[]
  pure (next, state)

opaque Memory : Type

@[extern "bap_jit_memory_create"]
opaque createMemory (addresses : @& Array UInt64) (values : @& Array UInt8) : IO Memory

@[extern "bap_jit_memory_write"]
opaque writeMemory (memory : @& Memory) (addresses : @& Array UInt64) (values : @& Array UInt8) : IO Unit

@[extern "bap_jit_run_memory_object_code"]
opaque runWithPersistentMemoryObservedCode (program : @& Program) (state : @& Array UInt64) (memory : @& Memory)
    (observer : @& Option MemoryObserver) (codeObserver : @& Option CodeObserver) :
    IO (Nat × Array UInt64 × Array UInt64 × Array UInt8)

def runWithPersistentMemory (program : Program) (state : Array UInt64) (memory : Memory)
    (observer : Option MemoryObserver) : IO (Nat × Array UInt64 × Array UInt64 × Array UInt8) :=
  runWithPersistentMemoryObservedCode program state memory observer none

@[extern "bap_jit_memory_dump"]
opaque dumpMemory (memory : @& Memory) : IO (Array UInt64 × Array UInt8)

@[extern "bap_jit_memory_clone"]
opaque cloneMemory (memory : @& Memory) : IO Memory

@[extern "bap_jit_memory_read"]
opaque readMemory (memory : @& Memory) (address : UInt64) : IO UInt8

@[extern "bap_jit_memory_read_range"]
opaque readMemoryRange (memory : @& Memory) (address : UInt64) (size : @& Nat) : IO ByteArray

@[extern "bap_jit_memory_create_chunks"]
opaque createMemoryChunks (bases : @& Array UInt64) (chunks : @& Array ByteArray) : IO Memory

@[extern "bap_jit_memory_zero"]
opaque zeroMemory (memory : @& Memory) (first last : UInt64) : IO Unit

@[extern "bap_jit_memory_step_begin"]
opaque beginMemoryStep (memory : @& Memory) : IO Unit

@[extern "bap_jit_memory_step_end"]
opaque endMemoryStep (memory : @& Memory) : IO Unit

@[extern "bap_jit_memory_step_writes"]
opaque memoryStepWrites (memory : @& Memory) : IO (Option (Array UInt64))

@[extern "bap_jit_memory_trim"]
opaque trimMemory (memory : @& Memory) (first last : UInt64) : IO Unit

@[extern "bap_jit_memory_size"]
opaque memorySize (memory : @& Memory) : IO Nat

end Bap.Jit
