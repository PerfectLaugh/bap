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
   the base plus 0 and so on in 64 bits. They do not wrap at the end of a narrower address space. Lowering does not
   let them get there: such a multi-byte access is either the interpreter's (`Lifted.wrapSafe`), or the observer
   rejects it first (`accessFault_past_end`). Any other access is the same on the model whose `view` wraps
   (`denoteLoad_view`, `denoteStore_view`, `wrap_in_range`).
3. `code` calls the code observer once with its pc. When that returns `true`, the program returns that pc at
   once, with 3 in the effect slot, and no op after it has run.
4. Once an observer has thrown, no further load, store or observer call takes effect, and the runner returns
   that error, whatever the program did next. The memory the failed program wrote before stays written,
   which is why `Lifted.discardMemory` follows every failure.
5. The observers run on the calling thread, and a program does not run them concurrently with itself.

**Runner results**
6. `runWithMemoryObservedCode` returns the final cells of the memory image, and
   `runWithPersistentMemoryObservedCode` the cells its stores changed, each once.

**Persistent memory** (`Memory`, `createMemory`, `writeMemory`, `readMemory`, `dumpMemory`, `cloneMemory`)
7. A `Memory` is a total map from `UInt64` to `UInt8`, 0 where nothing was written. `readMemory` reads it,
   `writeMemory` and `createMemory` write pairs in array order, and `createMemory` starts from nothing.
8. `dumpMemory` returns a cell for each address written, by ascending address, with no address twice
   (`persistentRegionData_bytes` depends on it), and its bytes are those `readMemory` reads.
9. `cloneMemory` returns a new map with the same contents, and no later operation on one affects the other.
10. Accesses of one byte from several threads are atomic: a parallel round has no other synchronization on
    memory. Multi-byte accesses are not atomic across threads, like on hardware.

Everything else in `Bap.Emu`, from what the code hooks see to what a rollback restores, is proved against
these. No theorem assumes anything of LLVM beyond them.

**What is proved about lowering, and what is not.** Expressions (`lowerExp_correct`), statements with their
branches, loops and stores (`lowerStatements_correct`), the way into native code (`encodeState_holds`) and the way
out (`syncState_output`, `syncState_frame`) are proved. A compiled range of several blocks is built of those, with
`enterBlock` between them. That the blocks of a range compose to what the instructions do one at a time, along the
back edges, is not proved as a whole: `closedTarget_sound`, `definitelyWritten_seed`, `reachedOutputs_unflagged` and
`enterBlock_starts` are its parts, the tests of `rangeRegressions` compare it with single steps, and otherwise it is
trusted. `Bap.Emu.Core` says what is trusted of the emulator around native code. -/

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

@[extern "bap_jit_compile"]
opaque compile (ops : List Op) : IO Program

abbrev MemoryObserver := Bool → Nat → Nat → Nat → IO Unit
abbrev CodeObserver := Nat → IO Bool

@[extern "bap_jit_run_memory_code"]
opaque runWithMemoryObservedCode (program : Program) (state addresses : Array UInt64) (values : Array UInt8)
    (observer : Option MemoryObserver) (codeObserver : Option CodeObserver) :
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
opaque createMemory (addresses : Array UInt64) (values : Array UInt8) : IO Memory

@[extern "bap_jit_memory_write"]
opaque writeMemory (memory : Memory) (addresses : Array UInt64) (values : Array UInt8) : IO Unit

@[extern "bap_jit_run_memory_object_code"]
opaque runWithPersistentMemoryObservedCode (program : Program) (state : Array UInt64) (memory : Memory)
    (observer : Option MemoryObserver) (codeObserver : Option CodeObserver) :
    IO (Nat × Array UInt64 × Array UInt64 × Array UInt8)

def runWithPersistentMemory (program : Program) (state : Array UInt64) (memory : Memory)
    (observer : Option MemoryObserver) : IO (Nat × Array UInt64 × Array UInt64 × Array UInt8) :=
  runWithPersistentMemoryObservedCode program state memory observer none

@[extern "bap_jit_memory_dump"]
opaque dumpMemory (memory : Memory) : IO (Array UInt64 × Array UInt8)

@[extern "bap_jit_memory_clone"]
opaque cloneMemory (memory : Memory) : IO Memory

@[extern "bap_jit_memory_read"]
opaque readMemory (memory : Memory) (address : UInt64) : IO UInt8

@[extern "bap_jit_memory_size"]
opaque memorySize (memory : Memory) : IO Nat

end Bap.Jit
