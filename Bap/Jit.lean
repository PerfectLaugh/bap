/-! ## The trusted base

`native/bap_jit.cpp` is opaque to Lean: everything `@[extern]` below is an axiom-free `opaque` whose behaviour
nothing can unfold. Every theorem about native execution therefore rests on exactly these obligations of the
C++, and on nothing else of it. `Bap.Proofs.Jit` states them on a model and proves the Lean side against it.

**Compiled programs** (`compile`, `runWithMemoryObservedCode`, `runWithPersistentMemoryObservedCode`)
1. Each `Op` computes what `Bap.Proofs.Primus.step` says on 64-bit slots, `label`, `goto` and `branch` go where
   `Bap.Proofs.Jit.nextCfg` says, and a program leaves its slots as the array it returns, and returns the value of
   the `jump` that ended it. What `compileOptimized` and `compileEntries` optimize leaves only the slots of `kept` so, and
   the others as they may be: `Bap.Primus.Lifted` keeps those that it reads afterwards, of the variables, the flags, the
   effect, the budget and where a run was entered (`keptSlots`). `lowerStatements_run` and `lowerExp_correct` are proved against that model.
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
16. `runWithPersistentMemoryFilteredCode` is `runWithPersistentMemoryObservedCode`, but for a `memLoad` or `memStore` that lies
    wholly within one range of its filter that lets that kind through (bit 1 a load, bit 2 a store), which calls no memory observer.
    That is the same run where the observer would have done nothing for such an access, as `Bap.Emu` keeps its filters
    (`Emu.Core.quietRanges`, `Emu.Core.quietBits`): the ranges of `createMemoryFilter`, and what `updateMemoryFilter` makes of them when
    it says `true`, are apart, and are those where `notifyAccess` does nothing.
    With `quietSites`, a `code` op calls no code observer while no memory observer has been called in the run: the pc of the last such op
    waits, and the code observer is called once with it just before the first memory observer is, after which obligation 3 holds of
    each. If that call returns `true` the run fails, as for an observer that throws (obligation 4). `Bap.Emu` asks for it where its code
    observer would only have set the pc, as nothing observes the range and nothing is dirty when it starts.
17. `runChain` is `runWithPersistentMemoryFilteredCode` of the range of the chain that starts at `firstPc`, which has to be the one
    numbered `firstId` and to be `program`, followed, while each ends with a jump (1 in its effect slot), with no observer having run
    Lean code, with budget left and with a range of the chain where it went, by that range, as `Bap.Primus.Lifted` would run it next:
    the outputs that the last run reached, by its flags, or those of its checkpoint where it went, each cut to its width, are what the
    variables now hold, which with those given at first (`variables`, `values`) are its slots of the layout, unless one that it needs
    isn't bound, which ends the run there; the slots it has for 0 are 0, and the others, which it writes before it reads, as may be; its budget is what the last left less one, and its observed slot 0. A range that isn't
    optimized is gone on to as `Bap.Primus.Lifted` counts its executions: not once they come to when it is to be optimized, and with its
    budget no more than what they have left until then. What is optimized with numbers for its variables (`variables` of
    `compileOptimized`, pairs of a slot and a number) reads and writes them as the chain's registers, rather than in its slots, which
    then hold nothing of them, and the chain takes what such a range writes as what it reached of its outputs. It gives back what the
    run of the last range gives, with: that range's number, the blocks entered after the first of all, the variables that the ranges
    before it wrote with what they hold last, and the number of runs of each range. A failed run fails it all, as in obligation 4.
13. After `beginMemoryStep`, `memoryStepWrites` holds every address that a `writeMemory` or a program wrote to this memory
    since, once each, by ascending address, also for a program that failed: `some`, or `none` when it was too many or
    no step began. It may hold addresses that were written the same as they were. `endMemoryStep` stops it.

**Byte arrays** (`zeros`, `regionBytes`, `sliceNative`, `piecesNative`, `fillNative`, `residentNative`)
15. `zeros size` is `size` bytes of zeros, and `regionBytes memory address size` is `readMemoryRange memory address size`: they differ
    only in how much memory of the host they take. `sliceNative`, `piecesNative`, `fillNative` and `residentNative` give what `slice`,
    `pieces`, `fill` and `resident` define in Lean, which they are `implemented_by`: what is proved of those (`fill_pieces`) holds of the C++ by this obligation.

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

/-- The operations of two slots that `Op.bin` has: arithmetic of 64 bits that wraps, shifts, comparisons that give 1 or 0, unsigned
unless `s` says signed, and division, which a divisor of 0 doesn't reach, as lowering guards it. -/
inductive BinOp where
  | add | sub | mul | and | or | xor | lshift | rshift
  | eq | neq | lt | le | gt | ge
  | udiv | urem | sdiv | srem | slt | sle | sgt | sge
  deriving Repr

/-- An operation of a compiled program, on its slots of 64 bits: what lowering makes of BIL and `compile` makes native code of, with the
meaning that obligation 1 says. -/
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

/-- Native code that `compile` made, which holds on to it until it is freed. -/
opaque Program : Type

/-! The native functions read their arguments and don't release them, so that they all borrow: an owned argument would never be freed.
`sliceNative`, `piecesNative` and `fillNative` are the exceptions: what `implemented_by` stands in for has to have the type of what it
stands in for, which owns them, and they release them. -/

/-- Compiled quickly, into code that is less quick than `compileOptimized` makes of the same. -/
@[extern "bap_jit_compile"]
opaque compile (ops : @& List Op) : IO Program

/-- Compiled with the optimizations of LLVM, which takes longer and is worth it for what runs a lot. -/
@[extern "bap_jit_compile_optimized"]
opaque compileOptimized (ops : @& List Op) (kept : @& Array UInt64) (budgetSlot : UInt64) (variables : @& Array UInt64) : IO Program

/-- A program that starts at the label that the slot `entrySlot` of its state says, as one more than it, of those that are
`entries`, and where it would otherwise when that holds zero. It takes a state that has that slot. -/
@[extern "bap_jit_compile_entries"]
opaque compileEntries (ops : @& List Op) (entries : @& List Nat) (entrySlot : @& Nat) (optimized : Bool) (kept : @& Array UInt64)
    (variables : @& Array UInt64) : IO Program

/-- What hears of each load and store before it happens, as obligation 2 says: whether it is a store, the address, the size and what is
stored. It throws to stop the program, as for a fault. -/
abbrev MemoryObserver := Bool → Nat → Nat → Nat → IO Unit
/-- What hears of each code site, as obligation 3 says, with its pc: `true` stops the program there. -/
abbrev CodeObserver := Nat → IO Bool

/-- Runs a program on a state and on a memory image given as its cells, and gives back where it went, its state, and the cells of the
image after it (obligation 6). -/
@[extern "bap_jit_run_memory_code"]
opaque runWithMemoryObservedCode (program : @& Program) (state addresses : @& Array UInt64) (values : @& Array UInt8)
    (observer : @& Option MemoryObserver) (codeObserver : @& Option CodeObserver) :
    IO (Nat × Array UInt64 × Array UInt64 × Array UInt8)

/-- `runWithMemoryObservedCode` without a code observer. -/
def runWithMemoryObserved (program : Program) (state addresses : Array UInt64) (values : Array UInt8)
    (observer : Option MemoryObserver) : IO (Nat × Array UInt64 × Array UInt64 × Array UInt8) :=
  runWithMemoryObservedCode program state addresses values observer none

/-- A run with a memory image and nothing that hears of it. -/
def runWithMemory (program : Program) (state addresses : Array UInt64) (values : Array UInt8) :
    IO (Nat × Array UInt64 × Array UInt64 × Array UInt8) :=
  runWithMemoryObserved program state addresses values none

/-- A run of a program that has no memory, on its slots alone. -/
def run (program : Program) (state : Array UInt64) : IO (Nat × Array UInt64) := do
  let (next, state, _, _) ← runWithMemory program state #[] #[]
  pure (next, state)

/-- Memory that lives on the host between runs, which programs read and write in place: obligations 7 to 14. -/
opaque Memory : Type

/-- A memory with these bytes at these addresses, and zero elsewhere. -/
@[extern "bap_jit_memory_create"]
opaque createMemory (addresses : @& Array UInt64) (values : @& Array UInt8) : IO Memory

/-- Writes each byte at its address, in order. -/
@[extern "bap_jit_memory_write"]
opaque writeMemory (memory : @& Memory) (addresses : @& Array UInt64) (values : @& Array UInt8) : IO Unit

/-- Runs a program on a state and on a `Memory`, which it changes, and gives back where it went, its state, and the cells that its
stores changed (obligation 6). -/
@[extern "bap_jit_run_memory_object_code"]
opaque runWithPersistentMemoryObservedCode (program : @& Program) (state : @& Array UInt64) (memory : @& Memory)
    (observer : @& Option MemoryObserver) (codeObserver : @& Option CodeObserver) :
    IO (Nat × Array UInt64 × Array UInt64 × Array UInt8)

/-- `runWithPersistentMemoryObservedCode` without a code observer. -/
def runWithPersistentMemory (program : Program) (state : Array UInt64) (memory : Memory)
    (observer : Option MemoryObserver) : IO (Nat × Array UInt64 × Array UInt64 × Array UInt8) :=
  runWithPersistentMemoryObservedCode program state memory observer none

/-- The ranges of addresses, in order and apart, where an access of a kind needs no memory observer (obligation 16): from `firsts` to
`lasts`, with `quiet` 1 for loads, 2 for stores and 3 for both. -/
opaque MemoryFilter : Type

@[extern "bap_jit_memory_filter_create"]
opaque createMemoryFilter (firsts lasts : @& Array UInt64) (quiet : @& Array UInt8) : IO MemoryFilter

/-- Takes the ranges that start at `removed` out of a filter and puts those given in: `true` if they are apart from all that are there,
and `false` otherwise, after which the filter is not to be used. -/
@[extern "bap_jit_memory_filter_update"]
opaque updateMemoryFilter (filter : @& MemoryFilter) (removed firsts lasts : @& Array UInt64) (quiet : @& Array UInt8) : IO Bool

/-- `runWithPersistentMemoryObservedCode` that calls the observer only for what the filter doesn't let through (obligation 16). -/
@[extern "bap_jit_run_memory_object_filtered_code"]
opaque runWithPersistentMemoryFilteredCode (program : @& Program) (state : @& Array UInt64) (memory : @& Memory)
    (filter : @& MemoryFilter) (quietSites : Bool) (observer : @& Option MemoryObserver) (codeObserver : @& Option CodeObserver) :
    IO (Nat × Array UInt64 × Array UInt64 × Array UInt8)

/-- Ranges that native code goes on to from one to the next (obligation 17), by where they start. -/
opaque Chain : Type

@[extern "bap_jit_chain_create"]
opaque createChain : IO Chain

/-- Forgets every range of a chain, as one may have changed. -/
@[extern "bap_jit_chain_clear"]
opaque clearChain (chain : @& Chain) : IO Unit

/-- Whether the range of a chain at `pc` is `program`. -/
@[extern "bap_jit_chain_holds"]
opaque chainHolds (chain : @& Chain) (pc : UInt64) (program : @& Program) : Bool

/-- That the range of a chain at `pc` is being optimized: it is gone on to for that many executions more, and then not, so that Lean
sees whether it is done. -/
@[extern "bap_jit_chain_optimizing"]
opaque chainOptimizing (chain : @& Chain) (pc executions : UInt64) : IO Unit

/-- Puts a range in a chain at `pc`, numbered `id`: `data` is the number of its slots, its effect, budget and observed slots (all ones
for none), its executions and the executions at which it is to be optimized (all ones if it is), the slots that are 0 at its start, and
its layout, the variables it needs, its outputs, its flags and its checkpoints, each as a count and what it counts. -/
@[extern "bap_jit_chain_add"]
opaque addToChain (chain : @& Chain) (pc id : UInt64) (program : @& Program) (data : @& Array UInt64) : IO Unit

/-- A run that goes on from range to range of a chain in native code (obligation 17): where it went, the slots and the changed cells of
the last range, and then that range's number, the blocks entered after the first, whether the last range's variables are among those
written rather than in its slots, the count and pairs of the variables written, and the count and triples of each range, its runs and
its executions. -/
@[extern "bap_jit_run_chain"]
opaque runChain (program : @& Program) (state : @& Array UInt64) (memory : @& Memory) (filter : @& MemoryFilter) (quietSites : Bool)
    (observer : @& Option MemoryObserver) (codeObserver : @& Option CodeObserver) (chain : @& Chain) (firstId firstPc firstBudget : UInt64)
    (variables values : @& Array UInt64) (variableCount : UInt64) : IO (Nat × Array UInt64 × Array UInt64 × Array UInt8 × Array UInt64)

/-- What isn't zero of a memory, as its cells by address (obligation 8). -/
@[extern "bap_jit_memory_dump"]
opaque dumpMemory (memory : @& Memory) : IO (Array UInt64 × Array UInt8)

/-- A memory of its own with what this one has (obligation 9). -/
@[extern "bap_jit_memory_clone"]
opaque cloneMemory (memory : @& Memory) : IO Memory

/-- The byte at an address. -/
@[extern "bap_jit_memory_read"]
opaque readMemory (memory : @& Memory) (address : UInt64) : IO UInt8

/-- `size` bytes from an address (obligation 11). -/
@[extern "bap_jit_memory_read_range"]
opaque readMemoryRange (memory : @& Memory) (address : UInt64) (size : @& Nat) : IO ByteArray

/-- A memory with each chunk at its base, which takes the host only the pages of them that aren't zeros (obligation 14). -/
@[extern "bap_jit_memory_create_chunks"]
opaque createMemoryChunks (bases : @& Array UInt64) (chunks : @& Array ByteArray) : IO Memory

/-- Zeros from `first` to `last` (obligation 14). -/
@[extern "bap_jit_memory_zero"]
opaque zeroMemory (memory : @& Memory) (first last : UInt64) : IO Unit

/-- Starts noting what is written, for a step that may have to be taken back (obligation 13). -/
@[extern "bap_jit_memory_step_begin"]
opaque beginMemoryStep (memory : @& Memory) : IO Unit

/-- Stops noting what is written. -/
@[extern "bap_jit_memory_step_end"]
opaque endMemoryStep (memory : @& Memory) : IO Unit

/-- What was written since `beginMemoryStep`, or `none` if that was too much to note (obligation 13). -/
@[extern "bap_jit_memory_step_writes"]
opaque memoryStepWrites (memory : @& Memory) : IO (Option (Array UInt64))

/-- Lets the host have back the pages from `first` to `last` that hold only zeros (obligation 12). -/
@[extern "bap_jit_memory_trim"]
opaque trimMemory (memory : @& Memory) (first last : UInt64) : IO Unit

/-- How many bytes of the host a memory takes, which nothing depends on. -/
@[extern "bap_jit_memory_size"]
opaque memorySize (memory : @& Memory) : IO Nat

/-- The bytes of a range of a memory, which take memory of the host only for the pages of it that the memory has. -/
@[extern "bap_jit_memory_region_bytes"]
opaque regionBytes (memory : @& Memory) (address : UInt64) (size : @& Nat) : IO ByteArray

/-- `size` zeros, of which the host gives the pages as they are written, so that what a program maps and doesn't use takes nothing. -/
@[extern "bap_zero_bytes"]
opaque zeros (size : @& Nat) : ByteArray

/-- What `slice` is, in native code (obligation 15). -/
@[extern "bap_bytes_slice"]
opaque sliceNative (data : ByteArray) (start stop : Nat) : ByteArray

/-- `ByteArray.extract`, which of what is big copies only what isn't zeros, into zeros that take nothing yet. -/
@[implemented_by sliceNative]
def slice (data : ByteArray) (start stop : Nat) : ByteArray := data.extract start stop

@[simp] theorem slice_eq (data : ByteArray) (start stop : Nat) : slice data start stop = data.extract start stop := rfl

/-- What a checkpoint can ask `fill` for, which is more than any host could give. -/
def fillLimit : Nat := 2 ^ 48

/-- How many bytes a piece of `pieces` has, but for the last, which has what is left. -/
def pieceSize : Nat := 4096

/-- What `pieces` is, in native code (obligation 15). -/
@[extern "bap_bytes_pieces"]
opaque piecesNative (data : ByteArray) : List (Nat × ByteArray)

/-- What of `data` isn't zeros, as each piece of `pieceSize` bytes from the start that isn't all zeros, with where it starts. -/
@[implemented_by piecesNative]
def pieces (data : ByteArray) : List (Nat × ByteArray) :=
  (List.range ((data.size + pieceSize - 1) / pieceSize)).filterMap fun index =>
    let piece := data.extract (index * pieceSize) (index * pieceSize + pieceSize)
    if piece.data.all (· == 0) then none else some (index * pieceSize, piece)

@[extern "bap_bytes_resident"]
opaque residentNative (data : ByteArray) : Nat

/-- How many bytes the pieces of `data` have, which is how much of it isn't zeros, by pieces: what it takes of the host as `fill` makes
it. It is counted without making the pieces. -/
@[implemented_by residentNative]
def resident (data : ByteArray) : Nat := (pieces data).foldl (fun total piece => total + piece.2.size) 0

/-- What `fill` has at `index`: from the first piece that has it, or else zero. -/
def byteOf (pieces : List (Nat × ByteArray)) (index : Nat) : UInt8 :=
  match pieces.find? fun (start, bytes) => start ≤ index && index < start + bytes.size with
  | some (start, bytes) => bytes[index - start]!
  | none => 0

/-- What `fill` is, in native code (obligation 15). -/
@[extern "bap_bytes_fill"]
opaque fillNative (size : Nat) (pieces : List (Nat × ByteArray)) : ByteArray

/-- `size` bytes of zeros with `pieces` in them, which take memory of the host only for the pieces, as `zeros` does. -/
@[implemented_by fillNative]
def fill (size : Nat) (pieces : List (Nat × ByteArray)) : ByteArray :=
  ⟨Array.ofFn (n := size) fun index => byteOf pieces index⟩

/-- Each piece of `pieces` is of `data`, from where it starts, which is in `data`. -/
theorem mem_pieces {data : ByteArray} {piece : Nat × ByteArray} (h : piece ∈ pieces data) :
    ∃ index, index * pieceSize < data.size ∧
      piece = (index * pieceSize, data.extract (index * pieceSize) (index * pieceSize + pieceSize)) := by
  simp only [pieces, List.mem_filterMap, List.mem_range] at h
  obtain ⟨index, hindex, hpiece⟩ := h
  split at hpiece
  · cases hpiece
  · refine ⟨index, ?_, (Option.some.inj hpiece).symm⟩
    have hdiv := Nat.div_mul_le_self (data.size + pieceSize - 1) pieceSize
    have hmul := Nat.mul_le_mul_right pieceSize (Nat.succ_le_of_lt hindex)
    simp only [Nat.succ_mul] at hmul
    have : 0 < pieceSize := by decide
    omega

/-- There are no more pieces than bytes, which a checkpoint's count of them needs to fit its field. -/
theorem length_pieces (data : ByteArray) : (pieces data).length ≤ data.size := by
  simp only [pieces]
  refine Nat.le_trans (List.length_filterMap_le _ _) ?_
  rw [List.length_range]
  rcases Nat.eq_zero_or_pos data.size with hzero | hpos
  · simp [hzero, pieceSize]
  · exact Nat.div_le_of_le_mul (by simp only [pieceSize]; omega)

/-- Zeros with the pieces of `data` in them are `data`. -/
theorem fill_pieces (data : ByteArray) : fill data.size (pieces data) = data := by
  apply ByteArray.ext
  apply Array.ext
  · exact Array.size_ofFn
  intro index hfill hdata
  have hindex : index < data.size := hdata
  have hget : (fill data.size (pieces data)).data[index]'hfill = byteOf (pieces data) index := Array.getElem_ofFn ..
  rw [hget]
  unfold byteOf
  split
  · next start bytes hfind =>
    have hin := List.find?_some hfind
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
    obtain ⟨k, _, hk⟩ := mem_pieces (List.mem_of_find?_eq_some hfind)
    simp only [Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    have hlt : index - k * pieceSize < (data.extract (k * pieceSize) (k * pieceSize + pieceSize)).size := by omega
    rw [getElem!_pos (data.extract (k * pieceSize) (k * pieceSize + pieceSize)) (index - k * pieceSize) hlt,
      ByteArray.getElem_extract]
    simp only [ByteArray.getElem_eq_getElem_data]
    congr 1
    omega
  · next hfind =>
    rw [List.find?_eq_none] at hfind
    have hP : 0 < pieceSize := by decide
    let k := index / pieceSize
    have hk1 : k * pieceSize ≤ index := Nat.div_mul_le_self index pieceSize
    have hk2 : index < k * pieceSize + pieceSize := by
      have := Nat.lt_div_mul_add (a := index) hP
      simpa [k, Nat.mul_comm] using this
    have hsize : index - k * pieceSize < (data.extract (k * pieceSize) (k * pieceSize + pieceSize)).size := by
      simp only [ByteArray.size_extract]
      omega
    by_cases hz : (data.extract (k * pieceSize) (k * pieceSize + pieceSize)).data.all (· == 0) = true
    · rw [Array.all_eq_true] at hz
      have := hz (index - k * pieceSize) hsize
      simp only [ByteArray.data_extract, Array.getElem_extract, beq_iff_eq] at this
      have heq : k * pieceSize + (index - k * pieceSize) = index := by omega
      simp only [heq] at this
      exact this.symm
    · exfalso
      have hmem : (k * pieceSize, data.extract (k * pieceSize) (k * pieceSize + pieceSize)) ∈ pieces data := by
        simp only [pieces, List.mem_filterMap, List.mem_range]
        refine ⟨k, ?_, ?_⟩
        · apply Nat.lt_of_lt_of_le (m := (index + pieceSize) / pieceSize)
          · rw [Nat.add_div_right _ hP]
            exact Nat.lt_succ_self _
          · exact Nat.div_le_div_right (by omega)
        · have hz' := Bool.eq_false_iff.mpr hz
          simp only [hz', Bool.false_eq_true, ↓reduceIte]
      have := hfind _ hmem
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_lt] at this
      have := this hk1
      simp only [ByteArray.size_extract] at this hsize
      omega

end Bap.Jit
