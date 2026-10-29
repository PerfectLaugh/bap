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
  deriving Repr

opaque Program : Type

@[extern "bap_jit_compile"]
opaque compile (ops : List Op) : IO Program

abbrev MemoryObserver := Bool → Nat → Nat → Nat → IO Unit

@[extern "bap_jit_run_memory"]
opaque runWithMemoryObserved (program : Program) (state addresses : Array UInt64) (values : Array UInt8)
    (observer : Option MemoryObserver) : IO (Nat × Array UInt64 × Array UInt64 × Array UInt8)

def runWithMemory (program : Program) (state addresses : Array UInt64) (values : Array UInt8) :
    IO (Nat × Array UInt64 × Array UInt64 × Array UInt8) :=
  runWithMemoryObserved program state addresses values none

def run (program : Program) (state : Array UInt64) : IO (Nat × Array UInt64) := do
  let (next, state, _, _) ← runWithMemory program state #[] #[]
  pure (next, state)

opaque Memory : Type

@[extern "bap_jit_memory_create"]
opaque createMemory (addresses : Array UInt64) (values : Array UInt8) : IO Memory

@[extern "bap_jit_run_memory_object"]
opaque runWithPersistentMemory (program : Program) (state : Array UInt64) (memory : Memory)
    (observer : Option MemoryObserver) : IO (Nat × Array UInt64 × Array UInt64 × Array UInt8)

@[extern "bap_jit_memory_dump"]
opaque dumpMemory (memory : Memory) : IO (Array UInt64 × Array UInt8)

@[extern "bap_jit_memory_size"]
opaque memorySize (memory : Memory) : IO Nat

end Bap.Jit
