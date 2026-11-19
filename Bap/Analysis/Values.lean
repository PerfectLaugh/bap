import Bap.Analysis.Frame

/-! # Value sets and variables

What ROSE's `Variables` finds of the functions of a `Partition`, with value sets as its interval domain has them: the variables of
the stack of each function, its locals, the registers it saves, its arguments in memory and its return address; and the global
variables of a program, with the functions that read and write each.

The values are strided intervals, run forward over the flow of a function: a register holds, of what a register held on entry or of
nothing, a number of `lo`, `lo + stride`, ... `hi`, or what isn't known. A mask, a remainder and a shift bound what they make, and a
sum and a product carry the bounds of their operands, so that an index of an array, `a[i & 7]`, is of all of the array. The stack
pointer before each instruction is what `Frame` found it to be, and a call clobbers what its convention doesn't keep; as `Frame`
has it, a store through an address that isn't known is taken not to change the stack.

A variable is what the loads and stores of a function or a program cover of the stack or of memory, where what overlaps is one:
each access is of all the addresses its value set has, each of the size it reads or writes. -/

namespace Bap.Analysis.Values

open Bap.Analysis.Partition (Partition)

/-- A set of values of `width` bits: of what register `base` held on entry, or of nothing, plus each of `lo`, `lo + stride`, ...
`hi`. Of nothing, they are numbers below `2 ^ width`; of a register, offsets from what it held, of either sign. -/
inductive Value where
  | top
  | set (base : Option String) (width : Nat) (lo hi : Int) (stride : Nat)
  deriving BEq, DecidableEq, Repr, Inhabited

def Value.const (width value : Nat) : Value := .set none width (value % 2 ^ width) (value % 2 ^ width) 0

/-- The values of a range, where they are of what can be: one, or more of a stride, within what a value of `width` bits is. -/
def Value.range (base : Option String) (width : Nat) (lo hi : Int) (stride : Nat) : Value :=
  if hi < lo then .top
  else if lo == hi then
    match base with
    | none => .const width (lo % 2 ^ width).toNat
    | some _ => .set base width lo lo 0
  else
    let stride := if stride == 0 then 1 else stride
    match base with
    | none => if lo < 0 || hi ≥ 2 ^ width then .top else .set none width lo hi stride
    | some _ => if hi - lo ≥ 2 ^ (width - 1) then .top else .set base width lo hi stride

def Value.width : Value → Option Nat
  | .top => none
  | .set _ width _ _ _ => some width

/-- The one value of a set of one. -/
def Value.single : Value → Option (Option String × Int)
  | .set base _ lo hi _ => if lo == hi then some (base, lo) else none
  | .top => none

/-- Whether a set has all that another has. -/
def Value.covers : Value → Value → Bool
  | .top, _ => true
  | _, .top => false
  | .set base width lo hi stride, .set base' width' lo' hi' stride' =>
    base == base' && width == width' && lo ≤ lo' && hi' ≤ hi &&
      (stride == 0 || ((lo' - lo) % stride == 0 && (stride' == 0 || stride' % stride == 0)))

/-- The least set that has both. -/
def Value.join : Value → Value → Value
  | .set base width lo hi stride, .set base' width' lo' hi' stride' =>
    if base != base' || width != width' then .top
    else
      let stride := Nat.gcd (Nat.gcd stride stride') (lo - lo').natAbs
      Value.range base width (min lo lo') (max hi hi') stride
  | _, _ => .top

/-- A slot of the stack, or of what a register held on entry points to, at a constant from it, of `size` bytes. -/
structure Slot where
  base : String
  offset : Int
  size : Nat
  value : Value
  deriving BEq, Repr

/-- Ranges of bytes, `[start, stop)` from what a register held on entry, in order and apart. -/
abbrev Ranges := List (String × Int × Int)

/-- Ranges with another. -/
def Ranges.add (ranges : Ranges) (base : String) (start stop : Int) : Ranges :=
  let (same, others) := ranges.partition (·.1 == base)
  let (start, stop, apart) := same.foldl (init := (start, stop, ([] : Ranges))) fun (start, stop, apart) (b, s, e) =>
    if e < start || stop < s then (start, stop, (b, s, e) :: apart) else (min start s, max stop e, apart)
  others ++ ((base, start, stop) :: apart).mergeSort fun a b => a.2.1 ≤ b.2.1

/-- What both ranges have. -/
def Ranges.inter (left right : Ranges) : Ranges :=
  left.flatMap fun (base, start, stop) => right.filterMap fun (base', start', stop') =>
    if base == base' && max start start' < min stop stop' then some (base, max start start', min stop stop') else none

/-- Whether ranges have all of `[start, stop)`. -/
def Ranges.has (ranges : Ranges) (base : String) (start stop : Int) : Bool :=
  ranges.any fun (base', start', stop') => base == base' && start' ≤ start && stop ≤ stop'

structure State where
  env : Std.HashMap String Value := {}
  slots : List Slot := []
  /-- What every way here has written, by exact addresses. -/
  written : Ranges := []
  /-- Whether an address of the stack has left the function, to memory or to a call, so that what is written there isn't all
  that the function writes. -/
  escaped : Bool := false
  deriving Inhabited

def State.read (state : State) (var : Bap.Var) : Value :=
  match state.env[var.name.str]? with
  | some value => value
  | none =>
    match var.typ with
    | .imm width => .set (some var.name.str) width 0 0 0
    | _ => .top

def State.write (state : State) (var : Bap.Var) (value : Value) : State :=
  { state with env := state.env.insert var.name.str value }

def State.join (left right : State) : State :=
  let keys := Partition.dedup (left.env.toList.map (·.1) ++ right.env.toList.map (·.1))
  -- a register that one hasn't written holds there what it held on entry
  let entryOf (key : String) (other : Value) : Value := match other.width with
    | some width => .set (some key) width 0 0 0
    | none => .top
  let env := keys.foldl (init := ({} : Std.HashMap String Value)) fun env key =>
    let value := match left.env[key]?, right.env[key]? with
      | some a, some b => a.join b
      | some a, none => a.join (entryOf key a)
      | none, some b => (entryOf key b).join b
      | none, none => .top
    env.insert key value
  { env, slots := left.slots.filterMap fun slot =>
      (right.slots.find? fun other => other.base == slot.base && other.offset == slot.offset && other.size == slot.size).map
        fun other => { slot with value := slot.value.join other.value }
    written := left.written.inter right.written
    escaped := left.escaped || right.escaped }

/-- Whether a state has all that another has, so that a join of them is the first. -/
def State.covers (left right : State) : Bool :=
  -- a register that one hasn't written holds there what it held on entry
  let entryOf (key : String) (other : Value) : Value := match other.width with
    | some width => .set (some key) width 0 0 0
    | none => .top
  left.env.toList.all (fun (key, value) => match right.env[key]? with
    | some other => value.covers other
    | none => value.covers (entryOf key value)) &&
  right.env.toList.all (fun (key, other) => left.env.contains key || (entryOf key other).covers other) &&
  left.slots.all (fun slot =>
    right.slots.any fun other => other.base == slot.base && other.offset == slot.offset && other.size == slot.size &&
      slot.value.covers other.value) &&
  left.written.all (fun (base, start, stop) => right.written.has base start stop) &&
  (left.escaped || !right.escaped)

/-- A load or a store of a function: by the instruction at `insn`, of `size` bytes at each address of `address`. -/
structure Access where
  insn : Nat
  address : Value
  size : Nat
  write : Bool
  /-- A store of what a register held on entry to the stack, which is to save it, and which register. -/
  saves : Bool := false
  register : Option String := none
  /-- Of a load at an address of a register, whether every way here wrote it first, or an address of the stack had left. -/
  initialized : Bool := true
  deriving BEq, Repr

structure Effects where
  /-- The instruction that is run. -/
  insn : Nat := 0
  accesses : Array Access := #[]

abbrev Run := StateM Effects

def note (address : Value) (size : Nat) (write : Bool) (saves : Bool := false) (initialized : Bool := true)
    (register : Option String := none) : Run Unit :=
  modify fun effects =>
    { effects with accesses := effects.accesses.push { insn := effects.insn, address, size, write, saves, initialized, register } }

/-! ## Running BIL -/

/-- The numbers of a set of few of them. -/
def Value.elements (most : Nat := 4) : Value → Option (List Int)
  | .set none _ lo hi stride =>
    if lo == hi then some [lo]
    else if stride == 0 || (hi - lo) / stride + 1 > most then none
    else some ((List.range ((hi - lo) / stride + 1).toNat).map fun (index : Nat) => lo + (stride : Int) * (index : Int))
  | _ => none

/-- The least set of numbers of `width` bits that has all of some. -/
def Value.ofElements (width : Nat) (values : List Nat) : Value :=
  match (Partition.dedup values).mergeSort (· ≤ ·) with
  | [] => .top
  | first :: rest =>
    let stride := rest.foldl (fun stride value => Nat.gcd stride (value - first)) 0
    .range none width first (rest.getLast?.getD first) stride

/-- The value of an operation of two sets: of few numbers each, each of what they make, which an operation of a choice without a
branch, `(c - 1) & m`, is; else as the bounds of each go. -/
def binary (op : Bil.BinOp) (left right : Value) : Value :=
  match left.elements, right.elements, left, right with
  | some lefts, some rights, .set none width .., .set none width' .. =>
    let results := lefts.flatMap fun a => rights.filterMap fun b =>
      match Bil.evalExp {} (.bin op (.int (BitVec.ofNat width (a % 2 ^ width).toNat)) (.int (BitVec.ofNat width' (b % 2 ^ width').toNat))) with
      | .ok (.bits (width := w) bits) => if w == width then some bits.toNat else none
      | _ => none
    if results.length == lefts.length * rights.length && lefts.length * rights.length > 1 then Value.ofElements width results
    else binaryBounds op left right
  | _, _, _, _ => binaryBounds op left right
where
  binaryBounds (op : Bil.BinOp) (left right : Value) : Value :=
  match op, left, right with
  | _, .set none width a a' 0, .set none _ b b' 0 =>
    if a == a' && b == b' then
      match Bil.evalExp {} (.bin op (.int (BitVec.ofNat width a.toNat)) (.int (BitVec.ofNat width b.toNat))) with
      | .ok (.bits (width := w) bits) => .const w bits.toNat
      | _ => .top
    else .top
  | .add, .set base width lo hi stride, .set none _ lo' hi' stride'
  | .add, .set none _ lo' hi' stride', .set base width lo hi stride =>
    match base with
    | none => .range none width (lo + lo') (hi + hi') (Nat.gcd stride stride')
    | some _ =>
      -- what an offset is of a register is of either sign: a constant of all the bits is a negative one
      let (lo', hi') := if lo' == hi' && lo' ≥ 2 ^ (width - 1) then (lo' - 2 ^ width, hi' - 2 ^ width) else (lo', hi')
      .range base width (lo + lo') (hi + hi') (Nat.gcd stride stride')
  | .sub, .set base width lo hi stride, .set none _ lo' hi' stride' =>
    .range base width (lo - hi') (hi - lo') (Nat.gcd stride stride')
  | .sub, .set (some base) width lo hi stride, .set (some base') _ lo' hi' stride' =>
    if base == base' then .range none width (lo - hi') (hi - lo') (Nat.gcd stride stride') else .top
  | .mul, .set none width lo hi stride, .set none _ k k' 0
  | .mul, .set none _ k k' 0, .set none width lo hi stride =>
    if k == k' && k ≥ 0 then .range none width (lo * k) (hi * k) (stride * k.toNat) else .top
  | .lshift, .set none width lo hi stride, .set none _ k k' 0 =>
    if k == k' && k < width then .range none width (lo * 2 ^ k.toNat) (hi * 2 ^ k.toNat) (stride * 2 ^ k.toNat) else .top
  | .rshift, .set none width lo hi stride, .set none _ k k' 0 =>
    if k == k' then
      let shift := 2 ^ k.toNat
      .range none width (lo / shift) (hi / shift) (if stride % shift.toNat == 0 then stride / shift.toNat else 1)
    else .top
  | .and, value, .set none width m m' 0 | .and, .set none width m m' 0, value =>
    if m != m' then .top else
    -- of a mask of the low bits, what is below it; of a number that is already below it, the number; of a mask of the high bits
    -- of what a register held, as a stack pointer aligned, what isn't known, rather than a number that loses whose it is
    match value with
    | .set none _ lo hi stride => if 0 ≤ lo && hi ≤ m && (m + 1).toNat.isPowerOfTwo then .set none width lo hi stride
                                  else .range none width 0 m 1
    | .set (some _) .. => if (m + 1).toNat.isPowerOfTwo then .range none width 0 m 1 else .top
    | .top => .range none width 0 m 1
  | .rem, _, .set none width k k' 0 => if k == k' && k > 0 then .range none width 0 (k - 1) 1 else .top
  | _, _, _ => .top

/-- A value as it is of another width: of what fits, the same. -/
def resize (signed : Bool) (width : Nat) : Value → Value
  | .set none from_ lo hi stride =>
    if lo == hi then
      let value := if signed && lo ≥ 2 ^ (from_ - 1) then lo - 2 ^ from_ else lo
      .const width (value % 2 ^ width).toNat
    else if hi < 2 ^ width && (!signed || hi < 2 ^ (from_ - 1)) then .set none width lo hi stride
    else .top
  | .set (some base) from_ lo hi stride => if from_ == width then .set (some base) width lo hi stride else .top
  | .top => .top

/-- What a run of BIL is of: the stack pointer, and the registers whose values on entry are of nothing, which a store of
doesn't write anything of the function's. -/
structure Machine where
  stackPointer : String
  scratch : List String := []

mutual
  partial def eval (state : State) : Bil.Exp → Run Value
    | .int (width := width) value => pure (.const width value.toNat)
    | .var var => pure (state.read var)
    | .load _ address _ size => do
      let address ← eval state address
      let initialized := match address.single with
        | some (some base, offset) => state.escaped || state.written.has base offset (offset + size)
        | _ => true
      note address size false (initialized := initialized)
      match address.single with
      | some (some base, offset) =>
        pure ((state.slots.find? fun slot => slot.base == base && slot.offset == offset && slot.size == size).map
          (·.value) |>.getD .top)
      | _ => pure .top
    | .store .. => pure .top
    | .bin op left right => do pure (binary op (← eval state left) (← eval state right))
    | .un op value => do
      match ← eval state value with
      | .set none width lo hi 0 =>
        if lo == hi then
          match Bil.evalExp {} (.un op (.int (BitVec.ofNat width lo.toNat))) with
          | .ok (.bits (width := w) bits) => pure (.const w bits.toNat)
          | _ => pure .top
        else pure .top
      | _ => pure .top
    | .cast kind width value => do
      let inner ← eval state value
      match kind with
      | .unsigned | .low => pure (resize false width inner)
      | .signed => pure (resize true width inner)
      | .high =>
        match inner with
        | .set none from_ lo hi _ =>
          if lo == hi && width ≤ from_ then pure (.const width (lo.toNat / 2 ^ (from_ - width))) else pure .top
        | _ => pure .top
    | .letIn var value body => do
      let value ← eval state value
      eval (state.write var value) body
    | .ite condition yes no => do
      let condition ← eval state condition
      let yes ← eval state yes
      let no ← eval state no
      match condition.single with
      | some (none, 1) => pure yes
      | some (none, 0) => pure no
      | _ => pure (yes.join no)
    | .extract high low value => do
      let inner ← eval state value
      if low == 0 then pure (resize false (high + 1) inner)
      else match inner with
        | .set none width lo hi _ =>
          if lo == hi then pure (.const (high - low + 1) ((lo.toNat / 2 ^ low) % 2 ^ (high - low + 1)))
          else if hi < 2 ^ width then
            .range none (high - low + 1) (lo / 2 ^ low) (hi / 2 ^ low) 1 |> pure
          else pure .top
        | _ => pure .top
    | .concat left right => do
      let left ← eval state left
      let right ← eval state right
      match left, right with
      | .set none w a a' _, .set none w' b b' _ =>
        if a == a' && b == b' then pure (.const (w + w') (a.toNat * 2 ^ w' + b.toNat)) else pure .top
      | _, _ => pure .top
    | .unknown _ _ => pure .top

  partial def store (machine : Machine) (state : State) : Bil.Exp → Run State
    | .store memory address value _ size => do
      let state ← store machine state memory
      let address ← eval state address
      let stored ← eval state value
      let stackPointer := machine.stackPointer
      let saves := match address, stored with
        | .set (some base) _ _ _ _, .set (some _) _ 0 0 _ => base == stackPointer
        | _, _ => false
      -- what a register of nothing held on entry, stored, as i686 makes a slot with `push eax`, writes nothing
      let garbage := match stored with
        | .set (some register) _ 0 0 _ => machine.scratch.contains register
        | _ => false
      let register := match stored with
        | .set (some register) _ 0 0 _ => if saves then some register else none
        | _ => none
      note address size true saves (register := register)
      -- an address of the stack stored is one that has left, but the stack pointer as it was, which PowerPC keeps in its frame
      let state := match stored with
        | .set (some base) _ _ _ _ => if base == stackPointer && !saves then { state with escaped := true } else state
        | _ => state
      match address with
      | .set (some base) _ lo hi _ =>
        let kept := state.slots.filter fun slot =>
          slot.base != base || slot.offset + slot.size ≤ lo || hi + size ≤ slot.offset
        if lo == hi then
          pure { state with slots := { base, offset := lo, size, value := stored } :: kept
                            written := if garbage then state.written else state.written.add base lo (lo + size) }
        else pure { state with slots := kept }
      | _ => pure state
    | .var _ => pure state
    | .letIn var value body => do
      let value ← eval state value
      store machine (state.write var value) body
    | _ => pure { state with slots := [] }
end

mutual
  partial def exec (machine : Machine) (state : State) : Bil.Program → Run State
    | [] => pure state
    | stmt :: rest => do
      let (state, jumped) ← execStmt machine state stmt
      if jumped then pure state else exec machine state rest

  /-- What a statement does, and whether it jumps, which leaves the instruction. -/
  partial def execStmt (machine : Machine) (state : State) : Bil.Stmt → Run (State × Bool)
    | .move var value => do
      match var.typ with
      | .mem _ _ => pure (← store machine state value, false)
      | _ => pure (state.write var (← eval state value), false)
    | .jmp target => do
      let _ ← eval state target
      pure (state, true)
    | .special _ | .cpuExn _ => pure (state, false)
    | .ifElse condition yes no => do
      match (← eval state condition).single with
      | some (none, 1) => pure (← exec machine state yes, false)
      | some (none, 0) => pure (← exec machine state no, false)
      | _ => pure ((← exec machine state yes).join (← exec machine state no), false)
    | .while _ body => do
      let rec loop : Nat → State → Run State
        | 0, _ => pure {}
        | fuel + 1, state => do
          let next ← exec machine state body
          let joined := state.join next
          if state.covers joined then pure joined else loop fuel joined
      pure (← loop 4 state, false)
end

/-! ## A function -/

/-- The context of a function: its convention, as `Frame` has it, and its frame. -/
structure Context where
  frame : Frame.Context
  stackPointer : Bap.Var
  deltas : Std.HashMap Nat Int
  machine : Machine
  /-- What registers hold on entry to each function, as MIPS's gp has `_gp` in code that isn't of PIC. -/
  entryRegisters : List (String × Nat) := []

/-- What an instruction does: the stack pointer before it is as its frame has it, and a call clobbers what its convention doesn't
keep. -/
def step (context : Context) (insn : Disasm.Insn) (state : State) : Run State := do
  let state := match context.deltas[insn.address]?, context.stackPointer.typ with
    | some delta, .imm width => state.write context.stackPointer (.set (some context.stackPointer.name.str) width delta delta 0)
    | _, _ => state
  modify fun effects => { effects with insn := insn.address }
  let after ← exec context.machine state insn.bil
  let after := { after with env := after.env.filter fun name _ => !name.startsWith "_" }
  if insn.flow != .call then return after
  -- an address of the stack that a call is given has left
  let given := (context.frame.convention.functionArguments ++ context.frame.convention.floatArguments).any fun var =>
    match after.read var with
    | .set (some base) _ _ _ _ => base == context.stackPointer.name.str
    | _ => false
  let after := if given then { after with escaped := true } else after
  return context.frame.volatile.foldl (init := after) fun state (name : String) =>
    state.write (⟨name, .imm context.frame.width, 0, false⟩ : Bap.Var) .top

/-- The accesses of a function, run over its flow to where nothing changes, with each bound widened to what isn't known when it
has grown a few times. -/
def analyze (context : Context) (program : Frame.Program) (function : Partition.Function) :
    Array Access × Std.HashMap Nat State := Id.run do
  let instructions : Std.HashMap Nat Disasm.Insn := function.instructions.foldl (init := {}) fun table address =>
    match program.instructions[address]? with
    | some insn => table.insert address insn
    | none => table
  let successors (address : Nat) : List Nat := (program.successors.getD address []).filter instructions.contains
  let initial : State := context.entryRegisters.foldl (init := {}) fun state (name, value) =>
    state.write (⟨name, .imm context.frame.width, 0, false⟩ : Bap.Var) (.const context.frame.width value)
  -- of 64-bit PowerPC of ELFv2, r12 has the address of the global entry, which r2, the pointer to the TOC, is made of; of MIPS,
  -- t9 has it, which gp is made of in code of PIC
  let initial : State := match context.frame.arch, context.frame.width with
    | .powerpc, 64 => initial.write (⟨"R12", .imm 64, 0, false⟩ : Bap.Var) (.const 64 function.entry)
    | .mips, width => initial.write (⟨"R25", .imm width, 0, false⟩ : Bap.Var) (.const width function.entry)
    | _, _ => initial
  let mut states : Std.HashMap Nat State := ({} : Std.HashMap Nat State).insert function.entry initial
  let mut work : Array Nat := #[function.entry]
  let mut next := 0
  let mut joins : Std.HashMap Nat Nat := {}
  let mut accesses : Std.HashMap Nat (Array Access) := {}
  let mut fuel := 64 * instructions.size + 64
  while next < work.size && fuel > 0 do
    fuel := fuel - 1
    let address := work[next]!
    next := next + 1
    let some insn := instructions[address]? | continue
    let (after, seen) := (step context insn (states.getD address {})).run {}
    -- what an instruction accesses is what it did of the last state it was run of, which has what the others had
    accesses := accesses.insert address seen.accesses
    for target in successors address do
      match states[target]? with
      | none =>
        states := states.insert target after
        work := work.push target
      | some old =>
        if !old.covers after then
          let count := joins.getD target 0
          joins := joins.insert target (count + 1)
          let joined := old.join after
          let env := joined.env.fold (init := joined.env) fun env key value =>
            if old.env[key]? == some value then env else env.insert key .top
          let widened : State := if count < 3 then joined else
            { joined with env, slots := joined.slots.filter fun slot => old.slots.contains slot }
          states := states.insert target widened
          work := work.push target
  return (accesses.fold (init := (#[] : Array Access)) fun all _ seen => all ++ seen, states)

/-! ## Variables -/

/-- What a variable is of a frame. -/
inductive Kind where
  /-- Of the function's own, as C's automatic variables. -/
  | automatic
  /-- Where a register is saved, to be restored. -/
  | saved
  /-- Above the stack pointer on entry: the return address, of x86, or arguments in memory. -/
  | argument
  | global
  deriving BEq, Repr, DecidableEq

/-- A variable: `size` bytes from `start`, an offset from the stack pointer on entry, or an address. -/
structure Variable where
  start : Int
  size : Nat
  kind : Kind
  /-- The instructions that read it, and those that write it. -/
  readers : List Nat
  writers : List Nat
  deriving Repr

/-- The variables of accesses: each from the least to the most of the addresses that it covers, where what overlaps is one. -/
def variables (spans : List (Int × Int × Access)) (kindOf : Int → List Access → Kind) : List Variable :=
  let sorted := spans.mergeSort fun a b => a.1 ≤ b.1
  let groups := sorted.foldl (init := ([] : List (Int × Int × List Access))) fun groups (start, stop, access) =>
    match groups with
    | (first, last, members) :: rest =>
      if start < last then (first, max last stop, access :: members) :: rest
      else (start, stop, [access]) :: groups
    | [] => [(start, stop, [access])]
  groups.reverse.map fun (start, stop, members) =>
    { start, size := (stop - start).toNat, kind := kindOf start members
      readers := Partition.dedup ((members.filter (!·.write)).map (·.insn)) |>.mergeSort (· ≤ ·)
      writers := Partition.dedup ((members.filter (·.write)).map (·.insn)) |>.mergeSort (· ≤ ·) }

/-- What a function was found to have. -/
structure Function where
  entry : Nat
  accesses : Array Access
  /-- The variables of its stack, by their offsets from the stack pointer on entry. -/
  stack : List Variable

/-- A global variable, with the functions that read it and those that write it. -/
structure Global where
  extent : Variable
  name : Option String
  readers : List Nat
  writers : List Nat
  deriving Repr

structure Variables where
  functions : List Function
  globals : List Global

def Variables.functionAt (variables : Variables) (entry : Nat) : Option Function :=
  variables.functions.find? (·.entry == entry)

/-- The variable that has an address, of the globals. -/
def Variables.globalAt (variables : Variables) (address : Nat) : Option Global :=
  variables.globals.find? fun found => found.extent.start ≤ address && address < found.extent.start + found.extent.size

/-- The context of a function of a partition of an image, as its frame has it. -/
def contextOf (image : Image.Image) (frames : Frame.Frames) (convention : ABI.Convention) (function : Partition.Function) :
    Context :=
  let width := image.addrWidth
  let frame : Frame.Context := { arch := image.arch, width, convention, calleeSaved := Frame.calleeSaved image.arch width
                                 volatile := Frame.volatileOf image.arch convention }
  -- of MIPS, gp has `_gp`, which the code of a program that isn't of PIC doesn't set
  let entryRegisters := match image.arch, image.symbols.find? (·.name == "_gp") with
    | .mips, some symbol => [("R28", symbol.addr)]
    | _, _ => []
  -- of nothing on entry: what a call clobbers, but the arguments and the return address
  let carried := convention.functionArguments.map (·.name.str) ++ convention.floatArguments.map (·.name.str) ++
    (Partition.linkRegister image.arch).toList
  let scratch := frame.volatile.filter fun name => !carried.contains name
  { frame, stackPointer := convention.stackPointer, entryRegisters
    machine := { stackPointer := convention.stackPointer.name.str, scratch }
    deltas := (frames.frameOf function.entry).map (·.deltas) |>.getD {} }

/-- The variables of the functions of a partition of an image, and those of the program. -/
def ofPartition (image : Image.Image) (partition : Partition) (frames : Frame.Frames) : Option Variables := do
  let convention ← ABI.convention image.arch image.addrWidth
  let program := Frame.Program.of partition
  let stackPointer := convention.stackPointer.name.str
  let functions := partition.functions.map fun function =>
    let (accesses, _) := analyze (contextOf image frames convention function) program function
    let spans := accesses.toList.filterMap fun access =>
      match access.address with
      | .set (some base) _ lo hi _ => if base == stackPointer then some (lo, hi + access.size, access) else none
      | _ => none
    let kindOf (start : Int) (members : List Access) : Kind :=
      if start ≥ 0 then .argument
      else if members.all (fun access => !access.write || access.saves) then .saved
      else .automatic
    { entry := function.entry, accesses, stack := variables spans kindOf }
  -- the globals: what is accessed at numbers, of what the image maps but its code
  let mapped (address : Nat) : Bool :=
    image.sections.any fun part => part.addr ≤ address && address < part.addr + part.size && part.addr != 0
  let spans := functions.flatMap fun function => function.accesses.toList.filterMap fun access =>
    match access.address with
    | .set none _ lo hi _ =>
      if mapped lo.toNat && mapped hi.toNat && !Partition.inCode image lo.toNat then some (lo, hi + access.size, access)
      else none
    | _ => none
  let ownerOf : Std.HashMap Nat Nat := functions.foldl (init := {}) fun table function =>
    function.accesses.foldl (init := table) fun table access => table.insert access.insn function.entry
  let globals := (variables spans fun _ _ => .global).map fun extent =>
    -- of the symbols there, not those that only say what is data or code, as `$d` of ARM
    let name := (image.symbols.find? fun symbol =>
      symbol.addr == extent.start.toNat && !symbol.name.isEmpty && !symbol.name.startsWith "$").map (·.name)
    { extent, name
      readers := Partition.dedup (extent.readers.filterMap ownerOf.get?) |>.mergeSort (· ≤ ·)
      writers := Partition.dedup (extent.writers.filterMap ownerOf.get?) |>.mergeSort (· ≤ ·) }
  pure { functions, globals }

/-! ## Jump tables of what value sets know -/

/-- The registers that hold a constant before each instruction of the functions of a partition that have an indirect jump it
left unresolved: what a path to one of them starts with, where it starts after a join or a call that `Partition` doesn't go
back over, as a base of a table set before a loop is. -/
def constantsOfUnresolved (image : Image.Image) (partition : Partition) (frames : Frame.Frames) :
    Option (Std.HashMap Nat (List (String × Nat × Nat))) := do
  let convention ← ABI.convention image.arch image.addrWidth
  let program := Frame.Program.of partition
  let functions := partition.functions.filter fun function =>
    partition.unresolved.any function.instructions.contains
  pure <| functions.foldl (init := {}) fun table function =>
    let (_, states) := analyze (contextOf image frames convention function) program function
    states.fold (init := table) fun table address state =>
      let constants := state.env.toList.filterMap fun (name, value) =>
        match value with
        | .set none width lo hi _ => if lo == hi && !name.startsWith "_" then some (name, width, lo.toNat) else none
        | _ => none
      if constants.isEmpty then table else table.insert address constants

/-- The partition of a project, with the tables that what value sets know of the registers resolves: of those it left
unresolved, a base that a register holds from before a join. The targets that `observed` gives a jump are its targets where the code
doesn't say them, as those that a run saw. -/
def partition (project : Project.Project) (observed : Nat → List Nat := fun _ => []) : IO (Option Partition) := do
  let some first ← Partition.partition project (observed := observed) | return none
  let some image := project.image | return some first
  if first.unresolved.isEmpty then return some first
  let some frames := Frame.frames image first | return some first
  let some known := constantsOfUnresolved image first frames | return some first
  if known.isEmpty then return some first
  match ← Partition.partition project (known := fun address => known.getD address []) (observed := observed) with
  | some again => return some (if again.unresolved.length < first.unresolved.length then again else first)
  | none => return some first

end Bap.Analysis.Values
