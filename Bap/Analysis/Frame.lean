import Bap.Analysis.Partition
import Bap.ABI

/-! # The frames of functions: stack deltas and calling conventions

What ROSE's `StackDelta` and `CallingConvention` analyses find, of the functions of a `Partition`: how far the stack pointer is from
where it was on entry, before each instruction and after each return; which registers a function reads before it writes them,
which are its inputs; what it reads above its frame, which are its arguments on the stack; which registers it gives back as they
were, of those that its convention has it keep; and which it changes. Of these, its signature, as its convention has it.

The values are an abstract domain, run forward over the flow of a function: a register holds what a register held on entry plus a
constant, a constant, what a call left in its result register, or what isn't known. Memory is the slots of the stack, at constants
from what a register held on entry, which a store sets and a load reads. A store through an address that isn't one of those is taken
not to change the stack, as ROSE also has it: what a function writes through its arguments isn't its own frame. A call does what its
callee was found to do to the stack pointer, or what leaves it as it was, and clobbers what its convention doesn't keep; whether a
function returns a value is whether a caller reads what it left in its result register before it writes it, as ROSE's
`ReturnValueUsed` has it, or the caller of one that calls it in its tail does.

An argument is read where what it held on entry is computed with, stored to what isn't the function's own stack, loaded through,
returned, or passed on to a callee: a store of a register as it is to the stack saves or spills it, which reads nothing, and a
copy of it is read where the copy is. A callee that was found to take `n` arguments is passed the first `n` registers of the
convention, of which those that still hold what one held on entry are read by the call, in its tail too; and what it reads of
its own arguments on the stack that the caller didn't write there is the caller's arguments. Of a callee that isn't known, a call
through a pointer or of an import, the registers passed are those that hold what they held on entry, from the first for as long
as they do: that is the most it can be passing on, and the count of such a function is the most that it takes (`Frame.open`). A
callee of a cycle, which has no count yet, passes nothing on. A function that returns with its result register as it was on entry
returns its argument if that register is one, as the first is of most conventions, and a caller uses what it returns; if none
does, the register is only left alone. -/

namespace Bap.Analysis.Frame

open Bap.Analysis.Partition (Partition)

/-- What a register or a slot holds. -/
inductive Value where
  | top
  | const (width value : Nat)
  /-- What register `name` held on entry, plus `offset`, of its width. -/
  | entry (name : String) (width offset : Nat)
  /-- What the call of a function left in the result register. -/
  | result (callee width : Nat)
  deriving BEq, Repr, Inhabited

def Value.width : Value → Option Nat
  | .top => none
  | .const width _ | .entry _ width _ | .result _ width => some width

/-- A slot of memory at a constant from what a register held on entry, of `size` bytes. -/
structure Slot where
  base : String
  offset : Nat
  size : Nat
  value : Value
  deriving BEq, Repr

structure State where
  /-- The registers that don't hold what they held on entry. -/
  env : Std.HashMap String Value := {}
  slots : List Slot := []
  deriving Inhabited

/-- What the runs of a function saw. -/
structure Effects where
  /-- The registers read as they were on entry, but to be saved. -/
  inputs : Std.HashSet String := {}
  /-- The offsets from the stack pointer on entry that it read above itself. -/
  stackReads : Std.HashSet Nat := {}
  /-- The functions whose results it read. -/
  usedResults : Std.HashSet Nat := {}
  /-- Whether registers were taken to be passed to a callee that isn't known. -/
  «open» : Bool := false

/-- What is had of a function that a call of it does. -/
structure Summary where
  /-- How far a return leaves the stack pointer from where it was on entry. -/
  returnDelta : Option Int := none
  /-- How many of the registers of the arguments of its convention it takes, of integers and of floating point, where that is
  known: not of one that passes them on to what isn't known. -/
  registerArguments : Option (Nat × Nat) := none
  /-- The offsets of its arguments in memory, from the stack pointer on entry. -/
  stackArguments : List Nat := []

/-- The convention of a function, and its registers. -/
structure Context where
  arch : Image.Arch
  width : Nat
  convention : ABI.Convention
  calleeSaved : List String
  volatile : List String
  summaries : Std.HashMap Nat Summary := {}
  /-- The function that each call calls, by the address of the call: its entry, of an entry of it that is another's alias, as the
  local entry of a function of 64-bit PowerPC of ELFv2 is of its global entry. -/
  callees : Std.HashMap Nat Nat := {}

/-! ## The registers of the conventions -/

/-- The registers that a callee keeps, of each ABI of the System V family, Linux's of each architecture. -/
def calleeSaved (arch : Image.Arch) (width : Nat) : List String :=
  let numbered (prefix_ : String) (first last : Nat) : List String :=
    (List.range (last - first + 1)).map fun index => s!"{prefix_}{first + index}"
  match arch with
  | .x86_64 => ["RBX", "RBP", "R12", "R13", "R14", "R15"]
  | .x86 => ["EBX", "ESI", "EDI", "EBP"]
  | .aarch64 => numbered "X" 19 29
  | .arm => numbered "R" 4 11
  | .riscv => ["X8", "X9"] ++ numbered "X" 18 27
  | .mips => numbered "R" 16 23 ++ ["R30"] ++ (if width == 64 then ["R28"] else [])
  | .powerpc => numbered "R" 14 31 ++ (if width == 64 then ["R2"] else [])
  | .systemz => numbered "R" 6 13
  | .unknown => []

/-- The registers that a call clobbers: those of its arguments and its result, and the scratch ones of each ABI. -/
def volatileOf (arch : Image.Arch) (convention : ABI.Convention) : List String :=
  let numbered (prefix_ : String) (first last : Nat) : List String :=
    (List.range (last - first + 1)).map fun index => s!"{prefix_}{first + index}"
  let scratch := match arch with
    | .x86_64 => ["RAX", "RCX", "RDX", "RSI", "RDI", "R8", "R9", "R10", "R11"]
    | .x86 => ["EAX", "ECX", "EDX"]
    | .aarch64 => numbered "X" 0 18 ++ ["X30"]
    | .arm => numbered "R" 0 3 ++ ["R12", "LR"]
    | .riscv => ["X1"] ++ numbered "X" 5 7 ++ numbered "X" 10 17 ++ numbered "X" 28 31
    | .mips => numbered "R" 1 15 ++ ["R24", "R25", "R31"]
    | .powerpc => ["R0"] ++ numbered "R" 3 12 ++ ["LR", "CTR"]
    | .systemz => numbered "R" 0 5 ++ ["R14"]
    | .unknown => []
  dedupStrings (convention.functionArguments.map (·.name.str) ++ convention.floatArguments.map (·.name.str) ++
    [convention.result.name.str] ++ scratch)
where
  dedupStrings (names : List String) : List String := Partition.dedup names

/-! ## Values -/

/-- A number of `width` bits as an integer. -/
def signed (width value : Nat) : Int :=
  if value < 2 ^ (width - 1) then value else (value : Int) - 2 ^ width

/-- A constant as a BIL expression. -/
def Value.asExp : Value → Option Bil.Exp
  | .const width value => some (.int (BitVec.ofNat width value))
  | _ => none

/-- The value of a closed BIL expression. -/
def fold (exp : Bil.Exp) : Value :=
  match Bil.evalExp {} exp with
  | .ok (.bits (width := width) bits) => .const width bits.toNat
  | _ => .top

/-- The join of two values: the same, or what isn't known. -/
def Value.join (left right : Value) : Value := if left == right then left else .top

/-- What a register holds in a state. -/
def State.read (state : State) (var : Bap.Var) : Value :=
  match state.env[var.name.str]? with
  | some value => value
  | none =>
    match var.typ with
    | .imm width => .entry var.name.str width 0
    | _ => .top

def State.write (state : State) (var : Bap.Var) (value : Value) : State :=
  match var.typ, value with
  | .imm width, .entry name width' 0 =>
    if name == var.name.str && width == width' then { state with env := state.env.erase var.name.str }
    else { state with env := state.env.insert var.name.str value }
  | _, _ => { state with env := state.env.insert var.name.str value }

/-- The join of two states: each register and slot as both have it, or what isn't known. -/
def State.join (left right : State) : State :=
  let keys := Partition.dedup (left.env.toList.map (·.1) ++ right.env.toList.map (·.1))
  let env := keys.foldl (init := ({} : Std.HashMap String Value)) fun env key =>
    let value := match left.env[key]?, right.env[key]? with
      | some a, some b => a.join b
      | _, _ => .top
    env.insert key value
  { env, slots := left.slots.filter fun slot => right.slots.contains slot }

def State.same (left right : State) : Bool :=
  left.env.size == right.env.size && left.env.toList.all (fun (key, value) => right.env[key]? == some value) &&
    left.slots.length == right.slots.length && left.slots.all right.slots.contains

/-! ## Running BIL -/

abbrev Run := StateM Effects

/-- That a register was read as it was on entry. -/
def noteInput (name : String) : Run Unit :=
  modify fun effects => { effects with inputs := effects.inputs.insert name }

/-- Whether an expression is a register as it is, or what is loaded as it is, which a copy or a store of it moves rather than
reads. -/
def plainVar : Bil.Exp → Bool
  | .var _ | .cast _ _ (.var _) | .extract _ _ (.var _) | .load .. => true
  | _ => false

mutual
  /-- The value of an expression. `quiet` reads registers without taking them for inputs, which a store of one to save it does. -/
  partial def eval (context : Context) (state : State) (quiet : Bool) : Bil.Exp → Run Value
    | .int (width := width) value => pure (.const width value.toNat)
    | .var var => do
      let value := state.read var
      match value with
      | .entry name _ 0 => if !quiet then noteInput name
      | .result callee _ => modify fun effects => { effects with usedResults := effects.usedResults.insert callee }
      | _ => pure ()
      pure value
    | .load _ address _ size => do
      let address ← eval context state false address
      match address with
      | .entry base width offset =>
        if base == context.convention.stackPointer.name.str then
          let from_ := signed width offset
          if from_ ≥ (context.convention.stackArgumentsStart : Int) then
            modify fun effects => { effects with stackReads := effects.stackReads.insert from_.toNat }
        let value := (state.slots.find? fun slot => slot.base == base && slot.offset == offset && slot.size == size).map
          (·.value) |>.getD .top
        -- what a register held on entry, spilled and loaded again, is read where what is loaded is
        match value with
        | .entry name _ 0 => if !quiet then noteInput name
        | .result callee _ => modify fun effects => { effects with usedResults := effects.usedResults.insert callee }
        | _ => pure ()
        pure value
      | _ => pure .top
    | .store .. => pure .top
    | .bin op left right => do
      let left ← eval context state false left
      let right ← eval context state false right
      match op, left, right with
      | .add, .entry name width offset, .const _ value | .add, .const _ value, .entry name width offset =>
        pure (.entry name width ((offset + value) % 2 ^ width))
      | .sub, .entry name width offset, .const _ value =>
        pure (.entry name width ((offset + 2 ^ width - value % 2 ^ width) % 2 ^ width))
      | _, .const _ _, .const _ _ =>
        match left.asExp, right.asExp with
        | some l, some r => pure (fold (.bin op l r))
        | _, _ => pure .top
      | _, _, _ => pure .top
    | .un op value => do
      match ← eval context state false value with
      | .const width bits => pure (fold (.un op (.int (BitVec.ofNat width bits))))
      | _ => pure .top
    | .cast kind width value => do
      let inner ← eval context state quiet value
      match inner with
      | .const w bits => pure (fold (.cast kind width (.int (BitVec.ofNat w bits))))
      | other => pure (if other.width == some width then other else .top)
    | .letIn var value body => do
      let value ← eval context state quiet value
      eval context (state.write var value) quiet body
    | .ite condition yes no => do
      let condition ← eval context state false condition
      let yes ← eval context state quiet yes
      let no ← eval context state quiet no
      match condition with
      | .const _ 1 => pure yes
      | .const _ 0 => pure no
      | _ => pure (yes.join no)
    | .extract high low value => do
      let inner ← eval context state quiet value
      match inner with
      | .const w bits => pure (fold (.extract high low (.int (BitVec.ofNat w bits))))
      | other => pure (if low == 0 && other.width == some (high + 1) then other else .top)
    | .concat left right => do
      let left ← eval context state false left
      let right ← eval context state false right
      match left.asExp, right.asExp with
      | some l, some r => pure (fold (.concat l r))
      | _, _ => pure .top
    | .unknown _ _ => pure .top

  /-- The stores of a value of memory, in order, on the slots. -/
  partial def store (context : Context) (state : State) : Bil.Exp → Run State
    | .store memory address value _ size => do
      let state ← store context state memory
      let address ← eval context state false address
      -- what a register held on entry, stored as it is to the stack, is saved or spilled rather than read
      let ownStack := match address with
        | .entry base _ _ => base == context.convention.stackPointer.name.str
        | _ => false
      let value ← eval context state (ownStack && plainVar value) value
      match address with
      | .entry base _ offset =>
        let kept := state.slots.filter fun slot =>
          slot.base != base || slot.offset + slot.size ≤ offset || offset + size ≤ slot.offset
        pure { state with slots := { base, offset, size, value } :: kept }
      | _ => pure state
    | .var _ => pure state
    | .letIn var value body => do
      let value ← eval context state false value
      store context (state.write var value) body
    | _ => pure { state with slots := [] }
end

/-- How a program ends: on, or by a jump to a value. -/
inductive Ending where
  | on
  | jump (target : Value)
  deriving Inhabited

mutual
  partial def exec (context : Context) (state : State) : Bil.Program → Run (State × Ending)
    | [] => pure (state, .on)
    | stmt :: rest => do
      let (state, ending) ← execStmt context state stmt
      match ending with
      | .on => exec context state rest
      | jump => pure (state, jump)

  partial def execStmt (context : Context) (state : State) : Bil.Stmt → Run (State × Ending)
    | .move var value => do
      match var.typ with
      | .mem _ _ => pure (← store context state value, .on)
      -- a copy of a register is read where the copy is
      | _ => pure (state.write var (← eval context state (plainVar value) value), .on)
    | .jmp target => do pure (state, .jump (← eval context state false target))
    | .special _ | .cpuExn _ => pure (state, .on)
    | .ifElse condition yes no => do
      match ← eval context state false condition with
      | .const _ 1 => exec context state yes
      | .const _ 0 => exec context state no
      | _ =>
        let (yesState, yesEnd) ← exec context state yes
        let (noState, noEnd) ← exec context state no
        -- a branch that jumps leaves the instruction, so what goes on is what the other does
        match yesEnd, noEnd with
        | .jump _, .on => pure (noState, .on)
        | .on, .jump _ => pure (yesState, .on)
        | .jump a, .jump b => pure (yesState.join noState, .jump (a.join b))
        | .on, .on => pure (yesState.join noState, .on)
    | .while _ body => do
      let rec loop : Nat → State → Run State
        | 0, state => pure state
        | fuel + 1, state => do
          let (next, _) ← exec context state body
          let joined := state.join next
          if joined.same state then pure joined else loop fuel joined
      pure (← loop 4 state, .on)
end

/-! ## A function -/

/-- What is had of a function. -/
structure Frame where
  entry : Nat
  /-- The stack pointer before each instruction, from where it was on entry, where it is known. -/
  deltas : Std.HashMap Nat Int := {}
  /-- Where a return leaves the stack pointer from where it was on entry, if all its returns agree. -/
  returnDelta : Option Int := none
  /-- The registers it reads as they were on entry, but to save them. -/
  inputs : List String := []
  /-- The offsets from the stack pointer on entry that it reads above it, which are its arguments in memory. -/
  stackArguments : List Nat := []
  /-- Of the registers that its convention keeps, those it gives back as they were, and those it doesn't. -/
  preserved : List String := []
  clobbered : List String := []
  /-- Of the functions it calls, those whose results it reads. -/
  usedResults : List Nat := []
  /-- Whether its inputs are the most it takes rather than what it takes: it passes registers on to a callee that isn't known. -/
  «open» : Bool := false
  /-- Whether a return of it leaves the result register as it was on entry. -/
  passesResult : Bool := false
  deriving Inhabited

/-- What a stack pointer is, where it is a constant from where it was on entry. -/
def deltaOf (context : Context) (state : State) : Option Int :=
  match state.read context.convention.stackPointer with
  | .entry name width offset =>
    if name == context.convention.stackPointer.name.str then some (signed width offset) else none
  | _ => none

/-- What an instruction does, of what it was in: a call does what its callee does to the stack pointer and clobbers what its
convention doesn't keep, with what is below the stack pointer, which is of the callee. -/
def plain (context : Context) (insn : Disasm.Insn) (state : State) : Run State := do
  let (after, _) ← exec context state insn.bil
  -- what is of the instruction alone, its temporaries, goes with it
  return { after with env := after.env.filter fun name _ => !name.startsWith "_" }

/-- What a callee is passed of what the function itself was entered with, in the state that the callee is entered in: `callee`
is where it is, if that is known. -/
def passes (context : Context) (callee : Option Nat) (after : State) : Run Unit := do
  -- what was copied to an argument is read by the call
  for var in context.convention.functionArguments ++ context.convention.floatArguments do
    match after.read var with
    | .entry name _ 0 => if name != var.name.str then noteInput name
    | _ => pure ()
  let own (var : Bap.Var) : Bool := match after.read var with
    | .entry name _ 0 => name == var.name.str
    | _ => false
  match callee, callee.bind context.summaries.get? with
  | some _, none => pure ()
  | _, some { registerArguments := some (integers, floats), .. } =>
    for var in context.convention.functionArguments.take integers ++ context.convention.floatArguments.take floats do
      if own var then noteInput var.name.str
  | _, _ =>
    let passed := context.convention.functionArguments.takeWhile own
    for var in passed do noteInput var.name.str
    if !passed.isEmpty then modify fun effects => { effects with «open» := true }
  -- an argument of the callee on the stack that wasn't written is one of the function's own, and one saved there as it was is passed
  let sp := context.convention.stackPointer
  match callee.bind context.summaries.get?, after.read sp with
  | some summary, .entry base width offset =>
    if base == sp.name.str then
      for argument in summary.stackArguments do
        let at_ := (offset + argument) % 2 ^ width
        match after.slots.find? fun slot => slot.base == base && slot.offset ≤ at_ && at_ < slot.offset + slot.size with
        | some { value := .entry name _ 0, .. } => noteInput name
        | some _ => pure ()
        | none =>
          let from_ := signed width at_
          if from_ ≥ (context.convention.stackArgumentsStart : Int) then
            modify fun effects => { effects with stackReads := effects.stackReads.insert from_.toNat }
  | _, _ => pure ()

/-- What a call does after it, of the state before it and after what it does itself, and after its delay slot if it has one. -/
def callEffects (context : Context) (insn : Disasm.Insn) (state after : State) : Run State := do
  let sp := context.convention.stackPointer
  let pushed := match deltaOf context state, deltaOf context after with
    | some before, some later => later - before
    | _, _ => 0
  let callee := context.callees[insn.address]? <|> insn.target
  passes context callee after
  let calleeReturn : Int := ((callee.bind context.summaries.get?).bind (·.returnDelta)).getD (-pushed)
  let moved := match after.read sp with
    | .entry name width offset =>
      let delta := calleeReturn
      Value.entry name width (((offset : Int) + delta).toNat % 2 ^ width)
    | other => other
  let after := after.write sp moved
  let resultValue : Value := match callee, context.convention.result.typ with
    | some callee, .imm width => .result callee width
    | _, _ => .top
  let after := context.volatile.foldl (init := after) fun (state : State) (name : String) =>
    let var : Bap.Var := ⟨name, .imm context.width, 0, false⟩
    if name == context.convention.result.name.str then state.write var resultValue else state.write var .top
  -- what is below the stack pointer is the callee's
  match moved with
  | .entry name width offset =>
    let below (slot : Slot) : Bool := slot.base == name && signed width slot.offset < signed width offset
    return { after with slots := after.slots.filter fun slot => !below slot }
  | _ => return after

def step (context : Context) (insn : Disasm.Insn) (state : State) : Run State := do
  let after ← plain context insn state
  if insn.flow != .call then return after
  callEffects context insn state after

/-- The instructions of a program by their addresses, and where each goes. -/
structure Program where
  instructions : Std.HashMap Nat Disasm.Insn
  successors : Std.HashMap Nat (List Nat)

def Program.of (partition : Partition) : Program where
  instructions := partition.disasm.instructions.foldl (init := {}) fun table insn => table.insert insn.address insn
  successors := partition.edges.foldl (init := {}) fun table (source, target) =>
    table.insert source (target :: table.getD source [])

/-- The frame of a function, run over its flow to where nothing changes. -/
def analyze (context : Context) (program : Program) (function : Partition.Function) : Frame := Id.run do
  let instructions : Std.HashMap Nat Disasm.Insn := function.instructions.foldl (init := {}) fun table address =>
    match program.instructions[address]? with
    | some insn => table.insert address insn
    | none => table
  let successors (address : Nat) : List Nat := (program.successors.getD address []).filter instructions.contains
  -- of 64-bit PowerPC of ELFv2, r12 has the address of the global entry, which r2, the pointer to the TOC, is made of
  let initial : State := if context.arch == .powerpc && context.width == 64 then
      ({} : State).write (⟨"R12", .imm 64, 0, false⟩ : Bap.Var) (.const 64 function.entry)
    else {}
  let mut states : Std.HashMap Nat State := ({} : Std.HashMap Nat State).insert function.entry initial
  -- the work, first in first out: what is at `next` and after it
  let mut work : Array Nat := #[function.entry]
  let mut next := 0
  let mut effects : Effects := {}
  let mut visits : Std.HashMap Nat Nat := {}
  let mut returns : List State := []
  let mut calls : Std.HashMap Nat (Disasm.Insn × State) := {}
  let tailCalls : Std.HashMap Nat Nat := function.tailCalls.foldl (init := {}) fun table (jump, target) => table.insert jump target
  let mut fuel := 64 * instructions.size + 64
  while next < work.size && fuel > 0 do
    fuel := fuel - 1
    let address := work[next]!
    next := next + 1
    let some insn := instructions[address]? | continue
    let state := states.getD address {}
    -- a call of MIPS with a delay slot calls after its slot, which may move what it is called with
    let action : Run State :=
      if insn.flow == .call && Partition.mipsSlotted context.arch insn then plain context insn state
      else match calls[address]? with
        | some (call, before) => do callEffects context call before (← step context insn state)
        | none => step context insn state
    let (after, seen) := action.run effects
    if insn.flow == .call && Partition.mipsSlotted context.arch insn then calls := calls.insert insn.next (insn, state)
    effects := seen
    if insn.flow == .ret || Partition.returnsBy context.arch insn then
      -- a return of MIPS but a compact one returns after its delay slot, which may restore the stack pointer
      let slot := if Partition.mipsSlotted context.arch insn then instructions[insn.next]? else none
      match slot with
      | some slot =>
        let (returned, seen) := (step context slot after).run effects
        effects := seen
        returns := returned :: returns
      | none => returns := after :: returns
    else
      -- a jump out of the function, to the entry of another or to where isn't known, is a call in its tail, which of MIPS is
      -- after its delay slot
      let tail : Option (Option Nat) := match tailCalls[address]? with
        | some target => some (some target)
        | none => if insn.flow == .indirectJump && (successors address).isEmpty then some none else none
      if let some callee := tail then
        let slot := if Partition.mipsSlotted context.arch insn then instructions[insn.next]? <|> program.instructions[insn.next]? else none
        let entered : Run Unit := do
          let state ← match slot with
            | some slot => plain context slot after
            | none => pure after
          passes context callee state
        effects := (entered.run effects).2
    for target in successors address do
      let count := visits.getD target 0
      match states[target]? with
      | none =>
        states := states.insert target after
        work := work.push target
      | some old =>
        let joined := old.join after
        if !joined.same old && count < 32 then
          visits := visits.insert target (count + 1)
          states := states.insert target joined
          work := work.push target
  let deltas := states.fold (init := ({} : Std.HashMap Nat Int)) fun table address state =>
    match deltaOf context state with
    | some delta => table.insert address delta
    | none => table
  let returnDeltas := Partition.dedup (returns.map (deltaOf context))
  let returnDelta := match returnDeltas with
    | [some delta] => some delta
    | _ => none
  -- the pointer to the TOC of 64-bit PowerPC is kept as long as it is the TOC, which is one of the whole program
  let keeps (name : String) : Bool := !returns.isEmpty && returns.all fun state =>
    match state.read (⟨name, .imm context.width, 0, false⟩ : Bap.Var) with
    | .entry other _ 0 => other == name
    | .const _ _ => context.arch == .powerpc && context.width == 64 && name == "R2"
    | _ => false
  -- what a return leaves in the result register: another register as it was on entry, which is read, or the result register
  let result := context.convention.result
  let returned := returns.filterMap fun state => match state.read result with
    | .entry name _ 0 => some name
    | _ => none
  effects := returned.foldl (init := effects) fun effects name =>
    if name == result.name.str then effects else { effects with inputs := effects.inputs.insert name }
  let preserved := context.calleeSaved.filter keeps
  let clobbered := context.calleeSaved.filter fun name => !returns.isEmpty && !keeps name
  { entry := function.entry, deltas, returnDelta
    inputs := effects.inputs.toList.mergeSort (· ≤ ·)
    stackArguments := effects.stackReads.toList.mergeSort (· ≤ ·)
    preserved, clobbered
    usedResults := effects.usedResults.toList
    «open» := effects.open
    passesResult := returned.contains result.name.str }

/-! ## A program -/

/-- What a function was found to take and give, as its convention has it. -/
structure Signature where
  entry : Nat
  name : String
  /-- Of the registers of the arguments of its convention, how many it reads, as far as the last it reads. -/
  registerArguments : Nat
  floatArguments : Nat
  /-- The offsets of its arguments in memory, from the stack pointer on entry. -/
  stackArguments : List Nat
  /-- Whether a caller reads its result. -/
  returnsValue : Bool
  /-- Whether it keeps what its convention says it keeps. -/
  conforms : Bool
  deriving Repr

structure Frames where
  frames : List Frame
  signatures : List Signature

/-- The functions in the order that a function comes after what it calls, but of a cycle, of its calls. -/
def calleesFirst (partition : Partition) : List Partition.Function :=
  let byEntry : Std.HashMap Nat Partition.Function := partition.functions.foldl (init := {}) fun table function =>
    table.insert function.entry function
  let rec visit : Nat → Std.HashSet Nat × List Partition.Function → Nat → Std.HashSet Nat × List Partition.Function
    | 0, state, _ => state
    | fuel + 1, (seen, order), entry =>
      if seen.contains entry then (seen, order) else
      match byEntry[entry]? with
      | none => (seen, order)
      | some function =>
        let (seen, order) := function.calls.foldl (init := (seen.insert entry, order)) fun state (_, callee) =>
          visit fuel state callee
        (seen, function :: order)
  let (_, order) := partition.functions.foldl (init := (({} : Std.HashSet Nat), ([] : List Partition.Function)))
    fun state function => visit (partition.functions.length + 1) state function.entry
  order.reverse

/-- How many of `registers` a function of `inputs` takes: as far as the last of them that it reads. -/
def lastIndex (inputs : List String) (registers : List Bap.Var) : Nat :=
  (registers.zipIdx.filter fun (var, _) => inputs.contains var.name).foldl (fun most (_, index) => max most (index + 1)) 0

/-- The frames and the signatures of the functions of a partition of an image. -/
def frames (image : Image.Image) (partition : Partition) : Option Frames := do
  let convention ← ABI.convention image.arch image.addrWidth
  let width := image.addrWidth
  let base : Context := { arch := image.arch, width, convention, calleeSaved := calleeSaved image.arch width
                          volatile := volatileOf image.arch convention
                          callees := partition.functions.foldl (init := {}) fun table function =>
                            function.calls.foldl (init := table) fun table (call, callee) => table.insert call callee }
  let program := Program.of partition
  let ordered := calleesFirst partition
  let (frames, _) := ordered.foldl (init := (([] : List Frame), base)) fun (frames, context) function =>
    let frame := analyze context program function
    -- of the stub of an import, what it takes is what the import does, which isn't known
    let registerArguments := if frame.open || function.importName.isSome then none
      else some (lastIndex frame.inputs convention.functionArguments, lastIndex frame.inputs convention.floatArguments)
    let summary : Summary := { returnDelta := frame.returnDelta, registerArguments, stackArguments := frame.stackArguments }
    (frame :: frames, { context with summaries := context.summaries.insert function.entry summary })
  let frames := frames.reverse
  -- what a caller reads of a function is of what that calls in its tail too
  let read : Std.HashSet Nat := frames.foldl (init := {}) fun set frame =>
    frame.usedResults.foldl (init := set) fun set callee => set.insert callee
  let rec spread : Nat → Std.HashSet Nat → Std.HashSet Nat
    | 0, used => used
    | fuel + 1, used =>
      let more := ordered.foldl (init := used) fun set function =>
        if set.contains function.entry then function.tailCalls.foldl (init := set) fun set (_, target) => set.insert target else set
      if more.size == used.size then used else spread fuel more
  let used := spread ordered.length read
  let signatures := (frames.zip ordered).map fun (frame, function) =>
    -- a result register left as it was is an argument returned, if a caller reads it
    let inputs := if frame.passesResult && used.contains frame.entry then convention.result.name.str :: frame.inputs else frame.inputs
    { entry := frame.entry, name := function.name
      registerArguments := lastIndex inputs convention.functionArguments
      floatArguments := lastIndex inputs convention.floatArguments
      stackArguments := frame.stackArguments
      returnsValue := used.contains frame.entry
      conforms := frame.clobbered.isEmpty }
  some { frames, signatures }

def Frames.signatureOf (frames : Frames) (entry : Nat) : Option Signature :=
  frames.signatures.find? (·.entry == entry)

def Frames.frameOf (frames : Frames) (entry : Nat) : Option Frame :=
  frames.frames.find? (·.entry == entry)

end Bap.Analysis.Frame
