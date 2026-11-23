import Bap.Analysis.Values
import Bap.FFI.Z3

/-! # A model checker and feasible paths

What ROSE's `ModelChecker` and `FeasiblePath` find of the functions of a `Partition`, of what `Values` and the symbolic executor
know, with Z3 to say which ways some input takes:

- a load or a store whose address is null, below the first page, of every input that takes a way, as a way that sets a pointer to
  null before it reads through it has it;
- a load of the stack that some way to it doesn't write first, where no address of the stack has left the function, which a callee
  could write through;
- a load or a store at an index, of the value sets of `Values`, past an array: of the stack, to where a register is saved or above
  the stack pointer on entry, where the return address and the arguments are; of the program, past the symbol of its object;
- and, of an address in a function, a way to it that some input takes, if there is one, or that none is, as far as the ways go.

The ways go from the entry of a function, each instruction run symbolically as it is in the way, a call as clobbering what its
convention doesn't keep. A way goes no further past `maxSteps` instructions or once it has been at an instruction `maxVisits`
times, or once its state is `oversized`, and the ways of a function run no more than `maxTotal` instructions together, nor longer
than `maxMillis`. Z3 is asked whether some input takes a way
only of a way that has what is looked for, as a context of it is costly; of conditions too big to ask, a load of null isn't
reported, and a way to an address is taken to be taken. -/

namespace Bap.Analysis.Checker

open Bap.Analysis.Partition (Partition)
open Bap.Symbolic (Expr)

inductive Tag where
  | nullDereference
  | uninitialized
  | outOfBounds
  deriving BEq, Repr, DecidableEq

/-- What was found: of what, in the function at `function`, by the instruction at `insn`, and the way to it, of a way. -/
structure Finding where
  tag : Tag
  function : Nat
  insn : Nat
  path : List Nat := []
  detail : String := ""
  deriving Repr

/-! ## Of value sets -/

/-- How many values of an address are taken for a choice of addresses rather than an index. -/
def maxChoices : Int := 4

/-- What the accesses of the functions that `Values` found say: loads of the stack that aren't written first, and accesses at
indexes past what they index. -/
def ofValues (image : Image.Image) (partition : Partition) (frames : Frame.Frames) (variables : Values.Variables) : List Finding :=
    Id.run do
  let nexts : Std.HashMap Nat Nat := partition.disasm.instructions.foldl (init := {}) fun table insn =>
    table.insert insn.address insn.next
  let nextOf (address : Nat) : Option Nat := nexts[address]?
  let some convention := ABI.convention image.arch image.addrWidth | return []
  let stackPointer := convention.stackPointer.name.str
  -- what a function keeps for its caller: the registers its convention has it keep, and where it returns to
  let kept := Frame.calleeSaved image.arch image.addrWidth ++ (Partition.linkRegister image.arch).toList
  let objects := image.symbols.filter fun symbol => !symbol.isFunction && symbol.size > 0
  let mut findings : Array Finding := #[]
  for function in variables.functions do
    let saved := function.accesses.toList.filterMap fun access =>
      match access.address.single with
      | some (some base, offset) =>
        if base == stackPointer && access.register.any kept.contains then some (offset, offset + access.size) else none
      | _ => none
    let mut seen : Std.HashSet (Nat × Bool) := {}
    let writes : Std.HashMap Nat (List Values.Value) := function.accesses.foldl (init := {}) fun table access =>
      if access.write then table.insert access.insn (access.address :: table.getD access.insn []) else table
    let deltas := (frames.frameOf function.entry).map (·.deltas) |>.getD {}
    for access in function.accesses do
      let key := (access.insn, access.write)
      if seen.contains key then continue
      match access.address with
      | .set (some base) _ lo hi _ =>
        if base != stackPointer then continue
        if lo == hi then
          -- a load that frees what it reads, as a pop of what was pushed to align the stack, reads nothing of the function's
          let pops := match deltas[access.insn]?, nextOf access.insn with
            | some before, some next => before ≤ lo && (deltas[next]?).any (lo < ·)
            | _, _ => false
          -- nor does one that writes it back, as a probe of the stack, `or qword ptr [rsp], 0`, does
          let probes := (writes.getD access.insn []).contains access.address
          if !access.write && !access.initialized && lo < 0 && !pops && !probes then
            seen := seen.insert key
            findings := findings.push { tag := .uninitialized, function := function.entry, insn := access.insn
                                        detail := s!"{access.size} bytes at {lo} from the stack pointer on entry" }
        else if lo < 0 then
          let stop := hi + access.size
          let reachesSaved := saved.any fun (start, end_) => lo < end_ && start < stop
          if stop > 0 || reachesSaved then
            seen := seen.insert key
            findings := findings.push { tag := .outOfBounds, function := function.entry, insn := access.insn
                                        detail := s!"from {lo} to {stop} from the stack pointer on entry" }
      | .set none _ lo hi stride =>
        if lo == hi then continue
        let objectOf (address : Int) := objects.find? fun symbol =>
          symbol.addr ≤ address.toNat && address.toNat < symbol.addr + symbol.size
        let within (address : Int) : Bool := match objectOf address with
          | some object => (address + access.size).toNat ≤ object.addr + object.size
          | none => false
        -- a few values are a choice of addresses, as a conditional move makes, each of which may be of an object of its own;
        -- more are an index, of the object of the first
        let count := (hi - lo) / stride + 1
        if count ≤ maxChoices then
          let outside := ((List.range count.toNat).map fun (k : Nat) => lo + (stride : Int) * (k : Int)).filter (!within ·)
          if let some address := outside.head? then
            if (objectOf lo).isSome then
              seen := seen.insert key
              findings := findings.push { tag := .outOfBounds, function := function.entry, insn := access.insn
                                          detail := s!"at {address}, of no object" }
        else
          match objectOf lo with
          | some object =>
            if (hi + access.size).toNat > object.addr + object.size then
              seen := seen.insert key
              findings := findings.push { tag := .outOfBounds, function := function.entry, insn := access.insn
                                          detail := s!"past {object.name}, to {hi + access.size - object.addr}" }
          | none => pure ()
      | .top => pure ()
  return findings.toList

/-! ## Of ways -/

structure Config where
  maxSteps : Nat := 256
  maxVisits : Nat := 2
  maxPaths : Nat := 128
  /-- How many instructions all the ways of a function run, together. -/
  maxTotal : Nat := 1024
  /-- How many accesses of a function Z3 is asked whether they are of null. -/
  maxQuestions : Nat := 64
  /-- How long the ways of a function go, in milliseconds: what a way writes of memory makes each step after it longer. -/
  maxMillis : Nat := 250

/-- The addresses of the loads and the stores of an expression, outside what a `let` binds and the choices of an `ite`, which
only one of runs. -/
def accessesOf : Bil.Exp → List Bil.Exp
  | .load memory address _ _ => address :: accessesOf memory ++ accessesOf address
  | .store memory address value _ _ => address :: accessesOf memory ++ accessesOf address ++ accessesOf value
  | .bin _ left right => accessesOf left ++ accessesOf right
  | .un _ value | .cast _ _ value | .extract _ _ value => accessesOf value
  | .letIn _ value _ => accessesOf value
  | .ite condition _ _ => accessesOf condition
  | .concat left right => accessesOf left ++ accessesOf right
  | _ => []

/-- The name of a variable that has the address of an access, which a program is given to have. -/
def accessName (index : Nat) : String := s!"__access{index}"

/-- A program with each address that a statement accesses moved first to a variable of its own. -/
partial def instrument (width : Nat) (program : Bil.Program) (next : Nat := 0) : Bil.Program × Nat :=
  program.foldl (init := ([], next)) fun (done, next) stmt =>
    let addresses := match stmt with
      | .move _ value => accessesOf value
      | .jmp target => accessesOf target
      | .ifElse condition _ _ | .while condition _ => accessesOf condition
      | _ => []
    let (moves, next) := addresses.foldl (init := ([], next)) fun (moves, next) address =>
      (moves ++ [Bil.Stmt.move ⟨accessName next, .imm width, 0, false⟩ address], next + 1)
    let (stmt, next) := match stmt with
      | .ifElse condition yes no =>
        let (yes, next) := instrument width yes next
        let (no, next) := instrument width no next
        (Bil.Stmt.ifElse condition yes no, next)
      | .while condition body =>
        let (body, next) := instrument width body next
        (Bil.Stmt.while condition body, next)
      | other => (other, next)
    (done ++ moves ++ [stmt], next)

/-- How many parts an expression has, as far as `limit`: past it, `limit + 1`; without the conditions of its choices, of
`conditions` false. -/
def sizeOf (limit : Nat) (expr : Expr) (conditions : Bool := true) : Nat := Partition.sizeOf limit expr conditions

/-- What Z3 is given at most of a question, beyond which it isn't asked. -/
def maxQuestion : Nat := 4000

/-- A state without the variables of addresses and the temporaries of an instruction, with each variable once, and of a value
too big to look at, as x86's parity of what a few instructions made is, a value new to the way, of `fresh`. -/
def compact (state : Symbolic.State) (fresh : String) : Symbolic.State :=
  let (env, _) := state.env.foldl (init := (([] : List (Bap.Var × Expr)), ({} : Std.HashSet String)))
    fun (env, seen) (var, value) =>
      let key := s!"{var.name}#{var.index}"
      if seen.contains key || var.name.str.startsWith "_" then (env, seen)
      else
        let value := if sizeOf (4 * maxQuestion) value > 4 * maxQuestion then .var s!"{var.name}@{fresh}" value.width
          else value
        ((var, value) :: env, seen.insert key)
  { state with env := env.reverse }

/-- Whether an expression is a constant, and which, of one small enough to look at: what the executor makes is shared, and
looking at all of a big one is looking at each part as many times as it is reached. -/
def constOf (expr : Expr) : Option Nat :=
  if sizeOf maxQuestion expr > maxQuestion then none
  else match Partition.simplify expr with
    | .const value => some value.toNat
    | _ => none

/-- Whether an expression has a choice in it, as a conditional move makes. -/
def hasIte : Expr → Bool
  | .ite .. => true
  | .app _ _ args => args.attach.any fun ⟨arg, _⟩ => hasIte arg
  | .extract _ _ value => hasIte value
  | .concat left right => hasIte left || hasIte right
  | .select _ address => hasIte address
  | _ => false

/-- Whether an expression has a constant of `width` bits in the first page, as a comparison of a pointer with null has. -/
def pageConstant (width : Nat) : Expr → Bool
  | @Expr.const w value => w == width && value.toNat < 4096
  | .app _ _ args => args.attach.any fun ⟨arg, _⟩ => pageConstant width arg
  | .extract _ _ value | .select _ value => pageConstant width value
  | .concat left right => pageConstant width left || pageConstant width right
  | .ite condition yes no => pageConstant width condition || pageConstant width yes || pageConstant width no
  | _ => false

/-- Whether every input that meets the conditions makes an address null, below the first page: of the conditions of what the
address is of, as far as they are small enough to ask. -/
def nullOf (constraints : List Expr) (address : Expr) (millis : Nat := 250) : IO Bool := do
  if sizeOf maxQuestion address > maxQuestion then return false
  match constOf address with
  | some value => pure (value < 4096)
  | none =>
    -- what a condition is of: the registers of the address, or the address itself, as a pointer loaded of memory is, each as
    -- `simplify` has it, without the casts that a lifter makes of one and not of another
    let names := Partition.varsOf address
    let simple := Partition.simplify address
    let related := constraints.filter fun constraint =>
      sizeOf maxQuestion constraint ≤ maxQuestion &&
        ((Partition.varsOf constraint).any names.contains || Partition.hasPart simple (Partition.simplify constraint))
    -- what can say that an address is null is a choice of it, or a condition of it against what is in the first page
    let againstPage := related.any fun constraint =>
      let constraint := Partition.simplify constraint
      pageConstant address.width constraint && Partition.hasPart simple constraint
    if !againstPage && !hasIte address then return false
    let size := related.foldl (fun total constraint => total + sizeOf maxQuestion constraint) (sizeOf maxQuestion address)
    if size > maxQuestion then return false
    let page := Expr.const (BitVec.ofNat address.width 4096)
    -- of conditions that no input meets, every address is null
    -- nor is an address null of what Z3 doesn't say in time
    if (← FFI.Z3.isSatWithin related millis) != some true then return false
    return (← FFI.Z3.isSatWithin (.app "bvuge" 1 [address, page] :: related) millis) == some false

/-- A way being gone: the state, the instructions so far, newest first, how many times each was been at, and where a delay slot
goes after it. -/
structure Way where
  state : Symbolic.State
  path : List Nat
  visits : Std.HashMap Nat Nat
  pending : Option Nat := none
  /-- Whether the way ends after the delay slot it is in, of a jump of MIPS that goes out of the function, as a return. -/
  ending : Bool := false
  steps : Nat := 0
  /-- Whether an address of the stack has left the function, so that what it calls may write its stack. -/
  escaped : Bool := false

/-- The variable of memory that a function's code reads. -/
def memoryVar (instructions : List Disasm.Insn) : Option Bap.Var :=
  let rec ofExp : Bil.Exp → Option Bap.Var
    | .var var => if var.typ matches .mem _ _ then some var else none
    | .load memory _ _ _ => ofExp memory
    | .store memory _ _ _ _ => ofExp memory
    | _ => none
  instructions.findSome? fun insn => insn.bil.findSome? fun stmt =>
    match stmt with
    | .move var value => if var.typ matches .mem _ _ then some var else ofExp value
    | _ => none

/-- What is had of a function to go its ways. -/
structure Function where
  image : Image.Image
  entry : Nat
  instructions : Std.HashMap Nat Disasm.Insn
  successors : Nat → List Nat
  volatile : List String
  width : Nat
  /-- The stack pointer, and the variable of memory that the code reads. -/
  stack : String := ""
  memory : Option Bap.Var := none

def Function.of (image : Image.Image) (program : Frame.Program) (function : Partition.Function) : Option Function := do
  let convention ← ABI.convention image.arch image.addrWidth
  let instructions : Std.HashMap Nat Disasm.Insn := function.instructions.foldl (init := {}) fun table address =>
    match program.instructions[address]? with
    | some insn => table.insert address insn
    | none => table
  pure { image, entry := function.entry, instructions, width := image.addrWidth
         successors := fun address => (program.successors.getD address []).filter instructions.contains
         volatile := Frame.volatileOf image.arch convention
         stack := convention.stackPointer.name.str
         memory := memoryVar (instructions.toList.map (·.2)) }

/-- A condition as what it is of, and whether it holds or not: `c`, `c = 1` and `c = 0` of a bit. -/
def polarityOf : Expr → Expr × Bool
  | .app "=" 1 [condition, @Expr.const 1 value] => (condition, value.toNat == 1)
  | condition => (condition, true)

/-- The results of running from a state, without those that a condition of constants alone rules out, and with the conditions of
constants alone that hold left out: the executor folds only conditions that are constants as they are, and `simplify` what doesn't
depend on what it has of what isn't known. -/
def decided (before : Symbolic.State) (results : List Symbolic.Result) : List Symbolic.Result :=
  let σ : Proofs.Symbolic.Assignment := { var := fun _ _ => 0, memory := fun _ _ _ => 0 }
  results.filterMap fun result =>
    -- the executor adds a condition after those it had
    let had := before.constraints.length
    let (old, fresh) := (result.state.constraints.take had, result.state.constraints.drop had)
    -- of what it is when simplified, as a bit of a condition register that a lifter makes with what isn't known beside it
    let simple (constraint : Expr) : Option Expr :=
      if sizeOf maxQuestion constraint ≤ maxQuestion then
        let simple := Partition.simplify constraint
        if Partition.closed simple then some simple else none
      else none
    -- nor those of a condition that the way already has the other way, as of each instruction of ARM of the same condition
    let contradicts (constraint : Expr) : Bool := old.any fun other =>
      match polarityOf constraint, polarityOf other with
      | (c, p), (c', p') => p != p' && Expr.structuralEq c c'
    if fresh.any fun constraint => (simple constraint).any (Partition.valueOf σ · == 0) || contradicts constraint then none
    else
      let kept := fresh.filter fun constraint => (simple constraint).isNone && !old.any (Expr.structuralEq · constraint)
      some { result with state := { result.state with constraints := old ++ kept } }

/-- The targets of a choice of targets, each with the conditions of its way. -/
def armsOf : Expr → List (List Expr × Expr)
  | .ite condition yes no =>
    (armsOf yes).map (fun (conditions, arm) => (Expr.eqOne condition :: conditions, arm)) ++
      (armsOf no).map fun (conditions, arm) => (Expr.eqZero condition :: conditions, arm)
  | target => [([], target)]

/-- Where a way goes after an instruction: the way, the next instruction, if it is of the function, and what the instruction
accessed of the way. -/
structure Step where
  way : Way
  next : Option Nat
  accesses : List Expr
  /-- Of a call, whether it calls, which one of ARM that has a condition doesn't of every way. -/
  calls : Bool := false

/-- Whether a value is an address of the stack as it is made, a constant from the stack pointer on entry, or a byte of one. -/
def stackAddress (stack : String) (entry : Bool := true) : Expr → Bool
  | .extract _ _ value => stackAddress stack entry value
  | value =>
    -- without what doesn't change it, as a cast of the lifter, where it is small enough to look at
    let value := if sizeOf 256 value > 256 then value else Partition.simplify value
    match Symbolic.Memory.baseOffset value with
    | (.var name _, offset) => name.startsWith (stack ++ "#") && (entry || offset != 0)
    | _ => false

/-- Whether an address of the stack has left the function, to what may write through it: one that a register of `registers` holds,
or that is in memory. The stack pointer as it was on entry isn't one, which PowerPC keeps in its frame. -/
def leaks (function : Function) (registers : List String) (state : Symbolic.State) : Bool :=
  let stack := function.stack
  stack.isEmpty ||
    registers.any (fun name => match state.env.find? (·.1.name.str == name) with
      | some (_, value) => stackAddress stack false value
      | none => false) ||
    state.memories.any fun (_, memory) => memory.branch.isSome || memory.cells.any fun (_, value) => stackAddress stack false value

/-- A state after what may write any of memory that it can reach, a call or a loop: the memories are new to the way, of `fresh`,
but for what is at a constant from the stack pointer on entry, unless an address of the stack has `left`, which nothing but the
function has otherwise. -/
def forgetMemory (function : Function) (fresh : String) (state : Symbolic.State) (left : Bool) : Symbolic.State :=
  -- a memory that the way hasn't written is one too
  let state := match function.memory with
    | some var => if (Bap.Assoc.get var state.memories).isSome then state
                  else { state with memories := (var, Symbolic.memoryOf state var) :: state.memories }
    | none => state
  { state with memories := state.memories.map fun (var, memory) =>
      (var, { name := s!"{memory.name}@{fresh}"
              cells := if left then [] else memory.cells.filter fun (address, _) => stackAddress function.stack true address }) }

/-- What a statement can write, at any depth, and whether it loops. -/
def assigned : Bil.Stmt → List Bap.Var × Bool
  | .move var _ => ([var], false)
  | .while _ body => ((body.map assigned).flatMap (·.1), true)
  | .ifElse _ yes no =>
    ((yes.map assigned).flatMap (·.1) ++ (no.map assigned).flatMap (·.1), (yes.map assigned).any (·.2) || (no.map assigned).any (·.2))
  | _ => ([], false)

/-- The ways that each way of an instruction goes on to. -/
def stepWay (function : Function) (way : Way) (insn : Disasm.Insn) : IO (List Step) := do
  let base := { way with path := insn.address :: way.path, steps := way.steps + 1
                         visits := way.visits.insert insn.address (way.visits.getD insn.address 0 + 1) }
  let within (address : Nat) : Option Nat := if function.instructions.contains address then some address else none
  -- a jump of MIPS goes after its delay slot
  let slotted := Partition.mipsSlotted function.image.arch insn && insn.flow != .normal && insn.flow != .call
  -- a call, of the ways of its condition, clobbers what its convention doesn't keep with values that are new to the way, and
  -- returns to after itself with the rest as it was
  if insn.flow == .call then
    let env := function.volatile.foldl (init := way.state.env) fun env (name : String) =>
      ((⟨name, .imm function.width, 0, false⟩ : Bap.Var), Expr.var s!"{name}@{insn.address}#{way.steps}" function.width) :: env
    let next := match way.pending with
      | some target => within target
      | none => within insn.next
    let some results := (Symbolic.run insn.bil way.state 4000).toOption | return []
    let results := decided way.state results
    return results.filterMap fun result =>
      let state := { way.state with constraints := result.state.constraints, unknowns := result.state.unknowns }
      match result.outcome with
      | .jump _ =>
        -- and writes what it can reach of memory
        -- of what it is given as it is called: of MIPS, what its delay slot gives it isn't in a register yet; and an
        -- address that has left once is one that any call after may write through
        let left := way.escaped || Partition.mipsSlotted function.image.arch insn || leaks function function.volatile way.state
        let state := forgetMemory function s!"{insn.address}#{way.steps}" { state with env } left
        some { way := { base with state, pending := none, escaped := left }, next, accesses := [], calls := true }
      | .normal => some { way := { base with state, pending := none }, next, accesses := [] }
      | _ => none
  -- a loop of an instruction, as a `rep` of x86, isn't gone round, which is a way of each round of a count that isn't known: what
  -- it writes is new to the way, and it goes on to after itself
  let written := insn.bil.map assigned
  if written.any (·.2) && insn.flow == .normal then
    let fresh := s!"{insn.address}#{way.steps}"
    let env := (written.flatMap (·.1)).foldl (init := way.state.env) fun env var =>
      match var.typ with
      | .imm width => (var, Expr.var s!"{var.name}@{fresh}" width) :: env
      | _ => env
    -- which is through the registers that it moves along, as a `rep` does edi, which a call keeps
    let left := way.escaped || leaks function ((written.flatMap (·.1)).map (·.name.str)) way.state
    let state := forgetMemory function fresh { way.state with env } left
    return [{ way := { base with state := compact state fresh, pending := none, escaped := left }
              next := match way.pending with
                | some target => within target
                | none => if way.ending then none else within insn.next
              accesses := [] }]
  let (program, count) := instrument function.width insn.bil
  let some results := (Symbolic.run program way.state 4000).toOption | return []
  let results := decided way.state results
  let mut steps : Array Step := #[]
  for result in results do
    let accesses := (List.range count).filterMap fun index =>
      Bap.Assoc.get (⟨accessName index, .imm function.width, 0, false⟩ : Bap.Var) result.state.env
    let state := compact result.state s!"{insn.address}#{way.steps}"
    -- where the way goes, and where after a delay slot: of a jump through a register of MIPS, where the slot goes on to, its
    -- targets, or nowhere, of a return
    -- where a jump goes: to a constant, or else to the targets of the jump but its fall-through, which is the way of a
    -- conditional one that isn't taken, as of a conditional return of PowerPC
    let jumpTo (target : Expr) : List (Option Nat × Option Nat × Bool) :=
      match constOf target with
      | some address => if slotted then [(within insn.next, some address, false)] else [(within address, none, false)]
      | none =>
        if slotted then
          match function.successors insn.next with
          | [] => [(within insn.next, none, true)]
          | targets => targets.map fun target => (within insn.next, some target, false)
        else
          let jumped := (function.successors insn.address).filter fun target =>
            insn.flow != .conditionalJump || target != insn.next
          match jumped with
          | [] => [(none, none, false)]
          | targets => targets.map fun target => (some target, none, false)
    let targets : List (List Expr × Option Nat × Option Nat × Bool) := match result.outcome, way.pending with
      | .normal, some target => [([], within target, none, false)]
      | .normal, none => if way.ending then [([], none, none, false)]
          else [([], within insn.next, if slotted then some (insn.next + insn.size) else none, false)]
      | .jump target, _ =>
        -- a jump to a choice, as ARM's `bxlt lr` to the link register or on, is a way of each, of its condition
        (armsOf target).flatMap fun (conditions, arm) => (jumpTo arm).map fun (next, pending, ending) =>
          (conditions, next, pending, ending)
      | _, _ => [([], none, none, false)]
    for (conditions, next, pending, ending) in targets do
      let state := { state with constraints := state.constraints ++ conditions }
      steps := steps.push { way := { base with state, pending, ending }, next, accesses }
  return steps.toList

/-- Whether the memory of a state has grown past what a step of it can be had of soon: a cell of more than `maxQuestion` parts,
or more than `maxCells` cells, which each write of memory compares its address with. -/
def oversized (state : Symbolic.State) (maxCells : Nat := 256) : Bool :=
  state.memories.any fun (_, memory) =>
    memory.branch.isSome || memory.cells.length > maxCells ||
      memory.cells.any fun (address, value) => sizeOf maxQuestion address + sizeOf maxQuestion value > maxQuestion

/-- Whether some input takes a way, of what Z3 says of its conditions: of conditions too big to ask, or that it doesn't say of
within `millis` milliseconds, `big`. -/
def feasible (way : Way) (big : Bool) (millis : Nat := 250) : IO Bool := do
  let size := way.state.constraints.foldl (fun total constraint => total + sizeOf (4 * maxQuestion) constraint) 0
  if size > 4 * maxQuestion then pure big else return (← FFI.Z3.isSatWithin way.state.constraints millis).getD big

/-- Each way of a function from its entry, as far as `config` lets it go: `visit` is given each step, of the instruction it is
of, and says whether to go on. Z3 isn't asked of each way, as a context of it is costly: what `visit` finds of a way, it asks
whether some input takes. -/
partial def explore (function : Function) (config : Config) (initial : Symbolic.State)
    (visit : Step → Disasm.Insn → IO Bool) : IO Unit := do
  let ends ← IO.mkRef 0
  let total ← IO.mkRef 0
  let deadline := (← IO.monoMsNow) + config.maxMillis
  let rec go (way : Way) (address : Nat) : IO Unit := do
    if (← ends.get) ≥ config.maxPaths || (← total.get) ≥ config.maxTotal then return
    if (← IO.monoMsNow) > deadline then return
    if oversized way.state then
      ends.modify (· + 1)
      return
    total.modify (· + 1)
    if way.steps ≥ config.maxSteps || way.visits.getD address 0 ≥ config.maxVisits then
      ends.modify (· + 1)
      return
    let some insn := function.instructions[address]? | return
    for step in ← stepWay function way insn do
      let way := step.way
      if !(← visit step insn) then continue
      match step.next with
      | some next => go way next
      | none => ends.modify (· + 1)
  go { state := initial, path := [], visits := {} } function.entry

/-- The loads and stores of the functions of a partition that every input that takes a way to them makes null. -/
def nullDereferences (image : Image.Image) (partition : Partition) (config : Config := {}) : IO (List Finding) := do
  let program := Frame.Program.of partition
  let found ← IO.mkRef (#[] : Array Finding)
  for function in partition.functions do
    if function.importName.isSome then continue
    let some checked := Function.of image program function | continue
    let reported ← IO.mkRef ({} : Std.HashSet Nat)
    let asked ← IO.mkRef ({} : Std.HashMap Nat Nat)
    let questions ← IO.mkRef 0
    explore checked config (Partition.entryState image function.entry) fun step insn => do
      if (← reported.get).contains insn.address then return true
      -- of each instruction, and of each function, Z3 is asked a few times at most
      if (← asked.get).getD insn.address 0 ≥ 4 || (← questions.get) ≥ config.maxQuestions then return true
      for address in step.accesses do
        let before := (← asked.get).getD insn.address 0
        asked.modify fun table => table.insert insn.address (before + 1)
        questions.modify (· + 1)
        if (← nullOf step.way.state.constraints address config.maxMillis) && (← feasible step.way false config.maxMillis) then
          reported.modify (·.insert insn.address)
          found.modify (·.push { tag := .nullDereference, function := function.entry, insn := insn.address
                                 path := step.way.path.reverse, detail := s!"through {(Partition.simplify address).render}" })
          -- what is past a load of null isn't
          return false
      return true
  return (← found.get).toList

/-- A way from the entry of a function that some input takes, if one of the ways that `config` lets go is, that runs the
instruction at an address in it, and of a call, calls. -/
def feasiblePath (image : Image.Image) (partition : Partition) (function : Partition.Function) (target : Nat)
    (config : Config := {}) : IO (Option (List Nat)) := do
  let program := Frame.Program.of partition
  let some checked := Function.of image program function | return none
  let found ← IO.mkRef (none : Option (List Nat))
  explore checked config (Partition.entryState image function.entry) fun step insn => do
    if (← found.get).isSome then return false
    if insn.address == target && (insn.flow != .call || step.calls) then
      -- of conditions too big to ask, a way is taken to be taken
      if ← feasible step.way true config.maxMillis then
        found.set (some step.way.path.reverse)
      return false
    return true
  found.get

/-- All that the checker finds of a partition of an image: of value sets, and of ways. -/
def check (image : Image.Image) (partition : Partition) (config : Config := {}) : IO (List Finding) := do
  let some frames := Frame.frames image partition | return []
  let some variables := Values.ofPartition image partition frames | return []
  return ofValues image partition frames variables ++ (← nullDereferences image partition config)

end Bap.Analysis.Checker
