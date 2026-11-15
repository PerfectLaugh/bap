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
          let probes := function.accesses.any fun other =>
            other.insn == access.insn && other.write && other.address == access.address
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

/-- The addresses of the loads and the stores of an expression, outside what a `let` binds. -/
partial def accessesOf : Bil.Exp → List Bil.Exp
  | .load memory address _ _ => address :: accessesOf memory ++ accessesOf address
  | .store memory address value _ _ => address :: accessesOf memory ++ accessesOf address ++ accessesOf value
  | .bin _ left right => accessesOf left ++ accessesOf right
  | .un _ value | .cast _ _ value | .extract _ _ value => accessesOf value
  | .letIn _ value _ => accessesOf value
  | .ite condition yes no => accessesOf condition ++ accessesOf yes ++ accessesOf no
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

/-- How many parts an expression has, as far as `limit`: past it, `limit + 1`. -/
partial def sizeOf (limit : Nat) (expr : Expr) : Nat :=
  -- what is left of the budget after the parts of an expression, of none left once it is spent
  let rec go (left : Nat) (expr : Expr) : Nat :=
    if left == 0 then 0 else
    let left := left - 1
    match expr with
    | .app _ _ args => args.foldl go left
    | .extract _ _ value | .select _ value => go left value
    | .concat first second => go (go left first) second
    | .ite condition yes no => go (go (go left condition) yes) no
    | _ => left
  let left := go (limit + 1) expr
  limit + 1 - left

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

def vars (expr : Expr) : List String := Partition.varsOf expr

/-- Whether an expression has a choice in it, as a conditional move makes. -/
partial def hasIte : Expr → Bool
  | .ite .. => true
  | .app _ _ args => args.any hasIte
  | .extract _ _ value => hasIte value
  | .concat left right => hasIte left || hasIte right
  | .select _ address => hasIte address
  | _ => false

/-- Whether every input that meets the conditions makes an address null, below the first page: of the conditions of what the
address is of, as far as they are small enough to ask. -/
def nullOf (constraints : List Expr) (address : Expr) : IO Bool := do
  if sizeOf maxQuestion address > maxQuestion then return false
  match constOf address with
  | some value => pure (value < 4096)
  | none =>
    let names := vars address
    let related := constraints.filter fun constraint =>
      sizeOf maxQuestion constraint ≤ maxQuestion && (vars constraint).any names.contains
    -- what can say that an address is null is a choice of it, or a condition of it against zero
    let zero : Expr := .const (BitVec.ofNat address.width 0)
    let againstZero := related.any fun constraint => Partition.hasPart zero constraint && Partition.hasPart address constraint
    if !againstZero && !hasIte address then return false
    let size := related.foldl (fun total constraint => total + sizeOf maxQuestion constraint) (sizeOf maxQuestion address)
    if size > maxQuestion then return false
    let page := Expr.const (BitVec.ofNat address.width 4096)
    -- of conditions that no input meets, every address is null
    if ← FFI.Z3.isUnsat related then return false
    FFI.Z3.isUnsat (.app "bvuge" 1 [address, page] :: related)

/-- A way being gone: the state, the instructions so far, newest first, how many times each was been at, and where a delay slot
goes after it. -/
structure Way where
  state : Symbolic.State
  path : List Nat
  visits : Std.HashMap Nat Nat
  pending : Option Nat := none
  steps : Nat := 0

/-- What is had of a function to go its ways. -/
structure Function where
  image : Image.Image
  entry : Nat
  instructions : Std.HashMap Nat Disasm.Insn
  successors : Nat → List Nat
  volatile : List String
  width : Nat

def Function.of (image : Image.Image) (program : Frame.Program) (function : Partition.Function) : Option Function := do
  let convention ← ABI.convention image.arch image.addrWidth
  let instructions : Std.HashMap Nat Disasm.Insn := function.instructions.foldl (init := {}) fun table address =>
    match program.instructions[address]? with
    | some insn => table.insert address insn
    | none => table
  pure { image, entry := function.entry, instructions, width := image.addrWidth
         successors := fun address => (program.successors.getD address []).filter instructions.contains
         volatile := Frame.volatileOf image.arch convention }

/-- The results of running from a state, without those that a condition of constants alone rules out, and with the conditions of
constants alone that hold left out: the executor folds only conditions that are constants as they are. -/
def decided (before : Symbolic.State) (results : List Symbolic.Result) : List Symbolic.Result :=
  let σ : Proofs.Symbolic.Assignment := { var := fun _ _ => 0, memory := fun _ _ _ => 0 }
  results.filterMap fun result =>
    -- the executor adds a condition after those it had
    let had := before.constraints.length
    let (old, fresh) := (result.state.constraints.take had, result.state.constraints.drop had)
    let closed (constraint : Expr) := sizeOf maxQuestion constraint ≤ maxQuestion && Partition.closed constraint
    if fresh.any fun constraint => closed constraint && Partition.valueOf σ constraint == 0 then none
    else
      let kept := fresh.filter fun constraint => !closed constraint
      some { result with state := { result.state with constraints := old ++ kept } }

/-- Where a way goes after an instruction: the way, the next instruction, if it is of the function, and what the instruction
accessed of the way. -/
structure Step where
  way : Way
  next : Option Nat
  accesses : List Expr
  /-- Of a call, whether it calls, which one of ARM that has a condition doesn't of every way. -/
  calls : Bool := false

/-- The ways that each way of an instruction goes on to. -/
def stepWay (function : Function) (way : Way) (insn : Disasm.Insn) : IO (List Step) := do
  let base := { way with path := insn.address :: way.path, steps := way.steps + 1
                         visits := way.visits.insert insn.address (way.visits.getD insn.address 0 + 1) }
  let within (address : Nat) : Option Nat := if function.instructions.contains address then some address else none
  -- a jump of MIPS goes after its delay slot
  let slotted := Frame.slotted function.image.arch insn && insn.flow != .normal && insn.flow != .call
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
      | .jump _ => some { way := { base with state := { state with env }, pending := none }, next, accesses := [], calls := true }
      | .normal => some { way := { base with state, pending := none }, next, accesses := [] }
      | _ => none
  let (program, count) := instrument function.width insn.bil
  let some results := (Symbolic.run program way.state 4000).toOption | return []
  let results := decided way.state results
  let mut steps : Array Step := #[]
  for result in results do
    let accesses := (List.range count).filterMap fun index =>
      Bap.Assoc.get (⟨accessName index, .imm function.width, 0, false⟩ : Bap.Var) result.state.env
    let state := compact result.state s!"{insn.address}#{way.steps}"
    let targets : List (Option Nat × Option Nat) := match result.outcome, way.pending with
      | .normal, some target => [(within target, none)]
      | .normal, none => [(within insn.next, if slotted then some (insn.next + insn.size) else none)]
      | .jump target, _ =>
        match constOf target with
        | some address => if slotted then [(within insn.next, some address)] else [(within address, none)]
        | none =>
          match function.successors insn.address with
          | [] => [(none, none)]
          | targets => targets.map fun target => (some target, none)
      | _, _ => [(none, none)]
    for (next, pending) in targets do
      steps := steps.push { way := { base with state, pending }, next, accesses }
  return steps.toList

/-- Whether the memory of a state has grown past what a step of it can be had of soon: a cell of more than `maxQuestion` parts,
or more than `maxCells` cells, which each write of memory compares its address with. -/
def oversized (state : Symbolic.State) (maxCells : Nat := 256) : Bool :=
  state.memories.any fun (_, memory) =>
    memory.branch.isSome || memory.cells.length > maxCells ||
      memory.cells.any fun (address, value) => sizeOf maxQuestion address + sizeOf maxQuestion value > maxQuestion

/-- Whether some input takes a way, of what Z3 says of its conditions: of conditions too big to ask, `big`. -/
def feasible (way : Way) (big : Bool) : IO Bool := do
  let size := way.state.constraints.foldl (fun total constraint => total + sizeOf (4 * maxQuestion) constraint) 0
  if size > 4 * maxQuestion then pure big else FFI.Z3.isSat way.state.constraints

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
        if (← nullOf step.way.state.constraints address) && (← feasible step.way false) then
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
      if ← feasible step.way true then
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
