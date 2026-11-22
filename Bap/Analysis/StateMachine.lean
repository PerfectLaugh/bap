import Bap.Analysis.Xrefs

/-! # State machines: the dispatcher of a flattened function, by its shape

A function whose control flow is flattened keeps a state in a variable, which a dispatcher compares against constants, in a loop,
to go to the block of each, and each block sets the state to the constant of what comes after it and goes back to the dispatcher.
`analyze` finds the variable and its cases in the instructions of a function: a case is an assignment of a constant to the
variable, with where control goes after it, and is one only of a variable of a byte or more that instructions compare against
two constants or more, one of them in a loop, of a constant that it is compared against, and where a comparison of it comes
after the assignment. So a register that is given constants, as the arguments of calls are, isn't a state, nor a flag that is
cleared, nor a counter of a loop, which isn't given the numbers it is compared against. A machine is `complete` with two cases
of two constants, and nothing that jumps where isn't known.

The instructions are read as they are: an assignment is a move of a closed expression to a variable, and a comparison is a
subtraction or a relation of a variable and a closed expression. `normalize` makes those of the code of a compiler: there, a
state is as often in a slot of the stack as in a register, the constants come through other registers, and an address is the
sum of temporaries. `ofCode` is `analyze` of what `normalize` gives. -/

namespace Bap.Analysis.StateMachine

structure Case where
  value : Nat
  target : Nat
  deriving DecidableEq, Repr

structure Result where
  stateVar : Option Bap.Var := none
  cases : List Case := []
  complete : Bool := false
  deriving Repr

private def directTarget (next : Disasm.Insn) : Option Nat :=
  match next.bil.reverse.find? fun stmt => match stmt with | .jmp _ => true | _ => false with
  | some (.jmp (.int target)) => some target.toNat
  | _ => if next.flow = .normal then some next.address else next.target

private def assignments (insn : Disasm.Insn) : List (Bap.Var × Nat) :=
  insn.bil.filterMap fun stmt =>
    match stmt with
    | .move var exp =>
      match Bil.evalExp {} exp with
      | .ok value => (Bap.Value.asBits value).toOption.map fun value => (var, value.2.toNat)
      | .error _ => none
    | _ => none

/-- The constant of a closed expression. -/
private def closed (exp : Bil.Exp) : Option Nat :=
  match Bil.evalExp {} exp with
  | .ok value => (Bap.Value.asBits value).toOption.map (·.2.toNat)
  | .error _ => none

/-- Whether an operation compares what it is of: a subtraction, which sets the flags of the architectures that have them, or a
relation. -/
private def comparing : Bil.BinOp → Bool
  | .sub | .eq | .neq | .lt | .le | .gt | .ge | .slt | .sle | .sgt | .sge => true
  | _ => false

mutual
  /-- The comparisons of a variable against a constant in an expression. -/
  private partial def expCompares : Bil.Exp → List (Bap.Var × Nat)
    | .bin op left right =>
      let here := if !comparing op then [] else
        match left, closed right, right, closed left with
        | .var var, some value, _, _ => [(var, value)]
        | _, _, .var var, some value => [(var, value)]
        | _, _, _, _ => []
      here ++ expCompares left ++ expCompares right
    | .load memory address _ _ => expCompares memory ++ expCompares address
    | .store memory address value _ _ => expCompares memory ++ expCompares address ++ expCompares value
    | .un _ value | .cast _ _ value | .extract _ _ value => expCompares value
    | .letIn _ value body => expCompares value ++ expCompares body
    | .ite condition yes no => expCompares condition ++ expCompares yes ++ expCompares no
    | .concat left right => expCompares left ++ expCompares right
    | .int _ | .var _ | .unknown _ _ => []

  private partial def stmtCompares : Bil.Stmt → List (Bap.Var × Nat)
    | .move _ value => expCompares value
    | .jmp target => expCompares target
    | .while condition body => expCompares condition ++ body.flatMap stmtCompares
    | .ifElse condition yes no => expCompares condition ++ yes.flatMap stmtCompares ++ no.flatMap stmtCompares
    | .special _ | .cpuExn _ => []
end

/-- What a dispatcher is of, by its variable: the constants that it compares the variable against, and the instructions that a
comparison of it comes after, or that are one. -/
structure Dispatcher where
  var : Bap.Var
  constants : List Nat
  leading : Std.HashSet Nat

/-- What leads to `seeds` by the edges that `before` has the sources of, of each target. -/
private def leadingTo (before : Std.HashMap Nat (List Nat)) : Nat → List Nat → Std.HashSet Nat → Std.HashSet Nat
  | 0, _, seen => seen
  | _, [], seen => seen
  | fuel + 1, address :: work, seen =>
    let fresh := (before.getD address []).filter fun source => !seen.contains source
    leadingTo before fuel (fresh ++ work) (fresh.foldl (init := seen) fun seen source => seen.insert source)

/-- The dispatchers of instructions: the variables of a byte or more that are compared against two constants or more, at an
instruction that control comes back to. -/
def dispatchers (instructions : List Disasm.Insn) : List Dispatcher :=
  let addresses : Std.HashSet Nat := instructions.foldl (init := {}) fun set insn => set.insert insn.address
  let edges := instructions.flatMap fun insn => (insn.successors.filter addresses.contains).map (insn.address, ·)
  let before : Std.HashMap Nat (List Nat) := edges.foldl (init := {}) fun table (source, target) =>
    table.insert target (source :: table.getD target [])
  let fuel := edges.length + instructions.length + 1
  let compared := instructions.flatMap fun insn => (insn.bil.flatMap stmtCompares).map fun (var, value) => (var, value, insn)
  let wide (var : Bap.Var) : Bool := match var.typ with
    | .imm width => width ≥ 8
    | _ => false
  ((compared.map (·.1)).eraseDups.filter wide).filterMap fun var =>
    let mine := compared.filter (·.1 == var)
    let constants := (mine.map (·.2.1)).eraseDups
    let sites := (mine.map (·.2.2.address)).eraseDups
    -- a comparison is in a loop if what it goes on to leads back to it
    let looped := mine.any fun (_, _, insn) =>
      let back := leadingTo before fuel [insn.address] {}
      insn.successors.any fun next => next == insn.address || back.contains next
    if constants.length ≥ 2 && looped then
      some { var, constants, leading := leadingTo before fuel sites (sites.foldl (init := {}) fun set site => set.insert site) }
    else none

/-- Whether an assignment of `value` to `var` at `current` sets the state of a dispatcher: the variable is one that a dispatcher
compares, against that constant too, and a comparison of it comes after the assignment. -/
def isCase (dispatchers : List Dispatcher) (current : Disasm.Insn) (var : Bap.Var) (value : Nat) : Bool :=
  dispatchers.any fun dispatcher =>
    dispatcher.var == var && dispatcher.constants.contains value && dispatcher.leading.contains current.address

private def simplerCandidates (instructions : List Disasm.Insn) : List (Bap.Var × Nat × Nat) :=
  let dispatchers := dispatchers instructions
  (List.range (instructions.length - 1)).flatMap fun index =>
    match instructions[index]?, instructions[index + 1]? with
    | some current, some next =>
      match directTarget next with
      | some target =>
        ((assignments current).filter fun assignment => isCase dispatchers current assignment.1 assignment.2).map
          fun assignment => (assignment.1, assignment.2, target)
      | none => []
    | _, _ => []

private def choose (instructions : List Disasm.Insn) : Option (Bap.Var × List Case) :=
  let triples := simplerCandidates instructions
  let variables := triples.map Prod.fst |>.eraseDups
  variables.foldl (init := none) fun best var =>
    let cases := (triples.filter fun triple => triple.1 = var).map fun triple => ⟨triple.2.1, triple.2.2⟩
    match best with
    | some current =>
      if current.2.length < cases.length then some (var, cases) else best
    | none => some (var, cases)

def analyzeWithState (instructions : List Disasm.Insn) (var : Bap.Var) : Result :=
  let cases := (simplerCandidates instructions).filterMap fun triple =>
    if triple.1 = var then some ⟨triple.2.1, triple.2.2⟩ else none
  {
    stateVar := some var
    cases
    complete := (cases.map Case.value).eraseDups.length ≥ 2 && !instructions.any fun insn => insn.flow = .indirectJump
  }

def analyze (instructions : List Disasm.Insn) : Result :=
  match choose instructions with
  | none => {}
  | some (var, cases) => {
    stateVar := some var
    cases
    complete := (cases.map Case.value).eraseDups.length ≥ 2 && !instructions.any fun insn => insn.flow = .indirectJump
  }

def isFlattened (result : Result) : Bool := result.complete && result.cases.length ≥ 2

def transition (result : Result) (value : Nat) : Option Nat :=
  (result.cases.find? fun current => current.value = value).map Case.target

def render (result : Result) : String :=
  let header := match result.stateVar with
    | some var => s!"state {var.name}"
    | none => "state <unknown>"
  let cases := result.cases.map fun current => s!"{current.value}: loc_{current.target}"
  String.intercalate "\n" (header :: cases)

/-! ## The code of a compiler

`normalize` runs each instruction over what is known in a line of them: a register, a temporary or a slot of memory holds a
constant, or what another holds plus a constant, or isn't known. A slot is the memory at a constant from a register, or at a
constant, and is a variable of its own, named by where it is. What a register holds is known from the instructions before it
up to where control comes in from elsewhere, or of a register that is only ever given one constant, as those that a compiler
loads before a loop, anywhere. -/

/-- What a place holds: a constant, what `var` holds now plus `offset`, or what isn't known. -/
private inductive Held where
  | top
  | const (width value : Nat)
  | place (var : Bap.Var) (offset : Nat)
  deriving BEq, Inhabited

private def foldHeld (exp : Bil.Exp) : Held :=
  match Bil.evalExp {} exp with
  | .ok (.bits (width := width) bits) => .const width bits.toNat
  | _ => .top

private def Held.asExp : Held → Option Bil.Exp
  | .const width value => some (.int (BitVec.ofNat width value))
  | _ => none

/-- The variable of a slot of memory of `size` bytes at `offset` from what `base` holds, or at the address `offset`. -/
def slotVar (base : Option Bap.Var) (offset size : Nat) : Bap.Var :=
  let at_ := match base with
    | some base => if offset < 2 ^ 63 then s!"{base.name.str}+{offset}" else s!"{base.name.str}-{2 ^ 64 - offset}"
    | none => s!"{offset}"
  ⟨s!"[{at_}]:{size}", .imm (8 * size), 0, false⟩

private def isSlot (var : Bap.Var) : Bool := var.name.str.startsWith "["
private def isTemporary (var : Bap.Var) : Bool := var.name.str.startsWith "_"

/-- What is known in a line of instructions, the comparisons and the assignments of constants that were seen, and whether a
variable was assigned at all. -/
private structure Line where
  held : Std.HashMap String Held := {}
  /-- The registers that are only ever given one constant. -/
  fixed : Std.HashMap String Held := {}
  compares : List (Bap.Var × Nat) := []
  assigns : List (Bap.Var × Held) := []
  /-- The registers stored to a slot as they were when the line started. -/
  saves : List String := []
  /-- Whether the line is the first of the function, where a register that wasn't given anything yet holds what it did on entry. -/
  first : Bool := false
  deriving Inhabited

private def Line.read (line : Line) (var : Bap.Var) : Held :=
  match line.held[var.name.str]? with
  | some held => held
  | none => if line.first then .place var 0 else (line.fixed[var.name.str]?).getD (.place var 0)

/-- A variable is given a value: what was known by what it held before isn't, nor of the slots that are at it. A register is
known by a slot it was loaded of, and a temporary by anything, but a register isn't known by another, so that a slot has one
name; one that is given what isn't known holds what it holds, from there on. -/
private def Line.assign (line : Line) (var : Bap.Var) (value : Held) : Line :=
  let name := var.name.str
  let at_ (slot : String) : Bool := slot.startsWith s!"[{name}+" || slot.startsWith s!"[{name}-"
  let held := line.held.filter fun other held => other != name && !at_ other && match held with
    | .place source _ => source.name.str != name && !at_ source.name.str
    | _ => true
  let known := match value with
    | .const .. => true
    | .place source offset => source.name.str != name && (isTemporary var || (offset == 0 && isSlot source))
    | .top => false
  let held := if known then held.insert name value else if line.fixed.contains name then held.insert name .top else held
  { line with held
              assigns := if isTemporary var then line.assigns else (var, value) :: line.assigns
              saves := match value with
                | .place source 0 => if isSlot var && !isSlot source && !isTemporary source then source.name.str :: line.saves else line.saves
                | _ => line.saves }

/-- Whether an expression is computed of a variable or has a complement in it, as what is added to subtract is, rather than
a number that the instruction has. -/
private partial def complemented : Bil.Exp → Bool
  | .un .not _ | .var _ => true
  | .un _ value | .cast _ _ value | .extract _ _ value => complemented value
  | .bin _ left right | .concat left right => complemented left || complemented right
  | _ => false

/-- The variable that an expression is, as it is or a part of it. -/
private def directVar : Bil.Exp → Option Bap.Var
  | .var var | .cast _ _ (.var var) | .extract _ _ (.var var) | .cast _ _ (.cast _ _ (.var var)) => some var
  | _ => none

private partial def evalHeld (line : Line) : Bil.Exp → StateM (List (Bap.Var × Nat)) Held
  | .int (width := width) value => pure (.const width value.toNat)
  | .var var => pure (line.read var)
  | .load _ address _ size => do
    match ← evalHeld line address with
    | .place base offset => pure (line.read (slotVar (some base) offset size))
    | .const _ address => pure (line.read (slotVar none address size))
    | .top => pure .top
  | .store .. => pure .top
  | .bin op left right => do
    let l ← evalHeld line left
    let r ← evalHeld line right
    -- a comparison of what a place holds against a constant: a relation or a subtraction, or the sum with the complement of
    -- what is taken away and one, as the architectures without a subtraction have it
    let note (place : Held) (direct : Option Bap.Var) (width value : Nat) (other : Bil.Exp) : StateM (List (Bap.Var × Nat)) Unit := do
      let value := if op == .add then (2 ^ width - value % 2 ^ width) % 2 ^ width else value
      let vars := (match place with
        | .place var 0 => [var]
        | _ => []) ++ (direct.filter fun var => !isTemporary var).toList
      if op != .add || complemented other then modify fun seen => vars.map (·, value) ++ seen
    if comparing op || op == .add then
      match l, r with
      | .const leftWidth leftValue, .const width value =>
        if (directVar left).isSome then note .top (directVar left) width value right
        else if (directVar right).isSome && op != .sub then note .top (directVar right) leftWidth leftValue left
      | place, .const width value => note place (directVar left) width value right
      | .const width value, place => if op != .sub then note place (directVar right) width value left
      | _, _ => pure ()
    match op, l, r with
    | .add, .place var offset, .const _ value | .add, .const _ value, .place var offset => pure (.place var ((offset + value) % 2 ^ 64))
    | .sub, .place var offset, .const _ value => pure (.place var ((offset + 2 ^ 64 - value % 2 ^ 64) % 2 ^ 64))
    | _, .const .., .const .. =>
      match l.asExp, r.asExp with
      | some l, some r => pure (foldHeld (.bin op l r))
      | _, _ => pure .top
    | _, _, _ => pure .top
  | .un op value => do
    match ← evalHeld line value with
    | .const width bits => pure (foldHeld (.un op (.int (BitVec.ofNat width bits))))
    | _ => pure .top
  | .cast kind width value => do
    match ← evalHeld line value with
    | .const w bits => pure (foldHeld (.cast kind width (.int (BitVec.ofNat w bits))))
    | .place var offset => pure (if offset == 0 || width ≥ 32 then .place var offset else .top)
    | .top => pure .top
  | .extract high low value => do
    match ← evalHeld line value with
    | .const w bits => pure (foldHeld (.extract high low (.int (BitVec.ofNat w bits))))
    | .place var 0 => pure (if low == 0 then .place var 0 else .top)
    | _ => pure .top
  | .letIn var value body => do
    let value ← evalHeld line value
    evalHeld { line with held := line.held.insert var.name.str value } body
  | .ite condition yes no => do
    let _ ← evalHeld line condition
    let yes ← evalHeld line yes
    let no ← evalHeld line no
    pure (if yes == no then yes else .top)
  | .concat left right => do
    let l ← evalHeld line left
    let r ← evalHeld line right
    match l.asExp, r.asExp with
    | some l, some r => pure (foldHeld (.concat l r))
    | _, _ => pure .top
  | .unknown _ _ => pure .top

private def Line.eval (line : Line) (exp : Bil.Exp) : Line × Held :=
  let (held, compares) := (evalHeld line exp).run []
  ({ line with compares := compares ++ line.compares }, held)

mutual
  /-- The stores of a value of memory, in order. A store where isn't known may be to any slot. -/
  private partial def storeLine (line : Line) : Bil.Exp → Line
    | .store memory address value _ size =>
      let line := storeLine line memory
      let (line, address) := line.eval address
      let (line, value) := line.eval value
      match address with
      | .place base offset => line.assign (slotVar (some base) offset size) value
      | .const _ address => line.assign (slotVar none address size) value
      | .top => { line with held := line.held.filter fun name held => !name.startsWith "[" && match held with
          | .place source _ => !isSlot source
          | _ => true }
    | _ => line

  private partial def stmtLine (line : Line) : Bil.Stmt → Line
    | .move var value =>
      match var.typ with
      | .mem _ _ => storeLine line value
      | _ =>
        let (line, value) := line.eval value
        line.assign var value
    | .jmp target => (line.eval target).1
    | .special _ | .cpuExn _ => line
    | .ifElse condition yes no =>
      let (line, _) := line.eval condition
      let after := no.foldl stmtLine (yes.foldl stmtLine { line with assigns := [] })
      -- what a branch assigns is assigned or isn't
      if after.assigns.isEmpty then { after with assigns := line.assigns }
      else { after with held := {}, assigns := after.assigns ++ line.assigns }
    | .while condition _ => { (line.eval condition).1 with held := {} }
end

/-- The lines of instructions run, each instruction with what it compares and what it assigns. -/
private def runLines (fixed : Std.HashMap String Held) (instructions : List Disasm.Insn) :
    List (Disasm.Insn × List (Bap.Var × Nat) × List (Bap.Var × Held)) × List String :=
  let targets : Std.HashSet Nat := instructions.foldl (init := {}) fun set insn =>
    match insn.target with
    | some target => set.insert target
    | none => set
  let step (state : Line × Option Disasm.Insn × List (Disasm.Insn × List (Bap.Var × Nat) × List (Bap.Var × Held)) × Option (List String))
      (insn : Disasm.Insn) :=
    let (line, before, done, saved) := state
    -- a line ends where control comes in from elsewhere, and after a call, which may write anything
    let on : Bool := match before with
      | some before => before.next == insn.address && before.fallsThrough && before.flow != .call && !targets.contains insn.address
      | none => false
    -- what the first line stores as it was is what the function saves
    let saved := if on || before.isNone then saved else saved <|> some line.saves
    let line : Line := { held := if on then line.held else {}, fixed, saves := if on then line.saves else []
                         first := before.isNone || (on && line.first) }
    let after := insn.bil.foldl stmtLine { line with compares := [], assigns := [] }
    let held := after.held.filter fun name held => !name.startsWith "_" && match held with
      | .place source _ => !isTemporary source
      | _ => true
    ({ after with held }, some insn, (insn, after.compares.reverse.eraseDups, after.assigns.reverse) :: done, saved)
  let (line, _, done, saved) := instructions.foldl step (({} : Line), none, [], none)
  (done.reverse, saved.getD line.saves)

/-- The instructions with what they do to the state of a machine as `analyze` reads it: each assignment of a constant to a
register or a slot of memory as a move of it, each comparison of one against a constant as the condition of a branch that does
nothing, and the jumps as they were. -/
def normalize (instructions : List Disasm.Insn) : List Disasm.Insn :=
  -- the registers that are only ever given one constant hold it wherever they are read
  -- but for what restores one that the function saved
  let (first, saved) := runLines {} instructions
  let given : Std.HashMap String (List (Option Nat)) := first.foldl (init := {}) fun table (_, _, assigns) =>
    assigns.foldl (init := table) fun table (var, value) =>
      let restores := saved.contains var.name.str && match value with
        | .place source 0 => isSlot source
        | _ => false
      let constant := match value with
        | .const _ value => some value
        | _ => none
      if isSlot var || restores then table else table.insert var.name.str (constant :: table.getD var.name.str [])
  let widths : Std.HashMap String Nat := first.foldl (init := {}) fun table (_, _, assigns) =>
    assigns.foldl (init := table) fun table (var, _) =>
      match var.typ with
      | .imm width => table.insert var.name.str width
      | _ => table
  let fixed : Std.HashMap String Held := given.fold (init := {}) fun table name values =>
    match values, widths[name]? with
    | some value :: rest, some width => if rest.all (· == some value) then table.insert name (.const width value) else table
    | _, _ => table
  (runLines fixed instructions).1.map fun (insn, compares, assigns) =>
    let width (var : Bap.Var) : Nat := match var.typ with
      | .imm width => width
      | _ => 64
    let moves := assigns.filterMap fun (var, value) => match value with
      | .const _ value => some (Bil.Stmt.move var (.int (BitVec.ofNat (width var) value)))
      | _ => none
    let tests := compares.map fun (var, value) =>
      Bil.Stmt.ifElse (.bin .eq (.var var) (.int (BitVec.ofNat (width var) value))) [] []
    let jumps := insn.bil.filter fun stmt => match stmt with
      | .jmp _ => true
      | _ => false
    { insn with bil := moves ++ tests ++ jumps }

/-- The machine of the code of a compiler: `analyze` of it as `normalize` has it. -/
def ofCode (instructions : List Disasm.Insn) : Result := analyze (normalize instructions)

end Bap.Analysis.StateMachine
