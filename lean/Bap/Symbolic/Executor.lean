import Bap.Symbolic.Expr
import Bap.Symbolic.Memory
import Bap.Bil.Eval
import Bap.Core.Assoc

namespace Bap.Symbolic

abbrev Env := List (Bap.Var × Expr)

structure State where
  env : Env := []
  constraints : List Expr := []
  /-- The memory of each memory variable written so far; the others are still unconstrained. -/
  memories : List (Bap.Var × Memory) := []
  /-- The number of `unknown` values drawn along this path. -/
  unknowns : Nat := 0
  deriving Repr

inductive Outcome where
  | normal
  | jump (target : Expr)
  | special (message : String)
  | cpuExn (number : Nat)
  /-- The exploration bound ran out here: the path is neither finished nor refuted. -/
  | exhausted
  deriving Repr

structure Result where
  state : State
  outcome : Outcome
  deriving Repr

private def lookup (env : Env) (var : Bap.Var) : Except String Expr :=
  if var.typ matches .mem _ _ then
    .error s!"memory variable {var.name} used as a bitvector"
  else
    match Assoc.get var env with
    | some value => .ok value
    | none => .error s!"unbound symbolic variable {var.name}"

/-- The memory of a variable that holds one; each has its own initial contents. -/
def memoryOf (state : State) (var : Bap.Var) : Memory :=
  match Assoc.get var state.memories with
  | some memory => memory
  | none => { name := s!"{var.name}#{var.index}" }

private def binaryApp (op : Bil.BinOp) (left right : Expr) : Expr :=
  let name := match op with
    | .add => "bvadd"
    | .sub => "bvsub"
    | .mul => "bvmul"
    | .div => "bvudiv"
    | .sdiv => "bvsdiv"
    | .rem => "bvurem"
    | .srem => "bvsrem"
    | .smod => "bvsmod"
    | .lshift => "bvshl"
    | .rshift => "bvlshr"
    | .ashift => "bvashr"
    | .and => "bvand"
    | .or => "bvor"
    | .xor => "bvxor"
    | .eq => "="
    | .neq => "distinct"
    | .lt => "bvult"
    | .le => "bvule"
    | .gt => "bvugt"
    | .ge => "bvuge"
    | .slt => "bvslt"
    | .sle => "bvsle"
    | .sgt => "bvsgt"
    | .sge => "bvsge"
  .app name (if op matches .eq | .neq | .lt | .le | .gt | .ge | .slt | .sle | .sgt | .sge then 1 else left.width) [left, right]

/-- BIL defines signed division by zero as all ones, SMT-LIB as a value that depends on the sign. -/
private def signedDivision (left right : Expr) : Expr :=
  .ite (.app "=" 1 [right, .const (BitVec.ofNat right.width 0)]) (.const (BitVec.allOnes left.width))
    (binaryApp .sdiv left right)

private def binary (op : Bil.BinOp) (left right : Expr) : Expr :=
  let symbolic :=
    match op with
    | .sdiv => signedDivision left right
    | _ => binaryApp op left right
  match left, right with
  | @Expr.const leftWidth leftValue, @Expr.const rightWidth rightValue =>
    match Bil.evalBin op ⟨leftWidth, leftValue⟩ ⟨rightWidth, rightValue⟩ with
    | .ok (.bits value) => .const value
    | _ => symbolic
  | _, _ => symbolic

private def evalCast (kind : Bil.Cast) (width : Nat) (value : Expr) : Except String Expr :=
  if width = 0 then
    .error "cast width must be positive"
  else
    match kind with
    | .high =>
      if value.width < width then
        .error "invalid high cast"
      else
        .ok (.extract (value.width - 1) (value.width - width) value)
    | .low | .unsigned | .signed =>
      if width ≤ value.width then
        .ok (.extract (width - 1) 0 value)
      else
        let extension := if kind matches .signed then "sign_extend" else "zero_extend"
        .ok (.app s!"(_ {extension} {width - value.width})" width [value])

private def isMemoryType : Typ → Bool
  | .mem _ _ => true
  | _ => false

mutual
  private def evalMemory (state : State) : Bil.Exp → Except String Memory
  | .var var =>
    if isMemoryType var.typ then .ok (memoryOf state var) else .error "expected symbolic memory"
  | .store memory address value endian size => do
    let memory ← evalMemory state memory
    let address ← evalExp state address
    let value ← evalExp state value
    if value.width ≠ size * 8 then
      .error "stored value has the wrong width"
    else
      .ok (Memory.write memory address value endian size)
  | .letIn var value body =>
    if isMemoryType var.typ then do
      let value ← evalMemory state value
      evalMemory { state with memories := (var, value) :: state.memories } body
    else do
      let value ← evalExp state value
      evalMemory { state with env := (var, value) :: state.env } body
  | _ => .error "expected symbolic memory"

def evalExp (state : State) : Bil.Exp → Except String Expr
  | .int value => .ok (.const value)
  | .var var => lookup state.env var
  | .bin op left right => do
    let left ← evalExp state left
    let right ← evalExp state right
    .ok (binary op left right)
  | .un op value => do
    let value ← evalExp state value
    .ok (.app (match op with | .neg => "bvneg" | .not => "bvnot") value.width [value])
  | .cast kind width value => do
    let value ← evalExp state value
    evalCast kind width value
  | .letIn var value body =>
    if isMemoryType var.typ then do
      let value ← evalMemory state value
      evalExp { state with memories := (var, value) :: state.memories } body
    else do
      let value ← evalExp state value
      evalExp { state with env := (var, value) :: state.env } body
  | .ite condition yes no => do
    let condition ← evalExp state condition
    let yes ← evalExp state yes
    let no ← evalExp state no
    if condition.width ≠ 1 then
      .error "condition must be one bit"
    else if yes.width ≠ no.width then
      .error "branches of a conditional have different widths"
    else
      .ok (.ite condition yes no)
  | .extract high low value => do
    let value ← evalExp state value
    if high < low then
      .error "extract high bound is below low bound"
    else if high ≥ value.width then
      .error "extract high bound exceeds source width"
    else
      .ok (.extract high low value)
  | .concat left right => do
    let left ← evalExp state left
    let right ← evalExp state right
    .ok (.concat left right)
  | .unknown message typ =>
    let width := match typ with | .imm width => width | _ => 64
    .ok (.var s!"unknown_{message}" width)
  | .load memory address endian size => do
    let memory ← evalMemory state memory
    let address ← evalExp state address
    .ok (Memory.read memory address endian size)
  | .store _ _ _ _ _ => .error "memory expression used as a bitvector"
end

/-- Gives every `unknown` in an expression a name of its own: separate unknowns are separate values. -/
def freshenUnknowns (next : Nat) : Bil.Exp → Bil.Exp × Nat
  | .unknown message typ => (.unknown s!"{message}#{next}" typ, next + 1)
  | .int value => (.int value, next)
  | .var var => (.var var, next)
  | .load memory address endian size =>
    let (memory, next) := freshenUnknowns next memory
    let (address, next) := freshenUnknowns next address
    (.load memory address endian size, next)
  | .store memory address value endian size =>
    let (memory, next) := freshenUnknowns next memory
    let (address, next) := freshenUnknowns next address
    let (value, next) := freshenUnknowns next value
    (.store memory address value endian size, next)
  | .bin op left right =>
    let (left, next) := freshenUnknowns next left
    let (right, next) := freshenUnknowns next right
    (.bin op left right, next)
  | .un op value =>
    let (value, next) := freshenUnknowns next value
    (.un op value, next)
  | .cast kind width value =>
    let (value, next) := freshenUnknowns next value
    (.cast kind width value, next)
  | .letIn var value body =>
    let (value, next) := freshenUnknowns next value
    let (body, next) := freshenUnknowns next body
    (.letIn var value body, next)
  | .ite condition yes no =>
    let (condition, next) := freshenUnknowns next condition
    let (yes, next) := freshenUnknowns next yes
    let (no, next) := freshenUnknowns next no
    (.ite condition yes no, next)
  | .extract high low value =>
    let (value, next) := freshenUnknowns next value
    (.extract high low value, next)
  | .concat left right =>
    let (left, next) := freshenUnknowns next left
    let (right, next) := freshenUnknowns next right
    (.concat left right, next)

private def freshen (state : State) (exp : Bil.Exp) : State × Bil.Exp :=
  let (exp, unknowns) := freshenUnknowns state.unknowns exp
  ({ state with unknowns := unknowns }, exp)

private def withConstraint (state : State) (constraint : Expr) : State :=
  { state with constraints := state.constraints ++ [constraint] }

/-- The value of a condition when it does not depend on the assignment. -/
def Expr.knownCondition : Expr → Option Bool
  | @Expr.const width value => if width = 1 then some (value.toNat == 1) else none
  | _ => none

private def expectCondition (condition : Expr) : Except String Expr :=
  if condition.width = 1 then .ok condition else .error "condition must be one bit"

mutual
  private def executeStmt (fuel : Nat) (state : State) (stmt : Bil.Stmt) : Except String (List Result) := do
  match fuel with
  | 0 => .ok [⟨state, .exhausted⟩]
  | fuel + 1 =>
    match stmt with
    | .move var value => do
      let (state, value) := freshen state value
      if isMemoryType var.typ then do
        let memory ← evalMemory state value
        .ok [⟨{ state with memories := (var, memory) :: state.memories }, .normal⟩]
      else do
        let value ← evalExp state value
        .ok [⟨{ state with env := (var, value) :: state.env }, .normal⟩]
    | .jmp target => do
      let (state, target) := freshen state target
      let target ← evalExp state target
      .ok [⟨state, .jump target⟩]
    | .special message => .ok [⟨state, .special message⟩]
    | .cpuExn number => .ok [⟨state, .cpuExn number⟩]
    | .ifElse condition yes no => do
      let (state, condition) := freshen state condition
      let condition ← expectCondition (← evalExp state condition)
      match condition.knownCondition with
      | some true => executeProgram fuel state yes
      | some false => executeProgram fuel state no
      | none =>
        let yesResults ← executeProgram fuel (withConstraint state (.eqOne condition)) yes
        let noResults ← executeProgram fuel (withConstraint state (.eqZero condition)) no
        .ok (yesResults ++ noResults)
    | .while condition body => do
      let (state, conditionExp) := freshen state condition
      let conditionValue ← expectCondition (← evalExp state conditionExp)
      let rec continueResults (results : List Result) : Except String (List Result) :=
        match results with
        | [] => .ok []
        | result :: rest => do
          let first ← match result.outcome with
            | .normal => executeStmt fuel result.state (.while condition body)
            | _ => .ok [result]
          let others ← continueResults rest
          .ok (first ++ others)
      match conditionValue.knownCondition with
      | some true => continueResults (← executeProgram fuel state body)
      | some false => .ok [⟨state, .normal⟩]
      | none =>
        let bodyResults ← executeProgram fuel (withConstraint state (.eqOne conditionValue)) body
        let continuation ← continueResults bodyResults
        .ok (continuation ++ [⟨withConstraint state (.eqZero conditionValue), .normal⟩])

private def executeProgram (fuel : Nat) (state : State) (program : Bil.Program) :
    Except String (List Result) := do
  match fuel, program with
  | _, [] => .ok [⟨state, .normal⟩]
  | 0, _ :: _ => .ok [⟨state, .exhausted⟩]
  | fuel + 1, stmt :: rest => do
    let results ← executeStmt fuel state stmt
    let rec continueResults (results : List Result) : Except String (List Result) :=
      match results with
      | [] => .ok []
      | result :: remaining => do
        let first ← match result.outcome with
          | .normal => executeProgram fuel result.state rest
          | _ => .ok [result]
        let others ← continueResults remaining
        .ok (first ++ others)
    continueResults results
end

def run (program : Bil.Program) (initial : State := {}) (fuel : Nat := 1000) :
    Except String (List Result) :=
  executeProgram fuel initial program

end Bap.Symbolic
