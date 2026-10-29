import Bap.Symbolic.Expr
import Bap.Symbolic.Memory
import Bap.Bil.Eval
import Bap.Core.Assoc

namespace Bap.Symbolic

abbrev Env := List (Bap.Var × Expr)

structure State where
  env : Env := []
  constraints : List Expr := []
  memory : Memory := Memory.empty
  deriving Repr

inductive Outcome where
  | normal
  | jump (target : Expr)
  | special (message : String)
  | cpuExn (number : Nat)
  deriving Repr

structure Result where
  state : State
  outcome : Outcome
  deriving Repr

private def lookup (env : Env) (var : Bap.Var) : Except String Expr :=
  match Assoc.get var env with
  | some value => .ok value
  | none => .error s!"unbound symbolic variable {var.name}"

private def binary (op : Bil.BinOp) (left right : Expr) : Expr :=
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

mutual
  private def evalMemory (state : State) : Bil.Exp → Except String Memory
  | .var _ => .ok state.memory
  | .store memory address value endian size => do
    let memory ← evalMemory state memory
    let address ← evalExp state address
    let value ← evalExp state value
    .ok (Memory.write memory address value endian size)
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
  | .letIn var value body => do
    let value ← evalExp state value
    evalExp { state with env := (var, value) :: state.env } body
  | .ite condition yes no => do
    let condition ← evalExp state condition
    let yes ← evalExp state yes
    let no ← evalExp state no
    .ok (.ite condition yes no)
  | .extract high low value => do
    let value ← evalExp state value
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

private def withConstraint (state : State) (constraint : Expr) : State :=
  { state with constraints := state.constraints ++ [constraint] }

mutual
  private def executeStmt (fuel : Nat) (state : State) (stmt : Bil.Stmt) : Except String (List Result) := do
  match fuel with
  | 0 => .error "symbolic execution fuel exhausted"
  | fuel + 1 =>
    match stmt with
    | .move var value => do
      match var.typ with
      | .mem _ _ => do
        let memory ← evalMemory state value
        .ok [⟨{ state with memory := memory }, .normal⟩]
      | _ => do
        let value ← evalExp state value
        .ok [⟨{ state with env := (var, value) :: state.env }, .normal⟩]
    | .jmp target => do
      let target ← evalExp state target
      .ok [⟨state, .jump target⟩]
    | .special message => .ok [⟨state, .special message⟩]
    | .cpuExn number => .ok [⟨state, .cpuExn number⟩]
    | .ifElse condition yes no => do
      let condition ← evalExp state condition
      let yesState := withConstraint state (.eqOne condition)
      let noState := withConstraint state (.eqZero condition)
      let yesResults ← executeProgram fuel yesState yes
      let noResults ← executeProgram fuel noState no
      .ok (yesResults ++ noResults)
    | .while condition body => do
      let conditionValue ← evalExp state condition
      let bodyState := withConstraint state (.eqOne conditionValue)
      let bodyResults ← executeProgram fuel bodyState body
      let rec continueResults (results : List Result) : Except String (List Result) :=
        match results with
        | [] => .ok []
        | result :: rest =>
          match result.outcome with
          | .normal => executeStmt fuel result.state (.while condition body)
          | _ => do
            let results ← continueResults rest
            .ok (result :: results)
      let continuation ← continueResults bodyResults
      let exit := withConstraint state (.eqZero conditionValue)
      .ok (continuation ++ [⟨exit, .normal⟩])

private def executeProgram (fuel : Nat) (state : State) (program : Bil.Program) :
    Except String (List Result) := do
  match fuel, program with
  | 0, _ :: _ => .error "symbolic execution fuel exhausted"
  | _, [] => .ok [⟨state, .normal⟩]
  | fuel + 1, stmt :: rest => do
    let results ← executeStmt fuel state stmt
    let rec continueResults (results : List Result) : Except String (List Result) :=
      match results with
      | [] => .ok []
      | result :: remaining =>
        match result.outcome with
        | .normal => executeProgram fuel result.state rest
        | _ => do
          let results ← continueResults remaining
          .ok (result :: results)
    continueResults results
end

def run (program : Bil.Program) (initial : State := {}) (fuel : Nat := 1000) :
    Except String (List Result) :=
  executeProgram fuel initial program

end Bap.Symbolic
