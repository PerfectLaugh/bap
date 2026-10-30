import Bap.Bil.Typecheck
import Bap.Core.Memory

namespace Bap.Bil

abbrev Env := List (Bap.Var × Value)

def lookup (env : Env) (var : Bap.Var) : Except String Value :=
  match env.find? fun binding => binding.1 == var with
  | some binding => .ok binding.2
  | none => .error s!"unbound variable {var.name}"

def bind (env : Env) (var : Bap.Var) (value : Value) : Env :=
  (var, value) :: env.filter fun binding => binding.1 != var

def bindMany (env : Env) (updates : List (Bap.Var × Value)) : Env :=
  let latest := updates.foldl (init := []) fun current update =>
    update :: current.filter (fun binding => binding.1 != update.1)
  let variables := updates.map Prod.fst
  latest ++ env.filter fun binding => !variables.contains binding.1

private def expectMemory : Value → Except String (Σ width, Memory width)
  | .memory value => .ok ⟨_, value⟩
  | _ => .error "expected memory"

def evalBin (op : BinOp) (left right : Σ width, BitVec width) : Except String Value := do
  let ⟨leftWidth, left⟩ := left
  let ⟨rightWidth, right⟩ := right
  if h : leftWidth = rightWidth then
    let right : BitVec leftWidth := h ▸ right
    let bits {width : Nat} (value : BitVec width) : Except String Value := .ok (.bits value)
    match op with
    | .add => bits (left + right)
    | .sub => bits (left - right)
    | .mul => bits (left * right)
    | .div => bits (Word.udiv left right)
    | .sdiv => bits (Word.sdiv left right)
    | .rem => bits (Word.urem left right)
    | .srem => bits (Word.srem left right)
    | .smod => bits (Word.smod left right)
    | .lshift => bits (Word.shl left right)
    | .rshift => bits (Word.lshr left right)
    | .ashift => bits (Word.ashr left right)
    | .and => bits (left &&& right)
    | .or => bits (left ||| right)
    | .xor => bits (left ^^^ right)
    | .eq => bits (Word.eq left right)
    | .neq => bits (Word.neq left right)
    | .lt => bits (Word.lt left right)
    | .le => bits (Word.le left right)
    | .gt => bits (Word.lt right left)
    | .ge => bits (Word.le right left)
    | .slt => bits (Word.slt left right)
    | .sle => bits (Word.sle left right)
    | .sgt => bits (Word.slt right left)
    | .sge => bits (Word.sle right left)
  else
    .error "binary operands have different widths"

private def evalUn (op : UnOp) (value : Σ width, BitVec width) : Value :=
  match op with
  | .neg => .bits (-value.2)
  | .not => .bits (~~~value.2)

def evalExp (env : Env) : Exp → Except String Value
  | .int value => .ok (.bits value)
  | .var var => lookup env var
  | .load memory address endian size => do
    let ⟨addressWidth, memory⟩ ← expectMemory (← evalExp env memory)
    let ⟨actualWidth, address⟩ ← Value.asBits (← evalExp env address)
    if h : actualWidth = addressWidth then
      let address : BitVec addressWidth := h ▸ address
      .ok (.bits (Memory.read memory address endian size))
    else
      .error "address width does not match memory"
  | .store memory address value endian size => do
    let ⟨addressWidth, memory⟩ ← expectMemory (← evalExp env memory)
    let ⟨actualWidth, address⟩ ← Value.asBits (← evalExp env address)
    let value ← Value.asBits (← evalExp env value)
    if h : actualWidth = addressWidth then
      let address : BitVec addressWidth := h ▸ address
      let updated ← Memory.write memory address value.2 endian size
      .ok (.memory updated)
    else
      .error "address width does not match memory"
  | .bin op left right => do
    let left ← Value.asBits (← evalExp env left)
    let right ← Value.asBits (← evalExp env right)
    evalBin op left right
  | .un op value => do
    .ok (evalUn op (← Value.asBits (← evalExp env value)))
  | .cast kind width value => do
    let value ← Value.asBits (← evalExp env value)
    match kind with
    | .low => .ok (.bits (Word.low width value.2))
    | .unsigned => .ok (.bits (Word.unsigned width value.2))
    | .signed => .ok (.bits (Word.signed width value.2))
    | .high => do
      let result ← Word.high width value.2
      .ok (.bits result)
  | .letIn var value body => do
    let value ← evalExp env value
    evalExp (bind env var value) body
  | .ite condition yes no => do
    let ⟨width, condition⟩ ← Value.asBits (← evalExp env condition)
    if h : width = 1 then
      let condition : BitVec 1 := h ▸ condition
      if condition = 1 then evalExp env yes else evalExp env no
    else
      .error "condition must be one bit"
  | .extract high low value => do
    let value ← Value.asBits (← evalExp env value)
    let result ← Word.extract high low value.2
    .ok (.bits result)
  | .concat left right => do
    let left ← Value.asBits (← evalExp env left)
    let right ← Value.asBits (← evalExp env right)
    .ok (.bits (Word.concat left.2 right.2))
  | .unknown message _ => .error s!"cannot evaluate unknown value: {message}"

inductive Effect where
  | normal
  | jump {width : Nat} (target : BitVec width)
  | special (message : String)
  | cpuExn (number : Nat)
  deriving Repr

structure State where
  env : Env := []
  deriving Repr

def execExp (state : State) (exp : Exp) : Except String Value := evalExp state.env exp

mutual
  def execStmt (fuel : Nat) (state : State) (stmt : Stmt) : Except String (State × Effect) :=
    match fuel with
    | 0 => .error "execution fuel exhausted"
    | fuel + 1 =>
      match stmt with
      | .move var value => do
        let value ← execExp state value
        .ok ({ env := bind state.env var value }, .normal)
      | .jmp target => do
        let target ← Value.asBits (← execExp state target)
        .ok (state, .jump target.2)
      | .special message => .ok (state, .special message)
      | .cpuExn number => .ok (state, .cpuExn number)
      | .ifElse condition yes no => do
        let ⟨width, condition⟩ ← Value.asBits (← execExp state condition)
        if h : width = 1 then
          let condition : BitVec 1 := h ▸ condition
          execProgram fuel state (if condition = 1 then yes else no)
        else
          .error "condition must be one bit"
      | .while condition body => do
        let ⟨width, conditionValue⟩ ← Value.asBits (← execExp state condition)
        if h : width = 1 then
          let conditionValue : BitVec 1 := h ▸ conditionValue
          if conditionValue = 1 then
            let (next, effect) ← execProgram fuel state body
            match effect with
            | .normal => execStmt fuel next (.while condition body)
            | other => .ok (next, other)
          else
            .ok (state, .normal)
        else
          .error "condition must be one bit"

  def execProgram (fuel : Nat) (state : State) (program : Program) :
      Except String (State × Effect) :=
    match fuel with
    | 0 => .error "execution fuel exhausted"
    | fuel + 1 =>
      match program with
      | [] => .ok (state, .normal)
      | stmt :: rest => do
        let (next, effect) ← execStmt fuel state stmt
        match effect with
        | .normal => execProgram fuel next rest
        | other => .ok (next, other)
end

def run (program : Program) (initial : State := {}) (fuel : Nat := 100000) :
    Except String (State × Effect) :=
  execProgram fuel initial program

end Bap.Bil
