import Bap.Bil.Typecheck
import Bap.Core.Memory
import Bap.Core.VarMap
import Bap.Graph.Fast

namespace Bap.Bil

/-- The values of variables: one for each, in a `VarMap`, which finds a variable where it is rather than by going through the others. -/
abbrev Env := VarMap Value

def lookup (env : Env) (var : Bap.Var) : Except String Value :=
  match env.get? var with
  | some value => .ok value
  | none => .error s!"unbound variable {var.name}"

/-- The environment with `var` bound to `value`, where it was if it was bound already. -/
def bind (env : Env) (var : Bap.Var) (value : Value) : Env :=
  env.insert var value

/-- Each of `updates` bound in turn, so that a later one of a variable is what it has. -/
def bindMany (env : Env) (updates : List (Bap.Var × Value)) : Env :=
  updates.foldl (fun env update => bind env update.1 update.2) env

theorem lookup_bind (env : Env) (var other : Bap.Var) (value : Value) :
    lookup (bind env var value) other = if var = other then .ok value else lookup env other := by
  simp only [lookup, bind, VarMap.get?_insert]
  by_cases h : var = other <;> simp [h]

@[simp] theorem lookup_bind_self (env : Env) (var : Bap.Var) (value : Value) :
    lookup (bind env var value) var = .ok value := by
  simp [lookup_bind]

theorem lookup_bind_of_ne (env : Env) {var other : Bap.Var} (value : Value) (h : var ≠ other) :
    lookup (bind env var value) other = lookup env other := by
  simp [lookup_bind, h]

/-- A variable that none of the updates bind keeps its value. -/
theorem lookup_bindMany_of_not_mem (env : Env) (updates : List (Bap.Var × Value)) {var : Bap.Var}
    (h : var ∉ updates.map Prod.fst) : lookup (bindMany env updates) var = lookup env var := by
  induction updates generalizing env with
  | nil => rfl
  | cons update rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [bindMany, List.foldl_cons] at ih ⊢
    rw [ih _ h.2, lookup_bind_of_ne _ _ (Ne.symm h.1)]

/-- A variable that the updates bind, each time to the same value, has it. -/
theorem lookup_bindMany_of_mem (env : Env) (updates : List (Bap.Var × Value)) {var : Bap.Var} {value : Value}
    (hm : (var, value) ∈ updates) (hu : ∀ update ∈ updates, update.1 = var → update.2 = value) :
    lookup (bindMany env updates) var = .ok value := by
  induction updates generalizing env with
  | nil => cases hm
  | cons update rest ih =>
    simp only [bindMany, List.foldl_cons] at ih ⊢
    by_cases hr : ∃ other, (var, other) ∈ rest
    · obtain ⟨other, ho⟩ := hr
      have he := hu _ (List.mem_cons_of_mem _ ho) rfl
      simp only at he
      subst he
      exact ih _ ho fun b hb => hu b (List.mem_cons_of_mem _ hb)
    · have hnot : var ∉ rest.map Prod.fst := fun h => by
        obtain ⟨⟨k, v⟩, hb, he⟩ := List.mem_map.1 h
        simp only at he
        subst he
        exact hr ⟨v, hb⟩
      have hupdate : update = (var, value) := by
        rcases List.mem_cons.1 hm with h | h
        · exact h.symm
        · exact absurd ⟨value, h⟩ hr
      subst hupdate
      have := lookup_bindMany_of_not_mem (bind env var value) rest hnot
      simp only [bindMany] at this
      rw [this, lookup_bind_self]

@[simp] theorem lookup_empty (var : Bap.Var) : lookup ({} : Env) var = .error s!"unbound variable {var.name}" := by
  simp [lookup]

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

private def evalBinFast (op : BinOp) (left right : Σ width, BitVec width) : Except String Value := do
  let ⟨leftWidth, left⟩ := left
  let ⟨rightWidth, right⟩ := right
  if h : leftWidth = rightWidth then
    let right : BitVec leftWidth := h ▸ right
    let bits {width : Nat} (value : BitVec width) : Except String Value := .ok (.bits value)
    match op with
    | .add => bits (Word.addFast left right)
    | .sub => bits (Word.subFast left right)
    | .mul => bits (Word.mulFast left right)
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

@[csimp] private theorem evalBin_eq_fast : @evalBin = @evalBinFast := by
  funext op left right
  obtain ⟨leftWidth, left⟩ := left
  obtain ⟨rightWidth, right⟩ := right
  unfold evalBin evalBinFast
  cases op <;> simp only [Word.addFast_eq, Word.subFast_eq, Word.mulFast_eq]

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
  env : Env := {}
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

/-! ### `let` without copying the environment

`evalExp` binds the variable of a `let` in the environment, which a caller still has, so that it would be copied. Here a `let` is in a
short list in front of the environment instead. -/

section Fast

/-- What `lookup` finds: in the scope of a `let`, or in the environment. -/
private def lookupIn (env : Env) (scope : List (Bap.Var × Value)) (var : Bap.Var) : Except String Value :=
  match scope.find? fun binding => binding.1 == var with
  | some binding => .ok binding.2
  | none => lookup env var

/-- `evalExp` on an environment and the `let` bindings in scope. -/
private def evalScoped (env : Env) (scope : List (Bap.Var × Value)) : Exp → Except String Value
  | .int value => .ok (.bits value)
  | .var var => lookupIn env scope var
  | .load memory address endian size => do
    let ⟨addressWidth, memory⟩ ← expectMemory (← evalScoped env scope memory)
    let ⟨actualWidth, address⟩ ← Value.asBits (← evalScoped env scope address)
    if h : actualWidth = addressWidth then
      let address : BitVec addressWidth := h ▸ address
      .ok (.bits (Memory.read memory address endian size))
    else
      .error "address width does not match memory"
  | .store memory address value endian size => do
    let ⟨addressWidth, memory⟩ ← expectMemory (← evalScoped env scope memory)
    let ⟨actualWidth, address⟩ ← Value.asBits (← evalScoped env scope address)
    let value ← Value.asBits (← evalScoped env scope value)
    if h : actualWidth = addressWidth then
      let address : BitVec addressWidth := h ▸ address
      let updated ← Memory.write memory address value.2 endian size
      .ok (.memory updated)
    else
      .error "address width does not match memory"
  | .bin op left right => do
    let left ← Value.asBits (← evalScoped env scope left)
    let right ← Value.asBits (← evalScoped env scope right)
    evalBin op left right
  | .un op value => do
    .ok (evalUn op (← Value.asBits (← evalScoped env scope value)))
  | .cast kind width value => do
    let value ← Value.asBits (← evalScoped env scope value)
    match kind with
    | .low => .ok (.bits (Word.low width value.2))
    | .unsigned => .ok (.bits (Word.unsigned width value.2))
    | .signed => .ok (.bits (Word.signed width value.2))
    | .high => do
      let result ← Word.high width value.2
      .ok (.bits result)
  | .letIn var value body => do
    let value ← evalScoped env scope value
    evalScoped env ((var, value) :: scope) body
  | .ite condition yes no => do
    let ⟨width, condition⟩ ← Value.asBits (← evalScoped env scope condition)
    if h : width = 1 then
      let condition : BitVec 1 := h ▸ condition
      if condition = 1 then evalScoped env scope yes else evalScoped env scope no
    else
      .error "condition must be one bit"
  | .extract high low value => do
    let value ← Value.asBits (← evalScoped env scope value)
    let result ← Word.extract high low value.2
    .ok (.bits result)
  | .concat left right => do
    let left ← Value.asBits (← evalScoped env scope left)
    let right ← Value.asBits (← evalScoped env scope right)
    .ok (.bits (Word.concat left.2 right.2))
  | .unknown message _ => .error s!"cannot evaluate unknown value: {message}"

private theorem evalScoped_eq (env : Env) (exp : Exp) (scope : List (Bap.Var × Value)) (spec : Env)
    (h : ∀ var, lookupIn env scope var = lookup spec var) : evalScoped env scope exp = evalExp spec exp := by
  induction exp generalizing scope spec with
  | letIn var value body ihv ihb =>
    simp only [evalScoped, evalExp, ihv scope spec h]
    cases evalExp spec value with
    | error => rfl
    | ok value =>
      apply ihb
      intro other
      rw [lookup_bind]
      by_cases he : var = other
      · simp [lookupIn, he]
      · have := h other
        simp [lookupIn, he] at this ⊢
        exact this
  | var var => exact h var
  | int value => rfl
  | unknown message typ => rfl
  | load memory address endian size ihm iha =>
    simp only [evalScoped, evalExp, ihm scope spec h, iha scope spec h]
  | store memory address value endian size ihm iha ihv =>
    simp only [evalScoped, evalExp, ihm scope spec h, iha scope spec h, ihv scope spec h]
  | bin op left right ihl ihr =>
    simp only [evalScoped, evalExp, ihl scope spec h, ihr scope spec h]
  | un op value ih => simp only [evalScoped, evalExp, ih scope spec h]
  | cast kind width value ih => simp only [evalScoped, evalExp, ih scope spec h]
  | ite condition yes no ihc ihy ihn =>
    simp only [evalScoped, evalExp, ihc scope spec h, ihy scope spec h, ihn scope spec h]
  | extract high low value ih => simp only [evalScoped, evalExp, ih scope spec h]
  | concat left right ihl ihr => simp only [evalScoped, evalExp, ihl scope spec h, ihr scope spec h]

private def evalExpFast (env : Env) (exp : Exp) : Except String Value := evalScoped env [] exp

@[csimp] private theorem evalExp_eq_fast : @evalExp = @evalExpFast := by
  funext env exp
  exact (evalScoped_eq env exp [] env fun _ => rfl).symm

end Fast

def run (program : Program) (initial : State := {}) (fuel : Nat := 100000) :
    Except String (State × Effect) :=
  execProgram fuel initial program

end Bap.Bil
