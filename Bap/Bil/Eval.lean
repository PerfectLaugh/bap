import Bap.Bil.Typecheck
import Bap.Core.Memory
import Bap.Graph.Fast

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

/-! ### Execution on a hash map

`execProgram` with its variables in a hash map. Bindings are in the order the list has them: `log` has the variables bound
since the start, last first, in front of what is left of the list it started from. `let` scopes in `evalInMap` are a short
list in front of the map, as the map outside of them is still in use. -/

section Fast

/-- What `lookup` finds: in the scope of a `let`, or in the map. -/
private def lookupIn (map : Std.HashMap Bap.Var Value) (scope : List (Bap.Var × Value)) (var : Bap.Var) :
    Except String Value :=
  match scope.find? fun binding => binding.1 == var with
  | some binding => .ok binding.2
  | none =>
    match map.get? var with
    | some value => .ok value
    | none => .error s!"unbound variable {var.name}"

/-- `evalExp` on a map and the `let` bindings in scope. -/
private def evalInMap (map : Std.HashMap Bap.Var Value) (scope : List (Bap.Var × Value)) : Exp → Except String Value
  | .int value => .ok (.bits value)
  | .var var => lookupIn map scope var
  | .load memory address endian size => do
    let ⟨addressWidth, memory⟩ ← expectMemory (← evalInMap map scope memory)
    let ⟨actualWidth, address⟩ ← Value.asBits (← evalInMap map scope address)
    if h : actualWidth = addressWidth then
      let address : BitVec addressWidth := h ▸ address
      .ok (.bits (Memory.read memory address endian size))
    else
      .error "address width does not match memory"
  | .store memory address value endian size => do
    let ⟨addressWidth, memory⟩ ← expectMemory (← evalInMap map scope memory)
    let ⟨actualWidth, address⟩ ← Value.asBits (← evalInMap map scope address)
    let value ← Value.asBits (← evalInMap map scope value)
    if h : actualWidth = addressWidth then
      let address : BitVec addressWidth := h ▸ address
      let updated ← Memory.write memory address value.2 endian size
      .ok (.memory updated)
    else
      .error "address width does not match memory"
  | .bin op left right => do
    let left ← Value.asBits (← evalInMap map scope left)
    let right ← Value.asBits (← evalInMap map scope right)
    evalBin op left right
  | .un op value => do
    .ok (evalUn op (← Value.asBits (← evalInMap map scope value)))
  | .cast kind width value => do
    let value ← Value.asBits (← evalInMap map scope value)
    match kind with
    | .low => .ok (.bits (Word.low width value.2))
    | .unsigned => .ok (.bits (Word.unsigned width value.2))
    | .signed => .ok (.bits (Word.signed width value.2))
    | .high => do
      let result ← Word.high width value.2
      .ok (.bits result)
  | .letIn var value body => do
    let value ← evalInMap map scope value
    evalInMap map ((var, value) :: scope) body
  | .ite condition yes no => do
    let ⟨width, condition⟩ ← Value.asBits (← evalInMap map scope condition)
    if h : width = 1 then
      let condition : BitVec 1 := h ▸ condition
      if condition = 1 then evalInMap map scope yes else evalInMap map scope no
    else
      .error "condition must be one bit"
  | .extract high low value => do
    let value ← Value.asBits (← evalInMap map scope value)
    let result ← Word.extract high low value.2
    .ok (.bits result)
  | .concat left right => do
    let left ← Value.asBits (← evalInMap map scope left)
    let right ← Value.asBits (← evalInMap map scope right)
    .ok (.bits (Word.concat left.2 right.2))
  | .unknown message _ => .error s!"cannot evaluate unknown value: {message}"

private theorem lookup_bind (env : Env) (var other : Bap.Var) (value : Value) :
    lookup (bind env var value) other = if var = other then .ok value else lookup env other := by
  simp only [lookup, bind, List.find?_cons]
  by_cases h : var = other
  · subst h
    simp
  · have hfilter : ∀ l : Env, (l.filter fun binding => binding.1 != var).find? (fun binding => binding.1 == other) =
        l.find? fun binding => binding.1 == other := by
      intro l
      induction l with
      | nil => rfl
      | cons b bs ih =>
        rw [List.filter_cons]
        by_cases hb : b.1 = var
        · have h1 : (b.1 != var) = false := by simpa using hb
          have h2 : (b.1 == other) = false := by simpa [hb] using h
          simp [h1, h2, ih]
        · have h1 : (b.1 != var) = true := by simpa using hb
          simp [h1, List.find?_cons, ih]
    have hb : (var == other) = false := by simpa using h
    simp only [hb, hfilter]
    simp [h]

private theorem evalInMap_eq (map : Std.HashMap Bap.Var Value) (exp : Exp) (scope : List (Bap.Var × Value)) (env : Env)
    (h : ∀ var, lookupIn map scope var = lookup env var) : evalInMap map scope exp = evalExp env exp := by
  induction exp generalizing scope env with
  | letIn var value body ihv ihb =>
    simp only [evalInMap, evalExp, ihv scope env h]
    cases evalExp env value with
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
    simp only [evalInMap, evalExp, ihm scope env h, iha scope env h]
  | store memory address value endian size ihm iha ihv =>
    simp only [evalInMap, evalExp, ihm scope env h, iha scope env h, ihv scope env h]
  | bin op left right ihl ihr =>
    simp only [evalInMap, evalExp, ihl scope env h, ihr scope env h]
  | un op value ih => simp only [evalInMap, evalExp, ih scope env h]
  | cast kind width value ih => simp only [evalInMap, evalExp, ih scope env h]
  | ite condition yes no ihc ihy ihn =>
    simp only [evalInMap, evalExp, ihc scope env h, ihy scope env h, ihn scope env h]
  | extract high low value ih => simp only [evalInMap, evalExp, ih scope env h]
  | concat left right ihl ihr => simp only [evalInMap, evalExp, ihl scope env h, ihr scope env h]

private structure MapEnv where
  map : Std.HashMap Bap.Var Value
  log : List Bap.Var := []
  logLength : Nat := 0
  base : Env

/-- The list a `MapEnv` stands for. -/
private def MapEnv.toEnv (state : MapEnv) : Env :=
  state.log.eraseDups.filterMap (fun var => (state.map.get? var).map (var, ·)) ++
    state.base.filter fun binding => !state.log.contains binding.1

private def MapEnv.toEnvFast (state : MapEnv) : Env :=
  match state.log with
  | [] => state.base
  | log =>
    let bound : Std.HashSet Bap.Var := Std.HashSet.ofList log
    (Bap.Graph.Fast.dedup log).filterMap (fun var => (state.map.get? var).map (var, ·)) ++
      state.base.filter fun binding => !bound.contains binding.1

private theorem MapEnv.toEnvFast_eq (state : MapEnv) : state.toEnvFast = state.toEnv := by
  obtain ⟨map, log, n, base⟩ := state
  cases log with
  | nil =>
    have hkeep : ∀ l : Env, (l.filter fun _ => true) = l := fun l => by induction l <;> simp_all
    simp [toEnvFast, toEnv, hkeep]
  | cons v vs =>
    simp only [toEnvFast, toEnv, Bap.Graph.Fast.dedup_eq]
    congr 1
    apply List.filter_congr
    intro b _
    simp [Std.HashSet.contains_ofList]

private def MapEnv.ofEnv (env : Env) : MapEnv :=
  { map := env.foldr (fun binding map => map.insert binding.1 binding.2) {}, base := env }

/-- The log only needs each variable once: one that runs in a loop would keep growing. -/
private def MapEnv.bind (state : MapEnv) (var : Bap.Var) (value : Value) : MapEnv :=
  let map := state.map.insert var value
  if state.logLength ≤ 2 * map.size + 64 then
    { state with map := map, log := var :: state.log, logLength := state.logLength + 1 }
  else
    let log := Bap.Graph.Fast.dedup (var :: state.log)
    { state with map := map, log := log, logLength := log.length }

/-- What a `MapEnv` has to be for a list. -/
private structure MapEnv.Rel (state : MapEnv) (env : Env) : Prop where
  list : state.toEnv = env
  get : ∀ var, state.map.get? var = (env.find? fun binding => binding.1 == var).map (·.2)

private theorem MapEnv.Rel.lookup {state : MapEnv} {env : Env} (h : state.Rel env) (var : Bap.Var) :
    lookupIn state.map [] var = Bil.lookup env var := by
  simp only [lookupIn, List.find?_nil, Bil.lookup, h.get]
  cases env.find? fun binding => binding.1 == var <;> rfl

private theorem MapEnv.rel_ofEnv (env : Env) : (MapEnv.ofEnv env).Rel env := by
  constructor
  · have hkeep : ∀ l : Env, (l.filter fun _ => true) = l := fun l => by induction l <;> simp_all
    simp [ofEnv, toEnv, hkeep]
  · intro var
    simp only [ofEnv]
    induction env with
    | nil => simp
    | cons b bs ih =>
      simp only [List.foldr_cons, List.find?_cons, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at ih ⊢
      by_cases hb : b.1 = var
      · simp [hb]
      · have hq : (b.1 == var) = false := by simpa using hb
        simp [hq, ih]

private theorem filter_eraseDups (p : Bap.Var → Bool) (l : List Bap.Var) :
    l.eraseDups.filter p = (l.filter p).eraseDups := by
  induction h : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    cases l with
    | nil => rfl
    | cons a as =>
      have hlt : (as.filter fun b => !b == a).length < n := by
        have := List.length_filter_le (fun b => !b == a) as
        simp only [List.length_cons] at h
        omega
      have hrec := ih _ hlt (as.filter fun b => !b == a) rfl
      simp only [List.eraseDups_cons, List.filter_cons]
      split
      · rename_i hp
        simp only [List.eraseDups_cons, hrec]
        congr 2
        simp only [List.filter_filter]
        apply List.filter_congr
        intro x _
        by_cases hx : x = a <;> simp [hx, hp, Bool.and_comm]
      · rename_i hp
        rw [hrec]
        congr 1
        simp only [List.filter_filter]
        apply List.filter_congr
        intro x _
        by_cases hx : x = a
        · simp [hx, hp]
        · simp [hx]

private theorem MapEnv.toEnv_cons (state : MapEnv) (var : Bap.Var) (value : Value) (n : Nat) :
    MapEnv.toEnv { state with map := state.map.insert var value, log := var :: state.log, logLength := n } =
      Bil.bind state.toEnv var value := by
  obtain ⟨map, log, m, base⟩ := state
  simp only [toEnv, Bil.bind, List.eraseDups_cons, List.filterMap_cons, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert_self, Option.map_some, List.filter_append, List.filter_filter]
  have hkeep : ∀ x ∈ (log.filter fun b => !b == var).eraseDups,
      ((map.insert var value)[x]?).map (x, ·) = (map[x]?).map (x, ·) := by
    intro x hx
    have hne : x ≠ var := by
      have := (List.mem_filter.1 (List.mem_eraseDups.1 hx)).2
      simpa using this
    have hb : (var == x) = false := by simpa using fun e : var = x => hne e.symm
    simp [Std.HashMap.getElem?_insert, hb]
  have hcongr : ∀ l : List Bap.Var, (∀ x ∈ l, ((map.insert var value)[x]?).map (x, ·) = (map[x]?).map (x, ·)) →
      l.filterMap (fun x => ((map.insert var value)[x]?).map (x, ·)) = l.filterMap fun x => (map[x]?).map (x, ·) := by
    intro l
    induction l with
    | nil => simp
    | cons a as ih =>
      intro hall
      simp only [List.filterMap_cons, hall a List.mem_cons_self, ih fun x hx => hall x (List.mem_cons_of_mem _ hx)]
  rw [hcongr _ hkeep]
  have hfil : (log.eraseDups.filterMap fun x => (map[x]?).map (x, ·)).filter (fun binding => binding.1 != var) =
      (log.filter fun b => !b == var).eraseDups.filterMap fun x => (map[x]?).map (x, ·) := by
    rw [← filter_eraseDups]
    generalize log.eraseDups = l
    induction l with
    | nil => rfl
    | cons a as ih =>
      simp only [List.filterMap_cons, List.filter_cons]
      cases hg : map[a]? with
      | none =>
        by_cases ha : a = var <;> simp [ha, ih, hg] <;> simpa [hg, ha] using ih
      | some v =>
        by_cases ha : a = var <;> simp [ha, ih, hg] <;> simpa [hg, ha] using ih
  simp only [hfil, List.cons_append]
  congr 2
  apply List.filter_congr
  intro b _
  by_cases hb : b.1 = var <;> simp [hb]

private theorem MapEnv.Rel.bind {state : MapEnv} {env : Env} (h : state.Rel env) (var : Bap.Var) (value : Value) :
    (state.bind var value).Rel (Bil.bind env var value) := by
  have hget : ∀ other, (state.map.insert var value).get? other =
      ((Bil.bind env var value).find? fun binding => binding.1 == other).map (·.2) := by
    intro other
    have hl := lookup_bind env var other value
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    have hg := h.get other
    rw [Std.HashMap.get?_eq_getElem?] at hg
    simp only [Bil.lookup] at hl
    by_cases he : var = other
    · subst he
      simp [Bil.bind]
    · have hb : (var == other) = false := by simpa using he
      simp only [hb, Bool.false_eq_true, ite_false, hg]
      simp only [he, ite_false] at hl
      cases h1 : (Bil.bind env var value).find? fun binding => binding.1 == other with
      | none =>
        cases h2 : env.find? fun binding => binding.1 == other with
        | none => rfl
        | some b => simp [h1, h2] at hl
      | some b1 =>
        cases h2 : env.find? fun binding => binding.1 == other with
        | none => simp [h1, h2] at hl
        | some b2 =>
          simp [h1, h2] at hl
          simp [hl]
  have hsame := MapEnv.toEnv_cons state var value
  unfold MapEnv.bind
  dsimp only
  split
  · exact ⟨by rw [hsame, h.list], hget⟩
  · refine ⟨?_, hget⟩
    rw [← h.list, ← hsame 0]
    simp only [toEnv, Bap.Graph.Fast.dedup_eq]
    rw [Bap.Proofs.Graph.eraseDups_of_nodup (Bap.Proofs.Graph.nodup_eraseDups _)]
    congr 1
    apply List.filter_congr
    intro b _
    simp [List.mem_eraseDups]

mutual
  /-- `execStmt` on a `MapEnv`. -/
  private def execStmtInMap (fuel : Nat) (state : MapEnv) (stmt : Stmt) : Except String (MapEnv × Effect) :=
    match fuel with
    | 0 => .error "execution fuel exhausted"
    | fuel + 1 =>
      match stmt with
      | .move var value => do
        let value ← evalInMap state.map [] value
        .ok (state.bind var value, .normal)
      | .jmp target => do
        let target ← Value.asBits (← evalInMap state.map [] target)
        .ok (state, .jump target.2)
      | .special message => .ok (state, .special message)
      | .cpuExn number => .ok (state, .cpuExn number)
      | .ifElse condition yes no => do
        let ⟨width, condition⟩ ← Value.asBits (← evalInMap state.map [] condition)
        if h : width = 1 then
          let condition : BitVec 1 := h ▸ condition
          execProgramInMap fuel state (if condition = 1 then yes else no)
        else
          .error "condition must be one bit"
      | .while condition body => do
        let ⟨width, conditionValue⟩ ← Value.asBits (← evalInMap state.map [] condition)
        if h : width = 1 then
          let conditionValue : BitVec 1 := h ▸ conditionValue
          if conditionValue = 1 then
            let (next, effect) ← execProgramInMap fuel state body
            match effect with
            | .normal => execStmtInMap fuel next (.while condition body)
            | other => .ok (next, other)
          else
            .ok (state, .normal)
        else
          .error "condition must be one bit"

  private def execProgramInMap (fuel : Nat) (state : MapEnv) (program : Program) : Except String (MapEnv × Effect) :=
    match fuel with
    | 0 => .error "execution fuel exhausted"
    | fuel + 1 =>
      match program with
      | [] => .ok (state, .normal)
      | stmt :: rest => do
        let (next, effect) ← execStmtInMap fuel state stmt
        match effect with
        | .normal => execProgramInMap fuel next rest
        | other => .ok (next, other)
end

/-- The results agree: the same error, or the same effect and a state for the same list. -/
private def SameResult : Except String (MapEnv × Effect) → Except String (State × Effect) → Prop
  | .error left, .error right => left = right
  | .ok left, .ok right => left.1.Rel right.1.env ∧ left.2 = right.2
  | _, _ => False

private theorem evalInMap_rel {state : MapEnv} {env : Env} (h : state.Rel env) (exp : Exp) :
    evalInMap state.map [] exp = evalExp env exp :=
  evalInMap_eq _ _ _ _ h.lookup

private theorem exec_same (fuel : Nat) :
    (∀ (state : MapEnv) (env : Env) (stmt : Stmt), state.Rel env →
      SameResult (execStmtInMap fuel state stmt) (execStmt fuel { env := env } stmt)) ∧
    (∀ (state : MapEnv) (env : Env) (program : Program), state.Rel env →
      SameResult (execProgramInMap fuel state program) (execProgram fuel { env := env } program)) := by
  induction fuel with
  | zero =>
    constructor <;> intros <;> simp [execStmtInMap, execStmt, execProgramInMap, execProgram, SameResult]
  | succ fuel ih =>
    obtain ⟨ihs, ihp⟩ := ih
    constructor
    · intro state env stmt h
      cases stmt with
      | move var value =>
        simp only [execStmtInMap, execStmt, execExp, evalInMap_rel h, Bind.bind, Except.bind]
        cases evalExp env value with
        | error => rfl
        | ok value => exact ⟨h.bind var value, rfl⟩
      | jmp target =>
        simp only [execStmtInMap, execStmt, execExp, evalInMap_rel h, Bind.bind, Except.bind]
        cases evalExp env target with
        | error => rfl
        | ok value =>
          dsimp only
          cases Value.asBits value with
          | error => rfl
          | ok bits => exact ⟨h, rfl⟩
      | special message => exact ⟨h, rfl⟩
      | cpuExn number => exact ⟨h, rfl⟩
      | ifElse condition yes no =>
        simp only [execStmtInMap, execStmt, execExp, evalInMap_rel h, Bind.bind, Except.bind]
        cases evalExp env condition with
        | error => rfl
        | ok value =>
          dsimp only
          cases Value.asBits value with
          | error => rfl
          | ok bits =>
            obtain ⟨width, bits⟩ := bits
            dsimp only
            split
            · exact ihp _ _ _ h
            · rfl
      | «while» condition body =>
        simp only [execStmtInMap, execStmt, execExp, evalInMap_rel h, Bind.bind, Except.bind]
        cases evalExp env condition with
        | error => rfl
        | ok value =>
          dsimp only
          cases Value.asBits value with
          | error => rfl
          | ok bits =>
            obtain ⟨width, bits⟩ := bits
            dsimp only
            split
            · split
              · have hp := ihp state env body h
                cases hl : execProgramInMap fuel state body with
                | error left =>
                  rw [hl] at hp
                  cases hr : execProgram fuel { env := env } body with
                  | error right =>
                    rw [hr] at hp
                    exact hp
                  | ok right =>
                    rw [hr] at hp
                    exact hp.elim
                | ok left =>
                  rw [hl] at hp
                  cases hr : execProgram fuel { env := env } body with
                  | error right =>
                    rw [hr] at hp
                    exact hp.elim
                  | ok right =>
                    rw [hr] at hp
                    obtain ⟨hrel, heff⟩ := hp
                    obtain ⟨next, effect⟩ := left
                    obtain ⟨final, effect'⟩ := right
                    dsimp only at hrel heff
                    subst heff
                    cases effect with
                    | normal => exact ihs _ _ _ hrel
                    | _ => exact ⟨hrel, rfl⟩
              · exact ⟨h, rfl⟩
            · rfl
    · intro state env program h
      cases program with
      | nil => exact ⟨h, rfl⟩
      | cons stmt rest =>
        simp only [execProgramInMap, execProgram, Bind.bind, Except.bind]
        have hs := ihs state env stmt h
        cases hl : execStmtInMap fuel state stmt with
        | error left =>
          rw [hl] at hs
          cases hr : execStmt fuel { env := env } stmt with
          | error right =>
            rw [hr] at hs
            exact hs
          | ok right =>
            rw [hr] at hs
            exact hs.elim
        | ok left =>
          rw [hl] at hs
          cases hr : execStmt fuel { env := env } stmt with
          | error right =>
            rw [hr] at hs
            exact hs.elim
          | ok right =>
            rw [hr] at hs
            obtain ⟨hrel, heff⟩ := hs
            obtain ⟨next, effect⟩ := left
            obtain ⟨final, effect'⟩ := right
            dsimp only at hrel heff
            subst heff
            cases effect with
            | normal => exact ihp _ _ _ hrel
            | _ => exact ⟨hrel, rfl⟩

/-- Statements for a map to pay off: setting it up costs as much per variable as a statement does looking through the
list, around ten statements' worth of a pass over it. A loop can run any number of them. -/
private def worthMap (program : Program) : Bool :=
  (program.drop 15 |>.isEmpty |> not) || program.any fun
    | .while _ _ => true
    | _ => false

/-- `execProgram`: on a map unless there is little to run. The call to `execProgram` here is to its list code, as this
function is compiled before the `csimp` theorem. -/
private def execProgramFast (fuel : Nat) (state : State) (program : Program) : Except String (State × Effect) :=
  if !worthMap program then
    execProgram fuel state program
  else
    match execProgramInMap fuel (MapEnv.ofEnv state.env) program with
    | .error error => .error error
    | .ok (final, effect) => .ok ({ env := final.toEnvFast }, effect)

@[csimp] private theorem execProgram_eq_fast : @execProgram = @execProgramFast := by
  funext fuel state program
  rw [execProgramFast]
  split
  · rfl
  · obtain ⟨env⟩ := state
    have hs := (exec_same fuel).2 _ env program (MapEnv.rel_ofEnv env)
    cases hl : execProgramInMap fuel (MapEnv.ofEnv env) program with
    | error left =>
      rw [hl] at hs
      cases hr : execProgram fuel { env := env } program with
      | error right =>
        rw [hr] at hs
        simpa using hs.symm
      | ok right =>
        rw [hr] at hs
        exact hs.elim
    | ok left =>
      rw [hl] at hs
      cases hr : execProgram fuel { env := env } program with
      | error right =>
        rw [hr] at hs
        exact hs.elim
      | ok right =>
        rw [hr] at hs
        obtain ⟨hrel, heff⟩ := hs
        obtain ⟨next, effect⟩ := left
        obtain ⟨⟨final⟩, effect'⟩ := right
        dsimp only at hrel heff ⊢
        subst heff
        rw [MapEnv.toEnvFast_eq, hrel.list]

end Fast

def run (program : Program) (initial : State := {}) (fuel : Nat := 100000) :
    Except String (State × Effect) :=
  execProgram fuel initial program

end Bap.Bil
