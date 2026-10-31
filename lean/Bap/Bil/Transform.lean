import Bap.Bil.Eval
import Bap.Core.Assoc

namespace Bap.Bil

private def union (left right : List Bap.Var) : List Bap.Var := (left ++ right).eraseDups

private def freeVarsExp (bound : List Bap.Var) : Exp → List Bap.Var
  | .int _ | .unknown _ _ => []
  | .var var => if var ∈ bound then [] else [var]
  | .load memory address _ _ => union (freeVarsExp bound memory) (freeVarsExp bound address)
  | .store memory address value _ _ =>
    union (union (freeVarsExp bound memory) (freeVarsExp bound address)) (freeVarsExp bound value)
  | .bin _ left right | .concat left right => union (freeVarsExp bound left) (freeVarsExp bound right)
  | .un _ value | .cast _ _ value | .extract _ _ value => freeVarsExp bound value
  | .letIn var value body =>
    union (freeVarsExp bound value) (freeVarsExp (var :: bound) body)
  | .ite condition yes no =>
    union (union (freeVarsExp bound condition) (freeVarsExp bound yes)) (freeVarsExp bound no)

def freeVars (exp : Exp) : List Bap.Var := freeVarsExp [] exp

/-- `freeVars` membership, without building the list. -/
def occursFree (target : Bap.Var) : Exp → Bool
  | .int _ | .unknown _ _ => false
  | .var var => var == target
  | .load memory address _ _ => occursFree target memory || occursFree target address
  | .store memory address value _ _ =>
    occursFree target memory || occursFree target address || occursFree target value
  | .bin _ left right | .concat left right => occursFree target left || occursFree target right
  | .un _ value | .cast _ _ value | .extract _ _ value => occursFree target value
  | .letIn var value body =>
    occursFree target value || (var != target && occursFree target body)
  | .ite condition yes no =>
    occursFree target condition || occursFree target yes || occursFree target no

/-- A version of `var` whose index exceeds that of every variable in `avoid`. -/
def freshVersion (var : Bap.Var) (avoid : List Bap.Var) : Bap.Var :=
  var.version (avoid.foldl (fun index other => max index (other.index + 1)) (var.index + 1))

/-- Simultaneous capture-avoiding substitution. A `let` is renamed, to a fresh version of its
variable, only if it would capture a free variable of a replacement that its body uses, so on
every other input this matches the reference `Exp.substitute`, which never renames. -/
def substitute (replacements : List (Bap.Var × Exp)) : Exp → Exp
  | .int value => .int value
  | .var var => (Assoc.get var replacements).getD (.var var)
  | .load memory address endian size =>
    .load (substitute replacements memory) (substitute replacements address) endian size
  | .store memory address value endian size =>
    .store (substitute replacements memory) (substitute replacements address)
      (substitute replacements value) endian size
  | .bin op left right => .bin op (substitute replacements left) (substitute replacements right)
  | .un op value => .un op (substitute replacements value)
  | .cast kind width value => .cast kind width (substitute replacements value)
  | .letIn var value body =>
    let inner := replacements.filter fun replacement => replacement.1 != var
    if inner.any fun replacement => occursFree var replacement.2 && occursFree replacement.1 body then
      let fresh := freshVersion var (inner.flatMap (freeVars ·.2) ++ freeVars body)
      .letIn fresh (substitute replacements value) (substitute ((var, .var fresh) :: inner) body)
    else
      .letIn var (substitute replacements value) (substitute inner body)
  | .ite condition yes no =>
    .ite (substitute replacements condition) (substitute replacements yes) (substitute replacements no)
  | .extract high low value => .extract high low (substitute replacements value)
  | .concat left right => .concat (substitute replacements left) (substitute replacements right)
  | .unknown message typ => .unknown message typ

def foldExp (exp : Exp) : Exp :=
  match evalExp [] exp with
  | .ok (.bits value) => .int value
  | _ =>
    match exp with
    | .int _ | .var _ | .unknown _ _ => exp
    | .load memory address endian size => .load (foldExp memory) (foldExp address) endian size
    | .store memory address value endian size =>
      .store (foldExp memory) (foldExp address) (foldExp value) endian size
    | .bin op left right => .bin op (foldExp left) (foldExp right)
    | .un op value => .un op (foldExp value)
    | .cast kind width value => .cast kind width (foldExp value)
    | .letIn var value body => .letIn var (foldExp value) (foldExp body)
    | .ite condition yes no => .ite (foldExp condition) (foldExp yes) (foldExp no)
    | .extract high low value => .extract high low (foldExp value)
    | .concat left right => .concat (foldExp left) (foldExp right)

/-- `exp` is well typed at exactly this bitvector width. -/
def hasImmWidth (exp : Exp) (width : Nat) : Bool :=
  match inferExp exp with
  | .ok (.imm actual) => actual == width
  | _ => false

def hasUnknown : Exp → Bool
  | .int _ | .var _ => false
  | .unknown _ _ => true
  | .load memory address _ _ | .bin _ memory address | .concat memory address =>
    hasUnknown memory || hasUnknown address
  | .store memory address value _ _ | .ite memory address value =>
    hasUnknown memory || hasUnknown address || hasUnknown value
  | .un _ value | .cast _ _ value | .extract _ _ value => hasUnknown value
  | .letIn _ value body => hasUnknown value || hasUnknown body

/-- Identity and annihilator rules, as in the reference `Exp.simpl`, but only where the dropped
operation could not have failed: an identity must keep the literal's width and an annihilator
must discard an expression that is sure to evaluate once its variables are bound. -/
def simplifyExp (exp : Exp) : Exp :=
  match evalExp [] exp with
  | .ok (.bits value) => .int value
  | _ =>
    match exp with
    | .int _ | .var _ | .unknown _ _ => exp
    | .load memory address endian size => .load (simplifyExp memory) (simplifyExp address) endian size
    | .store memory address value endian size =>
      .store (simplifyExp memory) (simplifyExp address) (simplifyExp value) endian size
    | .bin op left right =>
      let left := simplifyExp left
      let right := simplifyExp right
      match op, left, right with
      | .add, @Exp.int width zero, _ =>
        if zero = 0 ∧ hasImmWidth right width then right else .bin op left right
      | .add, _, @Exp.int width zero =>
        if zero = 0 ∧ hasImmWidth left width then left else .bin op left right
      | .sub, _, @Exp.int width zero =>
        if zero = 0 ∧ hasImmWidth left width then left else .bin op left right
      | .mul, @Exp.int width one, _ =>
        if !hasImmWidth right width then .bin op left right
        else if one = 1 then right
        else if one = 0 ∧ !hasUnknown right then left
        else .bin op left right
      | .mul, _, @Exp.int width one =>
        if !hasImmWidth left width then .bin op left right
        else if one = 1 then left
        else if one = 0 ∧ !hasUnknown left then right
        else .bin op left right
      | _, _, _ => .bin op left right
    | .un op value => .un op (simplifyExp value)
    | .cast kind width value => .cast kind width (simplifyExp value)
    | .letIn var value body => .letIn var (simplifyExp value) (simplifyExp body)
    | .ite condition yes no =>
      let condition := simplifyExp condition
      let yes := simplifyExp yes
      let no := simplifyExp no
      match condition with
      | @Exp.int 1 value => if value = 1 then yes else no
      | _ => .ite condition yes no
    | .extract high low value => .extract high low (simplifyExp value)
    | .concat left right => .concat (simplifyExp left) (simplifyExp right)

/-! `simplifyExp` evaluates each node, so all of an expression for each node of it: most have a variable in them that makes that fail. -/

/-- Evaluating without variables fails for sure: what is evaluated first of it cannot be evaluated. -/
private def stuck : Exp → Bool
  | .int _ => false
  | .var _ | .unknown _ _ => true
  | .load memory address _ _ => stuck memory || stuck address
  | .store memory address value _ _ => stuck memory || stuck address || stuck value
  | .bin _ left right | .concat left right => stuck left || stuck right
  | .un _ value | .cast _ _ value | .extract _ _ value => stuck value
  | .letIn _ value _ => stuck value
  | .ite condition _ _ => stuck condition

private theorem fails_left {α β : Type} {x : Except String α} {f : α → Except String β} (h : ∃ m, x = .error m) :
    ∃ m, (x >>= f) = .error m := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨m, rfl⟩

private theorem fails_right {α β : Type} (x : Except String α) {f : α → Except String β} (h : ∀ a, ∃ m, f a = .error m) :
    ∃ m, (x >>= f) = .error m := by
  cases x with
  | error e => exact ⟨e, rfl⟩
  | ok a => exact h a

private theorem eval_of_stuck {exp : Exp} (h : stuck exp = true) : ∃ message, evalExp [] exp = .error message := by
  induction exp with
  | int value => simp [stuck] at h
  | var var => exact ⟨_, rfl⟩
  | unknown message typ => exact ⟨_, rfl⟩
  | load m a e s ihm iha =>
    simp only [stuck, Bool.or_eq_true] at h
    simp only [evalExp]
    rcases h with h | h
    · exact fails_left (ihm h)
    · refine fails_right _ fun _ => fails_right _ fun p => ?_
      cases p
      exact fails_left (iha h)
  | store m a v e s ihm iha ihv =>
    simp only [stuck, Bool.or_eq_true] at h
    simp only [evalExp]
    rcases h with (h | h) | h
    · exact fails_left (ihm h)
    · refine fails_right _ fun _ => fails_right _ fun p => ?_
      cases p
      exact fails_left (iha h)
    · refine fails_right _ fun _ => fails_right _ fun p => ?_
      cases p
      refine fails_right _ fun _ => fails_right _ fun p => ?_
      cases p
      exact fails_left (ihv h)
  | bin op l r ihl ihr =>
    simp only [stuck, Bool.or_eq_true] at h
    simp only [evalExp]
    rcases h with h | h
    · exact fails_left (ihl h)
    · exact fails_right _ fun _ => fails_right _ fun _ => fails_left (ihr h)
  | concat l r ihl ihr =>
    simp only [stuck, Bool.or_eq_true] at h
    simp only [evalExp]
    rcases h with h | h
    · exact fails_left (ihl h)
    · exact fails_right _ fun _ => fails_right _ fun _ => fails_left (ihr h)
  | un op v ih => exact fails_left (ih h)
  | cast k w v ih => exact fails_left (ih h)
  | extract hi lo v ih => exact fails_left (ih h)
  | letIn var value body ihv _ => exact fails_left (ihv h)
  | ite c y n ihc _ _ => exact fails_left (ihc h)

/-- The rules of `simplifyExp` for what comes out of an operator. -/
private def binRule (op : BinOp) (left right : Exp) : Exp :=
  match op, left, right with
  | .add, @Exp.int width zero, _ =>
    if zero = 0 ∧ hasImmWidth right width then right else .bin op left right
  | .add, _, @Exp.int width zero =>
    if zero = 0 ∧ hasImmWidth left width then left else .bin op left right
  | .sub, _, @Exp.int width zero =>
    if zero = 0 ∧ hasImmWidth left width then left else .bin op left right
  | .mul, @Exp.int width one, _ =>
    if !hasImmWidth right width then .bin op left right
    else if one = 1 then right
    else if one = 0 ∧ !hasUnknown right then left
    else .bin op left right
  | .mul, _, @Exp.int width one =>
    if !hasImmWidth left width then .bin op left right
    else if one = 1 then left
    else if one = 0 ∧ !hasUnknown left then right
    else .bin op left right
  | _, _, _ => .bin op left right

private def iteRule (condition yes no : Exp) : Exp :=
  match condition with
  | @Exp.int 1 value => if value = 1 then yes else no
  | _ => .ite condition yes no

/-- `simplifyExp`, and whether it is `stuck`. -/
private def simplifyFast : Exp → Exp × Bool
  | .int value => (.int value, false)
  | .var var => (.var var, true)
  | .unknown message typ => (.unknown message typ, true)
  | .load memory address endian size =>
    let a := simplifyFast memory
    let b := simplifyFast address
    if a.2 || b.2 then (.load a.1 b.1 endian size, true)
    else
      match evalExp [] (.load memory address endian size) with
      | .ok (.bits value) => (.int value, false)
      | _ => (.load a.1 b.1 endian size, false)
  | .store memory address value endian size =>
    let a := simplifyFast memory
    let b := simplifyFast address
    let c := simplifyFast value
    if a.2 || b.2 || c.2 then (.store a.1 b.1 c.1 endian size, true)
    else
      match evalExp [] (.store memory address value endian size) with
      | .ok (.bits value) => (.int value, false)
      | _ => (.store a.1 b.1 c.1 endian size, false)
  | .bin op left right =>
    let a := simplifyFast left
    let b := simplifyFast right
    if a.2 || b.2 then (binRule op a.1 b.1, true)
    else
      match evalExp [] (.bin op left right) with
      | .ok (.bits value) => (.int value, false)
      | _ => (binRule op a.1 b.1, false)
  | .un op value =>
    let a := simplifyFast value
    if a.2 then (.un op a.1, true)
    else
      match evalExp [] (.un op value) with
      | .ok (.bits result) => (.int result, false)
      | _ => (.un op a.1, false)
  | .cast kind width value =>
    let a := simplifyFast value
    if a.2 then (.cast kind width a.1, true)
    else
      match evalExp [] (.cast kind width value) with
      | .ok (.bits result) => (.int result, false)
      | _ => (.cast kind width a.1, false)
  | .letIn var value body =>
    let a := simplifyFast value
    let b := simplifyFast body
    if a.2 then (.letIn var a.1 b.1, true)
    else
      match evalExp [] (.letIn var value body) with
      | .ok (.bits result) => (.int result, false)
      | _ => (.letIn var a.1 b.1, false)
  | .ite condition yes no =>
    let a := simplifyFast condition
    let b := simplifyFast yes
    let c := simplifyFast no
    if a.2 then (iteRule a.1 b.1 c.1, true)
    else
      match evalExp [] (.ite condition yes no) with
      | .ok (.bits result) => (.int result, false)
      | _ => (iteRule a.1 b.1 c.1, false)
  | .extract high low value =>
    let a := simplifyFast value
    if a.2 then (.extract high low a.1, true)
    else
      match evalExp [] (.extract high low value) with
      | .ok (.bits result) => (.int result, false)
      | _ => (.extract high low a.1, false)
  | .concat left right =>
    let a := simplifyFast left
    let b := simplifyFast right
    if a.2 || b.2 then (.concat a.1 b.1, true)
    else
      match evalExp [] (.concat left right) with
      | .ok (.bits result) => (.int result, false)
      | _ => (.concat a.1 b.1, false)

private theorem simplifyExp_of_not_bits {exp : Exp} (h : ∀ width (value : BitVec width), evalExp [] exp ≠ .ok (.bits value)) :
    simplifyExp exp =
      match exp with
      | .int _ | .var _ | .unknown _ _ => exp
      | .load memory address endian size => .load (simplifyExp memory) (simplifyExp address) endian size
      | .store memory address value endian size =>
        .store (simplifyExp memory) (simplifyExp address) (simplifyExp value) endian size
      | .bin op left right => binRule op (simplifyExp left) (simplifyExp right)
      | .un op value => .un op (simplifyExp value)
      | .cast kind width value => .cast kind width (simplifyExp value)
      | .letIn var value body => .letIn var (simplifyExp value) (simplifyExp body)
      | .ite condition yes no => iteRule (simplifyExp condition) (simplifyExp yes) (simplifyExp no)
      | .extract high low value => .extract high low (simplifyExp value)
      | .concat left right => .concat (simplifyExp left) (simplifyExp right) := by
  rw [simplifyExp.eq_def]
  split
  · rename_i hv
    exact (h _ _ hv).elim
  · cases exp <;> rfl

private theorem simplifyFast_eq (exp : Exp) : simplifyFast exp = (simplifyExp exp, stuck exp) := by
  have hstuck : ∀ {e : Exp}, stuck e = true → ∀ width (value : BitVec width), evalExp [] e ≠ .ok (.bits value) := by
    intro e h width value hv
    obtain ⟨_, he⟩ := eval_of_stuck h
    rw [he] at hv
    cases hv
  have hnode : ∀ (e result : Exp), (∀ (hn : ∀ width (value : BitVec width), evalExp [] e ≠ .ok (.bits value)), result = simplifyExp e) →
      stuck e = false → (match evalExp [] e with
        | .ok (.bits value) => (Exp.int value, false)
        | _ => (result, false)) = (simplifyExp e, stuck e) := by
    intro e result hr hs
    rw [hs]
    split
    · rename_i hv
      rw [simplifyExp.eq_def, hv]
    · rename_i hv
      rw [hr]
      intro w v heq
      exact hv _ _ heq
  induction exp with
  | int value => simp [simplifyFast, simplifyExp, evalExp, stuck]
  | var var => simp [simplifyFast, simplifyExp_of_not_bits (hstuck (e := .var var) rfl), stuck]
  | unknown m t => simp [simplifyFast, simplifyExp_of_not_bits (hstuck (e := .unknown m t) rfl), stuck]
  | load m a e s ihm iha =>
    simp only [simplifyFast, ihm, iha]
    by_cases hc : (stuck m || stuck a) = true
    · have hs : stuck (.load m a e s) = true := hc
      simp only [hc, ↓reduceIte, simplifyExp_of_not_bits (hstuck hs), hs]
    · have hs : stuck (.load m a e s) = false := Bool.eq_false_iff.2 hc
      simp only [hc]
      exact hnode (.load m a e s) _ (fun hn => (simplifyExp_of_not_bits hn).symm) hs
  | store m a v e s ihm iha ihv =>
    simp only [simplifyFast, ihm, iha, ihv]
    by_cases hc : (stuck m || stuck a || stuck v) = true
    · have hs : stuck (.store m a v e s) = true := hc
      simp only [hc, ↓reduceIte, simplifyExp_of_not_bits (hstuck hs), hs]
    · have hs : stuck (.store m a v e s) = false := Bool.eq_false_iff.2 hc
      simp only [hc]
      exact hnode (.store m a v e s) _ (fun hn => (simplifyExp_of_not_bits hn).symm) hs
  | bin op l r ihl ihr =>
    simp only [simplifyFast, ihl, ihr]
    by_cases hc : (stuck l || stuck r) = true
    · have hs : stuck (.bin op l r) = true := hc
      simp only [hc, ↓reduceIte, simplifyExp_of_not_bits (hstuck hs), hs]
    · have hs : stuck (.bin op l r) = false := Bool.eq_false_iff.2 hc
      simp only [hc]
      exact hnode (.bin op l r) _ (fun hn => (simplifyExp_of_not_bits hn).symm) hs
  | concat l r ihl ihr =>
    simp only [simplifyFast, ihl, ihr]
    by_cases hc : (stuck l || stuck r) = true
    · have hs : stuck (.concat l r) = true := hc
      simp only [hc, ↓reduceIte, simplifyExp_of_not_bits (hstuck hs), hs]
    · have hs : stuck (.concat l r) = false := Bool.eq_false_iff.2 hc
      simp only [hc]
      exact hnode (.concat l r) _ (fun hn => (simplifyExp_of_not_bits hn).symm) hs
  | un op v ih =>
    simp only [simplifyFast, ih]
    by_cases hc : stuck v = true
    · have hs : stuck (.un op v) = true := hc
      simp only [hc, ↓reduceIte, simplifyExp_of_not_bits (hstuck hs), hs]
    · have hs : stuck (.un op v) = false := Bool.eq_false_iff.2 hc
      simp only [hc]
      exact hnode (.un op v) _ (fun hn => (simplifyExp_of_not_bits hn).symm) hs
  | cast k w v ih =>
    simp only [simplifyFast, ih]
    by_cases hc : stuck v = true
    · have hs : stuck (.cast k w v) = true := hc
      simp only [hc, ↓reduceIte, simplifyExp_of_not_bits (hstuck hs), hs]
    · have hs : stuck (.cast k w v) = false := Bool.eq_false_iff.2 hc
      simp only [hc]
      exact hnode (.cast k w v) _ (fun hn => (simplifyExp_of_not_bits hn).symm) hs
  | extract hi lo v ih =>
    simp only [simplifyFast, ih]
    by_cases hc : stuck v = true
    · have hs : stuck (.extract hi lo v) = true := hc
      simp only [hc, ↓reduceIte, simplifyExp_of_not_bits (hstuck hs), hs]
    · have hs : stuck (.extract hi lo v) = false := Bool.eq_false_iff.2 hc
      simp only [hc]
      exact hnode (.extract hi lo v) _ (fun hn => (simplifyExp_of_not_bits hn).symm) hs
  | letIn var value body ihv ihb =>
    simp only [simplifyFast, ihv, ihb]
    by_cases hc : stuck value = true
    · have hs : stuck (.letIn var value body) = true := hc
      simp only [hc, ↓reduceIte, simplifyExp_of_not_bits (hstuck hs), hs]
    · have hs : stuck (.letIn var value body) = false := Bool.eq_false_iff.2 hc
      simp only [hc]
      exact hnode (.letIn var value body) _ (fun hn => (simplifyExp_of_not_bits hn).symm) hs
  | ite c y n ihc ihy ihn =>
    simp only [simplifyFast, ihc, ihy, ihn]
    by_cases hc : stuck c = true
    · have hs : stuck (.ite c y n) = true := hc
      simp only [hc, ↓reduceIte, simplifyExp_of_not_bits (hstuck hs), hs]
    · have hs : stuck (.ite c y n) = false := Bool.eq_false_iff.2 hc
      simp only [hc]
      exact hnode (.ite c y n) _ (fun hn => (simplifyExp_of_not_bits hn).symm) hs

private def simplifyExpFast (exp : Exp) : Exp := (simplifyFast exp).1

@[csimp] private theorem simplifyExp_eq_fast : @simplifyExp = @simplifyExpFast :=
  funext fun exp => by rw [simplifyExpFast, simplifyFast_eq]

def foldStmt : Stmt → Stmt
  | .move var value => .move var (foldExp value)
  | .jmp target => .jmp (foldExp target)
  | .while condition body => .while (foldExp condition) (body.map foldStmt)
  | .ifElse condition yes no => .ifElse (foldExp condition) (yes.map foldStmt) (no.map foldStmt)
  | stmt => stmt

def foldProgram (program : Program) : Program := program.map foldStmt

/-! ### Temporaries nothing reads

The lifter gives the value of a conditional, and of what it freezes, a variable of its own, not knowing if anything will read it. -/

mutual
  /-- All the variables a statement reads, however it runs. -/
  def readsOfStmt : Stmt → List Bap.Var
    | .move _ value => freeVars value
    | .jmp target => freeVars target
    | .while condition body => freeVars condition ++ readsOfProgram body
    | .ifElse condition yes no => freeVars condition ++ readsOfProgram yes ++ readsOfProgram no
    | .special _ | .cpuExn _ => []

  def readsOfProgram : Program → List Bap.Var
    | [] => []
    | stmt :: rest => readsOfStmt stmt ++ readsOfProgram rest
end

mutual
  /-- A statement without the assignments to what is `dead`. An assignment is nothing then. -/
  def dropStmt (dead : Bap.Var → Bool) : Stmt → Option Stmt
    | .move var value => if dead var then none else some (.move var value)
    | .while condition body => some (.while condition (dropProgram dead body))
    | .ifElse condition yes no => some (.ifElse condition (dropProgram dead yes) (dropProgram dead no))
    | stmt => some stmt

  def dropProgram (dead : Bap.Var → Bool) : Program → Program
    | [] => []
    | stmt :: rest =>
      match dropStmt dead stmt with
      | some kept => kept :: dropProgram dead rest
      | none => dropProgram dead rest
end

/-- What the lifter names for itself: `freeze`, `let` and the value of a conditional. -/
def isTemporary (var : Bap.Var) : Bool := var.name.startsWith "_primus_"

mutual
  /-- The temporaries a statement assigns. -/
  def stmtTemporaries : Stmt → List Bap.Var
    | .move var _ => if isTemporary var then [var] else []
    | .while _ body => programTemporaries body
    | .ifElse _ yes no => programTemporaries yes ++ programTemporaries no
    | _ => []

  def programTemporaries : Program → List Bap.Var
    | [] => []
    | stmt :: rest => stmtTemporaries stmt ++ programTemporaries rest
end

/-- A temporary is dead if the program reads it nowhere. -/
def deadTemporary (reads : Std.HashSet Bap.Var) (var : Bap.Var) : Bool := isTemporary var && !reads.contains var

def dropDeadTempsAux : Nat → Program → Program
  | 0, program => program
  | fuel + 1, program =>
    let temporaries := programTemporaries program
    if temporaries.isEmpty then program else
    let reads := Std.HashSet.ofList (readsOfProgram program)
    if temporaries.any (deadTemporary reads) then dropDeadTempsAux fuel (dropProgram (deadTemporary reads) program)
    else program

/-- A program without the temporaries nothing reads: those that only such a temporary reads go with them. -/
def dropDeadTemps (program : Program) : Program := dropDeadTempsAux (programTemporaries program).length program

@[simp] theorem substitute_empty (exp : Exp) : substitute [] exp = exp := by
  induction exp <;> simp [substitute, *]

@[simp] theorem substitute_let_shadow (var : Bap.Var) (replacement value body : Exp) :
    substitute [(var, replacement)] (.letIn var value body) =
      .letIn var (substitute [(var, replacement)] value) body := by
  simp [substitute]

theorem foldExp_of_eval_bits {exp : Exp} {value : BitVec width}
    (h : evalExp [] exp = .ok (.bits value)) : foldExp exp = .int value := by
  unfold foldExp
  rw [h]

theorem simplifyExp_of_eval_bits {exp : Exp} {value : BitVec width}
    (h : evalExp [] exp = .ok (.bits value)) : simplifyExp exp = .int value := by
  unfold simplifyExp
  rw [h]

end Bap.Bil
