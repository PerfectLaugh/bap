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

def foldStmt : Stmt → Stmt
  | .move var value => .move var (foldExp value)
  | .jmp target => .jmp (foldExp target)
  | .while condition body => .while (foldExp condition) (body.map foldStmt)
  | .ifElse condition yes no => .ifElse (foldExp condition) (yes.map foldStmt) (no.map foldStmt)
  | stmt => stmt

def foldProgram (program : Program) : Program := program.map foldStmt

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
