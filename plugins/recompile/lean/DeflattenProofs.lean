import Lean

namespace Deflatten

inductive Exp : Nat -> Type where
  | var (id : Nat) (w : Nat) : Exp w
  | int (w : Nat) (value : BitVec w) : Exp w
  | neg {w : Nat} : Exp w -> Exp w
  | not {w : Nat} : Exp w -> Exp w
  | add {w : Nat} : Exp w -> Exp w -> Exp w
  | sub {w : Nat} : Exp w -> Exp w -> Exp w
  | mul {w : Nat} : Exp w -> Exp w -> Exp w
  | udiv {w : Nat} : Exp w -> Exp w -> Exp w
  | sdiv {w : Nat} : Exp w -> Exp w -> Exp w
  | urem {w : Nat} : Exp w -> Exp w -> Exp w
  | srem {w : Nat} : Exp w -> Exp w -> Exp w
  | shiftLeft {w n : Nat} : Exp w -> Exp n -> Exp w
  | ushiftRight {w n : Nat} : Exp w -> Exp n -> Exp w
  | sshiftRight {w n : Nat} : Exp w -> Exp n -> Exp w
  | and {w : Nat} : Exp w -> Exp w -> Exp w
  | or {w : Nat} : Exp w -> Exp w -> Exp w
  | xor {w : Nat} : Exp w -> Exp w -> Exp w
  | eq {w : Nat} : Exp w -> Exp w -> Exp 1
  | neq {w : Nat} : Exp w -> Exp w -> Exp 1
  | ult {w : Nat} : Exp w -> Exp w -> Exp 1
  | ule {w : Nat} : Exp w -> Exp w -> Exp 1
  | slt {w : Nat} : Exp w -> Exp w -> Exp 1
  | sle {w : Nat} : Exp w -> Exp w -> Exp 1
  | zeroExtend (target : Nat) {w : Nat} : Exp w -> Exp target
  | signExtend (target : Nat) {w : Nat} : Exp w -> Exp target
  | extract (hi lo : Nat) {w : Nat} : Exp w -> Exp (hi - lo + 1)
  | concat {w n : Nat} : Exp w -> Exp n -> Exp (w + n)
  | ite {w : Nat} : Exp 1 -> Exp w -> Exp w -> Exp w

abbrev Env := Nat -> (w : Nat) -> BitVec w

def Env.empty : Env := fun _ w => BitVec.ofNat w 0

def Env.set (env : Env) (id : Nat) {w : Nat} (value : BitVec w) : Env :=
  fun id' w' =>
    if h : id' = id ∧ w' = w then
      h.2 ▸ value
    else
      env id' w'

def eval (env : Env) : {w : Nat} -> Exp w -> BitVec w
  | _, .var id _ => env id _
  | _, .int _ value => value
  | _, .neg x => -eval env x
  | _, .not x => ~~~eval env x
  | _, .add x y => eval env x + eval env y
  | _, .sub x y => eval env x - eval env y
  | _, .mul x y => eval env x * eval env y
  | _, .udiv x y => eval env x / eval env y
  | _, .sdiv x y => BitVec.sdiv (eval env x) (eval env y)
  | _, .urem x y => eval env x % eval env y
  | _, .srem x y => BitVec.srem (eval env x) (eval env y)
  | _, .shiftLeft x y => BitVec.shiftLeft (eval env x) (BitVec.toNat (eval env y))
  | _, .ushiftRight x y => BitVec.ushiftRight (eval env x) (BitVec.toNat (eval env y))
  | _, .sshiftRight x y => BitVec.sshiftRight (eval env x) (BitVec.toNat (eval env y))
  | _, .and x y => eval env x &&& eval env y
  | _, .or x y => eval env x ||| eval env y
  | _, .xor x y => eval env x ^^^ eval env y
  | _, .eq x y => BitVec.ofBool (eval env x == eval env y)
  | _, .neq x y => BitVec.ofBool (eval env x != eval env y)
  | _, .ult x y => BitVec.ofBool (BitVec.ult (eval env x) (eval env y))
  | _, .ule x y => BitVec.ofBool (BitVec.ule (eval env x) (eval env y))
  | _, .slt x y => BitVec.ofBool (BitVec.slt (eval env x) (eval env y))
  | _, .sle x y => BitVec.ofBool (BitVec.sle (eval env x) (eval env y))
  | _, .zeroExtend target x => BitVec.zeroExtend target (eval env x)
  | _, .signExtend target x => BitVec.signExtend target (eval env x)
  | _, .extract hi lo x => BitVec.extractLsb hi lo (eval env x)
  | _, .concat x y => eval env x ++ eval env y
  | _, .ite c yes no => if eval env c = 1#1 then eval env yes else eval env no

structure Phi where
  width : Nat
  lhs : Nat
  inputs : List (Nat × Exp width)

structure Item where
  width : Nat
  lhs : Nat
  rhs : Exp width

inductive Terminator where
  | br (target : Nat)
  | cbr (cond : Exp 1) (yes no : Nat)
  | switch {w : Nat} (value : Exp w) (cases : List (BitVec w × Nat)) (default : Nat)
  | ret
  | unreachable

structure Block where
  label : Nat
  phis : List Phi
  items : List Item
  effect : Bool
  terminator : Terminator

structure Value where
  width : Nat
  lhs : Nat
  value : BitVec width

def applyValues (env : Env) (values : List Value) : Env :=
  values.foldl (fun env value => Env.set env value.lhs value.value) env

def evalPhis (env : Env) (pred : Nat) (phis : List Phi) : List Value :=
  phis.filterMap fun phi =>
    match phi.inputs.find? (fun input => input.1 = pred) with
    | none => none
    | some input => some {
        width := phi.width
        lhs := phi.lhs
        value := eval env input.2
      }

def evalItems (env : Env) (items : List Item) : Env :=
  items.foldl (fun env item => Env.set env item.lhs (eval env item.rhs)) env

def selectCase {w : Nat} (value : BitVec w) (cases : List (BitVec w × Nat)) (default : Nat) : Nat :=
  match cases.find? (fun entry => entry.1 = value) with
  | none => default
  | some entry => entry.2

def run (blocks : List Block) (fuel : Nat) (label pred : Nat) (env : Env) : Option (Nat × Env) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match blocks.find? (fun block => block.label = label) with
    | none => none
    | some block =>
      if block.effect then
        some (label, env)
      else
        let env' := applyValues env (evalPhis env pred block.phis)
        let env' := evalItems env' block.items
        match block.terminator with
        | .br target => run blocks fuel target block.label env'
        | .cbr cond yes no =>
          let next := if eval env' cond = 1#1 then yes else no
          run blocks fuel next block.label env'
        | .switch value cases default =>
          let next := selectCase (eval env' value) cases default
          run blocks fuel next block.label env'
        | .ret | .unreachable => some (label, env')

theorem run_ite (blocks : List Block) (fuel label pred : Nat) (env : Env)
    (state : Nat) {w : Nat} (cond : Exp 1) (yes no : Exp w) :
    run blocks fuel label pred (Env.set env state (eval env (Exp.ite cond yes no))) =
      if eval env cond = 1#1 then
        run blocks fuel label pred (Env.set env state (eval env yes))
      else
        run blocks fuel label pred (Env.set env state (eval env no)) := by
  by_cases h : eval env cond = 1#1 <;> simp [h, eval]

def outcomeLabel (outcome : Option (Nat × Env)) : Option Nat :=
  outcome.map Prod.fst

def outcomeVar (outcome : Option (Nat × Env)) (id : Nat) {w : Nat} : Option (BitVec w) :=
  outcome.map fun pair => pair.2 id w

example (env : Env) : (Env.set env 1 (42#32)) 1 32 = 42#32 := by rfl
example (env : Env) : (Env.set env 1 (42#32)) 2 32 = env 2 32 := by rfl

end Deflatten
