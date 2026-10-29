import Bap.Core.Sexp

namespace Bap.Symbolic

inductive Expr where
  | var (name : String) (width : Nat)
  | const {width : Nat} (value : BitVec width)
  | app (name : String) (width : Nat) (args : List Expr)
  | extract (high low : Nat) (value : Expr)
  | concat (left right : Expr)
  | ite (condition yes no : Expr)
  deriving Repr

namespace Expr

def width : Expr → Nat
  | .var _ width => width
  | @Expr.const width _ => width
  | .app _ width _ => width
  | .extract high low _ => high - low + 1
  | .concat left right => left.width + right.width
  | .ite _ yes _ => yes.width

private def sanitize (name : String) : String :=
  String.ofList (name.toList.map fun c => if c.isAlphanum || c = '_' then c else '_')

def name : Expr → String
  | .var name _ => sanitize name
  | _ => "tmp"

def render : Expr → String
  | .var name _ => sanitize name
  | @Expr.const width value => s!"(_ bv{value.toNat} {width})"
  | .app name _ args =>
    if args.isEmpty then name else "(" ++ String.intercalate " " (name :: args.map render) ++ ")"
  | .extract high low value => s!"((_ extract {high} {low}) {render value})"
  | .concat left right => s!"(concat {render left} {render right})"
  | .ite condition yes no => s!"(ite {render condition} {render yes} {render no})"

def structuralEq (left right : Expr) : Bool := Expr.render left = Expr.render right

def vars : Expr → List (String × Nat)
  | .var name width => [(sanitize name, width)]
  | .const _ => []
  | .app _ _ args => (args.flatMap vars).eraseDups
  | .extract _ _ value => vars value
  | .concat left right => (vars left ++ vars right).eraseDups
  | .ite condition yes no => (vars condition ++ vars yes ++ vars no).eraseDups

def bool (value : Bool) : Expr := .const (BitVec.ofNat 1 value.toNat)
def eqOne (value : Expr) : Expr :=
  if value.width = 1 then value else .app "=" 1 [value, .const (BitVec.ofNat value.width 1)]
def eqZero (value : Expr) : Expr :=
  if value.width = 1 then .app "not" 1 [value] else .app "=" 1 [value, .const (BitVec.ofNat value.width 0)]

end Expr

def renderScript (constraints : List Expr) : String :=
  let variables := (constraints.flatMap Expr.vars).eraseDups
  let declarations := variables.map fun (name, width) => s!"(declare-const {name} (_ BitVec {width}))"
  let assertions := constraints.map fun constraint => s!"(assert {constraint.render})"
  String.intercalate "\n" (["(set-logic QF_BV)"] ++ declarations ++ assertions ++ ["(check-sat)"])

end Bap.Symbolic
