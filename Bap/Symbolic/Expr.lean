import Bap.Core.Sexp
import Bap.Graph.Fast

namespace Bap.Symbolic

inductive Expr where
  | var (name : String) (width : Nat)
  | const {width : Nat} (value : BitVec width)
  | app (name : String) (width : Nat) (args : List Expr)
  | extract (high low : Nat) (value : Expr)
  | concat (left right : Expr)
  | ite (condition yes no : Expr)
  /-- A byte of the initial contents of a memory, an uninterpreted function of the address. -/
  | select (memory : String) (address : Expr)
  deriving Repr

namespace Expr

def width : Expr → Nat
  | .var _ width => width
  | @Expr.const width _ => width
  | .app _ width _ => width
  | .extract high low _ => high + 1 - low
  | .concat left right => left.width + right.width
  | .ite _ yes _ => yes.width
  | .select _ _ => 8

/-- Syntactic equality of expressions. -/
def structuralEq : Expr → Expr → Bool
  | .var name width, .var name' width' => name == name' && width == width'
  | @Expr.const width value, @Expr.const width' value' => width == width' && value.toNat == value'.toNat
  | .app name width args, .app name' width' args' =>
    name == name' && width == width' && structuralEqList args args'
  | .extract high low value, .extract high' low' value' =>
    high == high' && low == low' && structuralEq value value'
  | .concat left right, .concat left' right' => structuralEq left left' && structuralEq right right'
  | .ite condition yes no, .ite condition' yes' no' =>
    structuralEq condition condition' && structuralEq yes yes' && structuralEq no no'
  | .select memory address, .select memory' address' => memory == memory' && structuralEq address address'
  | _, _ => false
where
  structuralEqList : List Expr → List Expr → Bool
    | [], [] => true
    | left :: lefts, right :: rights => structuralEq left right && structuralEqList lefts rights
    | _, _ => false

mutual
  private theorem structuralEq_iff_eq : (left right : Expr) → structuralEq left right = true ↔ left = right
    | .var name width, .var name' width' => by simp [structuralEq]
    | @Expr.const width value, @Expr.const width' value' => by
      simp only [structuralEq, Bool.and_eq_true, beq_iff_eq, Expr.const.injEq]
      constructor
      · rintro ⟨rfl, h⟩
        exact ⟨rfl, heq_of_eq (BitVec.eq_of_toNat_eq h)⟩
      · rintro ⟨rfl, h⟩
        cases eq_of_heq h
        exact ⟨rfl, rfl⟩
    | .app name width args, .app name' width' args' => by
      simp only [structuralEq, Bool.and_eq_true, beq_iff_eq, Expr.app.injEq, structuralEqList_iff_eq args args',
        and_assoc]
    | .extract high low value, .extract high' low' value' => by
      simp only [structuralEq, Bool.and_eq_true, beq_iff_eq, Expr.extract.injEq,
        structuralEq_iff_eq value value', and_assoc]
    | .concat left right, .concat left' right' => by
      simp only [structuralEq, Bool.and_eq_true, Expr.concat.injEq, structuralEq_iff_eq left left',
        structuralEq_iff_eq right right']
    | .ite condition yes no, .ite condition' yes' no' => by
      simp only [structuralEq, Bool.and_eq_true, Expr.ite.injEq, structuralEq_iff_eq condition condition',
        structuralEq_iff_eq yes yes', structuralEq_iff_eq no no', and_assoc]
    | .select memory address, .select memory' address' => by
      simp only [structuralEq, Bool.and_eq_true, beq_iff_eq, Expr.select.injEq,
        structuralEq_iff_eq address address']
    | .var .., .const .. | .var .., .app .. | .var .., .extract .. | .var .., .concat .. | .var .., .ite ..
    | .var .., .select ..
    | .const .., .var .. | .const .., .app .. | .const .., .extract .. | .const .., .concat .. | .const .., .ite ..
    | .const .., .select ..
    | .app .., .var .. | .app .., .const .. | .app .., .extract .. | .app .., .concat .. | .app .., .ite ..
    | .app .., .select ..
    | .extract .., .var .. | .extract .., .const .. | .extract .., .app .. | .extract .., .concat ..
    | .extract .., .ite .. | .extract .., .select ..
    | .concat .., .var .. | .concat .., .const .. | .concat .., .app .. | .concat .., .extract ..
    | .concat .., .ite .. | .concat .., .select ..
    | .ite .., .var .. | .ite .., .const .. | .ite .., .app .. | .ite .., .extract .. | .ite .., .concat ..
    | .ite .., .select ..
    | .select .., .var .. | .select .., .const .. | .select .., .app .. | .select .., .extract ..
    | .select .., .concat .. | .select .., .ite .. => by simp [structuralEq]

  private theorem structuralEqList_iff_eq : (lefts rights : List Expr) →
      structuralEq.structuralEqList lefts rights = true ↔ lefts = rights
    | [], [] => by simp [structuralEq.structuralEqList]
    | [], _ :: _ => by simp [structuralEq.structuralEqList]
    | _ :: _, [] => by simp [structuralEq.structuralEqList]
    | left :: lefts, right :: rights => by
      simp only [structuralEq.structuralEqList, Bool.and_eq_true, List.cons.injEq,
        structuralEq_iff_eq left right, structuralEqList_iff_eq lefts rights]
end

/-- `structuralEq` decides equality of expressions. -/
instance : DecidableEq Expr := fun left right =>
  decidable_of_iff _ (structuralEq_iff_eq left right)

theorem eq_of_structuralEq {left right : Expr} : structuralEq left right = true ↔ left = right :=
  structuralEq_iff_eq left right

private def escapeChar (c : Char) : String :=
  if c.isAlphanum || c = '_' then c.toString else s!"${c.toNat}$"

/-- An injective spelling of a name in characters that are valid in any SMT-LIB symbol. -/
def escapeName (name : String) : String :=
  String.join (name.toList.map escapeChar)

/-- The SMT-LIB symbol of a bitvector variable, different for each name and width. -/
def variableSymbol (name : String) (width : Nat) : String :=
  s!"|{escapeName name}!{width}|"

/-- The SMT-LIB symbol of a memory's initial contents, different for each name and address width. -/
def memorySymbol (memory : String) (addressWidth : Nat) : String :=
  s!"|{escapeName memory}@{addressWidth}|"

def name : Expr → String
  | .var name width => variableSymbol name width
  | _ => "tmp"

/-- Operators whose SMT-LIB result sort is Bool, though their BIL result is one bit. -/
def isPredicate (name : String) : Bool :=
  ["=", "distinct", "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge"].contains name

/-- The SMT-LIB term of an expression, which always has a bitvector sort. -/
def render : Expr → String
  | .var name width => variableSymbol name width
  | @Expr.const width value => s!"(_ bv{value.toNat} {width})"
  | .app name _ args =>
    if args.isEmpty then name
    else
      let term := "(" ++ String.intercalate " " (name :: args.map render) ++ ")"
      if isPredicate name then s!"(ite {term} #b1 #b0)" else term
  | .extract high low value => s!"((_ extract {high} {low}) {render value})"
  | .concat left right => s!"(concat {render left} {render right})"
  | .ite condition yes no =>
    s!"(ite (= {render condition} #b1) {render yes} {render no})"
  | .select memory address => s!"({memorySymbol memory address.width} {render address})"

/-! `render` into one string: otherwise each level of a term copies what is under it. -/

mutual
  private def renderTo (acc : String) : Expr → String
    | .var name width => acc ++ variableSymbol name width
    | @Expr.const width value => acc ++ s!"(_ bv{value.toNat} {width})"
    | .app name _ args =>
      match args with
      | [] => acc ++ name
      | first :: rest =>
        let term := renderArgsTo (renderTo (acc ++ (if isPredicate name then "(ite (" else "(") ++ name ++ " ") first) rest
        term ++ (if isPredicate name then ") #b1 #b0)" else ")")
    | .extract high low value => renderTo (acc ++ s!"((_ extract {high} {low}) ") value |>.push ')'
    | .concat left right => (renderTo ((renderTo (acc ++ "(concat ") left).push ' ') right).push ')'
    | .ite condition yes no =>
      (renderTo ((renderTo (renderTo (acc ++ "(ite (= ") condition ++ " #b1) ") yes).push ' ') no).push ')'
    | .select memory address => (renderTo (acc ++ "(" ++ memorySymbol memory address.width ++ " ") address).push ')'

  /-- The arguments after the first one, each with its separator. -/
  private def renderArgsTo (acc : String) : List Expr → String
    | [] => acc
    | arg :: rest => renderArgsTo (renderTo (acc.push ' ') arg) rest
end

private theorem toString_self (value : String) : toString value = value := rfl

mutual
  private theorem renderTo_eq (acc : String) : (value : Expr) → renderTo acc value = acc ++ render value
    | .var _ _ => by rw [renderTo, render]
    | .const _ => by rw [renderTo, render]
    | .app name _ [] => by rw [renderTo, render]; simp
    | .app name _ (first :: rest) => by
      rw [renderTo, render]
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.map_cons]
      have hargs := renderArgsTo_eq (acc ++ (if isPredicate name then "(ite (" else "(") ++ name ++ " ") (render first) rest
      rw [renderTo_eq _ first, hargs, String.intercalate_cons_cons]
      apply String.toList_injective
      by_cases hp : isPredicate name = true <;> simp [hp, toString_self]
    | .extract high low value => by
      rw [renderTo, render, renderTo_eq]
      apply String.toList_injective
      simp [toString_self]
    | .concat left right => by
      rw [renderTo, render, renderTo_eq, renderTo_eq]
      apply String.toList_injective
      simp [toString_self]
    | .ite condition yes no => by
      rw [renderTo, render, renderTo_eq, renderTo_eq, renderTo_eq]
      apply String.toList_injective
      simp [toString_self]
    | .select memory address => by
      rw [renderTo, render, renderTo_eq]
      apply String.toList_injective
      simp [toString_self]

  private theorem renderArgsTo_eq (acc first : String) : (args : List Expr) →
      renderArgsTo (acc ++ first) args = acc ++ String.intercalate " " (first :: args.map render)
    | [] => by simp [renderArgsTo, String.intercalate_singleton]
    | arg :: rest => by
      have happ : (acc ++ first).push ' ' ++ render arg = acc ++ (first ++ " " ++ render arg) := by
        apply String.toList_injective
        simp
      rw [renderArgsTo, renderTo_eq _ arg, happ, renderArgsTo_eq acc _ rest, List.map_cons,
        String.intercalate_cons_cons, String.intercalate_cons_append]
end

private def renderFast (value : Expr) : String := renderTo "" value

@[csimp] private theorem render_eq_fast : @render = @renderFast := by
  funext value
  simp [renderFast, renderTo_eq]

/-- The SMT-LIB formula that an expression is true, for use as an assertion. -/
def renderFormula (value : Expr) : String :=
  match value with
  | .app name _ args =>
    if isPredicate name && !args.isEmpty then
      "(" ++ String.intercalate " " (name :: args.map render) ++ ")"
    else
      s!"(= {render value} {if value.width = 1 then "#b1" else s!"(_ bv1 {value.width})"})"
  | _ => s!"(= {render value} {if value.width = 1 then "#b1" else s!"(_ bv1 {value.width})"})"

def vars : Expr → List (String × Nat)
  | .var name width => [(name, width)]
  | .const _ => []
  | .app _ _ args => (args.flatMap vars).eraseDups
  | .extract _ _ value => vars value
  | .concat left right => (vars left ++ vars right).eraseDups
  | .ite condition yes no => (vars condition ++ vars yes ++ vars no).eraseDups
  | .select _ address => vars address

/-- The memories an expression reads, with their address widths. -/
def memories : Expr → List (String × Nat)
  | .var _ _ => []
  | .const _ => []
  | .app _ _ args => (args.flatMap memories).eraseDups
  | .extract _ _ value => memories value
  | .concat left right => (memories left ++ memories right).eraseDups
  | .ite condition yes no => (memories condition ++ memories yes ++ memories no).eraseDups
  | .select memory address => ((memory, address.width) :: memories address).eraseDups

def bool (value : Bool) : Expr := .const (BitVec.ofNat 1 value.toNat)
def eqOne (value : Expr) : Expr :=
  if value.width = 1 then value else .app "=" 1 [value, .const (BitVec.ofNat value.width 1)]
def eqZero (value : Expr) : Expr :=
  .app "=" 1 [value, .const (BitVec.ofNat value.width 0)]

end Expr

private def renderScriptFast (constraints : List Expr) : String :=
  let variables := Bap.Graph.Fast.dedup (constraints.flatMap Expr.vars)
  let memories := Bap.Graph.Fast.dedup (constraints.flatMap Expr.memories)
  let logic := if memories.isEmpty then "QF_BV" else "QF_UFBV"
  let functions := memories.map fun (name, width) =>
    s!"(declare-fun {Expr.memorySymbol name width} ((_ BitVec {width})) (_ BitVec 8))"
  let declarations := variables.map fun (name, width) =>
    s!"(declare-const {Expr.variableSymbol name width} (_ BitVec {width}))"
  let assertions := constraints.map fun constraint => s!"(assert {constraint.renderFormula})"
  String.intercalate "\n" ([s!"(set-logic {logic})"] ++ functions ++ declarations ++ assertions ++ ["(check-sat)"])

def renderScript (constraints : List Expr) : String :=
  let variables := (constraints.flatMap Expr.vars).eraseDups
  let memories := (constraints.flatMap Expr.memories).eraseDups
  let logic := if memories.isEmpty then "QF_BV" else "QF_UFBV"
  let functions := memories.map fun (name, width) =>
    s!"(declare-fun {Expr.memorySymbol name width} ((_ BitVec {width})) (_ BitVec 8))"
  let declarations := variables.map fun (name, width) =>
    s!"(declare-const {Expr.variableSymbol name width} (_ BitVec {width}))"
  let assertions := constraints.map fun constraint => s!"(assert {constraint.renderFormula})"
  String.intercalate "\n" ([s!"(set-logic {logic})"] ++ functions ++ declarations ++ assertions ++ ["(check-sat)"])

@[csimp] private theorem renderScript_eq_fast : @renderScript = @renderScriptFast := by
  funext constraints
  simp only [renderScript, renderScriptFast, Bap.Graph.Fast.dedup_eq]

end Bap.Symbolic
