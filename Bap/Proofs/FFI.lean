import Lean.Elab.Command
import Std.Data.String.ToNat
import Bap.FFI.Z3

namespace Bap.Proofs.FFI

open Lean Elab Command in
/-- Bind short names to private declarations of an imported module (`open private` lives in Batteries). -/
local elab "open_private_decls " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

open Bap.Symbolic
open_private_decls Bap.Symbolic.Expr Bap.Symbolic.Expr escapeChar

/-! ### Foreign boundary

`checkSat` is an opaque extern, so nothing about solver answers can be proved here. These two laws
pin down the only logic on the Lean side: what is sent, and how the answer is read. -/

theorem isSat_sends_rendered_script (constraints : List Expr) :
    Bap.FFI.Z3.isSat constraints = Bap.FFI.Z3.checkSat (renderScript constraints) := rfl

theorem isUnsat_negates_isSat (constraints : List Expr) :
    Bap.FFI.Z3.isUnsat constraints = (Bap.FFI.Z3.isSat constraints >>= fun sat => pure (!sat)) := rfl

/-! ### Names

Every variable and memory has an SMT-LIB symbol of its own. -/

/-- The characters an escaped name is written in. -/
def SymbolChar (c : Char) : Prop := c.isAlphanum = true ∨ c = '_' ∨ c = '$'

private theorem toList_escapeChar (c : Char) :
    (escapeChar c).toList =
      if c.isAlphanum || c = '_' then [c] else '$' :: (Nat.toDigits 10 c.toNat ++ ['$']) := by
  unfold escapeChar
  split
  · simp
  · simp [String.toList_append, toString]

private theorem toList_escapeName (name : String) :
    (Expr.escapeName name).toList = name.toList.flatMap fun c => (escapeChar c).toList := by
  unfold Expr.escapeName
  generalize name.toList = chars
  induction chars with
  | nil => simp
  | cons c rest ih => simp [String.join_cons, String.toList_append, ih]

private theorem digit_not_dollar {n : Nat} {c : Char} (h : c ∈ Nat.toDigits 10 n) :
    c.isDigit = true := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

/-- Lists without a separator split uniquely around their first separator. -/
private theorem split_unique {sep : Char} {a b x y : List Char} (ha : sep ∉ a) (hb : sep ∉ b)
    (h : a ++ sep :: x = b ++ sep :: y) : a = b ∧ x = y := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa using h
    | cons d rest =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hb
  | cons e rest ih =>
    cases b with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1.symm ▸ List.mem_cons_self) ha
    | cons d rest' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := ih (fun m => ha (List.mem_cons_of_mem _ m))
        (fun m => hb (List.mem_cons_of_mem _ m)) h.2
      exact ⟨by rw [h.1, h1], h2⟩

private theorem dollar_not_digit {n : Nat} : '$' ∉ Nat.toDigits 10 n := fun h => by
  have := digit_not_dollar h
  revert this
  decide

private theorem escape_prefix_free {a b : Char} {x y : List Char}
    (h : (escapeChar a).toList ++ x = (escapeChar b).toList ++ y) : a = b ∧ x = y := by
  rw [toList_escapeChar, toList_escapeChar] at h
  have hdollar : ¬ (('$' : Char).isAlphanum || decide ('$' = '_')) = true := by decide
  by_cases ha : (a.isAlphanum || decide (a = '_')) = true <;>
    by_cases hb : (b.isAlphanum || decide (b = '_')) = true
  · simp only [ha, hb, ite_true, List.singleton_append, List.cons.injEq] at h
    exact h
  · simp only [ha, hb, ite_true, ite_false, Bool.false_eq_true, List.cons_append,
      List.cons.injEq] at h
    exact absurd (h.1 ▸ ha) hdollar
  · simp only [ha, hb, ite_true, ite_false, Bool.false_eq_true, List.cons_append,
      List.cons.injEq] at h
    exact absurd (h.1 ▸ hb) hdollar
  · simp only [ha, hb, ite_false, Bool.false_eq_true, List.cons_append, List.append_assoc, List.cons.injEq,
      true_and] at h
    obtain ⟨h1, h2⟩ := split_unique dollar_not_digit dollar_not_digit h
    have hrepr : Nat.repr a.toNat = Nat.repr b.toNat := String.toList_inj.mp (by simpa using h1)
    exact ⟨Char.toNat_inj.mp (Nat.repr_injective hrepr), h2⟩

/-- Escaping is injective, so different names never meet in the solver. -/
theorem escapeName_injective {left right : String} (h : Expr.escapeName left = Expr.escapeName right) :
    left = right := by
  apply String.toList_inj.mp
  have h' := congrArg String.toList h
  rw [toList_escapeName, toList_escapeName] at h'
  generalize left.toList = as at h'
  generalize right.toList = bs at h'
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => rfl
    | cons b rest =>
      simp only [List.flatMap_nil, List.flatMap_cons] at h'
      have hne : (escapeChar b).toList ≠ [] := by
        rw [toList_escapeChar]; split <;> simp
      simp only [List.nil_eq, List.append_eq_nil_iff] at h'
      exact absurd h'.1 hne
  | cons a rest ih =>
    cases bs with
    | nil =>
      simp only [List.flatMap_nil, List.flatMap_cons] at h'
      have hne : (escapeChar a).toList ≠ [] := by
        rw [toList_escapeChar]; split <;> simp
      simp only [List.append_eq_nil_iff] at h'
      exact absurd h'.1 hne
    | cons b rest' =>
      simp only [List.flatMap_cons] at h'
      obtain ⟨h1, h2⟩ := escape_prefix_free h'
      rw [h1, ih _ h2]

/-- What an escaped name is made of. -/
theorem symbolChar_escapeName {c : Char} {name : String} (h : c ∈ (Expr.escapeName name).toList) :
    SymbolChar c := by
  rw [toList_escapeName] at h
  obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp h
  rw [toList_escapeChar] at hd
  unfold SymbolChar
  split at hd
  · next hk =>
    rw [List.mem_singleton.mp hd]
    have : d.isAlphanum = true ∨ d = '_' := by simpa using hk
    rcases this with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · rcases List.mem_cons.mp hd with rfl | hd
    · simp
    · rcases List.mem_append.mp hd with hd | hd
      · have hdigit := digit_not_dollar hd
        refine .inl ?_
        simp [Char.isAlphanum, hdigit]
      · simp at hd
        simp [hd]

instance (c : Char) : Decidable (SymbolChar c) := by unfold SymbolChar; infer_instance

private theorem separator_not_escaped {sep : Char} (hsep : ¬ SymbolChar sep) (name : String) :
    sep ∉ (Expr.escapeName name).toList :=
  fun h => hsep (symbolChar_escapeName h)

private theorem toList_variableSymbol (name : String) (width : Nat) :
    (Expr.variableSymbol name width).toList =
      '|' :: ((Expr.escapeName name).toList ++ '!' :: (Nat.toDigits 10 width ++ ['|'])) := by
  simp [Expr.variableSymbol, String.toList_append, toString]

private theorem toList_memorySymbol (name : String) (width : Nat) :
    (Expr.memorySymbol name width).toList =
      '|' :: ((Expr.escapeName name).toList ++ '@' :: (Nat.toDigits 10 width ++ ['|'])) := by
  simp [Expr.memorySymbol, String.toList_append, toString]

/-- Variables have different symbols unless both the name and the width are the same, so there is
neither a merged variable nor a name declared at two widths. -/
theorem variableSymbol_injective {name name' : String} {width width' : Nat}
    (h : Expr.variableSymbol name width = Expr.variableSymbol name' width') : name = name' ∧ width = width' := by
  have h' := congrArg String.toList h
  rw [toList_variableSymbol, toList_variableSymbol] at h'
  simp only [List.cons.injEq, true_and] at h'
  obtain ⟨h1, h2⟩ := split_unique (separator_not_escaped (sep := '!') (by decide) name)
    (separator_not_escaped (sep := '!') (by decide) name') h'
  refine ⟨escapeName_injective (String.toList_inj.mp h1), ?_⟩
  have h3 := List.append_cancel_right h2
  exact Nat.repr_injective (String.toList_inj.mp (by simpa using h3))

theorem memorySymbol_injective {name name' : String} {width width' : Nat}
    (h : Expr.memorySymbol name width = Expr.memorySymbol name' width') : name = name' ∧ width = width' := by
  have h' := congrArg String.toList h
  rw [toList_memorySymbol, toList_memorySymbol] at h'
  simp only [List.cons.injEq, true_and] at h'
  obtain ⟨h1, h2⟩ := split_unique (separator_not_escaped (sep := '@') (by decide) name)
    (separator_not_escaped (sep := '@') (by decide) name') h'
  refine ⟨escapeName_injective (String.toList_inj.mp h1), ?_⟩
  have h3 := List.append_cancel_right h2
  exact Nat.repr_injective (String.toList_inj.mp (by simpa using h3))

/-- A memory never shares a symbol with a variable. -/
theorem memorySymbol_ne_variableSymbol (memory name : String) (width width' : Nat) :
    Expr.memorySymbol memory width ≠ Expr.variableSymbol name width' := by
  intro h
  have h' := congrArg String.toList h
  rw [toList_memorySymbol, toList_variableSymbol] at h'
  have hbang : '!' ∈ '|' :: ((Expr.escapeName name).toList ++ '!' :: (Nat.toDigits 10 width' ++ ['|'])) := by simp
  rw [← h'] at hbang
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hbang
  rcases hbang with hb | hb | hb | hb | hb
  · cases hb
  · exact separator_not_escaped (sep := '!') (by decide) memory hb
  · cases hb
  · have := digit_not_dollar hb
    revert this
    decide
  · cases hb

/-! ### Script shape -/

/-- The constants a script declares. -/
def scriptVars (constraints : List Expr) : List (String × Nat) :=
  (constraints.flatMap Expr.vars).eraseDups

/-- The functions a script declares. -/
def scriptMemories (constraints : List Expr) : List (String × Nat) :=
  (constraints.flatMap Expr.memories).eraseDups

def declaration (decl : String × Nat) : String :=
  s!"(declare-const {Expr.variableSymbol decl.1 decl.2} (_ BitVec {decl.2}))"

def functionDeclaration (decl : String × Nat) : String :=
  s!"(declare-fun {Expr.memorySymbol decl.1 decl.2} ((_ BitVec {decl.2})) (_ BitVec 8))"

def assertion (constraint : Expr) : String :=
  s!"(assert {constraint.renderFormula})"

def logic (constraints : List Expr) : String :=
  if (scriptMemories constraints).isEmpty then "QF_BV" else "QF_UFBV"

/-- The lines of a script: logic, declarations, assertions, query. -/
def scriptLines (constraints : List Expr) : List String :=
  [s!"(set-logic {logic constraints})"] ++ (scriptMemories constraints).map functionDeclaration ++
    (scriptVars constraints).map declaration ++ constraints.map assertion ++ ["(check-sat)"]

theorem renderScript_eq_lines (constraints : List Expr) :
    renderScript constraints = String.intercalate "\n" (scriptLines constraints) := by
  simp only [renderScript, scriptLines, scriptVars, scriptMemories, logic]
  congr 5

theorem length_scriptLines (constraints : List Expr) :
    (scriptLines constraints).length =
      (scriptMemories constraints).length + (scriptVars constraints).length + constraints.length + 2 := by
  simp [scriptLines]; omega

theorem assertion_mem_scriptLines {constraints : List Expr} {c : Expr} (h : c ∈ constraints) :
    assertion c ∈ scriptLines constraints := by
  simp only [scriptLines, List.mem_append, List.mem_map]
  exact .inl (.inr ⟨c, h, rfl⟩)

/-- Every constant used by any constraint is declared, and no others are. -/
theorem mem_scriptVars {v : String × Nat} {constraints : List Expr} :
    v ∈ scriptVars constraints ↔ ∃ c ∈ constraints, v ∈ c.vars := by
  simp [scriptVars, List.mem_eraseDups]

theorem mem_scriptMemories {v : String × Nat} {constraints : List Expr} :
    v ∈ scriptMemories constraints ↔ ∃ c ∈ constraints, v ∈ c.memories := by
  simp [scriptMemories, List.mem_eraseDups]

theorem declaration_mem_scriptLines {constraints : List Expr} {c : Expr} {v : String × Nat}
    (hc : c ∈ constraints) (hv : v ∈ c.vars) : declaration v ∈ scriptLines constraints := by
  simp only [scriptLines, List.mem_append, List.mem_map]
  exact .inl (.inl (.inr ⟨v, mem_scriptVars.mpr ⟨c, hc, hv⟩, rfl⟩))

/-- `List.eraseDups` is what its name promises. -/
theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  induction h : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    cases l with
    | nil => simp
    | cons a as =>
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨?_, ih _ (by
        have := List.length_filter_le (fun b => !b == a) as
        simp at h; omega) _ rfl⟩
      simp [List.mem_eraseDups]

/-- Declarations are collision free: no symbol is declared twice. -/
theorem scriptSymbols_nodup (constraints : List Expr) :
    ((scriptVars constraints).map fun v => Expr.variableSymbol v.1 v.2).Nodup := by
  refine List.pairwise_map.mpr ((nodup_eraseDups _).imp ?_)
  rintro ⟨a, w⟩ ⟨b, v⟩ hne h
  obtain ⟨h1, h2⟩ := variableSymbol_injective h
  simp only at h1 h2
  exact hne (by rw [h1, h2])

theorem scriptFunctions_nodup (constraints : List Expr) :
    ((scriptMemories constraints).map fun v => Expr.memorySymbol v.1 v.2).Nodup := by
  refine List.pairwise_map.mpr ((nodup_eraseDups _).imp ?_)
  rintro ⟨a, w⟩ ⟨b, v⟩ hne h
  obtain ⟨h1, h2⟩ := memorySymbol_injective h
  simp only at h1 h2
  exact hne (by rw [h1, h2])

private theorem infix_intercalate {x : String} {sep : String} {l : List String} (h : x ∈ l) :
    x.toList <:+: (sep.intercalate l).toList := by
  induction l with
  | nil => cases h
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp at h
      subst h
      simp [String.intercalate_singleton]
    | cons b tail =>
      rw [String.intercalate_cons_cons]
      simp only [String.toList_append]
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨[], _, by simp [List.append_assoc]; rfl⟩
      · exact (ih h).trans ⟨a.toList ++ sep.toList, [], by simp⟩

private theorem toString_string (s : String) : toString s = s := rfl

/-- Every variable a constraint declares textually occurs in it: `vars` agrees with `render`. -/
theorem var_occurs_in_render (e : Expr) :
    ∀ v ∈ e.vars, (Expr.variableSymbol v.1 v.2).toList <:+: e.render.toList := by
  apply Expr.rec (motive_1 := fun e => ∀ v ∈ e.vars, (Expr.variableSymbol v.1 v.2).toList <:+: e.render.toList)
    (motive_2 := fun args => ∀ a ∈ args, ∀ v ∈ a.vars, (Expr.variableSymbol v.1 v.2).toList <:+: a.render.toList)
  · intro name width v hv
    rw [Expr.vars] at hv
    simp at hv
    subst hv
    rw [Expr.render]
    exact List.infix_refl _
  · intro _ _ v hv
    rw [Expr.vars] at hv
    simp at hv
  · intro name width args ih v hv
    rw [Expr.vars] at hv
    simp only [List.mem_eraseDups, List.mem_flatMap] at hv
    obtain ⟨a, ha, hv⟩ := hv
    have hne : args.isEmpty = false := by
      cases args with
      | nil => cases ha
      | cons _ _ => rfl
    have hterm : (Expr.variableSymbol v.1 v.2).toList <:+:
        ("(" ++ String.intercalate " " (name :: args.map Expr.render) ++ ")").toList := by
      simp only [String.toList_append]
      exact (ih a ha v hv).trans ((infix_intercalate (sep := " ") (l := name :: args.map Expr.render)
        (x := a.render) (by simp; exact .inr ⟨a, ha, rfl⟩)).trans ⟨"(".toList, ")".toList, rfl⟩)
    rw [Expr.render, ite_eq_right (by simp [hne])]
    simp only
    split
    · refine hterm.trans ⟨"(ite ".toList, " #b1 #b0)".toList, ?_⟩
      simp [String.toList_append, toString]
    · exact hterm
  · intro high low value ih v hv
    rw [Expr.vars] at hv
    rw [Expr.render]
    refine (ih v hv).trans ⟨(toString "((_ extract " ++ toString high ++ toString " " ++ toString low ++
      toString ") ").toList, ")".toList, ?_⟩
    simp [String.toList_append, toString]
  · intro left right ihl ihr v hv
    rw [Expr.vars] at hv
    simp only [List.mem_eraseDups, List.mem_append] at hv
    rw [Expr.render]
    rcases hv with hv | hv
    · refine (ihl v hv).trans ⟨"(concat ".toList, (" " ++ right.render ++ ")").toList, ?_⟩
      simp [String.toList_append, toString]
    · refine (ihr v hv).trans ⟨("(concat " ++ left.render ++ " ").toList, ")".toList, ?_⟩
      simp [String.toList_append, toString]
  · intro cond yes no ihc ihy ihn v hv
    rw [Expr.vars] at hv
    simp only [List.mem_eraseDups, List.mem_append] at hv
    rw [Expr.render]
    rcases hv with (hv | hv) | hv
    · refine (ihc v hv).trans ⟨"(ite (= ".toList, (" #b1) " ++ yes.render ++ " " ++ no.render ++ ")").toList, ?_⟩
      simp [String.toList_append, toString]
    · refine (ihy v hv).trans ⟨("(ite (= " ++ cond.render ++ " #b1) ").toList, (" " ++ no.render ++ ")").toList, ?_⟩
      simp [String.toList_append, toString]
    · refine (ihn v hv).trans ⟨("(ite (= " ++ cond.render ++ " #b1) " ++ yes.render ++ " ").toList, ")".toList, ?_⟩
      simp [String.toList_append, toString]
  · intro memory address ih v hv
    rw [Expr.vars] at hv
    rw [Expr.render]
    refine (ih v hv).trans ⟨("(" ++ Expr.memorySymbol memory address.width ++ " ").toList, ")".toList, ?_⟩
    simp [String.toList_append, toString]
  · intro a ha; cases ha
  · intro head tail ih1 ih2 a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ih1
    · exact ih2 a ha

/-! ### Sorts

The term of an expression is always a bitvector, and an assertion is always a formula. Real Z3 agrees on
every operator and constructor; see `BapTests/Symbolic.lean`. -/

/-- Predicates are wrapped back into a bit when used as terms. -/
theorem render_predicate {name : String} {width : Nat} {args : List Expr} (hp : Expr.isPredicate name = true)
    (hne : args ≠ []) :
    (Expr.app name width args).render =
      "(ite " ++ ("(" ++ String.intercalate " " (name :: args.map Expr.render) ++ ")") ++ " #b1 #b0)" := by
  have : args.isEmpty = false := by simpa using hne
  rw [Expr.render]
  simp only [this, hp, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- A conditional always tests its one-bit condition through an equality. -/
theorem render_ite (condition yes no : Expr) :
    (Expr.ite condition yes no).render =
      "(ite (= " ++ condition.render ++ " #b1) " ++ yes.render ++ " " ++ no.render ++ ")" := by
  rw [Expr.render]
  apply String.toList_inj.mp
  simp [String.toList_append, toString]

/-- Bits are asserted through an equality with one, in every form. -/
theorem renderFormula_var (name : String) :
    (Expr.var name 1).renderFormula = s!"(= {Expr.variableSymbol name 1} #b1)" := by
  simp [Expr.renderFormula, Expr.render, Expr.width]
  apply String.toList_inj.mp
  simp [String.toList_append, toString]

theorem renderFormula_const (value : BitVec 1) :
    (Expr.const value).renderFormula = s!"(= {(Expr.const value).render} #b1)" := by
  simp [Expr.renderFormula, Expr.width]
  apply String.toList_inj.mp
  simp [String.toList_append, toString]

theorem renderFormula_ite (condition yes no : Expr) (h : yes.width = 1) :
    (Expr.ite condition yes no).renderFormula = s!"(= {(Expr.ite condition yes no).render} #b1)" := by
  simp [Expr.renderFormula, Expr.width, h]
  apply String.toList_inj.mp
  simp [String.toList_append, toString]

/-- A predicate is asserted directly, being a formula already. -/
theorem renderFormula_predicate {name : String} {width : Nat} {args : List Expr} (hp : Expr.isPredicate name = true)
    (hne : args ≠ []) :
    (Expr.app name width args).renderFormula = "(" ++ String.intercalate " " (name :: args.map Expr.render) ++ ")" := by
  have : args.isEmpty = false := by simpa using hne
  simp [Expr.renderFormula, hp, this]

/-- The else condition is a formula for any one-bit value, and so is the then condition. -/
theorem renderFormula_eqZero (value : Expr) :
    (Expr.eqZero value).renderFormula =
      "(" ++ String.intercalate " " ["=", value.render, (Expr.const (BitVec.ofNat value.width 0)).render] ++ ")" := by
  have hp : Expr.isPredicate "=" = true := by decide
  simp [Expr.eqZero, Expr.renderFormula, hp]

/-! ### Parentheses -/

/-- `(` minus `)`. -/
def balance (s : String) : Int :=
  (s.toList.map fun c => if c = '(' then (1 : Int) else if c = ')' then -1 else 0).sum

theorem balance_append (a b : String) : balance (a ++ b) = balance a + balance b := by
  simp [balance, String.toList_append, List.sum_append]

private theorem balance_of_no_parens {s : String} (h : ∀ c ∈ s.toList, c ≠ '(' ∧ c ≠ ')') : balance s = 0 := by
  unfold balance
  generalize s.toList = l at h
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := h a (by simp)
    simp only [List.map_cons, List.sum_cons, ha.1, ha.2, ↓reduceIte]
    rw [ih fun c hc => h c (by simp [hc])]
    rfl

theorem balance_toString_nat (n : Nat) : balance (toString n) = 0 := by
  apply balance_of_no_parens
  intro c hc
  have hd : c.isDigit = true := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by decide) (by decide)
    (by simpa using hc)
  constructor
  · rintro rfl; cases hd
  · rintro rfl; cases hd

theorem balance_escapeName (name : String) : balance (Expr.escapeName name) = 0 := by
  apply balance_of_no_parens
  intro c hc
  have := symbolChar_escapeName hc
  constructor
  · rintro rfl; revert this; decide
  · rintro rfl; revert this; decide

theorem balance_variableSymbol (name : String) (width : Nat) : balance (Expr.variableSymbol name width) = 0 := by
  simp only [Expr.variableSymbol, balance_append, balance_escapeName, balance_toString_nat, toString_string,
    show balance "|" = 0 by decide, show balance "!" = 0 by decide]
  decide

theorem balance_memorySymbol (name : String) (width : Nat) : balance (Expr.memorySymbol name width) = 0 := by
  simp only [Expr.memorySymbol, balance_append, balance_escapeName, balance_toString_nat, toString_string,
    show balance "|" = 0 by decide, show balance "@" = 0 by decide]
  decide

/-- Expressions whose application heads do not unbalance the text; the executor's heads all qualify. -/
inductive WellNamed : Expr → Prop where
  | var (name width) : WellNamed (.var name width)
  | const {width} (value : BitVec width) : WellNamed (.const value)
  | app {name width args} : balance name = 0 → (∀ a ∈ args, WellNamed a) → WellNamed (.app name width args)
  | extract {value} (high low) : WellNamed value → WellNamed (.extract high low value)
  | concat {left right} : WellNamed left → WellNamed right → WellNamed (.concat left right)
  | ite {c yes no} : WellNamed c → WellNamed yes → WellNamed no → WellNamed (.ite c yes no)
  | select {address} (memory) : WellNamed address → WellNamed (.select memory address)

private theorem balance_intercalate {sep : String} (hsep : balance sep = 0) {l : List String}
    (h : ∀ x ∈ l, balance x = 0) : balance (sep.intercalate l) = 0 := by
  induction l with
  | nil => simp [String.intercalate_nil, balance]
  | cons a rest ih =>
    cases rest with
    | nil => rw [String.intercalate_singleton]; exact h a (by simp)
    | cons b tail =>
      rw [String.intercalate_cons_cons, balance_append, balance_append, hsep, h a (by simp),
        ih fun x hx => h x (by simp [hx])]
      rfl

private theorem balance_term {name : String} {args : List Expr} (hname : balance name = 0)
    (ih : ∀ a ∈ args, balance a.render = 0) :
    balance ("(" ++ String.intercalate " " (name :: args.map Expr.render) ++ ")") = 0 := by
  rw [balance_append, balance_append, balance_intercalate (by decide),
    show balance "(" = 1 by decide, show balance ")" = -1 by decide]
  · decide
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hname
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact ih a ha

/-- The renderer closes every parenthesis it opens. -/
theorem balance_render {e : Expr} (h : WellNamed e) : balance e.render = 0 := by
  induction h with
  | var name width => rw [Expr.render]; exact balance_variableSymbol name width
  | @const width value =>
    rw [Expr.render]
    simp only [balance_append, balance_toString_nat, toString_string,
      show balance "(_ bv" = 1 by decide, show balance " " = 0 by decide, show balance ")" = -1 by decide]
    decide
  | @app name width args hname _ ih =>
    rw [Expr.render]
    split
    · exact hname
    · simp only
      split
      · simp only [balance_append, toString_string, balance_term hname ih,
          show balance "(ite " = 1 by decide, show balance " #b1 #b0)" = -1 by decide]
        decide
      · exact balance_term hname ih
  | extract high low _ ih =>
    rw [Expr.render]
    simp only [balance_append, balance_toString_nat, toString_string, ih,
      show balance "((_ extract " = 2 by decide, show balance " " = 0 by decide, show balance ") " = -1 by decide,
      show balance ")" = -1 by decide]
    decide
  | concat _ _ ihl ihr =>
    rw [Expr.render]
    simp only [balance_append, toString_string, ihl, ihr,
      show balance "(concat " = 1 by decide, show balance " " = 0 by decide, show balance ")" = -1 by decide]
    decide
  | ite _ _ _ ihc ihy ihn =>
    rw [Expr.render]
    simp only [balance_append, toString_string, ihc, ihy, ihn,
      show balance "(ite (= " = 2 by decide, show balance " #b1) " = -1 by decide, show balance " " = 0 by decide,
      show balance ")" = -1 by decide]
    decide
  | select memory _ ih =>
    rw [Expr.render]
    simp only [balance_append, toString_string, ih, balance_memorySymbol,
      show balance "(" = 1 by decide, show balance " " = 0 by decide, show balance ")" = -1 by decide]
    decide

theorem balance_renderFormula {e : Expr} (h : WellNamed e) : balance e.renderFormula = 0 := by
  have hbit : balance (if e.width = 1 then "#b1" else s!"(_ bv1 {e.width})") = 0 := by
    split
    · decide
    · simp only [balance_append, balance_toString_nat, toString_string,
        show balance "(_ bv1 " = 1 by decide, show balance ")" = -1 by decide]
      decide
  simp only [toString_string] at hbit
  have heq : balance s!"(= {e.render} {if e.width = 1 then "#b1" else s!"(_ bv1 {e.width})"})" = 0 := by
    simp only [balance_append, toString_string, balance_render h, hbit,
      show balance "(= " = 1 by decide, show balance " " = 0 by decide, show balance ")" = -1 by decide]
    decide
  cases e with
  | app name width args =>
    simp only [Expr.renderFormula]
    split
    · cases h with
      | app hname hargs => exact balance_term hname fun a ha => balance_render (hargs a ha)
    · exact heq
  | _ => exact heq

theorem balance_declaration (decl : String × Nat) : balance (declaration decl) = 0 := by
  simp only [declaration, balance_append, balance_toString_nat, toString_string, balance_variableSymbol,
    show balance "(declare-const " = 1 by decide, show balance " (_ BitVec " = 1 by decide,
    show balance "))" = -2 by decide]
  decide

theorem balance_functionDeclaration (decl : String × Nat) : balance (functionDeclaration decl) = 0 := by
  simp only [functionDeclaration, balance_append, balance_toString_nat, toString_string, balance_memorySymbol,
    show balance "(declare-fun " = 1 by decide, show balance " ((_ BitVec " = 2 by decide,
    show balance ")) (_ BitVec 8))" = -3 by decide]
  decide

/-- Whole scripts balance, so the solver never sees unterminated input. -/
theorem balance_renderScript {constraints : List Expr} (h : ∀ c ∈ constraints, WellNamed c) :
    balance (renderScript constraints) = 0 := by
  rw [renderScript_eq_lines]
  refine balance_intercalate (by decide) ?_
  intro line hline
  simp only [scriptLines, List.mem_append, List.mem_map, List.mem_singleton] at hline
  rcases hline with (((rfl | ⟨decl, _, rfl⟩) | ⟨decl, _, rfl⟩) | ⟨c, hc, rfl⟩) | rfl
  · simp only [balance_append, toString_string, logic]
    split <;> decide
  · exact balance_functionDeclaration decl
  · exact balance_declaration decl
  · simp only [assertion, balance_append, toString_string, balance_renderFormula (h c hc),
      show balance "(assert " = 1 by decide, show balance ")" = -1 by decide]
    decide
  · decide

end Bap.Proofs.FFI
