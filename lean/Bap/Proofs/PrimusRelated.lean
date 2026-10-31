import Lean
import Bap.Proofs.Primus

open Lean Elab Command in
/-- Bring private declarations of module `mod`, namespace `ns`, into scope by short name. -/
local elab "open_private " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

open Lean Elab Command in
/-- Like `open_private`, but for a private name that would clash with a public one. -/
local elab "open_private_as " mod:ident full:ident «alias»:ident : command => do
  let decl := OpenDecl.explicit «alias».getId (mkPrivateNameCore mod.getId full.getId)
  modifyScope fun scope => { scope with openDecls := decl :: scope.openDecls }

namespace Bap.Proofs.Primus

open Bap.Primus.Semantics
open_private Bap.Primus.Semantics Bap.Primus.Semantics compileFunction compileCallable compileValue expectBil expectNat truth condition widthOf binary unaryNot leadingZeros
  shift wordWidth assign assignRegister loadMemory storeMemory concatStep symbolText symbolConcat castSaturate floatOperation
  floatCall roundingMode intrinsicCall intrinsicParams intrinsicGroup assignInputs mapIndexedM valueOnly applyPrimitive
  applyPrimitiveIndex caseMatches selectForm selectArm
open_private Bap.Primus.Semantics Bap.Primus.Semantics.floatOperation match_1 match_3 match_5
open_private_as Bap.Primus.Semantics Bap.Primus.Semantics.compare primCompare
open_private_as Bap.Primus.Semantics Bap.Primus.Semantics.cast primCast

local notation "SV" => Bap.Primus.Semantics.Value

mutual
  /-- Two values that are the same up to which of the functions in them are compiled. -/
  inductive ValueRel (names : String → Option SV) : SV → SV → Prop
    | unit : ValueRel names .unit .unit
    | int (value) : ValueRel names (.int value) (.int value)
    | bil (width value) : ValueRel names (.bil width value) (.bil width value)
    | bool (value) : ValueRel names (.bool value) (.bool value)
    | register (name width baseWidth) : ValueRel names (.register name width baseWidth) (.register name width baseWidth)
    | symbol (name) : ValueRel names (.symbol name) (.symbol name)
    | list {first second} : ListRel names first second → ValueRel names (.list first) (.list second)
    | callable {first second} : CallableRel names first second → ValueRel names (.callable first) (.callable second)

  /-- Lists of such values, position by position. -/
  inductive ListRel (names : String → Option SV) : List SV → List SV → Prop
    | nil : ListRel names [] []
    | cons {a b as bs} : ValueRel names a b → ListRel names as bs → ListRel names (a :: as) (b :: bs)

  /-- Bindings of the same names to such values. -/
  inductive EnvRel (names : String → Option SV) : Locals → Locals → Prop
    | nil : EnvRel names [] []
    | cons (name) {a b as bs} : ValueRel names a b → EnvRel names as bs → EnvRel names ((name, a) :: as) ((name, b) :: bs)

  /-- The definitions of a name, position by position. -/
  inductive CandidatesRel (names : String → Option SV) : List Callable → List Callable → Prop
    | nil : CandidatesRel names [] []
    | cons {a b as bs} : CallableRel names a b → CandidatesRel names as bs → CandidatesRel names (a :: as) (b :: bs)

  /-- A function and itself, with the same up to compilation in what it closes over, or a function and its compilation, either way round. -/
  inductive CallableRel (names : String → Option SV) : Callable → Callable → Prop
    | function (params body) {first second} : EnvRel names first second →
        CallableRel names (.function params body first) (.function params body second)
    | compiled (params body) {first second} : EnvRel names first second →
        CallableRel names (.compiled params body first) (.compiled params body second)
    | «macro» (params body) : CallableRel names (.macro params body) (.macro params body)
    | primitive (name) : CallableRel names (.primitive name) (.primitive name)
    | overloads {first second} : CandidatesRel names first second → CallableRel names (.overloads first) (.overloads second)
    | compile {params body env compiled} : compileFunction names (.function params body env) = .compiled params compiled env →
        CallableRel names (.function params body env) (.compiled params compiled env)
    | decompile {params body env compiled} : compileFunction names (.function params body env) = .compiled params compiled env →
        CallableRel names (.compiled params compiled env) (.function params body env)
end

variable {names : String → Option SV}

mutual
  theorem ValueRel.refl : (value : SV) → ValueRel names value value
    | .unit => .unit
    | .int v => .int v
    | .bil w v => .bil w v
    | .bool v => .bool v
    | .register n w b => .register n w b
    | .symbol n => .symbol n
    | .list items => .list (ListRel.refl items)
    | .callable c => .callable (CallableRel.refl c)

  theorem ListRel.refl : (values : List SV) → ListRel names values values
    | [] => .nil
    | head :: rest => .cons (ValueRel.refl head) (ListRel.refl rest)

  theorem EnvRel.refl : (values : List (String × SV)) → EnvRel names values values
    | [] => .nil
    | (name, value) :: rest => .cons name (ValueRel.refl value) (EnvRel.refl rest)

  theorem CandidatesRel.refl : (values : List Callable) → CandidatesRel names values values
    | [] => .nil
    | head :: rest => .cons (CallableRel.refl head) (CandidatesRel.refl rest)

  theorem CallableRel.refl : (callable : Callable) → CallableRel names callable callable
    | .function p b e => .function p b (EnvRel.refl e)
    | .compiled p b e => .compiled p b (EnvRel.refl e)
    | .macro p b => .macro p b
    | .primitive n => .primitive n
    | .overloads c => .overloads (CandidatesRel.refl c)
end

mutual
  theorem ValueRel.symm {a b : SV} : ValueRel names a b → ValueRel names b a
    | .unit => .unit
    | .int v => .int v
    | .bil w v => .bil w v
    | .bool v => .bool v
    | .register n w b => .register n w b
    | .symbol n => .symbol n
    | .list h => .list h.symm
    | .callable h => .callable h.symm

  theorem ListRel.symm {a b : List SV} : ListRel names a b → ListRel names b a
    | .nil => .nil
    | .cons h t => .cons h.symm t.symm

  theorem EnvRel.symm {a b : Locals} : EnvRel names a b → EnvRel names b a
    | .nil => .nil
    | .cons n h t => .cons n h.symm t.symm

  theorem CandidatesRel.symm {a b : List Callable} : CandidatesRel names a b → CandidatesRel names b a
    | .nil => .nil
    | .cons h t => .cons h.symm t.symm

  theorem CallableRel.symm {a b : Callable} : CallableRel names a b → CallableRel names b a
    | .function p b h => .function p b h.symm
    | .compiled p b h => .compiled p b h.symm
    | .macro p b => .macro p b
    | .primitive n => .primitive n
    | .overloads h => .overloads h.symm
    | .compile h => .decompile h
    | .decompile h => .compile h
end


mutual
  /-- A value with no function anywhere in it. -/
  def firstOrder : SV → Bool
    | .callable _ => false
    | .list items => firstOrderList items
    | _ => true

  /-- A list of such values. -/
  def firstOrderList : List SV → Bool
    | [] => true
    | head :: rest => firstOrder head && firstOrderList rest
end

mutual
  /-- Values the same up to compilation with no function in them are the same. -/
  theorem ValueRel.eq_of_firstOrder {a b : SV} : ValueRel names a b → firstOrder a = true → a = b
    | .unit, _ => rfl
    | .int _, _ => rfl
    | .bil _ _, _ => rfl
    | .bool _, _ => rfl
    | .register _ _ _, _ => rfl
    | .symbol _, _ => rfl
    | .list h, hf => by
      rw [ListRel.eq_of_firstOrder h (by simpa [firstOrder] using hf)]
    | .callable _, hf => by simp [firstOrder] at hf

  theorem ListRel.eq_of_firstOrder {a b : List SV} : ListRel names a b → firstOrderList a = true → a = b
    | .nil, _ => rfl
    | .cons h t, hf => by
      simp only [firstOrderList, Bool.and_eq_true] at hf
      rw [ValueRel.eq_of_firstOrder h hf.1, ListRel.eq_of_firstOrder t hf.2]
end

/-! ### Definitions as they are in a state

A definition is seen as written or compiled, and two of its views are the same up to compilation. -/

theorem compileFunction_rel (callable : Callable) : CallableRel names callable (compileFunction names callable) := by
  cases callable with
  | function p b e =>
    cases hc : compileFunction names (.function p b e) with
    | compiled p' cb e' =>
      have heq : p' = p ∧ e' = e := by
        simp only [compileFunction] at hc
        split at hc <;> simp_all
      obtain ⟨rfl, rfl⟩ := heq
      exact .compile hc
    | function p' b' e' =>
      have heq : p' = p ∧ b' = b ∧ e' = e := by
        simp only [compileFunction] at hc
        split at hc <;> simp_all
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact CallableRel.refl _
    | «macro» p' b' =>
      simp only [compileFunction] at hc
      split at hc <;> simp_all
    | primitive n =>
      simp only [compileFunction] at hc
      split at hc <;> simp_all
    | overloads c =>
      simp only [compileFunction] at hc
      split at hc <;> simp_all
  | compiled p b e => exact CallableRel.refl _
  | «macro» p b => exact CallableRel.refl _
  | primitive n => exact CallableRel.refl _
  | overloads c => exact CallableRel.refl _

theorem compileCallable_rel (callable : Callable) : CallableRel names callable (compileCallable names callable) := by
  cases callable with
  | overloads candidates =>
    refine .overloads ?_
    induction candidates with
    | nil => exact .nil
    | cons head rest ih => exact .cons (compileFunction_rel head) ih
  | function p b e => exact compileFunction_rel _
  | compiled p b e => exact compileFunction_rel _
  | «macro» p b => exact compileFunction_rel _
  | primitive n => exact compileFunction_rel _

theorem compileValue_rel (value : SV) : ValueRel names value (compileValue names value) := by
  cases value
  case callable callable => exact .callable (compileCallable_rel callable)
  all_goals exact ValueRel.refl _

theorem viewValue_rel (first second : Bool) (value : SV) : ValueRel names (viewValue names first value) (viewValue names second value) := by
  cases first <;> cases second
  · exact ValueRel.refl _
  · exact compileValue_rel value
  · exact (compileValue_rel value).symm
  · exact ValueRel.refl _

/-! ### What looks at a value sees no difference -/

theorem expectBil_rel (context : Context) {a b : SV} (h : ValueRel names a b) : expectBil context a = expectBil context b := by
  cases h <;> rfl

theorem expectNat_rel {a b : SV} (h : ValueRel names a b) : expectNat a = expectNat b := by
  cases h <;> rfl

theorem truth_rel {a b : SV} (h : ValueRel names a b) : truth a = truth b := by
  cases h <;> rfl

theorem condition_rel (context : Context) {a b : SV} (h : ValueRel names a b) : condition context a = condition context b := by
  simp only [condition, expectBil_rel context h]

theorem widthOf_rel (context : Context) {a b : SV} (h : ValueRel names a b) : widthOf context a = widthOf context b := by
  cases h <;> rfl

theorem symbolText_rel {a b : SV} (h : ValueRel names a b) : symbolText a = symbolText b := by
  cases h <;> rfl

theorem roundingMode_rel {a b : SV} (h : ValueRel names a b) : roundingMode a = roundingMode b := by
  cases h <;> rfl

theorem caseMatches_rel {a b : SV} (h : ValueRel names a b) (form : Sexp) : caseMatches a form = caseMatches b form := by
  cases h <;> rfl

theorem selectForm_rel {a b : SV} (h : ValueRel names a b) (forms : List Sexp) : selectForm a forms = selectForm b forms := by
  match forms with
  | [] => simp only [selectForm]
  | [_] => simp only [selectForm]
  | label :: body :: rest => simp only [selectForm, caseMatches_rel h, selectForm_rel h rest]

theorem selectArm_rel {a b : SV} (h : ValueRel names a b) (arms : List (Option Sexp × CExp)) : selectArm a arms = selectArm b arms := by
  match arms with
  | [] => simp only [selectArm]
  | (none, _) :: _ => simp only [selectArm]
  | (some label, _) :: rest => simp only [selectArm, caseMatches_rel h, selectArm_rel h rest]

theorem ListRel.length_eq {a b : List SV} : ListRel names a b → a.length = b.length
  | .nil => rfl
  | .cons _ t => by simp only [List.length_cons, t.length_eq]

theorem ListRel.append {a b c d : List SV} : ListRel names a b → ListRel names c d → ListRel names (a ++ c) (b ++ d)
  | .nil, h => h
  | .cons x t, h => .cons x (t.append h)

theorem mapM_rel {β : Type} {f : SV → Except String β} (hf : ∀ {a b}, ValueRel names a b → f a = f b) :
    ∀ {a b}, ListRel names a b → a.mapM f = b.mapM f
  | _, _, .nil => rfl
  | _, _, .cons h t => by simp only [List.mapM_cons, hf h, mapM_rel hf t]

theorem binary_rel (context : Context) (op : Bil.BinOp) {a b : List SV} (h : ListRel names a b) :
    binary context op a = binary context op b := by
  simp only [binary, mapM_rel (expectBil_rel context) h]

theorem compare_rel (context : Context) (op : Bil.BinOp) {a b : List SV} (h : ListRel names a b) :
    primCompare context op a = primCompare context op b := by
  rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, t⟩⟩⟩
  · rfl
  · cases h1 <;> rfl
  · cases h1 <;> cases h2 <;> rfl
  · cases h1 <;> cases h2 <;> rfl

theorem unaryNot_rel (context : Context) {a b : List SV} (h : ListRel names a b) : unaryNot context a = unaryNot context b := by
  rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
  · rfl
  · simp only [unaryNot, expectBil_rel context h1]
  · rfl

theorem leadingZeros_rel (context : Context) {a b : List SV} (h : ListRel names a b) :
    leadingZeros context a = leadingZeros context b := by
  rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
  · rfl
  · simp only [leadingZeros, expectBil_rel context h1]
  · rfl

theorem shift_rel (context : Context) (op : Bil.BinOp) {a b : List SV} (h : ListRel names a b) :
    shift context op a = shift context op b := by
  rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, t⟩⟩⟩
  · rfl
  · rfl
  · simp only [shift, expectBil_rel context h1, expectBil_rel context h2]
  · rfl

theorem cast_rel (context : Context) (kind : Bil.Cast) {a b : List SV} (h : ListRel names a b) :
    primCast context kind a = primCast context kind b := by
  rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, t⟩⟩⟩
  · rfl
  · rfl
  · simp only [primCast, expectNat_rel h1, expectBil_rel context h2]
  · rfl

theorem wordWidth_rel (context : Context) {a b : List SV} (h : ListRel names a b) : wordWidth context a = wordWidth context b := by
  simp only [wordWidth, mapM_rel (widthOf_rel context) h]
  cases h <;> rfl

theorem assignRegister_rel (context : Context) (name : String) (width baseWidth : Nat) {a b : SV} (h : ValueRel names a b) :
    assignRegister context name width baseWidth a = assignRegister context name width baseWidth b := by
  simp only [assignRegister, expectBil_rel context h]

theorem assign_rel (context : Context) {a b c d : SV} (h1 : ValueRel names a b) (h2 : ValueRel names c d) :
    assign context a c = assign context b d := by
  cases h1
  case register => simp only [assign, assignRegister_rel context _ _ _ h2]
  all_goals rfl

theorem loadMemory_rel (context : Context) (bits : Nat) {a b : List SV} (h : ListRel names a b) :
    loadMemory context bits a = loadMemory context bits b := by
  rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
  · rfl
  · simp only [loadMemory, expectBil_rel context h1]
  · rfl

theorem storeMemory_rel (context : Context) {a b : List SV} (h : ListRel names a b) :
    storeMemory context a = storeMemory context b := by
  rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, t⟩⟩⟩
  · rfl
  · rfl
  · simp only [storeMemory, expectBil_rel context h1, expectBil_rel context h2]
  · rfl

theorem concatStep_rel (context : Context) (current : Nat × Bil.Exp) {a b : SV} (h : ValueRel names a b) :
    concatStep context current a = concatStep context current b := by
  simp only [concatStep, expectBil_rel context h]

theorem foldlM_concat_rel (context : Context) (current : Nat × Bil.Exp) {a b : List SV} (h : ListRel names a b) :
    a.foldlM (concatStep context) current = b.foldlM (concatStep context) current := by
  induction a generalizing b current with
  | nil => cases h; rfl
  | cons head rest ih =>
    cases h with
    | cons hh ht =>
      simp only [List.foldlM_cons, concatStep_rel context current hh]
      cases concatStep context current _ with
      | error => rfl
      | ok x => exact ih x ht

theorem symbolConcat_rel {a b : List SV} (h : ListRel names a b) : symbolConcat a = symbolConcat b := by
  simp only [symbolConcat, mapM_rel symbolText_rel h]

theorem castSaturate_rel (context : Context) {a b : List SV} (h : ListRel names a b) :
    castSaturate context a = castSaturate context b := by
  rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, t⟩⟩⟩⟩
  · rfl
  · cases h1 <;> rfl
  · cases h1 <;> rfl
  · cases h1
    case symbol => simp only [castSaturate, expectNat_rel h2, expectBil_rel context h3]
    all_goals rfl
  · cases h1 <;> rfl

/-! Intrinsics. -/

/-- The groups of arguments of an intrinsic, in order. -/
inductive GroupsRel (names : String → Option SV) : List (String × List SV) → List (String × List SV) → Prop
  | nil : GroupsRel names [] []
  | cons (key) {a b as bs} : ListRel names a b → GroupsRel names as bs → GroupsRel names ((key, a) :: as) ((key, b) :: bs)

theorem ListRel.reverse {a b : List SV} (h : ListRel names a b) : ListRel names a.reverse b.reverse := by
  induction a generalizing b with
  | nil => cases h; exact .nil
  | cons x xs ih =>
    cases h with
    | cons hh ht =>
      simp only [List.reverse_cons]
      exact (ih ht).append (.cons hh .nil)

theorem intrinsicParams_rel (key : String) {current current' a b : List SV} (hc : ListRel names current current') (h : ListRel names a b) :
    GroupsRel names (intrinsicParams key current a) (intrinsicParams key current' b) := by
  induction a generalizing key current current' b with
  | nil =>
    cases h
    simp only [intrinsicParams]
    exact .cons _ hc.reverse .nil
  | cons x xs ih =>
    cases h with
    | cons hh ht =>
      cases hh
      case symbol keyword =>
        simp only [intrinsicParams]
        split
        · exact .cons _ hc.reverse (ih _ .nil ht)
        · exact ih _ (.cons (.symbol _) hc) ht
      case unit => simp only [intrinsicParams]; exact ih _ (.cons .unit hc) ht
      case int v => simp only [intrinsicParams]; exact ih _ (.cons (.int v) hc) ht
      case bil w v => simp only [intrinsicParams]; exact ih _ (.cons (.bil w v) hc) ht
      case bool v => simp only [intrinsicParams]; exact ih _ (.cons (.bool v) hc) ht
      case register n w s => simp only [intrinsicParams]; exact ih _ (.cons (.register n w s) hc) ht
      case list hl => simp only [intrinsicParams]; exact ih _ (.cons (.list hl) hc) ht
      case callable hl => simp only [intrinsicParams]; exact ih _ (.cons (.callable hl) hc) ht

/-- Lists of lists of values. -/
inductive ListsRel (names : String → Option SV) : List (List SV) → List (List SV) → Prop
  | nil : ListsRel names [] []
  | cons {a b as bs} : ListRel names a b → ListsRel names as bs → ListsRel names (a :: as) (b :: bs)

theorem intrinsicGroup_rel (key : String) {a b : List (String × List SV)} (h : GroupsRel names a b) :
    ListsRel names (intrinsicGroup key a) (intrinsicGroup key b) := by
  induction h with
  | nil => exact .nil
  | cons k hh _ ih =>
    simp only [intrinsicGroup, List.filterMap_cons] at ih ⊢
    by_cases hk : k = key
    · simp only [hk, ↓reduceIte]
      exact .cons hh ih
    · simp only [hk, ↓reduceIte]
      exact ih

theorem ListsRel.flatten {a b : List (List SV)} (h : ListsRel names a b) : ListRel names a.flatten b.flatten := by
  induction h with
  | nil => exact .nil
  | cons hh _ ih => exact hh.append ih

theorem ListsRel.length_eq {a b : List (List SV)} (h : ListsRel names a b) : a.length = b.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem assignInputs_rel (context : Context) {a b : List SV} (h : ListRel names a b) :
    assignInputs context a = assignInputs context b := by
  simp only [assignInputs]
  generalize 0 = index
  induction a generalizing b index with
  | nil => cases h; rfl
  | cons x xs ih =>
    cases h with
    | cons hh ht => simp only [mapIndexedM, expectBil_rel context hh, ih ht]

theorem mapIndexedM_lists {β : Type} {f : Nat → List SV → Except String β} (hf : ∀ i {a b}, ListRel names a b → f i a = f i b)
    (index : Nat) {a b : List (List SV)} (h : ListsRel names a b) : mapIndexedM f index a = mapIndexedM f index b := by
  induction h generalizing index with
  | nil => rfl
  | cons hh _ ih => simp only [mapIndexedM, hf index hh, ih]

theorem intrinsicCall_rel (context : Context) (name : String) {a b : List SV} (h : ListRel names a b) :
    intrinsicCall context name a = intrinsicCall context name b := by
  have hp := intrinsicParams_rel ":inputs" (ListRel.nil (names := names)) h
  have hi := assignInputs_rel context (intrinsicGroup_rel ":inputs" hp).flatten
  have hr := intrinsicGroup_rel ":result" hp
  have hw := intrinsicGroup_rel ":writes" hp
  have hs := intrinsicGroup_rel ":stores" hp
  simp only [intrinsicCall]
  rw [hi]
  cases assignInputs context _ with
  | error => rfl
  | ok inputs =>
    simp only [bind, Except.bind, hr.length_eq]
    rw [mapIndexedM_lists ?_ 0 hw]
    · cases mapIndexedM _ 0 (intrinsicGroup ":writes" _) with
      | error => rfl
      | ok writes =>
        simp only
        rw [mapIndexedM_lists ?_ 0 hs]
        · cases mapIndexedM _ 0 (intrinsicGroup ":stores" _) with
          | error => rfl
          | ok stores =>
            simp only
            generalize intrinsicGroup ":result" (intrinsicParams ":inputs" [] a) = ra at hr
            generalize intrinsicGroup ":result" (intrinsicParams ":inputs" [] b) = rb at hr
            rcases hr with _ | ⟨_ | ⟨h1, _ | ⟨h2, t⟩⟩, _ | ⟨h3, t3⟩⟩
            · rfl
            · rfl
            · rfl
            · simp only [expectNat_rel h1]
            · rfl
            · rfl
            · rfl
        · intro i x y hxy
          rcases hxy with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, t⟩⟩⟩
          · rfl
          · simp only [storeMemory_rel context (.cons h1 (.cons (ValueRel.refl _) .nil))]
          · simp only [expectNat_rel h2, storeMemory_rel context (.cons h1 (.cons (ValueRel.refl _) .nil))]
          · rfl
    · intro i x y hxy
      rcases hxy with _ | ⟨h1, _ | ⟨h2, t⟩⟩
      · rfl
      · cases h1 <;> rfl
      · cases h1 <;> rfl

theorem floatCall_rel (context : Context) (name : String) (result : Nat) {a b : List SV} (h : ListRel names a b) :
    floatCall context name result a = floatCall context name result b :=
  intrinsicCall_rel context name (h.append (ListRel.refl _))

theorem floatOperation_rel (context : Context) (name : String) {a b : List SV} (h : ListRel names a b) :
    floatOperation context name a = floatOperation context name b := by
  unfold floatOperation
  simp only
  generalize match_1 _ name _ _ _ _ _ _ _ = binaryName
  generalize match_3 _ name _ _ _ _ _ _ = castName
  generalize match_5 _ name _ _ _ _ _ _ _ _ = orderName
  rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, t⟩⟩⟩
  · cases binaryName <;> cases castName <;> cases orderName <;> rfl
  · cases binaryName <;> cases castName <;> cases orderName <;>
      simp only [widthOf_rel context h1, floatCall_rel context _ _ (.cons h1 .nil)]
  · cases binaryName <;> cases castName <;> cases orderName <;>
      simp only [roundingMode_rel h1, widthOf_rel context h1, widthOf_rel context h2,
        floatCall_rel context _ _ (.cons h2 .nil), floatCall_rel context _ _ (.cons h1 (.cons h2 .nil))]
  · rcases t with _ | ⟨h4, t⟩
    · cases binaryName <;> cases castName <;> cases orderName <;>
        simp only [roundingMode_rel h1, expectNat_rel h2, widthOf_rel context h1, widthOf_rel context h2, widthOf_rel context h3,
          floatCall_rel context _ _ (.cons h3 .nil), floatCall_rel context _ _ (.cons h2 (.cons h3 .nil)),
          floatCall_rel context _ _ (.cons h1 (.cons h2 (.cons h3 .nil)))]
    · cases binaryName <;> cases castName <;> cases orderName <;>
        simp only [roundingMode_rel h1, widthOf_rel context h1, widthOf_rel context h2,
          floatCall_rel context _ _ (.cons h2 (.cons h3 (.cons h4 t))), floatCall_rel context _ _ (.cons h1 (.cons h2 (.cons h3 (.cons h4 t))))]

/-! ### Primitives

The result of a primitive is the same but for the values it hands on, and the code it makes is the same. -/

/-- Two results of a primitive with the same code, and values the same up to compilation. -/
def PrimRel (names : String → Option SV) (first second : Except String (SV × Bil.Program)) : Prop :=
  ∀ value code, first = .ok (value, code) → ∃ other, second = .ok (other, code) ∧ ValueRel names value other

theorem PrimRel.of_eq {first second : Except String (SV × Bil.Program)} (h : first = second) : PrimRel names first second := by
  intro value code he
  exact ⟨value, h ▸ he, ValueRel.refl _⟩

theorem PrimRel.value {first second : SV} (h : ValueRel names first second) : PrimRel names (valueOnly first) (valueOnly second) := by
  intro value code he
  simp only [valueOnly, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨second, rfl, h⟩

/-- A primitive whose result is a value it was given and the code of an assignment. -/
theorem set_rel (context : Context) {a b c d : SV} (h1 : ValueRel names a b) (h2 : ValueRel names c d) :
    PrimRel names
      (do
        let lifted ← assign context a c
        pure (c, lifted))
      (do
        let lifted ← assign context b d
        pure (d, lifted)) := by
  intro value code he
  rw [assign_rel context h1 h2] at he
  cases hx : assign context b d with
  | error => rw [hx] at he; cases he
  | ok x =>
    rw [hx] at he
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, rfl, h2⟩

theorem applyPrimitive_rel (context : Context) (name : String) {a b : List SV} (h : ListRel names a b) :
    PrimRel names (applyPrimitive context name a) (applyPrimitive context name b) := by
  unfold applyPrimitive
  split
  all_goals first
    | exact PrimRel.of_eq rfl
    | (refine PrimRel.of_eq ?_
       simp only [binary_rel context _ h, compare_rel context _ h, unaryNot_rel context h, leadingZeros_rel context h, shift_rel context _ h,
         cast_rel context _ h, wordWidth_rel context h, loadMemory_rel context _ h, storeMemory_rel context h, symbolConcat_rel h,
         castSaturate_rel context h, floatOperation_rel context _ h]
       done)
    | (refine PrimRel.of_eq ?_
       rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, t⟩⟩⟩⟩
       · rfl
       · first | rfl | (simp only [expectBil_rel context h1]; done)
       · first | rfl | (simp only [expectBil_rel context h1, expectBil_rel context h2, expectNat_rel h1, expectNat_rel h2,
           loadMemory_rel context _ (.cons h2 .nil), storeMemory_rel context (.cons h1 (.cons (ValueRel.refl _) .nil))]; done)
       · first | rfl | (simp only [expectBil_rel context h3, expectNat_rel h1, expectNat_rel h2]; done)
       · rfl
       done)
    | skip
  case h_3 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
    · exact PrimRel.of_eq rfl
    · exact PrimRel.of_eq (by simp only [expectBil_rel context h1])
    · exact PrimRel.of_eq (by simp only [binary_rel context _ (.cons h1 (.cons h2 t))])
  case h_39 =>
    rcases h with _ | ⟨h1, t⟩
    · exact PrimRel.of_eq rfl
    · refine PrimRel.of_eq ?_
      simp only [expectBil_rel context h1]
      cases expectBil context _ with
      | error => rfl
      | ok x =>
        simp only [bind, Except.bind]
        rw [foldlM_concat_rel context _ t]
  case h_41 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, t⟩⟩⟩
    · exact PrimRel.of_eq rfl
    · exact PrimRel.of_eq rfl
    · exact set_rel context h1 h2
    · exact PrimRel.of_eq rfl
  case h_42 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, t⟩⟩⟩
    · exact PrimRel.of_eq rfl
    · exact PrimRel.of_eq rfl
    · exact set_rel context h1 h2
    · exact PrimRel.of_eq rfl
  case h_43 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, t⟩⟩⟩
    · exact PrimRel.of_eq rfl
    · exact PrimRel.of_eq rfl
    · exact set_rel context h1 h2
    · exact PrimRel.of_eq rfl
  case h_44 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
    · exact PrimRel.of_eq rfl
    · cases h1 <;> exact PrimRel.of_eq rfl
    · cases h1 <;> exact PrimRel.of_eq rfl
  case h_45 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
    · exact PrimRel.of_eq rfl
    · cases h1 <;> exact PrimRel.of_eq rfl
    · cases h1 <;> exact PrimRel.of_eq rfl
  case h_53 =>
    rcases h with _ | ⟨h1, t⟩
    · exact PrimRel.of_eq rfl
    · cases h1
      case symbol => exact PrimRel.of_eq (intrinsicCall_rel context _ t)
      all_goals exact PrimRel.of_eq rfl
  case h_55 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
    · exact PrimRel.of_eq rfl
    · cases h1 <;> exact PrimRel.of_eq rfl
    · cases h1 <;> exact PrimRel.of_eq rfl
  case h_58 =>
    cases context.prefixes <;> rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
    · exact PrimRel.of_eq rfl
    · exact PrimRel.of_eq rfl
    · exact PrimRel.of_eq rfl
    · exact PrimRel.of_eq rfl
    · exact PrimRel.of_eq (by simp only [expectNat_rel h1])
    · exact PrimRel.of_eq rfl
  case h_82 => exact PrimRel.value (.list h)
  case h_83 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, t⟩⟩⟩
    · exact PrimRel.of_eq rfl
    · exact PrimRel.of_eq rfl
    · cases h2
      case list hl => exact PrimRel.value (.list (.cons h1 hl))
      all_goals exact PrimRel.of_eq rfl
    · cases h1 <;> cases h2 <;> exact PrimRel.of_eq rfl
  case h_84 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
    · exact PrimRel.of_eq rfl
    · cases h1
      case list hl =>
        cases hl with
        | nil => exact PrimRel.of_eq rfl
        | cons hh ht => exact PrimRel.value hh
      all_goals exact PrimRel.of_eq rfl
    · cases h1
      case list hl => cases hl <;> exact PrimRel.of_eq rfl
      all_goals exact PrimRel.of_eq rfl
  case h_85 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
    · exact PrimRel.of_eq rfl
    · cases h1
      case list hl =>
        cases hl with
        | nil => exact PrimRel.of_eq rfl
        | cons hh ht => exact PrimRel.value (.list ht)
      all_goals exact PrimRel.of_eq rfl
    · cases h1
      case list hl => cases hl <;> exact PrimRel.of_eq rfl
      all_goals exact PrimRel.of_eq rfl
  case h_86 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
    · exact PrimRel.of_eq rfl
    · cases h1
      case list hl => exact PrimRel.of_eq (by simp only [hl.length_eq])
      all_goals exact PrimRel.of_eq rfl
    · cases h1 <;> exact PrimRel.of_eq rfl
  case h_87 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
    · exact PrimRel.of_eq rfl
    · cases h1
      case list hl => cases hl <;> exact PrimRel.of_eq rfl
      all_goals exact PrimRel.of_eq rfl
    · cases h1 <;> exact PrimRel.of_eq rfl
  case h_88 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
    · exact PrimRel.of_eq rfl
    · cases h1 <;> exact PrimRel.of_eq rfl
    · cases h1 <;> exact PrimRel.of_eq rfl

theorem applyPrimitiveIndex_rel (context : Context) (operation : Nat) {a b : List SV} (h : ListRel names a b) :
    PrimRel names (applyPrimitiveIndex context operation a) (applyPrimitiveIndex context operation b) := by
  unfold applyPrimitiveIndex
  split
  all_goals first
    | exact PrimRel.of_eq rfl
    | (refine PrimRel.of_eq ?_
       simp only [binary_rel context _ h, compare_rel context _ h, unaryNot_rel context h, leadingZeros_rel context h, shift_rel context _ h,
         cast_rel context _ h, wordWidth_rel context h, loadMemory_rel context _ h, storeMemory_rel context h]
       done)
    | (refine PrimRel.of_eq ?_
       rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, t⟩⟩⟩⟩
       · rfl
       · first | rfl | (simp only [expectBil_rel context h1]; done)
       · first | rfl | (simp only [expectBil_rel context h1, expectBil_rel context h2, expectNat_rel h1,
           loadMemory_rel context _ (.cons h2 .nil), storeMemory_rel context (.cons h1 (.cons (ValueRel.refl _) .nil))]; done)
       · first | rfl | (simp only [expectBil_rel context h3, expectNat_rel h1, expectNat_rel h2]; done)
       · rfl
       done)
    | skip
  case h_2 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
    · exact PrimRel.of_eq rfl
    · exact PrimRel.of_eq (by simp only [expectBil_rel context h1])
    · exact PrimRel.of_eq (by simp only [binary_rel context _ (.cons h1 (.cons h2 t))])
  case h_26 =>
    rcases h with _ | ⟨h1, t⟩
    · exact PrimRel.of_eq rfl
    · refine PrimRel.of_eq ?_
      simp only [expectBil_rel context h1]
      cases expectBil context _ with
      | error => rfl
      | ok x =>
        simp only [bind, Except.bind]
        rw [foldlM_concat_rel context _ t]
  case h_32 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, t⟩⟩⟩
    · exact PrimRel.of_eq rfl
    · exact PrimRel.of_eq rfl
    · exact set_rel context h1 h2
    · exact PrimRel.of_eq rfl
  case h_33 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, t⟩⟩⟩
    · exact PrimRel.of_eq rfl
    · exact PrimRel.of_eq rfl
    · exact set_rel context h1 h2
    · exact PrimRel.of_eq rfl
  case h_34 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, t⟩⟩⟩
    · exact PrimRel.of_eq rfl
    · exact PrimRel.of_eq rfl
    · exact set_rel context h1 h2
    · exact PrimRel.of_eq rfl
  case h_35 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
    · exact PrimRel.of_eq rfl
    · cases h1 <;> exact PrimRel.of_eq rfl
    · cases h1 <;> exact PrimRel.of_eq rfl
  case h_36 =>
    rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
    · exact PrimRel.of_eq rfl
    · cases h1 <;> exact PrimRel.of_eq rfl
    · cases h1 <;> exact PrimRel.of_eq rfl

end Bap.Proofs.Primus
