import Bap.Bil.Semantics
import Bap.Bil.Transform
import Bap.Bil.Observe
import Bap.Bil.Wire
import Bap.Proofs.Core
import Lean.Elab.Command

set_option linter.unusedSimpArgs false

namespace Bap.Proofs.Bil
open Bap.Bil

open Lean Elab Command in
/-- Brings `private` declarations of an imported module into scope under their short names. -/
local elab "open_private " m:ident names:ident* : command => do
  for n in names do
    let full := n.getId
    let decl := mkPrivateNameCore m.getId full
    modifyScope fun s => { s with openDecls := .explicit (Name.mkSimple full.getString!) decl :: s.openDecls }

open Lean Elab Command in
/-- As `open_private`, under a chosen short name, for clashing private declarations. -/
local elab "open_private_as " m:ident full:ident short:ident : command => do
  let decl := mkPrivateNameCore m.getId full.getId
  modifyScope fun s => { s with openDecls := .explicit short.getId decl :: s.openDecls }

/-! ## Environments -/

private theorem find?_bind_other (env : Env) {var other : Bap.Var} (value : Value) (h : other ≠ var) :
    (Bap.Bil.bind env var value).find? (fun binding => binding.1 == other) =
      env.find? (fun binding => binding.1 == other) := by
  have hv : (var == other) = false := by simpa using h.symm
  simp only [Bap.Bil.bind, List.find?_cons, hv]
  induction env with
  | nil => simp
  | cons head rest ih =>
    obtain ⟨k, v⟩ := head
    by_cases hk : k = var
    · subst hk
      simp [hv, ih]
    · by_cases hko : k = other
      · subst hko; simp [hk]
      · simp [List.filter_cons, hk, hko, ih]

theorem lookup_bind_other (env : Env) {var other : Bap.Var} (value : Value) (h : other ≠ var) :
    lookup (Bap.Bil.bind env var value) other = lookup env other := by
  simp only [lookup, find?_bind_other env value h]

theorem lookup_bind_eq (env : Env) (var other : Bap.Var) (value : Value) :
    lookup (Bap.Bil.bind env var value) other = if other = var then .ok value else lookup env other := by
  by_cases h : other = var
  · subst h; simp [lookup, Bap.Bil.bind]
  · simp [h, lookup_bind_other env value h]

/-- Rebinding a variable makes the old binding unobservable. -/
theorem lookup_bind_bind (env : Env) (var other : Bap.Var) (old new : Value) :
    lookup (Bap.Bil.bind (Bap.Bil.bind env var old) var new) other = lookup (Bap.Bil.bind env var new) other := by
  simp only [lookup_bind_eq]
  by_cases h : other = var <;> simp [h]

theorem lookup_bind_comm (env : Env) {first second : Bap.Var} (h : first ≠ second) (x y : Value) (other : Bap.Var) :
    lookup (Bap.Bil.bind (Bap.Bil.bind env first x) second y) other =
      lookup (Bap.Bil.bind (Bap.Bil.bind env second y) first x) other := by
  simp only [lookup_bind_eq]
  by_cases h1 : other = first
  · subst h1; simp [h]
  · simp [h1]

theorem mem_of_lookup {env : Env} {var : Bap.Var} {value : Value} (h : lookup env var = .ok value) :
    (var, value) ∈ env := by
  simp only [lookup] at h
  split at h
  · rename_i binding hf
    simp only [Except.ok.injEq] at h
    subst h
    have hmem := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    simp only [beq_iff_eq] at hk
    obtain ⟨k, v⟩ := binding
    simp only at hk
    subst hk
    exact hmem
  · simp at h

private theorem foldl_latest_lookup (updates acc : List (Bap.Var × Value)) (other : Bap.Var) :
    (updates.foldl (init := acc) fun current update =>
        update :: current.filter (fun binding => binding.1 != update.1)).find? (fun b => b.1 == other) =
      match (updates.reverse.find? (fun b => b.1 == other)) with
      | some binding => some binding
      | none => acc.find? (fun b => b.1 == other) := by
  induction updates generalizing acc with
  | nil => simp
  | cons update rest ih =>
    rw [List.foldl_cons, ih, List.reverse_cons, List.find?_append]
    cases hr : rest.reverse.find? (fun b => b.1 == other) with
    | some binding => simp
    | none =>
      obtain ⟨k, v⟩ := update
      by_cases hk : k = other
      · subst hk; simp
      · have hbeq : (k == other) = false := by simpa using hk
        have := find?_bind_other acc (var := k) (other := other) v (Ne.symm hk)
        simp only [Bap.Bil.bind] at this
        simp only [List.find?_cons, hbeq, List.find?_nil, Option.or_none, this]

private theorem find?_filter_not (names : List Bap.Var) (env : Env) (other : Bap.Var) :
    (env.filter fun binding => !names.contains binding.1).find? (fun b => b.1 == other) =
      if other ∈ names then none else env.find? (fun b => b.1 == other) := by
  by_cases hm : other ∈ names
  · simp only [hm, ite_true]
    apply List.find?_eq_none.mpr
    intro entry hentry
    have := (List.mem_filter.mp hentry).2
    intro heq
    simp only [beq_iff_eq] at heq
    simp [heq, hm] at this
  · simp only [hm, ite_false]
    induction env with
    | nil => simp
    | cons head rest ih =>
      obtain ⟨k, v⟩ := head
      by_cases hk : k ∈ names
      · have hko : (k == other) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          rintro rfl
          exact hm hk
        have hc : names.contains k = true := by simpa using hk
        simp only [List.filter_cons, hc, Bool.not_true, Bool.false_eq_true, ite_false, List.find?_cons, hko, ih]
      · have hc : names.contains k = false := by simpa using hk
        simp only [List.filter_cons, hc, Bool.not_false, ite_true, List.find?_cons, ih]

/-- Parallel `bindMany` agrees with folding `bind`, so later updates win. -/
theorem lookup_bindMany (env : Env) (updates : List (Bap.Var × Value)) (other : Bap.Var) :
    lookup (bindMany env updates) other =
      lookup (updates.foldl (fun env update => Bap.Bil.bind env update.1 update.2) env) other := by
  have hfold : ∀ (env : Env) (updates : List (Bap.Var × Value)),
      (updates.foldl (fun env update => Bap.Bil.bind env update.1 update.2) env).find?
          (fun b => b.1 == other) =
        match updates.reverse.find? (fun b => b.1 == other) with
        | some binding => some binding
        | none => env.find? (fun b => b.1 == other) := by
    intro env updates
    induction updates generalizing env with
    | nil => simp
    | cons update rest ih =>
      rw [List.foldl_cons, ih, List.reverse_cons, List.find?_append]
      cases hr : rest.reverse.find? (fun b => b.1 == other) with
      | some binding => simp
      | none =>
        obtain ⟨k, v⟩ := update
        by_cases hk : k = other
        · subst hk; simp [Bap.Bil.bind]
        · have hbeq : (k == other) = false := by simpa using hk
          simp [find?_bind_other env v (Ne.symm hk), hbeq]
  have hrev : updates.reverse.find? (fun b => b.1 == other) = none → other ∉ updates.map Prod.fst := by
    intro hr hm
    obtain ⟨⟨k, v⟩, hmem, hk⟩ := List.mem_map.mp hm
    simp only at hk
    subst hk
    have := List.find?_eq_none.mp hr (k, v) (List.mem_reverse.mpr hmem)
    simp at this
  simp only [lookup]
  rw [hfold]
  simp only [bindMany]
  rw [List.find?_append, foldl_latest_lookup, find?_filter_not]
  cases hr : updates.reverse.find? (fun b => b.1 == other) with
  | some binding => simp
  | none => simp [hrev hr]

/-- Environment extension: everything `env` binds, `env'` binds to the same value. -/
def Extends (env env' : Env) : Prop :=
  ∀ var value, lookup env var = .ok value → lookup env' var = .ok value

theorem nil_extends (env : Env) : Extends [] env := by
  intro var value h
  simp [lookup] at h

theorem Extends.bind {env env' : Env} (h : Extends env env') (var : Bap.Var) (value : Value) :
    Extends (Bap.Bil.bind env var value) (Bap.Bil.bind env' var value) := by
  intro other result hl
  rw [lookup_bind_eq] at hl ⊢
  by_cases he : other = var
  · simpa [he] using hl
  · simp only [he, ite_false] at hl ⊢
    exact h _ _ hl

/-! ## Evaluation inversion -/

open_private Bap.Bil.Eval Bap.Bil.expectMemory Bap.Bil.evalUn

private theorem except_bind_ok {x : Except String α} {f : α → Except String β} {r : β} :
    (x >>= f) = .ok r ↔ ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => simp [Bind.bind, Except.bind]
  | ok a => simp [Bind.bind, Except.bind]

private theorem asBits_ok {value : Value} {w : Nat} {b : BitVec w} :
    Value.asBits value = .ok ⟨w, b⟩ ↔ value = .bits b := by
  cases value with
  | bits c =>
    constructor
    · intro h
      simp only [Value.asBits, Except.ok.injEq] at h
      cases h; rfl
    · intro h; cases h; rfl
  | memory m => simp [Value.asBits]
  | undefined => simp [Value.asBits]

private theorem expectMemory_ok {value : Value} {w : Nat} {m : Memory w} :
    expectMemory value = .ok ⟨w, m⟩ ↔ value = .memory m := by
  cases value with
  | memory c =>
    constructor
    · intro h
      simp only [expectMemory, Except.ok.injEq] at h
      cases h; rfl
    · intro h; cases h; rfl
  | bits b => simp [expectMemory]
  | undefined => simp [expectMemory]

/-- Results of `evalExp`, inverted one constructor at a time. -/
theorem eval_load_iff {env : Env} {memory address : Exp} {endian : Endian} {size : Nat} {result : Value} :
    evalExp env (.load memory address endian size) = .ok result ↔
      ∃ (w : Nat) (m : Memory w) (a : BitVec w), evalExp env memory = .ok (.memory m) ∧
        evalExp env address = .ok (.bits a) ∧ result = .bits (Memory.read m a endian size) := by
  simp only [evalExp, except_bind_ok]
  constructor
  · rintro ⟨mv, hm, ⟨w, m⟩, hexp, av, ha, ⟨aw, addr⟩, hbits, hif⟩
    rw [expectMemory_ok] at hexp
    rw [asBits_ok] at hbits
    subst hexp hbits
    simp only at hif
    split at hif
    · rename_i h
      cases h
      simp only [Except.ok.injEq] at hif
      exact ⟨w, m, addr, hm, ha, hif.symm⟩
    · simp at hif
  · rintro ⟨w, m, a, hm, ha, rfl⟩
    exact ⟨_, hm, ⟨w, m⟩, rfl, _, ha, ⟨w, a⟩, rfl, by simp⟩

theorem eval_store_iff {env : Env} {memory address value : Exp} {endian : Endian} {size : Nat} {result : Value} :
    evalExp env (.store memory address value endian size) = .ok result ↔
      ∃ (w : Nat) (m : Memory w) (a : BitVec w) (vw : Nat) (v : BitVec vw) (updated : Memory w),
        evalExp env memory = .ok (.memory m) ∧ evalExp env address = .ok (.bits a) ∧
        evalExp env value = .ok (.bits v) ∧ Memory.write m a v endian size = .ok updated ∧
        result = .memory updated := by
  simp only [evalExp, except_bind_ok]
  constructor
  · rintro ⟨mv, hm, ⟨w, m⟩, hexp, av, ha, ⟨aw, addr⟩, hbits, vv, hv, ⟨vw, v⟩, hvb, hif⟩
    rw [expectMemory_ok] at hexp
    rw [asBits_ok] at hbits hvb
    subst hexp hbits hvb
    simp only at hif
    split at hif
    · rename_i h
      cases h
      obtain ⟨updated, hw, hr⟩ := except_bind_ok.mp hif
      simp only [Except.ok.injEq] at hr
      exact ⟨w, m, addr, vw, v, updated, hm, ha, hv, hw, hr.symm⟩
    · simp at hif
  · rintro ⟨w, m, a, vw, v, updated, hm, ha, hv, hw, rfl⟩
    refine ⟨_, hm, ⟨w, m⟩, rfl, _, ha, ⟨w, a⟩, rfl, _, hv, ⟨vw, v⟩, rfl, ?_⟩
    simp only [↓reduceDIte]
    exact except_bind_ok.mpr ⟨_, hw, rfl⟩

theorem eval_bin_iff {env : Env} {op : BinOp} {left right : Exp} {result : Value} :
    evalExp env (.bin op left right) = .ok result ↔
      ∃ (lw rw : Nat) (a : BitVec lw) (b : BitVec rw), evalExp env left = .ok (.bits a) ∧
        evalExp env right = .ok (.bits b) ∧ evalBin op ⟨lw, a⟩ ⟨rw, b⟩ = .ok result := by
  simp only [evalExp, except_bind_ok]
  constructor
  · rintro ⟨lv, hl, ⟨lw, a⟩, hla, rv, hr, ⟨rw, b⟩, hrb, he⟩
    rw [asBits_ok] at hla hrb
    subst hla hrb
    exact ⟨lw, rw, a, b, hl, hr, he⟩
  · rintro ⟨lw, rw, a, b, hl, hr, he⟩
    exact ⟨_, hl, ⟨lw, a⟩, rfl, _, hr, ⟨rw, b⟩, rfl, he⟩

/-- Pure result of a unary operator on a bitvector. -/
def unValue (op : UnOp) (b : BitVec w) : Value :=
  match op with
  | .neg => .bits (-b)
  | .not => .bits (~~~b)

theorem eval_un_iff {env : Env} {op : UnOp} {value : Exp} {result : Value} :
    evalExp env (.un op value) = .ok result ↔
      ∃ (w : Nat) (b : BitVec w), evalExp env value = .ok (.bits b) ∧ result = unValue op b := by
  simp only [evalExp, except_bind_ok]
  constructor
  · rintro ⟨v, hv, ⟨w, b⟩, hb, he⟩
    rw [asBits_ok] at hb
    subst hb
    simp only [Except.ok.injEq] at he
    exact ⟨w, b, hv, by rw [← he]; cases op <;> rfl⟩
  · rintro ⟨w, b, hv, rfl⟩
    exact ⟨_, hv, ⟨w, b⟩, rfl, by cases op <;> rfl⟩

/-- Pure result of a cast applied to a bitvector. -/
def castValue (kind : Cast) (width : Nat) (b : BitVec w) : Except String Value :=
  match kind with
  | .low => .ok (.bits (Word.low width b))
  | .unsigned => .ok (.bits (Word.unsigned width b))
  | .signed => .ok (.bits (Word.signed width b))
  | .high => do
    let result ← Word.high width b
    .ok (.bits result)

theorem eval_cast_iff {env : Env} {kind : Cast} {width : Nat} {value : Exp} {result : Value} :
    evalExp env (.cast kind width value) = .ok result ↔
      ∃ (w : Nat) (b : BitVec w), evalExp env value = .ok (.bits b) ∧ castValue kind width b = .ok result := by
  simp only [evalExp, except_bind_ok]
  constructor
  · rintro ⟨v, hv, ⟨w, b⟩, hb, he⟩
    rw [asBits_ok] at hb
    subst hb
    exact ⟨w, b, hv, by cases kind <;> exact he⟩
  · rintro ⟨w, b, hv, he⟩
    exact ⟨_, hv, ⟨w, b⟩, rfl, by cases kind <;> exact he⟩

theorem eval_let_iff {env : Env} {var : Bap.Var} {value body : Exp} {result : Value} :
    evalExp env (.letIn var value body) = .ok result ↔
      ∃ v, evalExp env value = .ok v ∧ evalExp (Bap.Bil.bind env var v) body = .ok result := by
  simp only [evalExp, except_bind_ok]

theorem eval_ite_iff {env : Env} {condition yes no : Exp} {result : Value} :
    evalExp env (.ite condition yes no) = .ok result ↔
      ∃ c : BitVec 1, evalExp env condition = .ok (.bits c) ∧
        evalExp env (if c = 1 then yes else no) = .ok result := by
  simp only [evalExp, except_bind_ok]
  constructor
  · rintro ⟨v, hv, ⟨w, b⟩, hb, he⟩
    rw [asBits_ok] at hb
    subst hb
    simp only at he
    split at he
    · rename_i h
      cases h
      refine ⟨b, hv, ?_⟩
      rw [apply_ite (evalExp env)]
      exact he
    · simp at he
  · rintro ⟨c, hv, he⟩
    refine ⟨_, hv, ⟨1, c⟩, rfl, ?_⟩
    rw [apply_ite (evalExp env)] at he
    exact he

theorem eval_extract_iff {env : Env} {high low : Nat} {value : Exp} {result : Value} :
    evalExp env (.extract high low value) = .ok result ↔
      ∃ (w : Nat) (b : BitVec w) (x : BitVec (high - low + 1)), evalExp env value = .ok (.bits b) ∧
        Word.extract high low b = .ok x ∧ result = .bits x := by
  simp only [evalExp, except_bind_ok]
  constructor
  · rintro ⟨v, hv, ⟨w, b⟩, hb, x, hx, he⟩
    rw [asBits_ok] at hb
    subst hb
    simp only [Except.ok.injEq] at he
    exact ⟨w, b, x, hv, hx, he.symm⟩
  · rintro ⟨w, b, x, hv, hx, rfl⟩
    exact ⟨_, hv, ⟨w, b⟩, rfl, x, hx, rfl⟩

theorem eval_concat_iff {env : Env} {left right : Exp} {result : Value} :
    evalExp env (.concat left right) = .ok result ↔
      ∃ (lw rw : Nat) (a : BitVec lw) (b : BitVec rw), evalExp env left = .ok (.bits a) ∧
        evalExp env right = .ok (.bits b) ∧ result = .bits (Word.concat a b) := by
  simp only [evalExp, except_bind_ok]
  constructor
  · rintro ⟨lv, hl, ⟨lw, a⟩, hla, rv, hr, ⟨rw, b⟩, hrb, he⟩
    rw [asBits_ok] at hla hrb
    subst hla hrb
    simp only [Except.ok.injEq] at he
    exact ⟨lw, rw, a, b, hl, hr, he.symm⟩
  · rintro ⟨lw, rw, a, b, hl, hr, rfl⟩
    exact ⟨_, hl, ⟨lw, a⟩, rfl, _, hr, ⟨rw, b⟩, rfl, rfl⟩

/-- Evaluation is monotone in the environment: a result computed from fewer bindings still holds
when more are available. -/
theorem evalExp_extends {env env' : Env} (h : Extends env env') (exp : Exp) {result : Value}
    (he : evalExp env exp = .ok result) : evalExp env' exp = .ok result := by
  induction exp generalizing env env' result with
  | int value => exact he
  | var var => exact h _ _ he
  | unknown message typ => simp [evalExp] at he
  | load memory address endian size ihm iha =>
    obtain ⟨w, m, a, hm, ha, rfl⟩ := eval_load_iff.mp he
    exact eval_load_iff.mpr ⟨w, m, a, ihm h hm, iha h ha, rfl⟩
  | store memory address value endian size ihm iha ihv =>
    obtain ⟨w, m, a, vw, v, u, hm, ha, hv, hw, rfl⟩ := eval_store_iff.mp he
    exact eval_store_iff.mpr ⟨w, m, a, vw, v, u, ihm h hm, iha h ha, ihv h hv, hw, rfl⟩
  | bin op left right ihl ihr =>
    obtain ⟨lw, rw, a, b, hl, hr, hb⟩ := eval_bin_iff.mp he
    exact eval_bin_iff.mpr ⟨lw, rw, a, b, ihl h hl, ihr h hr, hb⟩
  | un op value ih =>
    obtain ⟨w, b, hv, rfl⟩ := eval_un_iff.mp he
    exact eval_un_iff.mpr ⟨w, b, ih h hv, rfl⟩
  | cast kind width value ih =>
    obtain ⟨w, b, hv, hc⟩ := eval_cast_iff.mp he
    exact eval_cast_iff.mpr ⟨w, b, ih h hv, hc⟩
  | letIn var value body ihv ihb =>
    obtain ⟨v, hv, hb⟩ := eval_let_iff.mp he
    exact eval_let_iff.mpr ⟨v, ihv h hv, ihb (h.bind var v) hb⟩
  | ite condition yes no ihc ihy ihn =>
    obtain ⟨c, hc, hb⟩ := eval_ite_iff.mp he
    refine eval_ite_iff.mpr ⟨c, ihc h hc, ?_⟩
    by_cases hc1 : c = 1
    · simp only [hc1, ite_true] at hb ⊢
      exact ihy h hb
    · simp only [hc1, ite_false] at hb ⊢
      exact ihn h hb
  | extract high low value ih =>
    obtain ⟨w, b, x, hv, hx, rfl⟩ := eval_extract_iff.mp he
    exact eval_extract_iff.mpr ⟨w, b, x, ih h hv, hx, rfl⟩
  | concat left right ihl ihr =>
    obtain ⟨lw, rw, a, b, hl, hr, rfl⟩ := eval_concat_iff.mp he
    exact eval_concat_iff.mpr ⟨lw, rw, a, b, ihl h hl, ihr h hr, rfl⟩

/-! ## Free variables, substitution, constant folding -/

open_private Bap.Bil.Transform Bap.Bil.union Bap.Bil.freeVarsExp

private theorem mem_union {v : Bap.Var} {left right : List Bap.Var} :
    v ∈ union left right ↔ v ∈ left ∨ v ∈ right := by
  simp [union, List.mem_eraseDups]

private theorem not_mem_freeVarsExp_of_mem {v : Bap.Var} {bound : List Bap.Var} (exp : Exp) (h : v ∈ bound) :
    v ∉ freeVarsExp bound exp := by
  induction exp generalizing bound with
  | int value => simp [freeVarsExp]
  | unknown message typ => simp [freeVarsExp]
  | var var =>
    simp only [freeVarsExp]
    split
    · simp
    · rename_i hn
      simp only [List.mem_singleton]
      rintro rfl
      exact hn h
  | load _ _ _ _ ih1 ih2 => simp only [freeVarsExp, mem_union]; simp [ih1 h, ih2 h]
  | store _ _ _ _ _ ih1 ih2 ih3 => simp only [freeVarsExp, mem_union]; simp [ih1 h, ih2 h, ih3 h]
  | bin _ _ _ ih1 ih2 => simp only [freeVarsExp, mem_union]; simp [ih1 h, ih2 h]
  | un _ _ ih => simpa only [freeVarsExp] using ih h
  | cast _ _ _ ih => simpa only [freeVarsExp] using ih h
  | letIn var _ _ ih1 ih2 =>
    simp only [freeVarsExp, mem_union]
    simp [ih1 h, ih2 (List.mem_cons_of_mem _ h)]
  | ite _ _ _ ih1 ih2 ih3 => simp only [freeVarsExp, mem_union]; simp [ih1 h, ih2 h, ih3 h]
  | extract _ _ _ ih => simpa only [freeVarsExp] using ih h
  | concat _ _ ih1 ih2 => simp only [freeVarsExp, mem_union]; simp [ih1 h, ih2 h]

private theorem mem_freeVarsExp_cons {v var : Bap.Var} {bound : List Bap.Var} {exp : Exp}
    (h : v ∈ freeVarsExp (var :: bound) exp) : v ≠ var := by
  rintro rfl
  exact not_mem_freeVarsExp_of_mem exp (List.mem_cons_self) h

private theorem evalExp_congr_aux (exp : Exp) (bound : List Bap.Var) (env env' : Env)
    (hbound : ∀ v ∈ bound, lookup env v = lookup env' v)
    (hfree : ∀ v ∈ freeVarsExp bound exp, lookup env v = lookup env' v) :
    evalExp env exp = evalExp env' exp := by
  induction exp generalizing bound env env' with
  | int value => rfl
  | unknown message typ => rfl
  | var var =>
    simp only [evalExp]
    by_cases hv : var ∈ bound
    · exact hbound _ hv
    · exact hfree _ (by simp [freeVarsExp, hv])
  | load memory address _ _ ih1 ih2 =>
    simp only [freeVarsExp, mem_union] at hfree
    simp only [evalExp, ih1 bound env env' hbound (fun v h => hfree v (Or.inl h)),
      ih2 bound env env' hbound (fun v h => hfree v (Or.inr h))]
  | store memory address value _ _ ih1 ih2 ih3 =>
    simp only [freeVarsExp, mem_union] at hfree
    simp only [evalExp, ih1 bound env env' hbound (fun v h => hfree v (Or.inl (Or.inl h))),
      ih2 bound env env' hbound (fun v h => hfree v (Or.inl (Or.inr h))),
      ih3 bound env env' hbound (fun v h => hfree v (Or.inr h))]
  | bin op left right ih1 ih2 =>
    simp only [freeVarsExp, mem_union] at hfree
    simp only [evalExp, ih1 bound env env' hbound (fun v h => hfree v (Or.inl h)),
      ih2 bound env env' hbound (fun v h => hfree v (Or.inr h))]
  | concat left right ih1 ih2 =>
    simp only [freeVarsExp, mem_union] at hfree
    simp only [evalExp, ih1 bound env env' hbound (fun v h => hfree v (Or.inl h)),
      ih2 bound env env' hbound (fun v h => hfree v (Or.inr h))]
  | un op value ih =>
    simp only [freeVarsExp] at hfree
    simp only [evalExp, ih bound env env' hbound hfree]
  | cast kind width value ih =>
    simp only [freeVarsExp] at hfree
    simp only [evalExp, ih bound env env' hbound hfree]
  | extract high low value ih =>
    simp only [freeVarsExp] at hfree
    simp only [evalExp, ih bound env env' hbound hfree]
  | letIn var value body ih1 ih2 =>
    simp only [freeVarsExp, mem_union] at hfree
    simp only [evalExp, ih1 bound env env' hbound (fun v h => hfree v (Or.inl h))]
    congr 1
    funext result
    apply ih2 (var :: bound)
    · intro v hv
      rw [lookup_bind_eq, lookup_bind_eq]
      by_cases he : v = var
      · simp [he]
      · simp only [he, ite_false]
        exact hbound v ((List.mem_cons.mp hv).resolve_left he)
    · intro v hv
      rw [lookup_bind_other _ _ (mem_freeVarsExp_cons hv), lookup_bind_other _ _ (mem_freeVarsExp_cons hv)]
      exact hfree v (Or.inr hv)
  | ite condition yes no ih1 ih2 ih3 =>
    simp only [freeVarsExp, mem_union] at hfree
    simp only [evalExp, ih1 bound env env' hbound (fun v h => hfree v (Or.inl (Or.inl h))),
      ih2 bound env env' hbound (fun v h => hfree v (Or.inl (Or.inr h))),
      ih3 bound env env' hbound (fun v h => hfree v (Or.inr h))]

/-- Evaluation depends only on the bindings of the free variables. -/
theorem evalExp_congr_freeVars (exp : Exp) {env env' : Env}
    (h : ∀ v ∈ freeVars exp, lookup env v = lookup env' v) : evalExp env exp = evalExp env' exp :=
  evalExp_congr_aux exp [] env env' (by simp) h

theorem occursFree_iff_mem_freeVarsExp (v : Bap.Var) (bound : List Bap.Var) (exp : Exp) :
    v ∈ freeVarsExp bound exp ↔ v ∉ bound ∧ occursFree v exp = true := by
  induction exp generalizing bound with
  | int value => simp [freeVarsExp, occursFree]
  | unknown message typ => simp [freeVarsExp, occursFree]
  | var var =>
    by_cases hv : var ∈ bound
    · simp only [freeVarsExp, hv, ite_true, occursFree, List.not_mem_nil, false_iff, not_and, beq_iff_eq]
      rintro hn rfl
      exact hn hv
    · simp only [freeVarsExp, hv, ite_false, occursFree, List.mem_singleton, beq_iff_eq]
      constructor
      · rintro rfl; exact ⟨hv, rfl⟩
      · rintro ⟨_, rfl⟩; rfl
  | load _ _ _ _ ih1 ih2 => simp only [freeVarsExp, occursFree, mem_union, ih1, ih2, Bool.or_eq_true]; grind
  | store _ _ _ _ _ ih1 ih2 ih3 => simp only [freeVarsExp, occursFree, mem_union, ih1, ih2, ih3, Bool.or_eq_true]; grind
  | bin _ _ _ ih1 ih2 => simp only [freeVarsExp, occursFree, mem_union, ih1, ih2, Bool.or_eq_true]; grind
  | concat _ _ ih1 ih2 => simp only [freeVarsExp, occursFree, mem_union, ih1, ih2, Bool.or_eq_true]; grind
  | un _ _ ih => simpa only [freeVarsExp, occursFree] using ih bound
  | cast _ _ _ ih => simpa only [freeVarsExp, occursFree] using ih bound
  | extract _ _ _ ih => simpa only [freeVarsExp, occursFree] using ih bound
  | ite _ _ _ ih1 ih2 ih3 => simp only [freeVarsExp, occursFree, mem_union, ih1, ih2, ih3, Bool.or_eq_true]; grind
  | letIn var _ _ ih1 ih2 =>
    simp only [freeVarsExp, occursFree, mem_union, ih1, ih2, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne,
      List.mem_cons, not_or]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨h1, Or.inl h2⟩
      · exact ⟨h2, Or.inr ⟨fun e => h1 e.symm, h3⟩⟩
    · rintro ⟨h1, h2 | ⟨h2, h3⟩⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨⟨fun e => h2 e.symm, h1⟩, h3⟩

theorem mem_freeVars_iff (v : Bap.Var) (exp : Exp) : v ∈ freeVars exp ↔ occursFree v exp = true := by
  simpa [freeVars] using occursFree_iff_mem_freeVarsExp v [] exp

private theorem foldl_index_mono (avoid : List Bap.Var) (init : Nat) :
    init ≤ avoid.foldl (fun index other => max index (other.index + 1)) init := by
  induction avoid generalizing init with
  | nil => exact Nat.le_refl _
  | cons head rest ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem freshVersion_not_mem (var : Bap.Var) (avoid : List Bap.Var) : freshVersion var avoid ∉ avoid := by
  have key : ∀ (rest : List Bap.Var) (init : Nat), ∀ v ∈ rest,
      v.index < rest.foldl (fun index other => max index (other.index + 1)) init := by
    intro rest
    induction rest with
    | nil => simp
    | cons head tail ih =>
      intro init v hv
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hv with rfl | hv
      · have := foldl_index_mono tail (max init (v.index + 1))
        have := Nat.le_max_right init (v.index + 1)
        omega
      · exact ih _ v hv
  intro hm
  have := key avoid (var.index + 1) _ hm
  simp [freshVersion, Var.version] at this

private theorem get_cons (key k : Bap.Var) (v : Exp) (rest : List (Bap.Var × Exp)) :
    Assoc.get key ((k, v) :: rest) = if key = k then some v else Assoc.get key rest := by
  by_cases h : key = k
  · simp [Assoc.get, h]
  · have : (key == k) = false := by simpa using h
    simp [Assoc.get, List.lookup, this, h]

private theorem get_filter_ne (replacements : List (Bap.Var × Exp)) (var other : Bap.Var) :
    Assoc.get other (replacements.filter fun r => r.1 != var) =
      if other = var then none else Assoc.get other replacements := by
  induction replacements with
  | nil => simp [Assoc.get]
  | cons head rest ih =>
    obtain ⟨k, v⟩ := head
    by_cases hk : k = var
    · subst hk
      have : ((k, v) :: rest).filter (fun r => r.1 != k) = rest.filter (fun r => r.1 != k) := by simp
      rw [this, ih, get_cons]
      by_cases h : other = k <;> simp [h]
    · have : ((k, v) :: rest).filter (fun r => r.1 != var) = (k, v) :: rest.filter (fun r => r.1 != var) := by
        simp [hk]
      rw [this, get_cons, ih, get_cons]
      by_cases h : other = var
      · subst h; simp [Ne.symm hk]
      · simp [h]

private theorem assoc_mem {key : Bap.Var} {value : Exp} {entries : List (Bap.Var × Exp)}
    (h : Assoc.get key entries = some value) : (key, value) ∈ entries := by
  induction entries with
  | nil => simp [Assoc.get] at h
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    rw [get_cons] at h
    by_cases hk : key = k
    · subst hk
      simp only [ite_true, Option.some.injEq] at h
      simp [h]
    · simp only [hk, ite_false] at h
      exact List.mem_cons_of_mem _ (ih h)

private theorem evalExp_bind_unused (exp : Exp) (env : Env) (var : Bap.Var) (value : Value)
    (h : occursFree var exp = false) : evalExp (Bap.Bil.bind env var value) exp = evalExp env exp := by
  apply evalExp_congr_freeVars
  intro u hu
  apply lookup_bind_other
  rintro rfl
  rw [(mem_freeVars_iff u exp).mp hu] at h
  cases h

/-- Substitution correctness: replacing variables by expressions equals evaluating in an environment
that binds each variable the expression uses to its replacement's value. No side condition on
binders is needed, because `substitute` renames a `let` that would capture. -/
theorem evalExp_substitute (exp : Exp) (replacements : List (Bap.Var × Exp)) (env env' : Env)
    (hr : ∀ v, occursFree v exp = true → match Assoc.get v replacements with
      | some r => evalExp env r = lookup env' v
      | none => lookup env v = lookup env' v) :
    evalExp env (substitute replacements exp) = evalExp env' exp := by
  induction exp generalizing replacements env env' with
  | int value => rfl
  | unknown message typ => rfl
  | var var =>
    have := hr var (by simp [occursFree])
    simp only [substitute, evalExp]
    cases hg : Assoc.get var replacements with
    | none => simpa [hg, evalExp] using this
    | some r => simpa [hg] using this
  | load memory address _ _ ih1 ih2 =>
    simp only [substitute, evalExp,
      ih1 replacements env env' (fun v hv => hr v (by simp [occursFree, hv])),
      ih2 replacements env env' (fun v hv => hr v (by simp [occursFree, hv]))]
  | store memory address value _ _ ih1 ih2 ih3 =>
    simp only [substitute, evalExp,
      ih1 replacements env env' (fun v hv => hr v (by simp [occursFree, hv])),
      ih2 replacements env env' (fun v hv => hr v (by simp [occursFree, hv])),
      ih3 replacements env env' (fun v hv => hr v (by simp [occursFree, hv]))]
  | bin op left right ih1 ih2 =>
    simp only [substitute, evalExp,
      ih1 replacements env env' (fun v hv => hr v (by simp [occursFree, hv])),
      ih2 replacements env env' (fun v hv => hr v (by simp [occursFree, hv]))]
  | concat left right ih1 ih2 =>
    simp only [substitute, evalExp,
      ih1 replacements env env' (fun v hv => hr v (by simp [occursFree, hv])),
      ih2 replacements env env' (fun v hv => hr v (by simp [occursFree, hv]))]
  | un op value ih =>
    simp only [substitute, evalExp, ih replacements env env' (fun v hv => hr v (by simp [occursFree, hv]))]
  | cast kind width value ih =>
    simp only [substitute, evalExp, ih replacements env env' (fun v hv => hr v (by simp [occursFree, hv]))]
  | extract high low value ih =>
    simp only [substitute, evalExp, ih replacements env env' (fun v hv => hr v (by simp [occursFree, hv]))]
  | ite condition yes no ih1 ih2 ih3 =>
    simp only [substitute, evalExp,
      ih1 replacements env env' (fun v hv => hr v (by simp [occursFree, hv])),
      ih2 replacements env env' (fun v hv => hr v (by simp [occursFree, hv])),
      ih3 replacements env env' (fun v hv => hr v (by simp [occursFree, hv]))]
  | letIn var value body ih1 ih2 =>
    have hvalue := ih1 replacements env env' (fun v hv => hr v (by simp [occursFree, hv]))
    have hbody : ∀ v, occursFree v body = true → v ≠ var → match Assoc.get v replacements with
        | some r => evalExp env r = lookup env' v
        | none => lookup env v = lookup env' v :=
      fun v hv hne => hr v (by simp [occursFree, hv, Ne.symm hne])
    simp only [substitute]
    split
    · simp only [evalExp, hvalue]
      congr 1
      funext result
      apply ih2
      generalize hfresh : freshVersion var
        ((replacements.filter fun r => r.1 != var).flatMap (freeVars ·.2) ++ freeVars body) = fresh
      have hnot := freshVersion_not_mem var
        ((replacements.filter fun r => r.1 != var).flatMap (freeVars ·.2) ++ freeVars body)
      rw [hfresh] at hnot
      intro v hv
      rw [get_cons]
      by_cases he : v = var
      · subst he
        simp [evalExp, lookup_bind_eq]
      · simp only [he, ite_false]
        rw [get_filter_ne]
        simp only [he, ite_false]
        have hvf : v ≠ fresh := by
          rintro rfl
          exact hnot (List.mem_append_right _ ((mem_freeVars_iff _ _).mpr hv))
        have := hbody v hv he
        rw [lookup_bind_other _ _ he]
        cases hg : Assoc.get v replacements with
        | none =>
          simp only [hg] at this ⊢
          rw [lookup_bind_other _ _ hvf]
          exact this
        | some r =>
          simp only [hg] at this ⊢
          rw [← this]
          apply evalExp_bind_unused
          cases hu : occursFree fresh r with
          | false => rfl
          | true =>
            refine absurd (List.mem_append_left _ (List.mem_flatMap.mpr ⟨(v, r), ?_, (mem_freeVars_iff _ _).mpr hu⟩)) hnot
            exact List.mem_filter.mpr ⟨assoc_mem hg, by simpa using he⟩
    · rename_i hcapture
      simp only [evalExp, hvalue]
      congr 1
      funext result
      apply ih2
      intro v hv
      rw [get_filter_ne]
      by_cases he : v = var
      · simp [he, lookup_bind_eq]
      · simp only [he, ite_false]
        have := hbody v hv he
        rw [lookup_bind_other _ _ he]
        cases hg : Assoc.get v replacements with
        | none =>
          simp only [hg] at this ⊢
          rw [lookup_bind_other _ _ he]
          exact this
        | some r =>
          simp only [hg] at this ⊢
          rw [← this]
          apply evalExp_bind_unused
          cases hu : occursFree var r with
          | false => rfl
          | true =>
            exact absurd (List.any_eq_true.mpr ⟨(v, r),
              List.mem_filter.mpr ⟨assoc_mem hg, by simpa using he⟩, by simp [hu, hv]⟩) hcapture

/-- Single-variable substitution, with no condition on binders. -/
theorem evalExp_substitute_single (exp replacement : Exp) (var : Bap.Var) (env : Env) (value : Value)
    (hvalue : evalExp env replacement = .ok value) :
    evalExp env (substitute [(var, replacement)] exp) = evalExp (Bap.Bil.bind env var value) exp := by
  apply evalExp_substitute
  intro v _
  by_cases he : v = var
  · subst he
    simp [Assoc.get, hvalue, lookup_bind_eq]
  · have : Assoc.get v [(var, replacement)] = none := by
      simp [get_cons, he, Assoc.get]
    simp [this, lookup_bind_other _ _ he]

/-- Where no `let` could capture, `substitute` keeps the binder like the reference `Exp.substitute`. -/
theorem substitute_letIn_keeps_binder (replacements : List (Bap.Var × Exp)) (var : Bap.Var) (value body : Exp)
    (h : ∀ r ∈ replacements.filter (fun r => r.1 != var), occursFree var r.2 = false ∨ occursFree r.1 body = false) :
    substitute replacements (.letIn var value body) =
      .letIn var (substitute replacements value) (substitute (replacements.filter fun r => r.1 != var) body) := by
  have : (replacements.filter fun r => r.1 != var).any
      (fun r => occursFree var r.2 && occursFree r.1 body) = false := by
    apply List.any_eq_false.mpr
    intro r hr
    rcases h r hr with h1 | h1 <;> simp [h1]
  simp only [substitute, this, Bool.false_eq_true, ite_false]

/-- Constant folding preserves evaluation exactly, including error messages. -/
theorem evalExp_foldExp (env : Env) (exp : Exp) : evalExp env (foldExp exp) = evalExp env exp := by
  induction exp generalizing env <;> rw [foldExp] <;> split <;>
    first
      | (rename_i hv; exact (evalExp_extends (nil_extends env) _ hv).symm)
      | simp only [evalExp, *]

private theorem fold_exec (fuel : Nat) :
    (∀ state (stmt : Stmt), execStmt fuel state (foldStmt stmt) = execStmt fuel state stmt) ∧
    (∀ state (program : Program), execProgram fuel state (program.map foldStmt) = execProgram fuel state program) := by
  induction fuel with
  | zero => exact ⟨fun _ _ => by simp [execStmt], fun _ _ => by simp [execProgram]⟩
  | succ f ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun state stmt => ?_, fun state program => ?_⟩
    · cases stmt with
      | move var value => simp only [foldStmt, execStmt, execExp, evalExp_foldExp]
      | jmp target => simp only [foldStmt, execStmt, execExp, evalExp_foldExp]
      | special message => simp only [foldStmt]
      | cpuExn number => simp only [foldStmt]
      | ifElse condition yes no =>
        simp only [foldStmt, execStmt, execExp, evalExp_foldExp, apply_ite, ih2]
      | «while» condition body =>
        have hw : ∀ next, execStmt f next (.while (foldExp condition) (body.map foldStmt)) =
            execStmt f next (.while condition body) := by
          intro next
          have := ih1 next (.while condition body)
          simpa only [foldStmt] using this
        simp only [foldStmt, execStmt, execExp, evalExp_foldExp, ih2, hw]
    · cases program with
      | nil => rfl
      | cons stmt rest => simp only [List.map_cons, execProgram, ih1, ih2]

/-- Folding a program changes nothing the interpreter can observe, at any fuel. -/
theorem execProgram_foldProgram (fuel : Nat) (state : State) (program : Program) :
    execProgram fuel state (foldProgram program) = execProgram fuel state program :=
  (fold_exec fuel).2 state program

theorem execStmt_foldStmt (fuel : Nat) (state : State) (stmt : Stmt) :
    execStmt fuel state (foldStmt stmt) = execStmt fuel state stmt :=
  (fold_exec fuel).1 state stmt

/-! ## Type soundness -/

open_private Bap.Bil.Typecheck Bap.Bil.expectImm Bap.Bil.expectSameType Bap.Bil.expectBits Bap.Bil.checkCondition

/-- Every binding holds a value of its variable's declared type. -/
def WellTypedEnv (env : Env) : Prop :=
  ∀ binding ∈ env, binding.2.type = binding.1.typ

theorem wellTypedEnv_nil : WellTypedEnv [] := by simp [WellTypedEnv]

theorem WellTypedEnv.bind {env : Env} (h : WellTypedEnv env) {var : Bap.Var} {value : Value}
    (hv : value.type = var.typ) : WellTypedEnv (Bap.Bil.bind env var value) := by
  intro binding hm
  simp only [Bap.Bil.bind, List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact hv
  · exact h _ (List.mem_filter.mp hm).1

theorem WellTypedEnv.lookup {env : Env} (h : WellTypedEnv env) {var : Bap.Var} {value : Value}
    (hl : Bap.Bil.lookup env var = .ok value) : value.type = var.typ :=
  h _ (mem_of_lookup hl)

private theorem expectImm_ok {t : Typ} {w : Nat} : expectImm t = .ok w ↔ t = .imm w := by
  cases t <;> simp [expectImm]

private theorem expectBits_ok {t t' : Typ} (h : expectBits t = .ok t') : t' = t := by
  unfold expectBits at h
  split at h <;> cases h <;> rfl

private def comparison : BinOp → Bool
  | .eq | .neq | .lt | .le | .gt | .ge | .slt | .sle | .sgt | .sge => true
  | _ => false

private theorem infer_bin_inv {op : BinOp} {left right : Exp} {t : Typ}
    (h : inferExp (.bin op left right) = .ok t) :
    ∃ w, inferExp left = .ok (.imm w) ∧ inferExp right = .ok (.imm w) ∧
      t = if comparison op then .imm 1 else .imm w := by
  simp only [inferExp, except_bind_ok] at h
  obtain ⟨lt, hl, rt, hr, lw, hlw, rw, hrw, he⟩ := h
  rw [expectImm_ok] at hlw hrw
  subst hlw hrw
  by_cases hne : lw = rw
  · subst hne
    refine ⟨lw, hl, hr, ?_⟩
    simp only [ne_eq, not_true_eq_false, ite_false] at he
    cases op <;> simpa [comparison, eq_comm] using he.symm
  · simp [hne] at he

private theorem evalBin_type {op : BinOp} {a b : BitVec w} {r : Value}
    (h : evalBin op ⟨w, a⟩ ⟨w, b⟩ = .ok r) : r.type = if comparison op then .imm 1 else .imm w := by
  cases op <;> simp [evalBin] at h <;> subst h <;> rfl

private theorem evalBin_width {op : BinOp} {a : BitVec w} {b : BitVec w'} {r : Value}
    (h : evalBin op ⟨w, a⟩ ⟨w', b⟩ = .ok r) : w = w' := by
  by_cases hne : w = w'
  · exact hne
  · simp [evalBin, hne, Bind.bind, Except.bind] at h

private theorem bit_cases (c : BitVec 1) : c = 1 ∨ c = 0 := by
  have := c.isLt
  by_cases h : c.toNat = 0
  · exact Or.inr (BitVec.eq_of_toNat_eq (by simpa using h))
  · exact Or.inl (BitVec.eq_of_toNat_eq (by simp; omega))

private theorem infer_load_inv {memory address : Exp} {endian : Endian} {size : Nat} {t : Typ}
    (h : inferExp (.load memory address endian size) = .ok t) :
    ∃ w, inferExp memory = .ok (.mem w 8) ∧ inferExp address = .ok (.imm w) ∧ t = .imm (size * 8) ∧ size ≠ 0 := by
  simp only [inferExp, except_bind_ok] at h
  obtain ⟨mt, hmt, h⟩ := h
  split at h
  · rename_i aw vw
    split at h
    · rename_i hv
      subst hv
      simp only [except_bind_ok] at h
      obtain ⟨at', hat, w, hw, hif⟩ := h
      rw [expectImm_ok] at hw
      subst hw
      split at hif
      · rename_i he
        subst he
        split at hif
        · simp at hif
        · rename_i hz
          simp only [Except.ok.injEq] at hif
          exact ⟨_, hmt, hat, hif.symm, hz⟩
      · simp at hif
    · simp at h
  · simp at h

private theorem infer_store_inv {memory address value : Exp} {endian : Endian} {size : Nat} {t : Typ}
    (h : inferExp (.store memory address value endian size) = .ok t) :
    ∃ w, inferExp memory = .ok (.mem w 8) ∧ inferExp address = .ok (.imm w) ∧
      inferExp value = .ok (.imm (size * 8)) ∧ t = .mem w 8 ∧ size ≠ 0 ∧ size ≤ 2 ^ w := by
  simp only [inferExp, except_bind_ok] at h
  obtain ⟨mt, hmt, h⟩ := h
  split at h
  · split at h
    · simp at h
    · rename_i hv
      have hv8 := Decidable.not_not.mp hv
      subst hv8
      simp only [except_bind_ok] at h
      obtain ⟨at', hat, w, hw, h⟩ := h
      rw [expectImm_ok] at hw
      subst hw
      split at h
      · simp at h
      · rename_i he
        have he' := Decidable.not_not.mp he
        subst he'
        simp only [except_bind_ok] at h
        obtain ⟨vt, hvt, vw, hvw, hif⟩ := h
        rw [expectImm_ok] at hvw
        subst hvw
        split at hif
        · simp at hif
        · rename_i hs
          have hs' := Decidable.not_not.mp hs
          subst hs'
          split at hif
          · simp at hif
          · rename_i hz
            split at hif
            · simp at hif
            · rename_i hfit
              simp only [Except.ok.injEq] at hif
              exact ⟨_, hmt, hat, hvt, hif.symm, hz, by omega⟩
  · simp at h

private theorem infer_un_inv {op : UnOp} {value : Exp} {t : Typ} (h : inferExp (.un op value) = .ok t) :
    ∃ w, inferExp value = .ok (.imm w) ∧ t = .imm w := by
  simp only [inferExp, except_bind_ok, Except.ok.injEq] at h
  obtain ⟨vt, hvt, w, hw, rfl⟩ := h
  rw [expectImm_ok] at hw
  subst hw
  exact ⟨w, hvt, rfl⟩

private theorem infer_cast_inv {kind : Cast} {width : Nat} {value : Exp} {t : Typ}
    (h : inferExp (.cast kind width value) = .ok t) :
    ∃ source, inferExp value = .ok (.imm source) ∧ t = .imm width ∧ width ≠ 0 ∧
      (kind = .low ∨ kind = .high → width ≤ source) := by
  simp only [inferExp, except_bind_ok] at h
  obtain ⟨vt, hvt, source, hs, h⟩ := h
  rw [expectImm_ok] at hs
  subst hs
  split at h
  · simp at h
  · rename_i hne
    refine ⟨source, hvt, ?_⟩
    cases kind <;> simp only at h
    · split at h
      · rename_i hle
        simp only [Except.ok.injEq] at h
        exact ⟨h.symm, hne, fun _ => hle⟩
      · simp at h
    · split at h
      · rename_i hle
        simp only [Except.ok.injEq] at h
        exact ⟨h.symm, hne, fun _ => hle⟩
      · simp at h
    · simp only [Except.ok.injEq] at h
      exact ⟨h.symm, hne, by simp⟩
    · simp only [Except.ok.injEq] at h
      exact ⟨h.symm, hne, by simp⟩

private theorem infer_let_inv {var : Bap.Var} {value body : Exp} {t : Typ}
    (h : inferExp (.letIn var value body) = .ok t) :
    inferExp value = .ok var.typ ∧ inferExp body = .ok t := by
  simp only [inferExp, except_bind_ok] at h
  obtain ⟨vt, hvt, h⟩ := h
  split at h
  · simp at h
  · rename_i hne
    have heq : var.typ = vt := Decidable.not_not.mp hne
    subst heq
    exact ⟨hvt, h⟩

private theorem infer_ite_inv {condition yes no : Exp} {t : Typ}
    (h : inferExp (.ite condition yes no) = .ok t) :
    inferExp condition = .ok (.imm 1) ∧ inferExp yes = .ok t ∧ inferExp no = .ok t := by
  simp only [inferExp, except_bind_ok] at h
  obtain ⟨ct, hct, cw, hcw, h⟩ := h
  rw [expectImm_ok] at hcw
  subst hcw
  split at h
  · simp at h
  · rename_i hne
    have h1 : cw = 1 := Decidable.not_not.mp hne
    subst h1
    simp only [except_bind_ok] at h
    obtain ⟨yt, hyt, nt, hnt, u, hsame, hfinal⟩ := h
    simp only [Except.ok.injEq] at hfinal
    subst hfinal
    have hsame' : yt = nt := by
      simp only [expectSameType] at hsame
      split at hsame
      · assumption
      · simp at hsame
    subst hsame'
    exact ⟨hct, hyt, hnt⟩

private theorem infer_extract_inv {high low : Nat} {value : Exp} {t : Typ}
    (h : inferExp (.extract high low value) = .ok t) :
    ∃ w, inferExp value = .ok (.imm w) ∧ t = .imm (high - low + 1) ∧ low ≤ high ∧ high < w := by
  simp only [inferExp, except_bind_ok] at h
  obtain ⟨vt, hvt, w, hw, h⟩ := h
  rw [expectImm_ok] at hw
  subst hw
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i h1 h2
      simp only [Except.ok.injEq] at h
      exact ⟨w, hvt, h.symm, by omega, by omega⟩

private theorem infer_concat_inv {left right : Exp} {t : Typ} (h : inferExp (.concat left right) = .ok t) :
    ∃ lw rw, inferExp left = .ok (.imm lw) ∧ inferExp right = .ok (.imm rw) ∧ t = .imm (lw + rw) := by
  simp only [inferExp, except_bind_ok] at h
  obtain ⟨lt, hlt, lw, hlw, rt, hrt, rw, hrw, hfinal⟩ := h
  rw [expectImm_ok] at hlw hrw
  subst hlw hrw
  simp only [Except.ok.injEq] at hfinal
  exact ⟨lw, rw, hlt, hrt, hfinal.symm⟩

/-- Type soundness: a successful evaluation in a well-typed environment produces a value of exactly
the inferred type. -/
theorem evalExp_type_sound {env : Env} (hwt : WellTypedEnv env) (exp : Exp) {t : Typ} {result : Value}
    (hi : inferExp exp = .ok t) (he : evalExp env exp = .ok result) : result.type = t := by
  induction exp generalizing env t result with
  | int value =>
    simp only [inferExp] at hi
    simp only [evalExp, Except.ok.injEq] at he
    cases expectBits_ok hi
    subst he
    rfl
  | var var =>
    simp only [inferExp] at hi
    cases expectBits_ok hi
    exact hwt.lookup he
  | unknown message typ => simp [evalExp] at he
  | load memory address endian size _ _ =>
    obtain ⟨w, m, a, _, _, rfl⟩ := eval_load_iff.mp he
    obtain ⟨_, _, _, rfl, _⟩ := infer_load_inv hi
    rfl
  | store memory address value endian size ihm _ _ =>
    obtain ⟨w, m, a, vw, v, u, hm, _, _, _, rfl⟩ := eval_store_iff.mp he
    obtain ⟨w', hmt, _, _, rfl, _⟩ := infer_store_inv hi
    have := ihm hwt hmt hm
    simpa [Value.type] using this
  | bin op left right ihl _ =>
    obtain ⟨lw, rw, a, b, hl, hr, hb⟩ := eval_bin_iff.mp he
    obtain ⟨w, hil, hir, rfl⟩ := infer_bin_inv hi
    cases evalBin_width hb
    have := ihl hwt hil hl
    simp only [Value.type, Typ.imm.injEq] at this
    subst this
    exact evalBin_type hb
  | un op value ih =>
    obtain ⟨w, b, hv, rfl⟩ := eval_un_iff.mp he
    obtain ⟨w', hvt, rfl⟩ := infer_un_inv hi
    have := ih hwt hvt hv
    simp only [Value.type, Typ.imm.injEq] at this
    subst this
    cases op <;> rfl
  | cast kind width value _ =>
    obtain ⟨w, b, hv, hc⟩ := eval_cast_iff.mp he
    obtain ⟨_, _, rfl, _, _⟩ := infer_cast_inv hi
    cases kind with
    | low => simp only [castValue, Except.ok.injEq] at hc; subst hc; rfl
    | unsigned => simp only [castValue, Except.ok.injEq] at hc; subst hc; rfl
    | signed => simp only [castValue, Except.ok.injEq] at hc; subst hc; rfl
    | high =>
      obtain ⟨x, _, hx⟩ := except_bind_ok.mp hc
      simp only [Except.ok.injEq] at hx
      subst hx
      rfl
  | letIn var value body ihv ihb =>
    obtain ⟨v, hv, hb⟩ := eval_let_iff.mp he
    obtain ⟨hvt, hbt⟩ := infer_let_inv hi
    exact ihb (hwt.bind (ihv hwt hvt hv)) hbt hb
  | ite condition yes no _ ihy ihn =>
    obtain ⟨c, _, hb⟩ := eval_ite_iff.mp he
    obtain ⟨_, hyt, hnt⟩ := infer_ite_inv hi
    by_cases hc1 : c = 1
    · rw [ite_eq_left hc1] at hb
      exact ihy hwt hyt hb
    · rw [ite_eq_right hc1] at hb
      exact ihn hwt hnt hb
  | extract high low value _ =>
    obtain ⟨w, b, x, _, _, rfl⟩ := eval_extract_iff.mp he
    obtain ⟨_, _, rfl, _, _⟩ := infer_extract_inv hi
    rfl
  | concat left right ihl ihr =>
    obtain ⟨lw, rw, a, b, hl, hr, rfl⟩ := eval_concat_iff.mp he
    obtain ⟨lw', rw', hlt, hrt, rfl⟩ := infer_concat_inv hi
    have h1 := ihl hwt hlt hl
    have h2 := ihr hwt hrt hr
    simp only [Value.type, Typ.imm.injEq] at h1 h2
    subst h1 h2
    rfl

/-- The checker rejects unary operators on non-bitvectors, which the evaluator cannot run. -/
theorem infer_un_memory_rejected (op : UnOp) {value : Exp} {a v : Nat} (h : inferExp value = .ok (.mem a v)) :
    (inferExp (.un op value)).toOption = none := by
  simp [inferExp, h, Bind.bind, Except.bind, expectImm, Except.toOption]

/-- The checker rejects a `load` whose address width differs from the memory's. -/
theorem infer_load_width_rejected {memory address : Exp} {w w' : Nat} (hne : w' ≠ w) (endian : Endian) (size : Nat)
    (hm : inferExp memory = .ok (.mem w 8)) (ha : inferExp address = .ok (.imm w')) :
    inferExp (.load memory address endian size) = .error "address width does not match memory" := by
  simp [inferExp, hm, ha, hne, Bind.bind, Except.bind, expectImm]

theorem infer_store_width_rejected {memory address value : Exp} {w w' : Nat} (hne : w' ≠ w) (endian : Endian)
    (size : Nat) (hm : inferExp memory = .ok (.mem w 8)) (ha : inferExp address = .ok (.imm w')) :
    inferExp (.store memory address value endian size) = .error "address width does not match memory" := by
  simp [inferExp, hm, ha, hne, Bind.bind, Except.bind, expectImm]

/-- `low` and `high` casts can only narrow, as in the reference `Exp.infer`. -/
theorem infer_narrowing_cast_rejected {kind : Cast} (hk : kind = .low ∨ kind = .high) {value : Exp} {source width : Nat}
    (hw : source < width) (hv : inferExp value = .ok (.imm source)) :
    inferExp (.cast kind width value) = .error "cast is wider than its operand" := by
  have h1 : width ≠ 0 := by omega
  have h2 : ¬ width ≤ source := by omega
  rcases hk with rfl | rfl <;> simp [inferExp, hv, h1, h2, Bind.bind, Except.bind, expectImm]

private theorem evalBin_progress (op : BinOp) (a b : BitVec w) :
    ∃ (w' : Nat) (r : BitVec w'), (if comparison op then Typ.imm 1 else Typ.imm w) = .imm w' ∧
      evalBin op ⟨w, a⟩ ⟨w, b⟩ = .ok (.bits r) := by
  cases op <;> simp [evalBin, comparison]

private theorem bits_of_type {value : Value} {w : Nat} (h : value.type = .imm w) :
    ∃ b : BitVec w, value = .bits b := by
  cases value with
  | @bits w' b =>
    simp only [Value.type, Typ.imm.injEq] at h
    subst h
    exact ⟨b, rfl⟩
  | memory m => simp [Value.type] at h
  | undefined => simp [Value.type] at h

private theorem memory_of_type {value : Value} {w v : Nat} (h : value.type = .mem w v) :
    v = 8 ∧ ∃ m : Memory w, value = .memory m := by
  cases value with
  | @memory w' m =>
    simp only [Value.type, Typ.mem.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, m, rfl⟩
  | bits b => simp [Value.type] at h
  | undefined => simp [Value.type] at h

/-- Progress: a well-typed expression containing no `unknown` cannot get stuck once its free
variables are bound, in any well-typed environment. With `evalExp_type_sound`, it evaluates to a
value of the inferred type. -/
private theorem evalExp_progress_aux (exp : Exp) (hu : hasUnknown exp = false) {t : Typ} (hi : inferExp exp = .ok t)
    {env : Env} (hwt : WellTypedEnv env) (hb : ∀ v, occursFree v exp = true → ∃ value, lookup env v = .ok value) :
    ∃ value, evalExp env exp = .ok value := by
  induction exp generalizing env t with
  | int value => exact ⟨_, rfl⟩
  | unknown message typ => simp [hasUnknown] at hu
  | var var => exact hb var (by simp [occursFree])
  | load memory address endian size ihm iha =>
    simp only [hasUnknown, Bool.or_eq_false_iff, and_assoc] at hu
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨w, hmt, hat, _⟩ := infer_load_inv hi
    obtain ⟨mv, hm⟩ := ihm hu1 hmt hwt (fun v h => hb v (by simp [occursFree, h]))
    obtain ⟨av, ha⟩ := iha hu2 hat hwt (fun v h => hb v (by simp [occursFree, h]))
    obtain ⟨_, m, rfl⟩ := memory_of_type (evalExp_type_sound hwt _ hmt hm)
    obtain ⟨a, rfl⟩ := bits_of_type (evalExp_type_sound hwt _ hat ha)
    exact ⟨_, eval_load_iff.mpr ⟨w, m, a, hm, ha, rfl⟩⟩
  | store memory address value endian size ihm iha ihv =>
    simp only [hasUnknown, Bool.or_eq_false_iff, and_assoc] at hu
    obtain ⟨hu1, hu2, hu3⟩ := hu
    obtain ⟨w, hmt, hat, hvt, _⟩ := infer_store_inv hi
    obtain ⟨mv, hm⟩ := ihm hu1 hmt hwt (fun v h => hb v (by simp [occursFree, h]))
    obtain ⟨av, ha⟩ := iha hu2 hat hwt (fun v h => hb v (by simp [occursFree, h]))
    obtain ⟨vv, hv⟩ := ihv hu3 hvt hwt (fun v h => hb v (by simp [occursFree, h]))
    obtain ⟨_, m, rfl⟩ := memory_of_type (evalExp_type_sound hwt _ hmt hm)
    obtain ⟨a, rfl⟩ := bits_of_type (evalExp_type_sound hwt _ hat ha)
    obtain ⟨x, rfl⟩ := bits_of_type (evalExp_type_sound hwt _ hvt hv)
    exact ⟨_, eval_store_iff.mpr ⟨w, m, a, _, x, _, hm, ha, hv, Bap.Proofs.Core.MemoryLaws.write_eq rfl endian, rfl⟩⟩
  | bin op left right ihl ihr =>
    simp only [hasUnknown, Bool.or_eq_false_iff, and_assoc] at hu
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨w, hil, hir, _⟩ := infer_bin_inv hi
    obtain ⟨lv, hl⟩ := ihl hu1 hil hwt (fun v h => hb v (by simp [occursFree, h]))
    obtain ⟨rv, hr⟩ := ihr hu2 hir hwt (fun v h => hb v (by simp [occursFree, h]))
    obtain ⟨a, rfl⟩ := bits_of_type (evalExp_type_sound hwt _ hil hl)
    obtain ⟨b, rfl⟩ := bits_of_type (evalExp_type_sound hwt _ hir hr)
    obtain ⟨_, _, _, he⟩ := evalBin_progress op a b
    exact ⟨_, eval_bin_iff.mpr ⟨w, w, a, b, hl, hr, he⟩⟩
  | un op value ih =>
    obtain ⟨w, hvt, _⟩ := infer_un_inv hi
    obtain ⟨vv, hv⟩ := ih (by simpa [hasUnknown] using hu) hvt hwt (fun v h => hb v (by simpa [occursFree] using h))
    obtain ⟨b, rfl⟩ := bits_of_type (evalExp_type_sound hwt _ hvt hv)
    exact ⟨_, eval_un_iff.mpr ⟨w, b, hv, rfl⟩⟩
  | cast kind width value ih =>
    obtain ⟨source, hvt, _, h0, hk⟩ := infer_cast_inv hi
    obtain ⟨vv, hv⟩ := ih (by simpa [hasUnknown] using hu) hvt hwt (fun v h => hb v (by simpa [occursFree] using h))
    obtain ⟨b, rfl⟩ := bits_of_type (evalExp_type_sound hwt _ hvt hv)
    cases kind with
    | low => exact ⟨_, eval_cast_iff.mpr ⟨source, b, hv, rfl⟩⟩
    | unsigned => exact ⟨_, eval_cast_iff.mpr ⟨source, b, hv, rfl⟩⟩
    | signed => exact ⟨_, eval_cast_iff.mpr ⟨source, b, hv, rfl⟩⟩
    | high =>
      have hle := hk (Or.inr rfl)
      have hhigh : Word.high width b = .ok (BitVec.zeroExtend width (BitVec.ushiftRight b (source - width))) := by
        simp only [Word.high]
        rw [ite_eq_left ⟨by omega, hle⟩]
      exact ⟨_, eval_cast_iff.mpr ⟨source, b, hv, by
        simp only [castValue, hhigh]
        rfl⟩⟩
  | letIn var value body ihv ihb =>
    simp only [hasUnknown, Bool.or_eq_false_iff, and_assoc] at hu
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨hvt, hbt⟩ := infer_let_inv hi
    obtain ⟨x, hv⟩ := ihv hu1 hvt hwt (fun v h => hb v (by simp [occursFree, h]))
    obtain ⟨r, hr⟩ := ihb hu2 hbt (hwt.bind (evalExp_type_sound hwt _ hvt hv)) (by
      intro v h
      by_cases he : v = var
      · exact ⟨x, by simp [he, lookup_bind_eq]⟩
      · rw [lookup_bind_other _ _ he]
        exact hb v (by simp [occursFree, h, Ne.symm he]))
    exact ⟨r, eval_let_iff.mpr ⟨x, hv, hr⟩⟩
  | ite condition yes no ihc ihy ihn =>
    simp only [hasUnknown, Bool.or_eq_false_iff, and_assoc] at hu
    obtain ⟨hu1, hu2, hu3⟩ := hu
    obtain ⟨hct, hyt, hnt⟩ := infer_ite_inv hi
    obtain ⟨cv, hc⟩ := ihc hu1 hct hwt (fun v h => hb v (by simp [occursFree, h]))
    obtain ⟨c, rfl⟩ := bits_of_type (evalExp_type_sound hwt _ hct hc)
    obtain ⟨y, hy⟩ := ihy hu2 hyt hwt (fun v h => hb v (by simp [occursFree, h]))
    obtain ⟨n, hn⟩ := ihn hu3 hnt hwt (fun v h => hb v (by simp [occursFree, h]))
    by_cases hc1 : c = 1
    · exact ⟨y, eval_ite_iff.mpr ⟨c, hc, by rw [ite_eq_left hc1]; exact hy⟩⟩
    · exact ⟨n, eval_ite_iff.mpr ⟨c, hc, by rw [ite_eq_right hc1]; exact hn⟩⟩
  | extract high low value ih =>
    obtain ⟨w, hvt, _, h1, h2⟩ := infer_extract_inv hi
    obtain ⟨vv, hv⟩ := ih (by simpa [hasUnknown] using hu) hvt hwt (fun v h => hb v (by simpa [occursFree] using h))
    obtain ⟨b, rfl⟩ := bits_of_type (evalExp_type_sound hwt _ hvt hv)
    have hok : Word.extract high low b = .ok (BitVec.extractLsb high low b) := by
      simp [Word.extract, show ¬ high < low by omega, show ¬ w ≤ high by omega]
    exact ⟨_, eval_extract_iff.mpr ⟨w, b, _, hv, hok, rfl⟩⟩
  | concat left right ihl ihr =>
    simp only [hasUnknown, Bool.or_eq_false_iff, and_assoc] at hu
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨lw, rw, hlt, hrt, _⟩ := infer_concat_inv hi
    obtain ⟨lv, hl⟩ := ihl hu1 hlt hwt (fun v h => hb v (by simp [occursFree, h]))
    obtain ⟨rv, hr⟩ := ihr hu2 hrt hwt (fun v h => hb v (by simp [occursFree, h]))
    obtain ⟨a, rfl⟩ := bits_of_type (evalExp_type_sound hwt _ hlt hl)
    obtain ⟨b, rfl⟩ := bits_of_type (evalExp_type_sound hwt _ hrt hr)
    exact ⟨_, eval_concat_iff.mpr ⟨lw, rw, a, b, hl, hr, rfl⟩⟩

/-- Type safety: an `unknown`-free expression that typechecks evaluates, once its free variables are
bound in a well-typed environment, to a value of the inferred type. -/
theorem evalExp_progress (exp : Exp) (hu : hasUnknown exp = false) {t : Typ} (hi : inferExp exp = .ok t)
    {env : Env} (hwt : WellTypedEnv env) (hb : ∀ v, occursFree v exp = true → ∃ value, lookup env v = .ok value) :
    ∃ value, evalExp env exp = .ok value ∧ value.type = t := by
  obtain ⟨value, hv⟩ := evalExp_progress_aux exp hu hi hwt hb
  exact ⟨value, hv, evalExp_type_sound hwt exp hi hv⟩


/-! ## Simplification -/

private theorem simplify_shortcut {env : Env} {exp : Exp} {result : Value} {value : BitVec w}
    (h : evalExp env exp = .ok result) (hv : evalExp [] exp = .ok (.bits value)) :
    evalExp env (.int value) = .ok result := by
  have := evalExp_extends (nil_extends env) _ hv
  rw [h] at this
  rw [this]
  rfl

private theorem int_value {env : Env} {z : BitVec w} {a : BitVec w'}
    (h : evalExp env (.int z) = .ok (.bits a)) : ∃ he : w = w', he ▸ z = a := by
  simp only [evalExp, Except.ok.injEq, Value.bits.injEq] at h
  obtain ⟨rfl, hz⟩ := h
  exact ⟨rfl, eq_of_heq hz⟩

private theorem bin_inv_left {env : Env} {op : BinOp} {z : BitVec w} {R : Exp} {r : Value}
    (hb : evalExp env (.bin op (.int z) R) = .ok r) :
    ∃ b : BitVec w, evalExp env R = .ok (.bits b) ∧ evalBin op ⟨w, z⟩ ⟨w, b⟩ = .ok r := by
  obtain ⟨lw, rw, a, b, hl, hr, he⟩ := eval_bin_iff.mp hb
  obtain ⟨rfl, rfl⟩ := int_value hl
  cases evalBin_width he
  exact ⟨b, hr, he⟩

private theorem bin_inv_right {env : Env} {op : BinOp} {z : BitVec w} {L : Exp} {r : Value}
    (hb : evalExp env (.bin op L (.int z)) = .ok r) :
    ∃ a : BitVec w, evalExp env L = .ok (.bits a) ∧ evalBin op ⟨w, a⟩ ⟨w, z⟩ = .ok r := by
  obtain ⟨lw, rw, a, b, hl, hr, he⟩ := eval_bin_iff.mp hb
  obtain ⟨rfl, rfl⟩ := int_value hr
  cases evalBin_width he
  exact ⟨a, hl, he⟩

/-- Simplification refines evaluation: every successful result is preserved. -/
theorem evalExp_simplifyExp (env : Env) (exp : Exp) {result : Value} (h : evalExp env exp = .ok result) :
    evalExp env (simplifyExp exp) = .ok result := by
  induction exp generalizing env result with
  | int value =>
    rw [simplifyExp]; split
    · exact simplify_shortcut h (by assumption)
    · exact h
  | var var =>
    rw [simplifyExp]; split
    · exact simplify_shortcut h (by assumption)
    · exact h
  | unknown message typ => simp [evalExp] at h
  | load memory address endian size ihm iha =>
    rw [simplifyExp]; split
    · exact simplify_shortcut h (by assumption)
    · obtain ⟨w, m, a, hm, ha, rfl⟩ := eval_load_iff.mp h
      exact eval_load_iff.mpr ⟨w, m, a, ihm env hm, iha env ha, rfl⟩
  | store memory address value endian size ihm iha ihv =>
    rw [simplifyExp]; split
    · exact simplify_shortcut h (by assumption)
    · obtain ⟨w, m, a, vw, v, u, hm, ha, hv, hw, rfl⟩ := eval_store_iff.mp h
      exact eval_store_iff.mpr ⟨w, m, a, vw, v, u, ihm env hm, iha env ha, ihv env hv, hw, rfl⟩
  | un op value ih =>
    rw [simplifyExp]; split
    · exact simplify_shortcut h (by assumption)
    · obtain ⟨w, b, hv, rfl⟩ := eval_un_iff.mp h
      exact eval_un_iff.mpr ⟨w, b, ih env hv, rfl⟩
  | cast kind width value ih =>
    rw [simplifyExp]; split
    · exact simplify_shortcut h (by assumption)
    · obtain ⟨w, b, hv, hc⟩ := eval_cast_iff.mp h
      exact eval_cast_iff.mpr ⟨w, b, ih env hv, hc⟩
  | letIn var value body ihv ihb =>
    rw [simplifyExp]; split
    · exact simplify_shortcut h (by assumption)
    · obtain ⟨v, hv, hb⟩ := eval_let_iff.mp h
      exact eval_let_iff.mpr ⟨v, ihv env hv, ihb _ hb⟩
  | extract high low value ih =>
    rw [simplifyExp]; split
    · exact simplify_shortcut h (by assumption)
    · obtain ⟨w, b, x, hv, hx, rfl⟩ := eval_extract_iff.mp h
      exact eval_extract_iff.mpr ⟨w, b, x, ih env hv, hx, rfl⟩
  | concat left right ihl ihr =>
    rw [simplifyExp]; split
    · exact simplify_shortcut h (by assumption)
    · obtain ⟨lw, rw, a, b, hl, hr, rfl⟩ := eval_concat_iff.mp h
      exact eval_concat_iff.mpr ⟨lw, rw, a, b, ihl env hl, ihr env hr, rfl⟩
  | ite condition yes no ihc ihy ihn =>
    rw [simplifyExp]; split
    · exact simplify_shortcut h (by assumption)
    · obtain ⟨c, hc, hb⟩ := eval_ite_iff.mp h
      have hc' := ihc env hc
      have hbase : evalExp env (.ite (simplifyExp condition) (simplifyExp yes) (simplifyExp no)) = .ok result := by
        refine eval_ite_iff.mpr ⟨c, hc', ?_⟩
        by_cases hc1 : c = 1
        · simp only [hc1, ite_true] at hb ⊢
          exact ihy env hb
        · simp only [hc1, ite_false] at hb ⊢
          exact ihn env hb
      dsimp only
      generalize simplifyExp condition = C at hc' hbase ⊢
      generalize simplifyExp yes = Y at hbase ⊢
      generalize simplifyExp no = N at hbase ⊢
      split
      · rename_i z
        obtain ⟨c2, hc2, hb2⟩ := eval_ite_iff.mp hbase
        obtain ⟨he, rfl⟩ := int_value hc2
        cases he
        exact hb2
      · exact hbase
  | bin op left right ihl ihr =>
    rw [simplifyExp]; split
    · exact simplify_shortcut h (by assumption)
    · obtain ⟨lw, rw, a, b, hl, hr, hb⟩ := eval_bin_iff.mp h
      have hl' := ihl env hl
      have hr' := ihr env hr
      have hbase : evalExp env (.bin op (simplifyExp left) (simplifyExp right)) = .ok result :=
        eval_bin_iff.mpr ⟨lw, rw, a, b, hl', hr', hb⟩
      dsimp only
      generalize simplifyExp left = L at hl' hbase ⊢
      generalize simplifyExp right = R at hr' hbase ⊢
      split
      · split
        · rename_i hz
          obtain ⟨b', hb', he⟩ := bin_inv_left hbase
          rw [hz.1] at he
          simp [evalBin] at he
          rw [hb', he]
        · exact hbase
      · split
        · rename_i hz
          obtain ⟨a', ha', he⟩ := bin_inv_right hbase
          rw [hz.1] at he
          simp [evalBin] at he
          rw [ha', he]
        · exact hbase
      · split
        · rename_i hz
          obtain ⟨a', ha', he⟩ := bin_inv_right hbase
          rw [hz.1] at he
          simp [evalBin] at he
          rw [ha', he]
        · exact hbase
      · split
        · exact hbase
        · split
          · rename_i hz
            obtain ⟨b', hb', he⟩ := bin_inv_left hbase
            rw [hz] at he
            simp [evalBin] at he
            rw [hb', he]
          · split
            · rename_i hz
              obtain ⟨b', hb', he⟩ := bin_inv_left hbase
              rw [hz.1] at he
              simp [evalBin] at he
              rw [← he, hz.1]
              rfl
            · exact hbase
      · split
        · exact hbase
        · split
          · rename_i hz
            obtain ⟨a', ha', he⟩ := bin_inv_right hbase
            rw [hz] at he
            simp [evalBin] at he
            rw [ha', he]
          · split
            · rename_i hz
              obtain ⟨a', ha', he⟩ := bin_inv_right hbase
              rw [hz.1] at he
              simp [evalBin] at he
              rw [← he, hz.1]
              rfl
            · exact hbase
      · exact hbase

private theorem hasImmWidth_iff {exp : Exp} {width : Nat} :
    hasImmWidth exp width = true ↔ inferExp exp = .ok (.imm width) := by
  simp only [hasImmWidth]
  split
  · rename_i he
    simp only [beq_iff_eq]
    constructor
    · rintro rfl; exact he
    · intro h
      rw [he] at h
      simpa using h
  · rename_i hne
    simp only [Bool.false_eq_true, false_iff]
    intro h
    exact hne _ h

/-- Simplifying can only drop variable occurrences. -/
theorem occursFree_simplifyExp {v : Bap.Var} (exp : Exp) (h : occursFree v (simplifyExp exp) = true) :
    occursFree v exp = true := by
  induction exp with
  | int value => rw [simplifyExp] at h; split at h <;> simp [occursFree] at h
  | var var =>
    rw [simplifyExp] at h
    split at h
    · simp [occursFree] at h
    · exact h
  | unknown message typ => rw [simplifyExp] at h; split at h <;> simp [occursFree] at h
  | load _ _ _ _ ih1 ih2 =>
    rw [simplifyExp] at h; split at h
    · simp [occursFree] at h
    · simp only [occursFree, Bool.or_eq_true] at h ⊢
      exact h.imp ih1 ih2
  | store _ _ _ _ _ ih1 ih2 ih3 =>
    rw [simplifyExp] at h; split at h
    · simp [occursFree] at h
    · simp only [occursFree, Bool.or_eq_true] at h ⊢
      exact h.imp (fun h => h.imp ih1 ih2) ih3
  | concat _ _ ih1 ih2 =>
    rw [simplifyExp] at h; split at h
    · simp [occursFree] at h
    · simp only [occursFree, Bool.or_eq_true] at h ⊢
      exact h.imp ih1 ih2
  | un _ _ ih =>
    rw [simplifyExp] at h; split at h
    · simp [occursFree] at h
    · simpa only [occursFree] using ih h
  | cast _ _ _ ih =>
    rw [simplifyExp] at h; split at h
    · simp [occursFree] at h
    · simpa only [occursFree] using ih h
  | extract _ _ _ ih =>
    rw [simplifyExp] at h; split at h
    · simp [occursFree] at h
    · simpa only [occursFree] using ih h
  | letIn var _ _ ih1 ih2 =>
    rw [simplifyExp] at h; split at h
    · simp [occursFree] at h
    · simp only [occursFree, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
      exact h.imp ih1 (fun h => ⟨h.1, ih2 h.2⟩)
  | ite c y n ih1 ih2 ih3 =>
    rw [simplifyExp] at h; split at h
    · simp [occursFree] at h
    · dsimp only at h
      simp only [occursFree, Bool.or_eq_true]
      generalize hC : simplifyExp c = C at h ih1
      split at h
      · split at h
        · exact Or.inl (Or.inr (ih2 h))
        · exact Or.inr (ih3 h)
      · simp only [occursFree, Bool.or_eq_true] at h
        exact h.imp (fun h => h.imp ih1 ih2) ih3
  | bin op l r ih1 ih2 =>
    rw [simplifyExp] at h; split at h
    · simp [occursFree] at h
    · dsimp only at h
      simp only [occursFree, Bool.or_eq_true]
      generalize simplifyExp l = L at h ih1
      generalize simplifyExp r = R at h ih2
      have hbin : occursFree v (.bin op L R) = true → occursFree v l = true ∨ occursFree v r = true := by
        simp only [occursFree, Bool.or_eq_true]
        exact fun h => h.imp ih1 ih2
      split at h
      all_goals (repeat' split at h)
      all_goals first
        | exact hbin h
        | exact Or.inr (ih2 h)
        | exact Or.inl (ih1 h)
        | exact Or.inl (ih1 (by simpa [occursFree] using h))
        | exact Or.inr (ih2 (by simpa [occursFree] using h))

private theorem eval_bin_left_error {env : Env} {op : BinOp} {L R : Exp} {e : String}
    (h : evalExp env L = .error e) : evalExp env (.bin op L R) = .error e := by
  simp only [evalExp, h, Bind.bind, Except.bind]

private theorem eval_bin_right_error {env : Env} {op : BinOp} {L R : Exp} {e : String} {a : BitVec w}
    (hl : evalExp env L = .ok (.bits a)) (h : evalExp env R = .error e) : evalExp env (.bin op L R) = .error e := by
  simp only [evalExp, hl, h, Bind.bind, Except.bind, Value.asBits]

/-- A right-neutral literal: `L op z` means `L` for well-typed `L` of the literal's width. -/
private theorem bin_neutral_right {env : Env} {op : BinOp} {L R : Exp} {z : BitVec w}
    (hR : evalExp env R = .ok (.bits z))
    (hneutral : ∀ a : BitVec w, evalBin op ⟨w, a⟩ ⟨w, z⟩ = .ok (.bits a))
    (hwt : WellTypedEnv env) (hty : inferExp L = .ok (.imm w)) :
    evalExp env L = evalExp env (.bin op L R) := by
  cases hl : evalExp env L with
  | error e => rw [eval_bin_left_error hl]
  | ok x =>
    obtain ⟨a, rfl⟩ := bits_of_type (evalExp_type_sound hwt _ hty hl)
    exact (eval_bin_iff.mpr ⟨w, w, a, z, hl, hR, hneutral a⟩).symm

private theorem bin_neutral_left {env : Env} {op : BinOp} {L R : Exp} {z : BitVec w}
    (hL : evalExp env L = .ok (.bits z))
    (hneutral : ∀ b : BitVec w, evalBin op ⟨w, z⟩ ⟨w, b⟩ = .ok (.bits b))
    (hwt : WellTypedEnv env) (hty : inferExp R = .ok (.imm w)) :
    evalExp env R = evalExp env (.bin op L R) := by
  cases hr : evalExp env R with
  | error e => rw [eval_bin_right_error hL hr]
  | ok x =>
    obtain ⟨b, rfl⟩ := bits_of_type (evalExp_type_sound hwt _ hty hr)
    exact (eval_bin_iff.mpr ⟨w, w, z, b, hL, hr, hneutral b⟩).symm

/-- Simplification preserves evaluation exactly, error messages included, for a well-typed
expression whose free variables are bound in a well-typed environment. Bindings are needed because,
like the reference simplifier, `x * 0` becomes `0` without looking `x` up. -/
theorem evalExp_simplifyExp_exact (exp : Exp) {t : Typ} (hi : inferExp exp = .ok t) {env : Env}
    (hwt : WellTypedEnv env) (hb : ∀ v, occursFree v exp = true → ∃ value, lookup env v = .ok value) :
    evalExp env (simplifyExp exp) = evalExp env exp := by
  induction exp generalizing env t with
  | int value =>
    rw [simplifyExp]; split
    · rename_i hv; exact (evalExp_extends (nil_extends env) _ hv).symm
    · rfl
  | var var =>
    rw [simplifyExp]; split
    · rename_i hv; exact (evalExp_extends (nil_extends env) _ hv).symm
    · rfl
  | unknown message typ =>
    rw [simplifyExp]; split
    · rename_i hv; exact (evalExp_extends (nil_extends env) _ hv).symm
    · rfl
  | load memory address endian size ihm iha =>
    obtain ⟨w, hmt, hat, _⟩ := infer_load_inv hi
    rw [simplifyExp]; split
    · rename_i hv; exact (evalExp_extends (nil_extends env) _ hv).symm
    · simp only [evalExp, ihm hmt hwt (fun v h => hb v (by simp [occursFree, h])),
        iha hat hwt (fun v h => hb v (by simp [occursFree, h]))]
  | store memory address value endian size ihm iha ihv =>
    obtain ⟨w, hmt, hat, hvt, _⟩ := infer_store_inv hi
    rw [simplifyExp]; split
    · rename_i hv; exact (evalExp_extends (nil_extends env) _ hv).symm
    · simp only [evalExp, ihm hmt hwt (fun v h => hb v (by simp [occursFree, h])),
        iha hat hwt (fun v h => hb v (by simp [occursFree, h])),
        ihv hvt hwt (fun v h => hb v (by simp [occursFree, h]))]
  | un op value ih =>
    obtain ⟨w, hvt, _⟩ := infer_un_inv hi
    rw [simplifyExp]; split
    · rename_i hv; exact (evalExp_extends (nil_extends env) _ hv).symm
    · simp only [evalExp, ih hvt hwt (fun v h => hb v (by simpa [occursFree] using h))]
  | cast kind width value ih =>
    obtain ⟨_, hvt, _⟩ := infer_cast_inv hi
    rw [simplifyExp]; split
    · rename_i hv; exact (evalExp_extends (nil_extends env) _ hv).symm
    · simp only [evalExp, ih hvt hwt (fun v h => hb v (by simpa [occursFree] using h))]
  | extract high low value ih =>
    obtain ⟨_, hvt, _⟩ := infer_extract_inv hi
    rw [simplifyExp]; split
    · rename_i hv; exact (evalExp_extends (nil_extends env) _ hv).symm
    · simp only [evalExp, ih hvt hwt (fun v h => hb v (by simpa [occursFree] using h))]
  | concat left right ihl ihr =>
    obtain ⟨_, _, hlt, hrt, _⟩ := infer_concat_inv hi
    rw [simplifyExp]; split
    · rename_i hv; exact (evalExp_extends (nil_extends env) _ hv).symm
    · simp only [evalExp, ihl hlt hwt (fun v h => hb v (by simp [occursFree, h])),
        ihr hrt hwt (fun v h => hb v (by simp [occursFree, h]))]
  | letIn var value body ihv ihb =>
    obtain ⟨hvt, hbt⟩ := infer_let_inv hi
    rw [simplifyExp]; split
    · rename_i hv; exact (evalExp_extends (nil_extends env) _ hv).symm
    · have hvalue := ihv hvt hwt (fun v h => hb v (by simp [occursFree, h]))
      simp only [evalExp, hvalue]
      cases hx : evalExp env value with
      | error e => rfl
      | ok x =>
        apply ihb hbt (hwt.bind (evalExp_type_sound hwt _ hvt hx))
        intro v h
        by_cases he : v = var
        · exact ⟨x, by simp [he, lookup_bind_eq]⟩
        · rw [lookup_bind_other _ _ he]
          exact hb v (by simp [occursFree, h, Ne.symm he])
  | ite condition yes no ihc ihy ihn =>
    obtain ⟨hct, hyt, hnt⟩ := infer_ite_inv hi
    rw [simplifyExp]; split
    · rename_i hv; exact (evalExp_extends (nil_extends env) _ hv).symm
    · have h1 := ihc hct hwt (fun v h => hb v (by simp [occursFree, h]))
      have h2 := ihy hyt hwt (fun v h => hb v (by simp [occursFree, h]))
      have h3 := ihn hnt hwt (fun v h => hb v (by simp [occursFree, h]))
      dsimp only
      have hbase : evalExp env (.ite (simplifyExp condition) (simplifyExp yes) (simplifyExp no)) =
          evalExp env (.ite condition yes no) := by
        simp only [evalExp, h1, h2, h3]
      generalize simplifyExp condition = C at h1 hbase ⊢
      generalize simplifyExp yes = Y at h2 hbase ⊢
      generalize simplifyExp no = N at h3 hbase ⊢
      split
      · rename_i z
        rw [← hbase]
        simp only [evalExp, Bind.bind, Except.bind, Value.asBits, ↓reduceDIte]
        split <;> rfl
      · exact hbase
  | bin op left right ihl ihr =>
    obtain ⟨w, hlt, hrt, _⟩ := infer_bin_inv hi
    rw [simplifyExp]; split
    · rename_i hv; exact (evalExp_extends (nil_extends env) _ hv).symm
    · have hbl : ∀ v, occursFree v left = true → ∃ value, lookup env v = .ok value :=
        fun v h => hb v (by simp [occursFree, h])
      have hbr : ∀ v, occursFree v right = true → ∃ value, lookup env v = .ok value :=
        fun v h => hb v (by simp [occursFree, h])
      have h1 := ihl hlt hwt hbl
      have h2 := ihr hrt hwt hbr
      dsimp only
      have hbase : evalExp env (.bin op (simplifyExp left) (simplifyExp right)) = evalExp env (.bin op left right) := by
        simp only [evalExp, h1, h2]
      have hbL : ∀ v, occursFree v (simplifyExp left) = true → ∃ value, lookup env v = .ok value :=
        fun v h => hbl v (occursFree_simplifyExp _ h)
      have hbR : ∀ v, occursFree v (simplifyExp right) = true → ∃ value, lookup env v = .ok value :=
        fun v h => hbr v (occursFree_simplifyExp _ h)
      rw [← hbase]
      generalize simplifyExp left = L at hbL ⊢
      generalize simplifyExp right = R at hbR ⊢
      split
      · split
        · rename_i hz
          obtain ⟨rfl, hw⟩ := hz
          exact bin_neutral_left rfl (fun b => by simp [evalBin]) hwt (hasImmWidth_iff.mp hw)
        · rfl
      · split
        · rename_i hz
          obtain ⟨rfl, hw⟩ := hz
          exact bin_neutral_right rfl (fun a => by simp [evalBin]) hwt (hasImmWidth_iff.mp hw)
        · rfl
      · split
        · rename_i hz
          obtain ⟨rfl, hw⟩ := hz
          exact bin_neutral_right rfl (fun a => by simp [evalBin]) hwt (hasImmWidth_iff.mp hw)
        · rfl
      · split
        · rfl
        · rename_i hw
          have hw' := hasImmWidth_iff.mp (by simpa using hw)
          split
          · rename_i hz
            subst hz
            exact bin_neutral_left rfl (fun b => by simp [evalBin]) hwt hw'
          · split
            · rename_i hz
              obtain ⟨hz0, hu⟩ := hz
              subst hz0
              obtain ⟨x, hx, hty⟩ := evalExp_progress R (by simpa using hu) hw' hwt hbR
              obtain ⟨b, rfl⟩ := bits_of_type hty
              exact (eval_bin_iff.mpr ⟨_, _, _, b, rfl, hx, by simp [evalBin]⟩).symm
            · rfl
      · split
        · rfl
        · rename_i hw
          have hw' := hasImmWidth_iff.mp (by simpa using hw)
          split
          · rename_i hz
            subst hz
            exact bin_neutral_right rfl (fun a => by simp [evalBin]) hwt hw'
          · split
            · rename_i hz
              obtain ⟨hz0, hu⟩ := hz
              subst hz0
              obtain ⟨x, hx, hty⟩ := evalExp_progress L (by simpa using hu) hw' hwt hbL
              obtain ⟨a, rfl⟩ := bits_of_type hty
              exact (eval_bin_iff.mpr ⟨_, _, a, _, hx, rfl, by simp [evalBin]⟩).symm
            · rfl
      · rfl

/-- Intended: an unbound variable under `* 0` is dropped, as in the reference simplifier's
`TIMES, x, _ when is0 x`, so `evalExp_simplifyExp_exact` needs its variables to be bound. -/
theorem simplify_drops_unbound_variable (var : Bap.Var) (h : var.typ = .imm 8) :
    (evalExp [] (.bin .mul (.int (0#8)) (.var var))).toOption = none ∧
      evalExp [] (simplifyExp (.bin .mul (.int (0#8)) (.var var))) = .ok (.bits (0#8)) := by
  have horig : evalExp [] (.bin .mul (.int (0#8)) (.var var)) = .error s!"unbound variable {var.name}" := by
    simp [evalExp, lookup, Bind.bind, Except.bind, Value.asBits]
  refine ⟨by rw [horig]; rfl, ?_⟩
  rw [simplifyExp, horig]
  simp [simplifyExp, evalExp, lookup, hasImmWidth, inferExp, expectBits, h, hasUnknown, Bind.bind, Except.bind, Value.asBits]

/-- Width errors survive simplification. -/
theorem simplify_keeps_width_error :
    evalExp [] (simplifyExp (.bin .add (.int (0#8)) (.int (1#16)))) =
      .error "binary operands have different widths" := by
  have horig : evalExp [] (.bin .add (.int (0#8)) (.int (1#16))) = .error "binary operands have different widths" := rfl
  rw [simplifyExp, horig]
  simp [simplifyExp, evalExp, hasImmWidth, inferExp, expectBits, Bind.bind, Except.bind, Value.asBits, evalBin]

/-- `0 * unknown` keeps failing: the annihilator rule never drops an `unknown`. -/
theorem simplify_keeps_unknown_error :
    evalExp [] (simplifyExp (.bin .mul (.int (0#8)) (.unknown "x" (.imm 8)))) =
      .error "cannot evaluate unknown value: x" := by
  have horig : evalExp [] (.bin .mul (.int (0#8)) (.unknown "x" (.imm 8))) =
      .error "cannot evaluate unknown value: x" := rfl
  rw [simplifyExp, horig]
  simp [simplifyExp, evalExp, hasImmWidth, inferExp, expectBits, hasUnknown, Bind.bind, Except.bind, Value.asBits]
  rfl

/-! ## The fuel interpreter -/

private abbrev fuelError : Except String (State × Effect) := .error "execution fuel exhausted"

private theorem exec_step_mono (f : Nat)
    (ihs : ∀ state stmt, execStmt f state stmt ≠ fuelError → execStmt (f + 1) state stmt = execStmt f state stmt)
    (ihp : ∀ state program, execProgram f state program ≠ fuelError →
      execProgram (f + 1) state program = execProgram f state program)
    (state : State) (stmt : Stmt) (h : execStmt (f + 1) state stmt ≠ fuelError) :
    execStmt (f + 1 + 1) state stmt = execStmt (f + 1) state stmt := by
  cases stmt with
  | move var value => simp only [execStmt]
  | jmp target => simp only [execStmt]
  | special message => simp only [execStmt]
  | cpuExn number => simp only [execStmt]
  | ifElse condition yes no =>
    simp only [execStmt, Bind.bind, Except.bind] at h ⊢
    cases hc : execExp state condition with
    | error e => simp only [hc]
    | ok v =>
      simp only [hc] at h ⊢
      cases v with
      | memory m => simp only [Value.asBits]
      | undefined => simp only [Value.asBits]
      | @bits w b =>
        simp only [Value.asBits] at h ⊢
        by_cases hw : w = 1
        · subst hw
          simp only [↓reduceDIte] at h ⊢
          exact ihp _ _ h
        · simp only [hw, ↓reduceDIte]
  | «while» condition body =>
    simp only [execStmt, Bind.bind, Except.bind] at h ⊢
    cases hc : execExp state condition with
    | error e => simp only [hc]
    | ok v =>
      simp only [hc] at h ⊢
      cases v with
      | memory m => simp only [Value.asBits]
      | undefined => simp only [Value.asBits]
      | @bits w b =>
        simp only [Value.asBits] at h ⊢
        by_cases hw : w = 1
        · subst hw
          simp only [↓reduceDIte] at h ⊢
          by_cases hb : b = 1
          · simp only [hb, ↓reduceIte] at h ⊢
            cases hp : execProgram f state body with
            | error e =>
              rw [ihp state body (by
                intro he
                rw [he] at h
                exact h rfl), hp]
            | ok r =>
              rw [ihp state body (by rw [hp]; simp), hp]
              simp only [hp] at h
              obtain ⟨next, effect⟩ := r
              cases effect with
              | normal => exact ihs _ _ h
              | jump target => rfl
              | special message => rfl
              | cpuExn number => rfl
          · simp only [hb, ↓reduceIte]
        · simp only [hw, ↓reduceDIte]

private theorem exec_mono_succ (f : Nat) :
    (∀ state stmt, execStmt f state stmt ≠ fuelError → execStmt (f + 1) state stmt = execStmt f state stmt) ∧
    (∀ state program, execProgram f state program ≠ fuelError →
      execProgram (f + 1) state program = execProgram f state program) := by
  induction f with
  | zero =>
    exact ⟨fun _ _ h => absurd (by simp [execStmt]) h, fun _ _ h => absurd (by simp [execProgram]) h⟩
  | succ f ih =>
    obtain ⟨ihs, ihp⟩ := ih
    refine ⟨exec_step_mono f ihs ihp, fun state program h => ?_⟩
    cases program with
    | nil => rfl
    | cons stmt rest =>
      simp only [execProgram, Bind.bind, Except.bind] at h ⊢
      cases hs : execStmt f state stmt with
      | error e =>
        rw [ihs state stmt (by
          intro he
          rw [he] at h
          exact h rfl), hs]
      | ok r =>
        rw [ihs state stmt (by rw [hs]; simp), hs]
        simp only [hs] at h
        obtain ⟨next, effect⟩ := r
        cases effect with
        | normal => exact ihp _ _ h
        | jump target => rfl
        | special message => rfl
        | cpuExn number => rfl

/-- Extra fuel never changes any outcome other than fuel exhaustion itself. -/
theorem execProgram_fuel_mono {fuel fuel' : Nat} (hle : fuel ≤ fuel') {state : State} {program : Program}
    (h : execProgram fuel state program ≠ .error "execution fuel exhausted") :
    execProgram fuel' state program = execProgram fuel state program := by
  induction hle with
  | refl => rfl
  | step _ ih =>
    rw [(exec_mono_succ _).2 _ _ (by rw [ih]; exact h), ih]

theorem execStmt_fuel_mono {fuel fuel' : Nat} (hle : fuel ≤ fuel') {state : State} {stmt : Stmt}
    (h : execStmt fuel state stmt ≠ .error "execution fuel exhausted") :
    execStmt fuel' state stmt = execStmt fuel state stmt := by
  induction hle with
  | refl => rfl
  | step _ ih =>
    rw [(exec_mono_succ _).1 _ _ (by rw [ih]; exact h), ih]

theorem execProgram_ok_mono {fuel fuel' : Nat} (hle : fuel ≤ fuel') {state : State} {program : Program}
    {result : State × Effect} (h : execProgram fuel state program = .ok result) :
    execProgram fuel' state program = .ok result := by
  rw [execProgram_fuel_mono hle (by rw [h]; simp), h]

theorem execStmt_ok_mono {fuel fuel' : Nat} (hle : fuel ≤ fuel') {state : State} {stmt : Stmt}
    {result : State × Effect} (h : execStmt fuel state stmt = .ok result) :
    execStmt fuel' state stmt = .ok result := by
  rw [execStmt_fuel_mono hle (by rw [h]; simp), h]

/-- Running out of fuel is the only error that more fuel can cure. -/
theorem run_error_stable {program : Program} {state : State} {fuel fuel' : Nat} {message : String}
    (hle : fuel ≤ fuel') (h : run program state fuel = .error message)
    (hne : message ≠ "execution fuel exhausted") : run program state fuel' = .error message := by
  simp only [run] at h ⊢
  rw [execProgram_fuel_mono hle (by rw [h]; simpa using hne), h]

/-! ## Interpreter inversion -/

/-- What happens after a statement finished with `effect`: run the continuation or stop abruptly. -/
def AfterStep (next : State) : Effect → Except String (State × Effect) → (State × Effect) → Prop
  | .normal, continuation, result => continuation = .ok result
  | other, _, result => result = (next, other)

theorem exec_move_iff {fuel : Nat} {state : State} {var : Bap.Var} {exp : Exp} {r : State × Effect} :
    execStmt (fuel + 1) state (.move var exp) = .ok r ↔
      ∃ value, execExp state exp = .ok value ∧ r = ({ env := Bap.Bil.bind state.env var value }, .normal) := by
  simp only [execStmt, except_bind_ok, Except.ok.injEq]
  constructor
  · rintro ⟨v, h, rfl⟩; exact ⟨v, h, rfl⟩
  · rintro ⟨v, h, rfl⟩; exact ⟨v, h, rfl⟩

theorem exec_jmp_iff {fuel : Nat} {state : State} {target : Exp} {r : State × Effect} :
    execStmt (fuel + 1) state (.jmp target) = .ok r ↔
      ∃ (w : Nat) (a : BitVec w), execExp state target = .ok (.bits a) ∧ r = (state, .jump a) := by
  simp only [execStmt, except_bind_ok, Except.ok.injEq]
  constructor
  · rintro ⟨v, h, ⟨w, a⟩, hb, rfl⟩
    rw [asBits_ok] at hb
    subst hb
    exact ⟨w, a, h, rfl⟩
  · rintro ⟨w, a, h, rfl⟩
    exact ⟨_, h, ⟨w, a⟩, rfl, rfl⟩

theorem exec_if_iff {fuel : Nat} {state : State} {condition : Exp} {yes no : Program} {r : State × Effect} :
    execStmt (fuel + 1) state (.ifElse condition yes no) = .ok r ↔
      ∃ c : BitVec 1, execExp state condition = .ok (.bits c) ∧
        execProgram fuel state (if c = 1 then yes else no) = .ok r := by
  simp only [execStmt, except_bind_ok]
  constructor
  · rintro ⟨v, h, ⟨w, b⟩, hb, he⟩
    rw [asBits_ok] at hb
    subst hb
    simp only at he
    split at he
    · rename_i hw
      cases hw
      exact ⟨b, h, he⟩
    · simp at he
  · rintro ⟨c, h, he⟩
    exact ⟨_, h, ⟨1, c⟩, rfl, by simpa using he⟩

theorem exec_while_iff {fuel : Nat} {state : State} {condition : Exp} {body : Program} {r : State × Effect} :
    execStmt (fuel + 1) state (.while condition body) = .ok r ↔
      ∃ c : BitVec 1, execExp state condition = .ok (.bits c) ∧
        ((c = 1 ∧ ∃ next effect, execProgram fuel state body = .ok (next, effect) ∧
            AfterStep next effect (execStmt fuel next (.while condition body)) r) ∨
          (c ≠ 1 ∧ r = (state, .normal))) := by
  simp only [execStmt, except_bind_ok]
  constructor
  · rintro ⟨v, h, ⟨w, b⟩, hb, he⟩
    rw [asBits_ok] at hb
    subst hb
    simp only at he
    split at he
    · rename_i hw
      cases hw
      refine ⟨b, h, ?_⟩
      simp only at he
      split at he
      · rename_i hc
        obtain ⟨⟨next, effect⟩, hp, hk⟩ := except_bind_ok.mp he
        refine Or.inl ⟨hc, next, effect, hp, ?_⟩
        cases effect with
        | normal => exact hk
        | jump target => simpa [AfterStep, eq_comm] using hk
        | special message => simpa [AfterStep, eq_comm] using hk
        | cpuExn number => simpa [AfterStep, eq_comm] using hk
      · rename_i hc
        simp only [Except.ok.injEq] at he
        exact Or.inr ⟨hc, he.symm⟩
    · simp at he
  · rintro ⟨c, h, hor⟩
    refine ⟨_, h, ⟨1, c⟩, rfl, ?_⟩
    rcases hor with ⟨hc, next, effect, hp, hk⟩ | ⟨hc, rfl⟩
    · simp only [↓reduceDIte, hc, ↓reduceIte]
      refine except_bind_ok.mpr ⟨(next, effect), hp, ?_⟩
      cases effect with
      | normal => exact hk
      | jump target => subst hk; rfl
      | special message => subst hk; rfl
      | cpuExn number => subst hk; rfl
    · simp only [↓reduceDIte]
      rw [ite_eq_right hc]

theorem exec_cons_iff {fuel : Nat} {state : State} {stmt : Stmt} {rest : Program} {r : State × Effect} :
    execProgram (fuel + 1) state (stmt :: rest) = .ok r ↔
      ∃ next effect, execStmt fuel state stmt = .ok (next, effect) ∧
        AfterStep next effect (execProgram fuel next rest) r := by
  simp only [execProgram, except_bind_ok]
  constructor
  · rintro ⟨⟨next, effect⟩, hs, hk⟩
    refine ⟨next, effect, hs, ?_⟩
    cases effect with
    | normal => exact hk
    | jump target => simpa [AfterStep, eq_comm] using hk
    | special message => simpa [AfterStep, eq_comm] using hk
    | cpuExn number => simpa [AfterStep, eq_comm] using hk
  · rintro ⟨next, effect, hs, hk⟩
    refine ⟨(next, effect), hs, ?_⟩
    cases effect with
    | normal => exact hk
    | jump target => subst hk; rfl
    | special message => subst hk; rfl
    | cpuExn number => subst hk; rfl

private theorem exec_preserves (fuel : Nat) :
    (∀ state stmt r, WellTypedEnv state.env → checkStmt stmt = .ok () → execStmt fuel state stmt = .ok r →
      WellTypedEnv r.1.env) ∧
    (∀ state program r, WellTypedEnv state.env → checkProgram program = .ok () →
      execProgram fuel state program = .ok r → WellTypedEnv r.1.env) := by
  induction fuel with
  | zero => exact ⟨fun _ _ _ _ _ h => by simp [execStmt] at h, fun _ _ _ _ _ h => by simp [execProgram] at h⟩
  | succ f ih =>
    obtain ⟨ihs, ihp⟩ := ih
    constructor
    · intro state stmt r hwt hc he
      cases stmt with
      | move var value =>
        obtain ⟨v, hv, rfl⟩ := exec_move_iff.mp he
        simp only [checkStmt, except_bind_ok] at hc
        obtain ⟨t, ht, hif⟩ := hc
        have hty := evalExp_type_sound hwt value ht hv
        split at hif
        · rename_i hvar
          exact hwt.bind (hty.trans hvar.symm)
        · simp at hif
      | jmp target =>
        obtain ⟨w, a, _, rfl⟩ := exec_jmp_iff.mp he
        exact hwt
      | special message =>
        simp only [execStmt, Except.ok.injEq] at he
        subst he; exact hwt
      | cpuExn number =>
        simp only [execStmt, Except.ok.injEq] at he
        subst he; exact hwt
      | ifElse condition yes no =>
        obtain ⟨c, _, hp⟩ := exec_if_iff.mp he
        simp only [checkStmt, except_bind_ok] at hc
        obtain ⟨_, _, ⟨⟩, hy, hn⟩ := hc
        by_cases hc1 : c = 1
        · rw [ite_eq_left hc1] at hp
          exact ihp _ _ _ hwt hy hp
        · rw [ite_eq_right hc1] at hp
          exact ihp _ _ _ hwt hn hp
      | «while» condition body =>
        obtain ⟨c, _, hor⟩ := exec_while_iff.mp he
        rcases hor with ⟨_, next, effect, hp, hk⟩ | ⟨_, rfl⟩
        · have hcheck := hc
          simp only [checkStmt, except_bind_ok] at hc
          obtain ⟨_, _, hb⟩ := hc
          have hn := ihp _ _ _ hwt hb hp
          cases effect with
          | normal => exact ihs _ _ _ hn hcheck hk
          | jump target => subst hk; exact hn
          | special message => subst hk; exact hn
          | cpuExn number => subst hk; exact hn
        · exact hwt
    · intro state program r hwt hc he
      cases program with
      | nil =>
        simp only [execProgram, Except.ok.injEq] at he
        subst he; exact hwt
      | cons stmt rest =>
        obtain ⟨next, effect, hs, hk⟩ := exec_cons_iff.mp he
        simp only [checkProgram, except_bind_ok] at hc
        obtain ⟨_, hcs, hcr⟩ := hc
        have hn := ihs _ _ _ hwt hcs hs
        cases effect with
        | normal => exact ihp _ _ _ hn hcr hk
        | jump target => subst hk; exact hn
        | special message => subst hk; exact hn
        | cpuExn number => subst hk; exact hn

/-- Type preservation at statement level: a checked program never breaks the environment's typing. -/
theorem execProgram_preserves_wellTyped {fuel : Nat} {state : State} {program : Program} {r : State × Effect}
    (hwt : WellTypedEnv state.env) (hc : checkProgram program = .ok ())
    (he : execProgram fuel state program = .ok r) : WellTypedEnv r.1.env :=
  (exec_preserves fuel).2 _ _ _ hwt hc he

/-- Consequently every variable read after running a checked program has its declared type. -/
theorem run_lookup_type {program : Program} {fuel : Nat} {r : State × Effect} {var : Bap.Var} {value : Value}
    (hc : checkProgram program = .ok ()) (he : run program {} fuel = .ok r)
    (hl : lookup r.1.env var = .ok value) : value.type = var.typ :=
  (execProgram_preserves_wellTyped (state := {}) wellTypedEnv_nil hc he).lookup hl

/-- Executing a statement never removes a binding (the environment only grows or updates). -/
private theorem exec_keeps_bound (fuel : Nat) :
    (∀ state stmt r var, execStmt fuel state stmt = .ok r →
      (∃ v, lookup state.env var = .ok v) → ∃ v, lookup r.1.env var = .ok v) ∧
    (∀ state program r var, execProgram fuel state program = .ok r →
      (∃ v, lookup state.env var = .ok v) → ∃ v, lookup r.1.env var = .ok v) := by
  induction fuel with
  | zero => exact ⟨fun _ _ _ _ h => by simp [execStmt] at h, fun _ _ _ _ h => by simp [execProgram] at h⟩
  | succ f ih =>
    obtain ⟨ihs, ihp⟩ := ih
    constructor
    · intro state stmt r var he hb
      cases stmt with
      | move target value =>
        obtain ⟨v, _, rfl⟩ := exec_move_iff.mp he
        by_cases hvar : var = target
        · exact ⟨v, by simp [hvar, lookup_bind_eq]⟩
        · simpa [lookup_bind_other _ _ hvar] using hb
      | jmp target =>
        obtain ⟨w, a, _, rfl⟩ := exec_jmp_iff.mp he
        exact hb
      | special message =>
        simp only [execStmt, Except.ok.injEq] at he
        subst he; exact hb
      | cpuExn number =>
        simp only [execStmt, Except.ok.injEq] at he
        subst he; exact hb
      | ifElse condition yes no =>
        obtain ⟨c, _, hp⟩ := exec_if_iff.mp he
        exact ihp _ _ _ _ hp hb
      | «while» condition body =>
        obtain ⟨c, _, hor⟩ := exec_while_iff.mp he
        rcases hor with ⟨_, next, effect, hp, hk⟩ | ⟨_, rfl⟩
        · have hn := ihp _ _ _ var hp hb
          cases effect with
          | normal => exact ihs _ _ _ _ hk hn
          | jump target => subst hk; exact hn
          | special message => subst hk; exact hn
          | cpuExn number => subst hk; exact hn
        · exact hb
    · intro state program r var he hb
      cases program with
      | nil =>
        simp only [execProgram, Except.ok.injEq] at he
        subst he; exact hb
      | cons stmt rest =>
        obtain ⟨next, effect, hs, hk⟩ := exec_cons_iff.mp he
        have hn := ihs _ _ _ var hs hb
        cases effect with
        | normal => exact ihp _ _ _ _ hk hn
        | jump target => subst hk; exact hn
        | special message => subst hk; exact hn
        | cpuExn number => subst hk; exact hn

theorem execProgram_keeps_bound {fuel : Nat} {state : State} {program : Program} {r : State × Effect}
    (he : execProgram fuel state program = .ok r) {var : Bap.Var} (hb : ∃ v, lookup state.env var = .ok v) :
    ∃ v, lookup r.1.env var = .ok v :=
  (exec_keeps_bound fuel).2 _ _ _ var he hb

/-! ## Nothing well-typed lacks bits, and a well-typed program can only run out of fuel

The checker rejects what has no bits: a zero-width constant, variable or `unknown`, and a load or store of no bytes.
Concrete evaluation gives these a degenerate value, a `BitVec 0`, but neither upstream, whose `Size.t` starts at a
byte and whose `Type.imm` starts at a bit, nor SMT-LIB, which has no sort for them, has them at all. It also rejects a
store that covers an address twice: the evaluator lets the last byte win, but no load gets the stored value back. -/

private theorem expectBits_has_bits {t t' : Typ} (h : expectBits t = .ok t') :
    (∀ w, t' = .imm w → 0 < w) ∧ (∀ a v, t' = .mem a v → 0 < a ∧ 0 < v) := by
  unfold expectBits at h
  split at h
  · cases h
  · cases h
  · cases h
  · next t hi hm hm' =>
    cases h
    refine ⟨fun w he => Nat.pos_of_ne_zero fun hz => hi (by rw [he, hz]), fun a v he => ?_⟩
    exact ⟨Nat.pos_of_ne_zero fun hz => hm v (by rw [he, hz]), Nat.pos_of_ne_zero fun hz => hm' a (by rw [he, hz])⟩

/-- Every type the checker infers has bits. -/
theorem inferExp_has_bits (exp : Exp) :
    (∀ w, inferExp exp = .ok (.imm w) → 0 < w) ∧ (∀ a v, inferExp exp = .ok (.mem a v) → 0 < a ∧ 0 < v) := by
  induction exp with
  | int value =>
    refine ⟨fun w h => (expectBits_has_bits h).1 w rfl, fun a v h => (expectBits_has_bits h).2 a v rfl⟩
  | var var =>
    refine ⟨fun w h => (expectBits_has_bits h).1 w rfl, fun a v h => (expectBits_has_bits h).2 a v rfl⟩
  | unknown message typ =>
    refine ⟨fun w h => (expectBits_has_bits h).1 w rfl, fun a v h => (expectBits_has_bits h).2 a v rfl⟩
  | load memory address endian size =>
    refine ⟨fun w h => ?_, fun a v h => ?_⟩
    · obtain ⟨_, _, _, he, hz⟩ := infer_load_inv h
      cases he
      have := Nat.pos_of_ne_zero hz
      omega
    · obtain ⟨_, _, _, he, _⟩ := infer_load_inv h
      cases he
  | store memory address value endian size ihm =>
    refine ⟨fun w h => ?_, fun a v h => ?_⟩
    · obtain ⟨_, _, _, _, he, _⟩ := infer_store_inv h
      cases he
    · obtain ⟨_, hm, _, _, he, _⟩ := infer_store_inv h
      cases he
      exact ihm.2 _ _ hm
  | bin op left right ihl =>
    refine ⟨fun w h => ?_, fun a v h => ?_⟩
    · obtain ⟨w', hl, _, he⟩ := infer_bin_inv h
      have := ihl.1 _ hl
      revert he
      split <;> (intro he; cases he; first | omega | exact Nat.one_pos)
    · obtain ⟨w', hl, _, he⟩ := infer_bin_inv h
      revert he
      split <;> (intro he; cases he)
  | un op value ih =>
    refine ⟨fun w h => ?_, fun a v h => ?_⟩
    · obtain ⟨w', hv, he⟩ := infer_un_inv h
      cases he
      exact ih.1 _ hv
    · obtain ⟨w', hv, he⟩ := infer_un_inv h
      cases he
  | cast kind width value =>
    refine ⟨fun w h => ?_, fun a v h => ?_⟩
    · obtain ⟨_, _, he, hz, _⟩ := infer_cast_inv h
      cases he
      exact Nat.pos_of_ne_zero hz
    · obtain ⟨_, _, he, _⟩ := infer_cast_inv h
      cases he
  | letIn var value body _ ihb =>
    obtain := ihb
    exact ⟨fun w h => ihb.1 _ (infer_let_inv h).2, fun a v h => ihb.2 _ _ (infer_let_inv h).2⟩
  | ite condition yes no _ ihy =>
    exact ⟨fun w h => ihy.1 _ (infer_ite_inv h).2.1, fun a v h => ihy.2 _ _ (infer_ite_inv h).2.1⟩
  | extract high low value =>
    refine ⟨fun w h => ?_, fun a v h => ?_⟩
    · obtain ⟨_, _, he, _⟩ := infer_extract_inv h
      cases he
      omega
    · obtain ⟨_, _, he, _⟩ := infer_extract_inv h
      cases he
  | concat left right ihl =>
    refine ⟨fun w h => ?_, fun a v h => ?_⟩
    · obtain ⟨_, _, hl, _, he⟩ := infer_concat_inv h
      cases he
      have := ihl.1 _ hl
      omega
    · obtain ⟨_, _, _, _, he⟩ := infer_concat_inv h
      cases he

theorem infer_int_zero_rejected (value : BitVec 0) : (inferExp (.int value)).toOption = none := rfl

theorem infer_var_zero_rejected {var : Bap.Var} (h : var.typ = .imm 0) : (inferExp (.var var)).toOption = none := by
  simp [inferExp, h, expectBits, Except.toOption]

theorem infer_unknown_zero_rejected (message : String) : (inferExp (.unknown message (.imm 0))).toOption = none := rfl

theorem infer_load_zero_rejected {memory address : Exp} {w : Nat} (endian : Endian)
    (hm : inferExp memory = .ok (.mem w 8)) (ha : inferExp address = .ok (.imm w)) :
    inferExp (.load memory address endian 0) = .error "a load must have at least one byte" := by
  simp [inferExp, hm, ha, Bind.bind, Except.bind, expectImm]

/-- A store that writes no bytes is rejected for its value, or for its size if that had no bits. -/
theorem infer_store_zero_rejected (memory address value : Exp) (endian : Endian) :
    (inferExp (.store memory address value endian 0)).toOption = none := by
  cases h : inferExp (.store memory address value endian 0) with
  | error e => rfl
  | ok t =>
    obtain ⟨_, _, _, _, _, hz, _⟩ := infer_store_inv h
    exact absurd rfl hz

/-- A store that covers an address twice is rejected. -/
theorem infer_store_overlap_rejected {memory address value : Exp} {w size : Nat} (endian : Endian)
    (hfit : 2 ^ w < size) (hm : inferExp memory = .ok (.mem w 8)) (ha : inferExp address = .ok (.imm w))
    (hv : inferExp value = .ok (.imm (size * 8))) :
    inferExp (.store memory address value endian size) = .error "a store must not overlap itself" := by
  have hz : size ≠ 0 := by have := Nat.two_pow_pos w; omega
  simp [inferExp, hm, ha, hv, hz, hfit, Bind.bind, Except.bind, expectImm]

/-- Progress with the checker's guarantee: a well-typed `unknown`-free expression evaluates, once its free variables
are bound, to a value of the inferred type that has bits. -/
theorem evalExp_progress_has_bits (exp : Exp) (hu : hasUnknown exp = false) {t : Typ} (hi : inferExp exp = .ok t)
    {env : Env} (hwt : WellTypedEnv env) (hb : ∀ v, occursFree v exp = true → ∃ value, lookup env v = .ok value) :
    ∃ value, evalExp env exp = .ok value ∧ value.type = t ∧ ∀ {w} (b : BitVec w), value = .bits b → 0 < w := by
  obtain ⟨value, hv, ht⟩ := evalExp_progress exp hu hi hwt hb
  refine ⟨value, hv, ht, fun b he => ?_⟩
  subst he
  simp only [Value.type] at ht
  subst ht
  exact (inferExp_has_bits exp).1 _ hi

mutual
  /-- No expression of a statement has an `unknown`, which the concrete evaluator has no value for. -/
  def stmtKnown : Stmt → Bool
    | .move _ value | .jmp value => !hasUnknown value
    | .special _ | .cpuExn _ => true
    | .while condition body => !hasUnknown condition && programKnown body
    | .ifElse condition yes no => !hasUnknown condition && programKnown yes && programKnown no

  def programKnown : Program → Bool
    | [] => true
    | stmt :: rest => stmtKnown stmt && programKnown rest
end

mutual
  /-- A variable some expression of a statement reads, if an earlier statement doesn't bind it. -/
  def stmtReads (var : Bap.Var) : Stmt → Bool
    | .move _ value | .jmp value => occursFree var value
    | .special _ | .cpuExn _ => false
    | .while condition body => occursFree var condition || programReads var body
    | .ifElse condition yes no => occursFree var condition || programReads var yes || programReads var no

  def programReads (var : Bap.Var) : Program → Bool
    | [] => false
    | stmt :: rest => stmtReads var stmt || programReads var rest
end

private theorem condition_progress {env : Env} {condition : Exp} (hc : checkCondition condition = .ok ())
    (hu : hasUnknown condition = false) (hwt : WellTypedEnv env)
    (hb : ∀ v, occursFree v condition = true → ∃ value, lookup env v = .ok value) :
    ∃ b : BitVec 1, evalExp env condition = .ok (.bits b) := by
  unfold checkCondition at hc
  simp only [except_bind_ok] at hc
  obtain ⟨t, ht, w, hw, hif⟩ := hc
  rw [expectImm_ok] at hw
  subst hw
  have hw1 : w = 1 := by
    split at hif
    · assumption
    · cases hif
  subst hw1
  obtain ⟨value, hv, hty⟩ := evalExp_progress condition hu ht hwt hb
  obtain ⟨b, rfl⟩ := bits_of_type hty
  exact ⟨b, hv⟩

/-- Progress for statements and programs: running a well-typed, `unknown`-free program whose inputs are bound in a
well-typed environment only ever fails by running out of fuel. -/
theorem exec_progress (fuel : Nat) :
    (∀ state stmt, WellTypedEnv state.env → checkStmt stmt = .ok () → stmtKnown stmt = true →
      (∀ v, stmtReads v stmt = true → ∃ value, lookup state.env v = .ok value) →
      execStmt fuel state stmt = .error "execution fuel exhausted" ∨ ∃ r, execStmt fuel state stmt = .ok r) ∧
    (∀ state program, WellTypedEnv state.env → checkProgram program = .ok () → programKnown program = true →
      (∀ v, programReads v program = true → ∃ value, lookup state.env v = .ok value) →
      execProgram fuel state program = .error "execution fuel exhausted" ∨ ∃ r, execProgram fuel state program = .ok r) := by
  induction fuel with
  | zero =>
    exact ⟨fun _ _ _ _ _ _ => .inl (by rw [execStmt]), fun _ _ _ _ _ _ => .inl (by rw [execProgram])⟩
  | succ f ih =>
    obtain ⟨ihs, ihp⟩ := ih
    refine ⟨fun state stmt hwt hc hk hb => ?_, fun state program hwt hc hk hb => ?_⟩
    · cases stmt with
      | move var value =>
        simp only [checkStmt, except_bind_ok] at hc
        obtain ⟨t, ht, _⟩ := hc
        simp only [stmtKnown, Bool.not_eq_true'] at hk
        obtain ⟨v, hv, _⟩ := evalExp_progress value hk ht hwt fun x hx => hb x (by simpa [stmtReads] using hx)
        exact .inr ⟨_, by rw [execStmt]; simp [execExp, hv, Bind.bind, Except.bind]; rfl⟩
      | jmp target =>
        simp only [checkStmt, except_bind_ok] at hc
        obtain ⟨t, ht, w, hw, _⟩ := hc
        rw [expectImm_ok] at hw
        subst hw
        simp only [stmtKnown, Bool.not_eq_true'] at hk
        obtain ⟨v, hv, hty⟩ := evalExp_progress target hk ht hwt fun x hx => hb x (by simpa [stmtReads] using hx)
        obtain ⟨b, rfl⟩ := bits_of_type hty
        exact .inr ⟨_, by rw [execStmt]; simp [execExp, hv, Value.asBits, Bind.bind, Except.bind]; rfl⟩
      | special message => exact .inr ⟨_, by rw [execStmt]⟩
      | cpuExn number => exact .inr ⟨_, by rw [execStmt]⟩
      | ifElse condition yes no =>
        simp only [checkStmt, except_bind_ok] at hc
        obtain ⟨_, hcc, _, hcy, hcn⟩ := hc
        simp only [stmtKnown, Bool.and_eq_true, Bool.not_eq_true'] at hk
        obtain ⟨⟨hkc, hky⟩, hkn⟩ := hk
        simp only [stmtReads, Bool.or_eq_true] at hb
        obtain ⟨b, hv⟩ := condition_progress hcc hkc hwt fun x hx => hb x (.inl (.inl hx))
        have hstep : execStmt (f + 1) state (.ifElse condition yes no) =
            execProgram f state (if b = 1 then yes else no) := by
          rw [execStmt]
          simp [execExp, hv, Value.asBits, Bind.bind, Except.bind]
        rw [hstep]
        by_cases h1 : b = 1
        · rw [ite_eq_left h1]
          exact ihp _ _ hwt hcy hky fun x hx => hb x (.inl (.inr hx))
        · rw [ite_eq_right h1]
          exact ihp _ _ hwt hcn hkn fun x hx => hb x (.inr hx)
      | «while» condition body =>
        have hck := hc
        have hkk := hk
        simp only [checkStmt, except_bind_ok] at hc
        obtain ⟨_, hcc, hcb⟩ := hc
        simp only [stmtKnown, Bool.and_eq_true, Bool.not_eq_true'] at hk
        obtain ⟨hkc, hkb⟩ := hk
        have hb' := hb
        simp only [stmtReads, Bool.or_eq_true] at hb'
        obtain ⟨b, hv⟩ := condition_progress hcc hkc hwt fun x hx => hb' x (.inl hx)
        have hstep : execStmt (f + 1) state (.while condition body) =
            if b = 1 then
              execProgram f state body >>= fun r => match r.2 with
                | .normal => execStmt f r.1 (.while condition body)
                | other => .ok (r.1, other)
            else .ok (state, .normal) := by
          rw [execStmt]
          simp only [execExp, hv, Value.asBits, Bind.bind, Except.bind, dite_true]
          rfl
        rw [hstep]
        by_cases h1 : b = 1
        · rw [ite_eq_left h1]
          rcases ihp _ _ hwt hcb hkb (fun x hx => hb' x (.inr hx)) with he | ⟨⟨next, effect⟩, he⟩
          · exact .inl (by simp [he, Bind.bind, Except.bind])
          · cases effect with
            | normal =>
              have hnext := ihs next (.while condition body) (execProgram_preserves_wellTyped hwt hcb he) hck hkk
                fun x hx => execProgram_keeps_bound he (hb x hx)
              simpa [he, Bind.bind, Except.bind] using hnext
            | jump target => exact .inr ⟨_, by simp [he, Bind.bind, Except.bind]; rfl⟩
            | special message => exact .inr ⟨_, by simp [he, Bind.bind, Except.bind]; rfl⟩
            | cpuExn number => exact .inr ⟨_, by simp [he, Bind.bind, Except.bind]; rfl⟩
        · rw [ite_eq_right h1]
          exact .inr ⟨_, rfl⟩
    · cases program with
      | nil => exact .inr ⟨_, by rw [execProgram]⟩
      | cons stmt rest =>
        simp only [checkProgram, except_bind_ok] at hc
        obtain ⟨_, hcs, hcr⟩ := hc
        simp only [programKnown, Bool.and_eq_true] at hk
        have hstep : execProgram (f + 1) state (stmt :: rest) =
            execStmt f state stmt >>= fun r => match r.2 with
              | .normal => execProgram f r.1 rest
              | other => .ok (r.1, other) := by
          rw [execProgram]
          rfl
        rw [hstep]
        simp only [programReads, Bool.or_eq_true] at hb
        rcases ihs _ _ hwt hcs hk.1 (fun x hx => hb x (.inl hx)) with he | ⟨⟨next, effect⟩, he⟩
        · exact .inl (by simp [he, Bind.bind, Except.bind])
        · cases effect with
          | normal =>
            have hwn : WellTypedEnv next.env := (exec_preserves f).1 _ _ _ hwt hcs he
            have hnext := ihp next rest hwn hcr hk.2
              fun x hx => (exec_keeps_bound f).1 _ _ _ x he (hb x (.inr hx))
            simpa [he, Bind.bind, Except.bind] using hnext
          | jump target => exact .inr ⟨_, by simp [he, Bind.bind, Except.bind]; rfl⟩
          | special message => exact .inr ⟨_, by simp [he, Bind.bind, Except.bind]; rfl⟩
          | cpuExn number => exact .inr ⟨_, by simp [he, Bind.bind, Except.bind]; rfl⟩

/-! ## Small-step semantics against the fuel interpreter -/

/-- Reflexive-transitive closure of `Step` up to a final state and effect: normal steps until the
program is empty, or one abrupt step. -/
inductive Reach : State → Program → State → Effect → Prop where
  | done (state : State) : Reach state [] state .normal
  | step {state next final : State} {program rest : Program} {effect : Effect} :
      Step state program next rest .normal → Reach next rest final effect →
      Reach state program final effect
  | stop {state final : State} {program : Program} {effect : Effect} :
      Step state program final [] effect → (effect = .normal → False) →
      Reach state program final effect

private theorem step_append_normal {state next : State} {program rest : Program} (tail : Program)
    (h : Step state program next rest .normal) : Step state (program ++ tail) next (rest ++ tail) .normal := by
  generalize he : Effect.normal = e at h
  cases h with
  | move state var exp value rest hv => exact .move state var exp value (rest ++ tail) hv
  | ifTrue state c yes no rest hc =>
    simpa using Step.ifTrue state c yes no (rest ++ tail) hc
  | ifFalse state c yes no rest hc =>
    simpa using Step.ifFalse state c yes no (rest ++ tail) hc
  | whileTrue state c body rest hc =>
    simpa using Step.whileTrue state c body (rest ++ tail) hc
  | whileFalse state c body rest hc => exact .whileFalse state c body (rest ++ tail) hc
  | jump state target address rest hc => cases he
  | special state message rest => cases he
  | cpuExn state number rest => cases he

private theorem step_append_abrupt {state next : State} {program : Program} {effect : Effect} (tail : Program)
    (h : Step state program next [] effect) (hne : effect = .normal → False) :
    Step state (program ++ tail) next [] effect := by
  generalize hp : ([] : Program) = rest at h
  cases h with
  | jump state target address rest hc => exact .jump state target address (rest ++ tail) hc
  | special state message rest => exact .special state message (rest ++ tail)
  | cpuExn state number rest => exact .cpuExn state number (rest ++ tail)
  | move => exact (hne rfl).elim
  | ifTrue => exact (hne rfl).elim
  | ifFalse => exact (hne rfl).elim
  | whileTrue => exact (hne rfl).elim
  | whileFalse => exact (hne rfl).elim

private theorem reach_append_abrupt {state final : State} {program : Program} {effect : Effect} (tail : Program)
    (h : Reach state program final effect) (hne : effect = .normal → False) :
    Reach state (program ++ tail) final effect := by
  induction h with
  | done state => exact (hne rfl).elim
  | step hs _ ih => exact .step (step_append_normal tail hs) (ih hne)
  | stop hs hn => exact .stop (step_append_abrupt tail hs hn) hn

private theorem reach_append_normal {state middle final : State} {first second : Program} {effect : Effect}
    (h1 : Reach state first middle .normal) (h2 : Reach middle second final effect) :
    Reach state (first ++ second) final effect := by
  generalize he : Effect.normal = e at h1
  induction h1 with
  | done state => exact h2
  | step hs _ ih => exact .step (step_append_normal second hs) (ih h2 he)
  | stop hs hn => exact (hn he.symm).elim

private theorem reach_of_exec (fuel : Nat) :
    (∀ state stmt next effect, execStmt fuel state stmt = .ok (next, effect) → Reach state [stmt] next effect) ∧
    (∀ state program next effect, execProgram fuel state program = .ok (next, effect) →
      Reach state program next effect) := by
  induction fuel with
  | zero => exact ⟨fun _ _ _ _ h => by simp [execStmt] at h, fun _ _ _ _ h => by simp [execProgram] at h⟩
  | succ f ih =>
    obtain ⟨ihs, ihp⟩ := ih
    constructor
    · intro state stmt next effect he
      cases stmt with
      | move var value =>
        obtain ⟨v, hv, hr⟩ := exec_move_iff.mp he
        simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact .step (.move _ var value v [] hv) (.done _)
      | jmp target =>
        obtain ⟨w, a, ha, hr⟩ := exec_jmp_iff.mp he
        simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact .stop (.jump _ target a [] ha) (by intro h; cases h)
      | special message =>
        simp only [execStmt, Except.ok.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact .stop (.special _ message []) (by intro h; cases h)
      | cpuExn number =>
        simp only [execStmt, Except.ok.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact .stop (.cpuExn _ number []) (by intro h; cases h)
      | ifElse condition yes no =>
        obtain ⟨c, hc, hp⟩ := exec_if_iff.mp he
        rcases bit_cases c with rfl | rfl
        · simp only [ite_true] at hp
          exact .step (.ifTrue _ condition yes no [] hc) (by simpa using ihp _ _ _ _ hp)
        · simp only [show (0 : BitVec 1) ≠ 1 by decide, ite_false] at hp
          exact .step (.ifFalse _ condition yes no [] hc) (by simpa using ihp _ _ _ _ hp)
      | «while» condition body =>
        obtain ⟨c, hc, hor⟩ := exec_while_iff.mp he
        rcases hor with ⟨rfl, middle, inner, hp, hk⟩ | ⟨hne, hr⟩
        · have hb := ihp _ _ _ _ hp
          refine .step (.whileTrue _ condition body [] hc) ?_
          cases inner with
          | normal => exact reach_append_normal hb (ihs _ _ _ _ hk)
          | jump target =>
            simp only [AfterStep, Prod.mk.injEq] at hk
            obtain ⟨rfl, rfl⟩ := hk
            exact reach_append_abrupt _ hb (by intro h; cases h)
          | special message =>
            simp only [AfterStep, Prod.mk.injEq] at hk
            obtain ⟨rfl, rfl⟩ := hk
            exact reach_append_abrupt _ hb (by intro h; cases h)
          | cpuExn number =>
            simp only [AfterStep, Prod.mk.injEq] at hk
            obtain ⟨rfl, rfl⟩ := hk
            exact reach_append_abrupt _ hb (by intro h; cases h)
        · simp only [Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          rcases bit_cases c with rfl | rfl
          · exact (hne rfl).elim
          · exact .step (.whileFalse _ condition body [] hc) (.done _)
    · intro state program next effect he
      cases program with
      | nil =>
        simp only [execProgram, Except.ok.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact .done _
      | cons stmt rest =>
        obtain ⟨middle, inner, hs, hk⟩ := exec_cons_iff.mp he
        have hb := ihs _ _ _ _ hs
        have hsplit : stmt :: rest = [stmt] ++ rest := rfl
        rw [hsplit]
        cases inner with
        | normal => exact reach_append_normal hb (ihp _ _ _ _ hk)
        | jump target =>
          simp only [AfterStep, Prod.mk.injEq] at hk
          obtain ⟨rfl, rfl⟩ := hk
          exact reach_append_abrupt _ hb (by intro h; cases h)
        | special message =>
          simp only [AfterStep, Prod.mk.injEq] at hk
          obtain ⟨rfl, rfl⟩ := hk
          exact reach_append_abrupt _ hb (by intro h; cases h)
        | cpuExn number =>
          simp only [AfterStep, Prod.mk.injEq] at hk
          obtain ⟨rfl, rfl⟩ := hk
          exact reach_append_abrupt _ hb (by intro h; cases h)

/-- Completeness: every interpreter result is reachable by small steps. -/
theorem reach_of_execProgram {fuel : Nat} {state final : State} {program : Program} {effect : Effect}
    (h : execProgram fuel state program = .ok (final, effect)) : Reach state program final effect :=
  (reach_of_exec fuel).2 _ _ _ _ h

private theorem exec_split (fuel : Nat) (state : State) (first second : Program) (r : State × Effect)
    (h : execProgram fuel state (first ++ second) = .ok r) :
    (∃ middle, execProgram fuel state first = .ok (middle, .normal) ∧ execProgram fuel middle second = .ok r) ∨
      (execProgram fuel state first = .ok r ∧ (r.2 = .normal → False)) := by
  induction first generalizing fuel state with
  | nil =>
    cases fuel with
    | zero => simp [execProgram] at h
    | succ f => exact Or.inl ⟨state, rfl, h⟩
  | cons stmt rest ih =>
    cases fuel with
    | zero => simp [execProgram] at h
    | succ f =>
      obtain ⟨next, effect, hs, hk⟩ := exec_cons_iff.mp h
      cases effect with
      | normal =>
        rcases ih f next hk with ⟨middle, h1, h2⟩ | ⟨h1, hne⟩
        · refine Or.inl ⟨middle, exec_cons_iff.mpr ⟨next, .normal, hs, h1⟩, ?_⟩
          exact execProgram_ok_mono (Nat.le_succ f) h2
        · exact Or.inr ⟨exec_cons_iff.mpr ⟨next, .normal, hs, h1⟩, hne⟩
      | jump target =>
        subst hk
        exact Or.inr ⟨exec_cons_iff.mpr ⟨next, _, hs, rfl⟩, by simp⟩
      | special message =>
        subst hk
        exact Or.inr ⟨exec_cons_iff.mpr ⟨next, _, hs, rfl⟩, by simp⟩
      | cpuExn number =>
        subst hk
        exact Or.inr ⟨exec_cons_iff.mpr ⟨next, _, hs, rfl⟩, by simp⟩

/-- Stopping after an abrupt program satisfies `AfterStep` for any continuation. -/
private theorem afterStep_stop {next : State} {effect : Effect} (hne : effect = .normal → False)
    (k : Except String (State × Effect)) : AfterStep next effect k (next, effect) := by
  cases effect with
  | normal => exact (hne rfl).elim
  | jump target => rfl
  | special message => rfl
  | cpuExn number => rfl

/-- One normal small step, simulated by the interpreter with more fuel. -/
private theorem exec_of_step {state next : State} {program rest : Program} {r : State × Effect} {fuel : Nat}
    (hs : Step state program next rest .normal) (h : execProgram fuel next rest = .ok r) :
    ∃ fuel', execProgram fuel' state program = .ok r := by
  generalize he : Effect.normal = e at hs
  cases hs with
  | jump => cases he
  | special => cases he
  | cpuExn => cases he
  | move state var exp value rest hv =>
    refine ⟨fuel + 2, exec_cons_iff.mpr ⟨_, .normal, exec_move_iff.mpr ⟨value, hv, rfl⟩, ?_⟩⟩
    exact execProgram_ok_mono (Nat.le_succ_of_le (Nat.le_refl _)) h
  | whileFalse state c body rest hc =>
    refine ⟨fuel + 2, exec_cons_iff.mpr ⟨_, .normal, exec_while_iff.mpr ⟨0, hc, Or.inr ⟨by decide, rfl⟩⟩, ?_⟩⟩
    exact execProgram_ok_mono (Nat.le_succ_of_le (Nat.le_refl _)) h
  | ifTrue state c yes no rest hc =>
    rcases exec_split _ _ _ _ _ h with ⟨middle, h1, h2⟩ | ⟨h1, hne⟩
    · exact ⟨fuel + 2, exec_cons_iff.mpr ⟨middle, .normal,
        exec_if_iff.mpr ⟨1, hc, by simpa using h1⟩,
        execProgram_ok_mono (Nat.le_succ_of_le (Nat.le_refl _)) h2⟩⟩
    · obtain ⟨final, effect⟩ := r
      exact ⟨fuel + 2, exec_cons_iff.mpr ⟨final, effect,
        exec_if_iff.mpr ⟨1, hc, by simpa using h1⟩, afterStep_stop hne _⟩⟩
  | ifFalse state c yes no rest hc =>
    rcases exec_split _ _ _ _ _ h with ⟨middle, h1, h2⟩ | ⟨h1, hne⟩
    · exact ⟨fuel + 2, exec_cons_iff.mpr ⟨middle, .normal,
        exec_if_iff.mpr ⟨0, hc, by simpa using h1⟩,
        execProgram_ok_mono (Nat.le_succ_of_le (Nat.le_refl _)) h2⟩⟩
    · obtain ⟨final, effect⟩ := r
      exact ⟨fuel + 2, exec_cons_iff.mpr ⟨final, effect,
        exec_if_iff.mpr ⟨0, hc, by simpa using h1⟩, afterStep_stop hne _⟩⟩
  | whileTrue state c body rest hc =>
    rcases exec_split _ _ _ _ _ h with ⟨middle, h1, h2⟩ | ⟨h1, hne⟩
    · cases fuel with
      | zero => simp [execProgram] at h2
      | succ g =>
        obtain ⟨n2, e2, hw, hk⟩ := exec_cons_iff.mp h2
        have hwhile : execStmt (g + 2) state (.while c body) = .ok (n2, e2) :=
          exec_while_iff.mpr ⟨1, hc, Or.inl ⟨rfl, middle, .normal, h1,
            execStmt_ok_mono (Nat.le_succ g) hw⟩⟩
        refine ⟨g + 3, exec_cons_iff.mpr ⟨n2, e2, hwhile, ?_⟩⟩
        cases e2 with
        | normal => exact execProgram_ok_mono (Nat.le_add_right g 2) hk
        | jump target => exact hk
        | special message => exact hk
        | cpuExn number => exact hk
    · obtain ⟨final, effect⟩ := r
      have hwhile : execStmt (fuel + 1) state (.while c body) = .ok (final, effect) :=
        exec_while_iff.mpr ⟨1, hc, Or.inl ⟨rfl, final, effect, h1, afterStep_stop hne _⟩⟩
      exact ⟨fuel + 2, exec_cons_iff.mpr ⟨final, effect, hwhile, afterStep_stop hne _⟩⟩

/-- Soundness: every small-step run is matched by the interpreter at some fuel. -/
theorem execProgram_of_reach {state final : State} {program : Program} {effect : Effect}
    (h : Reach state program final effect) : ∃ fuel, execProgram fuel state program = .ok (final, effect) := by
  induction h with
  | done state => exact ⟨1, rfl⟩
  | step hs _ ih =>
    obtain ⟨fuel, he⟩ := ih
    exact exec_of_step hs he
  | stop hs hn =>
    rename_i state final program effect
    generalize hp : ([] : Program) = rest at hs
    cases hs with
    | move => exact (hn rfl).elim
    | ifTrue => exact (hn rfl).elim
    | ifFalse => exact (hn rfl).elim
    | whileTrue => exact (hn rfl).elim
    | whileFalse => exact (hn rfl).elim
    | jump state target address rest ha =>
      exact ⟨2, exec_cons_iff.mpr ⟨_, _, exec_jmp_iff.mpr ⟨_, address, ha, rfl⟩, rfl⟩⟩
    | special state message rest => exact ⟨2, exec_cons_iff.mpr ⟨_, _, rfl, rfl⟩⟩
    | cpuExn state number rest => exact ⟨2, exec_cons_iff.mpr ⟨_, _, rfl, rfl⟩⟩

/-- The small-step relation and the fuel interpreter define the same terminating behaviours. -/
theorem execProgram_iff_reach {state final : State} {program : Program} {effect : Effect} :
    (∃ fuel, execProgram fuel state program = .ok (final, effect)) ↔ Reach state program final effect :=
  ⟨fun ⟨_, h⟩ => reach_of_execProgram h, execProgram_of_reach⟩

/-- `Step` is a function of the current state and program. -/
theorem step_deterministic {state s1 s2 : State} {program p1 p2 : Program} {e1 e2 : Effect}
    (h1 : Step state program s1 p1 e1) (h2 : Step state program s2 p2 e2) :
    s1 = s2 ∧ p1 = p2 ∧ e1 = e2 := by
  cases h1 with
  | move state var exp v rest hv =>
    cases h2 with
    | move _ _ _ v2 _ hv2 =>
      rw [hv] at hv2
      simp only [Except.ok.injEq] at hv2
      subst hv2
      exact ⟨rfl, rfl, rfl⟩
  | jump state target a rest ha =>
    cases h2 with
    | jump _ _ a2 _ ha2 =>
      rw [ha] at ha2
      simp only [Except.ok.injEq, Value.bits.injEq] at ha2
      obtain ⟨rfl, h⟩ := ha2
      cases h
      exact ⟨rfl, rfl, rfl⟩
  | ifTrue state c yes no rest hc =>
    cases h2 with
    | ifTrue => exact ⟨rfl, rfl, rfl⟩
    | ifFalse _ _ _ _ _ hc2 =>
      rw [hc] at hc2
      simp only [Except.ok.injEq, Value.bits.injEq] at hc2
      exact absurd (eq_of_heq hc2.2) (by decide)
  | ifFalse state c yes no rest hc =>
    cases h2 with
    | ifFalse => exact ⟨rfl, rfl, rfl⟩
    | ifTrue _ _ _ _ _ hc2 =>
      rw [hc] at hc2
      simp only [Except.ok.injEq, Value.bits.injEq] at hc2
      exact absurd (eq_of_heq hc2.2) (by decide)
  | whileTrue state c body rest hc =>
    cases h2 with
    | whileTrue => exact ⟨rfl, rfl, rfl⟩
    | whileFalse _ _ _ _ hc2 =>
      rw [hc] at hc2
      simp only [Except.ok.injEq, Value.bits.injEq] at hc2
      exact absurd (eq_of_heq hc2.2) (by decide)
  | whileFalse state c body rest hc =>
    cases h2 with
    | whileFalse => exact ⟨rfl, rfl, rfl⟩
    | whileTrue _ _ _ _ hc2 =>
      rw [hc] at hc2
      simp only [Except.ok.injEq, Value.bits.injEq] at hc2
      exact absurd (eq_of_heq hc2.2) (by decide)
  | special state message rest =>
    cases h2 with
    | special => exact ⟨rfl, rfl, rfl⟩
  | cpuExn state number rest =>
    cases h2 with
    | cpuExn => exact ⟨rfl, rfl, rfl⟩

/-- The interpreter is deterministic across fuel: two successful runs agree. -/
theorem execProgram_ok_unique {f1 f2 : Nat} {state : State} {program : Program} {r1 r2 : State × Effect}
    (h1 : execProgram f1 state program = .ok r1) (h2 : execProgram f2 state program = .ok r2) : r1 = r2 := by
  have := execProgram_ok_mono (Nat.le_max_left f1 f2) h1
  rw [execProgram_ok_mono (Nat.le_max_right f1 f2) h2] at this
  simpa using this.symm

/-! ## Wire format -/

namespace WireLaws
open Bap.Bil.Wire
open_private Bap.Bil.Wire Bap.Bil.Wire.hexDigit Bap.Bil.Wire.parseHexLoop Bap.Bil.Wire.binOpNames

private theorem hexDigit_digitChar : ∀ d, d < 16 → hexDigit (Nat.digitChar d) = some d := by
  decide

private theorem parseHexLoop_append (first second : List Char) (acc : Nat) :
    parseHexLoop (first ++ second) acc = (parseHexLoop first acc).bind (parseHexLoop second) := by
  induction first generalizing acc with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.cons_append, parseHexLoop]
    split
    · exact ih _
    · rfl

private theorem parseHexLoop_toDigits (n : Nat) : parseHexLoop (Nat.toDigits 16 n) 0 = .ok n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 16
    · rw [Nat.toDigits_of_lt_base h]
      simp [parseHexLoop, hexDigit_digitChar n h]
    · rw [Nat.toDigits_of_base_le (by decide) (by omega), parseHexLoop_append,
        ih (n / 16) (by omega)]
      have hd := hexDigit_digitChar (n % 16) (Nat.mod_lt _ (by decide))
      simp only [Except.bind, parseHexLoop, hd]
      congr 1
      omega

/-- The hex printer and parser are inverse on natural numbers. -/
theorem parseHex_toHex (value : BitVec width) : parseHex (Word.toHex value) = .ok value.toNat := by
  have hne : (Nat.toDigits 16 value.toNat) ≠ [] := by
    intro h
    have := Nat.length_toDigits_pos (b := 16) (n := value.toNat)
    simp [h] at this
  have heq : Word.toHex value = String.ofList (Nat.toDigits 16 value.toNat) := rfl
  rw [parseHex, heq, ite_eq_right (by simp [hne])]
  simpa using parseHexLoop_toDigits value.toNat

theorem parseEndian_print (endian : Endian) : parseEndian (printEndian endian) = .ok endian := by
  cases endian <;> rfl

theorem parseCast_print (cast : Cast) : parseCast (printCast cast) = .ok cast := by
  cases cast <;> rfl

theorem parseUnOp_print (op : UnOp) : parseUnOp (printUnOp op) = .ok op := by
  cases op <;> rfl

theorem parseBinOp_print (op : BinOp) : parseBinOp (printBinOp op) = .ok op := by
  cases op <;> rfl

private theorem nat_repr (n : Nat) : Sexp.nat (.atom n.repr) = .ok n := by
  have hdigits : ∀ c ∈ n.repr.toList, c.isDigit = true := by
    intro c hc
    rw [Nat.toList_repr] at hc
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  have hisNat : n.repr.isNat = true := String.isNat_of_isDigit Nat.repr_ne_empty hdigits
  have hfilter : n.repr.toList.filter (· != '_') = n.repr.toList := by
    apply List.filter_eq_self.mpr
    intro c hc
    have := hdigits c hc
    simp only [bne_iff_ne, ne_eq]
    rintro rfl
    simp at this
  have : n.repr.toNat? = some n := by
    rw [String.toNat?_eq_some_ofDigitChars hisNat, hfilter, Nat.toList_repr, Nat.ofDigitChars_ten_toDigits]
  simp only [Sexp.nat, Sexp.asAtom, Bind.bind, Except.bind, this]

theorem parseTyp_print (typ : Typ) : parseTyp (printTyp typ) = .ok typ := by
  cases typ with
  | unknown => rfl
  | unit => rfl
  | imm width => simp [printTyp, parseTyp, Sexp.tagged, nat_repr, Bind.bind, Except.bind]
  | mem address value => simp [printTyp, parseTyp, Sexp.tagged, nat_repr, Bind.bind, Except.bind]

theorem parseVar_print (var : Bap.Var) : parseVar (printVar var) = .ok var := by
  obtain ⟨name, typ, index, isVirtual⟩ := var
  cases isVirtual <;>
    simp [printVar, parseVar, Sexp.tagged, Sexp.expectTagged, Sexp.asList, Sexp.asAtom, nat_repr,
      parseTyp_print, Bind.bind, Except.bind]

/-- The S-expression encoding of expressions is a section of the decoder: every expression,
including arbitrary widths, names and messages, decodes to itself. -/
theorem parseExp_print (exp : Exp) : parseExp (printExp exp) = .ok exp := by
  induction exp with
  | int value =>
    simp [printExp, Sexp.tagged, parseExp, Bind.bind, Except.bind, parseHex_toHex, value.isLt]
  | var var =>
    have h := parseVar_print var
    simp only [printVar, Sexp.tagged] at h
    simp only [printExp, printVar, Sexp.tagged]
    simp only [parseExp, Bind.bind, Except.bind, h]
  | load m a e s ih1 ih2 =>
    simp [printExp, Sexp.tagged, parseExp, Bind.bind, Except.bind, ih1, ih2, parseEndian_print, nat_repr]
  | store m a v e s ih1 ih2 ih3 =>
    simp [printExp, Sexp.tagged, parseExp, Bind.bind, Except.bind, ih1, ih2, ih3, parseEndian_print, nat_repr]
  | bin op l r ih1 ih2 =>
    simp [printExp, Sexp.tagged, parseExp, Bind.bind, Except.bind, ih1, ih2, parseBinOp_print]
  | un op v ih =>
    simp [printExp, Sexp.tagged, parseExp, Bind.bind, Except.bind, ih, parseUnOp_print]
  | cast k w v ih =>
    simp [printExp, Sexp.tagged, parseExp, Bind.bind, Except.bind, ih, parseCast_print, nat_repr]
  | letIn var v b ih1 ih2 =>
    simp [printExp, Sexp.tagged, parseExp, Bind.bind, Except.bind, ih1, ih2, parseVar_print]
  | ite c y n ih1 ih2 ih3 =>
    simp [printExp, Sexp.tagged, parseExp, Bind.bind, Except.bind, ih1, ih2, ih3]
  | extract hi lo v ih =>
    simp [printExp, Sexp.tagged, parseExp, Bind.bind, Except.bind, ih, nat_repr]
  | concat l r ih1 ih2 =>
    simp [printExp, Sexp.tagged, parseExp, Bind.bind, Except.bind, ih1, ih2]
  | unknown m t =>
    simp [printExp, Sexp.tagged, parseExp, Bind.bind, Except.bind, Sexp.asAtom, parseTyp_print]

mutual
  /-- Nesting depth of a statement, a lower bound on the parser fuel it needs. -/
  def stmtDepth : Stmt → Nat
    | .while _ body => 1 + programDepth body
    | .ifElse _ yes no => 1 + max (programDepth yes) (programDepth no)
    | _ => 1

  def programDepth : List Stmt → Nat
    | [] => 0
    | stmt :: rest => max (stmtDepth stmt) (programDepth rest)
end

mutual
  theorem parseStmt_print : (stmt : Stmt) → (fuel : Nat) → stmtDepth stmt ≤ fuel →
      parseStmt fuel (printStmt stmt) = .ok stmt
    | .move var value, fuel, h => by
      have hf : fuel ≠ 0 := by simp [stmtDepth] at h; omega
      simp [parseStmt, printStmt, Sexp.tagged, hf, parseVar_print, parseExp_print, Bind.bind, Except.bind]
    | .jmp target, fuel, h => by
      have hf : fuel ≠ 0 := by simp [stmtDepth] at h; omega
      simp [parseStmt, printStmt, Sexp.tagged, hf, parseExp_print, Bind.bind, Except.bind]
    | .special message, fuel, h => by
      have hf : fuel ≠ 0 := by simp [stmtDepth] at h; omega
      simp [parseStmt, printStmt, Sexp.tagged, hf, Sexp.asAtom, Bind.bind, Except.bind]
    | .cpuExn number, fuel, h => by
      have hf : fuel ≠ 0 := by simp [stmtDepth] at h; omega
      simp [parseStmt, printStmt, Sexp.tagged, hf, nat_repr, Bind.bind, Except.bind]
    | .while condition body, fuel, h => by
      have hb : programDepth body ≤ fuel - 1 := by simp [stmtDepth] at h; omega
      have hf : fuel ≠ 0 := by simp [stmtDepth] at h; omega
      have hl := parseStmtList_print body (fuel - 1) hb
      simp [parseStmt, printStmt, Sexp.tagged, hf, parseExp_print, parseStmts, Sexp.asList, hl, Bind.bind, Except.bind]
    | .ifElse condition yes no, fuel, h => by
      have hb : programDepth yes ≤ fuel - 1 ∧ programDepth no ≤ fuel - 1 := by
        simp [stmtDepth] at h; omega
      have hf : fuel ≠ 0 := by simp [stmtDepth] at h; omega
      have hy := parseStmtList_print yes (fuel - 1) hb.1
      have hn := parseStmtList_print no (fuel - 1) hb.2
      simp [parseStmt, printStmt, Sexp.tagged, hf, parseExp_print, parseStmts, Sexp.asList, hy, hn, Bind.bind, Except.bind]

  theorem parseStmtList_print : (program : List Stmt) → (fuel : Nat) → programDepth program ≤ fuel →
      parseStmtList fuel (program.map printStmt) = .ok program
    | [], _, _ => by simp [parseStmtList]
    | stmt :: rest, fuel, h => by
      simp only [programDepth, Nat.max_le] at h
      simp [parseStmtList, parseStmt_print stmt fuel h.1, parseStmtList_print rest fuel h.2, Bind.bind, Except.bind]
end

/-- Whole-program encoding round-trip at the S-expression level, for programs nested less than the
parser's fuel limit in `parseProgram`. -/
theorem parseStmts_printProgram (program : Program) (h : programDepth program ≤ 1000000) :
    parseStmts 1000000 (printProgram program) = .ok program := by
  simp [parseStmts, printProgram, Sexp.asList, parseStmtList_print program 1000000 h, Bind.bind, Except.bind]

/-- An integer literal that fits its width decodes to exactly that value. -/
theorem parseExp_int_in_range {width value : String} {w n : Nat} (hw : width.toNat? = some w)
    (hv : parseHex value = .ok n) (hn : n < 2 ^ w) :
    ∃ bits : BitVec w, parseExp (.list [.atom "int", .atom width, .atom value]) = .ok (.int bits) ∧ bits.toNat = n := by
  refine ⟨BitVec.ofNat w n, ?_, by simp [Nat.mod_eq_of_lt hn]⟩
  simp [parseExp, hw, hv, hn, Bind.bind, Except.bind]

/-- A literal too large for its width is rejected rather than truncated. -/
theorem parseExp_int_out_of_range {width value : String} {w n : Nat} (hw : width.toNat? = some w)
    (hv : parseHex value = .ok n) (hn : 2 ^ w ≤ n) :
    parseExp (.list [.atom "int", .atom width, .atom value]) = .error "integer literal does not fit its width" := by
  have : ¬ n < 2 ^ w := by omega
  simp [parseExp, hw, hv, this, Bind.bind, Except.bind]

/-- Whole-program round-trip through the text format, for programs nested less than the parser's
fuel limit. -/
theorem parseProgram_renderProgram (program : Program) (h : programDepth program ≤ 1000000) :
    parseProgram (renderProgram program) = .ok program := by
  have hr : Sexp.parse (toString (Sexp.tagged "bil" [printProgram program])) =
      .ok (Sexp.tagged "bil" [printProgram program]) := Bap.Proofs.Core.SexpLaws.parse_render _
  simp only [parseProgram, renderProgram, hr]
  simp [Bind.bind, Except.bind, Sexp.tagged, Sexp.expectTagged, Sexp.asList, parseStmts_printProgram program h]

/-- The wire printer is injective on expressions, a consequence of the round-trip. -/
theorem printExp_injective {left right : Exp} (h : printExp left = printExp right) : left = right := by
  have := parseExp_print left
  rw [h, parseExp_print right] at this
  simpa [eq_comm] using this

end WireLaws

/-! ## The observed evaluator -/

namespace ObserveLaws
open_private Bap.Bil.Observe Bap.Bil.notify
open_private_as Bap.Bil.Observe Bap.Bil.expectMemory observedExpectMemory

private theorem observedExpectMemory_memory {w : Nat} (m : Memory w) :
    observedExpectMemory (.memory m) = .ok ⟨w, m⟩ := rfl
private theorem observedExpectMemory_bits {w : Nat} (b : BitVec w) :
    observedExpectMemory (.bits b) = .error "expected memory" := rfl
private theorem observedExpectMemory_undefined :
    observedExpectMemory .undefined = .error "expected memory" := rfl

private theorem io_pure_bind (x : α) (f : α → IO β) : (pure x >>= f) = f x := rfl

local macro "observed_simp" : tactic =>
  `(tactic| simp [evalExp, Value.asBits, expectMemory, observedExpectMemory_memory, observedExpectMemory_bits,
    observedExpectMemory_undefined, Bind.bind, Except.bind, Except.map, *])

/-- With no observer attached, the IO evaluator is exactly the pure evaluator, down to error
messages. -/
theorem evalExpObserved_none (env : Env) (exp : Exp) :
    evalExpObserved none env exp = pure (evalExp env exp) := by
  induction exp generalizing env with
  | int value => rw [evalExpObserved]; rfl
  | var var => rw [evalExpObserved]; rfl
  | unknown message typ => rw [evalExpObserved]; rfl
  | bin op left right ihl ihr =>
    rw [evalExpObserved]
    simp only [ihl, ihr, io_pure_bind]
    cases hl : evalExp env left with
    | error e => observed_simp
    | ok lv =>
      cases lv with
      | memory m => observed_simp
      | undefined => observed_simp
      | bits a =>
        cases hr : evalExp env right with
        | error e => observed_simp
        | ok rv => cases rv <;> observed_simp
  | concat left right ihl ihr =>
    rw [evalExpObserved]
    simp only [ihl, ihr, io_pure_bind]
    cases hl : evalExp env left with
    | error e => observed_simp
    | ok lv =>
      cases lv with
      | memory m => observed_simp
      | undefined => observed_simp
      | bits a =>
        cases hr : evalExp env right with
        | error e => observed_simp
        | ok rv => cases rv <;> observed_simp
  | un op value ih =>
    rw [evalExpObserved]
    simp only [ih, io_pure_bind]
    cases h : evalExp env value with
    | error e => observed_simp
    | ok v => cases v <;> cases op <;> observed_simp <;> rfl
  | cast kind width value ih =>
    rw [evalExpObserved]
    simp only [ih, io_pure_bind]
    cases h : evalExp env value with
    | error e => observed_simp
    | ok v => cases v <;> cases kind <;> observed_simp
  | extract high low value ih =>
    rw [evalExpObserved]
    simp only [ih, io_pure_bind]
    cases h : evalExp env value with
    | error e => observed_simp
    | ok v => cases v <;> observed_simp
  | letIn var value body ihv ihb =>
    rw [evalExpObserved]
    simp only [ihv, io_pure_bind]
    cases h : evalExp env value with
    | error e => observed_simp
    | ok v =>
      simp only [ihb]
      observed_simp
  | ite condition yes no ihc ihy ihn =>
    rw [evalExpObserved]
    simp only [ihc, io_pure_bind]
    cases hc : evalExp env condition with
    | error e => observed_simp
    | ok v =>
      cases v with
      | memory m => observed_simp
      | undefined => observed_simp
      | @bits w b =>
        simp only [Value.asBits]
        by_cases hw : w = 1
        · subst hw
          simp only [↓reduceDIte]
          rw [apply_ite (evalExpObserved none env), ihy, ihn]
          by_cases hb : b = 1
          · have hb' : b = 1#1 := hb
            simp [evalExp, hc, hb', Value.asBits, Bind.bind, Except.bind]
          · have hb' : ¬ b = 1#1 := hb
            simp [evalExp, hc, hb', Value.asBits, Bind.bind, Except.bind]
        · simp [evalExp, hc, hw, Value.asBits, Bind.bind, Except.bind]
  | load memory address endian size ihm iha =>
    rw [evalExpObserved]
    simp only [ihm, iha, io_pure_bind]
    cases hm : evalExp env memory with
    | error e => observed_simp
    | ok mv =>
      cases mv with
      | bits b => observed_simp
      | undefined => observed_simp
      | @memory mw m =>
        simp only [observedExpectMemory_memory]
        cases ha : evalExp env address with
        | error e => observed_simp
        | ok av =>
          cases av with
          | memory x => observed_simp
          | undefined => observed_simp
          | @bits aw addr =>
            simp only [Value.asBits]
            by_cases hw : aw = mw
            · subst hw
              simp only [↓reduceDIte, notify]
              simp [evalExp, hm, ha, expectMemory, Value.asBits, Bind.bind, Except.bind]
              rfl
            · simp [evalExp, hm, ha, hw, expectMemory, Value.asBits, Bind.bind, Except.bind]
  | store memory address value endian size ihm iha ihv =>
    rw [evalExpObserved]
    simp only [ihm, iha, ihv, io_pure_bind]
    cases hm : evalExp env memory with
    | error e => observed_simp
    | ok mv =>
      cases mv with
      | bits b => observed_simp
      | undefined => observed_simp
      | @memory mw m =>
        simp only [observedExpectMemory_memory]
        cases ha : evalExp env address with
        | error e => observed_simp
        | ok av =>
          cases av with
          | memory x => observed_simp
          | undefined => observed_simp
          | @bits aw addr =>
            simp only [Value.asBits]
            cases hv : evalExp env value with
            | error e => observed_simp
            | ok vv =>
              cases vv with
              | memory x => observed_simp
              | undefined => observed_simp
              | @bits vw stored =>
                simp only [Value.asBits]
                by_cases hw : aw = mw
                · subst hw
                  simp only [↓reduceDIte, notify]
                  have hg : pure () >>= (fun _ => (pure (Except.map Value.memory (Memory.write m addr stored endian size)) : IO _)) =
                      pure (Except.map Value.memory (Memory.write m addr stored endian size)) := rfl
                  cases hwr : Memory.write m addr stored endian size <;>
                    simp [evalExp, hm, ha, hv, hwr, expectMemory, Value.asBits, Bind.bind, Except.bind, Except.map] <;> rfl
                · simp [evalExp, hm, ha, hv, hw, expectMemory, Value.asBits, Bind.bind, Except.bind]

private theorem execObserved_none (fuel : Nat) :
    (∀ state stmt, execStmtObserved none fuel state stmt = pure (execStmt fuel state stmt)) ∧
    (∀ state program, execProgramObserved none fuel state program = pure (execProgram fuel state program)) := by
  induction fuel with
  | zero =>
    constructor
    · intro state stmt
      rw [execStmtObserved]
      simp [execStmt]
    · intro state program
      rw [execProgramObserved]
      simp [execProgram]
  | succ f ih =>
    obtain ⟨ihs, ihp⟩ := ih
    constructor
    · intro state stmt
      rw [execStmtObserved.eq_def]
      dsimp only
      cases stmt with
      | special message => simp [execStmt]
      | cpuExn number => simp [execStmt]
      | move var value =>
        simp only [evalExpObserved_none, io_pure_bind]
        cases h : evalExp state.env value <;> simp [execStmt, execExp, h, Bind.bind, Except.bind]
      | jmp target =>
        simp only [evalExpObserved_none, io_pure_bind]
        cases h : evalExp state.env target with
        | error e => simp [execStmt, execExp, h, Bind.bind, Except.bind]
        | ok v => cases v <;> simp [execStmt, execExp, h, Bind.bind, Except.bind, Value.asBits, Except.map]
      | ifElse condition yes no =>
        simp only [evalExpObserved_none, io_pure_bind]
        cases h : evalExp state.env condition with
        | error e => simp [execStmt, execExp, h, Bind.bind, Except.bind]
        | ok v =>
          cases v with
          | memory m => simp [execStmt, execExp, h, Bind.bind, Except.bind, Value.asBits]
          | undefined => simp [execStmt, execExp, h, Bind.bind, Except.bind, Value.asBits]
          | @bits w b =>
            simp only [Value.asBits]
            by_cases hw : w = 1
            · subst hw
              simp only [↓reduceDIte, ihp]
              simp [execStmt, execExp, h, Bind.bind, Except.bind, Value.asBits]
            · simp [execStmt, execExp, h, hw, Bind.bind, Except.bind, Value.asBits]
      | «while» condition body =>
        simp only [evalExpObserved_none, io_pure_bind]
        cases h : evalExp state.env condition with
        | error e => simp [execStmt, execExp, h, Bind.bind, Except.bind]
        | ok v =>
          cases v with
          | memory m => simp [execStmt, execExp, h, Bind.bind, Except.bind, Value.asBits]
          | undefined => simp [execStmt, execExp, h, Bind.bind, Except.bind, Value.asBits]
          | @bits w b =>
            simp only [Value.asBits]
            by_cases hw : w = 1
            · subst hw
              simp only [↓reduceDIte]
              by_cases hb : b = 1
              · have hb' : b = 1#1 := hb
                simp only [hb, ↓reduceIte, ihp, io_pure_bind]
                cases hp : execProgram f state body with
                | error e => simp [execStmt, execExp, h, hb', hp, Bind.bind, Except.bind, Value.asBits]
                | ok r =>
                  obtain ⟨next, effect⟩ := r
                  cases effect with
                  | normal =>
                    simp only [ihs]
                    simp [execStmt, execExp, h, hb', hp, Bind.bind, Except.bind, Value.asBits]
                  | jump target => simp [execStmt, execExp, h, hb', hp, Bind.bind, Except.bind, Value.asBits]
                  | special message => simp [execStmt, execExp, h, hb', hp, Bind.bind, Except.bind, Value.asBits]
                  | cpuExn number => simp [execStmt, execExp, h, hb', hp, Bind.bind, Except.bind, Value.asBits]
              · have hb' : ¬ b = 1#1 := hb
                simp only [hb, ↓reduceIte]
                simp [execStmt, execExp, h, hb', Bind.bind, Except.bind, Value.asBits]
            · simp [execStmt, execExp, h, hw, Bind.bind, Except.bind, Value.asBits]
    · intro state program
      rw [execProgramObserved.eq_def]
      dsimp only
      cases program with
      | nil => simp [execProgram]
      | cons stmt rest =>
        simp only [ihs, io_pure_bind]
        cases hs : execStmt f state stmt with
        | error e => simp [execProgram, hs, Bind.bind, Except.bind]
        | ok r =>
          obtain ⟨next, effect⟩ := r
          cases effect with
          | normal =>
            simp only [ihp]
            simp [execProgram, hs, Bind.bind, Except.bind]
          | jump target => simp [execProgram, hs, Bind.bind, Except.bind]
          | special message => simp [execProgram, hs, Bind.bind, Except.bind]
          | cpuExn number => simp [execProgram, hs, Bind.bind, Except.bind]

/-- With no observer the IO interpreter is exactly `execProgram`. -/
theorem execProgramObserved_none (fuel : Nat) (state : State) (program : Program) :
    execProgramObserved none fuel state program = pure (execProgram fuel state program) :=
  (execObserved_none fuel).2 state program

theorem runObserved_none (program : Program) (state : State) (fuel : Nat) :
    runObserved none program state fuel = pure (run program state fuel) :=
  execProgramObserved_none fuel state program

end ObserveLaws

/-! ## `Word` and `evalBin` against mathematics and SMT-LIB -/

namespace WordMath

/-! ## The specification: `Nat` and `Int` only -/

/-- The two's complement reading of `a`: `a ≥ 2^(w-1)` means `a - 2^w`. Width `0` has only the value `0`. -/
def signedOf (w a : Nat) : Int :=
  if w = 0 then 0 else if a < 2 ^ (w - 1) then (a : Int) else (a : Int) - 2 ^ w

/-- The residue of `i` modulo `2^w`. -/
def wrap (w : Nat) (i : Int) : Nat := (i % (2 ^ w : Int)).toNat

/-- `1` when `p` holds and `0` otherwise, the value of a comparison. -/
def flag (p : Prop) [Decidable p] : Nat := if p then 1 else 0

/-- The width of a result: a comparison has one bit, anything else the width of its operands. -/
def resultWidth : BinOp → Nat → Nat
  | .eq, _ | .neq, _ | .lt, _ | .le, _ | .gt, _ | .ge, _ | .slt, _ | .sle, _ | .sgt, _ | .sge, _ => 1
  | _, w => w

/-- What each operator means on the numbers `a` and `b` of `w` bits. -/
def mathBin : BinOp → (w a b : Nat) → Nat
  | .add, w, a, b => wrap w ((a : Int) + b)
  | .sub, w, a, b => wrap w ((a : Int) - b)
  | .mul, w, a, b => wrap w ((a : Int) * b)
  | .div, w, a, b => if b = 0 then 2 ^ w - 1 else a / b
  | .rem, _, a, b => if b = 0 then a else a % b
  | .sdiv, w, a, b =>
    if b = 0 then (if signedOf w a < 0 then 1 else 2 ^ w - 1) else wrap w ((signedOf w a).tdiv (signedOf w b))
  | .srem, w, a, b => if b = 0 then a else wrap w ((signedOf w a).tmod (signedOf w b))
  | .smod, w, a, b => if b = 0 then a else wrap w ((signedOf w a).fmod (signedOf w b))
  | .lshift, w, a, b => (a * 2 ^ b) % 2 ^ w
  | .rshift, _, a, b => a / 2 ^ b
  | .ashift, w, a, b => wrap w (signedOf w a / (2 ^ b : Int))
  | .and, _, a, b => a.land b
  | .or, _, a, b => a.lor b
  | .xor, _, a, b => a.xor b
  | .eq, _, a, b => flag (a = b)
  | .neq, _, a, b => flag (a ≠ b)
  | .lt, _, a, b => flag (a < b)
  | .le, _, a, b => flag (a ≤ b)
  | .gt, _, a, b => flag (a > b)
  | .ge, _, a, b => flag (a ≥ b)
  | .slt, w, a, b => flag (signedOf w a < signedOf w b)
  | .sle, w, a, b => flag (signedOf w a ≤ signedOf w b)
  | .sgt, w, a, b => flag (signedOf w a > signedOf w b)
  | .sge, w, a, b => flag (signedOf w a ≥ signedOf w b)

/-! ## `Word` against the specification -/

theorem wrap_eq_ofInt (w : Nat) (i : Int) : wrap w i = (BitVec.ofInt w i).toNat := by
  simp [wrap, BitVec.toNat_ofInt]

theorem wrap_toInt {w : Nat} (x : BitVec w) : wrap w x.toInt = x.toNat := by
  rw [wrap_eq_ofInt, BitVec.ofInt_toInt]

theorem two_pow_cast (w : Nat) : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by simp

theorem wrap_bmod (w : Nat) (i : Int) : wrap w (i.bmod (2 ^ w)) = wrap w i := by
  have h := Int.bmod_emod (x := i) (m := 2 ^ w)
  simp only [wrap, ← two_pow_cast, h]

theorem wrap_natCast (w n : Nat) : wrap w n = n % 2 ^ w := by
  simp only [wrap, ← two_pow_cast]; rw [← Int.natCast_emod, Int.toNat_natCast]

/-- The two's complement reading is `BitVec.toInt`. -/
theorem signedOf_toNat {w : Nat} (x : BitVec w) : signedOf w x.toNat = x.toInt := by
  rcases w with _ | w
  · simp [signedOf, BitVec.toInt_eq_toNat_cond, BitVec.eq_nil x]
  · have h : 2 * x.toNat < 2 ^ (w + 1) ↔ x.toNat < 2 ^ w := by rw [Nat.pow_succ]; omega
    simp [signedOf, BitVec.toInt_eq_toNat_cond, h]

theorem word_add {w : Nat} (x y : BitVec w) : (x + y).toNat = wrap w ((x.toNat : Int) + y.toNat) := by
  rw [← Int.natCast_add, wrap_natCast, BitVec.toNat_add]

theorem word_mul {w : Nat} (x y : BitVec w) : (x * y).toNat = wrap w ((x.toNat : Int) * y.toNat) := by
  rw [← Int.natCast_mul, wrap_natCast, BitVec.toNat_mul]

theorem word_sub {w : Nat} (x y : BitVec w) : (x - y).toNat = wrap w ((x.toNat : Int) - y.toNat) := by
  have hy := y.isLt
  have e : (x.toNat : Int) - y.toNat = ((2 ^ w - y.toNat + x.toNat : Nat) : Int) - ((2 ^ w : Nat) : Int) := by omega
  rw [e, BitVec.toNat_sub, ← wrap_natCast]
  simp only [wrap, ← two_pow_cast, Int.sub_emod_right]

theorem word_udiv {w : Nat} (x y : BitVec w) :
    BitVec.toNat (Word.udiv x y) = if y.toNat = 0 then 2 ^ w - 1 else x.toNat / y.toNat := by
  by_cases h : y = 0
  · subst h; simp [Word.udiv, Word.ones]
  · have : y.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using h
    rw [Word.udiv, ite_eq_right h, ite_eq_right this, BitVec.toNat_udiv]

theorem word_urem {w : Nat} (x y : BitVec w) :
    BitVec.toNat (Word.urem x y) = if y.toNat = 0 then x.toNat else x.toNat % y.toNat := by
  by_cases h : y = 0
  · subst h; simp [Word.urem]
  · have : y.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using h
    rw [Word.urem, ite_eq_right h, ite_eq_right this, BitVec.toNat_umod]

theorem word_sdiv_of_ne {w : Nat} (x : BitVec w) {y : BitVec w} (h : y ≠ 0) : Word.sdiv x y = BitVec.sdiv x y := by
  have hn : y.neg ≠ 0 := fun e => h (by simpa using (BitVec.neg_eq_zero_iff (x := y)).mp e)
  simp only [Word.sdiv, BitVec.smtSDiv, BitVec.smtUDiv, BitVec.sdiv]
  split <;> simp_all

/-- Division by zero is the `udiv` of the magnitude, with the sign of the dividend: `-1`, or `1` for a negative one. -/
theorem word_sdiv_zero {w : Nat} (x : BitVec w) :
    Word.sdiv x 0 = if x.toInt < 0 then 1#w else BitVec.allOnes w := by
  rcases w with _ | w
  · exact Subsingleton.elim ..
  have hneg : x.toInt < 0 ↔ x.msb = true := by simp [BitVec.toInt_neg_iff, BitVec.msb_eq_true_iff_two_mul_ge]
  simp only [Word.sdiv, BitVec.smtSDiv, BitVec.smtUDiv]
  cases hm : x.msb
  · simp [hneg, hm]
  · have h1 : -BitVec.allOnes (w + 1) = 1#(w + 1) := by
      apply BitVec.eq_of_toNat_eq
      have hp := Nat.two_pow_pos (w + 1)
      simp only [BitVec.toNat_neg, BitVec.toNat_allOnes, BitVec.toNat_ofNat]
      rw [show 2 ^ (w + 1) - (2 ^ (w + 1) - 1) = 1 by omega]
    simp [hneg, hm, h1]

theorem word_sdiv {w : Nat} (x y : BitVec w) :
    BitVec.toNat (Word.sdiv x y) =
      if y.toNat = 0 then (if x.toInt < 0 then 1 else 2 ^ w - 1) else wrap w (x.toInt.tdiv y.toInt) := by
  by_cases h : y = 0
  · subst h
    rw [word_sdiv_zero]
    rcases w with _ | w
    · rw [Subsingleton.elim x 0#0]; simp
    · split <;> simp [*]
  · have : y.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using h
    rw [word_sdiv_of_ne x h, ite_eq_right this, ← wrap_toInt, BitVec.toInt_sdiv, wrap_bmod]

theorem word_srem {w : Nat} (x y : BitVec w) :
    BitVec.toNat (Word.srem x y) = if y.toNat = 0 then x.toNat else wrap w (x.toInt.tmod y.toInt) := by
  by_cases h : y = 0
  · subst h; simp [Word.srem]
  · have : y.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using h
    rw [Word.srem, ite_eq_right h, ite_eq_right this, ← wrap_toInt, BitVec.toInt_srem]

theorem word_smod {w : Nat} (x y : BitVec w) :
    BitVec.toNat (Word.smod x y) = if y.toNat = 0 then x.toNat else wrap w (x.toInt.fmod y.toInt) := by
  by_cases h : y = 0
  · subst h; simp [Word.smod]
  · have : y.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using h
    rw [Word.smod, ite_eq_right this, ← wrap_toInt, BitVec.toInt_smod]

theorem word_shl {w : Nat} (x y : BitVec w) : BitVec.toNat (Word.shl x y) = (x.toNat * 2 ^ y.toNat) % 2 ^ w := by
  simp [Word.shl, Word.toNat, Nat.shiftLeft_eq]

theorem word_lshr {w : Nat} (x y : BitVec w) : BitVec.toNat (Word.lshr x y) = x.toNat / 2 ^ y.toNat := by
  simp [Word.lshr, Word.toNat, Nat.shiftRight_eq_div_pow]

theorem word_ashr {w : Nat} (x y : BitVec w) :
    BitVec.toNat (Word.ashr x y) = wrap w (x.toInt / (2 ^ y.toNat : Int)) := by
  rw [← wrap_toInt, Word.ashr, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, Word.toNat]; simp

theorem word_bool (b : Bool) : BitVec.toNat (Word.bool b) = if b then 1 else 0 := by cases b <;> rfl

theorem word_eq {w : Nat} (x y : BitVec w) : BitVec.toNat (Word.eq x y) = flag (x.toNat = y.toNat) := by
  simp [Word.eq, word_bool, flag, BitVec.toNat_eq]

theorem word_neq {w : Nat} (x y : BitVec w) : BitVec.toNat (Word.neq x y) = flag (x.toNat ≠ y.toNat) := by
  simp [Word.neq, word_bool, flag, BitVec.toNat_eq]

theorem word_lt {w : Nat} (x y : BitVec w) : BitVec.toNat (Word.lt x y) = flag (x.toNat < y.toNat) := by
  simp [Word.lt, word_bool, flag, BitVec.lt_def]

theorem word_le {w : Nat} (x y : BitVec w) : BitVec.toNat (Word.le x y) = flag (x.toNat ≤ y.toNat) := by
  simp [Word.le, word_bool, flag, BitVec.le_def]

theorem word_slt {w : Nat} (x y : BitVec w) : BitVec.toNat (Word.slt x y) = flag (x.toInt < y.toInt) := by
  simp [Word.slt, word_bool, flag, BitVec.slt_iff_toInt_lt]

theorem word_sle {w : Nat} (x y : BitVec w) : BitVec.toNat (Word.sle x y) = flag (x.toInt ≤ y.toInt) := by
  simp [Word.sle, word_bool, flag, BitVec.sle_iff_toInt_le]

/-- The value of every operator on equal widths, at every width including `0`. -/
theorem evalBin_math (op : BinOp) {w : Nat} (x y : BitVec w) :
    ∃ z : BitVec (resultWidth op w),
      evalBin op ⟨w, x⟩ ⟨w, y⟩ = .ok (.bits z) ∧ z.toNat = mathBin op w x.toNat y.toNat := by
  cases op
  case add => exact ⟨x + y, by simp [evalBin, resultWidth], word_add x y⟩
  case sub => exact ⟨x - y, by simp [evalBin, resultWidth], word_sub x y⟩
  case mul => exact ⟨x * y, by simp [evalBin, resultWidth], word_mul x y⟩
  case div => exact ⟨Word.udiv x y, by simp [evalBin, resultWidth], word_udiv x y⟩
  case rem => exact ⟨Word.urem x y, by simp [evalBin, resultWidth], word_urem x y⟩
  case sdiv =>
    exact ⟨Word.sdiv x y, by simp [evalBin, resultWidth], (word_sdiv x y).trans (by simp [mathBin, signedOf_toNat])⟩
  case srem =>
    exact ⟨Word.srem x y, by simp [evalBin, resultWidth], (word_srem x y).trans (by simp [mathBin, signedOf_toNat])⟩
  case smod =>
    exact ⟨Word.smod x y, by simp [evalBin, resultWidth], (word_smod x y).trans (by simp [mathBin, signedOf_toNat])⟩
  case lshift => exact ⟨Word.shl x y, by simp [evalBin, resultWidth], word_shl x y⟩
  case rshift => exact ⟨Word.lshr x y, by simp [evalBin, resultWidth], word_lshr x y⟩
  case ashift =>
    exact ⟨Word.ashr x y, by simp [evalBin, resultWidth], (word_ashr x y).trans (by simp [mathBin, signedOf_toNat])⟩
  case and => exact ⟨x &&& y, by simp [evalBin, resultWidth], BitVec.toNat_and x y⟩
  case or => exact ⟨x ||| y, by simp [evalBin, resultWidth], BitVec.toNat_or x y⟩
  case xor => exact ⟨x ^^^ y, by simp [evalBin, resultWidth], BitVec.toNat_xor x y⟩
  case eq => exact ⟨Word.eq x y, by simp [evalBin, resultWidth], word_eq x y⟩
  case neq => exact ⟨Word.neq x y, by simp [evalBin, resultWidth], word_neq x y⟩
  case lt => exact ⟨Word.lt x y, by simp [evalBin, resultWidth], word_lt x y⟩
  case le => exact ⟨Word.le x y, by simp [evalBin, resultWidth], word_le x y⟩
  case gt => exact ⟨Word.lt y x, by simp [evalBin, resultWidth], word_lt y x⟩
  case ge => exact ⟨Word.le y x, by simp [evalBin, resultWidth], word_le y x⟩
  case slt =>
    exact ⟨Word.slt x y, by simp [evalBin, resultWidth], (word_slt x y).trans (by simp [mathBin, signedOf_toNat])⟩
  case sle =>
    exact ⟨Word.sle x y, by simp [evalBin, resultWidth], (word_sle x y).trans (by simp [mathBin, signedOf_toNat])⟩
  case sgt =>
    exact ⟨Word.slt y x, by simp [evalBin, resultWidth], (word_slt y x).trans (by simp [mathBin, signedOf_toNat])⟩
  case sge =>
    exact ⟨Word.sle y x, by simp [evalBin, resultWidth], (word_sle y x).trans (by simp [mathBin, signedOf_toNat])⟩

/-- Operands of different widths are an error, whatever the operator. -/
theorem evalBin_widths (op : BinOp) {v w : Nat} (x : BitVec v) (y : BitVec w) (h : v ≠ w) :
    evalBin op ⟨v, x⟩ ⟨w, y⟩ = .error "binary operands have different widths" := by
  simp [evalBin, h]

/-! ## SMT-LIB, by the text of `FixedSizeBitVectors` and `QF_BV` -/

namespace Smt

/-- `nat2bv[m]`, a vector read back as its number. -/
def nat2bv (w n : Nat) : Nat := n % 2 ^ w
/-- `((_ extract |m-1| |m-1|) s) = #b1`. -/
def msb (w s : Nat) : Bool := s.testBit (w - 1)
def bvnot (w s : Nat) : Nat := 2 ^ w - 1 - s
def bvneg (w s : Nat) : Nat := nat2bv w (2 ^ w - s)
def bvadd (w s t : Nat) : Nat := nat2bv w (s + t)
def bvmul (w s t : Nat) : Nat := nat2bv w (s * t)
def bvsub (w s t : Nat) : Nat := bvadd w s (bvneg w t)
def bvudiv (w s t : Nat) : Nat := if t ≠ 0 then nat2bv w (s / t) else 2 ^ w - 1
def bvurem (w s t : Nat) : Nat := if t ≠ 0 then nat2bv w (s % t) else s

def bvsdiv (w s t : Nat) : Nat :=
  match msb w s, msb w t with
  | false, false => bvudiv w s t
  | true, false => bvneg w (bvudiv w (bvneg w s) t)
  | false, true => bvneg w (bvudiv w s (bvneg w t))
  | true, true => bvudiv w (bvneg w s) (bvneg w t)

def bvsrem (w s t : Nat) : Nat :=
  match msb w s, msb w t with
  | false, false => bvurem w s t
  | true, false => bvneg w (bvurem w (bvneg w s) t)
  | false, true => bvurem w s (bvneg w t)
  | true, true => bvneg w (bvurem w (bvneg w s) (bvneg w t))

def bvsmod (w s t : Nat) : Nat :=
  let absS := if msb w s then bvneg w s else s
  let absT := if msb w t then bvneg w t else t
  let u := bvurem w absS absT
  if u = 0 then u
  else
    match msb w s, msb w t with
    | false, false => u
    | true, false => bvadd w (bvneg w u) t
    | false, true => bvadd w u t
    | true, true => bvneg w u

def bvshl (w s t : Nat) : Nat := nat2bv w (s * 2 ^ t)
def bvlshr (w s t : Nat) : Nat := nat2bv w (s / 2 ^ t)
def bvashr (w s t : Nat) : Nat := if msb w s then bvnot w (bvlshr w (bvnot w s) t) else bvlshr w s t

def bvult (s t : Nat) : Bool := decide (s < t)
def bvule (s t : Nat) : Bool := bvult s t || decide (s = t)
def bvslt (w s t : Nat) : Bool := (msb w s && !msb w t) || (msb w s == msb w t && bvult s t)
def bvsle (w s t : Nat) : Bool := (msb w s && !msb w t) || (msb w s == msb w t && bvule s t)
/-- A predicate as a one-bit vector. -/
def bit (p : Bool) : Nat := if p then 1 else 0

end Smt
open Smt

/-- Every BIL operator as its SMT-LIB term, as the symbolic executor emits it. -/
def smtBin : BinOp → (w a b : Nat) → Nat
  | .add, w, a, b => bvadd w a b
  | .sub, w, a, b => bvsub w a b
  | .mul, w, a, b => bvmul w a b
  | .div, w, a, b => bvudiv w a b
  | .rem, w, a, b => bvurem w a b
  | .sdiv, w, a, b => bvsdiv w a b
  | .srem, w, a, b => bvsrem w a b
  | .smod, w, a, b => bvsmod w a b
  | .lshift, w, a, b => bvshl w a b
  | .rshift, w, a, b => bvlshr w a b
  | .ashift, w, a, b => bvashr w a b
  | .and, _, a, b => a.land b
  | .or, _, a, b => a.lor b
  | .xor, _, a, b => a.xor b
  | .eq, _, a, b => bit (decide (a = b))
  | .neq, _, a, b => bit (!decide (a = b))
  | .lt, _, a, b => bit (bvult a b)
  | .le, _, a, b => bit (bvule a b)
  | .gt, _, a, b => bit (bvult b a)
  | .ge, _, a, b => bit (bvule b a)
  | .slt, w, a, b => bit (bvslt w a b)
  | .sle, w, a, b => bit (bvsle w a b)
  | .sgt, w, a, b => bit (bvslt w b a)
  | .sge, w, a, b => bit (bvsle w b a)

section Transport
variable {w : Nat} (x y : BitVec w)

theorem msb_toNat : msb w x.toNat = x.msb := by
  rw [BitVec.msb_eq_getLsbD_last]; rfl

theorem bvneg_toNat : bvneg w x.toNat = (-x).toNat := (BitVec.toNat_neg x).symm

theorem bvadd_toNat : bvadd w x.toNat y.toNat = (x + y).toNat := (BitVec.toNat_add x y).symm

theorem bvudiv_toNat : bvudiv w x.toNat y.toNat = (BitVec.smtUDiv x y).toNat := by
  by_cases h : y = 0
  · subst h; simp [bvudiv, BitVec.smtUDiv]
  · have hn : y.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using h
    have hlt : x.toNat / y.toNat < 2 ^ w := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt
    rw [BitVec.smtUDiv, ite_eq_right h, BitVec.udiv_eq, BitVec.toNat_udiv]
    simp [bvudiv, hn, nat2bv, Nat.mod_eq_of_lt hlt]

theorem bvurem_toNat : bvurem w x.toNat y.toNat = (x % y).toNat := by
  by_cases h : y = 0
  · subst h; simp [bvurem]
  · have hn : y.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using h
    have hlt : x.toNat % y.toNat < 2 ^ w := Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt
    simp [bvurem, hn, nat2bv, Nat.mod_eq_of_lt hlt]

theorem bvsdiv_toNat : bvsdiv w x.toNat y.toNat = (BitVec.smtSDiv x y).toNat := by
  simp only [bvsdiv, msb_toNat, BitVec.smtSDiv]
  cases x.msb <;> cases y.msb <;> simp only [bvneg_toNat, bvudiv_toNat] <;> rfl

theorem bvsrem_toNat : bvsrem w x.toNat y.toNat = (BitVec.srem x y).toNat := by
  simp only [bvsrem, msb_toNat, BitVec.srem_eq]
  cases x.msb <;> cases y.msb <;> simp only [bvneg_toNat, bvurem_toNat]

theorem bvsmod_toNat : bvsmod w x.toNat y.toNat = (BitVec.smod x y).toNat := by
  have z : ∀ u : BitVec w, u.toNat = 0 ↔ u = 0#w := fun u => by simp [BitVec.toNat_eq]
  simp only [bvsmod, msb_toNat, BitVec.smod_eq]
  cases x.msb <;> cases y.msb <;> simp only [ite_true, ite_false, Bool.false_eq_true, bvneg_toNat, bvurem_toNat, z,
    bvadd_toNat, BitVec.umod_eq]
  · split <;> rfl
  · by_cases hu : x % -y = 0#w <;> simp only [hu, ↓reduceIte]
  · by_cases hu : -x % y = 0#w <;> simp only [hu, ↓reduceIte, BitVec.sub_eq_add_neg, BitVec.add_comm]
  · by_cases hu : -x % -y = 0#w <;> simp only [hu, ↓reduceIte, BitVec.neg_zero]

theorem bvashr_toNat (n : Nat) : bvashr w x.toNat n = (x.sshiftRight n).toNat := by
  have hl : ∀ m, m < 2 ^ w → bvlshr w m n = m >>> n := fun m hm => by
    rw [bvlshr, nat2bv, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm)]
  have hn : 2 ^ w - 1 - x.toNat < 2 ^ w := by have := x.isLt; omega
  rw [BitVec.toNat_sshiftRight, bvashr, msb_toNat]
  cases x.msb <;> simp [hl, hn, x.isLt, bvnot]

theorem bvslt_toNat : bvslt w x.toNat y.toNat = decide (x.toInt < y.toInt) := by
  have hx : (x.toNat : Int) < ((2 ^ w : Nat) : Int) := by exact_mod_cast x.isLt
  have hy : (y.toNat : Int) < ((2 ^ w : Nat) : Int) := by exact_mod_cast y.isLt
  rw [BitVec.toInt_eq_msb_cond x, BitVec.toInt_eq_msb_cond y, bvslt, msb_toNat, msb_toNat]
  generalize ((2 ^ w : Nat) : Int) = m at *
  cases x.msb <;> cases y.msb <;> simp [bvult] <;> omega

theorem bvsle_toNat : bvsle w x.toNat y.toNat = decide (x.toInt ≤ y.toInt) := by
  have hx : (x.toNat : Int) < ((2 ^ w : Nat) : Int) := by exact_mod_cast x.isLt
  have hy : (y.toNat : Int) < ((2 ^ w : Nat) : Int) := by exact_mod_cast y.isLt
  rw [BitVec.toInt_eq_msb_cond x, BitVec.toInt_eq_msb_cond y, bvsle, msb_toNat, msb_toNat]
  generalize ((2 ^ w : Nat) : Int) = m at *
  generalize x.toNat = a at *
  generalize y.toNat = b at *
  have le : (decide (a < b) || decide (a = b)) = decide (a ≤ b) := 
    Bool.eq_iff_iff.mpr (by simp; omega)
  cases x.msb <;> cases y.msb <;> simp [bvule, bvult, le] <;> omega

end Transport

theorem msb_pos {w a : Nat} (h : msb w a = true) (ha : a < 2 ^ w := by assumption) : 0 < w := by
  rcases w with _ | w
  · have : a = 0 := by simpa using ha
    subst this; simp [msb] at h
  · omega

theorem math_sdiv {w : Nat} (x y : BitVec w) : mathBin .sdiv w x.toNat y.toNat = BitVec.toNat (Word.sdiv x y) := by
  simp [mathBin, word_sdiv, signedOf_toNat]

theorem math_srem {w : Nat} (x y : BitVec w) : mathBin .srem w x.toNat y.toNat = BitVec.toNat (Word.srem x y) := by
  simp [mathBin, word_srem, signedOf_toNat]

theorem math_smod {w : Nat} (x y : BitVec w) : mathBin .smod w x.toNat y.toNat = BitVec.toNat (Word.smod x y) := by
  simp [mathBin, word_smod, signedOf_toNat]

theorem math_ashift {w : Nat} (x : BitVec w) (n : Nat) : mathBin .ashift w x.toNat n = (x.sshiftRight n).toNat := by
  rw [mathBin, signedOf_toNat, ← wrap_toInt, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; simp

theorem exists_toNat {w a : Nat} (h : a < 2 ^ w) : ∃ x : BitVec w, x.toNat = a := ⟨BitVec.ofNatLT a h, by simp⟩

theorem flag_eq_bit {p : Prop} [Decidable p] {q : Bool} (h : p ↔ q = true) : flag p = bit q := by
  cases q <;> simp_all [flag, bit]

theorem flag_bit (p : Prop) [Decidable p] : flag p = bit (decide p) := by simp [flag, bit]

/-- SMT-LIB agrees with the specification on every operator, for `w`-bit operands. -/
theorem math_eq_smt (op : BinOp) {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    mathBin op w a b = smtBin op w a b := by
  obtain ⟨x, rfl⟩ := exists_toNat ha
  obtain ⟨y, rfl⟩ := exists_toNat hb
  cases op
  case sdiv => rw [math_sdiv, smtBin, bvsdiv_toNat]; rfl
  case add => exact (word_add x y).symm.trans (BitVec.toNat_add x y)
  case mul => exact (word_mul x y).symm.trans (BitVec.toNat_mul x y)
  case sub =>
    refine (word_sub x y).symm.trans ?_
    simp only [smtBin, bvsub, bvneg_toNat, bvadd_toNat, BitVec.sub_eq_add_neg]
  case div =>
    refine (word_udiv x y).symm.trans ?_
    rw [smtBin, bvudiv_toNat, Word.udiv, BitVec.smtUDiv, Word.ones]; rfl
  case rem =>
    refine (word_urem x y).symm.trans ?_
    rw [smtBin, bvurem_toNat, Word.urem]
    split <;> simp_all
  case srem =>
    rw [math_srem, smtBin, bvsrem_toNat, Word.srem]
    split <;> simp_all
  case smod => exact (math_smod x y).trans (bvsmod_toNat x y).symm
  case lshift => exact rfl
  case rshift =>
    rw [mathBin, smtBin, bvlshr, nat2bv, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)]
  case ashift =>
    exact (math_ashift x y.toNat).trans (bvashr_toNat x y.toNat).symm
  case and => rfl
  case or => rfl
  case xor => rfl
  case eq => exact flag_bit _
  case neq => exact flag_eq_bit (by simp)
  case lt => exact flag_eq_bit (by simp [bvult])
  case le => exact flag_eq_bit (by simp [bvule, bvult]; omega)
  case gt => exact flag_eq_bit (by simp [bvult])
  case ge => exact flag_eq_bit (by simp [bvule, bvult]; omega)
  case slt => rw [mathBin, signedOf_toNat, signedOf_toNat]; exact flag_eq_bit (by simp [bvslt_toNat])
  case sle => rw [mathBin, signedOf_toNat, signedOf_toNat]; exact flag_eq_bit (by simp [bvsle_toNat])
  case sgt => rw [mathBin, signedOf_toNat, signedOf_toNat]; exact flag_eq_bit (by simp [bvslt_toNat])
  case sge => rw [mathBin, signedOf_toNat, signedOf_toNat]; exact flag_eq_bit (by simp [bvsle_toNat])

/-- SMT-LIB's division by zero depends on the sign of the dividend: `1` for a negative one. -/
theorem smt_sdiv_zero {w a : Nat} (ha : a < 2 ^ w) :
    smtBin .sdiv w a 0 = if msb w a then 1 else 2 ^ w - 1 := by
  obtain ⟨x, rfl⟩ := exists_toNat ha
  have hz : msb w 0 = false := by simp [msb]
  simp only [smtBin, bvsdiv, hz]
  cases h : msb w x.toNat
  · simp [bvudiv]
  · have hw : 0 < w := msb_pos h
    have : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
    rw [Nat.pow_one] at this
    have h1 : 2 ^ w - (2 ^ w - 1) = 1 := by omega
    simp [bvudiv, bvneg, nat2bv, h1, Nat.mod_eq_of_lt (show 1 < 2 ^ w by omega)]

/-- BIL's division by zero is SMT-LIB's: it depends on the sign of the dividend, `1` for a negative one. -/
theorem math_sdiv_zero (w a : Nat) : mathBin .sdiv w a 0 = if signedOf w a < 0 then 1 else 2 ^ w - 1 := rfl

/-! ## The edges -/

section Edges
variable {w : Nat} (x y : BitVec w)

/-- Shifting left past the width gives `0`. -/
theorem shl_past_width (h : w ≤ y.toNat) : Word.shl x y = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [word_shl]
  exact (Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow 2 h) (Nat.dvd_mul_left _ _))).trans (by simp)

/-- Shifting right past the width gives `0`. -/
theorem lshr_past_width (h : w ≤ y.toNat) : Word.lshr x y = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [word_lshr, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) h))]; simp

/-- An arithmetic shift past the width fills with the sign: all ones or `0`. -/
theorem sshiftRight_past_width {n : Nat} (h : w ≤ n) : x.sshiftRight n = if x.msb then BitVec.allOnes w else 0 := by
  have hl : ∀ z : BitVec w, z >>> n = 0 := fun z => by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le z.isLt (Nat.pow_le_pow_right (by omega) h))]; simp
  cases hx : x.msb
  · simp [BitVec.sshiftRight_eq_of_msb_false hx, hl]
  · simp [BitVec.sshiftRight_eq_of_msb_true hx, hl]

theorem ashr_past_width (h : w ≤ y.toNat) : Word.ashr x y = if x.msb then BitVec.allOnes w else 0 :=
  sshiftRight_past_width x h

end Edges

theorem math_lshift_past (a : Nat) {w b : Nat} (h : w ≤ b) : mathBin .lshift w a b = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow 2 h) (Nat.dvd_mul_left _ _))

theorem math_rshift_past {w a b : Nat} (ha : a < 2 ^ w) (h : w ≤ b) : mathBin .rshift w a b = 0 :=
  Nat.div_eq_of_lt (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) h))

/-- `ashift` past the width is all ones for a negative value and `0` for any other. -/
theorem math_ashift_past {w a b : Nat} (ha : a < 2 ^ w) (h : w ≤ b) :
    mathBin .ashift w a b = if msb w a then 2 ^ w - 1 else 0 := by
  obtain ⟨x, rfl⟩ := exists_toNat ha
  rw [math_ashift, sshiftRight_past_width x h, msb_toNat]
  cases x.msb <;> simp

/-- Division and remainder by zero. -/
theorem math_div_zero (w a : Nat) : mathBin .div w a 0 = 2 ^ w - 1 := rfl
theorem math_rem_zero (w a : Nat) : mathBin .rem w a 0 = a := rfl
theorem math_srem_zero (w a : Nat) : mathBin .srem w a 0 = a := rfl
theorem math_smod_zero (w a : Nat) : mathBin .smod w a 0 = a := rfl

section EvalEdges
variable {w : Nat} (x y : BitVec w)

theorem evalBin_lshift_past (h : w ≤ y.toNat) : evalBin .lshift ⟨w, x⟩ ⟨w, y⟩ = .ok (.bits (0#w)) := by
  simp [evalBin, shl_past_width x y h]

theorem evalBin_rshift_past (h : w ≤ y.toNat) : evalBin .rshift ⟨w, x⟩ ⟨w, y⟩ = .ok (.bits (0#w)) := by
  simp [evalBin, lshr_past_width x y h]

theorem evalBin_ashift_past (h : w ≤ y.toNat) :
    evalBin .ashift ⟨w, x⟩ ⟨w, y⟩ = .ok (.bits (if x.msb then BitVec.allOnes w else 0#w)) := by
  simp [evalBin, ashr_past_width x y h]

theorem evalBin_div_zero : evalBin .div ⟨w, x⟩ ⟨w, 0#w⟩ = .ok (.bits (BitVec.allOnes w)) := by
  simp [evalBin, Word.udiv, Word.ones]

theorem evalBin_rem_zero : evalBin .rem ⟨w, x⟩ ⟨w, 0#w⟩ = .ok (.bits x) := by simp [evalBin, Word.urem]

theorem evalBin_sdiv_zero :
    evalBin .sdiv ⟨w, x⟩ ⟨w, 0#w⟩ = .ok (.bits (if x.toInt < 0 then 1#w else BitVec.allOnes w)) := by
  simp [evalBin, ← word_sdiv_zero]

theorem evalBin_srem_zero : evalBin .srem ⟨w, x⟩ ⟨w, 0#w⟩ = .ok (.bits x) := by simp [evalBin, Word.srem]

theorem evalBin_smod_zero : evalBin .smod ⟨w, x⟩ ⟨w, 0#w⟩ = .ok (.bits x) := by simp [evalBin, Word.smod]

end EvalEdges

/-- `intMin / -1` overflows back to `intMin`. -/
theorem word_intMin_sdiv (w : Nat) : Word.sdiv (BitVec.intMin w) (-1#w) = BitVec.intMin w := by
  rcases w with _ | w
  · exact Subsingleton.elim ..
  · have h : (-1#(w + 1)) ≠ 0 := by simp
    rw [word_sdiv_of_ne _ h, BitVec.intMin_sdiv_neg_one]

theorem word_intMin_srem (w : Nat) : Word.srem (BitVec.intMin w) (-1#w) = 0 := by
  rcases w with _ | w
  · exact Subsingleton.elim ..
  · have h : (-1#(w + 1)) ≠ 0 := by simp
    rw [Word.srem, ite_eq_right h]
    apply BitVec.eq_of_toInt_eq
    simp [BitVec.toInt_srem, BitVec.neg_one_eq_allOnes]

theorem word_intMin_smod (w : Nat) : Word.smod (BitVec.intMin w) (-1#w) = 0 := by
  rcases w with _ | w
  · exact Subsingleton.elim ..
  · apply BitVec.eq_of_toInt_eq
    simp [Word.smod, BitVec.toInt_smod, BitVec.neg_one_eq_allOnes, Int.fmod_eq_zero_of_dvd]

theorem evalBin_intMin_sdiv (w : Nat) :
    evalBin .sdiv ⟨w, BitVec.intMin w⟩ ⟨w, -1#w⟩ = .ok (.bits (BitVec.intMin w)) := by
  simp only [evalBin, ↓reduceDIte]; exact congrArg (fun z => (.ok (.bits z) : Except String Value)) (word_intMin_sdiv w)

theorem evalBin_intMin_srem (w : Nat) : evalBin .srem ⟨w, BitVec.intMin w⟩ ⟨w, -1#w⟩ = .ok (.bits (0#w)) := by
  simp only [evalBin, ↓reduceDIte]; exact congrArg (fun z => (.ok (.bits z) : Except String Value)) (word_intMin_srem w)

theorem evalBin_intMin_smod (w : Nat) : evalBin .smod ⟨w, BitVec.intMin w⟩ ⟨w, -1#w⟩ = .ok (.bits (0#w)) := by
  simp only [evalBin, ↓reduceDIte]; exact congrArg (fun z => (.ok (.bits z) : Except String Value)) (word_intMin_smod w)

theorem toNat_intMin_neg_one {w : Nat} (hw : 0 < w) :
    (BitVec.intMin w).toNat = 2 ^ (w - 1) ∧ (-1#w).toNat = 2 ^ w - 1 :=
  ⟨BitVec.toNat_intMin_of_pos hw, by simp [BitVec.neg_one_eq_allOnes]⟩

/-- `intMin / -1 = intMin`, in numbers. -/
theorem math_intMin_sdiv {w : Nat} (hw : 0 < w) : mathBin .sdiv w (2 ^ (w - 1)) (2 ^ w - 1) = 2 ^ (w - 1) := by
  obtain ⟨h1, h2⟩ := toNat_intMin_neg_one hw
  rw [← h1, ← h2, math_sdiv, word_intMin_sdiv]

theorem math_intMin_srem {w : Nat} (hw : 0 < w) : mathBin .srem w (2 ^ (w - 1)) (2 ^ w - 1) = 0 := by
  obtain ⟨h1, h2⟩ := toNat_intMin_neg_one hw
  rw [← h1, ← h2, math_srem, word_intMin_srem]; simp

theorem math_intMin_smod {w : Nat} (hw : 0 < w) : mathBin .smod w (2 ^ (w - 1)) (2 ^ w - 1) = 0 := by
  obtain ⟨h1, h2⟩ := toNat_intMin_neg_one hw
  rw [← h1, ← h2, math_smod, word_intMin_smod]; simp

/-! Signs -/

theorem signedOf_neg_iff {w a : Nat} (ha : a < 2 ^ w) : signedOf w a < 0 ↔ msb w a = true := by
  obtain ⟨x, rfl⟩ := exists_toNat ha
  have h : (x.toNat : Int) < ((2 ^ w : Nat) : Int) := by exact_mod_cast x.isLt
  rw [signedOf_toNat, msb_toNat, BitVec.toInt_eq_msb_cond]
  generalize ((2 ^ w : Nat) : Int) = m at *
  cases x.msb <;> simp <;> omega

theorem signedOf_ne_zero {w a : Nat} (ha : a < 2 ^ w) (h : a ≠ 0) : signedOf w a ≠ 0 := by
  obtain ⟨x, rfl⟩ := exists_toNat ha
  have hb : (x.toNat : Int) < ((2 ^ w : Nat) : Int) := by exact_mod_cast x.isLt
  rw [signedOf_toNat, BitVec.toInt_eq_msb_cond]
  generalize ((2 ^ w : Nat) : Int) = m at *
  cases x.msb <;> simp <;> omega

/-- `smod` is the floored remainder of the signed values, with no overflow at all. -/
theorem signedOf_smod {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    signedOf w (mathBin .smod w a b) = (signedOf w a).fmod (signedOf w b) := by
  obtain ⟨x, rfl⟩ := exists_toNat ha
  obtain ⟨y, rfl⟩ := exists_toNat hb
  rw [math_smod, signedOf_toNat, signedOf_toNat, signedOf_toNat, Word.smod, BitVec.toInt_smod]

/-- `srem` is the truncated remainder of the signed values, with no overflow at all. -/
theorem signedOf_srem {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    signedOf w (mathBin .srem w a b) = (signedOf w a).tmod (signedOf w b) := by
  obtain ⟨x, rfl⟩ := exists_toNat ha
  obtain ⟨y, rfl⟩ := exists_toNat hb
  rw [math_srem, signedOf_toNat, signedOf_toNat, signedOf_toNat, Word.srem]
  split
  · simp [*]
  · rw [BitVec.toInt_srem]

theorem fmod_sign (a : Int) {b : Int} :
    (0 < b → 0 ≤ a.fmod b ∧ a.fmod b < b) ∧ (b < 0 → b < a.fmod b ∧ a.fmod b ≤ 0) := by
  refine ⟨fun h => ⟨Int.fmod_nonneg_of_pos _ h, Int.fmod_lt_of_pos _ h⟩, fun h => ?_⟩
  have e : a.fmod b = -((-a).fmod (-b)) := by rw [Int.neg_fmod_neg, Int.neg_neg]
  have h1 := Int.fmod_nonneg_of_pos (-a) (b := -b) (by omega)
  have h2 := Int.fmod_lt_of_pos (-a) (b := -b) (by omega)
  omega

/-- The sign of a nonzero `smod` follows the divisor, and its magnitude is below the divisor's. -/
theorem smod_sign_follows_divisor {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) (h : b ≠ 0)
    (hr : mathBin .smod w a b ≠ 0) :
    (signedOf w (mathBin .smod w a b) < 0 ↔ signedOf w b < 0) ∧
      (signedOf w (mathBin .smod w a b)).natAbs < (signedOf w b).natAbs := by
  have hs := signedOf_ne_zero hb h
  have hrlt : mathBin .smod w a b < 2 ^ w := by
    obtain ⟨x, rfl⟩ := exists_toNat ha
    obtain ⟨y, rfl⟩ := exists_toNat hb
    rw [math_smod]; exact BitVec.isLt _
  have hr' := signedOf_ne_zero hrlt hr
  rw [signedOf_smod ha hb] at hr' ⊢
  obtain ⟨p, n⟩ := fmod_sign (signedOf w a) (b := signedOf w b)
  rcases Int.lt_or_gt_of_ne hs with g | g
  · have := n g; omega
  · have := p g; omega

/-- The sign of a nonzero `srem` follows the dividend, and its magnitude is below the divisor's. -/
theorem srem_sign_follows_dividend {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) (h : b ≠ 0)
    (hr : mathBin .srem w a b ≠ 0) :
    (signedOf w (mathBin .srem w a b) < 0 ↔ signedOf w a < 0) ∧
      (signedOf w (mathBin .srem w a b)).natAbs < (signedOf w b).natAbs := by
  have hs := signedOf_ne_zero hb h
  have hrlt : mathBin .srem w a b < 2 ^ w := by
    obtain ⟨x, rfl⟩ := exists_toNat ha
    obtain ⟨y, rfl⟩ := exists_toNat hb
    rw [math_srem]; exact BitVec.isLt _
  have hr' := signedOf_ne_zero hrlt hr
  rw [signedOf_srem ha hb] at hr' ⊢
  generalize signedOf w a = i at *
  generalize signedOf w b = j at *
  refine ⟨?_, by rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (by omega)⟩
  by_cases g : i < 0
  · have e : i.tmod j = -((-i).tmod j) := by rw [Int.neg_tmod, Int.neg_neg]
    have := Int.tmod_nonneg j (a := -i) (by omega)
    omega
  · have := Int.tmod_nonneg j (a := i) (by omega)
    omega

/-- A remainder differs from its dividend by a multiple of the divisor, for `smod`... -/
theorem smod_dvd {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    signedOf w b ∣ signedOf w a - signedOf w (mathBin .smod w a b) := by
  rw [signedOf_smod ha hb, Int.fmod_def]
  exact ⟨_, Int.sub_sub_self ..⟩

/-- ...and for `srem`. -/
theorem srem_dvd {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    signedOf w b ∣ signedOf w a - signedOf w (mathBin .srem w a b) := by
  rw [signedOf_srem ha hb, Int.tmod_def]
  exact ⟨_, Int.sub_sub_self ..⟩

/-- Signed division and remainder fit together: `(a /$ b) * b + a srem b = a` modulo `2^w`. -/
theorem sdiv_mul_add_srem {w : Nat} (x y : BitVec w) (h : y ≠ 0) : Word.sdiv x y * y + Word.srem x y = x := by
  have hn : y.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using h
  have hd : Word.sdiv x y = BitVec.ofInt w (x.toInt.tdiv y.toInt) := by
    apply BitVec.eq_of_toNat_eq; rw [word_sdiv, ite_eq_right hn, wrap_eq_ofInt]
  have hr : Word.srem x y = BitVec.ofInt w (x.toInt.tmod y.toInt) := by
    apply BitVec.eq_of_toNat_eq; rw [word_srem, ite_eq_right hn, wrap_eq_ofInt]
  conv => lhs; rw [hd, hr]; arg 1; arg 2; rw [← BitVec.ofInt_toInt (x := y)]
  rw [← BitVec.ofInt_mul, ← BitVec.ofInt_add, Int.add_comm, Int.tmod_add_tdiv_mul, BitVec.ofInt_toInt]

/-- The same in numbers. -/
theorem math_sdiv_srem {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) (h : b ≠ 0) :
    mathBin .add w (mathBin .mul w (mathBin .sdiv w a b) b) (mathBin .srem w a b) = a := by
  obtain ⟨x, rfl⟩ := exists_toNat ha
  obtain ⟨y, rfl⟩ := exists_toNat hb
  have hy : y ≠ 0 := fun e => h (by simp [e])
  have e := congrArg BitVec.toNat (sdiv_mul_add_srem x y hy)
  rw [word_add, word_mul] at e
  rw [math_sdiv, math_srem]; exact e

/-! Bits -/

theorem math_and_testBit (w a b i : Nat) : (mathBin .and w a b).testBit i = (a.testBit i && b.testBit i) :=
  Nat.testBit_and a b i

theorem math_or_testBit (w a b i : Nat) : (mathBin .or w a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_or a b i

theorem math_xor_testBit (w a b i : Nat) : (mathBin .xor w a b).testBit i = (a.testBit i ^^ b.testBit i) :=
  Nat.testBit_xor a b i

/-- `bvnot` as `2^w - 1 - s` is the bitwise complement of the text. -/
theorem bvnot_testBit {w s : Nat} (hs : s < 2 ^ w) {i : Nat} (hi : i < w) : (bvnot w s).testBit i = !s.testBit i := by
  have : 2 ^ w - 1 - s = 2 ^ w - (s + 1) := by omega
  simp [bvnot, this, Nat.testBit_two_pow_sub_succ hs, hi]

/-- A result always fits its width. -/
theorem mathBin_lt (op : BinOp) {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    mathBin op w a b < 2 ^ resultWidth op w := by
  obtain ⟨x, rfl⟩ := exists_toNat ha
  obtain ⟨y, rfl⟩ := exists_toNat hb
  obtain ⟨z, -, h⟩ := evalBin_math op x y
  exact h ▸ z.isLt

end WordMath

end Bap.Proofs.Bil
