import Lean
import Bap.Proofs.PrimusBisim

open Lean Elab Command in
/-- Bring private declarations of module `mod`, namespace `ns`, into scope by short name. -/
local elab "open_private " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

/-! What a run gets without reading the address of the instruction, it gets at every address. -/

namespace Bap.Proofs.Primus

open Bap.Primus.Semantics

local notation "SV" => Bap.Primus.Semantics.Value

open_private Bap.Primus.Semantics Bap.Primus.Semantics evalSequence evalList evalConditional apply eval evalCompiledSequence evalCompiledList evalCompiledConditional evalCompiled
  applyPrimitive applyPrimitiveIndex addressPrimitive expectBil condition leadingZeros freeze bindAssignable truth expectNat emit extend
  resolveFunction resolveDestination resolveSymbol intrinsicResult lookupState macroExpansion selectForm selectArm assignsLocal namesOf
open_private Bap.Proofs.Primus Bap.Proofs.Primus bind_ok

/-- A run of `c` doesn't know the address, and `c'` is the same but for it. -/
structure Anywhere (c c' : Context) : Prop where
  off : c.addressed = false
  bits : c.bits = c'.bits
  endian : c.endian = c'.endian
  memory : c.memory = c'.memory
  prefixes : c.prefixes = c'.prefixes

variable {c c' : Context}

theorem Anywhere.expectBil (h : Anywhere c c') (v : SV) : expectBil c v = expectBil c' v := by
  obtain ⟨_, h1, h2, h3, h4⟩ := h
  cases c; cases c'; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

theorem Anywhere.condition (h : Anywhere c c') (v : SV) : condition c v = condition c' v := by
  obtain ⟨_, h1, h2, h3, h4⟩ := h
  cases c; cases c'; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

theorem Anywhere.leadingZeros (h : Anywhere c c') (v : List SV) : leadingZeros c v = leadingZeros c' v := by
  obtain ⟨_, h1, h2, h3, h4⟩ := h
  cases c; cases c'; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

theorem Anywhere.freeze (h : Anywhere c c') (s : State) (v : SV) : freeze c s v = freeze c' s v := by
  obtain ⟨_, h1, h2, h3, h4⟩ := h
  cases c; cases c'; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

theorem Anywhere.bindAssignable (h : Anywhere c c') (s : State) (v : SV) : bindAssignable c s v = bindAssignable c' s v := by
  obtain ⟨_, h1, h2, h3, h4⟩ := h
  cases c; cases c'; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

theorem Anywhere.address (h : Anywhere c c') (next : Bool) {r : SV × Bil.Program} (hr : addressPrimitive c next = .ok r) : addressPrimitive c' next = .ok r := by
  simp [addressPrimitive, h.off] at hr

theorem Anywhere.primitive (h : Anywhere c c') (name : String) (args : List SV) {r : SV × Bil.Program} (hr : applyPrimitive c name args = .ok r) :
    applyPrimitive c' name args = .ok r := by
  have hz := h.address (r := r)
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  cases c; cases c'; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4
  unfold applyPrimitive at hr ⊢
  split at hr
  all_goals first
    | exact hr
    | exact hz _ hr

theorem Anywhere.primitiveIndex (h : Anywhere c c') (op : Nat) (args : List SV) {r : SV × Bil.Program} (hr : applyPrimitiveIndex c op args = .ok r) :
    applyPrimitiveIndex c' op args = .ok r := by
  have hz := h.address (r := r)
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  cases c; cases c'; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4
  unfold applyPrimitiveIndex at hr ⊢
  split at hr
  all_goals first
    | exact hr
    | exact hz _ hr

private theorem bind_of {α β : Type} {x : Except String α} {f : α → Except String β} {v : α} {r : β} (hx : x = .ok v) (h : f v = .ok r) :
    (x >>= f) = .ok r := by
  subst hx
  exact h

/-- All of the evaluator at a fuel. -/
structure AnySim (c c' : Context) (fuel : Nat) : Prop where
  iSeq : ∀ {locals s forms r}, evalSequence fuel locals c s forms = .ok r → evalSequence fuel locals c' s forms = .ok r
  iList : ∀ {locals s forms r}, evalList fuel locals c s forms = .ok r → evalList fuel locals c' s forms = .ok r
  iCond : ∀ {locals s test yes no r}, evalConditional fuel locals c s test yes no = .ok r → evalConditional fuel locals c' s test yes no = .ok r
  iApply : ∀ {s value args r}, apply fuel c s value args = .ok r → apply fuel c' s value args = .ok r
  iEval : ∀ {locals s form r}, eval fuel locals c s form = .ok r → eval fuel locals c' s form = .ok r
  iCSeq : ∀ {locals s forms r}, evalCompiledSequence fuel locals c s forms = .ok r → evalCompiledSequence fuel locals c' s forms = .ok r
  iCList : ∀ {locals s forms r}, evalCompiledList fuel locals c s forms = .ok r → evalCompiledList fuel locals c' s forms = .ok r
  iCCond : ∀ {locals s test yes no r}, evalCompiledConditional fuel locals c s test yes no = .ok r →
    evalCompiledConditional fuel locals c' s test yes no = .ok r
  iComp : ∀ {locals s form r}, evalCompiled fuel locals c s form = .ok r → evalCompiled fuel locals c' s form = .ok r

private theorem conditional_any (hc : Anywhere c c') {test test' : Nat → Except String (SV × State)} {yes yes' no no' : Nat → State → Except String (SV × State)} {fuel : Nat}
    (ht : ∀ r, test fuel = .ok r → test' fuel = .ok r) (hy : ∀ s r, yes fuel s = .ok r → yes' fuel s = .ok r)
    (hn : ∀ s r, no fuel s = .ok r → no' fuel s = .ok r) {r : SV × State}
    (h : conditionalBody c test yes no fuel = .ok r) : conditionalBody c' test' yes' no' fuel = .ok r := by
  simp only [conditionalBody] at h ⊢
  obtain ⟨⟨tv, s⟩, h1, h⟩ := bind_ok h
  refine bind_of (ht _ h1) ?_
  obtain ⟨tr, h2, h⟩ := bind_ok h
  refine bind_of h2 ?_
  match tr, h with
  | some true, h => exact hy s _ h
  | some false, h => exact hn s _ h
  | none, h =>
    obtain ⟨cd, h3, h⟩ := bind_ok h
    rw [hc.condition] at h3
    refine bind_of h3 ?_
    obtain ⟨⟨yv, ys⟩, h4, h⟩ := bind_ok h
    refine bind_of (hy _ _ h4) ?_
    obtain ⟨⟨nv, ns⟩, h5, h⟩ := bind_ok h
    refine bind_of (hn _ _ h5) ?_
    simp only [hc.expectBil] at h
    exact h

theorem AnySim.seq_succ (ih : AnySim c c' fuel) {locals s forms r} (h : evalSequence (fuel + 1) locals c s forms = .ok r) :
    evalSequence (fuel + 1) locals c' s forms = .ok r := by
  rw [evalSequence.eq_def] at h
  simp only at h
  split at h
  · simpa only [evalSequence] using h
  · simp only [evalSequence]
    exact ih.iEval h
  · obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [evalSequence]
    exact bind_of (ih.iEval h1) (ih.iSeq h)

theorem AnySim.list_succ (ih : AnySim c c' fuel) {locals s forms r} (h : evalList (fuel + 1) locals c s forms = .ok r) :
    evalList (fuel + 1) locals c' s forms = .ok r := by
  rw [evalList.eq_def] at h
  simp only at h
  split at h
  · simpa only [evalList] using h
  · obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    obtain ⟨⟨vs, s2⟩, h2, h⟩ := bind_ok h
    simp only [evalList]
    exact bind_of (ih.iEval h1) (bind_of (ih.iList h2) h)

theorem AnySim.cond_succ (hc : Anywhere c c') (ih : AnySim c c' fuel) {locals s test yes no r} (h : evalConditional (fuel + 1) locals c s test yes no = .ok r) :
    evalConditional (fuel + 1) locals c' s test yes no = .ok r := by
  rw [evalConditional_body] at h ⊢
  exact conditional_any hc (fun _ h => ih.iEval h) (fun _ _ h => ih.iSeq h) (fun _ _ h => ih.iSeq h) h

theorem AnySim.ccond_succ (hc : Anywhere c c') (ih : AnySim c c' fuel) {locals s test yes no r} (h : evalCompiledConditional (fuel + 1) locals c s test yes no = .ok r) :
    evalCompiledConditional (fuel + 1) locals c' s test yes no = .ok r := by
  rw [evalCompiledConditional_body] at h ⊢
  exact conditional_any hc (fun _ h => ih.iComp h) (fun _ _ h => ih.iCSeq h) (fun _ _ h => ih.iCSeq h) h

theorem AnySim.apply_succ (hc : Anywhere c c') (ih : AnySim c c' fuel) {s value args r} (h : apply (fuel + 1) c s value args = .ok r) :
    apply (fuel + 1) c' s value args = .ok r := by
  rw [apply.eq_def] at h
  simp only at h
  split at h
  · rename_i name
    simp only [apply]
    obtain ⟨⟨v, code⟩, h1, h⟩ := bind_ok h
    refine bind_of (hc.primitive name _ h1) ?_
    simp only [hc.freeze] at h
    exact h
  · rename_i candidates
    simp only [apply]
    cases hr : resolveFunction args.length candidates with
    | none =>
      simp only [hr] at h
      cases h
    | some x =>
      simp only [hr] at h
      exact ih.iApply h
  · simp only [apply]
    split at h
    · cases h
    · rename_i hne
      simp only [hne]
      exact ih.iSeq h
  · simp only [apply]
    split at h
    · cases h
    · rename_i hne
      simp only [hne]
      exact ih.iCSeq h
  · cases h
  · cases h

theorem AnySim.cseq_succ (ih : AnySim c c' fuel) {locals s forms r} (h : evalCompiledSequence (fuel + 1) locals c s forms = .ok r) :
    evalCompiledSequence (fuel + 1) locals c' s forms = .ok r := by
  rw [evalCompiledSequence.eq_def] at h
  simp only at h
  split at h
  · simpa only [evalCompiledSequence] using h
  · simp only [evalCompiledSequence]
    exact ih.iComp h
  · obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [evalCompiledSequence]
    exact bind_of (ih.iComp h1) (ih.iCSeq h)

theorem AnySim.clist_succ (ih : AnySim c c' fuel) {locals s forms r} (h : evalCompiledList (fuel + 1) locals c s forms = .ok r) :
    evalCompiledList (fuel + 1) locals c' s forms = .ok r := by
  rw [evalCompiledList.eq_def] at h
  simp only at h
  split at h
  · simpa only [evalCompiledList] using h
  · obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    obtain ⟨⟨vs, s2⟩, h2, h⟩ := bind_ok h
    simp only [evalCompiledList]
    exact bind_of (ih.iComp h1) (bind_of (ih.iCList h2) h)

theorem AnySim.comp_succ (hc : Anywhere c c') (ih : AnySim c c' fuel) {locals s form r} (h : evalCompiled (fuel + 1) locals c s form = .ok r) :
    evalCompiled (fuel + 1) locals c' s form = .ok r := by
  rw [evalCompiled.eq_def] at h
  simp only at h
  split at h
  · simpa only [evalCompiled] using h
  · simpa only [evalCompiled] using h
  · simpa only [evalCompiled] using h
  · simp only [evalCompiled]
    obtain ⟨⟨vs, s1⟩, h1, h⟩ := bind_ok h
    refine bind_of (ih.iCList h1) ?_
    obtain ⟨⟨v, code⟩, h2, h⟩ := bind_ok h
    exact bind_of (hc.primitiveIndex _ _ h2) h
  · obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    obtain ⟨⟨vs, s2⟩, h2, h⟩ := bind_ok h
    simp only [evalCompiled]
    exact bind_of (ih.iComp h1) (bind_of (ih.iCList h2) (ih.iApply h))
  · simp only [evalCompiled]
    exact ih.iCCond h
  · obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [evalCompiled]
    refine bind_of (ih.iComp h1) ?_
    simp only [hc.freeze] at h ⊢
    exact ih.iComp h
  · simp only [evalCompiled]
    exact ih.iCSeq h
  · obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [evalCompiled]
    refine bind_of (ih.iComp h1) ?_
    obtain ⟨arm, h2, h⟩ := bind_ok h
    exact bind_of h2 (ih.iComp h)

theorem AnySim.letStep_any (hc : Anywhere c c') (ih : AnySim c c' fuel) {all body : List Sexp} {current : Locals × State} {binding : Sexp} {r : Locals × State}
    (h : letStep fuel c all body current binding = .ok r) : letStep fuel c' all body current binding = .ok r := by
  simp only [letStep] at h ⊢
  split at h
  · obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    refine bind_of (ih.iEval h1) ?_
    simp only [hc.bindAssignable, hc.freeze] at h ⊢
    exact h
  · cases h

theorem AnySim.foldlM_any (hc : Anywhere c c') (ih : AnySim c c' fuel) {all body bindings : List Sexp} {current : Locals × State} {r : Locals × State}
    (h : bindings.foldlM (letStep fuel c all body) current = .ok r) : bindings.foldlM (letStep fuel c' all body) current = .ok r := by
  induction bindings generalizing current with
  | nil => simpa only [List.foldlM_nil] using h
  | cons head rest ih' =>
    simp only [List.foldlM_cons] at h ⊢
    obtain ⟨x, h1, h⟩ := bind_ok h
    exact bind_of (ih.letStep_any hc h1) (ih' h)

theorem AnySim.form_succ (hc : Anywhere c c') (ih : AnySim c c' fuel) {locals s form r} (h : eval (fuel + 1) locals c s form = .ok r) :
    eval (fuel + 1) locals c' s form = .ok r := by
  rw [eval.eq_def] at h
  simp only at h
  split at h
  · -- an atom
    simp only [eval]
    exact h
  · simpa only [eval] using h
  · simpa only [eval] using h
  · -- sizeof
    simp only [eval, ← hc.bits]
    exact h
  · -- an assertion
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [eval]
    exact bind_of (ih.iEval h1) h
  · -- replicate
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    obtain ⟨⟨k, s2⟩, h2, h⟩ := bind_ok h
    simp only [eval]
    refine bind_of (ih.iEval h1) (bind_of (ih.iEval h2) ?_)
    simp only [hc.expectBil] at h
    exact h
  · -- replicate by its other name
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    obtain ⟨⟨k, s2⟩, h2, h⟩ := bind_ok h
    simp only [eval]
    refine bind_of (ih.iEval h1) (bind_of (ih.iEval h2) ?_)
    simp only [hc.expectBil] at h
    exact h
  · -- clz
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [eval]
    refine bind_of (ih.iEval h1) ?_
    simp only [hc.leadingZeros] at h
    exact h
  · simp only [eval]
    exact ih.iCond h
  · simp only [eval]
    exact ih.iCond h
  · simp only [eval]
    exact ih.iCond h
  · simp only [eval]
    exact ih.iSeq h
  · simp only [eval]
    exact ih.iSeq h
  · -- a loop
    rename_i _ loopBody
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [eval]
    refine bind_of (ih.iEval h1) ?_
    obtain ⟨tr, h2, h⟩ := bind_ok h
    refine bind_of h2 ?_
    have tail :
        (do
          let cd ← condition c v
          let (_, bodyState) ← evalSequence fuel locals c { s1 with code := [] } loopBody
          Except.ok (Value.unit, emit { bodyState with code := s.code } (s1.code ++ [.while cd (bodyState.code ++ s1.code)]))) = Except.ok r →
        (do
          let cd ← condition c' v
          let (_, bodyState) ← evalSequence fuel locals c' { s1 with code := [] } loopBody
          Except.ok (Value.unit, emit { bodyState with code := s.code } (s1.code ++ [.while cd (bodyState.code ++ s1.code)]))) = Except.ok r := by
      intro he
      obtain ⟨cd, h3, he⟩ := bind_ok he
      rw [hc.condition] at h3
      refine bind_of h3 ?_
      obtain ⟨⟨_, bs⟩, h4, he⟩ := bind_ok he
      exact bind_of (ih.iSeq h4) he
    match tr, h with
    | some false, h => exact h
    | some true, h => exact tail h
    | none, h => exact tail h
  · -- an error
    split at h <;> cases h
  · simpa only [eval] using h
  · -- let
    rename_i bindings body
    obtain ⟨⟨locals2, s2⟩, h1, h⟩ := bind_ok h
    have hE : eval (fuel + 1) locals c' s (.list (.atom "let" :: .list bindings :: body)) =
        bindings.foldlM (letStep fuel c' bindings body) (locals, s) >>= fun x =>
          evalSequence fuel x.1 c' x.2 body := by
      rw [eval]
      rfl
    rw [hE]
    exact bind_of (ih.foldlM_any hc h1) (ih.iSeq h)
  · -- a function
    simp only [eval]
    exact h
  · -- a case
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [eval]
    refine bind_of (ih.iEval h1) ?_
    obtain ⟨forms, h2, h⟩ := bind_ok h
    exact bind_of h2 (ih.iSeq h)
  · -- a call of a name
    rename_i operator operands _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    have hE : eval (fuel + 1) locals c' s (.list (.atom operator :: operands)) = (do
        let expansion ← match ← lookupState operator locals s with
          | .callable callable =>
            if (Assoc.get operator locals).isSome then .ok none else macroExpansion callable operands
          | _ => .ok none
        match expansion with
        | some expanded => evalSequence fuel locals c' s expanded
        | none =>
          eval fuel locals c' s (.atom operator) >>= fun x =>
            evalList fuel locals c' x.2 operands >>= fun y => apply fuel c' y.2 x.1 y.1) := by
      rw [eval]
      · rfl
      all_goals (intros; simp_all)
    rw [hE]
    obtain ⟨lv, h0, h⟩ := bind_ok h
    refine bind_of h0 ?_
    have tail : ∀ {e : Except String (Option (List Sexp))},
        (do
          let expansion ← e
          match expansion with
          | some body => evalSequence fuel locals c s body
          | none => do
            let x ← eval fuel locals c s (Sexp.atom operator)
            let y ← evalList fuel locals c x.2 operands
            apply fuel c y.2 x.1 y.1) = .ok r →
        (do
          let expansion ← e
          match expansion with
          | some body => evalSequence fuel locals c' s body
          | none => do
            let x ← eval fuel locals c' s (Sexp.atom operator)
            let y ← evalList fuel locals c' x.2 operands
            apply fuel c' y.2 x.1 y.1) = .ok r := by
      intro e he
      obtain ⟨exp, h3, he⟩ := bind_ok he
      refine bind_of h3 ?_
      match exp, he with
      | some expanded, he => exact ih.iSeq he
      | none, he =>
        obtain ⟨⟨v, s1⟩, h4, he⟩ := bind_ok he
        obtain ⟨⟨vs, s2⟩, h5, he⟩ := bind_ok he
        exact bind_of (ih.iEval h4) (bind_of (ih.iList h5) (ih.iApply he))
    cases lv with
    | callable cb =>
      simp only at h ⊢
      by_cases hb : (Assoc.get operator locals).isSome = true
      · simp only [hb] at h ⊢
        exact tail h
      · simp only [hb] at h ⊢
        exact tail h
    | unit => exact tail h
    | int => exact tail h
    | bil => exact tail h
    | bool => exact tail h
    | register => exact tail h
    | symbol => exact tail h
    | list => exact tail h
  · -- a call of a form
    obtain ⟨⟨v, s1⟩, h4, h⟩ := bind_ok h
    obtain ⟨⟨vs, s2⟩, h5, h⟩ := bind_ok h
    simp only [eval]
    exact bind_of (ih.iEval h4) (bind_of (ih.iList h5) (ih.iApply h))

theorem anySim (hc : Anywhere c c') (fuel : Nat) : AnySim c c' fuel := by
  induction fuel with
  | zero =>
    constructor
    · intro _ _ _ _ h
      rw [evalSequence.eq_def] at h
      cases h
    · intro _ _ _ _ h
      rw [evalList.eq_def] at h
      cases h
    · intro _ _ _ _ _ _ h
      rw [evalConditional.eq_def] at h
      cases h
    · intro _ _ _ _ h
      rw [apply.eq_def] at h
      cases h
    · intro _ _ _ _ h
      rw [eval.eq_def] at h
      cases h
    · intro _ _ _ _ h
      rw [evalCompiledSequence.eq_def] at h
      cases h
    · intro _ _ _ _ h
      rw [evalCompiledList.eq_def] at h
      cases h
    · intro _ _ _ _ _ _ h
      rw [evalCompiledConditional.eq_def] at h
      cases h
    · intro _ _ _ _ h
      rw [evalCompiled.eq_def] at h
      cases h
  | succ fuel ih =>
    exact ⟨ih.seq_succ, ih.list_succ, ih.cond_succ hc, ih.apply_succ hc, ih.form_succ hc, ih.cseq_succ, ih.clist_succ, ih.ccond_succ hc, ih.comp_succ hc⟩

/-- **What a run gets without the address of the instruction, it gets at every address**: reading it is the only use of
`pc` and `nextPc`, and it is an error that nothing in the evaluator recovers from. -/
theorem apply_anywhere (hc : Anywhere c c') {fuel : Nat} {s : State} {value : SV} {args : List SV} {r : SV × State}
    (h : apply fuel c s value args = .ok r) : apply fuel c' s value args = .ok r :=
  (anySim hc fuel).iApply h

/-- `eval` the same. -/
theorem eval_anywhere (hc : Anywhere c c') {fuel : Nat} {locals : Locals} {s : State} {form : Sexp} {r : SV × State}
    (h : eval fuel locals c s form = .ok r) : eval fuel locals c' s form = .ok r :=
  (anySim hc fuel).iEval h

/-- `evalCompiled` the same. -/
theorem evalCompiled_anywhere (hc : Anywhere c c') {fuel : Nat} {locals : Locals} {s : State} {form : CExp} {r : SV × State}
    (h : evalCompiled fuel locals c s form = .ok r) : evalCompiled fuel locals c' s form = .ok r :=
  (anySim hc fuel).iComp h

/-- The context of a lift without its address. -/
theorem anywhere_off (c : Context) (pc next : Nat) (addressed : Bool) :
    Anywhere { c with addressed := false } { c with pc := pc, nextPc := next, addressed := addressed } :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem liftCode_anywhere (hc : Anywhere c c') {env : Environment} {callable : SV} {operands : List SV} {p : Bil.Program}
    (h : liftCode env c callable operands = .ok p) : liftCode env c' callable operands = .ok p := by
  simp only [liftCode] at h ⊢
  split at h
  · rename_i hr
    rw [apply_anywhere hc hr]
    exact h
  · cases h

theorem liftWithCode_anywhere (hc : Anywhere c c') {env : Environment} {name : String} {operands : List SV} {p : Bil.Program}
    (h : liftWithCode env c name operands = .ok p) : liftWithCode env c' name operands = .ok p := by
  simp only [liftWithCode] at h ⊢
  obtain ⟨callable, h1, h⟩ := bind_ok h
  refine bind_of h1 ?_
  split at h
  · rename_i hr
    rw [liftCode_anywhere hc hr]
    exact h
  · cases h

theorem liftMCCode_anywhere (hc : Anywhere c c') {env : Environment} {opcode : Nat} {operands : List SV} {p : Bil.Program}
    (h : liftMCCode env c opcode operands = .ok p) : liftMCCode env c' opcode operands = .ok p := by
  simp only [liftMCCode] at h ⊢
  obtain ⟨callable, h1, h⟩ := bind_ok h
  refine bind_of h1 ?_
  split at h
  · rename_i hr
    rw [liftCode_anywhere hc hr]
    exact h
  · cases h

end Bap.Proofs.Primus
