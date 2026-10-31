import Lean
import Bap.Proofs.IR

/-! Constant propagation keeps only the constants that can still be read at the end of each block (`constReads`).
This file proves that the rewrite comes out the same as with every constant kept.

The steps, each of which needs the one before:

1. `simplify_mono`: knowing more constants never loses a constant the rewrite found. This is what fails without
   `Constant.ofDef`'s check of the type and `isZeroLiteral`'s rule in `simplifyExp`.
2. `transfer_grows`: so a block's exit constants grow with its entry constants.
3. `propagateAux_above`: the worklist never drops below any solution of the equations.
4. `propagateAux_finishes`: its fuel is always enough, for any table of what to keep, as each change loses a constant.
5. `restricted_eq`: the restricted solution is the unrestricted one, cut down to what is kept. Each is a solution of the
   other's equations, and the worklist finds the greatest.
6. `propagateConstants_unrestricted`: what is cut is never read, so the rewrite is the same. -/


open Lean Elab Command in
/-- Bring private declarations of module `mod`, namespace `ns`, into scope by short name. -/
local elab "open_private " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

namespace Bap.Proofs.IR

open Bap Bap.Bil Bap.IR

open_private Bap.Bil.Transform Bap.Bil binRule iteRule simplifyExp_of_not_bits
open_private Bap.Bil.Typecheck Bap.Bil expectBits expectImm expectSameType
open_private Bap.Proofs.Bil Bap.Proofs.Bil comparison hasImmWidth_iff infer_bin_inv infer_load_inv infer_store_inv infer_un_inv infer_cast_inv infer_let_inv infer_ite_inv infer_extract_inv infer_concat_inv
open_private Bap.Proofs.IR Bap.Proofs.IR propStep propFold propEntry propJump propagateBlock_eq
open_private Bap.IR.Optimize Bap.IR replacements get_replacements propagateBlock propagateExit propagateExit_eq constStep removeConst_eq substConst substConst_eq joinEnv keepReads entryEnv propagateAux isSolved sameConsts settled propagateFuel constReads

/-! ### Simplifying knows more when more is known -/

/-- What `s'`, an expression `s` with more of its variables known, keeps of it. -/
structure SimpRel (s s' : Exp) : Prop where
  lit : ∀ {w} (v : BitVec w), s = .int v → s' = .int v
  typ : ∀ τ, inferExp s = .ok τ → inferExp s' = .ok τ
  unk : hasUnknown s' = true → hasUnknown s = true

theorem SimpRel.refl (s : Exp) : SimpRel s s := ⟨fun _ h => h, fun _ h => h, fun h => h⟩

theorem SimpRel.imm {s s' : Exp} (h : SimpRel s s') {w : Nat} (hw : hasImmWidth s w = true) : hasImmWidth s' w = true :=
  hasImmWidth_iff.2 (h.typ _ (hasImmWidth_iff.1 hw))

theorem SimpRel.known {s s' : Exp} (h : SimpRel s s') (hu : (!hasUnknown s) = true) : (!hasUnknown s') = true := by
  cases hs : hasUnknown s' with
  | false => rfl
  | true =>
    have := h.unk hs
    simp [this] at hu

private theorem infer_int {w : Nat} (v : BitVec w) (hw : 0 < w) : inferExp (.int v) = .ok (.imm w) := by
  cases w with
  | zero => omega
  | succ w => rfl

private theorem infer_bin_ok {op : BinOp} {l r : Exp} {w : Nat} (hl : inferExp l = .ok (.imm w)) (hr : inferExp r = .ok (.imm w)) :
    inferExp (.bin op l r) = .ok (if comparison op then .imm 1 else .imm w) := by
  simp only [inferExp, hl, hr]
  cases op <;> simp [Bind.bind, Except.bind, comparison, expectImm]

private theorem rel_of_infer {s s' : Exp} (hs : ∀ {w} (v : BitVec w), s ≠ .int v)
    (ht : ∀ τ, inferExp s = .ok τ → inferExp s' = .ok τ) (hu : hasUnknown s' = true → hasUnknown s = true) : SimpRel s s' :=
  ⟨fun v h => absurd h (hs v), ht, hu⟩

/-- `binRule` gives one of its operands only for these operators. -/
private abbrev Ruled (op : BinOp) : Prop := comparison op = false

private theorem binRule_cases (op : BinOp) (l r : Exp) :
    binRule op l r = .bin op l r ∨ (Ruled op ∧ (binRule op l r = l ∨ binRule op l r = r)) := by
  simp only [binRule]
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr ⟨rfl, Or.inl rfl⟩
    | exact Or.inr ⟨rfl, Or.inr rfl⟩
    | skip

/-- Whatever becomes of an operation once more is known, it has what the operation had. -/
private theorem rel_bin_rule {op : BinOp} {l l' r r' : Exp} (hl : SimpRel l l') (hr : SimpRel r r') :
    SimpRel (.bin op l r) (binRule op l' r') := by
  refine rel_of_infer (fun _ h => by cases h) (fun τ h => ?_) (fun h => ?_)
  · obtain ⟨w, hlw, hrw, rfl⟩ := infer_bin_inv h
    have hl' := hl.typ _ hlw
    have hr' := hr.typ _ hrw
    rcases binRule_cases op l' r' with he | ⟨hc, he | he⟩ <;> rw [he]
    · exact infer_bin_ok hl' hr'
    · simpa [hc] using hl'
    · simpa [hc] using hr'
  · simp only [hasUnknown, Bool.or_eq_true]
    rcases binRule_cases op l' r' with he | ⟨_, he | he⟩ <;> rw [he] at h
    · simp only [hasUnknown, Bool.or_eq_true] at h
      exact h.imp hl.unk hr.unk
    · exact Or.inl (hl.unk h)
    · exact Or.inr (hr.unk h)

private abbrev NotLit (e : Exp) : Prop := ∀ {w} (v : BitVec w), e ≠ .int v

private theorem binRule_nonlit (op : BinOp) {l r : Exp} (hl : NotLit l) (hr : NotLit r) : binRule op l r = .bin op l r := by
  cases l <;> first
    | exact absurd rfl (hl _)
    | (cases r <;> first
        | exact absurd rfl (hr _)
        | (cases op <;> rfl))

private theorem binRule_add_right {l : Exp} (hl : NotLit l) {w} (b : BitVec w) :
    binRule .add l (.int b) = if b = 0 ∧ hasImmWidth l w then l else .bin .add l (.int b) := by
  cases l <;> first
    | exact absurd rfl (hl _)
    | rfl

private theorem binRule_mul_right {l : Exp} (hl : NotLit l) {w} (b : BitVec w) :
    binRule .mul l (.int b) =
      if !hasImmWidth l w then .bin .mul l (.int b) else if b = 1 then l
      else if b = 0 ∧ !hasUnknown l then .int b else .bin .mul l (.int b) := by
  cases l <;> first
    | exact absurd rfl (hl _)
    | rfl

private theorem binRule_sub (l : Exp) {w} (b : BitVec w) :
    binRule .sub l (.int b) = if b = 0 ∧ hasImmWidth l w then l else .bin .sub l (.int b) := by
  cases l <;> rfl

private theorem binRule_sub_nonlit (l : Exp) {r : Exp} (hr : NotLit r) : binRule .sub l r = .bin .sub l r := by
  cases r <;> first
    | exact absurd rfl (hr _)
    | (cases l <;> rfl)

private theorem notLit_or (e : Exp) : NotLit e ∨ ∃ w, ∃ v : BitVec w, e = .int v := by
  cases e with
  | @int w v => exact Or.inr ⟨w, v, rfl⟩
  | _ => exact Or.inl (fun _ h => by cases h)

private theorem has_bits {e : Exp} {w : Nat} (h : inferExp e = .ok (.imm w)) : 0 < w := (Bap.Proofs.Bil.inferExp_has_bits e).1 w h

/-- What is not a literal and has a width keeps it, as anything of that width. -/
private theorem rel_of_width {s s' : Exp} (hs : NotLit s) {w : Nat} (ht : inferExp s = .ok (.imm w) → inferExp s' = .ok (.imm w))
    (hty : ∀ τ, inferExp s = .ok τ → τ = .imm w) (hu : hasUnknown s' = true → hasUnknown s = true) : SimpRel s s' :=
  rel_of_infer hs (fun τ h => by
    have := hty τ h
    subst this
    exact ht h) hu

private theorem rel_add {l l' r r' : Exp} (hl : SimpRel l l') (hr : SimpRel r r') :
    SimpRel (binRule .add l r) (binRule .add l' r') := by
  rcases notLit_or l with hln | ⟨w, a, rfl⟩
  · rcases notLit_or r with hrn | ⟨w, b, rfl⟩
    · rw [binRule_nonlit _ hln hrn]
      exact rel_bin_rule hl hr
    · have hr' := hr.lit b rfl
      subst hr'
      rw [binRule_add_right hln]
      split
      · rename_i hc
        obtain ⟨rfl, hw⟩ := hc
        have hw' := hasImmWidth_iff.1 hw
        rcases notLit_or l' with hln' | ⟨w', a', rfl⟩
        · rw [binRule_add_right hln', ite_eq_left ⟨rfl, hl.imm hw⟩]
          exact hl
        · have hlw := hl.typ _ hw'
          have hpos := has_bits hw'
          have : w' = w := by
            cases w' with
            | zero => simp [inferExp, expectBits] at hlw
            | succ n => simpa [inferExp, expectBits] using hlw
          subst this
          show SimpRel l (if a' = 0 ∧ hasImmWidth (.int (0#w')) w' then .int (0#w') else .bin .add (.int a') (.int (0#w')))
          split
          · rename_i hc
            rw [hc.1] at hl
            exact hl
          · refine rel_of_width hln (w := w') (fun _ => ?_) (fun τ h => ?_) (by simp [hasUnknown])
            · simpa [comparison] using infer_bin_ok (op := .add) (infer_int a' hpos) (infer_int (0#w') hpos)
            · have := hw'
              rw [h] at this
              cases this
              rfl
      · exact rel_bin_rule hl hr
  · have hl' := hl.lit a rfl
    subst hl'
    show SimpRel (if a = 0 ∧ hasImmWidth r w then r else .bin .add (.int a) r)
      (if a = 0 ∧ hasImmWidth r' w then r' else .bin .add (.int a) r')
    by_cases hc : a = 0 ∧ hasImmWidth r w = true
    · rw [ite_eq_left hc, ite_eq_left ⟨hc.1, hr.imm hc.2⟩]
      exact hr
    · rw [ite_eq_right hc]
      have := rel_bin_rule (op := .add) hl hr
      have hrule : binRule .add (.int a) r' = if a = 0 ∧ hasImmWidth r' w then r' else .bin .add (.int a) r' := rfl
      rwa [hrule] at this

private theorem rel_sub {l l' r r' : Exp} (hl : SimpRel l l') (hr : SimpRel r r') :
    SimpRel (binRule .sub l r) (binRule .sub l' r') := by
  rcases notLit_or r with hrn | ⟨w, b, rfl⟩
  · rw [binRule_sub_nonlit _ hrn]
    exact rel_bin_rule hl hr
  · have hr' := hr.lit b rfl
    subst hr'
    rw [binRule_sub, binRule_sub]
    by_cases hc : b = 0 ∧ hasImmWidth l w = true
    · rw [ite_eq_left hc, ite_eq_left ⟨hc.1, hl.imm hc.2⟩]
      exact hl
    · rw [ite_eq_right hc]
      have := rel_bin_rule (op := .sub) hl hr
      rwa [binRule_sub] at this

private theorem rel_mul {l l' r r' : Exp} (hl : SimpRel l l') (hr : SimpRel r r') :
    SimpRel (binRule .mul l r) (binRule .mul l' r') := by
  rcases notLit_or l with hln | ⟨w, a, rfl⟩
  · rcases notLit_or r with hrn | ⟨w, b, rfl⟩
    · rw [binRule_nonlit _ hln hrn]
      exact rel_bin_rule hl hr
    · have hr' := hr.lit b rfl
      subst hr'
      rw [binRule_mul_right hln]
      by_cases hw : hasImmWidth l w = true
      · have hw' := hasImmWidth_iff.1 hw
        have hpos := has_bits hw'
        have hlw := hl.typ _ hw'
        have hb1 : ∀ τ, inferExp l = .ok τ → τ = .imm w := fun τ h => by
          rw [hw'] at h
          cases h
          rfl
        simp only [hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases notLit_or l' with hln' | ⟨w', a', rfl⟩
        · rw [binRule_mul_right hln']
          simp only [hl.imm hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          by_cases h1 : b = 1
          · simp only [h1, ↓reduceIte]
            exact hl
          · simp only [h1, ↓reduceIte]
            by_cases h0 : b = 0 ∧ (!hasUnknown l) = true
            · rw [ite_eq_left h0, ite_eq_left ⟨h0.1, hl.known h0.2⟩]
              exact SimpRel.refl _
            · rw [ite_eq_right h0]
              have := rel_bin_rule (op := .mul) hl hr
              rwa [binRule_mul_right hln', ite_eq_right (by simp [hl.imm hw]), ite_eq_right h1] at this
        · have : w' = w := by
            cases w' with
            | zero => simp [inferExp, expectBits] at hlw
            | succ n => simpa [inferExp, expectBits] using hlw
          subst this
          have hbi := infer_int b hpos
          have hbt : hasImmWidth (.int b) w' = true := hasImmWidth_iff.2 hbi
          have hrule : binRule .mul (.int a') (.int b) =
              if a' = 1 then .int b else if a' = 0 ∧ (!hasUnknown (.int b)) = true then .int a'
              else if isZeroLiteral (.int b) then .int b else .bin .mul (.int a') (.int b) := by
            show (if (!hasImmWidth (.int b) w') = true then _ else _) = _
            simp only [hbt, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rw [hrule]
          have hany : ∀ X : Exp, (X = .int b ∨ X = .int a' ∨ X = .bin .mul (.int a') (.int b)) → SimpRel l X := by
            rintro X (rfl | rfl | rfl)
            · exact rel_of_width hln (w := w') (fun _ => hbi) hb1 (by simp [hasUnknown])
            · exact rel_of_width hln (w := w') (fun _ => infer_int a' hpos) hb1 (by simp [hasUnknown])
            · refine rel_of_width hln (w := w') (fun _ => ?_) hb1 (by simp [hasUnknown])
              simpa [comparison] using infer_bin_ok (op := .mul) (infer_int a' hpos) hbi
          by_cases h1 : b = 1
          · rw [ite_eq_left h1]
            apply hany
            repeat' split
            all_goals simp
          · simp only [h1, ↓reduceIte]
            by_cases h0 : b = 0 ∧ (!hasUnknown l) = true
            · rw [ite_eq_left h0]
              obtain ⟨rfl, _⟩ := h0
              by_cases ha1 : a' = 1
              · rw [ite_eq_left ha1]
                exact SimpRel.refl _
              · rw [ite_eq_right ha1]
                by_cases ha0 : a' = 0
                · rw [ite_eq_left ⟨ha0, by simp [hasUnknown]⟩, ha0]
                  exact SimpRel.refl _
                · rw [ite_eq_right (fun h => ha0 h.1), ite_eq_left (by simp [isZeroLiteral])]
                  exact SimpRel.refl _
            · rw [ite_eq_right h0]
              apply rel_of_infer (fun _ h => by cases h)
              · intro τ h
                obtain ⟨_, hlt, _, rfl⟩ := infer_bin_inv h
                rw [hw'] at hlt
                cases hlt
                have hmul : inferExp (.bin .mul (.int a') (.int b)) = .ok (.imm w') := by
                  simpa [comparison] using infer_bin_ok (op := .mul) (infer_int a' hpos) hbi
                simp only [comparison, Bool.false_eq_true, ↓reduceIte]
                repeat' split
                all_goals first | exact hbi | exact infer_int a' hpos | exact hmul
              · intro h
                exfalso
                revert h
                repeat' split
                all_goals simp [hasUnknown]
      · rw [ite_eq_left (by simpa using hw)]
        exact rel_bin_rule hl hr
  · have hl' := hl.lit a rfl
    subst hl'
    have hrule : ∀ r : Exp, binRule .mul (.int a) r =
        if !hasImmWidth r w then .bin .mul (.int a) r else if a = 1 then r
        else if a = 0 ∧ !hasUnknown r then .int a else if isZeroLiteral r then r else .bin .mul (.int a) r := fun _ => rfl
    have hbin := rel_bin_rule (op := .mul) hl hr
    rw [hrule] at hbin ⊢
    rw [hrule]
    by_cases hw : hasImmWidth r w = true
    · have hw' := hr.imm hw
      simp only [hw, hw', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hbin ⊢
      by_cases h1 : a = 1
      · simp only [h1, ↓reduceIte]
        exact hr
      · simp only [h1, ↓reduceIte] at hbin ⊢
        by_cases h0 : a = 0 ∧ (!hasUnknown r) = true
        · rw [ite_eq_left h0, ite_eq_left ⟨h0.1, hr.known h0.2⟩]
          exact SimpRel.refl _
        · rw [ite_eq_right h0]
          by_cases hz : isZeroLiteral r = true
          · rw [ite_eq_left hz]
            cases r with
            | @int w₂ v =>
              have hr' := hr.lit v rfl
              subst hr'
              have ha : ¬ a = 0 := fun h => h0 ⟨h, by simp [hasUnknown]⟩
              rw [ite_eq_right (fun h => ha h.1), ite_eq_left hz]
              exact SimpRel.refl _
            | _ => simp [isZeroLiteral] at hz
          · rw [ite_eq_right hz]
            exact hbin
    · rw [ite_eq_left (by simpa using hw)]
      exact hbin

/-- `binRule` keeps what its operands keep. -/
theorem rel_binRule {op : BinOp} {l l' r r' : Exp} (hl : SimpRel l l') (hr : SimpRel r r') :
    SimpRel (binRule op l r) (binRule op l' r') := by
  cases op with
  | add => exact rel_add hl hr
  | sub => exact rel_sub hl hr
  | mul => exact rel_mul hl hr
  | _ => exact rel_bin_rule hl hr

private theorem rel_load {m m' a a' : Exp} {e : Endian} {n : Nat} (hm : SimpRel m m') (ha : SimpRel a a') :
    SimpRel (.load m a e n) (.load m' a' e n) := by
  refine rel_of_infer (fun _ h => by cases h) (fun τ h => ?_) (fun h => ?_)
  · obtain ⟨w, h₁, h₂, rfl, h₃⟩ := infer_load_inv h
    simp [inferExp, hm.typ _ h₁, ha.typ _ h₂, Bind.bind, Except.bind, expectImm, h₃]
  · simp only [hasUnknown, Bool.or_eq_true] at h ⊢
    exact h.imp hm.unk ha.unk

private theorem rel_store {m m' a a' v v' : Exp} {e : Endian} {n : Nat} (hm : SimpRel m m') (ha : SimpRel a a') (hv : SimpRel v v') :
    SimpRel (.store m a v e n) (.store m' a' v' e n) := by
  refine rel_of_infer (fun _ h => by cases h) (fun τ h => ?_) (fun h => ?_)
  · obtain ⟨w, h₁, h₂, h₃, rfl, h₄, h₅⟩ := infer_store_inv h
    simp [inferExp, hm.typ _ h₁, ha.typ _ h₂, hv.typ _ h₃, Bind.bind, Except.bind, expectImm, h₄, Nat.not_lt.2 h₅]
  · simp only [hasUnknown, Bool.or_eq_true] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (hm.unk h))
    · exact Or.inl (Or.inr (ha.unk h))
    · exact Or.inr (hv.unk h)

private theorem rel_un {op : UnOp} {v v' : Exp} (hv : SimpRel v v') : SimpRel (.un op v) (.un op v') := by
  refine rel_of_infer (fun _ h => by cases h) (fun τ h => ?_) (fun h => hv.unk h)
  obtain ⟨w, h₁, rfl⟩ := infer_un_inv h
  simp [inferExp, hv.typ _ h₁, Bind.bind, Except.bind, expectImm]

private theorem rel_cast {k : Cast} {w : Nat} {v v' : Exp} (hv : SimpRel v v') : SimpRel (.cast k w v) (.cast k w v') := by
  refine rel_of_infer (fun _ h => by cases h) (fun τ h => ?_) (fun h => hv.unk h)
  obtain ⟨source, h₁, rfl, h₂, h₃⟩ := infer_cast_inv h
  cases k <;> simp [inferExp, hv.typ _ h₁, Bind.bind, Except.bind, expectImm, h₂, h₃]

private theorem rel_extract {hi lo : Nat} {v v' : Exp} (hv : SimpRel v v') : SimpRel (.extract hi lo v) (.extract hi lo v') := by
  refine rel_of_infer (fun _ h => by cases h) (fun τ h => ?_) (fun h => hv.unk h)
  obtain ⟨w, h₁, rfl, h₂, h₃⟩ := infer_extract_inv h
  simp [inferExp, hv.typ _ h₁, Bind.bind, Except.bind, expectImm, Nat.not_lt.2 h₂, Nat.not_le.2 h₃]

private theorem rel_concat {l l' r r' : Exp} (hl : SimpRel l l') (hr : SimpRel r r') : SimpRel (.concat l r) (.concat l' r') := by
  refine rel_of_infer (fun _ h => by cases h) (fun τ h => ?_) (fun h => ?_)
  · obtain ⟨a, b, h₁, h₂, rfl⟩ := infer_concat_inv h
    simp [inferExp, hl.typ _ h₁, hr.typ _ h₂, Bind.bind, Except.bind, expectImm]
  · simp only [hasUnknown, Bool.or_eq_true] at h ⊢
    exact h.imp hl.unk hr.unk

private theorem rel_let {x : Var} {v v' b b' : Exp} (hv : SimpRel v v') (hb : SimpRel b b') : SimpRel (.letIn x v b) (.letIn x v' b') := by
  refine rel_of_infer (fun _ h => by cases h) (fun τ h => ?_) (fun h => ?_)
  · obtain ⟨h₁, h₂⟩ := infer_let_inv h
    simp [inferExp, hv.typ _ h₁, hb.typ _ h₂, Bind.bind, Except.bind]
  · simp only [hasUnknown, Bool.or_eq_true] at h ⊢
    exact h.imp hv.unk hb.unk

private theorem iteRule_nonlit {c : Exp} (hc : ∀ v : BitVec 1, c ≠ .int v) (y n : Exp) : iteRule c y n = .ite c y n := by
  cases c with
  | @int w v =>
    match w, v, hc with
    | 0, _, _ => rfl
    | 1, v, hc => exact absurd rfl (hc v)
    | _ + 2, _, _ => rfl
  | _ => rfl

private theorem iteRule_cases (c y n : Exp) : iteRule c y n = .ite c y n ∨ iteRule c y n = y ∨ iteRule c y n = n := by
  by_cases hc : ∀ v : BitVec 1, c ≠ .int v
  · exact Or.inl (iteRule_nonlit hc y n)
  · have : ∃ v : BitVec 1, c = .int v := by simpa using hc
    obtain ⟨v, rfl⟩ := this
    show (if v = 1 then y else n) = _ ∨ (if v = 1 then y else n) = _ ∨ (if v = 1 then y else n) = _
    split <;> simp

theorem rel_iteRule {c c' y y' n n' : Exp} (hc : SimpRel c c') (hy : SimpRel y y') (hn : SimpRel n n') :
    SimpRel (iteRule c y n) (iteRule c' y' n') := by
  by_cases hl : ∀ v : BitVec 1, c ≠ .int v
  · rw [iteRule_nonlit hl]
    refine rel_of_infer (fun _ h => by cases h) (fun τ h => ?_) (fun h => ?_)
    · obtain ⟨h₁, h₂, h₃⟩ := infer_ite_inv h
      have h₁' := hc.typ _ h₁
      have h₂' := hy.typ _ h₂
      have h₃' := hn.typ _ h₃
      rcases iteRule_cases c' y' n' with he | he | he <;> rw [he]
      · simp [inferExp, h₁', h₂', h₃', Bind.bind, Except.bind, expectImm, expectSameType]
      · exact h₂'
      · exact h₃'
    · simp only [hasUnknown, Bool.or_eq_true]
      rcases iteRule_cases c' y' n' with he | he | he <;> rw [he] at h
      · simp only [hasUnknown, Bool.or_eq_true] at h
        rcases h with (h | h) | h
        · exact Or.inl (Or.inl (hc.unk h))
        · exact Or.inl (Or.inr (hy.unk h))
        · exact Or.inr (hn.unk h)
      · exact Or.inl (Or.inr (hy.unk h))
      · exact Or.inr (hn.unk h)
  · have : ∃ v : BitVec 1, c = .int v := by simpa using hl
    obtain ⟨v, rfl⟩ := this
    have hc' := hc.lit v rfl
    subst hc'
    show SimpRel (if v = 1 then y else n) (if v = 1 then y' else n')
    split
    · exact hy
    · exact hn

/-! ### Under more constants -/

/-- A table says at least what another does. -/
def ConstLe (a b : ConstEnv) : Prop := ∀ v c, Assoc.get v a = some c → Assoc.get v b = some c

theorem ConstLe.refl (a : ConstEnv) : ConstLe a a := fun _ _ h => h

theorem ConstLe.trans {a b c : ConstEnv} (h₁ : ConstLe a b) (h₂ : ConstLe b c) : ConstLe a c := fun v k h => h₂ v k (h₁ v k h)

/-- Each constant of a table has the type of its variable. -/
def ConstTyped (e : ConstEnv) : Prop := ∀ x ∈ e, x.1.typ = .imm x.2.width

private def constValues (e : ConstEnv) : Env := e.map fun x => (x.1, .bits (BitVec.ofNat x.2.width x.2.value))

private theorem lookup_constValues (e : ConstEnv) (v : Var) :
    lookup (constValues e) v = match Assoc.get v e with
      | some c => .ok (.bits (BitVec.ofNat c.width c.value))
      | none => .error s!"unbound variable {v.name}" := by
  induction e with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k, c⟩ := x
    by_cases hk : v = k
    · subst hk
      simp [constValues, lookup, Assoc.get]
    · have h1 : (k == v) = false := by simpa using fun h : k = v => hk h.symm
      have h2 : (v == k) = false := by simpa using hk
      simp only [constValues, List.map_cons, lookup, List.find?_cons, h1, Assoc.get, List.lookup_cons, h2] at ih ⊢
      exact ih

private theorem constValues_typed {e : ConstEnv} (h : ConstTyped e) : Bap.Proofs.Bil.WellTypedEnv (constValues e) := by
  intro b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
  exact (h x hx).symm

private abbrev sub (e : ConstEnv) (x : Exp) : Exp := Bil.substitute (replacements e) x

private theorem eval_sub (e : ConstEnv) (x : Exp) : evalExp [] (sub e x) = evalExp (constValues e) x := by
  apply Bap.Proofs.Bil.evalExp_substitute
  intro v _
  rw [get_replacements, lookup_constValues]
  cases Assoc.get v e <;> rfl

private theorem eval_sub_above {a b : ConstEnv} (h : ConstLe a b) (x : Exp) : evalExp (constValues b) (sub a x) = evalExp (constValues b) x := by
  apply Bap.Proofs.Bil.evalExp_substitute
  intro v _
  rw [get_replacements]
  cases hg : Assoc.get v a with
  | none => rfl
  | some c =>
    rw [lookup_constValues, h v c hg]
    rfl

private theorem constValues_extends {a b : ConstEnv} (h : ConstLe a b) : Bap.Proofs.Bil.Extends (constValues a) (constValues b) := by
  intro v r hr
  rw [lookup_constValues] at hr ⊢
  cases hg : Assoc.get v a with
  | none =>
    rw [hg] at hr
    cases hr
  | some c =>
    rw [hg] at hr
    rw [h v c hg]
    exact hr

private theorem simp_fold {x : Exp} {w} {v : BitVec w} (h : evalExp [] x = .ok (.bits v)) : simplifyExp x = .int v := by
  rw [simplifyExp.eq_def, h]

/-- Either side folding settles it. Neither is what's left, where the two are of the same form. -/
private theorem rel_wrap {a b : ConstEnv} (hle : ConstLe a b) (hb : ConstTyped b) (x : Exp)
    (hnf : (∀ w (v : BitVec w), evalExp [] (sub a x) ≠ .ok (.bits v)) → (∀ w (v : BitVec w), evalExp [] (sub b x) ≠ .ok (.bits v)) →
      SimpRel (simplifyExp (sub a x)) (simplifyExp (sub b x))) :
    SimpRel (simplifyExp (sub a x)) (simplifyExp (sub b x)) := by
  by_cases h₁ : ∀ w (v : BitVec w), evalExp [] (sub a x) ≠ .ok (.bits v)
  · by_cases h₂ : ∀ w (v : BitVec w), evalExp [] (sub b x) ≠ .ok (.bits v)
    · exact hnf h₁ h₂
    · obtain ⟨w, hw⟩ := Classical.not_forall.1 h₂
      obtain ⟨u, hu⟩ := Classical.not_forall.1 hw
      have hu := Classical.not_not.1 hu
      rw [simp_fold hu]
      have hev : evalExp (constValues b) (simplifyExp (sub a x)) = .ok (.bits u) := by
        apply Bap.Proofs.Bil.evalExp_simplifyExp
        rw [eval_sub_above hle, ← eval_sub, hu]
      refine ⟨fun v h => ?_, fun τ h => ?_, fun h => by simp [hasUnknown] at h⟩
      · rw [h] at hev
        have hv : Value.bits v = Value.bits u := by
          have : evalExp (constValues b) (.int v) = .ok (.bits v) := rfl
          rw [this] at hev
          exact Except.ok.inj hev
        cases hv
        rfl
      · have ht := Bap.Proofs.Bil.evalExp_type_sound (constValues_typed hb) _ h hev
        subst ht
        exact infer_int u (has_bits h)
  · obtain ⟨w, hw⟩ := Classical.not_forall.1 h₁
    obtain ⟨v, hv⟩ := Classical.not_forall.1 hw
    have hv := Classical.not_not.1 hv
    have hv' : evalExp [] (sub b x) = .ok (.bits v) := by
      rw [eval_sub] at hv ⊢
      exact Bap.Proofs.Bil.evalExp_extends (constValues_extends hle) _ hv
    rw [simp_fold hv, simp_fold hv']
    exact SimpRel.refl _

private theorem sub_let (e : ConstEnv) (x : Var) (v b : Exp) :
    sub e (.letIn x v b) = .letIn x (sub e v) (sub (Assoc.remove x e) b) := by
  have hinner : (replacements e).filter (fun r => r.1 != x) = replacements (Assoc.remove x e) := by
    simp only [replacements, Assoc.remove, List.filter_map]
    rfl
  have hany : ((replacements e).filter (fun r => r.1 != x)).any (fun r => occursFree x r.2 && occursFree r.1 b) = false := by
    rw [List.any_eq_false]
    intro r hr
    obtain ⟨⟨k, c⟩, _, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hr).1
    simp [Constant.toExp, occursFree]
  rw [hinner] at hany
  simp only [sub, Bil.substitute, hinner, hany, Bool.false_eq_true, ↓reduceIte]

theorem get_filter_key {β : Type} (p : Var → Bool) (e : List (Var × β)) (v : Var) :
    Assoc.get v (e.filter fun x => p x.1) = if p v then Assoc.get v e else none := by
  induction e with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨k, c⟩ := x
    simp only [Assoc.get] at ih ⊢
    rw [List.filter_cons]
    by_cases hp : p k = true
    · simp only [hp, ↓reduceIte, List.lookup_cons]
      by_cases hk : v = k
      · subst hk
        simp [hp]
      · have h2 : (v == k) = false := by simpa using hk
        simp only [h2]
        exact ih
    · have hp' : p k = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ↓reduceIte, List.lookup_cons]
      by_cases hk : v = k
      · subst hk
        simp only [hp', Bool.false_eq_true, ↓reduceIte] at ih ⊢
        exact ih
      · have h2 : (v == k) = false := by simpa using hk
        simp only [h2]
        exact ih

theorem get_remove {β : Type} (x v : Var) (e : List (Var × β)) :
    Assoc.get v (Assoc.remove x e) = if v = x then none else Assoc.get v e := by
  have := get_filter_key (fun k => k != x) e v
  by_cases hv : v = x <;> simp_all [Assoc.remove]

private theorem ConstLe.remove {a b : ConstEnv} (h : ConstLe a b) (x : Var) : ConstLe (Assoc.remove x a) (Assoc.remove x b) := by
  intro v c hg
  by_cases hv : v = x
  · subst hv
    simp [get_remove] at hg
  · rw [get_remove] at hg ⊢
    simp only [hv, ite_false] at hg ⊢
    exact h v c hg

private theorem ConstTyped.remove {a : ConstEnv} (h : ConstTyped a) (x : Var) : ConstTyped (Assoc.remove x a) :=
  fun e he => h e (List.mem_filter.1 he).1

/-- Knowing more constants never loses what the rewrite found: a literal stays that literal, what has a type keeps it, and no
`unknown` comes back. -/
theorem simplify_mono (x : Exp) {a b : ConstEnv} (hle : ConstLe a b) (hb : ConstTyped b) :
    SimpRel (simplifyExp (sub a x)) (simplifyExp (sub b x)) := by
  induction x generalizing a b with
  | int v => exact SimpRel.refl _
  | unknown m t => exact SimpRel.refl _
  | var x =>
    apply rel_wrap hle hb
    intro _ h₂
    have hsub : ∀ e, sub e (.var x) = ((Assoc.get x e).map Constant.toExp).getD (.var x) := fun e => by
      simp only [sub, Bil.substitute, get_replacements]
    cases hg : Assoc.get x a with
    | some c => rw [hsub, hsub, hg, hle x c hg]; exact SimpRel.refl _
    | none =>
      cases hg' : Assoc.get x b with
      | none => rw [hsub, hsub, hg, hg']; exact SimpRel.refl _
      | some c =>
        rw [hsub, hg'] at h₂
        exact absurd rfl (h₂ _ (BitVec.ofNat c.width c.value))
  | load m a' e n ihm iha =>
    apply rel_wrap hle hb
    intro h₁ h₂
    rw [simplifyExp_of_not_bits h₁, simplifyExp_of_not_bits h₂]
    exact rel_load (ihm hle hb) (iha hle hb)
  | store m a' v e n ihm iha ihv =>
    apply rel_wrap hle hb
    intro h₁ h₂
    rw [simplifyExp_of_not_bits h₁, simplifyExp_of_not_bits h₂]
    exact rel_store (ihm hle hb) (iha hle hb) (ihv hle hb)
  | bin op l r ihl ihr =>
    apply rel_wrap hle hb
    intro h₁ h₂
    rw [simplifyExp_of_not_bits h₁, simplifyExp_of_not_bits h₂]
    exact rel_binRule (ihl hle hb) (ihr hle hb)
  | un op v ih =>
    apply rel_wrap hle hb
    intro h₁ h₂
    rw [simplifyExp_of_not_bits h₁, simplifyExp_of_not_bits h₂]
    exact rel_un (ih hle hb)
  | cast k w v ih =>
    apply rel_wrap hle hb
    intro h₁ h₂
    rw [simplifyExp_of_not_bits h₁, simplifyExp_of_not_bits h₂]
    exact rel_cast (ih hle hb)
  | letIn x v body ihv ihb =>
    apply rel_wrap hle hb
    intro h₁ h₂
    rw [sub_let] at h₁ h₂ ⊢
    rw [sub_let, simplifyExp_of_not_bits h₁, simplifyExp_of_not_bits h₂]
    exact rel_let (ihv hle hb) (ihb (hle.remove x) (ConstTyped.remove hb x))
  | ite c y n ihc ihy ihn =>
    apply rel_wrap hle hb
    intro h₁ h₂
    rw [simplifyExp_of_not_bits h₁, simplifyExp_of_not_bits h₂]
    exact rel_iteRule (ihc hle hb) (ihy hle hb) (ihn hle hb)
  | extract hi lo v ih =>
    apply rel_wrap hle hb
    intro h₁ h₂
    rw [simplifyExp_of_not_bits h₁, simplifyExp_of_not_bits h₂]
    exact rel_extract (ih hle hb)
  | concat l r ihl ihr =>
    apply rel_wrap hle hb
    intro h₁ h₂
    rw [simplifyExp_of_not_bits h₁, simplifyExp_of_not_bits h₂]
    exact rel_concat (ihl hle hb) (ihr hle hb)

/-! ### A block's constants -/

private theorem get_constStep (e : ConstEnv) (x v : Var) (rhs : Exp) :
    Assoc.get v (constStep e x rhs) = if v = x then Constant.ofDef x rhs else Assoc.get v e := by
  simp only [constStep]
  split
  · rename_i c hc
    rw [get_put, hc]
  · rename_i hc
    rw [removeConst_eq, get_remove, hc]

private theorem ofDef_rel {s s' : Exp} (h : SimpRel s s') (x : Var) {c : Constant} (hc : Constant.ofDef x s = some c) :
    Constant.ofDef x s' = some c := by
  cases s with
  | int v =>
    rw [h.lit v rfl]
    exact hc
  | _ => simp [Constant.ofDef, Constant.ofExp] at hc

private theorem ofDef_typed {x : Var} {s : Exp} {c : Constant} (hc : Constant.ofDef x s = some c) : x.typ = .imm c.width := by
  simp only [Constant.ofDef] at hc
  split at hc
  · split at hc
    · rename_i h
      cases hc
      exact h
    · cases hc
  · cases hc

/-- What the tables of the analysis all are. -/
structure ConstWF (e : ConstEnv) : Prop where
  nodup : (e.map Prod.fst).Nodup
  typed : ConstTyped e

theorem ConstWF.nil : ConstWF [] := ⟨by simp, by simp [ConstTyped]⟩

private theorem nodup_filter_keys {e : ConstEnv} (h : (e.map Prod.fst).Nodup) (p : Var × Constant → Bool) :
    ((e.filter p).map Prod.fst).Nodup :=
  List.Pairwise.sublist (List.Sublist.map _ List.filter_sublist) h

theorem ConstWF.filter {e : ConstEnv} (h : ConstWF e) (p : Var × Constant → Bool) : ConstWF (e.filter p) :=
  ⟨nodup_filter_keys h.nodup p, fun x hx => h.typed x (List.mem_filter.1 hx).1⟩

private theorem constStep_wf {e : ConstEnv} (h : ConstWF e) (x : Var) (rhs : Exp) : ConstWF (constStep e x rhs) := by
  simp only [constStep]
  split
  · rename_i c hc
    refine ⟨?_, ?_⟩
    · simp only [Assoc.put, List.map_cons, List.nodup_cons]
      refine ⟨?_, nodup_filter_keys h.nodup _⟩
      intro hm
      obtain ⟨y, hy, hk⟩ := List.mem_map.1 hm
      have := (List.mem_filter.1 hy).2
      simp [hk] at this
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ofDef_typed hc
      · exact h.typed y (List.mem_filter.1 hy).1
  · rw [removeConst_eq]
    exact h.filter _

private abbrev stepC (e : ConstEnv) (d : Def) : ConstEnv := constStep e d.var (simplifyExp (sub e d.rhs))

private theorem stepC_mono {a b : ConstEnv} (hle : ConstLe a b) (hb : ConstTyped b) (d : Def) : ConstLe (stepC a d) (stepC b d) := by
  intro v c hg
  rw [get_constStep] at hg ⊢
  split
  · rename_i hv
    rw [ite_eq_left hv] at hg
    exact ofDef_rel (simplify_mono d.rhs hle hb) _ hg
  · rename_i hv
    rw [ite_eq_right hv] at hg
    exact hle v c hg

/-- The constants at the end of a block, given those at its entry, whatever `propagateBlock` is written as. -/
private def exitOf (blk : Blk) (e : ConstEnv) : ConstEnv :=
  blk.defs.foldl stepC (e.filter fun x => decide (x.1 ∉ blk.phis.map Phi.var))

private theorem exit_eq (blk : Blk) (e : ConstEnv) : (propagateBlock blk e).2 = exitOf blk e := by
  rw [propagateExit_eq]
  have hf : (if (blk.phis.map Phi.var).isEmpty then e else e.filter fun x => decide (x.1 ∉ blk.phis.map Phi.var)) =
      e.filter fun x => decide (x.1 ∉ blk.phis.map Phi.var) := by
    split
    · rename_i h
      have hnil : blk.phis.map Phi.var = [] := by simpa using h
      rw [hnil]
      exact (List.filter_eq_self.2 (by simp)).symm
    · rfl
  simp only [propagateExit, hf, exitOf, substConst_eq]

private theorem foldC_mono (defs : List Def) {a b : ConstEnv} (hle : ConstLe a b) (hb : ConstWF b) :
    ConstLe (defs.foldl stepC a) (defs.foldl stepC b) := by
  induction defs generalizing a b with
  | nil => exact hle
  | cons d ds ih => exact ih (stepC_mono hle hb.typed d) (constStep_wf hb _ _)

private theorem ConstLe.filter_keys {a b : ConstEnv} (h : ConstLe a b) (p : Var → Bool) :
    ConstLe (a.filter fun x => p x.1) (b.filter fun x => p x.1) := by
  intro v c hg
  rw [get_filter_key] at hg ⊢
  split
  · rename_i hp
    rw [ite_eq_left hp] at hg
    exact h v c hg
  · rename_i hp
    rw [ite_eq_right hp] at hg
    cases hg

private theorem exitOf_mono (blk : Blk) {a b : ConstEnv} (hle : ConstLe a b) (hb : ConstWF b) : ConstLe (exitOf blk a) (exitOf blk b) :=
  foldC_mono _ (hle.filter_keys fun k => decide (k ∉ blk.phis.map Phi.var)) (hb.filter _)

private theorem foldC_wf (defs : List Def) {a : ConstEnv} (h : ConstWF a) : ConstWF (defs.foldl stepC a) := by
  induction defs generalizing a with
  | nil => exact h
  | cons d ds ih => exact ih (constStep_wf h _ _)

private theorem exitOf_wf (blk : Blk) {a : ConstEnv} (h : ConstWF a) : ConstWF (exitOf blk a) := foldC_wf _ (h.filter _)

/-- Which variables have constants, as a set: every table of the analysis is of these. -/
def KeysIn (U : List Var) (e : ConstEnv) : Prop := ∀ v c, Assoc.get v e = some c → v ∈ U

private theorem foldC_keys {U : List Var} (defs : List Def) (hU : ∀ d ∈ defs, d.var ∈ U) {a : ConstEnv} (h : KeysIn U a) :
    KeysIn U (defs.foldl stepC a) := by
  induction defs generalizing a with
  | nil => exact h
  | cons d ds ih =>
    refine ih (fun d' hd' => hU d' (List.mem_cons_of_mem _ hd')) fun v c hg => ?_
    rw [get_constStep] at hg
    split at hg
    · rename_i hv
      subst hv
      exact hU d (List.mem_cons_self ..)
    · exact h v c hg

private theorem KeysIn.filter_keys {U : List Var} {a : ConstEnv} (h : KeysIn U a) (p : Var → Bool) : KeysIn U (a.filter fun x => p x.1) := by
  intro v c hg
  rw [get_filter_key] at hg
  split at hg
  · exact h v c hg
  · cases hg

/-- What the analysis says of a block's end. -/
private def transfer (reads : List (Tid × List Var)) (blk : Blk) (e : ConstEnv) : ConstEnv :=
  keepReads reads blk.tid (exitOf blk e)

private theorem transfer_eq (reads : List (Tid × List Var)) (blk : Blk) (e : ConstEnv) :
    keepReads reads blk.tid (propagateBlock blk e).2 = transfer reads blk e := by
  rw [exit_eq]
  rfl

private theorem keep_eq (reads : List (Tid × List Var)) (t : Tid) (e : ConstEnv) :
    keepReads reads t e = e.filter fun x => (fun k => decide (k ∈ (Assoc.get t reads).getD [])) x.1 := rfl

/-- A block's exit constants grow with its entry constants. -/
theorem transfer_grows (reads : List (Tid × List Var)) (blk : Blk) {a b : ConstEnv} (hle : ConstLe a b) (hb : ConstWF b) :
    ConstLe (transfer reads blk a) (transfer reads blk b) := by
  simp only [transfer, keep_eq]
  exact (exitOf_mono blk hle hb).filter_keys fun k => decide (k ∈ (Assoc.get blk.tid reads).getD [])

private theorem transfer_wf (reads : List (Tid × List Var)) (blk : Blk) {a : ConstEnv} (h : ConstWF a) : ConstWF (transfer reads blk a) := by
  simp only [transfer, keep_eq]
  exact (exitOf_wf blk h).filter _

private theorem transfer_keys {U : List Var} (reads : List (Tid × List Var)) (blk : Blk) (hU : ∀ d ∈ blk.defs, d.var ∈ U) {a : ConstEnv}
    (h : KeysIn U a) : KeysIn U (transfer reads blk a) := by
  simp only [transfer, keep_eq, exitOf]
  exact KeysIn.filter_keys (foldC_keys _ hU (KeysIn.filter_keys h fun k => decide (k ∉ blk.phis.map Phi.var)))
    fun k => decide (k ∈ (Assoc.get blk.tid reads).getD [])

/-! ### What the blocks before say of a block's entry -/

private theorem get_join {l : ConstEnv} (hl : (l.map Prod.fst).Nodup) (r : ConstEnv) (v : Var) (c : Constant) :
    Assoc.get v (joinEnv l r) = some c ↔ Assoc.get v l = some c ∧ Assoc.get v r = some c := by
  induction l with
  | nil => simp [joinEnv]
  | cons x xs ih =>
    obtain ⟨k, d⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hl
    have hj : joinEnv ((k, d) :: xs) r =
        if Assoc.get k r = some d then (k, d) :: joinEnv xs r else joinEnv xs r := by
      simp only [joinEnv, List.filter_cons, decide_eq_true_eq]
    have hg0 : ∀ c', Assoc.get k xs ≠ some c' := fun c' hg => hl.1 (List.mem_map.2 ⟨(k, c'), get_mem_env' hg, rfl⟩)
    have hj0 : ∀ c', Assoc.get k (joinEnv xs r) ≠ some c' := fun c' hg => by
      have hm := get_mem_env' hg
      exact hl.1 (List.mem_map.2 ⟨(k, c'), (List.mem_filter.1 hm).1, rfl⟩)
    rw [hj]
    by_cases hv : v = k
    · subst hv
      have hcons : ∀ tail : ConstEnv, Assoc.get v ((v, d) :: tail) = some d := fun _ => by simp [Assoc.get]
      rw [hcons]
      split
      · rename_i hr
        rw [hcons]
        constructor
        · rintro h
          cases h
          exact ⟨rfl, hr⟩
        · rintro ⟨h, _⟩
          exact h
      · rename_i hr
        constructor
        · intro h
          exact absurd h (hj0 c)
        · rintro ⟨h, h'⟩
          cases h
          exact absurd h' hr
    · have hb : (v == k) = false := by simpa using hv
      have hcons : ∀ tail : ConstEnv, Assoc.get v ((k, d) :: tail) = Assoc.get v tail := fun _ => by simp [Assoc.get, List.lookup_cons, hb]
      rw [hcons]
      split
      · rw [hcons]
        exact ih hl.2
      · exact ih hl.2

private theorem join_nodup {l : ConstEnv} (hl : (l.map Prod.fst).Nodup) (r : ConstEnv) : ((joinEnv l r).map Prod.fst).Nodup :=
  nodup_filter_keys hl _

private theorem get_fold {first : ConstEnv} {rest : List ConstEnv} (hf : (first.map Prod.fst).Nodup) (v : Var) (c : Constant) :
    Assoc.get v (rest.foldl joinEnv first) = some c ↔ ∀ e ∈ first :: rest, Assoc.get v e = some c := by
  induction rest generalizing first with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons]
    rw [ih (join_nodup hf r)]
    simp only [List.mem_cons, forall_eq_or_imp]
    rw [get_join hf, and_assoc]

private abbrev AllWF (exits : ExitEnvs) : Prop := ∀ t e, Assoc.get t exits = some e → ConstWF e

private theorem fold_wf {first : ConstEnv} {rest : List ConstEnv} (hf : ConstWF first) : ConstWF (rest.foldl joinEnv first) := by
  induction rest generalizing first with
  | nil => exact hf
  | cons r rs ih => exact ih (hf.filter _)

/-- A table at a block's entry says what all the tables so far of the blocks before it say. -/
private theorem entry_get {cfg : Cfg} {exits : ExitEnvs} (hw : AllWF exits) (t : Tid) (v : Var) (c : Constant) :
    Assoc.get v (entryEnv cfg exits t) = some c ↔
      t ≠ cfg.start ∧ (∃ p ∈ cfg.predecessors t, ∃ e, Assoc.get p exits = some e) ∧
        ∀ p ∈ cfg.predecessors t, ∀ e, Assoc.get p exits = some e → Assoc.get v e = some c := by
  have heq : entryEnv cfg exits t = if t = cfg.start then [] else
      match (cfg.predecessors t).filterMap fun pred => Assoc.get pred exits with
      | [] => []
      | first :: rest => rest.foldl joinEnv first := rfl
  rw [heq]
  by_cases ht : t = cfg.start
  · simp [ht]
  · simp only [ht, ite_false]
    have hmem : ∀ e, e ∈ (cfg.predecessors t).filterMap (fun pred => Assoc.get pred exits) ↔
        ∃ p ∈ cfg.predecessors t, Assoc.get p exits = some e := fun e => List.mem_filterMap
    split
    · rename_i hnil
      simp only [Assoc.get_nil, reduceCtorEq, false_iff, not_and]
      rintro _ ⟨p, hp, e, he⟩
      have := (hmem e).2 ⟨p, hp, he⟩
      rw [hnil] at this
      cases this
    · rename_i first rest hl
      have hf : ConstWF first := by
        have : first ∈ (cfg.predecessors t).filterMap (fun pred => Assoc.get pred exits) := by simp [hl]
        obtain ⟨p, _, he⟩ := (hmem _).1 this
        exact hw _ _ he
      rw [get_fold hf.nodup]
      constructor
      · intro h
        refine ⟨fun h' => ht h', ?_, ?_⟩
        · have : first ∈ (cfg.predecessors t).filterMap (fun pred => Assoc.get pred exits) := by simp [hl]
          obtain ⟨p, hp, he⟩ := (hmem _).1 this
          exact ⟨p, hp, _, he⟩
        · intro p hp e he
          have : e ∈ first :: rest := by
            rw [← hl]
            exact (hmem _).2 ⟨p, hp, he⟩
          exact h e this
      · rintro ⟨_, _, h⟩ e he
        rw [← hl] at he
        obtain ⟨p, hp, hge⟩ := (hmem _).1 he
        exact h p hp e hge

private theorem entry_wf {cfg : Cfg} {exits : ExitEnvs} (hw : AllWF exits) (t : Tid) : ConstWF (entryEnv cfg exits t) := by
  have heq : entryEnv cfg exits t = if t = cfg.start then [] else
      match (cfg.predecessors t).filterMap fun pred => Assoc.get pred exits with
      | [] => []
      | first :: rest => rest.foldl joinEnv first := rfl
  rw [heq]
  split
  · exact ConstWF.nil
  · split
    · exact ConstWF.nil
    · rename_i first rest hl
      apply fold_wf
      have : first ∈ (cfg.predecessors t).filterMap (fun pred => Assoc.get pred exits) := by simp [hl]
      obtain ⟨p, _, he⟩ := List.mem_filterMap.1 this
      exact hw _ _ he

private theorem entry_keys {cfg : Cfg} {exits : ExitEnvs} {U : List Var} (hw : AllWF exits) (hk : ∀ t e, Assoc.get t exits = some e → KeysIn U e)
    (t : Tid) : KeysIn U (entryEnv cfg exits t) := by
  intro v c hg
  obtain ⟨_, ⟨p, _, e, he⟩, h⟩ := (entry_get hw t v c).1 hg
  exact hk p e he v c (h p ‹_› e he)

/-- Entry tables grow with the tables before them, if the larger knows a block before. -/
private theorem entry_le {cfg : Cfg} {A B : ExitEnvs} (hA : AllWF A) (hB : AllWF B) {t : Tid}
    (hfed : t = cfg.start ∨ ∃ p ∈ cfg.predecessors t, ∃ e, Assoc.get p B = some e)
    (hsub : ∀ p ∈ cfg.predecessors t, ∀ e, Assoc.get p B = some e → ∃ e', Assoc.get p A = some e' ∧ ConstLe e' e) :
    ConstLe (entryEnv cfg A t) (entryEnv cfg B t) := by
  intro v c hg
  obtain ⟨hs, _, h⟩ := (entry_get hA t v c).1 hg
  rw [entry_get hB]
  refine ⟨hs, ?_, ?_⟩
  · rcases hfed with hs' | hp
    · exact absurd hs' hs
    · exact hp
  · intro p hp e he
    obtain ⟨e', he', hle⟩ := hsub p hp e he
    exact hle v c (h p hp e' he')

private theorem entry_congr {cfg : Cfg} {A B : ExitEnvs} {t : Tid} (h : ∀ p ∈ cfg.predecessors t, Assoc.get p A = Assoc.get p B) :
    entryEnv cfg A t = entryEnv cfg B t := by
  have heq : ∀ X, entryEnv cfg X t = if t = cfg.start then [] else
      match (cfg.predecessors t).filterMap fun pred => Assoc.get pred X with
      | [] => []
      | first :: rest => rest.foldl joinEnv first := fun _ => rfl
  have key : ∀ l : List Tid, (∀ p ∈ l, Assoc.get p A = Assoc.get p B) →
      l.filterMap (fun pred => Assoc.get pred A) = l.filterMap (fun pred => Assoc.get pred B) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons x xs ih =>
      intro hl
      simp only [List.filterMap_cons, hl x (List.mem_cons_self ..), ih fun p hp => hl p (List.mem_cons_of_mem _ hp)]
  rw [heq, heq, key _ h]

/-! ### The worklist -/

private theorem mem_predecessors_cfg {cfg : Cfg} (a b : Tid) : a ∈ cfg.predecessors b ↔ (a, b) ∈ cfg.graph.edges :=
  Bap.Proofs.Graph.mem_predecessors ..

/-- Two tables say the same of every variable. -/
def SameC (a b : ConstEnv) : Prop := ∀ v, Assoc.get v a = Assoc.get v b

private theorem sameC_of_same {a b : ConstEnv} (h : sameConsts a b = true) : SameC a b := by
  have hd : sameConsts a b = (a == b || (a.all (fun entry => Assoc.get entry.1 b == some entry.2) &&
      b.all (fun entry => Assoc.get entry.1 a == some entry.2))) := rfl
  rw [hd] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with rfl | ⟨h₁, h₂⟩
  · intro _; rfl
  · intro v
    have hsub : ∀ (x y : ConstEnv), (x.all fun entry => Assoc.get entry.1 y == some entry.2) = true →
        ∀ c, Assoc.get v x = some c → Assoc.get v y = some c := by
      intro x y hxy c hg
      have := List.all_eq_true.1 hxy _ (get_mem_env' hg)
      simpa using this
    cases hg : Assoc.get v a with
    | some c => rw [hsub a b h₁ c hg]
    | none =>
      cases hg' : Assoc.get v b with
      | none => rfl
      | some c =>
        rw [hsub b a h₂ c hg'] at hg
        cases hg

private theorem get_of_mem {e : ConstEnv} (h : (e.map Prod.fst).Nodup) {x : Var × Constant} (hx : x ∈ e) : Assoc.get x.1 e = some x.2 := by
  induction e with
  | nil => cases hx
  | cons y ys ih =>
    obtain ⟨k, c⟩ := y
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hx with rfl | hm
    · simp [Assoc.get]
    · have hne : x.1 ≠ k := fun he => h.1 (List.mem_map.2 ⟨x, hm, he⟩)
      have hb : (x.1 == k) = false := by simpa using hne
      simp only [Assoc.get, List.lookup_cons, hb]
      exact ih h.2 hm

private theorem same_of_sameC {a b : ConstEnv} (ha : ConstWF a) (hb : ConstWF b) (h : SameC a b) : sameConsts a b = true := by
  have hd : sameConsts a b = (a == b || (a.all (fun entry => Assoc.get entry.1 b == some entry.2) &&
      b.all (fun entry => Assoc.get entry.1 a == some entry.2))) := rfl
  rw [hd]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine Or.inr ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [← h, get_of_mem ha.nodup hx]
  · rw [h, get_of_mem hb.nodup hx]

/-- What holds of the worklist's state between steps. -/
structure Inv (cfg : Cfg) (reads : List (Tid × List Var)) (U : List Var) (exits : ExitEnvs) (work : List Tid) : Prop where
  wf : ∀ t e, Assoc.get t exits = some e → ConstWF e ∧ KeysIn U e ∧ ∃ blk, cfg.block t = some blk
  fed : ∀ t e, Assoc.get t exits = some e → t = cfg.start ∨ ∃ p ∈ cfg.predecessors t, ∃ e', Assoc.get p exits = some e'
  workFed : ∀ t ∈ work, t = cfg.start ∨ ∃ p ∈ cfg.predecessors t, ∃ e', Assoc.get p exits = some e'
  drop : ∀ t blk e, cfg.block t = some blk → Assoc.get t exits = some e → ConstLe (transfer reads blk (entryEnv cfg exits t)) e
  pend : ∀ t blk e, cfg.block t = some blk → Assoc.get t exits = some e → t ∈ work ∨ SameC e (transfer reads blk (entryEnv cfg exits t))
  close : ∀ t e, Assoc.get t exits = some e → ∀ s ∈ cfg.successors t, (∃ e', Assoc.get s exits = some e') ∨ s ∈ work ∨ cfg.block s = none
  start : (∃ e, Assoc.get cfg.start exits = some e) ∨ cfg.start ∈ work ∨ cfg.block cfg.start = none

private theorem Inv.allWF {cfg : Cfg} {reads : List (Tid × List Var)} {U : List Var} {exits : ExitEnvs} {work : List Tid}
    (h : Inv cfg reads U exits work) : AllWF exits := fun t e he => (h.wf t e he).1

private theorem Inv.init (cfg : Cfg) (reads : List (Tid × List Var)) (U : List Var) : Inv cfg reads U [] [cfg.start] where
  wf := by simp
  fed := by simp
  workFed := by simp
  drop := by simp
  pend := by simp
  close := by simp
  start := by simp

private theorem Inv.skip {cfg : Cfg} {reads : List (Tid × List Var)} {U : List Var} {exits : ExitEnvs} {t : Tid} {work : List Tid}
    (h : Inv cfg reads U exits (t :: work)) (hb : cfg.block t = none) : Inv cfg reads U exits work where
  wf := h.wf
  fed := h.fed
  workFed := fun t' ht' => h.workFed t' (List.mem_cons_of_mem _ ht')
  drop := h.drop
  pend := fun t' blk e hb' he => by
    rcases h.pend t' blk e hb' he with hm | hs
    · rcases List.mem_cons.1 hm with rfl | hm
      · rw [hb] at hb'
        cases hb'
      · exact Or.inl hm
    · exact Or.inr hs
  close := fun t' e he s hs => by
    rcases h.close t' e he s hs with hk | hm | hn
    · exact Or.inl hk
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact Or.inr (Or.inr hb)
      · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hn)
  start := by
    rcases h.start with hk | hm | hn
    · exact Or.inl hk
    · rcases List.mem_cons.1 hm with he | hm
      · rw [he]
        exact Or.inr (Or.inr hb)
      · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hn)

private theorem settled_some {k : Option ConstEnv} {e : ConstEnv} (h : settled k e = true) : ∃ old, k = some old ∧ SameC old e := by
  cases k with
  | none => cases h
  | some old => exact ⟨old, rfl, sameC_of_same h⟩

private theorem Inv.settle {cfg : Cfg} {reads : List (Tid × List Var)} {U : List Var} {exits : ExitEnvs} {t : Tid} {work : List Tid}
    (h : Inv cfg reads U exits (t :: work)) {blk : Blk} (hb : cfg.block t = some blk)
    (hs : settled (Assoc.get t exits) (transfer reads blk (entryEnv cfg exits t)) = true) : Inv cfg reads U exits work := by
  obtain ⟨old, hold, hsame⟩ := settled_some hs
  exact {
    wf := h.wf
    fed := h.fed
    workFed := fun t' ht' => h.workFed t' (List.mem_cons_of_mem _ ht')
    drop := h.drop
    pend := fun t' blk' e hb' he => by
      by_cases ht : t' = t
      · subst ht
        rw [hb] at hb'
        cases hb'
        rw [hold] at he
        cases he
        exact Or.inr hsame
      · rcases h.pend t' blk' e hb' he with hm | hs'
        · exact Or.inl ((List.mem_cons.1 hm).resolve_left ht)
        · exact Or.inr hs'
    close := fun t' e he s hs' => by
      rcases h.close t' e he s hs' with hk | hm | hn
      · exact Or.inl hk
      · rcases List.mem_cons.1 hm with rfl | hm
        · exact Or.inl ⟨old, hold⟩
        · exact Or.inr (Or.inl hm)
      · exact Or.inr (Or.inr hn)
    start := by
      rcases h.start with hk | hm | hn
      · exact Or.inl hk
      · rcases List.mem_cons.1 hm with he | hm
        · rw [he]
          exact Or.inl ⟨old, hold⟩
        · exact Or.inr (Or.inl hm)
      · exact Or.inr (Or.inr hn)
  }

private theorem pred_of_succ {cfg : Cfg} {a b : Tid} (h : b ∈ cfg.successors a) : a ∈ cfg.predecessors b :=
  (mem_predecessors_cfg a b).2 ((Bap.Graph.successors_mem cfg.graph a b).1 h)

private theorem succ_of_pred {cfg : Cfg} {a b : Tid} (h : a ∈ cfg.predecessors b) : b ∈ cfg.successors a :=
  (Bap.Graph.successors_mem cfg.graph a b).2 ((mem_predecessors_cfg a b).1 h)

private theorem Inv.change {cfg : Cfg} {reads : List (Tid × List Var)} {U : List Var} {exits : ExitEnvs} {t : Tid} {work : List Tid}
    (h : Inv cfg reads U exits (t :: work)) {blk : Blk} (hb : cfg.block t = some blk) (hU : ∀ d ∈ blk.defs, d.var ∈ U) :
    Inv cfg reads U (Assoc.put t (transfer reads blk (entryEnv cfg exits t)) exits) (work ++ cfg.successors t) := by
  generalize henv : transfer reads blk (entryEnv cfg exits t) = env
  have hw := h.allWF
  have hget : ∀ p, Assoc.get p (Assoc.put t env exits) = if p = t then some env else Assoc.get p exits := fun p => get_put p t env exits
  have hself : Assoc.get t (Assoc.put t env exits) = some env := by simp [hget]
  have hother : ∀ {p}, p ≠ t → Assoc.get p (Assoc.put t env exits) = Assoc.get p exits := fun {p} hp => by simp [hget, hp]
  have hgrow : ∀ {p e}, Assoc.get p exits = some e → ∃ e', Assoc.get p (Assoc.put t env exits) = some e' := fun {p e} he => by
    by_cases hp : p = t
    · subst hp
      exact ⟨env, hself⟩
    · exact ⟨e, by rw [hother hp, he]⟩
  have henvwf : ConstWF env := henv ▸ transfer_wf reads blk (entry_wf hw t)
  have hkeys : ∀ t' e, Assoc.get t' exits = some e → KeysIn U e := fun t' e he => (h.wf t' e he).2.1
  have henvk : KeysIn U env := henv ▸ transfer_keys reads blk hU (entry_keys hw hkeys t)
  have hw' : AllWF (Assoc.put t env exits) := fun p e he => by
    by_cases hp : p = t
    · subst hp
      rw [hself] at he
      cases he
      exact henvwf
    · rw [hother hp] at he
      exact hw p e he
  have hlow : ∀ {t'}, (t' = cfg.start ∨ ∃ p ∈ cfg.predecessors t', ∃ e', Assoc.get p exits = some e') →
      ConstLe (entryEnv cfg (Assoc.put t env exits) t') (entryEnv cfg exits t') := fun {t'} hf => by
    apply entry_le hw' hw hf
    intro p _ e he
    by_cases hp : p = t
    · subst hp
      exact ⟨env, hself, henv ▸ h.drop p blk e hb he⟩
    · exact ⟨e, by rw [hother hp, he], ConstLe.refl _⟩
  have hfedT := h.workFed t (List.mem_cons_self ..)
  have hsame : ∀ {t'}, t' ∉ cfg.successors t → entryEnv cfg (Assoc.put t env exits) t' = entryEnv cfg exits t' := fun {t'} hs =>
    entry_congr fun p hp => hother fun he => hs (he ▸ succ_of_pred hp)
  exact {
    wf := fun p e he => by
      by_cases hp : p = t
      · subst hp
        rw [hself] at he
        cases he
        exact ⟨henvwf, henvk, blk, hb⟩
      · rw [hother hp] at he
        exact h.wf p e he
    fed := fun p e he => by
      by_cases hp : p = t
      · subst hp
        rcases hfedT with hs | ⟨q, hq, e', he'⟩
        · exact Or.inl hs
        · exact Or.inr ⟨q, hq, hgrow he'⟩
      · rw [hother hp] at he
        rcases h.fed p e he with hs | ⟨q, hq, e', he'⟩
        · exact Or.inl hs
        · exact Or.inr ⟨q, hq, hgrow he'⟩
    workFed := fun p hp => by
      rcases List.mem_append.1 hp with hm | hm
      · rcases h.workFed p (List.mem_cons_of_mem _ hm) with hs | ⟨q, hq, e', he'⟩
        · exact Or.inl hs
        · exact Or.inr ⟨q, hq, hgrow he'⟩
      · exact Or.inr ⟨t, pred_of_succ hm, env, hself⟩
    drop := fun p blk' e hb' he => by
      by_cases hp : p = t
      · subst hp
        rw [hb] at hb'
        cases hb'
        rw [hself] at he
        cases he
        have := transfer_grows reads blk (hlow hfedT) (entry_wf hw _)
        rw [henv] at this
        exact this
      · rw [hother hp] at he
        exact ConstLe.trans (transfer_grows reads blk' (hlow (h.fed p e he)) (entry_wf hw _)) (h.drop p blk' e hb' he)
    pend := fun p blk' e hb' he => by
      by_cases hs : p ∈ cfg.successors t
      · exact Or.inl (List.mem_append.2 (Or.inr hs))
      · rw [hsame hs]
        by_cases hp : p = t
        · subst hp
          rw [hb] at hb'
          cases hb'
          rw [hself] at he
          cases he
          rw [henv]
          exact Or.inr fun _ => rfl
        · rw [hother hp] at he
          rcases h.pend p blk' e hb' he with hm | hs'
          · exact Or.inl (List.mem_append.2 (Or.inl ((List.mem_cons.1 hm).resolve_left hp)))
          · exact Or.inr hs'
    close := fun p e he s hs => by
      by_cases hp : p = t
      · subst hp
        exact Or.inr (Or.inl (List.mem_append.2 (Or.inr hs)))
      · rw [hother hp] at he
        rcases h.close p e he s hs with ⟨e', he'⟩ | hm | hn
        · exact Or.inl (hgrow he')
        · rcases List.mem_cons.1 hm with rfl | hm
          · exact Or.inl ⟨env, hself⟩
          · exact Or.inr (Or.inl (List.mem_append.2 (Or.inl hm)))
        · exact Or.inr (Or.inr hn)
    start := by
      rcases h.start with ⟨e', he'⟩ | hm | hn
      · exact Or.inl (hgrow he')
      · rcases List.mem_cons.1 hm with he | hm
        · rw [he]
          exact Or.inl ⟨env, hself⟩
        · exact Or.inr (Or.inl (List.mem_append.2 (Or.inl hm)))
      · exact Or.inr (Or.inr hn)
  }

private theorem aux_none {cfg : Cfg} {reads : List (Tid × List Var)} {f : Nat} {exits : ExitEnvs} {t : Tid} {w : List Tid} (hb : cfg.block t = none) :
    propagateAux cfg reads (f + 1) exits (t :: w) = propagateAux cfg reads f exits w := by
  simp only [propagateAux, hb]

private theorem aux_some {cfg : Cfg} {reads : List (Tid × List Var)} {f : Nat} {exits : ExitEnvs} {t : Tid} {w : List Tid} {blk : Blk}
    (hb : cfg.block t = some blk) :
    propagateAux cfg reads (f + 1) exits (t :: w) =
      if settled (Assoc.get t exits) (transfer reads blk (entryEnv cfg exits t)) = true then propagateAux cfg reads f exits w
      else propagateAux cfg reads f (Assoc.put t (transfer reads blk (entryEnv cfg exits t)) exits) (w ++ cfg.successors t) := by
  obtain ⟨_, rfl⟩ := block_some hb
  simp only [propagateAux, hb, transfer_eq]

/-! Each change loses a constant, and what it adds to the work is paid for by that. -/

private def constCard (U : List Var) (e : ConstEnv) : Nat := U.countP fun v => (Assoc.get v e).isSome

private theorem card_lt_of {U : List Var} {a b : ConstEnv} (hle : ConstLe a b) {v : Var} (hv : v ∈ U)
    (ha : Assoc.get v a = none) (hb : (Assoc.get v b).isSome = true) : constCard U a < constCard U b := by
  have hmono : ∀ l : List Var, l.countP (fun v => (Assoc.get v a).isSome) ≤ l.countP fun v => (Assoc.get v b).isSome := by
    intro l
    apply List.countP_mono_left
    intro x _ hx
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hx
    rw [hle x c hc]
    rfl
  induction U with
  | nil => cases hv
  | cons x xs ih =>
    simp only [constCard, List.countP_cons] at ih ⊢
    rcases List.mem_cons.1 hv with rfl | hm
    · have h0 := hmono xs
      simp only [ha, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hb]
      omega
    · have h1 := ih hm
      split <;> split <;> first | omega | skip
      rename_i hxa hxb
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hxa
      rw [hle x c hc] at hxb
      simp at hxb

private theorem card_le_length (U : List Var) (e : ConstEnv) : constCard U e ≤ U.length := List.countP_le_length

private def constWeight (U : List Var) (exits : ExitEnvs) (t : Tid) : Nat :=
  match Assoc.get t exits with
  | some e => constCard U e
  | none => U.length + 1

private def constPotential (cfg : Cfg) (U : List Var) (exits : ExitEnvs) (work : List Tid) : Nat :=
  work.length + (((cfg.blocks.map Blk.tid).eraseDups).map fun t => constWeight U exits t * (cfg.successors t).length).sum

private theorem sum_le {β : Type} (B : List β) {f g : β → Nat} (h : ∀ x, f x ≤ g x) : (B.map f).sum ≤ (B.map g).sum := by
  induction B with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h x
    omega

private theorem sum_drop {β : Type} [DecidableEq β] {B : List β} {f g : β → Nat} {t : β} {n : Nat} (ht : t ∈ B)
    (ho : ∀ x, x ≠ t → g x = f x) (hg : g t + n ≤ f t) : (B.map g).sum + n ≤ (B.map f).sum := by
  have hle : ∀ x, g x ≤ f x := fun x => by
    by_cases hx : x = t
    · subst hx
      omega
    · exact Nat.le_of_eq (ho x hx)
  induction B with
  | nil => cases ht
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases hx : x = t
    · subst hx
      have := sum_le xs hle
      omega
    · have := ih ((List.mem_cons.1 ht).resolve_left (Ne.symm hx))
      have := ho x hx
      omega

private theorem Inv.changed_lt {cfg : Cfg} {reads : List (Tid × List Var)} {U : List Var} {exits : ExitEnvs} {t : Tid} {work : List Tid}
    (h : Inv cfg reads U exits (t :: work)) {blk : Blk} (hb : cfg.block t = some blk)
    (hs : ¬ settled (Assoc.get t exits) (transfer reads blk (entryEnv cfg exits t)) = true) :
    constPotential cfg U (Assoc.put t (transfer reads blk (entryEnv cfg exits t)) exits) (work ++ cfg.successors t) < constPotential cfg U exits (t :: work) := by
  generalize henv : transfer reads blk (entryEnv cfg exits t) = env at *
  have hw := h.allWF
  have henvwf : ConstWF env := henv ▸ transfer_wf reads blk (entry_wf hw t)
  have hweight : constWeight U (Assoc.put t env exits) t + 1 ≤ constWeight U exits t := by
    have hself : constWeight U (Assoc.put t env exits) t = constCard U env := by
      simp only [constWeight, get_put, ↓reduceIte]
    rw [hself]
    cases hold : Assoc.get t exits with
    | none =>
      simp only [constWeight, hold]
      have := card_le_length U env
      omega
    | some old =>
      simp only [constWeight, hold]
      rw [hold] at hs
      have hle : ConstLe env old := henv ▸ h.drop t blk old hb hold
      have hnot : ¬ SameC old env := fun hsame => hs (same_of_sameC (h.wf t old hold).1 henvwf hsame)
      have : ∃ v, Assoc.get v old ≠ Assoc.get v env := by
        apply Classical.byContradiction
        intro hn
        exact hnot fun v => Classical.byContradiction fun hv => hn ⟨v, hv⟩
      obtain ⟨v, hv⟩ := this
      cases hg : Assoc.get v env with
      | some c =>
        rw [hg, hle v c hg] at hv
        exact absurd rfl hv
      | none =>
        cases hg' : Assoc.get v old with
        | none =>
          rw [hg, hg'] at hv
          exact absurd rfl hv
        | some c =>
          exact card_lt_of hle ((h.wf t old hold).2.1 v c hg') hg (by simp [hg'])
  have hother : ∀ x, x ≠ t → constWeight U (Assoc.put t env exits) x = constWeight U exits x := fun x hx => by
    simp only [constWeight, get_put, hx, ↓reduceIte]
  have htmem : t ∈ (cfg.blocks.map Blk.tid).eraseDups := by
    obtain ⟨hm, ht⟩ := block_some hb
    exact List.mem_eraseDups.2 (List.mem_map.2 ⟨blk, hm, ht⟩)
  have hsum := sum_drop (f := fun x => constWeight U exits x * (cfg.successors x).length)
    (g := fun x => constWeight U (Assoc.put t env exits) x * (cfg.successors x).length) (n := (cfg.successors t).length) htmem
    (fun x hx => by simp only [hother x hx])
    (by
      show constWeight U (Assoc.put t env exits) t * _ + _ ≤ constWeight U exits t * _
      calc constWeight U (Assoc.put t env exits) t * (cfg.successors t).length + (cfg.successors t).length
          = (constWeight U (Assoc.put t env exits) t + 1) * (cfg.successors t).length := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ _ := Nat.mul_le_mul_right _ hweight)
  simp only [constPotential, List.length_append, List.length_cons]
  omega

private theorem potential_tail (cfg : Cfg) (U : List Var) (exits : ExitEnvs) (t : Tid) (w : List Tid) :
    constPotential cfg U exits w < constPotential cfg U exits (t :: w) := by
  simp only [constPotential, List.length_cons]
  omega

/-- The worklist runs its course within any fuel above the potential, and everything between steps then holds with nothing left. -/
private theorem aux_inv {cfg : Cfg} {reads : List (Tid × List Var)} {U : List Var} (hU : ∀ blk ∈ cfg.blocks, ∀ d ∈ blk.defs, d.var ∈ U)
    (fuel : Nat) {exits : ExitEnvs} {work : List Tid} (h : Inv cfg reads U exits work) (hf : constPotential cfg U exits work < fuel) :
    Inv cfg reads U (propagateAux cfg reads fuel exits work) [] := by
  induction fuel generalizing exits work with
  | zero => omega
  | succ f ih =>
    cases work with
    | nil => exact h
    | cons t w =>
      cases hb : cfg.block t with
      | none =>
        rw [aux_none hb]
        exact ih (h.skip hb) (by have := potential_tail cfg U exits t w; omega)
      | some blk =>
        rw [aux_some hb]
        split
        · rename_i hs
          exact ih (h.settle hb hs) (by have := potential_tail cfg U exits t w; omega)
        · rename_i hs
          have hd := hU blk (block_some hb).1
          exact ih (h.change hb hd) (by have := h.changed_lt hb hs; omega)

/-! Nothing the worklist holds goes below a solution. -/

/-- Every constant of `X` is in the table of the worklist. -/
def Above (X exits : ExitEnvs) : Prop := ∀ t x e, Assoc.get t X = some x → Assoc.get t exits = some e → ConstLe x e

/-- `X` is a solution of the equations of the analysis: each block's table says at most what follows from those before it. -/
structure Solves (cfg : Cfg) (reads : List (Tid × List Var)) (X : ExitEnvs) : Prop where
  wf : AllWF X
  sol : ∀ blk ∈ cfg.blocks, ∃ x, Assoc.get blk.tid X = some x ∧ ConstLe x (transfer reads blk (entryEnv cfg X blk.tid))

/-- The worklist stays above every solution, for any fuel. -/
theorem propagateAux_above {cfg : Cfg} {reads : List (Tid × List Var)} {U : List Var} {X : ExitEnvs} (hU : ∀ blk ∈ cfg.blocks, ∀ d ∈ blk.defs, d.var ∈ U)
    (hX : Solves cfg reads X) (fuel : Nat) {exits : ExitEnvs} {work : List Tid} (h : Inv cfg reads U exits work) (ha : Above X exits) :
    Above X (propagateAux cfg reads fuel exits work) := by
  induction fuel generalizing exits work with
  | zero => exact ha
  | succ f ih =>
    cases work with
    | nil => exact ha
    | cons t w =>
      cases hb : cfg.block t with
      | none =>
        rw [aux_none hb]
        exact ih (h.skip hb) ha
      | some blk =>
        rw [aux_some hb]
        split
        · rename_i hs
          exact ih (h.settle hb hs) ha
        · rename_i hs
          refine ih (h.change hb (hU blk (block_some hb).1)) ?_
          intro t' x e hx he
          by_cases ht : t' = t
          · subst ht
            simp only [get_put, ↓reduceIte, Option.some.injEq] at he
            subst he
            obtain ⟨hm, htid⟩ := block_some hb
            obtain ⟨x', hx', hle⟩ := hX.sol blk hm
            rw [htid, hx] at hx'
            cases hx'
            rw [htid] at hle
            refine ConstLe.trans hle (transfer_grows reads blk ?_ (entry_wf h.allWF _))
            refine entry_le hX.wf h.allWF (h.workFed t' (List.mem_cons_self ..)) ?_
            intro p _ e' he'
            obtain ⟨b, hbp⟩ := (h.wf p e' he').2.2
            obtain ⟨hmp, hpt⟩ := block_some hbp
            obtain ⟨x'', hx'', _⟩ := hX.sol b hmp
            rw [hpt] at hx''
            exact ⟨x'', hx'', ha p x'' e' hx'' he'⟩
          · rw [get_put, ite_eq_right ht] at he
            exact ha t' x e hx he

/-! ### What the analysis of a whole function finds -/

/-- What `Cfg.fromSub` gives, after `Cfg.prune`, if the blocks of a function have different ids. -/
structure Tidy (cfg : Cfg) : Prop where
  nodes : ∀ t ∈ cfg.graph.nodes, ∃ blk ∈ cfg.blocks, blk.tid = t
  nodup : (cfg.blocks.map Blk.tid).Nodup
  reach : ∀ blk ∈ cfg.blocks, blk.tid ∈ cfg.reachable

theorem Tidy.block {cfg : Cfg} (h : Tidy cfg) {t : Tid} {blk : Blk} (hm : blk ∈ cfg.blocks) (ht : blk.tid = t) : cfg.block t = some blk := by
  have key : ∀ l : List Blk, (l.map Blk.tid).Nodup → blk ∈ l → l.find? (fun b => decide (b.tid = t)) = some blk := by
    intro l
    induction l with
    | nil => simp
    | cons b bs ih =>
      intro hn hb
      simp only [List.map_cons, List.nodup_cons] at hn
      rcases List.mem_cons.1 hb with rfl | hb
      · simp [ht]
      · have hne : ¬ b.tid = t := fun he => hn.1 (List.mem_map.2 ⟨blk, hb, ht.trans he.symm⟩)
        simp only [List.find?_cons, hne, decide_false]
        exact ih hn.2 hb
  exact key cfg.blocks h.nodup hm

private theorem Tidy.block_some' {cfg : Cfg} (h : Tidy cfg) {t : Tid} (ht : t ∈ cfg.graph.nodes) : ∃ blk, cfg.block t = some blk := by
  obtain ⟨blk, hm, hb⟩ := h.nodes t ht
  exact ⟨blk, h.block hm hb⟩

/-- With no work left, every block has its table, and it is what follows from those before it. -/
private theorem Inv.final {cfg : Cfg} {reads : List (Tid × List Var)} {U : List Var} {exits : ExitEnvs} (h : Inv cfg reads U exits []) (ht : Tidy cfg)
    {blk : Blk} (hm : blk ∈ cfg.blocks) :
    ∃ e, Assoc.get blk.tid exits = some e ∧ SameC e (transfer reads blk (entryEnv cfg exits blk.tid)) := by
  have hreach : ∃ e, Assoc.get blk.tid exits = some e := by
    refine Bap.Proofs.Graph.reachableFrom_least cfg.graph [cfg.start] (fun t => ∃ e, Assoc.get t exits = some e) ?_ ?_ _ (ht.reach blk hm)
    · intro x hx hn
      have hx : x = cfg.start := by simpa using hx
      subst hx
      rcases h.start with hk | hw | hnone
      · exact hk
      · cases hw
      · obtain ⟨b, hb⟩ := ht.block_some' hn
        rw [hb] at hnone
        cases hnone
    · rintro a b ⟨e, he⟩ hedge hn
      rcases h.close a e he b ((Bap.Graph.successors_mem cfg.graph a b).2 hedge) with hk | hw | hnone
      · exact hk
      · cases hw
      · obtain ⟨b', hb⟩ := ht.block_some' hn
        rw [hb] at hnone
        cases hnone
  obtain ⟨e, he⟩ := hreach
  refine ⟨e, he, ?_⟩
  rcases h.pend blk.tid blk e (ht.block hm rfl) he with hw | hs
  · cases hw
  · exact hs

/-- Every variable a block of the graph defines or reads. -/
def varsOf (cfg : Cfg) : List Var := (cfg.blocks.flatMap fun blk => blk.definedVars ++ blk.freeVars).eraseDups

private theorem defs_in_vars (cfg : Cfg) : ∀ blk ∈ cfg.blocks, ∀ d ∈ blk.defs, d.var ∈ varsOf cfg := by
  intro blk hb d hd
  refine List.mem_eraseDups.2 (List.mem_flatMap.2 ⟨blk, hb, List.mem_append.2 (Or.inl ?_)⟩)
  simp only [Blk.definedVars, List.mem_eraseDups, List.mem_append, List.mem_map]
  exact Or.inr ⟨d, hd, rfl⟩

private theorem eraseDups_length_le (l : List Tid) : l.eraseDups.length ≤ l.length := by
  generalize hn : l.length = n
  induction n using Nat.strongRecOn generalizing l with
  | _ n ih =>
    cases l with
    | nil => simp
    | cons x xs =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons] at hn ⊢
      have hle : (xs.filter fun b => !b == x).length ≤ xs.length := List.length_filter_le _ _
      have := ih _ (by omega) (xs.filter fun b => !b == x) rfl
      omega

private theorem sum_filter_le (E : List (Tid × Tid)) (B : List Tid) (hB : B.Nodup) :
    (B.map fun t => (E.filter fun edge => decide (edge.1 = t)).length).sum ≤ E.length := by
  induction B generalizing E with
  | nil => simp
  | cons x xs ih =>
    simp only [List.nodup_cons] at hB
    simp only [List.map_cons, List.sum_cons]
    have hsplit : (E.filter fun edge => decide (edge.1 = x)).length + (E.filter fun edge => decide (edge.1 ≠ x)).length = E.length := by
      induction E with
      | nil => rfl
      | cons e es ih' =>
        simp only [List.filter_cons, List.length_cons, ne_eq, decide_not]
        by_cases he : e.1 = x
        · simp only [he, decide_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true, List.length_cons]
          simp only [ne_eq, decide_not] at ih'
          omega
        · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          simp only [ne_eq, decide_not] at ih'
          simp only [List.length_cons]
          omega
    have hrest := ih (E.filter fun edge => decide (edge.1 ≠ x)) hB.2
    have hsame : (xs.map fun t => ((E.filter fun edge => decide (edge.1 ≠ x)).filter fun edge => decide (edge.1 = t)).length).sum =
        (xs.map fun t => (E.filter fun edge => decide (edge.1 = t)).length).sum := by
      congr 1
      apply List.map_congr_left
      intro t ht
      rw [List.filter_filter]
      congr 1
      apply List.filter_congr
      intro e _
      have hne : t ≠ x := fun he => hB.1 (he ▸ ht)
      by_cases he : e.1 = t
      · have : e.1 ≠ x := he ▸ hne
        simp [he, hne]
      · simp [he]
    omega

private theorem sum_out_le (cfg : Cfg) :
    (((cfg.blocks.map Blk.tid).eraseDups).map fun t => (cfg.successors t).length).sum ≤ cfg.graph.edges.length := by
  refine Nat.le_trans (sum_le _ fun t => ?_) (sum_filter_le cfg.graph.edges _ (Bap.Proofs.Graph.nodup_eraseDups _))
  refine Nat.le_trans (eraseDups_length_le _) ?_
  simp

private theorem sum_mul (B : List Tid) (f : Tid → Nat) (k : Nat) : (B.map fun t => k * f t).sum = k * (B.map f).sum := by
  induction B with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

private theorem potential_start (cfg : Cfg) : constPotential cfg (varsOf cfg) [] [cfg.start] < propagateFuel cfg := by
  have hw : ∀ t, constWeight (varsOf cfg) [] t = (varsOf cfg).length + 1 := fun _ => rfl
  simp only [constPotential, hw, List.length_cons, List.length_nil]
  rw [sum_mul]
  have hsum := Nat.mul_le_mul_left ((varsOf cfg).length + 1) (sum_out_le cfg)
  have hfuel : propagateFuel cfg = ((varsOf cfg).length + 2) * (cfg.blocks.length + 2) * (cfg.graph.edges.length + 2) := rfl
  rw [hfuel]
  generalize (varsOf cfg).length = V at *
  generalize cfg.graph.edges.length = E at *
  generalize (((cfg.blocks.map Blk.tid).eraseDups).map fun t => (cfg.successors t).length).sum = S at *
  have h1 : (V + 2) * (E + 2) ≤ (V + 2) * (cfg.blocks.length + 2) * (E + 2) := by
    apply Nat.mul_le_mul_right
    exact Nat.le_mul_of_pos_right _ (by omega)
  have h2 : (V + 2) * (E + 2) = V * E + 2 * V + 2 * E + 4 := by
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  have h3 : (V + 1) * E = V * E + E := by
    simp only [Nat.add_mul, Nat.one_mul]
  omega

/-- The fuel is enough for the worklist to finish, for any table of what to keep. -/
theorem propagateAux_finishes (cfg : Cfg) (reads : List (Tid × List Var)) :
    Inv cfg reads (varsOf cfg) (propagateAux cfg reads (propagateFuel cfg) [] [cfg.start]) [] :=
  aux_inv (defs_in_vars cfg) _ (Inv.init cfg reads _) (potential_start cfg)

/-- So the analysis of a tidy graph is always solved: it never falls back on constants local to each block. -/
theorem isSolved_always {cfg : Cfg} (ht : Tidy cfg) (reads : List (Tid × List Var)) :
    isSolved cfg reads (propagateAux cfg reads (propagateFuel cfg) [] [cfg.start]) = true := by
  have hinv := propagateAux_finishes cfg reads
  refine List.all_eq_true.2 fun blk hm => ?_
  obtain ⟨e, he, hs⟩ := hinv.final ht hm
  rw [transfer_eq, he]
  exact same_of_sameC (hinv.wf _ e he).1 (transfer_wf reads blk (entry_wf hinv.allWF _)) hs

/-! ### What is not kept is not read -/

private theorem sub_congr (x : Exp) {a b : ConstEnv} (h : ∀ v, occursFree v x = true → Assoc.get v a = Assoc.get v b) : sub a x = sub b x := by
  induction x generalizing a b with
  | int v => rfl
  | unknown m t => rfl
  | var x =>
    simp only [sub, Bil.substitute, get_replacements]
    rw [h x (by simp [occursFree])]
  | load m a' e n ihm iha =>
    simp only [sub, Bil.substitute] at ihm iha ⊢
    rw [ihm fun v hv => h v (by simp [occursFree, hv]), iha fun v hv => h v (by simp [occursFree, hv])]
  | store m a' d e n ihm iha ihv =>
    simp only [sub, Bil.substitute] at ihm iha ihv ⊢
    rw [ihm fun v hv => h v (by simp [occursFree, hv]), iha fun v hv => h v (by simp [occursFree, hv]),
      ihv fun v hv => h v (by simp [occursFree, hv])]
  | bin op l r ihl ihr =>
    simp only [sub, Bil.substitute] at ihl ihr ⊢
    rw [ihl fun v hv => h v (by simp [occursFree, hv]), ihr fun v hv => h v (by simp [occursFree, hv])]
  | un op d ih =>
    simp only [sub, Bil.substitute] at ih ⊢
    rw [ih fun v hv => h v (by simp [occursFree, hv])]
  | cast k w d ih =>
    simp only [sub, Bil.substitute] at ih ⊢
    rw [ih fun v hv => h v (by simp [occursFree, hv])]
  | letIn y d body ihv ihb =>
    rw [sub_let, sub_let, ihv fun v hv => h v (by simp [occursFree, hv])]
    congr 1
    apply ihb
    intro v hv
    by_cases hy : v = y
    · subst hy
      simp [get_remove]
    · simp only [get_remove, hy, ite_false]
      refine h v ?_
      have hy' : (y != v) = true := by simpa using fun h' : y = v => hy h'.symm
      simp [occursFree, hv, hy']
  | ite c y n ihc ihy ihn =>
    simp only [sub, Bil.substitute] at ihc ihy ihn ⊢
    rw [ihc fun v hv => h v (by simp [occursFree, hv]), ihy fun v hv => h v (by simp [occursFree, hv]),
      ihn fun v hv => h v (by simp [occursFree, hv])]
  | extract hi lo d ih =>
    simp only [sub, Bil.substitute] at ih ⊢
    rw [ih fun v hv => h v (by simp [occursFree, hv])]
  | concat l r ihl ihr =>
    simp only [sub, Bil.substitute] at ihl ihr ⊢
    rw [ihl fun v hv => h v (by simp [occursFree, hv]), ihr fun v hv => h v (by simp [occursFree, hv])]

private theorem free_of_vars {v : Var} {x : Exp} (h : v ∈ freeVars x) : occursFree v x = true :=
  (Bap.Proofs.Bil.mem_freeVars_iff v x).1 h

private theorem vars_of_free {v : Var} {x : Exp} (h : occursFree v x = true) : v ∈ freeVars x :=
  (Bap.Proofs.Bil.mem_freeVars_iff v x).2 h

/-- The rewritten definitions and the constants after them depend on what the definitions read and what is wanted after. -/
private theorem defs_local (S : Var → Prop) (defs : List Def) (acc : List Def) {a b : ConstEnv}
    (h : ∀ v, (Exposed defs v ∨ (S v ∧ ∀ d ∈ defs, d.var ≠ v)) → Assoc.get v a = Assoc.get v b) :
    (defs.foldl propStep (acc, a)).1 = (defs.foldl propStep (acc, b)).1 ∧
      ∀ v, S v → Assoc.get v (defs.foldl propStep (acc, a)).2 = Assoc.get v (defs.foldl propStep (acc, b)).2 := by
  induction defs generalizing acc a b with
  | nil =>
    refine ⟨rfl, fun v hv => h v (Or.inr ⟨hv, by simp⟩)⟩
  | cons d ds ih =>
    have hrhs : sub a d.rhs = sub b d.rhs := sub_congr _ fun v hv => h v (Or.inl (Or.inl (vars_of_free hv)))
    have hstep : ∀ e : ConstEnv, (propStep (acc, e) d).2 = constStep e d.var (simplifyExp (sub e d.rhs)) := by
      intro e
      simp only [constStep, removeConst_eq, sub]
      rfl
    have hdefs : (propStep (acc, a) d).1 = (propStep (acc, b) d).1 := by
      have ha : (propStep (acc, a) d).1 = acc ++ [{ d with rhs := simplifyExp (sub a d.rhs) }] := rfl
      have hb : (propStep (acc, b) d).1 = acc ++ [{ d with rhs := simplifyExp (sub b d.rhs) }] := rfl
      rw [ha, hb, hrhs]
    have hagree : ∀ v, (Exposed ds v ∨ (S v ∧ ∀ d' ∈ ds, d'.var ≠ v)) →
        Assoc.get v (propStep (acc, a) d).2 = Assoc.get v (propStep (acc, b) d).2 := by
      intro v hv
      rw [hstep, hstep, get_constStep, get_constStep, hrhs]
      split
      · rfl
      · rename_i hne
        refine h v ?_
        rcases hv with hv | ⟨hs, hv⟩
        · exact Or.inl (Or.inr ⟨hne, hv⟩)
        · refine Or.inr ⟨hs, ?_⟩
          intro d' hd'
          rcases List.mem_cons.1 hd' with rfl | hd'
          · exact fun he => hne he.symm
          · exact hv d' hd'
    have := ih (acc := (propStep (acc, a) d).1) (a := (propStep (acc, a) d).2) (b := (propStep (acc, b) d).2) hagree
    simp only [List.foldl_cons]
    have ea : (propStep (acc, a) d) = ((propStep (acc, a) d).1, (propStep (acc, a) d).2) := rfl
    have eb : (propStep (acc, b) d) = ((propStep (acc, a) d).1, (propStep (acc, b) d).2) := by
      rw [hdefs]
    rw [ea, eb]
    exact this

private theorem jmp_local (j : Jmp) {a b : ConstEnv} (h : ∀ v, v ∈ j.freeVars → Assoc.get v a = Assoc.get v b) :
    Jmp.mapExp (propJump a) j = Jmp.mapExp (propJump b) j := by
  have hexp : ∀ x, (∀ v, v ∈ freeVars x → v ∈ j.freeVars) → propJump a x = propJump b x := fun x hx => by
    show simplifyExp (sub a x) = simplifyExp (sub b x)
    rw [sub_congr x fun v hv => h v (hx v (vars_of_free hv))]
  have hlabel : ∀ l : Label, (∀ v, v ∈ l.freeVars → v ∈ j.freeVars) → Label.mapExp (propJump a) l = Label.mapExp (propJump b) l := by
    intro l hl
    cases l with
    | direct t => rfl
    | indirect x =>
      simp only [Label.mapExp]
      rw [hexp x hl]
  have hmem : ∀ v, (v ∈ (j.condition.map freeVars).getD [] ∨ v ∈ j.kind.freeVars) → v ∈ j.freeVars := fun v hv => by
    simp only [Jmp.freeVars, List.mem_eraseDups, List.mem_append]
    exact hv
  have hc : j.condition.map (propJump a) = j.condition.map (propJump b) := by
    cases hcond : j.condition with
    | none => rfl
    | some x =>
      simp only [Option.map_some]
      rw [hexp x fun v hv => hmem v (Or.inl (by simp [hcond, hv]))]
  have hk : j.kind.mapExp (propJump a) = j.kind.mapExp (propJump b) := by
    cases hkind : j.kind with
    | goto l =>
      simp only [JmpKind.mapExp]
      rw [hlabel l fun v hv => hmem v (Or.inr (by simpa [hkind, JmpKind.freeVars] using hv))]
    | ret l =>
      simp only [JmpKind.mapExp]
      rw [hlabel l fun v hv => hmem v (Or.inr (by simpa [hkind, JmpKind.freeVars] using hv))]
    | call l r =>
      simp only [JmpKind.mapExp]
      rw [hlabel l fun v hv => hmem v (Or.inr (by simp [hkind, JmpKind.freeVars, List.mem_eraseDups, hv]))]
      cases r with
      | none => rfl
      | some l' =>
        simp only [Option.map_some]
        rw [hlabel l' fun v hv => hmem v (Or.inr (by simp [hkind, JmpKind.freeVars, List.mem_eraseDups, hv]))]
    | interrupt n t => rfl
  simp only [Jmp.mapExp, hc, hk]

/-- What a block's rewrite and exit constants depend on, given what is wanted of them after it. -/
private def ReadsOf (blk : Blk) (out : List Var) (v : Var) : Prop :=
  Exposed blk.defs v ∨ (((∃ j ∈ blk.jmps, v ∈ j.freeVars) ∨ v ∈ out) ∧ ∀ d ∈ blk.defs, d.var ≠ v)

/-- The rewrite of a block and what is wanted of its constants depend only on what it reads of those at its entry. -/
private theorem block_local (blk : Blk) (out : List Var) {a b : ConstEnv} (h : ∀ v, ReadsOf blk out v → Assoc.get v a = Assoc.get v b) :
    (propagateBlock blk a).1 = (propagateBlock blk b).1 ∧ ∀ v ∈ out, Assoc.get v (exitOf blk a) = Assoc.get v (exitOf blk b) := by
  have hentry : ∀ v, (Exposed blk.defs v ∨ (((∃ j ∈ blk.jmps, v ∈ j.freeVars) ∨ v ∈ out) ∧ ∀ d ∈ blk.defs, d.var ≠ v)) →
      Assoc.get v (propEntry blk a) = Assoc.get v (propEntry blk b) := by
    intro v hv
    have e : ∀ x : ConstEnv, propEntry blk x = x.filter fun y => (fun k => decide (k ∉ blk.phis.map Phi.var)) y.1 := fun _ => rfl
    rw [e, e, get_filter_key (fun k => decide (k ∉ blk.phis.map Phi.var)) a v,
      get_filter_key (fun k => decide (k ∉ blk.phis.map Phi.var)) b v, h v hv]
  obtain ⟨h₁, h₂⟩ := defs_local (fun v => (∃ j ∈ blk.jmps, v ∈ j.freeVars) ∨ v ∈ out) blk.defs [] hentry
  have hexit : ∀ x, exitOf blk x = (propFold blk x).2 := fun x => by
    rw [← exit_eq, propagateBlock_eq]
  constructor
  · rw [propagateBlock_eq, propagateBlock_eq]
    have hj : blk.jmps.map (Jmp.mapExp (propJump (propFold blk a).2)) = blk.jmps.map (Jmp.mapExp (propJump (propFold blk b).2)) := by
      apply List.map_congr_left
      intro j hj
      exact jmp_local j fun v hv => h₂ v (Or.inl ⟨j, hj, hv⟩)
    simp only [hj, show (propFold blk a).1 = (propFold blk b).1 from h₁]
  · intro v hv
    rw [hexit, hexit]
    exact h₂ v (Or.inr hv)

/-! ### Keeping only what can be read -/

private abbrev stripped (cfg : Cfg) : Cfg := { cfg with blocks := cfg.blocks.map fun blk => { blk with phis := [] } }

private theorem stripped_block (cfg : Cfg) {t : Tid} {blk : Blk} (h : cfg.block t = some blk) :
    (stripped cfg).block t = some { blk with phis := [] } := by
  have key : ∀ l : List Blk, l.find? (fun b => decide (b.tid = t)) = some blk →
      (l.map fun b : Blk => { b with phis := [] }).find? (fun b : Blk => decide (b.tid = t)) = some { blk with phis := [] } := by
    intro l
    induction l with
    | nil => simp
    | cons b bs ih =>
      intro hf
      simp only [List.find?_cons, List.map_cons] at hf ⊢
      by_cases hb : b.tid = t
      · subst hb
        simp only [decide_true] at hf ⊢
        cases hf
        rfl
      · simp only [hb, decide_false] at hf ⊢
        exact ih hf
  exact key cfg.blocks h

/-- What is read before the block's end and what is wanted after it is live at its entry. -/
private theorem reads_live (cfg : Cfg) {t : Tid} {blk : Blk} (ht : t ∈ cfg.reachable) (hb : cfg.block t = some blk) {v : Var}
    (hr : ReadsOf blk ((Assoc.get t (constReads cfg)).getD []) v) : v ∈ (Assoc.get t (stripped cfg).liveness.1).getD [] := by
  have heq := liveness_equations (stripped cfg) (t := t) ht (stripped_block cfg hb) v
  rw [heq.1, mem_blockIn]
  refine ⟨by simp, ?_⟩
  rcases hr with hr | ⟨hr, hd⟩
  · exact Or.inl hr
  · refine Or.inr ⟨?_, hd⟩
    rcases hr with hj | ho
    · exact Or.inl hj
    · exact Or.inr (heq.2.1 ho)

/-- What is live at a block's entry can be read after each block before it. -/
private theorem live_kept (cfg : Cfg) {p t : Tid} {blk b : Blk} (hp : p ∈ cfg.reachable) (hbp : cfg.block p = some b) (hb : cfg.block t = some blk)
    (hedge : p ∈ cfg.predecessors t) {v : Var} (hv : v ∈ (Assoc.get t (stripped cfg).liveness.1).getD []) :
    v ∈ (Assoc.get p (constReads cfg)).getD [] := by
  have heq := liveness_equations (stripped cfg) (t := p) hp (stripped_block cfg hbp) v
  refine heq.2.2 ?_
  rw [mem_blockOut]
  exact ⟨t, succ_of_pred hedge, { blk with phis := [] }, stripped_block cfg hb, Or.inl ⟨hv, by simp⟩⟩

/-- Keeping every constant. -/
def allReads (cfg : Cfg) : List (Tid × List Var) := cfg.blocks.map fun blk => (blk.tid, varsOf cfg)

/-- `propagateConstants` with nothing cut from the tables. Only for stating what it is: nothing runs this. -/
def propagateUnrestricted (cfg : Cfg) : Cfg :=
  let cfg := cfg.prune
  let reads := allReads cfg
  let exits := propagateAux cfg reads (propagateFuel cfg) [] [cfg.start]
  let solved := isSolved cfg reads exits
  { cfg with blocks := cfg.blocks.map fun blk =>
    (propagateBlock blk (if solved then entryEnv cfg exits blk.tid else [])).1
  }

private theorem transfer_get (reads : List (Tid × List Var)) (blk : Blk) (e : ConstEnv) (v : Var) :
    Assoc.get v (transfer reads blk e) = if v ∈ (Assoc.get blk.tid reads).getD [] then Assoc.get v (exitOf blk e) else none := by
  simp only [transfer, keep_eq]
  rw [get_filter_key (fun k => decide (k ∈ (Assoc.get blk.tid reads).getD []))]
  simp only [decide_eq_true_eq]

private theorem allReads_row (cfg : Cfg) {blk : Blk} (hm : blk ∈ cfg.blocks) : (Assoc.get blk.tid (allReads cfg)).getD [] = varsOf cfg := by
  have key : ∀ l : List Blk, blk ∈ l → Assoc.get blk.tid (l.map fun b => (b.tid, varsOf cfg)) = some (varsOf cfg) := by
    intro l
    induction l with
    | nil => simp
    | cons b bs ih =>
      intro hb
      simp only [Assoc.get, List.map_cons, List.lookup_cons]
      split
      · rfl
      · rcases List.mem_cons.1 hb with rfl | hb
        · simp_all
        · exact ih hb
  simp only [allReads, key cfg.blocks hm, Option.getD_some]

private theorem transfer_all (cfg : Cfg) {blk : Blk} (hm : blk ∈ cfg.blocks) {e : ConstEnv} (he : KeysIn (varsOf cfg) e) :
    SameC (transfer (allReads cfg) blk e) (exitOf blk e) := by
  intro v
  rw [transfer_get, allReads_row cfg hm]
  split
  · rfl
  · rename_i hv
    cases hg : Assoc.get v (exitOf blk e) with
    | none => rfl
    | some c =>
      have hk : KeysIn (varsOf cfg) (exitOf blk e) :=
        foldC_keys _ (defs_in_vars cfg blk hm) (KeysIn.filter_keys he fun k => decide (k ∉ blk.phis.map Phi.var))
      exact absurd (hk v c hg) hv

private theorem entry_same_one {cfg : Cfg} {A B : ExitEnvs} (hA : AllWF A) (hB : AllWF B) (t : Tid) (v : Var)
    (hdom : ∀ p, (∃ e, Assoc.get p A = some e) → ∃ e, Assoc.get p B = some e)
    (hdom' : ∀ p, (∃ e, Assoc.get p B = some e) → ∃ e, Assoc.get p A = some e)
    (hv : ∀ p ∈ cfg.predecessors t, ∀ e e', Assoc.get p A = some e → Assoc.get p B = some e' → Assoc.get v e = Assoc.get v e') (c : Constant)
    (h : Assoc.get v (entryEnv cfg A t) = some c) : Assoc.get v (entryEnv cfg B t) = some c := by
  obtain ⟨hs, ⟨p, hp, hk⟩, hall⟩ := (entry_get hA t v c).1 h
  refine (entry_get hB t v c).2 ⟨hs, ⟨p, hp, hdom p hk⟩, fun q hq e' he' => ?_⟩
  obtain ⟨e, he⟩ := hdom' q ⟨e', he'⟩
  rw [← hv q hq e e' he he']
  exact hall q hq e he

private theorem entry_same {cfg : Cfg} {A B : ExitEnvs} (hA : AllWF A) (hB : AllWF B) (t : Tid) (v : Var)
    (hdom : ∀ p, (∃ e, Assoc.get p A = some e) ↔ ∃ e, Assoc.get p B = some e)
    (hv : ∀ p ∈ cfg.predecessors t, ∀ e e', Assoc.get p A = some e → Assoc.get p B = some e' → Assoc.get v e = Assoc.get v e') :
    Assoc.get v (entryEnv cfg A t) = Assoc.get v (entryEnv cfg B t) := by
  apply Option.ext
  intro c
  constructor
  · exact entry_same_one hA hB t v (fun p => (hdom p).1) (fun p => (hdom p).2) hv c
  · exact entry_same_one hB hA t v (fun p => (hdom p).2) (fun p => (hdom p).1) (fun p hp e e' he he' => (hv p hp e' e he' he).symm) c

/-- The table every other block's exit is cut down to. -/
private def kept (reads : List (Tid × List Var)) (A : ExitEnvs) : ExitEnvs := A.map fun x => (x.1, keepReads reads x.1 x.2)

private theorem get_kept (reads : List (Tid × List Var)) (A : ExitEnvs) (t : Tid) :
    Assoc.get t (kept reads A) = (Assoc.get t A).map (keepReads reads t) := by
  induction A with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k, e⟩ := x
    simp only [kept, List.map_cons, Assoc.get, List.lookup_cons] at ih ⊢
    by_cases hk : t = k
    · subst hk
      simp
    · have hb : (t == k) = false := by simpa using hk
      simp only [hb]
      exact ih

private abbrev solR (cfg : Cfg) : ExitEnvs := propagateAux cfg (constReads cfg) (propagateFuel cfg) [] [cfg.start]
private abbrev solA (cfg : Cfg) : ExitEnvs := propagateAux cfg (allReads cfg) (propagateFuel cfg) [] [cfg.start]

/-- The restricted solution is a solution of the unrestricted equations, as cutting only removes constants. -/
private theorem restricted_solves {cfg : Cfg} (ht : Tidy cfg) : Solves cfg (allReads cfg) (solR cfg) := by
  have hinv := propagateAux_finishes cfg (constReads cfg)
  refine ⟨hinv.allWF, fun blk hm => ?_⟩
  obtain ⟨e, he, hs⟩ := hinv.final ht hm
  refine ⟨e, he, fun v c hg => ?_⟩
  rw [transfer_all cfg hm (entry_keys hinv.allWF (fun t e he => (hinv.wf t e he).2.1) _)]
  rw [hs, transfer_get] at hg
  split at hg
  · exact hg
  · cases hg

/-- The two solutions have tables for the same blocks. -/
private theorem dom_iff {cfg : Cfg} (ht : Tidy cfg) (r r' : List (Tid × List Var)) (p : Tid) :
    (∃ e, Assoc.get p (propagateAux cfg r (propagateFuel cfg) [] [cfg.start]) = some e) ↔
      ∃ e, Assoc.get p (propagateAux cfg r' (propagateFuel cfg) [] [cfg.start]) = some e := by
  have side : ∀ s s' : List (Tid × List Var), (∃ e, Assoc.get p (propagateAux cfg s (propagateFuel cfg) [] [cfg.start]) = some e) →
      ∃ e, Assoc.get p (propagateAux cfg s' (propagateFuel cfg) [] [cfg.start]) = some e := by
    rintro s s' ⟨e, he⟩
    obtain ⟨b, hb⟩ := ((propagateAux_finishes cfg s).wf p e he).2.2
    obtain ⟨hm, rfl⟩ := block_some hb
    obtain ⟨e', he', _⟩ := (propagateAux_finishes cfg s').final ht hm
    exact ⟨e', he'⟩
  exact ⟨side r r', side r' r⟩

/-- Cut down to what is kept, the unrestricted solution solves the restricted equations: what is cut can't be read. -/
private theorem unrestricted_solves {cfg : Cfg} (ht : Tidy cfg) : Solves cfg (constReads cfg) (kept (constReads cfg) (solA cfg)) := by
  have hinv := propagateAux_finishes cfg (allReads cfg)
  have hwf : AllWF (kept (constReads cfg) (solA cfg)) := by
    intro t e he
    rw [get_kept] at he
    cases hg : Assoc.get t (solA cfg) with
    | none =>
      rw [hg] at he
      cases he
    | some e' =>
      rw [hg] at he
      cases he
      exact (hinv.allWF t e' hg).filter _
  refine ⟨hwf, fun blk hm => ?_⟩
  obtain ⟨e, he, hs⟩ := hinv.final ht hm
  refine ⟨keepReads (constReads cfg) blk.tid e, by rw [get_kept, he]; rfl, fun v c hg => ?_⟩
  rw [keep_eq, get_filter_key (fun k => decide (k ∈ (Assoc.get blk.tid (constReads cfg)).getD []))] at hg
  split at hg
  · rename_i hrow
    have hrow' : v ∈ (Assoc.get blk.tid (constReads cfg)).getD [] := by simpa using hrow
    rw [hs, transfer_all cfg hm (entry_keys hinv.allWF (fun t e he => (hinv.wf t e he).2.1) _)] at hg
    rw [transfer_get, ite_eq_left hrow', ← hg]
    refine ((block_local blk ((Assoc.get blk.tid (constReads cfg)).getD []) fun x hx => ?_).2 v hrow').symm
    have hlive := reads_live cfg (ht.reach blk hm) (ht.block hm rfl) hx
    refine entry_same hinv.allWF hwf _ _ (fun p => ?_) ?_
    · simp only [get_kept, Option.map_eq_some_iff]
      constructor
      · rintro ⟨e', he'⟩
        exact ⟨_, e', he', rfl⟩
      · rintro ⟨_, e', he', _⟩
        exact ⟨e', he'⟩
    · intro p hp e₁ e₂ h₁ h₂
      rw [get_kept, h₁] at h₂
      simp only [Option.map_some, Option.some.injEq] at h₂
      subst h₂
      obtain ⟨b, hb⟩ := (hinv.wf p e₁ h₁).2.2
      have hbm := block_some hb
      have hkeep := live_kept cfg (hbm.2 ▸ ht.reach b hbm.1) hb (ht.block hm rfl) hp hlive
      rw [keep_eq, get_filter_key (fun k => decide (k ∈ (Assoc.get p (constReads cfg)).getD [])), ite_eq_left (by simpa using hkeep)]
  · cases hg

/-- The restricted solution is the unrestricted one, cut down to what is kept. -/
theorem restricted_eq {cfg : Cfg} (ht : Tidy cfg) {t : Tid} {r e : ConstEnv} (hr : Assoc.get t (solR cfg) = some r) (he : Assoc.get t (solA cfg) = some e)
    {v : Var} (hv : v ∈ (Assoc.get t (constReads cfg)).getD []) : Assoc.get v r = Assoc.get v e := by
  have hup : Above (solR cfg) (solA cfg) :=
    propagateAux_above (defs_in_vars cfg) (restricted_solves ht) _ (Inv.init cfg _ _) (by intro _ _ _ _ h; simp at h)
  have hdown : Above (kept (constReads cfg) (solA cfg)) (solR cfg) :=
    propagateAux_above (defs_in_vars cfg) (unrestricted_solves ht) _ (Inv.init cfg _ _) (by intro _ _ _ _ h; simp at h)
  apply Option.ext
  intro c
  constructor
  · exact hup t r e hr he v c
  · intro hg
    refine hdown t _ r (by rw [get_kept, he]; rfl) hr v c ?_
    rw [keep_eq, get_filter_key (fun k => decide (k ∈ (Assoc.get t (constReads cfg)).getD [])), ite_eq_left (by simpa using hv)]
    exact hg

/-- **Constant propagation with only the constants that can be read rewrites exactly as with all of them**, in a function whose
blocks have different ids. The analysis never falls back on what is local to each block in either case (`isSolved_always`). -/
theorem propagateConstants_unrestricted {cfg : Cfg} (ht : Tidy cfg.prune) : propagateConstants cfg = propagateUnrestricted cfg := by
  simp only [propagateConstants, propagateUnrestricted]
  rw [isSolved_always ht, isSolved_always ht]
  simp only [↓reduceIte]
  congr 1
  apply List.map_congr_left
  intro blk hm
  refine (block_local blk ((Assoc.get blk.tid (constReads cfg.prune)).getD []) fun x hx => ?_).1
  have hA := propagateAux_finishes cfg.prune (allReads cfg.prune)
  have hR := propagateAux_finishes cfg.prune (constReads cfg.prune)
  have hlive := reads_live cfg.prune (ht.reach blk hm) (ht.block hm rfl) hx
  refine entry_same hR.allWF hA.allWF _ _ (dom_iff ht _ _) ?_
  intro p hp e₁ e₂ h₁ h₂
  obtain ⟨b, hb⟩ := (hR.wf p e₁ h₁).2.2
  have hbm := block_some hb
  exact restricted_eq ht h₁ h₂ (live_kept cfg.prune (hbm.2 ▸ ht.reach b hbm.1) hb (ht.block hm rfl) hp hlive)

/-- A function's graph is tidy once pruned, if its blocks have different ids. -/
theorem tidy_fromSub {sub : Sub} (h : (sub.blks.map Blk.tid).Nodup) : Tidy (Cfg.fromSub sub).prune where
  nodes := fun t ht => by
    have hr : t ∈ (Cfg.fromSub sub).reachable := prune_mem_nodes.1 ht
    have hn : t ∈ (Cfg.fromSub sub).graph.nodes := Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ hr
    obtain ⟨blk, hm, rfl⟩ := List.mem_map.1 hn
    exact ⟨blk, List.mem_filter.2 ⟨hm, decide_eq_true ht⟩, rfl⟩
  nodup := List.Pairwise.sublist (List.Sublist.map _ (prune_blocks_sublist (Cfg.fromSub sub))) h
  reach := fun blk hm => prune_reachable.2 (prune_blocks_reachable hm)

/-- What the optimizer runs on: `propagateConstants` of a function's graph is the unrestricted analysis's. -/
theorem propagateConstants_fromSub {sub : Sub} (h : (sub.blks.map Blk.tid).Nodup) :
    propagateConstants (Cfg.fromSub sub) = propagateUnrestricted (Cfg.fromSub sub) :=
  propagateConstants_unrestricted (tidy_fromSub h)

end Bap.Proofs.IR
