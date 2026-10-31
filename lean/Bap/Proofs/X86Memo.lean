import Lean
import Bap.Proofs.PrimusAddress
import Bap.Target.LLVMLift

open Lean Elab Command in
/-- Bring private declarations of module `mod`, namespace `ns`, into scope by short name. -/
local elab "open_private " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

/-! The memo of x86 code gives what lifting the instruction afresh gives.

A program goes into the memo only if a run that doesn't know the address made it. Such a run gets the same at every address
(`Bap.Proofs.Primus.apply_anywhere`), so also at the address of each instruction with the same key, whatever its size. The key
holds all else a run reads: the opcode, the name of an opcode of AVX-512, the operands and the prefixes. -/

namespace Bap.Proofs.Target

open Bap Bap.Target.LLVMLift
open Bap.Primus.Semantics (Context Environment)
open Bap.Proofs.Primus (Anywhere liftWithCode_anywhere liftMCCode_anywhere)

local notation "SV" => Bap.Primus.Semantics.Value

open_private Bap.Target.LLVMLift Bap.Target.LLVMLift avxCode x86Code x86MemoStep

variable {c c' : Context}

theorem avxCode_anywhere (hc : Anywhere c c') {env : Environment} {name : String} {operands : List SV} {p : Bil.Program}
    (h : avxCode env c name operands = .ok p) : avxCode env c' name operands = .ok p := by
  unfold avxCode at h ⊢
  simp only at h ⊢
  by_cases h1 : env.instructions.contains name = true
  · simp only [h1, ↓reduceIte] at h ⊢
    exact liftWithCode_anywhere hc h
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases h2 : (name.endsWith "_EVEX" && env.instructions.contains (name.dropEnd 5).toString) = true
    · simp only [h2, ↓reduceIte] at h ⊢
      exact liftWithCode_anywhere hc h
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hop : evexOpcode? name with
      | none =>
        simp only [hop] at h
        cases h
      | some opcode =>
        simp only [hop] at h ⊢
        by_cases h3 : env.operations.contains s!"evex:{opcode.family}" = true
        · simp only [h3, ↓reduceIte] at h ⊢
          exact liftWithCode_anywhere hc h
        · simp only [h3, Bool.false_eq_true, ↓reduceIte] at h ⊢
          split at h
          · rename_i h4
            simp only [h4, ↓reduceIte]
            exact liftWithCode_anywhere hc h
          · cases h

theorem x86Code_anywhere (hc : Anywhere c c') {globals avx : Environment} {opcode : Nat} {name : Option String} {operands : List SV} {p : Bil.Program}
    (h : x86Code globals avx c opcode name operands = .ok p) : x86Code globals avx c' opcode name operands = .ok p := by
  cases name with
  | none => exact liftMCCode_anywhere hc h
  | some name => exact avxCode_anywhere hc h

/-- Two contexts of the same decoder. -/
structure SameDecoder (c c' : Context) : Prop where
  bits : c.bits = c'.bits
  endian : c.endian = c'.endian
  memory : c.memory = c'.memory

/-- What is in the memo of a decoder of the context `base`: each program is the code of its key, whatever the address.
`operandsOf` is what the decoder makes of the operands of the machine, and `finish` what it does to the code. -/
def MemoSound (globals avx : Environment) (base : Context) (operandsOf : LiftKey → List SV) (finish : Bil.Program → Bil.Program) (memo : LiftMemo) : Prop :=
  ∀ key program, memo.get? key = some (some program) → ∀ c, SameDecoder base c → c.prefixes = key.prefixes →
    (x86Code globals avx c key.opcode key.name (operandsOf key)).map finish = .ok program

theorem MemoSound.empty (globals avx : Environment) (base : Context) (operandsOf : LiftKey → List SV) (finish : Bil.Program → Bil.Program) :
    MemoSound globals avx base operandsOf finish {} := by
  intro _ _ h
  simp at h

/-- **Reusing code from the memo gives what lifting it afresh does, and what the step adds keeps the memo so**, for any context of
the instruction, at any address and of any size. -/
theorem x86MemoStep_sound {globals avx : Environment} {base : Context} {operandsOf : LiftKey → List SV} {finish : Bil.Program → Bil.Program}
    {memo : LiftMemo} (hm : MemoSound globals avx base operandsOf finish memo) (key : LiftKey) (worth : Bool) {c : Context}
    (hd : SameDecoder base c) (hp : c.prefixes = key.prefixes) :
    let step := x86MemoStep (memo.get? key) worth fun _ =>
      (x86Code globals avx { c with addressed := false } key.opcode key.name (operandsOf key)).map finish
    (∀ program, step.1 = some program →
      (x86Code globals avx c key.opcode key.name (operandsOf key)).map finish = .ok program) ∧
    MemoSound globals avx base operandsOf finish (match step.2 with
      | some entry => memo.insert key entry
      | none => memo) := by
  intro step
  have hstep : step = x86MemoStep (memo.get? key) worth fun _ =>
      (x86Code globals avx { c with addressed := false } key.opcode key.name (operandsOf key)).map finish := rfl
  have hany : ∀ {program}, (x86Code globals avx { c with addressed := false } key.opcode key.name (operandsOf key)).map finish = .ok program →
      ∀ c₂, SameDecoder base c₂ → c₂.prefixes = key.prefixes →
        (x86Code globals avx c₂ key.opcode key.name (operandsOf key)).map finish = .ok program := by
    intro program h c₂ hd₂ hp₂
    cases hx : x86Code globals avx { c with addressed := false } key.opcode key.name (operandsOf key) with
    | error e =>
      rw [hx] at h
      cases h
    | ok raw =>
      rw [hx] at h
      have hc₂ : Anywhere { c with addressed := false } c₂ :=
        ⟨rfl, hd.bits.symm.trans hd₂.bits, hd.endian.symm.trans hd₂.endian, hd.memory.symm.trans hd₂.memory, hp.trans hp₂.symm⟩
      rw [x86Code_anywhere hc₂ hx]
      exact h
  have hinsert : ∀ entry, (∀ program, entry = some program → ∀ c₂, SameDecoder base c₂ → c₂.prefixes = key.prefixes →
      (x86Code globals avx c₂ key.opcode key.name (operandsOf key)).map finish = .ok program) →
      MemoSound globals avx base operandsOf finish (memo.insert key entry) := by
    intro entry he k program hk c₂ hd₂ hp₂
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hk
    split at hk
    · rename_i hb
      have hb' : key = k := by simpa using hb
      subst hb'
      exact he program (by simpa using hk) c₂ hd₂ hp₂
    · exact hm k program (by simpa using hk) c₂ hd₂ hp₂
  rw [hstep]
  simp only [x86MemoStep]
  cases worth with
  | false => exact ⟨by simp, hm⟩
  | true =>
    simp only [↓reduceIte]
    cases hk : memo.get? key with
    | some entry =>
      refine ⟨fun program hp' => hm key program ?_ c hd hp, hm⟩
      rw [hk]
      exact congrArg some hp'
    | none =>
      simp only
      split
      · rename_i program hok
        refine ⟨fun p hp' => hany hok c hd hp |>.trans (congrArg _ (Option.some.inj hp')), hinsert _ fun p hp' => ?_⟩
        rw [← Option.some.inj hp']
        exact hany hok
      · exact ⟨by simp, hinsert _ (by simp)⟩

end Bap.Proofs.Target
