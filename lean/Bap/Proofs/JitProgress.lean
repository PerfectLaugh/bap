import Lean
import Bap.Primus.Lifted
import Bap.Proofs.Primus

open Lean Elab Command in
/-- Bring private declarations of module `mod`, namespace `ns`, into scope by short name. -/
local elab "open_private " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

/-! **What lowers has a result in the interpreter.** `Bap.Primus.Lifted` lowers what reads a variable it has not written
as an input of the run, and `definitelyWritten` says what a block has written on every way to it. Here is why that is
enough: a program that lowers, on an environment with its inputs bound at the widths of their variables and its memory
bound as memory, ends in the interpreter with a result, or for want of fuel, and in no other error. -/

namespace Bap.Proofs.Jit

open Bap.Primus.Lifted Bap.Proofs.Primus
open_private Bap.Primus.Lifted Bap.Primus.Lifted Lowering Lowering.ops Lowering.layout Lowering.nextSlot Lowering.memory
  Lowering.effectSlot Lowering.nextLabel Lowering.next Lowering.written Lowering.outputs Lowering.inputs Lowering.push Lowering.withWritten
  Operand Operand.slot Operand.width lowerExp lowerMove lowerStmt lowerStatements setEffect temporary jumpConstant jumpSlot immediate useMemory
  useMemoryAt writeVar slot widthOf wrapSafe recordWrite addressOf readVar readsMemory signExtend narrow binaryOp isSigned isComparison
  stmtLeaves programLeaves stmtWrites programWrites writtenAt writesOf writtenStable definitelyWritten closedTarget closedTarget.closed
  blockExit BlockExit BlockExit.direct BlockExit.branch BlockExit.other BlockExit.fall graphEdgeOps freshLabel enterBlock codeSite
  GraphPlan GraphPlan.seed GraphPlan.labels GraphPlan.edges GraphPlan.budget GraphPlan.observed GraphPlan.chained GraphPlan.definite GraphPlan.guarded
  lowerEntry lowerExit lowerBlock lowerBlocks
open_private Bap.Bil.Eval Bap.Bil expectMemory evalUn
open_private Bap.Proofs.Primus Bap.Proofs.Primus obind lookup_bind_same lookup_bind_other

/-- The one error that fuel makes. -/
def fuelError : String := "execution fuel exhausted"

/-- A variable has bits, at the width of its type. -/
def Good (env : Bil.Env) (var : Bap.Var) : Prop :=
  ∃ width, widthOf var = some width ∧ ∃ bits : BitVec width, Bil.lookup env var = .ok (.bits bits)

/-- A variable has memory, with the addresses of its type. -/
def GoodMem (env : Bil.Env) (var : Bap.Var) : Prop :=
  ∃ width, var.typ = .mem width 8 ∧ ∃ cells : Bap.Memory width, Bil.lookup env var = .ok (.memory cells)

/-- What lowering an expression leaves of what the interpreter depends on. -/
structure ExpMono (first second : Lowering) : Prop where
  written : Lowering.written second = Lowering.written first
  inputs : ∀ var ∈ Lowering.inputs first, var ∈ Lowering.inputs second
  memory : ∀ var, Lowering.memory first = some var → Lowering.memory second = some var

theorem ExpMono.refl (lowering : Lowering) : ExpMono lowering lowering := ⟨rfl, fun _ h => h, fun _ h => h⟩

theorem ExpMono.trans {a b c : Lowering} (h1 : ExpMono a b) (h2 : ExpMono b c) : ExpMono a c :=
  ⟨by rw [h2.written, h1.written], fun v hv => h2.inputs v (h1.inputs v hv), fun v hv => h2.memory v (h1.memory v hv)⟩

/-- What an expression needs of an environment. -/
structure ExpReady (env : Bil.Env) (first second : Lowering) : Prop where
  written : ∀ var ∈ Lowering.written first, Good env var
  inputs : ∀ var ∈ Lowering.inputs second, Good env var
  memory : ∀ var, Lowering.memory second = some var → GoodMem env var

def ExpOK (exp : Bil.Exp) : Prop :=
  ∀ {first second : Lowering} {operand : Operand}, lowerExp first exp = some (second, operand) →
    ExpMono first second ∧ ∀ env, ExpReady env first second → ∃ bits : BitVec (Operand.width operand), Bil.evalExp env exp = .ok (.bits bits)

theorem ExpReady.before {env : Bil.Env} {a b c : Lowering} (h : ExpReady env a c) (m : ExpMono b c) : ExpReady env a b :=
  ⟨h.written, fun v hv => h.inputs v (m.inputs v hv), fun v hv => h.memory v (m.memory v hv)⟩

theorem ExpReady.after {env : Bil.Env} {a b c : Lowering} (h : ExpReady env a c) (m : ExpMono a b) : ExpReady env b c :=
  ⟨by rw [m.written]; exact h.written, h.inputs, h.memory⟩

private theorem bits_asBits {width : Nat} (bits : BitVec width) : Value.asBits (.bits bits) = .ok ⟨width, bits⟩ := rfl

theorem narrow_mono (lowering : Lowering) (width slot : Nat) : ExpMono lowering (narrow lowering width slot) := by
  unfold narrow
  split <;> exact ⟨rfl, fun _ h => h, fun _ h => h⟩

theorem exp_int {width : Nat} (value : BitVec width) : ExpOK (.int value) := by
  intro first second operand h
  rw [lowerExp] at h
  split at h
  · simp only [temporary, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨rfl, fun _ h => h, fun _ h => h⟩, fun _ _ => ⟨value, rfl⟩⟩
  · simp at h

theorem exp_var (var : Bap.Var) : ExpOK (.var var) := by
  intro first second operand h
  rw [lowerExp] at h
  obtain ⟨width, hw, h⟩ := obind h
  obtain ⟨⟨result, index⟩, hrv, h⟩ := obind h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hslot : ∀ first : Lowering, Lowering.written (slot first var).1 = Lowering.written first ∧
      Lowering.inputs (slot first var).1 = Lowering.inputs first ∧ Lowering.memory (slot first var).1 = Lowering.memory first := by
    intro first
    unfold slot
    split <;> exact ⟨rfl, rfl, rfl⟩
  obtain ⟨h1, h2, h3⟩ := hslot first
  simp only [readVar, hw, bind, Option.bind_some] at hrv
  have key : ExpMono first result ∧ (var ∈ Lowering.written first ∨ var ∈ Lowering.inputs result) := by
    split at hrv
    · next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hrv
      obtain ⟨rfl, -⟩ := hrv
      refine ⟨⟨h1, fun v hv => by rw [h2]; exact hv, fun v hv => by rw [h3]; exact hv⟩, ?_⟩
      simp only [Bool.or_eq_true, List.contains_iff_mem] at hc
      rw [h1, h2] at hc
      rw [h2]
      exact hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at hrv
      obtain ⟨rfl, -⟩ := hrv
      refine ⟨⟨h1, fun v hv => ?_, fun v hv => by rw [← hv]; exact h3⟩, Or.inr ?_⟩
      · simp only [List.mem_append]; left; rw [h2]; exact hv
      · simp
  refine ⟨key.1, fun env ready => ?_⟩
  have hg : Good env var := by
    rcases key.2 with hm | hm
    · exact ready.written _ hm
    · exact ready.inputs _ hm
  obtain ⟨w, hw', bits, hl⟩ := hg
  rw [hw] at hw'
  simp only [Option.some.injEq] at hw'
  subst hw'
  exact ⟨bits, hl⟩

theorem useMemoryAt_spec {first second : Lowering} {var : Bap.Var} {size : Nat} (h : useMemoryAt first var size = some second) :
    ∃ m, var.typ = .mem m 8 ∧ ExpMono first second ∧ Lowering.memory second = some var := by
  unfold useMemoryAt at h
  split at h
  · unfold useMemory at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      next hne w _ =>
        exact ⟨_, by assumption, ⟨rfl, fun _ h => h, by intro v hv; simp_all⟩, rfl⟩
    · next w _ existing _ _ =>
      split at h
      · next he =>
        simp only [Option.some.injEq] at h
        subst h
        have : existing = var := by simpa using he
        subst this
        exact ⟨_, by assumption, ExpMono.refl _, by assumption⟩
      · simp at h
    · simp at h
  · simp at h

theorem exp_load (memory address : Bil.Exp) (endian : Endian) (size : Nat) (ih : ExpOK address) : ExpOK (.load memory address endian size) := by
  intro first second operand h
  have hmem : ∃ var, memory = .var var := by
    cases memory
    case var v => exact ⟨v, rfl⟩
    all_goals (rw [lowerExp] at h <;> simp_all)
  obtain ⟨var, rfl⟩ := hmem
  rw [lowerExp] at h
  obtain ⟨var', hvar, h⟩ := obind h
  obtain rfl : var = var' := by simpa using hvar
  obtain ⟨l1, hl1, h⟩ := obind h
  obtain ⟨⟨l2, addr⟩, hl2, h⟩ := obind h
  dsimp only at h
  split at h
  · simp at h
  · next hc =>
    simp only [temporary, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨m, value⟩ := useMemoryAt_spec hl1
    obtain ⟨htyp, m1, hl⟩ := value
    obtain ⟨m2, ev⟩ := ih hl2
    have mono : ExpMono l1 l2 := m2
    refine ⟨(m1.trans m2).trans ⟨rfl, fun _ h => h, fun _ h => h⟩, fun env ready => ?_⟩
    obtain ⟨width, hty, cells, hcells⟩ := ready.memory var (m2.memory _ hl)
    rw [htyp] at hty
    simp only [Typ.mem.injEq, and_true] at hty
    subst hty
    obtain ⟨bits, hb⟩ := ev env (ready.after m1 |>.before ⟨rfl, fun _ h => h, fun _ h => h⟩)
    have haddr : Operand.width addr = m := by
      simp only [Bool.or_eq_true, not_or, decide_eq_true_eq, gt_iff_lt, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      simp only [addressOf, htyp] at hc
      simpa using (show m = Operand.width addr by simpa using hc.2).symm
    subst haddr
    refine ⟨Memory.read cells bits endian size, ?_⟩
    simp [Bil.evalExp, hcells, hb, bind, Except.bind, expectMemory, bits_asBits]

theorem exp_un (op : Bil.UnOp) (value : Bil.Exp) (ih : ExpOK value) : ExpOK (.un op value) := by
  intro first second operand h
  rw [lowerExp] at h
  obtain ⟨⟨l1, v⟩, h1, h⟩ := obind h
  simp only [temporary] at h
  obtain ⟨m, ev⟩ := ih h1
  cases op <;> simp only [bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨hs, rfl⟩ := h
  all_goals
    have last : ExpMono l1 second := by subst hs; refine ExpMono.trans ?_ (narrow_mono _ _ _); exact ⟨rfl, fun _ h => h, fun _ h => h⟩
    refine ⟨m.trans last, fun env ready => ?_⟩
    obtain ⟨bits, hb⟩ := ev env (ready.before last)
  · exact ⟨-bits, by simp [Bil.evalExp, hb, bind, Except.bind, bits_asBits, evalUn]⟩
  · exact ⟨~~~bits, by simp [Bil.evalExp, hb, bind, Except.bind, bits_asBits, evalUn]⟩

theorem exp_ite (condition yes no : Bil.Exp) (ihc : ExpOK condition) (ihy : ExpOK yes) (ihn : ExpOK no) : ExpOK (.ite condition yes no) := by
  intro first second operand h
  rw [lowerExp] at h
  split at h
  · simp at h
  obtain ⟨⟨l1, c⟩, h1, h⟩ := obind h
  obtain ⟨⟨l2, y⟩, h2, h⟩ := obind h
  obtain ⟨⟨l3, n⟩, h3, h⟩ := obind h
  dsimp only at h
  split at h
  · simp at h
  next hc =>
  simp only [temporary, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hs, rfl⟩ := h
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hc
  obtain ⟨mc, ec⟩ := ihc h1
  obtain ⟨my, ey⟩ := ihy h2
  obtain ⟨mn, en⟩ := ihn h3
  have last : ExpMono l3 second := by subst hs; exact ⟨rfl, fun _ h => h, fun _ h => h⟩
  refine ⟨(mc.trans my).trans (mn.trans last), fun env ready => ?_⟩
  have r3 := ready.before last
  have r2 := r3.before mn
  obtain ⟨bc, hbc⟩ := ec env (r2.before my)
  obtain ⟨by', hby⟩ := ey env (r2.after mc)
  obtain ⟨bn, hbn⟩ := en env ((r3.after mc).after my)
  have hcw := hc.1
  obtain ⟨cs, cw⟩ := c
  dsimp only [Operand.width] at hcw
  subst hcw
  obtain ⟨ns, nw⟩ := n
  obtain ⟨ys, yw⟩ := y
  dsimp only [Operand.width] at hc hby hbn ⊢
  obtain rfl : yw = nw := hc.2
  by_cases hb : bc = 1
  · exact ⟨by', by simp [Bil.evalExp, hbc, hb, hby, bind, Except.bind, bits_asBits]⟩
  · exact ⟨bn, by simp [Bil.evalExp, hbc, hbn, bind, Except.bind, bits_asBits]; exact fun h => absurd h hb⟩

theorem exp_extract (high low : Nat) (value : Bil.Exp) (ih : ExpOK value) : ExpOK (.extract high low value) := by
  intro first second operand h
  rw [lowerExp] at h
  obtain ⟨⟨l1, v⟩, h1, h⟩ := obind h
  dsimp only at h
  split at h
  · simp at h
  next hc =>
  simp only [temporary, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hs, rfl⟩ := h
  obtain ⟨m, ev⟩ := ih h1
  have last : ExpMono l1 second := by subst hs; exact ⟨rfl, fun _ h => h, fun _ h => h⟩
  refine ⟨m.trans last, fun env ready => ?_⟩
  obtain ⟨bits, hb⟩ := ev env (ready.before last)
  simp only [Bool.or_eq_true, decide_eq_true_eq, ge_iff_le, not_or, Nat.not_lt, Nat.not_le] at hc
  have hhi : ¬ high ≥ Operand.width v := by omega
  have hlo : ¬ high < low := by omega
  exact ⟨_, by simp [Bil.evalExp, hb, bind, Except.bind, bits_asBits, Word.extract, hhi, hlo]; rfl⟩

private theorem narrow_written (lowering : Lowering) (width slot : Nat) : Lowering.written (narrow lowering width slot) = Lowering.written lowering := by
  unfold narrow; split <;> rfl

private theorem narrow_inputs (lowering : Lowering) (width slot : Nat) : Lowering.inputs (narrow lowering width slot) = Lowering.inputs lowering := by
  unfold narrow; split <;> rfl

private theorem narrow_memory (lowering : Lowering) (width slot : Nat) : Lowering.memory (narrow lowering width slot) = Lowering.memory lowering := by
  unfold narrow; split <;> rfl

/-- What only adds operations and slots leaves all of it. -/
local macro "mono_ops" : tactic =>
  `(tactic| exact ⟨by simp only [narrow_written], fun _ h => by simpa only [narrow_inputs] using h, fun _ h => by simpa only [narrow_memory] using h⟩)

theorem exp_smod (left right : Bil.Exp) (ihl : ExpOK left) (ihr : ExpOK right) : ExpOK (.bin .smod left right) := by
  intro first second operand h
  rw [lowerExp] at h
  obtain ⟨⟨l1, a⟩, h1, h⟩ := obind h
  obtain ⟨⟨l2, b⟩, h2, h⟩ := obind h
  dsimp only at h
  split at h
  · simp at h
  next hc =>
  simp only [temporary, signExtend, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hs, rfl⟩ := h
  obtain ⟨m1, e1⟩ := ihl h1
  obtain ⟨m2, e2⟩ := ihr h2
  have last : ExpMono l2 second := by
    subst hs
    mono_ops
  refine ⟨(m1.trans m2).trans last, fun env ready => ?_⟩
  have r2 := ready.before last
  obtain ⟨x, hx⟩ := e1 env (r2.before m2)
  obtain ⟨y, hy⟩ := e2 env (r2.after m1)
  obtain ⟨aS, aW⟩ := a
  obtain ⟨bS, bW⟩ := b
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hc
  dsimp only [Operand.width] at hc hx hy ⊢
  subst hc
  exact ⟨_, by simp [Bil.evalExp, hx, hy, bind, Except.bind, bits_asBits, Bil.evalBin]; rfl⟩

theorem exp_ashift (left right : Bil.Exp) (ihl : ExpOK left) (ihr : ExpOK right) : ExpOK (.bin .ashift left right) := by
  intro first second operand h
  rw [lowerExp] at h
  obtain ⟨⟨l1, a⟩, h1, h⟩ := obind h
  obtain ⟨⟨l2, b⟩, h2, h⟩ := obind h
  dsimp only at h
  split at h
  · simp at h
  next hc =>
  simp only [temporary, signExtend, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hs, rfl⟩ := h
  obtain ⟨m1, e1⟩ := ihl h1
  obtain ⟨m2, e2⟩ := ihr h2
  have last : ExpMono l2 second := by
    subst hs
    mono_ops
  refine ⟨(m1.trans m2).trans last, fun env ready => ?_⟩
  have r2 := ready.before last
  obtain ⟨x, hx⟩ := e1 env (r2.before m2)
  obtain ⟨y, hy⟩ := e2 env (r2.after m1)
  obtain ⟨aS, aW⟩ := a
  obtain ⟨bS, bW⟩ := b
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hc
  dsimp only [Operand.width] at hc hx hy ⊢
  subst hc
  exact ⟨_, by simp [Bil.evalExp, hx, hy, bind, Except.bind, bits_asBits, Bil.evalBin]; rfl⟩

private theorem evalBin_progress {op : Bil.BinOp} {op' : Jit.BinOp} {width : Nat} (x y : BitVec width) (hop : binaryOp op = some op') :
    ∃ bits : BitVec (if isComparison op' then 1 else width), Bil.evalBin op ⟨width, x⟩ ⟨width, y⟩ = .ok (.bits bits) := by
  cases op <;> simp only [binaryOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop <;>
    (unfold Bil.evalBin; simp only [↓reduceDIte]; exact ⟨_, rfl⟩)

theorem exp_bin (op : Bil.BinOp) (left right : Bil.Exp) (ihl : ExpOK left) (ihr : ExpOK right) : ExpOK (.bin op left right) := by
  by_cases hsmod : op = .smod
  · subst hsmod; exact exp_smod left right ihl ihr
  by_cases hash : op = .ashift
  · subst hash; exact exp_ashift left right ihl ihr
  intro h
  rename_i first second operand
  rw [lowerExp] at h
  rotate_left
  · exact fun e => hsmod e
  · exact fun e => hash e
  obtain ⟨op', hop, h⟩ := obind h
  obtain ⟨⟨l1, a⟩, h1, h⟩ := obind h
  obtain ⟨⟨l2, b⟩, h2, h⟩ := obind h
  dsimp only at h
  split at h
  · simp at h
  next hc =>
  simp only [temporary, signExtend, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hs, rfl⟩ := h
  obtain ⟨m1, e1⟩ := ihl h1
  obtain ⟨m2, e2⟩ := ihr h2
  have last : ExpMono l2 second := by
    subst hs
    split <;> split <;> mono_ops
  refine ⟨(m1.trans m2).trans last, fun env ready => ?_⟩
  have r2 := ready.before last
  obtain ⟨x, hx⟩ := e1 env (r2.before m2)
  obtain ⟨y, hy⟩ := e2 env (r2.after m1)
  obtain ⟨aS, aW⟩ := a
  obtain ⟨bS, bW⟩ := b
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hc
  dsimp only [Operand.width] at hc hx hy ⊢
  subst hc
  obtain ⟨bits, hb⟩ := evalBin_progress x y hop
  exact ⟨bits, by simp only [Bil.evalExp, hx, hy, bind, Except.bind, bits_asBits]; exact hb⟩

theorem exp_cast (kind : Bil.Cast) (width : Nat) (value : Bil.Exp) (ih : ExpOK value) : ExpOK (.cast kind width value) := by
  intro first second operand h
  cases kind with
  | signed =>
    rw [lowerExp] at h
    split at h
    · simp at h
    obtain ⟨⟨l1, v⟩, h1, h⟩ := obind h
    obtain ⟨m, ev⟩ := ih h1
    have key : ExpMono l1 second ∧ Operand.width operand = width := by
      dsimp only at h
      split at h
      · simp only [signExtend, temporary, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, rfl⟩ := h
        subst hs
        exact ⟨by mono_ops, rfl⟩
      · simp only [temporary, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, rfl⟩ := h
        subst hs
        exact ⟨by mono_ops, rfl⟩
    obtain ⟨last, hw⟩ := key
    refine ⟨m.trans last, fun env ready => ?_⟩
    obtain ⟨bits, hb⟩ := ev env (ready.before last)
    rw [hw]
    exact ⟨Word.signed width bits, by simp [Bil.evalExp, hb, bind, Except.bind, bits_asBits]⟩
  | high =>
    rw [lowerExp] at h
    obtain ⟨⟨l1, v⟩, h1, h⟩ := obind h
    obtain ⟨m, ev⟩ := ih h1
    dsimp only at h
    split at h
    · simp at h
    next hc =>
    simp only [temporary, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hs, rfl⟩ := h
    have last : ExpMono l1 second := by subst hs; mono_ops
    refine ⟨m.trans last, fun env ready => ?_⟩
    obtain ⟨bits, hb⟩ := ev env (ready.before last)
    simp only [Bool.or_eq_true, decide_eq_true_eq, gt_iff_lt, not_or, Nat.not_lt] at hc
    have hg : 0 < width ∧ width ≤ Operand.width v := ⟨by omega, hc.2⟩
    exact ⟨_, by simp [Bil.evalExp, hb, bind, Except.bind, bits_asBits, Word.high, hg]; rfl⟩
  | low =>
    rw [lowerExp] at h
    rotate_left
    · simp_all
    · simp_all
    split at h
    · simp at h
    obtain ⟨⟨l1, v⟩, h1, h⟩ := obind h
    obtain ⟨m, ev⟩ := ih h1
    have key : ExpMono l1 second ∧ Operand.width operand = width := by
      dsimp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, rfl⟩ := h
        subst hs
        exact ⟨ExpMono.refl _, rfl⟩
      · simp only [temporary, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, rfl⟩ := h
        subst hs
        exact ⟨by mono_ops, rfl⟩
    obtain ⟨last, hw⟩ := key
    refine ⟨m.trans last, fun env ready => ?_⟩
    obtain ⟨bits, hb⟩ := ev env (ready.before last)
    rw [hw]
    exact ⟨Word.low width bits, by simp [Bil.evalExp, hb, bind, Except.bind, bits_asBits]⟩
  | unsigned =>
    rw [lowerExp] at h
    rotate_left
    · simp_all
    · simp_all
    split at h
    · simp at h
    obtain ⟨⟨l1, v⟩, h1, h⟩ := obind h
    obtain ⟨m, ev⟩ := ih h1
    have key : ExpMono l1 second ∧ Operand.width operand = width := by
      dsimp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, rfl⟩ := h
        subst hs
        exact ⟨ExpMono.refl _, rfl⟩
      · simp only [temporary, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, rfl⟩ := h
        subst hs
        exact ⟨by mono_ops, rfl⟩
    obtain ⟨last, hw⟩ := key
    refine ⟨m.trans last, fun env ready => ?_⟩
    obtain ⟨bits, hb⟩ := ev env (ready.before last)
    rw [hw]
    exact ⟨Word.unsigned width bits, by simp [Bil.evalExp, hb, bind, Except.bind, bits_asBits]⟩

/-- An expression that lowers has the bits of its operand. -/
theorem lowered_exp (exp : Bil.Exp) : ExpOK exp := by
  induction exp with
  | int value => exact exp_int value
  | var var => exact exp_var var
  | load memory address endian size _ iha => exact exp_load memory address endian size iha
  | store memory address value endian size =>
    intro _ _ _ h
    rw [lowerExp] at h <;> simp_all
  | bin op left right ihl ihr => exact exp_bin op left right ihl ihr
  | un op value ih => exact exp_un op value ih
  | cast kind width value ih => exact exp_cast kind width value ih
  | letIn var value body =>
    intro _ _ _ h
    rw [lowerExp] at h <;> simp_all
  | ite condition yes no ihc ihy ihn => exact exp_ite condition yes no ihc ihy ihn
  | extract high low value ih => exact exp_extract high low value ih
  | concat left right =>
    intro _ _ _ h
    rw [lowerExp] at h <;> simp_all
  | unknown message typ =>
    intro _ _ _ h
    rw [lowerExp] at h <;> simp_all

/-! ### Statements -/

private def isNormal : Bil.Effect → Prop
  | .normal => True
  | _ => False

/-- What lowering a statement leaves. What it writes comes after what was written, at most once each. -/
structure StmtMono (first second : Lowering) : Prop where
  written : ∃ extra, Lowering.written second = Lowering.written first ++ extra ∧ extra.Nodup ∧ ∀ var ∈ extra, var ∉ Lowering.written first
  inputs : ∀ var ∈ Lowering.inputs first, var ∈ Lowering.inputs second
  memory : ∀ var, Lowering.memory first = some var → Lowering.memory second = some var

theorem StmtMono.refl (lowering : Lowering) : StmtMono lowering lowering :=
  ⟨⟨[], by simp, by simp, by simp⟩, fun _ h => h, fun _ h => h⟩

theorem StmtMono.trans {a b c : Lowering} (h1 : StmtMono a b) (h2 : StmtMono b c) : StmtMono a c := by
  obtain ⟨e1, r1, n1, d1⟩ := h1.written
  obtain ⟨e2, r2, n2, d2⟩ := h2.written
  refine ⟨⟨e1 ++ e2, by rw [r2, r1, List.append_assoc], ?_, ?_⟩, fun v hv => h2.inputs v (h1.inputs v hv), fun v hv => h2.memory v (h1.memory v hv)⟩
  · rw [List.nodup_append]
    refine ⟨n1, n2, fun x hx y hy he => ?_⟩
    subst he
    exact d2 x hy (by rw [r1]; exact List.mem_append_right _ hx)
  · intro v hv
    rcases List.mem_append.1 hv with h | h
    · exact d1 v h
    · exact fun hm => d2 v h (by rw [r1]; exact List.mem_append_left _ hm)

theorem ExpMono.toStmt {a b : Lowering} (h : ExpMono a b) : StmtMono a b :=
  ⟨⟨[], by rw [h.written]; simp, by simp, by simp⟩, h.inputs, h.memory⟩

/-- What holds of a run of a statement or a program that had a result. -/
structure RanOK (env : Bil.Env) (second : Lowering) (terminated leaves : Bool) (writes : List Bap.Var) (result : Bil.State × Bil.Effect) : Prop where
  frame : ∀ var, Good env var → Good result.1.env var
  frameMem : ∀ var, GoodMem env var → GoodMem result.1.env var
  writes : ∀ var ∈ writes, Good result.1.env var
  written : isNormal result.2 → ∀ var ∈ Lowering.written second, Good result.1.env var
  terminated : terminated = true → ¬ isNormal result.2
  normal : leaves = false → isNormal result.2

/-- An interpreter run has a result, or no fuel. -/
def Progress (run : Except String (Bil.State × Bil.Effect)) (post : Bil.State × Bil.Effect → Prop) : Prop :=
  run = .error fuelError ∨ ∃ result, run = .ok result ∧ post result

theorem ExpReady.before' {env : Bil.Env} {a b c : Lowering} (h : ExpReady env a c) (m : ExpMono b c) : ExpReady env a b := h.before m

theorem ExpReady.frame {env env' : Bil.Env} {a b : Lowering} (h : ExpReady env a b) (hf : ∀ var, Good env var → Good env' var)
    (hm : ∀ var, GoodMem env var → GoodMem env' var) : ExpReady env' a b :=
  ⟨fun v hv => hf v (h.written v hv), fun v hv => hf v (h.inputs v hv), fun v hv => hm v (h.memory v hv)⟩

/-- A variable with a width is not memory. -/
private theorem good_not_mem {var : Bap.Var} {width m c : Nat} (hw : widthOf var = some width) (ht : var.typ = .mem m c) : False := by
  simp [widthOf, ht] at hw

theorem bind_bits_frame {env : Bil.Env} {dst : Bap.Var} {width : Nat} (hw : widthOf dst = some width) (bits : BitVec width) :
    (∀ var, Good env var → Good (Bil.bind env dst (.bits bits)) var) ∧ (∀ var, GoodMem env var → GoodMem (Bil.bind env dst (.bits bits)) var) ∧
      Good (Bil.bind env dst (.bits bits)) dst := by
  have hdst : Good (Bil.bind env dst (.bits bits)) dst := ⟨width, hw, bits, lookup_bind_same _ _ _⟩
  refine ⟨fun var hg => ?_, fun var hg => ?_, hdst⟩
  · by_cases he : var = dst
    · subst he; exact hdst
    · obtain ⟨w, h1, b, h2⟩ := hg
      exact ⟨w, h1, b, by rw [lookup_bind_other he]; exact h2⟩
  · obtain ⟨w, h1, c, h2⟩ := hg
    have he : var ≠ dst := by
      rintro rfl
      exact good_not_mem hw h1
    exact ⟨w, h1, c, by rw [lookup_bind_other he]; exact h2⟩

theorem bind_memory_frame {env : Bil.Env} {dst : Bap.Var} {width c : Nat} (ht : dst.typ = .mem width c) (cells : Bap.Memory width) :
    (∀ var, Good env var → Good (Bil.bind env dst (.memory cells)) var) ∧
      (∀ var, GoodMem env var → GoodMem (Bil.bind env dst (.memory cells)) var) := by
  refine ⟨fun var hg => ?_, fun var hg => ?_⟩
  · obtain ⟨w, h1, b, h2⟩ := hg
    have he : var ≠ dst := by
      rintro rfl
      exact good_not_mem h1 ht
    exact ⟨w, h1, b, by rw [lookup_bind_other he]; exact h2⟩
  · by_cases he : var = dst
    · subst he
      obtain ⟨w, h1, _, _⟩ := hg
      rw [ht] at h1
      simp only [Typ.mem.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact ⟨_, ht, cells, lookup_bind_same _ _ _⟩
    · obtain ⟨w, h1, b, h2⟩ := hg
      exact ⟨w, h1, b, by rw [lookup_bind_other he]; exact h2⟩

theorem writeVar_spec {first second : Lowering} {dst : Bap.Var} {index : Nat} (h : writeVar first dst = some (second, index)) :
    Lowering.inputs second = Lowering.inputs first ∧ Lowering.memory second = Lowering.memory first ∧
      ((Lowering.written second = Lowering.written first ∧ dst ∈ Lowering.written first) ∨
        (Lowering.written second = Lowering.written first ++ [dst] ∧ dst ∉ Lowering.written first)) := by
  have hslot : Lowering.written (slot first dst).1 = Lowering.written first ∧
      Lowering.inputs (slot first dst).1 = Lowering.inputs first ∧ Lowering.memory (slot first dst).1 = Lowering.memory first := by
    unfold slot
    split <;> exact ⟨rfl, rfl, rfl⟩
  obtain ⟨h1, h2, h3⟩ := hslot
  cases hw : widthOf dst with
  | none => simp [writeVar, hw] at h
  | some width =>
    simp only [writeVar, hw, bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨h2, h3, ?_⟩
    by_cases hm : dst ∈ Lowering.written first
    · left
      simp [recordWrite, h1, hm]
    · right
      simp [recordWrite, h1, hm]

/-- A move. -/
theorem lowerMove_progress {first second : Lowering} {dst : Bap.Var} {value : Bil.Exp} (h : lowerMove first dst value = some second) :
    StmtMono first second ∧ ∀ env, ExpReady env first second → ∃ result, Bil.evalExp env value = .ok result ∧
      (∀ var, Good env var → Good (Bil.bind env dst result) var) ∧ (∀ var, GoodMem env var → GoodMem (Bil.bind env dst result) var) ∧
      (∀ var ∈ Lowering.written second, var ∈ Lowering.written first ∨ Good (Bil.bind env dst result) var) ∧ ((widthOf dst).isSome = true → Good (Bil.bind env dst result) dst) := by
  cases hty : dst.typ
  case mem a c =>
    cases value
    case store memory address stored endian size =>
      unfold lowerMove at h
      rw [hty] at h
      dsimp only at h
      have hmem : memory = .var dst := by
        cases memory
        case var v =>
          by_cases he : v = dst
          · rw [he]
          · simp [he] at h
        all_goals simp at h
      subst hmem
      simp only [beq_self_eq_true, ↓reduceIte, bind, Option.bind_some] at h
      obtain ⟨l1, hl1, h⟩ := obind h
      obtain ⟨⟨l2, addr⟩, hl2, h⟩ := obind h
      obtain ⟨⟨l3, sto⟩, hl3, h⟩ := obind h
      dsimp only at h
      split at h
      · simp at h
      next hc =>
      simp only [Option.some.injEq] at h
      obtain ⟨m, htyp, m1, hl⟩ := useMemoryAt_spec hl1
      obtain ⟨m2, e2⟩ := lowered_exp address hl2
      obtain ⟨m3, e3⟩ := lowered_exp stored hl3
      have last : ExpMono l3 second := by subst h; exact ⟨rfl, fun _ h => h, fun _ h => h⟩
      have all := (m1.trans m2).trans (m3.trans last)
      refine ⟨all.toStmt, fun env ready => ?_⟩
      have r3 := ready.before last
      have r2 := r3.before m3
      obtain ⟨width, hty', cells, hcells⟩ := ready.memory dst (last.memory _ (m3.memory _ (m2.memory _ hl)))
      rw [htyp] at hty'
      simp only [Typ.mem.injEq, and_true] at hty'
      subst hty'
      obtain ⟨a', ha⟩ := e2 env (r2.after m1)
      obtain ⟨s', hs⟩ := e3 env ((r3.after m1).after m2)
      simp only [Bool.or_eq_true, not_or] at hc
      obtain ⟨⟨_, hsw⟩, haw⟩ := hc
      have hwa : Operand.width addr = m := by
        simp only [addressOf, htyp] at haw
        have : m = Operand.width addr := by simpa using haw
        exact this.symm
      subst hwa
      obtain ⟨sS, sW⟩ := sto
      dsimp only [Operand.width] at hsw hs
      obtain rfl : sW = size * 8 := by simpa using hsw
      have hwrite : ∃ updated : Bap.Memory (Operand.width addr), Memory.write cells a' s' endian size = .ok updated := by
        exact ⟨_, by simp [Memory.write]; rfl⟩
      obtain ⟨updated, hup⟩ := hwrite
      obtain ⟨f1, f2⟩ := bind_memory_frame (env := env) htyp updated
      refine ⟨.memory updated, ?_, f1, f2, ?_, ?_⟩
      · simp [Bil.evalExp, hcells, ha, hs, hup, bind, Except.bind, expectMemory, bits_asBits]
      · intro var hv
        left
        rw [all.written] at hv
        exact hv
      · intro hw
        simp [widthOf, htyp] at hw
    all_goals
      unfold lowerMove at h
      rw [hty] at h
      simp [widthOf, hty] at h
  all_goals
    have hnot : ∀ a c, dst.typ ≠ .mem a c := by intro a c he; rw [hty] at he; simp at he
    rw [lowerMove] at h
    rotate_left
    · intro a c _ _ _ _ _ he; exact absurd he (hnot a c)
    obtain ⟨width, hw, h⟩ := obind h
    obtain ⟨⟨l1, v⟩, h1, h⟩ := obind h
    dsimp only at h
    split at h
    · simp at h
    next hc =>
    obtain ⟨⟨l2, index⟩, h2, h⟩ := obind h
    simp only [Option.some.injEq] at h
    obtain ⟨m, e⟩ := lowered_exp value h1
    obtain ⟨fi, fm, fw⟩ := writeVar_spec h2
    have m2 : StmtMono l1 l2 := by
      refine ⟨?_, fun x hx => by rw [fi]; exact hx, fun x hx => by rw [fm]; exact hx⟩
      rcases fw with ⟨he, -⟩ | ⟨he, hn⟩
      · exact ⟨[], by rw [he]; simp, by simp, by simp⟩
      · exact ⟨[dst], he, by simp, by simpa using hn⟩
    have m3 : StmtMono l2 second := by subst h; exact ExpMono.toStmt ⟨rfl, fun _ h => h, fun _ h => h⟩
    have hl2 : Lowering.written second = Lowering.written l2 := by subst h; rfl
    refine ⟨m.toStmt.trans (m2.trans m3), fun env ready => ?_⟩
    have ready1 : ExpReady env first l1 :=
      ⟨ready.written, fun x hx => ready.inputs x (m3.inputs x (m2.inputs x hx)), fun x hx => ready.memory x (m3.memory x (m2.memory x hx))⟩
    obtain ⟨bits, hb⟩ := e env ready1
    obtain ⟨vs, vw⟩ := v
    dsimp only [Operand.width] at hc hb
    obtain rfl : vw = width := by simpa using hc
    obtain ⟨f1, f2, f3⟩ := bind_bits_frame (env := env) hw bits
    refine ⟨.bits bits, hb, f1, f2, fun var hv => ?_, fun _ => f3⟩
    rw [hl2] at hv
    rw [m.written] at fw
    rcases fw with ⟨he, -⟩ | ⟨he, -⟩
    · rw [he] at hv; exact Or.inl hv
    · rw [he, List.mem_append] at hv
      rcases hv with hv | hv
      · exact Or.inl hv
      · obtain rfl : var = dst := by simpa using hv
        exact Or.inr f3

private def StmtProgress (stmt : Bil.Stmt) : Prop :=
  ∀ (first second : Lowering) (terminated : Bool), lowerStmt first stmt = some (second, terminated) →
    StmtMono first second ∧ ∀ (fuel : Nat) (state : Bil.State), ExpReady state.env first second →
      Progress (Bil.execStmt fuel state stmt) (RanOK state.env second terminated (stmtLeaves stmt) (stmtWrites stmt))

private def ProgramProgress (program : Bil.Program) : Prop :=
  ∀ (first second : Lowering) (terminated : Bool), lowerStatements first program = some (second, terminated) →
    StmtMono first second ∧ ∀ (fuel : Nat) (state : Bil.State), ExpReady state.env first second →
      Progress (Bil.execProgram fuel state program) (RanOK state.env second terminated (programLeaves program) (programWrites program))

private theorem move_progress (dst : Bap.Var) (value : Bil.Exp) : StmtProgress (.move dst value) := by
  intro first second terminated h
  rw [lowerStmt] at h
  obtain ⟨lowering, hm, h⟩ := obind h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨mono, ok⟩ := lowerMove_progress hm
  refine ⟨mono, fun fuel state ready => ?_⟩
  cases fuel with
  | zero => exact Or.inl (by simp [Bil.execStmt]; rfl)
  | succ fuel =>
    obtain ⟨result, he, f1, f2, f3, f4⟩ := ok state.env ready
    refine Or.inr ⟨({ env := Bil.bind state.env dst result }, .normal), ?_, ?_⟩
    · simp [Bil.execStmt, Bil.execExp, he, bind, Except.bind]
    · refine ⟨f1, f2, ?_, ?_, ?_, ?_⟩
      · intro var hv
        simp only [stmtWrites] at hv
        split at hv
        · next hs =>
          simp only [List.mem_singleton] at hv
          subst hv
          exact f4 hs
        · simp at hv
      · intro _ var hv
        rcases f3 var hv with hv | hg
        · exact f1 _ (ready.written _ hv)
        · exact hg
      · simp
      · intro _; trivial

private theorem jmp_progress (target : Bil.Exp) : StmtProgress (.jmp target) := by
  intro first second terminated h
  have key : StmtMono first second ∧ terminated = true ∧ ∀ env, ExpReady env first second → ∃ (width : Nat) (bits : BitVec width), Bil.evalExp env target = .ok (.bits bits) := by
    cases hc : target
    case int value =>
      subst hc
      rw [lowerStmt] at h
      split at h
      · simp only [jumpConstant, setEffect, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, rfl⟩ := h
        refine ⟨?_, rfl, fun _ _ => ⟨_, value, rfl⟩⟩
        subst hs
        split <;> exact ExpMono.toStmt ⟨rfl, fun _ h => h, fun _ h => h⟩
      · simp at h
    all_goals
      subst hc
      rw [lowerStmt] at h
      rotate_left
      · intro _ _ he; simp at he
      obtain ⟨⟨l1, v⟩, h1, h⟩ := obind h
      simp only [jumpSlot, setEffect, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs, rfl⟩ := h
      obtain ⟨m, e⟩ := lowered_exp _ h1
      have last : ExpMono l1 second := by
        subst hs
        split <;> exact ⟨rfl, fun _ h => h, fun _ h => h⟩
      refine ⟨(m.trans last).toStmt, rfl, fun env ready => ?_⟩
      obtain ⟨bits, hb⟩ := e env (ready.before last)
      exact ⟨_, bits, hb⟩
  obtain ⟨mono, rfl, ok⟩ := key
  refine ⟨mono, fun fuel state ready => ?_⟩
  cases fuel with
  | zero => exact Or.inl (by simp [Bil.execStmt]; rfl)
  | succ fuel =>
    obtain ⟨width, bits, hb⟩ := ok state.env ready
    refine Or.inr ⟨(state, .jump bits), ?_, fun _ h => h, fun _ h => h, by simp [stmtWrites], fun h => h.elim, fun _ h => h, by simp [stmtLeaves]⟩
    simp [Bil.execStmt, Bil.execExp, hb, bind, Except.bind, bits_asBits]

private theorem program_nil_progress : ProgramProgress [] := by
  intro first second terminated h
  rw [lowerStatements] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨StmtMono.refl _, fun fuel state ready => ?_⟩
  cases fuel with
  | zero => exact Or.inl (by simp [Bil.execProgram]; rfl)
  | succ fuel =>
    exact Or.inr ⟨(state, .normal), by simp [Bil.execProgram], fun _ h => h, fun _ h => h, by simp [programWrites], fun _ v hv => ready.written v hv,
      by simp, fun _ => trivial⟩

private theorem cons_error {fuel : Nat} {state : Bil.State} {stmt : Bil.Stmt} {rest : Bil.Program} {error : String}
    (h : Bil.execStmt fuel state stmt = .error error) : Bil.execProgram (fuel + 1) state (stmt :: rest) = .error error := by
  simp [Bil.execProgram, h, bind, Except.bind]

private theorem cons_normal {fuel : Nat} {state next : Bil.State} {stmt : Bil.Stmt} {rest : Bil.Program}
    (h : Bil.execStmt fuel state stmt = .ok (next, .normal)) :
    Bil.execProgram (fuel + 1) state (stmt :: rest) = Bil.execProgram fuel next rest := by
  simp [Bil.execProgram, h, bind, Except.bind]

private theorem cons_other {fuel : Nat} {state next : Bil.State} {stmt : Bil.Stmt} {rest : Bil.Program} {effect : Bil.Effect}
    (h : Bil.execStmt fuel state stmt = .ok (next, effect)) (hn : ¬ isNormal effect) :
    Bil.execProgram (fuel + 1) state (stmt :: rest) = .ok (next, effect) := by
  cases effect with
  | normal => exact absurd trivial hn
  | _ => simp [Bil.execProgram, h, bind, Except.bind]

private theorem program_cons_progress {stmt : Bil.Stmt} {rest : Bil.Program} (hs : StmtProgress stmt) (hr : ProgramProgress rest) :
    ProgramProgress (stmt :: rest) := by
  intro first second terminated h
  rw [lowerStatements] at h
  obtain ⟨⟨mid, stop⟩, h1, h⟩ := obind h
  obtain ⟨m1, ok1⟩ := hs first mid stop h1
  dsimp only at h
  split at h
  · next hstop =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨m1, fun fuel state ready => ?_⟩
    cases fuel with
    | zero => exact Or.inl (by simp [Bil.execProgram]; rfl)
    | succ fuel =>
      rcases ok1 fuel state ready with he | ⟨⟨next, effect⟩, he, ran⟩
      · exact Or.inl (cons_error he)
      · have hn : ¬ isNormal effect := ran.terminated hstop
        have hl : stmtLeaves stmt = true := by
          cases hc : stmtLeaves stmt with
          | true => rfl
          | false => exact absurd (ran.normal hc) hn
        refine Or.inr ⟨(next, effect), cons_other he hn, ran.frame, ran.frameMem, ?_, fun h => absurd h hn, fun _ => hn, ?_⟩
        · intro var hv
          simp only [programWrites, hl, ↓reduceIte, List.append_nil] at hv
          exact ran.writes var hv
        · simp [programLeaves, hl]
  · next hstop =>
    obtain ⟨m2, ok2⟩ := hr mid second terminated h
    refine ⟨m1.trans m2, fun fuel state ready => ?_⟩
    have ready1 : ExpReady state.env first mid :=
      ⟨ready.written, fun v hv => ready.inputs v (m2.inputs v hv), fun v hv => ready.memory v (m2.memory v hv)⟩
    cases fuel with
    | zero => exact Or.inl (by simp [Bil.execProgram]; rfl)
    | succ fuel =>
      rcases ok1 fuel state ready1 with he | ⟨⟨next, effect⟩, he, ran⟩
      · exact Or.inl (cons_error he)
      · by_cases hn : isNormal effect
        · obtain rfl : effect = .normal := by cases effect <;> first | rfl | exact hn.elim
          have ready2 : ExpReady next.env mid second :=
            ⟨ran.written hn, fun v hv => ran.frame v (ready.inputs v hv), fun v hv => ran.frameMem v (ready.memory v hv)⟩
          rcases ok2 fuel next ready2 with he2 | ⟨result, he2, ran2⟩
          · exact Or.inl (by rw [cons_normal he]; exact he2)
          · refine Or.inr ⟨result, by rw [cons_normal he]; exact he2, fun v hv => ran2.frame v (ran.frame v hv),
              fun v hv => ran2.frameMem v (ran.frameMem v hv), ?_, ran2.written, ran2.terminated, ?_⟩
            · intro var hv
              simp only [programWrites, List.mem_append] at hv
              rcases hv with hv | hv
              · exact ran2.frame _ (ran.writes _ hv)
              · split at hv
                · simp at hv
                · exact ran2.writes _ hv
            · intro hl
              simp only [programLeaves, Bool.or_eq_false_iff] at hl
              exact ran2.normal hl.2
        · have hl : stmtLeaves stmt = true := by
            cases hc : stmtLeaves stmt with
            | true => rfl
            | false => exact absurd (ran.normal hc) hn
          refine Or.inr ⟨(next, effect), cons_other he hn, ran.frame, ran.frameMem, ?_, fun h => absurd h hn, fun _ => hn, ?_⟩
          · intro var hv
            simp only [programWrites, hl, ↓reduceIte, List.append_nil] at hv
            exact ran.writes var hv
          · simp [programLeaves, hl]

private theorem subset_of_length {yes no : List Bap.Var} (hy : yes.Nodup) (hs : yes ⊆ no) (hl : no.length ≤ yes.length) : no ⊆ yes := by
  induction yes generalizing no with
  | nil =>
    obtain rfl : no = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    exact fun _ h => h
  | cons a t ih =>
    have ha : a ∈ no := hs List.mem_cons_self
    have hn := List.nodup_cons.1 hy
    have hsub : t ⊆ no.erase a := by
      intro v hv
      have hne : v ≠ a := fun he => hn.1 (he ▸ hv)
      exact (List.mem_erase_of_ne hne).2 (hs (List.mem_cons_of_mem _ hv))
    have hlen : (no.erase a).length ≤ t.length := by
      rw [List.length_erase_of_mem ha]
      simp only [List.length_cons] at hl
      omega
    have hback := ih hn.2 hsub hlen
    intro v hv
    by_cases he : v = a
    · subst he; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hback ((List.mem_erase_of_ne he).2 hv))

/-- Two lists of what was written, both from the same on, with no element twice after it, where all of the first is in
the second and they are as long: all of the second is in the first. -/
private theorem written_same {initial yes no : List Bap.Var} (hy : yes.Nodup) (hdy : ∀ v ∈ yes, v ∉ initial)
    (hlen : (initial ++ yes).length = (initial ++ no).length) (hsub : ∀ v ∈ initial ++ yes, v ∈ initial ++ no) :
    ∀ v ∈ initial ++ no, v ∈ initial ++ yes := by
  have hs : yes ⊆ no := by
    intro v hv
    rcases List.mem_append.1 (hsub v (List.mem_append_right _ hv)) with h | h
    · exact absurd h (hdy v hv)
    · exact h
  have hl : no.length ≤ yes.length := by
    simp only [List.length_append] at hlen
    omega
  have hback := subset_of_length hy hs hl
  intro v hv
  rcases List.mem_append.1 hv with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (hback h)

private theorem setEffect_fields (lowering : Lowering) (value : UInt64) :
    Lowering.written (setEffect lowering value).1 = Lowering.written lowering ∧ Lowering.inputs (setEffect lowering value).1 = Lowering.inputs lowering ∧
      Lowering.memory (setEffect lowering value).1 = Lowering.memory lowering := by
  unfold setEffect
  split <;> exact ⟨rfl, rfl, rfl⟩

private theorem ifElse_progress {condition : Bil.Exp} {yes no : Bil.Program} (hy : ProgramProgress yes) (hn : ProgramProgress no) :
    StmtProgress (.ifElse condition yes no) := by
  intro first second terminated h
  rw [lowerStmt] at h
  obtain ⟨⟨mid, operand⟩, h1, h⟩ := obind h
  have hw : Operand.width operand = 1 := by
    by_cases hc : Operand.width operand = 1
    · exact hc
    · simp [hc] at h
  simp only [hw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨⟨yesEnd, yesDone⟩, hyes, h⟩ := obind h
  obtain ⟨⟨noEnd, noDone⟩, hno, h⟩ := obind h
  split at h
  · simp at h
  next hcheck =>
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hs, rfl⟩ := h
  obtain ⟨mc, ec⟩ := lowered_exp condition h1
  obtain ⟨my, oky⟩ := hy _ _ _ hyes
  obtain ⟨mn, okn⟩ := hn _ _ _ hno
  obtain ⟨Y, ry, ny, dy⟩ := my.written
  obtain ⟨N, rn, nn, dn⟩ := mn.written
  have ry' : Lowering.written yesEnd = Lowering.written first ++ Y := by rw [ry, mc.written]
  have rn' : Lowering.written noEnd = Lowering.written first ++ N := rn.trans (by rw [mc.written])
  have rs : Lowering.written second = Lowering.written noEnd := by rw [← hs]
  have is : ∀ v ∈ Lowering.inputs noEnd, v ∈ Lowering.inputs second := by rw [← hs]; exact fun _ h => h
  have ms : ∀ v, Lowering.memory noEnd = some v → Lowering.memory second = some v := by rw [← hs]; exact fun _ h => h
  have dy' : ∀ v ∈ Y, v ∉ Lowering.written first := by rw [← mc.written]; exact dy
  have mono : StmtMono first second := by
    refine ⟨⟨N, by rw [rs, rn'], nn, by intro v hv; have := dn v hv; rwa [show _ = Lowering.written first from mc.written] at this⟩, ?_, ?_⟩
    · exact fun v hv => is v (mn.inputs v (my.inputs v (mc.inputs v hv)))
    · exact fun v hv => ms v (mn.memory v (my.memory v (mc.memory v hv)))
  refine ⟨mono, fun fuel state ready => ?_⟩
  have hsub : ∀ v ∈ Lowering.written first ++ Y, v ∈ Lowering.written first ++ N := by
    intro v hv
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, Bool.not_eq_true', not_or, Decidable.not_not, not_exists, not_and, Bool.not_eq_false, List.contains_iff_mem] at hcheck
    have := hcheck.2 v (by rw [ry']; exact hv)
    rwa [rn'] at this
  have hlen : (Lowering.written first ++ Y).length = (Lowering.written first ++ N).length := by
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hcheck
    rw [← ry', ← rn']
    exact hcheck.1
  have hback := written_same ny dy' hlen hsub
  cases fuel with
  | zero => exact Or.inl (by simp [Bil.execStmt]; rfl)
  | succ fuel =>
    have rc : ExpReady state.env first mid :=
      ⟨ready.written, fun v hv => ready.inputs v (is v (mn.inputs v (my.inputs v hv))), fun v hv => ready.memory v (ms v (mn.memory v (my.memory v hv)))⟩
    obtain ⟨bits, hb⟩ := ec state.env rc
    obtain ⟨cS, cW⟩ := operand
    dsimp only [Operand.width] at hw hb
    subst hw
    have heval : Bil.execStmt (fuel + 1) state (.ifElse condition yes no) = Bil.execProgram fuel state (if bits = 1 then yes else no) := by
      simp [Bil.execStmt, Bil.execExp, hb, bind, Except.bind, bits_asBits]
    rw [heval]
    by_cases hbit : bits = 1
    · rw [ite_eq_left hbit]
      rcases oky fuel state ⟨by rw [show _ = Lowering.written first from mc.written]; exact ready.written, fun v hv => ready.inputs v (is v (mn.inputs v hv)), fun v hv => ready.memory v (ms v (mn.memory v hv))⟩ with he | ⟨result, he, ran⟩
      · exact Or.inl he
      · refine Or.inr ⟨result, he, ran.frame, ran.frameMem, ?_, ?_, ?_, ?_⟩
        · intro v hv
          simp only [stmtWrites, List.mem_filter] at hv
          exact ran.writes v hv.1
        · intro hnm v hv
          rw [rs, rn'] at hv
          exact ran.written hnm v (by rw [ry']; exact hback v hv)
        · intro ht
          simp only [Bool.and_eq_true] at ht
          exact ran.terminated ht.1
        · intro hl
          simp only [stmtLeaves, Bool.or_eq_false_iff] at hl
          exact ran.normal hl.1
    · rw [ite_eq_right hbit]
      rcases okn fuel state ⟨by intro v hv; exact ready.written v (by rw [show _ = Lowering.written first from mc.written] at hv; exact hv), fun v hv => ready.inputs v (is v hv), fun v hv => ready.memory v (ms v hv)⟩ with he | ⟨result, he, ran⟩
      · exact Or.inl he
      · refine Or.inr ⟨result, he, ran.frame, ran.frameMem, ?_, ?_, ?_, ?_⟩
        · intro v hv
          simp only [stmtWrites, List.mem_filter, List.contains_iff_mem] at hv
          exact ran.writes v hv.2
        · intro hnm v hv
          rw [rs] at hv
          exact ran.written hnm v hv
        · intro ht
          simp only [Bool.and_eq_true] at ht
          exact ran.terminated ht.2
        · intro hl
          simp only [stmtLeaves, Bool.or_eq_false_iff] at hl
          exact ran.normal hl.2

private theorem while_progress {condition : Bil.Exp} {body : Bil.Program} (hb : ProgramProgress body) : StmtProgress (.while condition body) := by
  intro first second terminated h
  rw [lowerStmt] at h
  simp only [temporary] at h
  obtain ⟨⟨mid, operand⟩, h1, h⟩ := obind h
  have hw : Operand.width operand = 1 := by
    by_cases hc : Operand.width operand = 1
    · exact hc
    · simp [hc] at h
  simp only [hw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨⟨bodyEnd, bodyDone⟩, hbody, h⟩ := obind h
  split at h
  · simp at h
  next hcheck =>
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hs, rfl⟩ := h
  obtain ⟨mc, ec⟩ := lowered_exp condition h1
  obtain ⟨mb, okb⟩ := hb _ _ _ hbody
  obtain ⟨E, re, ne, de⟩ := mb.written
  have rs : Lowering.written second = Lowering.written bodyEnd := by rw [← hs]; exact (setEffect_fields _ _).1
  have is : Lowering.inputs second = Lowering.inputs bodyEnd := by rw [← hs]; exact (setEffect_fields _ _).2.1
  have ms : Lowering.memory second = Lowering.memory bodyEnd := by rw [← hs]; exact (setEffect_fields _ _).2.2
  have rm : Lowering.written mid = Lowering.written first := by rw [mc.written]
  have hnone : E = [] := by
    cases E with
    | nil => rfl
    | cons x rest =>
      exfalso
      have hx : x ∈ Lowering.written bodyEnd := by rw [re]; simp
      simp only [List.any_eq_true, Bool.not_eq_true', not_exists, not_and, Bool.not_eq_false, List.contains_iff_mem] at hcheck
      exact de x (by simp) (hcheck x hx)
  subst hnone
  have rb : Lowering.written bodyEnd = Lowering.written first := by rw [re, List.append_nil]; exact rm
  have mono : StmtMono first second := by
    refine ⟨⟨[], by rw [rs, rb]; simp, by simp, by simp⟩, fun v hv => ?_, fun v hv => ?_⟩
    · rw [is]; exact mb.inputs v (mc.inputs v hv)
    · rw [ms]; exact mb.memory v (mc.memory v hv)
  refine ⟨mono, ?_⟩
  obtain ⟨cS, cW⟩ := operand
  dsimp only [Operand.width] at hw ec
  subst hw
  intro fuel
  induction fuel with
  | zero => exact fun _ _ => Or.inl (by simp [Bil.execStmt]; rfl)
  | succ fuel ih =>
    intro state ready
    obtain ⟨bits, hbits⟩ := ec state.env ⟨ready.written, fun v hv => ready.inputs v (by rw [is]; exact mb.inputs v hv), fun v hv => ready.memory v (by rw [ms]; exact mb.memory v hv)⟩
    by_cases hbit : bits = 1
    · rcases okb fuel state ⟨by rw [show _ = Lowering.written mid from rfl, rm]; exact ready.written, fun v hv => ready.inputs v (by rw [is]; exact hv), fun v hv => ready.memory v (by rw [ms]; exact hv)⟩ with he | ⟨⟨next, effect⟩, he, ran⟩
      · refine Or.inl ?_
        simp [Bil.execStmt, Bil.execExp, hbits, hbit, he, bind, Except.bind, bits_asBits]
      · by_cases hn : isNormal effect
        · obtain rfl : effect = .normal := by cases effect <;> first | rfl | exact hn.elim
          have ready2 : ExpReady next.env first second := ready.frame ran.frame ran.frameMem
          rcases ih next ready2 with he2 | ⟨result, he2, ran2⟩
          · refine Or.inl ?_
            simp [Bil.execStmt, Bil.execExp, hbits, hbit, he, bind, Except.bind, bits_asBits]
            exact he2
          · refine Or.inr ⟨result, ?_, fun v hv => ran2.frame v (ran.frame v hv), fun v hv => ran2.frameMem v (ran.frameMem v hv), by simp [stmtWrites], ran2.written, by simp, ran2.normal⟩
            simp [Bil.execStmt, Bil.execExp, hbits, hbit, he, bind, Except.bind, bits_asBits]
            exact he2
        · refine Or.inr ⟨(next, effect), ?_, ran.frame, ran.frameMem, by simp [stmtWrites], fun h => absurd h hn, by simp, ?_⟩
          · cases effect with
            | normal => exact absurd trivial hn
            | _ => simp [Bil.execStmt, Bil.execExp, hbits, hbit, he, bind, Except.bind, bits_asBits]
          · intro hl
            exact ran.normal (by simpa [stmtLeaves] using hl)
    · refine Or.inr ⟨(state, .normal), ?_, fun _ h => h, fun _ h => h, by simp [stmtWrites], fun _ v hv => ?_, by simp, fun _ => trivial⟩
      · simp [Bil.execStmt, Bil.execExp, hbits, bind, Except.bind, bits_asBits]
        intro hh
        exact absurd hh hbit
      · rw [rs, rb] at hv
        exact ready.written v hv

private theorem special_progress (message : String) : StmtProgress (.special message) := by
  intro first second terminated h
  rw [lowerStmt] at h
  · simp at h
  all_goals (intros; simp_all)

private theorem cpuExn_progress (number : Nat) : StmtProgress (.cpuExn number) := by
  intro first second terminated h
  rw [lowerStmt] at h
  · simp at h
  all_goals (intros; simp_all)

private theorem lowered_progress : (∀ stmt, StmtProgress stmt) ∧ (∀ program, ProgramProgress program) := by
  have key : ∀ stmt, StmtProgress stmt := fun stmt =>
    @Bil.Stmt.rec StmtProgress ProgramProgress move_progress jmp_progress special_progress (fun _ _ hb => while_progress hb)
      (fun _ _ _ hy hn => ifElse_progress hy hn) cpuExn_progress program_nil_progress (fun _ _ hs hr => program_cons_progress hs hr) stmt
  have keyP : ∀ program, ProgramProgress program := fun program =>
    @Bil.Stmt.rec_1 StmtProgress ProgramProgress move_progress jmp_progress special_progress (fun _ _ hb => while_progress hb)
      (fun _ _ _ hy hn => ifElse_progress hy hn) cpuExn_progress program_nil_progress (fun _ _ hs hr => program_cons_progress hs hr) program
  exact ⟨key, keyP⟩

/-! ### Blocks -/

/-- A closed target is the same value in every environment. -/
theorem closed_evalExp (exp : Bil.Exp) (env : Bil.Env) (h : closedTarget.closed exp = true) :
    Bil.evalExp env exp = Bil.evalExp [] exp := by
  induction exp with
  | int value => rfl
  | bin op left right ihl ihr =>
    simp only [closedTarget.closed, Bool.and_eq_true] at h
    rw [Bil.evalExp, Bil.evalExp, ihl h.1, ihr h.2]
  | un op value ih =>
    simp only [closedTarget.closed] at h
    rw [Bil.evalExp, Bil.evalExp, ih h]
  | cast kind width value ih =>
    simp only [closedTarget.closed] at h
    rw [Bil.evalExp, Bil.evalExp, ih h]
  | _ => simp [closedTarget.closed] at h

/-- A target that a range goes to directly is where the interpreter jumps, in whatever environment it runs. This is what
makes a pc-relative branch an edge of the graph. -/
theorem closedTarget_sound {target : Bil.Exp} {address : Nat} (h : closedTarget target = some address) (env : Bil.Env) :
    ∃ (width : Nat) (value : BitVec width), Bil.evalExp env target = .ok (.bits value) ∧ width ≤ 64 ∧ value.toNat = address := by
  unfold closedTarget at h
  split at h
  · next hc =>
    split at h
    · next width value he =>
      split at h
      · next hw =>
        simp only [Option.some.injEq] at h
        exact ⟨width, value, by rw [closed_evalExp _ _ hc, he], hw, h⟩
      · simp at h
    · simp at h
  · simp at h

theorem snoc_of_getLast? {α : Type} {items : List α} {last : α} (h : items.getLast? = some last) :
    items = items.dropLast ++ [last] := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 h
  simp

/-- `blockExit` goes by the last statement. -/
theorem blockExit_direct {block : Block} {target : Nat} (h : blockExit block = BlockExit.direct target) :
    ∃ exp, block.program = block.program.dropLast ++ [.jmp exp] ∧ closedTarget exp = some target := by
  unfold blockExit at h
  split at h
  · next exp hl =>
    split at h
    · next t ht =>
      injection h with h
      subst h
      exact ⟨exp, snoc_of_getLast? hl, ht⟩
    · cases h
  all_goals first
    | (split at h <;> cases h)
    | cases h

theorem blockExit_branch {block : Block} {condition : Bil.Exp} {yes no : Nat} {falls : Bool}
    (h : blockExit block = BlockExit.branch condition yes no falls) :
    ∃ yesExp, closedTarget yesExp = some yes ∧
      ((falls = true ∧ no = block.next ∧ block.program = block.program.dropLast ++ [.ifElse condition [.jmp yesExp] []]) ∨
       (falls = false ∧ ∃ noExp, closedTarget noExp = some no ∧
         block.program = block.program.dropLast ++ [.ifElse condition [.jmp yesExp] [.jmp noExp]])) := by
  unfold blockExit at h
  split at h
  · split at h <;> cases h
  · next cond yesExp hl =>
    split at h
    · next t ht =>
      injection h with h1 h2 h3 h4
      subst h1 h2 h3 h4
      exact ⟨yesExp, ht, Or.inl ⟨rfl, rfl, snoc_of_getLast? hl⟩⟩
    · cases h
  · next cond yesExp noExp hl =>
    split at h
    · next t f ht hf =>
      injection h with h1 h2 h3 h4
      subst h1 h2 h3 h4
      exact ⟨yesExp, ht, Or.inr ⟨rfl, noExp, hf, snoc_of_getLast? hl⟩⟩
    · cases h
  all_goals cases h

/-- What a run has at its end, whichever it is. -/
structure EndOK (env : Bil.Env) (writes : List Bap.Var) (result : Bil.State × Bil.Effect) : Prop where
  frame : ∀ var, Good env var → Good result.1.env var
  frameMem : ∀ var, GoodMem env var → GoodMem result.1.env var
  writes : ∀ var ∈ writes, Good result.1.env var

/-- A program with its last statement apart, where what comes before it does not end the lowering. -/
theorem snoc_progress (y : Bil.Stmt) (xs : Bil.Program) {first second final : Lowering}
    (h : lowerStatements first xs = some (second, false))
    (hlast : ∀ (fuel : Nat) (state : Bil.State), ExpReady state.env second final → Progress (Bil.execStmt fuel state y) (EndOK state.env (stmtWrites y)))
    (hi : ∀ var ∈ Lowering.inputs second, var ∈ Lowering.inputs final) (hm : ∀ var, Lowering.memory second = some var → Lowering.memory final = some var)
    (fuel : Nat) (state : Bil.State) (ready : ExpReady state.env first final) :
    Progress (Bil.execProgram fuel state (xs ++ [y])) (EndOK state.env (programWrites (xs ++ [y]))) := by
  induction xs generalizing first fuel state with
  | nil =>
    rw [lowerStatements] at h
    simp only [Option.some.injEq, Prod.mk.injEq, and_true] at h
    subst h
    cases fuel with
    | zero => exact Or.inl (by simp [Bil.execProgram]; rfl)
    | succ fuel =>
      rcases hlast fuel state ready with he | ⟨⟨next, effect⟩, he, ran⟩
      · exact Or.inl (cons_error he)
      · have hw : programWrites [y] = stmtWrites y := by simp [programWrites]
        rw [List.nil_append, hw]
        by_cases hn : isNormal effect
        · obtain rfl : effect = .normal := by cases effect <;> first | rfl | exact hn.elim
          rw [Progress, cons_normal he]
          cases fuel with
          | zero => exact Or.inl (by simp [Bil.execProgram]; rfl)
          | succ fuel => exact Or.inr ⟨(next, .normal), by simp [Bil.execProgram], ran⟩
        · exact Or.inr ⟨(next, effect), cons_other he hn, ran⟩
  | cons x rest ih =>
    rw [lowerStatements] at h
    obtain ⟨⟨mid, stop⟩, h1, h⟩ := obind h
    obtain ⟨m1, ok1⟩ := lowered_progress.1 x first mid stop h1
    dsimp only at h
    split at h
    · simp at h
    next hstop =>
    obtain ⟨m2, _⟩ := lowered_progress.2 rest mid second false h
    cases fuel with
    | zero => exact Or.inl (by simp [Bil.execProgram]; rfl)
    | succ fuel =>
      have ready1 : ExpReady state.env first mid :=
        ⟨ready.written, fun v hv => ready.inputs v (hi v (m2.inputs v hv)), fun v hv => ready.memory v (hm v (m2.memory v hv))⟩
      rw [List.cons_append]
      rcases ok1 fuel state ready1 with he | ⟨⟨next, effect⟩, he, ran⟩
      · exact Or.inl (cons_error he)
      · by_cases hn : isNormal effect
        · obtain rfl : effect = .normal := by cases effect <;> first | rfl | exact hn.elim
          rw [Progress, cons_normal he]
          rcases ih h fuel next ⟨ran.written hn, fun v hv => ran.frame v (ready.inputs v hv), fun v hv => ran.frameMem v (ready.memory v hv)⟩ with he2 | ⟨result, he2, ran2⟩
          · exact Or.inl he2
          · refine Or.inr ⟨result, he2, fun v hv => ran2.frame v (ran.frame v hv), fun v hv => ran2.frameMem v (ran.frameMem v hv), ?_⟩
            intro var hv
            simp only [programWrites, List.mem_append] at hv
            rcases hv with hv | hv
            · exact ran2.frame _ (ran.writes _ hv)
            · split at hv
              · simp at hv
              · exact ran2.writes _ hv
        · have hl : stmtLeaves x = true := by
            cases hc : stmtLeaves x with
            | true => rfl
            | false => exact absurd (ran.normal hc) hn
          refine Or.inr ⟨(next, effect), cons_other he hn, ran.frame, ran.frameMem, ?_⟩
          intro var hv
          simp only [programWrites, hl, ↓reduceIte, List.append_nil] at hv
          exact ran.writes var hv

private theorem jump_closed {exp : Bil.Exp} {target : Nat} (hc : closedTarget exp = some target) (fuel : Nat) (state : Bil.State) :
    Progress (Bil.execStmt fuel state (.jmp exp)) (EndOK state.env (stmtWrites (.jmp exp))) := by
  cases fuel with
  | zero => exact Or.inl (by simp [Bil.execStmt]; rfl)
  | succ fuel =>
    obtain ⟨w, value, he, -, -⟩ := closedTarget_sound hc state.env
    exact Or.inr ⟨(state, .jump value), by simp [Bil.execStmt, Bil.execExp, he, bind, Except.bind, bits_asBits], fun _ h => h, fun _ h => h, by simp [stmtWrites]⟩

private theorem jump_program {exp : Bil.Exp} {target : Nat} (hc : closedTarget exp = some target) (fuel : Nat) (state : Bil.State) :
    Progress (Bil.execProgram fuel state [.jmp exp]) (EndOK state.env []) := by
  cases fuel with
  | zero => exact Or.inl (by simp [Bil.execProgram]; rfl)
  | succ fuel =>
    cases fuel with
    | zero => exact Or.inl (by simp [Bil.execProgram, Bil.execStmt, bind, Except.bind]; rfl)
    | succ fuel =>
      obtain ⟨w, value, hv, -, -⟩ := closedTarget_sound hc state.env
      exact Or.inr ⟨(state, .jump value), by simp [Bil.execProgram, Bil.execStmt, Bil.execExp, hv, bind, Except.bind, bits_asBits], fun _ h => h, fun _ h => h, by simp⟩

/-- What lowering a block leaves. -/
structure BlockMono (first second : Lowering) : Prop where
  inputs : ∀ var ∈ Lowering.inputs first, var ∈ Lowering.inputs second
  memory : ∀ var, Lowering.memory first = some var → Lowering.memory second = some var

theorem BlockMono.trans {a b c : Lowering} (h1 : BlockMono a b) (h2 : BlockMono b c) : BlockMono a c :=
  ⟨fun v hv => h2.inputs v (h1.inputs v hv), fun v hv => h2.memory v (h1.memory v hv)⟩

theorem StmtMono.toBlock {a b : Lowering} (h : StmtMono a b) : BlockMono a b := ⟨h.inputs, h.memory⟩

theorem ExpMono.toBlock {a b : Lowering} (h : ExpMono a b) : BlockMono a b := ⟨h.inputs, h.memory⟩

/-- What only pushes operations. -/
private theorem push_mono (lowering : Lowering) (ops : List Jit.Op) : ExpMono lowering (Lowering.push lowering ops) :=
  ⟨rfl, fun _ h => h, fun _ h => h⟩

theorem lowerExit_progress {plan : GraphPlan} {first second : Lowering} {block : Block} (h : lowerExit plan first block = some second) :
    StmtMono first second ∧ ∀ (fuel : Nat) (state : Bil.State), ExpReady state.env first second →
      Progress (Bil.execProgram fuel state block.program) (EndOK state.env (programWrites block.program)) := by
  unfold lowerExit at h
  split at h
  · next target he =>
    obtain ⟨exp, hprog, hc⟩ := blockExit_direct he
    obtain ⟨⟨lowered, done⟩, h1, h⟩ := obind h
    dsimp only at h
    split at h
    · simp at h
    next hdone =>
    obtain ⟨ops, _, h⟩ := obind h
    simp only [Option.some.injEq] at h
    subst h
    have hd : done = false := by simpa using hdone
    subst hd
    obtain ⟨m1, _⟩ := lowered_progress.2 _ _ _ _ h1
    refine ⟨m1.trans (push_mono lowered ops).toStmt, fun fuel state ready => ?_⟩
    rw [hprog]
    exact snoc_progress (final := Lowering.push lowered ops) (.jmp exp) _ h1 (fun fuel state _ => jump_closed hc fuel state) (fun _ h => h) (fun _ h => h) fuel state ready
  · next condition yes no falls he =>
    obtain ⟨yesExp, hcy, hshape⟩ := blockExit_branch he
    obtain ⟨⟨lowered, done⟩, h1, h⟩ := obind h
    dsimp only at h
    split at h
    · simp at h
    next hdone =>
    obtain ⟨⟨l2, operand⟩, h2, h⟩ := obind h
    dsimp only at h
    split at h
    · simp at h
    next hw =>
    simp only [freshLabel] at h
    obtain ⟨yesOps, _, h⟩ := obind h
    have hd : done = false := by simpa using hdone
    subst hd
    obtain ⟨m1, _⟩ := lowered_progress.2 _ _ _ _ h1
    obtain ⟨mc, ec⟩ := lowered_exp condition h2
    have last : ExpMono l2 second := by
      split at h
      · simp only [bind, Option.bind_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, fun _ h => h, fun _ h => h⟩
      · obtain ⟨noOps, _, h⟩ := obind h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, fun _ h => h, fun _ h => h⟩
    have mono : StmtMono first second := m1.trans (mc.trans last).toStmt
    have hwidth : Operand.width operand = 1 := by simpa using hw
    refine ⟨mono, fun fuel state ready => ?_⟩
    have ends : ∀ (else' : Bil.Program), (∀ (fuel : Nat) (next : Bil.State), Progress (Bil.execProgram fuel next else') (EndOK next.env [])) →
        ∀ (fuel : Nat) (state : Bil.State), ExpReady state.env lowered second →
          Progress (Bil.execStmt fuel state (.ifElse condition [.jmp yesExp] else')) (EndOK state.env (stmtWrites (.ifElse condition [.jmp yesExp] else'))) := by
      intro else' hno fuel state ready
      have hwrites : stmtWrites (.ifElse condition [.jmp yesExp] else') = [] := by simp [stmtWrites, programWrites, stmtLeaves]
      rw [hwrites]
      cases fuel with
      | zero => exact Or.inl (by simp [Bil.execStmt]; rfl)
      | succ fuel =>
        obtain ⟨bits, hb⟩ := ec state.env ⟨ready.written, fun v hv => ready.inputs v (last.inputs v hv), fun v hv => ready.memory v (last.memory v hv)⟩
        obtain ⟨cS, cW⟩ := operand
        dsimp only [Operand.width] at hwidth hb
        subst hwidth
        have heval : Bil.execStmt (fuel + 1) state (.ifElse condition [.jmp yesExp] else') = Bil.execProgram fuel state (if bits = 1 then [.jmp yesExp] else else') := by
          simp [Bil.execStmt, Bil.execExp, hb, bind, Except.bind, bits_asBits]
        rw [Progress, heval]
        by_cases hbit : bits = 1
        · rw [ite_eq_left hbit]
          exact jump_program hcy fuel state
        · rw [ite_eq_right hbit]
          exact hno fuel state
    have hi : ∀ var ∈ Lowering.inputs lowered, var ∈ Lowering.inputs second := fun v hv => last.inputs v (mc.inputs v hv)
    have hm : ∀ var, Lowering.memory lowered = some var → Lowering.memory second = some var := fun v hv => last.memory v (mc.memory v hv)
    rcases hshape with ⟨-, -, hprog⟩ | ⟨-, noExp, hcn, hprog⟩
    · rw [hprog]
      refine snoc_progress _ _ h1 (ends [] ?_) hi hm fuel state ready
      intro fuel next
      cases fuel with
      | zero => exact Or.inl (by simp [Bil.execProgram]; rfl)
      | succ fuel => exact Or.inr ⟨(next, .normal), by simp [Bil.execProgram], fun _ h => h, fun _ h => h, by simp⟩
    · rw [hprog]
      exact snoc_progress _ _ h1 (ends [.jmp noExp] (jump_program hcn)) hi hm fuel state ready
  · obtain ⟨⟨lowered, done⟩, h1, h⟩ := obind h
    obtain ⟨m1, ok⟩ := lowered_progress.2 _ _ _ _ h1
    have last : ExpMono lowered second := by
      dsimp only at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact ExpMono.refl _
      · split at h
        · obtain ⟨ops, _, h⟩ := obind h
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨rfl, fun _ h => h, fun _ h => h⟩
        · simp only [Option.some.injEq] at h
          subst h
          exact ⟨rfl, fun _ h => h, fun _ h => h⟩
    refine ⟨m1.trans last.toStmt, fun fuel state ready => ?_⟩
    rcases ok fuel state (ready.before' last) with he | ⟨result, he, ran⟩
    · exact Or.inl he
    · exact Or.inr ⟨result, he, ran.frame, ran.frameMem, ran.writes⟩

private theorem enterBlock_mono (lowering : Lowering) (budget observed address : Nat) (guarded : Bool) :
    ExpMono lowering (enterBlock lowering budget observed address guarded) := by
  refine ⟨?_, fun v hv => ?_, fun v hv => ?_⟩ <;> cases guarded <;>
    simp_all [enterBlock, freshLabel, jumpConstant, codeSite, setEffect_fields]

private theorem lowerEntry_mono {plan : GraphPlan} {first second : Lowering} {block : Block} {hasEdge : Bool} (h : lowerEntry plan first block hasEdge = some second) :
    ExpMono first second := by
  unfold lowerEntry at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ExpMono.refl _
    · simp at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact (push_mono first _).trans (enterBlock_mono _ _ _ _ _)
    · simp at h

/-- A block that lowers has a result or no fuel, if what it starts from has what it reads, and what it writes at every end of it then is there. -/
theorem lowerBlock_progress {plan : GraphPlan} {first second : Lowering} {block : Block} (h : lowerBlock plan first block = some second) :
    BlockMono first second ∧ ∀ (fuel : Nat) (state : Bil.State),
      (∀ var ∈ Lowering.written (if GraphPlan.chained plan = true then Lowering.withWritten first (GraphPlan.definite plan block.address) else first), Good state.env var) →
      (∀ var ∈ Lowering.inputs second, Good state.env var) → (∀ var, Lowering.memory second = some var → GoodMem state.env var) →
      Progress (Bil.execProgram fuel state block.program) (EndOK state.env (programWrites block.program)) := by
  unfold lowerBlock at h
  dsimp only at h
  generalize hl0 : (if GraphPlan.chained plan = true then Lowering.withWritten first (GraphPlan.definite plan block.address) else first) = l0 at h
  have m0 : BlockMono first l0 := by
    subst hl0
    split
    · exact ⟨fun _ h => h, fun _ h => h⟩
    · exact ⟨fun _ h => h, fun _ h => h⟩
  have key : ∃ l1, ExpMono l0 l1 ∧ lowerExit plan l1 block = some second := by
    split at h
    · simp only [freshLabel] at h
      obtain ⟨l1, h1, h⟩ := obind h
      have n := lowerEntry_mono h1
      refine ⟨_, ?_, h⟩
      exact ⟨n.written, n.inputs, n.memory⟩
    · obtain ⟨l1, h1, h⟩ := obind h
      exact ⟨_, lowerEntry_mono h1, h⟩
  obtain ⟨l1, m1, hexit⟩ := key
  obtain ⟨m2, ok⟩ := lowerExit_progress hexit
  refine ⟨(m0.trans m1.toBlock).trans m2.toBlock, fun fuel state hw hi hm => ?_⟩
  exact ok fuel state ⟨by rw [m1.written]; exact hw, hi, hm⟩

/-- Each block of a range lowers on the way to the end of the lowering. -/
theorem lowerBlocks_progress {plan : GraphPlan} (blocks : List Block) {first second : Lowering} (h : lowerBlocks plan first blocks = some second) :
    BlockMono first second ∧ ∀ block ∈ blocks, ∃ a b, lowerBlock plan a block = some b ∧ BlockMono b second ∧ BlockMono first a := by
  induction blocks generalizing first with
  | nil =>
    simp only [lowerBlocks, Option.some.injEq] at h
    subst h
    exact ⟨⟨fun _ h => h, fun _ h => h⟩, by simp⟩
  | cons block rest ih =>
    simp only [lowerBlocks] at h
    obtain ⟨mid, h1, h⟩ := obind h
    obtain ⟨m1, -⟩ := lowerBlock_progress h1
    obtain ⟨m2, all⟩ := ih h
    refine ⟨m1.trans m2, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨first, mid, h1, m2, ⟨fun _ h => h, fun _ h => h⟩⟩
    · obtain ⟨a, c, h3, m3, m4⟩ := all b hb
      exact ⟨a, c, h3, m3, m1.trans m4⟩

/-! ### What each block has written -/

/-- **`definitelyWritten` is sound**: nothing at the seed, and along each edge what its target has is what its source has
or writes at every end of it. -/
theorem definitelyWritten_sound (seed : Nat) (blocks : List Block) (edges : List (Nat × Nat)) :
    writtenAt (definitelyWritten seed blocks edges) seed = [] ∧ ∀ edge ∈ edges, ∀ var ∈ writtenAt (definitelyWritten seed blocks edges) edge.2,
      var ∈ writtenAt (definitelyWritten seed blocks edges) edge.1 ∨ var ∈ writesOf blocks edge.1 := by
  unfold definitelyWritten
  dsimp only
  split
  · next hs =>
    simp only [writtenStable, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem] at hs
    exact ⟨hs.1, fun edge he var hv => hs.2 edge he var hv⟩
  · simp [writtenAt]

/-- What the block at its address writes. -/
theorem writesOf_block {blocks : List Block} {block : Block} (hd : (blocks.map Block.address).Nodup) (hm : block ∈ blocks) :
    writesOf blocks block.address = programWrites block.program := by
  induction blocks with
  | nil => simp at hm
  | cons head rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hd
    simp only [writesOf, List.find?_cons]
    rcases List.mem_cons.1 hm with rfl | hm
    · simp
    · have hne : head.address ≠ block.address := fun he => hd.1 (he ▸ List.mem_map_of_mem hm)
      have hb : (head.address == block.address) = false := by simpa using hne
      simp only [hb]
      exact ih hd.2 hm

/-- What a chained range needs of the environment at the start of a block. -/
def GraphReady (seed : Nat) (blocks : List Block) (edges : List (Nat × Nat)) (lowering : Lowering) (address : Nat) (env : Bil.Env) : Prop :=
  (∀ var ∈ writtenAt (definitelyWritten seed blocks edges) address, Good env var) ∧ (∀ var ∈ Lowering.inputs lowering, Good env var) ∧
    (∀ var, Lowering.memory lowering = some var → GoodMem env var)

/-- At the seed, that is what the run has at its start. -/
theorem graphReady_seed (seed : Nat) (blocks : List Block) (edges : List (Nat × Nat)) {lowering : Lowering} {env : Bil.Env}
    (hi : ∀ var ∈ Lowering.inputs lowering, Good env var) (hm : ∀ var, Lowering.memory lowering = some var → GoodMem env var) :
    GraphReady seed blocks edges lowering seed env :=
  ⟨by rw [(definitelyWritten_sound seed blocks edges).1]; simp, hi, hm⟩

/-- **What lowers has a result or no fuel, block by block**: a block of a chained range, in an environment ready for it, has a result in the
interpreter, or has no fuel, and the environment it ends with is ready for each block that an edge leads to from it. -/
theorem graph_progress {plan : GraphPlan} {seed : Nat} {blocks : List Block} {edges : List (Nat × Nat)} {initial lowering : Lowering}
    (hlower : lowerBlocks plan initial blocks = some lowering) (hchained : GraphPlan.chained plan = true)
    (hdefinite : GraphPlan.definite plan = writtenAt (definitelyWritten seed blocks edges))
    (haddresses : (blocks.map Block.address).Nodup) {block : Block} (hb : block ∈ blocks) (fuel : Nat) (state : Bil.State)
    (ready : GraphReady seed blocks edges lowering block.address state.env) :
    Progress (Bil.execProgram fuel state block.program)
      (fun result => ∀ target, (block.address, target) ∈ edges → GraphReady seed blocks edges lowering target result.1.env) := by
  obtain ⟨-, all⟩ := lowerBlocks_progress blocks hlower
  obtain ⟨a, b, h1, m, -⟩ := all block hb
  obtain ⟨-, ok⟩ := lowerBlock_progress h1
  have hw : ∀ var ∈ Lowering.written (if GraphPlan.chained plan = true then Lowering.withWritten a (GraphPlan.definite plan block.address) else a), Good state.env var := by
    rw [hchained]
    simp only [↓reduceIte]
    rw [hdefinite]
    exact ready.1
  rcases ok fuel state hw (fun v hv => ready.2.1 v (m.inputs v hv)) (fun v hv => ready.2.2 v (m.memory v hv)) with he | ⟨result, he, ran⟩
  · exact Or.inl he
  · refine Or.inr ⟨result, he, fun target hedge => ⟨fun var hv => ?_, fun v hv => ran.frame v (ready.2.1 v hv), fun v hv => ran.frameMem v (ready.2.2 v hv)⟩⟩
    rcases (definitelyWritten_sound seed blocks edges).2 _ hedge var hv with h2 | h2
    · exact ran.frame var (ready.1 var h2)
    · rw [writesOf_block haddresses hb] at h2
      exact ran.writes var h2

end Bap.Proofs.Jit
