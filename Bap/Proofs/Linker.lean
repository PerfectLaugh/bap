import Bap.Proofs.Image

/-!
The ELF linker as a whole: what holds across its driver, and what a whole link leaves in memory.
-/

namespace Bap.Proofs.Linker

open Bap.Image Bap.Image.ElfLinker Bap.Proofs.Image Bap.Proofs.Image.LinkerLaws

/-! ### Invariants of the driver -/

theorem bind_err {m : LinkM α} {f : α → LinkM β} {state after : LinkState} {e : String} (h : m state = .error e after) :
    (m >>= f) state = .error e after := by
  simp [Bind.bind, EStateM.bind, h]

/-- An action that keeps a property of the state, whether it succeeds or not. -/
def Preserves (R : LinkState → Prop) (m : LinkM α) : Prop := ∀ state, R state → R (stateOf (m state))

namespace Preserves

variable {R : LinkState → Prop}

theorem pure (a : α) : Preserves R (Pure.pure a : LinkM α) := fun _ h => h

theorem throw (e : String) : Preserves R (MonadExcept.throw e : LinkM α) := fun _ h => h

theorem get : Preserves R (MonadState.get : LinkM LinkState) := fun _ h => h

theorem bind {m : LinkM α} {f : α → LinkM β} (hm : Preserves R m) (hf : ∀ a, Preserves R (f a)) : Preserves R (m >>= f) := by
  intro state hs
  have h1 := hm state hs
  cases hr : m state with
  | error e after =>
    have he : (m >>= f) state = .error e after := by simp [Bind.bind, EStateM.bind, hr]
    rw [he]
    rw [hr] at h1
    exact h1
  | ok a after =>
    rw [bind_ok hr]
    rw [hr] at h1
    exact hf a after h1

theorem forIn {list : List β} {init : γ} {f : β → γ → LinkM (ForInStep γ)} (hf : ∀ b ∈ list, ∀ c, Preserves R (f b c)) :
    Preserves R (ForIn.forIn list init f) := by
  induction list generalizing init with
  | nil => exact pure _
  | cons b rest ih =>
    rw [List.forIn_cons]
    refine bind (hf b (by simp) init) fun step => ?_
    cases step with
    | done c => exact pure _
    | yield c => exact ih fun b hb => hf b (by simp [hb])

theorem modify {f : LinkState → LinkState} (h : ∀ state, R state → R (f state)) :
    Preserves R (_root_.modify f : LinkM PUnit) := fun state hs => h state hs

theorem guard (hw : ∀ state message, R state → R { state with warnings := message :: state.warnings }) {action : LinkM Unit}
    (h : Preserves R action) : Preserves R (ElfLinker.guard action) := by
  intro state hs
  have := h state hs
  rw [guard_run]
  cases hr : action state with
  | ok _ after => rw [hr] at this; exact this
  | error message after => rw [hr] at this; exact hw _ _ this

theorem bind_at {m : LinkM α} {f : α → LinkM β} {state : LinkState} (hm : R (stateOf (m state))) (hf : ∀ a, Preserves R (f a)) :
    R (stateOf ((m >>= f) state)) := by
  cases hr : m state with
  | error e after =>
    have he : (m >>= f) state = .error e after := by simp [Bind.bind, EStateM.bind, hr]
    rw [he]
    rw [hr] at hm
    exact hm
  | ok a after =>
    rw [bind_ok hr]
    rw [hr] at hm
    exact hf a after hm

end Preserves

theorem preserves_load {R : LinkState → Prop} (site : Site) (at' n : Nat) (little : Bool) : Preserves R (load site at' n little) := by
  unfold ElfLinker.load
  refine Preserves.bind Preserves.get fun _ => ?_
  split
  · exact Preserves.pure _
  · exact Preserves.throw _

/-- A place the relocations may store to is before the GOT. -/
def SiteOk (env : Env) (site : Site) : Prop := site.limit ≤ env.gotOff

/-- What it takes of a property of the state to hold across the second pass of a link: that it doesn't care about the warnings
and what else the driver writes down, and that it survives the GOT and the stores. -/
structure Invariant (env : Env) (R : LinkState → Prop) : Prop where
  warnings : ∀ state message, R state → R { state with warnings := message :: state.warnings }
  references : ∀ state entry, R state → R { state with references := entry :: state.references }
  got : ∀ value, Preserves R (gotEntry env value)
  /-- Deferring a site whose place was just read. -/
  defer : ∀ state site, env.machine = 8 → (site.rel.typ = 5 ∨ site.rel.typ = 9) → SiteOk env site → R state →
    inSection site 0 4 state.memory.size = true →
    R { state with mipsPending := (site, readNat state.memory env.little (site.off + 0) 4 &&& 0xffff) :: state.mipsPending }
  /-- A deferred half is resolved. -/
  applyHi : ∀ site, env.machine = 8 → (site.rel.typ = 5 ∨ site.rel.typ = 9) → SiteOk env site → site.rel.isExplicit = true →
    Preserves R (mipsApplyHi env site site.a)
  /-- `R_MIPS_LO16` resolves what is pending of its symbol. -/
  flush : ∀ state site, env.machine = 8 → site.rel.typ = 6 → SiteOk env site → R state → inSection site 0 4 state.memory.size = true →
    R (stateOf (mipsFlush env (mipsA16 env site state) site.rel.symbol state))
  /-- What is still pending at the end is resolved without its `LO16`. -/
  finish : ∀ symbol, env.machine = 8 → Preserves R (mipsFlush env 0 symbol)
  /-- What the handler of a site returned is stored, the check of its field having added at most a warning. -/
  store : ∀ apply site state mid writes warnings, handler env = some apply → SiteOk env site → R state →
    apply site state = .ok (some writes) mid → R { mid with warnings := warnings } →
    R (stateOf (commit site writes { mid with warnings := warnings }))

section Handlers

variable {R : LinkState → Prop} {env : Env}

theorem preserves_ld (e : Env) (site : Site) (at' n : Nat) : Preserves R (ld e site at' n) := preserves_load _ _ _ _

theorem preserves_ldInt (e : Env) (site : Site) (at' n : Nat) : Preserves R (ldInt e site at' n) :=
  Preserves.bind (preserves_ld _ _ _ _) fun _ => Preserves.pure _

theorem preserves_ldi (e : Env) (site : Site) (at' n : Nat) : Preserves R (ldi e site at' n) := preserves_load _ _ _ _

theorem preserves_done (writes : List Write) : Preserves R (done writes) := Preserves.pure _

/-- What a handler is made of. -/
local macro "pres_auto" : tactic => `(tactic|
  repeat' first
    | assumption
    | with_reducible apply Preserves.bind
    | with_reducible apply Preserves.forIn
    | with_reducible exact Preserves.pure _
    | with_reducible exact Preserves.throw _
    | with_reducible exact Preserves.get
    | with_reducible exact preserves_done _
    | with_reducible exact preserves_ld _ _ _ _
    | with_reducible exact preserves_ldInt _ _ _ _
    | with_reducible exact preserves_ldi _ _ _ _
    | with_reducible exact preserves_load _ _ _ _
    | with_reducible exact (‹∀ value, Preserves R (gotEntry env value)› _)
    | split
    | intro _)

theorem Invariant.mipsFinish (I : Invariant env R) (hm : env.machine = 8) : Preserves R (mipsFinish env) := by
  unfold ElfLinker.mipsFinish
  refine Preserves.bind Preserves.get fun _ => ?_
  dsimp only
  refine Preserves.bind ?_ fun _ => Preserves.pure _
  exact Preserves.forIn fun _ _ _ => Preserves.bind (I.finish _ hm) fun _ => Preserves.pure _

/-- A site is deferred right after its place is read, so that its place is known to be in bounds. -/
theorem Invariant.deferred (I : Invariant env R) (site : Site) (hm : env.machine = 8) (ht : site.rel.typ = 5 ∨ site.rel.typ = 9)
    (hsite : SiteOk env site) :
    Preserves R (do
      let x ← ld env site 0 4
      modify fun state : LinkState => { state with mipsPending := (site, x &&& 0xffff) :: state.mipsPending }
      done [] : Outcome) := by
  intro state hs
  by_cases hb : inSection site 0 4 state.memory.size = true
  · have : ld env site 0 4 state = .ok _ state := ld_ok hb
    rw [bind_ok this]
    exact I.defer state site hm ht hsite hs hb
  · have : ld env site 0 4 state = .error (outside site) state := by
      simp only [ld, ElfLinker.load, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hb]
      rfl
    simp only [bind, EStateM.bind, this, stateOf]
    exact hs

/-- `R_MIPS_LO16`: its addend and its instruction are read, then what is pending of its symbol is resolved. -/
theorem Invariant.lo16 (I : Invariant env R) {site : Site} (hm : env.machine = 8) (ht : site.rel.typ = 6) (hsite : SiteOk env site)
    (f : Int → Nat → Unit → LinkM (Option (List Write)))
    (hf : ∀ lo insn u, Preserves R (f lo insn u)) :
    Preserves R (do
      let lo ← (if site.rel.isExplicit = true then pure site.a else do
        let x ← ld env site 0 4
        pure (sext (x &&& 0xffff : Nat) 16) : LinkM Int)
      let insn ← ld env site 0 4
      let u ← mipsFlush env lo site.rel.symbol
      f lo insn u) := by
  intro state hs
  by_cases hb : inSection site 0 4 state.memory.size = true
  · have hl : ld env site 0 4 state = .ok _ state := ld_ok hb
    have hflush := I.flush state site hm ht hsite hs hb
    have ha : (if site.rel.isExplicit = true then pure site.a else do
        let x ← ld env site 0 4
        pure (sext (x &&& 0xffff : Nat) 16) : LinkM Int) state = .ok (mipsA16 env site state) state := by
      cases he : site.rel.isExplicit
      · simp only [Bool.false_eq_true, ite_false]
        rw [bind_ok hl]
        simp only [mipsA16, he, Bool.false_eq_true, ite_false]
        rfl
      · simp only [ite_true, mipsA16, he]
        rfl
    rw [bind_ok ha, bind_ok hl]
    exact Preserves.bind_at hflush fun u => hf _ _ u
  · have hl : ld env site 0 4 state = .error (outside site) state := by
      simp only [ld, ElfLinker.load, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hb]
      rfl
    cases he : site.rel.isExplicit
    · simp only [bind, EStateM.bind, Bool.false_eq_true, ite_false, hl, stateOf]
      exact hs
    · simp only [bind, EStateM.bind, ite_true, pure, EStateM.pure, hl, stateOf]
      exact hs

theorem Invariant.handler (I : Invariant env R) {apply : Site → Outcome} (hh : ElfLinker.handler env = some apply) {site : Site}
    (hsite : SiteOk env site) : Preserves R (apply site) := by
  have hg := I.got
  unfold ElfLinker.handler at hh
  split at hh <;> cases hh
  · unfold x86_64; dsimp only; split <;> pres_auto
  · unfold i386; dsimp only; split <;> pres_auto
  · unfold aarch64; dsimp only; split <;> pres_auto
  · unfold arm; dsimp only; split <;> pres_auto
  · rename_i hm
    have happly := fun ht => I.applyHi site hm ht hsite
    have hdefer := fun ht => I.deferred site hm ht hsite
    have hcompound : Preserves R (mipsCompound env site) := by
      unfold mipsCompound mipsCompoundBase
      dsimp only
      pres_auto
    unfold mips
    dsimp only
    split <;> repeat' first
      | (with_reducible refine @id (Preserves R (ld env site 0 4 >>= _)) ?_
         exact hdefer (by first | exact Or.inl (by assumption) | exact Or.inr (by assumption)))
      | (have h6 : site.rel.typ = 6 := by assumption
         exact I.lo16 hm h6 hsite _ fun _ _ _ => Preserves.pure _)
      | with_reducible apply Preserves.bind
      | with_reducible exact Preserves.pure _
      | with_reducible exact happly (by first | exact Or.inl (by assumption) | exact Or.inr (by assumption)) (by assumption)
      | with_reducible exact hcompound
      | with_reducible exact Preserves.throw _
      | with_reducible exact Preserves.get
      | with_reducible exact preserves_done _
      | with_reducible exact preserves_ld _ _ _ _
      | with_reducible exact preserves_ldInt _ _ _ _
      | with_reducible exact preserves_load _ _ _ _
      | with_reducible exact (hg _)
      | split
      | intro _
  · have huleb : ∀ (f : Nat → Int), Preserves R (rewriteUleb env site f) := by
      have hlen : ∀ fuel n, Preserves R (ulebLength env site fuel n) := by
        intro fuel
        induction fuel with
        | zero => exact fun _ => Preserves.pure _
        | succ fuel ih =>
          intro n
          unfold ulebLength
          refine Preserves.bind (preserves_load _ _ _ _) fun _ => ?_
          split
          · exact Preserves.pure _
          · exact ih _
      intro f
      unfold rewriteUleb
      refine Preserves.bind (hlen _ _) fun _ => ?_
      pres_auto
    unfold riscv; dsimp only; split <;> first
      | with_reducible exact huleb _
      | pres_auto
  all_goals
    have hinsn : Preserves R (ppcInsnOfHalf env site) := by
      unfold ppcInsnOfHalf
      pres_auto
  · unfold powerpc; dsimp only; split <;> pres_auto
  · unfold powerpc; dsimp only; split <;> pres_auto
  · unfold systemz; dsimp only; split <;> pres_auto

theorem preserves_warn (hw : ∀ state message, R state → R { state with warnings := message :: state.warnings }) (message : String) :
    Preserves R (ElfLinker.warn message) :=
  Preserves.modify fun state hs => hw state message hs

/-- Finding a site only writes things down. -/
theorem preserves_siteOf (hw : ∀ state message, R state → R { state with warnings := message :: state.warnings })
    (hr : ∀ state entry, R state → R { state with references := entry :: state.references }) (tables : Tables) (report : Bool)
    (rel : Rel) : Preserves R (ElfLinker.siteOf tables report rel) := by
  have hwarn := preserves_warn hw
  have hrefs : ∀ entry, Preserves R (modify fun state : LinkState =>
      { state with references := entry :: state.references } : LinkM PUnit) :=
    fun entry => Preserves.modify fun state hs => hr state entry hs
  unfold ElfLinker.siteOf
  dsimp only
  repeat' first
    | with_reducible apply Preserves.bind
    | with_reducible exact Preserves.pure _
    | with_reducible exact hwarn _
    | with_reducible exact hrefs _
    | split
    | intro _

/-- The first pass. -/
theorem preserves_prescanOne (hw : ∀ state message, R state → R { state with warnings := message :: state.warnings })
    (hr : ∀ state entry, R state → R { state with references := entry :: state.references })
    (hhi : ∀ state key value, R state → R { state with riscvHi := state.riscvHi.insert key value })
    (tables : Tables) (hg : ∀ value, Preserves R (gotEntry tables.env value)) (rel : Rel) :
    Preserves R (ElfLinker.prescanOne tables rel) := by
  have hmod : ∀ key value, Preserves R (modify fun state : LinkState =>
      { state with riscvHi := state.riscvHi.insert key value } : LinkM PUnit) :=
    fun key value => Preserves.modify fun state hs => hhi state key value hs
  unfold ElfLinker.prescanOne
  refine Preserves.guard hw (Preserves.bind (preserves_siteOf hw hr _ _ _) fun site => ?_)
  cases site with
  | none => exact Preserves.pure _
  | some site =>
    dsimp only
    split
    · unfold riscvPrescan
      split <;> repeat' first
        | with_reducible exact Preserves.pure _
        | with_reducible exact (hg _)
        | with_reducible exact hmod _ _
        | with_reducible apply Preserves.bind
        | intro _
    · exact Preserves.pure _

theorem Invariant.applySite (I : Invariant env R) {apply : Site → Outcome} (hh : ElfLinker.handler env = some apply) {site : Site}
    (hsite : SiteOk env site) : Preserves R (ElfLinker.applySite env apply site) := by
  intro state hs
  have hrun := I.handler hh hsite state hs
  unfold ElfLinker.applySite
  cases hr : apply site state with
  | error e after =>
    rw [bind_err hr]
    rw [hr] at hrun
    exact hrun
  | ok outcome mid =>
    rw [bind_ok hr]
    rw [hr] at hrun
    cases outcome with
    | none => exact I.warnings _ _ hrun
    | some writes =>
      dsimp only
      rw [bind_ok (checkField_run env site mid)]
      split
      · exact I.store apply site state mid writes mid.warnings hh hsite hs hr hrun
      · exact I.store apply site state mid writes _ hh hsite hs hr (I.warnings _ _ hrun)

theorem siteOf_ok {tables : Tables} {report : Bool} {rel : Rel} {state after : LinkState} {site : Site}
    (h : ElfLinker.siteOf tables report rel state = .ok (some site) after) : SiteOk tables.env site := by
  obtain ⟨sec, base, s, _, _, _, rfl⟩ := siteOf_some h
  exact Nat.min_le_right _ _

theorem Invariant.applyOne (I : Invariant env R) (tables : Tables) (henv : tables.env = env) {apply : Site → Outcome}
    (hh : ElfLinker.handler env = some apply) (rel : Rel) : Preserves R (ElfLinker.applyOne tables apply rel) := by
  subst henv
  unfold ElfLinker.applyOne
  refine Preserves.guard I.warnings ?_
  intro state hs
  have hrun := preserves_siteOf I.warnings I.references tables false rel state hs
  cases hr : ElfLinker.siteOf tables false rel state with
  | error e after =>
    rw [bind_err hr]
    rw [hr] at hrun
    exact hrun
  | ok site? mid =>
    rw [bind_ok hr]
    rw [hr] at hrun
    cases site? with
    | none => exact hrun
    | some site => exact I.applySite hh (siteOf_ok hr) mid hrun

theorem preserves_foldl {R : LinkState → Prop} {f : β → LinkM Unit} (hf : ∀ b, Preserves R (f b)) (list : List β) (state : LinkState)
    (hs : R state) : R (list.foldl (fun state b => stateOf (f b state)) state) := by
  induction list generalizing state with
  | nil => exact hs
  | cons b rest ih => exact ih _ (hf b state hs)

/-- **A property that is an `Invariant` holds across all of `relocate`** for a machine with a handler, or none. -/
theorem Invariant.relocate {tables : Tables} (I : Invariant tables.env R)
    (hhi : ∀ state key value, R state → R { state with riscvHi := state.riscvHi.insert key value }) :
    Preserves R (ElfLinker.relocate tables) := by
  intro state hs
  cases hh : ElfLinker.handler tables.env with
  | some apply =>
    rw [relocate_run hh]
    have h1 := preserves_foldl (preserves_prescanOne I.warnings I.references hhi tables I.got) tables.input.relocations state hs
    have h2 := preserves_foldl (I.applyOne tables rfl hh) tables.input.relocations _ h1
    dsimp only [stateOf]
    split
    · next hm => exact (Preserves.guard I.warnings (I.mipsFinish (by simpa [emMips] using hm))) _ h2
    · exact h2
  | none =>
    have hb : Preserves R (ElfLinker.relocate tables) := by
      unfold ElfLinker.relocate
      dsimp only
      split
      · refine Preserves.bind (Preserves.forIn fun _ _ _ => ?_) fun _ => ?_
        · refine Preserves.bind (preserves_siteOf I.warnings I.references _ _ _) fun _ => ?_
          split <;> exact Preserves.pure _
        · split
          · exact preserves_warn I.warnings _
          · exact Preserves.pure _
      · next heq => rw [hh] at heq; cases heq
    exact hb state hs

end Handlers

/-! ### What is pending -/

theorem commit_size {site : Site} {writes : List Write} {state : LinkState} (hs : PendingOk state) :
    PendingOk (stateOf (commit site writes state)) := by
  have hc := commit_run site writes state
  change commit site writes state = _ at hc
  rw [hc]
  split
  · next hall =>
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hall
    have hsize := (commit_fold writes state.memory fun w hw => (hall w hw).2).1
    intro entry he
    show inSection _ _ _ (foldWrites state.memory writes).size = true
    have hfold : foldWrites state.memory writes = writes.foldl (init := state.memory)
        (fun memory w => writeNat memory w.little w.off w.n w.value) := rfl
    rw [hfold, hsize]
    exact hs entry he
  · exact hs

theorem flush_pendingOk (env : Env) (lo : Int) (symbol : Nat) : Preserves PendingOk (mipsFlush env lo symbol) := by
  intro state hs
  obtain ⟨after, hf, hsize, hpend⟩ := mipsFlush_ok env lo symbol hs
  rw [hf]
  intro entry he
  change entry ∈ after.mipsPending at he
  rw [hpend] at he
  exact inSection_mono (hs entry (List.mem_filter.mp he).1) hsize

theorem got_pendingOk (env : Env) (value : Int) : Preserves PendingOk (gotEntry env value) := by
  intro state hs
  obtain ⟨_, after, hg, hsize, hpend⟩ := gotEntry_ok env value state
  rw [hg]
  intro entry he
  exact inSection_mono (hs entry (hpend ▸ he)) hsize

/-- **`PendingOk` is an invariant of the driver.** -/
theorem pendingOk_invariant (env : Env) : Invariant env PendingOk where
  warnings _ _ h := h
  references _ _ h := h
  got value := got_pendingOk env value
  defer state site _ _ _ hs hb := hs.push _ hb
  applyHi site _ _ _ _ := by
    unfold mipsApplyHi
    refine Preserves.bind (preserves_ld _ _ _ _) fun _ => ?_
    dsimp only
    split
    · exact fun _ h => commit_size h
    · exact Preserves.bind (got_pendingOk _ _) fun _ _ h => commit_size h
  flush state site _ _ _ hs _ := flush_pendingOk env _ _ state hs
  finish symbol _ := flush_pendingOk env 0 symbol
  store _ _ _ _ _ _ _ _ _ _ h := commit_size h

/-- **What is pending stays resolvable across a whole link**, at every step of its second pass: what `mips_lo16_resolves` asks
of a state holds of each state the relocations see. -/
theorem relocate_pendingOk (tables : Tables) (state : LinkState) (hs : PendingOk state) :
    PendingOk (stateOf (relocate tables state)) := (pendingOk_invariant tables.env).relocate (fun _ _ _ h => h) state hs

/-- The states of the second pass, from one with nothing pending. -/
theorem applied_pendingOk {tables : Tables} {apply : Site → Outcome} (hh : handler tables.env = some apply) (done : List Rel)
    (start : LinkState) (hs : start.mipsPending = []) :
    PendingOk (done.foldl (fun state rel => stateOf (applyOne tables apply rel state))
      (tables.input.relocations.foldl (fun state rel => stateOf (prescanOne tables rel state)) start)) := by
  have I := pendingOk_invariant tables.env
  have h0 : PendingOk start := fun entry he => by simp [hs] at he
  exact preserves_foldl (I.applyOne tables rfl hh) done _
    (preserves_foldl (preserves_prescanOne I.warnings I.references (fun _ _ _ h => h) tables I.got) _ start h0)

/-- **`R_MIPS_LO16` in a whole link**: whichever one of the relocations of a file it is, what is pending of its symbol is resolved
and it does what its ABI says, with its place in bounds as the only condition. -/
theorem link_mips_lo16 {tables : Tables} {apply : Site → Outcome} (hh : handler tables.env = some apply) (before : List Rel)
    {start : LinkState} (hs : start.mipsPending = []) {site : Site}
    (ht : site.rel.typ = 6) :
    let state := before.foldl (fun state rel => stateOf (applyOne tables apply rel state))
      (tables.input.relocations.foldl (fun state rel => stateOf (prescanOne tables rel state)) start)
    inSection site 0 4 state.memory.size = true →
    ∃ flushed, mipsFlush tables.env (mipsA16 tables.env site state) site.rel.symbol state = .ok () flushed ∧
      flushed.mipsPending = (state.mipsPending.filter fun entry => !(entry.1.rel.symbol == site.rel.symbol)) ∧
      (mips tables.env site).run state = .ok (some [stAt tables.env site 0 4 (setLo16 (readNat state.memory tables.env.little (site.off + 0) 4)
        ((if site.sym.name == "_gp_disp" then mipsGp tables.env - site.p + 4 else site.s) + mipsA16 tables.env site state))]) flushed :=
  fun hb => mips_lo16_resolves ht hb (applied_pendingOk hh before start hs)

end Bap.Proofs.Linker
