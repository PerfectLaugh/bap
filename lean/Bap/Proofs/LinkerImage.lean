import Bap.Proofs.LinkerAbi

/-!
**What a whole link leaves in memory**, for every machine with a handler and every relocation the linker applies.
-/

namespace Bap.Proofs.Linker

open Bap.Image Bap.Image.ElfLinker Bap.Proofs.Image Bap.Proofs.Image.LinkerLaws

/-! ### The tables of all machines -/

/-- What a relocation of a machine stores. -/
def abi (env : Env) (site : Site) (rd : Bool → Nat → Nat → Nat) (slot : Int → Int) (hi : Int → Option Int) : Option (List Write) :=
  match env.machine with
  | 62 => x86_64Spec env site slot
  | 3 => i386Spec env site rd slot
  | 183 => aarch64Spec env site rd slot
  | 40 => armSpec env site rd slot
  | 8 => mipsSpec env site rd slot
  | 243 => riscvSpec env site rd slot hi
  | 20 | 21 => powerpcSpec env site rd slot
  | 22 => systemzSpec env site rd slot
  | _ => none

/-- Where the place of a relocation starts. -/
def placeLo (env : Env) (site : Site) : Nat :=
  match env.machine with
  | 20 | 21 => powerpcLo env.little site.rel.typ site.off
  | _ => site.off

/-- Where the place of a relocation stops. -/
def placeHi (env : Env) (site : Site) : Nat :=
  site.off + match env.machine with
    | 62 => x86_64Place site.rel.typ
    | 3 => i386Place site.rel.typ
    | 183 => aarch64Place site.rel.typ
    | 40 => armPlace site.rel.typ
    | 8 => mipsPlace site.rel.typ
    | 243 => riscvPlace site.rel.typ
    | 20 | 21 => powerpcPlace env.little site.rel.typ
    | 22 => systemzPlace site.rel.typ
    | _ => 0

/-- What a relocation can see of a memory: its place. -/
def view (env : Env) (site : Site) (memory : ByteArray) : Bool → Nat → Nat → Nat :=
  cut (placeLo env site) (placeHi env site) site.limit fun little o n => readNat memory little o n

/-- **A handler stores what the table of its machine says**, of the bytes of its place and the entries of the GOT. -/
theorem handler_says {env : Env} {apply : Site → Outcome} (hh : handler env = some apply) {site : Site} {st : LinkState}
    (hl : site.limit ≤ env.gotOff) (hs : env.gotOff ≤ st.memory.size) :
    wp (apply site) (Says fun after => abi env site (view env site st.memory) (slotOf after) (fun key => st.riscvHi[key]?)) st := by
  unfold handler at hh
  split at hh <;> cases hh <;> rename_i hm
  · have := x86_64_says (env := env) (site := site) (st := st)
    simpa only [abi, hm] using this
  · have := i386_says (env := env) (site := site) (st := st) hl hs
    simpa only [abi, view, placeLo, placeHi, hm] using this
  · have := aarch64_says (env := env) (site := site) (st := st) hl hs
    simpa only [abi, view, placeLo, placeHi, hm] using this
  · have := arm_says (env := env) (site := site) (st := st) hl hs
    simpa only [abi, view, placeLo, placeHi, hm] using this
  · have := mips_says (env := env) (site := site) (st := st) hl hs
    simpa only [abi, view, placeLo, placeHi, hm] using this
  · have := riscv_says (env := env) (site := site) (st := st) hl hs
    simpa only [abi, view, placeLo, placeHi, hm] using this
  · have := powerpc_says (env := env) (site := site) (st := st) hl hs
    simpa only [abi, view, placeLo, placeHi, hm] using this
  · have := powerpc_says (env := env) (site := site) (st := st) hl hs
    simpa only [abi, view, placeLo, placeHi, hm] using this
  · have := systemz_says (env := env) (site := site) (st := st) hl hs
    simpa only [abi, view, placeLo, placeHi, hm] using this

/-! ### The stores of a link -/

/-- The stores of a log, the oldest first. The log has the latest first. -/
def flat (log : List (Site × List Write)) : List Write := log.reverse.flatMap (·.2)

/-- The input with the stores of a log. -/
def overlay (data : ByteArray) (log : List (Site × List Write)) : ByteArray := foldWrites data (flat log)

theorem overlay_cons (data : ByteArray) (e : Site × List Write) (log : List (Site × List Write)) :
    overlay data (e :: log) = foldWrites (overlay data log) e.2 := by
  simp [overlay, flat, foldWrites, List.foldl_append]

/-- A table has everything it found by then. -/
def GotLe (a b : LinkState) : Prop := ∀ (k v : Nat), a.got[k]? = some v → b.got[k]? = some v

theorem GotLe.refl (a : LinkState) : GotLe a a := fun _ _ h => h

theorem GotLe.trans {a b c : LinkState} (h1 : GotLe a b) (h2 : GotLe b c) : GotLe a c := fun k v h => h2 k v (h1 k v h)

/-- What a deferred `HI16`, or the `GOT16` of a local symbol, stores once its addend is known. -/
def hiWrites (env : Env) (site : Site) (insn : Nat) (ahl : Int) (slot : Int → Int) : List Write :=
  if site.rel.typ == 5 then
    [stAt env site 0 4 (setLo16 insn ((ahl + (if site.sym.name == "_gp_disp" then mipsGp env - site.p else site.s) + 0x8000) >>> 16))]
  else
    [stAt env site 0 4 (setLo16 insn (slot ((site.s + ahl + 0x8000) - (site.s + ahl + 0x8000) % 65536) - mipsGp env))]

/-- The addend of `R_MIPS_LO16`, or of `R_MIPS_HI16` without one. -/
def LoOf (env : Env) (data : ByteArray) (log : List (Site × List Write)) (symbol : Nat) (lo : Int) : Prop :=
  lo = 0 ∨ ∃ site older, older <:+ log ∧ site.rel.typ = 6 ∧ site.rel.symbol = symbol ∧ SiteOk env site ∧
    inSection site 0 4 data.size = true ∧ lo = mipsA16 env site { memory := overlay data older }

/-- The addend of a pair: the one of the record, or `(AHI << 16) + ALO`, with `AHI` from its place when it was deferred. -/
def AhlOf (env : Env) (data : ByteArray) (log : List (Site × List Write)) (site : Site) (ahl : Int) : Prop :=
  (site.rel.isExplicit = true ∧ ahl = site.a) ∨
    ∃ older lo, older <:+ log ∧ LoOf env data log site.rel.symbol lo ∧
      ahl = ((view env site (overlay data older) env.little (site.off + 0) 4 &&& 0xffff : Nat) : Int) * 65536 + lo

/-- An entry of the log stores what its relocation says, as of some state of the GOT by now and with what its place held at some
time before. -/
def Valid (env : Env) (data : ByteArray) (hi : Int → Option Int) (cur : LinkState) (e : Site × List Write)
    (log : List (Site × List Write)) : Prop :=
  e.2 = [] ∨ ∃ G older, GotLe G cur ∧ older <:+ log ∧
    (some e.2 = abi env e.1 (view env e.1 (overlay data older)) (slotOf G) hi ∨
      ∃ ahl, env.machine = 8 ∧ AhlOf env data log e.1 ahl ∧
        e.2 = hiWrites env e.1 (view env e.1 (overlay data older) env.little (e.1.off + 0) 4) ahl (slotOf G))

/-- What holds of a state in the second pass of a link. -/
structure Logged (env : Env) (data : ByteArray) (hi : Int → Option Int) (st : LinkState) : Prop where
  size : env.gotOff ≤ st.memory.size
  agree : ∀ o, o < env.gotOff → st.memory.get! o = (overlay data st.applied).get! o
  bounds : ∀ w ∈ flat st.applied, w.off + w.n ≤ env.gotOff
  fixed : (fun key => st.riscvHi[key]?) = hi
  pending : ∀ entry ∈ st.mipsPending, (entry.1.rel.typ = 5 ∨ entry.1.rel.typ = 9) ∧ SiteOk env entry.1 ∧ ∃ older, older <:+ st.applied ∧
    entry.2 = view env entry.1 (overlay data older) env.little (entry.1.off + 0) 4 &&& 0xffff
  valid : ∀ e log, (e :: log) <:+ st.applied → Valid env data hi st e log

theorem got_fields (env : Env) (value : Int) (st : LinkState) :
    (gotAfter env value st).applied = st.applied ∧ (gotAfter env value st).riscvHi = st.riscvHi ∧
      (gotAfter env value st).mipsPending = st.mipsPending ∧ GotLe st (gotAfter env value st) := by
  simp only [gotAfter, stateOf, gotEntry, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
  cases hc : st.got[field value 0 64]? with
  | some slot => exact ⟨rfl, rfl, rfl, GotLe.refl _⟩
  | none =>
    refine ⟨rfl, rfl, rfl, fun k v h => ?_⟩
    show (st.got.insert _ _)[k]? = some v
    rw [Std.HashMap.getElem?_insert]
    split
    · next he =>
      have : field value 0 64 = k := by simpa using he
      subst this
      rw [hc] at h
      cases h
    · exact h

section

variable {env : Env} {data : ByteArray} {hi : Int → Option Int}

theorem LoOf.mono {log log' : List (Site × List Write)} {symbol : Nat} {lo : Int} (h : LoOf env data log symbol lo) (hl : log <:+ log') :
    LoOf env data log' symbol lo := by
  rcases h with h | ⟨site, older, ho, h⟩
  · exact .inl h
  · exact .inr ⟨site, older, ho.trans hl, h⟩

theorem AhlOf.mono {log log' : List (Site × List Write)} {site : Site} {ahl : Int} (h : AhlOf env data log site ahl) (hl : log <:+ log') :
    AhlOf env data log' site ahl := by
  rcases h with h | ⟨older, lo, ho, hlo, h⟩
  · exact .inl h
  · exact .inr ⟨older, lo, ho.trans hl, hlo.mono hl, h⟩

theorem Valid.mono {a b : LinkState} {e : Site × List Write} {log : List (Site × List Write)} (h : Valid env data hi a e log)
    (hle : GotLe a b) : Valid env data hi b e log := by
  rcases h with h | ⟨G, older, hG, ho, h⟩
  · exact .inl h
  · exact .inr ⟨G, older, hG.trans hle, ho, h⟩

theorem foldWrites_agree {N : Nat} : ∀ (writes : List Write) (a b : ByteArray), N ≤ a.size → N ≤ b.size →
    (∀ w ∈ writes, w.off + w.n ≤ N) → (∀ o, o < N → a.get! o = b.get! o) →
    (∀ o, o < N → (foldWrites a writes).get! o = (foldWrites b writes).get! o)
  | [], _, _, _, _, _, h => h
  | w :: rest, a, b, ha, hb, hw, h => by
    have hw0 := hw w (by simp)
    have ⟨s1, k1, r1⟩ := writeNat_spec (memory := a) (little := w.little) (value := w.value) (off := w.off) (n := w.n) (by omega)
    have ⟨s2, k2, r2⟩ := writeNat_spec (memory := b) (little := w.little) (value := w.value) (off := w.off) (n := w.n) (by omega)
    have hs1 : N ≤ (writeNat a w.little w.off w.n w.value).size := by omega
    have hs2 : N ≤ (writeNat b w.little w.off w.n w.value).size := by omega
    refine foldWrites_agree rest _ _ hs1 hs2 (fun x hx => hw x (by simp [hx])) fun o ho => ?_
    by_cases hout : o < w.off ∨ w.off + w.n ≤ o
    · rw [k1 o hout, k2 o hout]
      exact h o ho
    · have hi : o - w.off < w.n := by omega
      have e1 := r1 (o - w.off) hi
      have e2 := r2 (o - w.off) hi
      rw [show w.off + (o - w.off) = o by omega] at e1 e2
      exact UInt8.toNat_inj.mp (e1.trans e2.symm)

theorem overlay_size {log : List (Site × List Write)} (h : ∀ w ∈ flat log, w.off + w.n ≤ data.size) :
    (overlay data log).size = data.size := (commit_fold (flat log) data h).1

theorem flat_cons (e : Site × List Write) (log : List (Site × List Write)) : flat (e :: log) = flat log ++ e.2 := by
  simp [flat]

theorem flat_suffix {older log : List (Site × List Write)} (h : older <:+ log) : ∀ w ∈ flat older, w ∈ flat log := by
  obtain ⟨front, rfl⟩ := h
  intro w hw
  simp only [flat, List.reverse_append, List.flatMap_append, List.mem_append] at hw ⊢
  exact .inl hw

theorem Logged.store (hdata : data.size = env.gotOff) {st : LinkState} {site : Site} {writes : List Write} (hL : Logged env data hi st) (hok : SiteOk env site)
    (hv : Valid env data hi st (site, writes) st.applied) :
    Logged env data hi (stateOf (commit site writes st)) ∧ st.applied <:+ (stateOf (commit site writes st)).applied := by
  have hc := commit_run site writes st
  change commit site writes st = _ at hc
  rw [hc]
  split
  · next hall =>
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hall
    have hsize := (commit_fold writes st.memory fun w hw => (hall w hw).2).1
    have hfold : foldWrites st.memory writes = writes.foldl (init := st.memory)
        (fun memory w => writeNat memory w.little w.off w.n w.value) := rfl
    have hbw : ∀ w ∈ writes, w.off + w.n ≤ env.gotOff := fun w hw => Nat.le_trans (hall w hw).1.2 hok
    refine ⟨⟨?_, fun o ho => ?_, fun w hw => ?_, hL.fixed, fun entry he => ?_, fun e log hsuf => ?_⟩, List.suffix_cons _ _⟩
    · show env.gotOff ≤ (foldWrites st.memory writes).size
      rw [hfold, hsize]
      exact hL.size
    · show (foldWrites st.memory writes).get! o = (overlay data ((site, writes) :: st.applied)).get! o
      rw [overlay_cons]
      exact foldWrites_agree (N := env.gotOff) writes _ _ hL.size
        (by rw [overlay_size (by rw [hdata]; exact hL.bounds), hdata]; exact Nat.le_refl _) hbw hL.agree o ho
    · show w.off + w.n ≤ env.gotOff
      have hw' : w ∈ flat st.applied ++ writes := by rw [← flat_cons (site, writes)]; exact hw
      rcases List.mem_append.mp hw' with h | h
      · exact hL.bounds w h
      · exact hbw w h
    · obtain ⟨h1, h2, older, ho, h3⟩ := hL.pending entry he
      exact ⟨h1, h2, older, ho.trans (List.suffix_cons _ _), h3⟩
    · change (e :: log) <:+ ((site, writes) :: st.applied) at hsuf
      rw [List.suffix_cons_iff] at hsuf
      rcases hsuf with h | h
      · have := List.cons.inj h
        obtain ⟨rfl, rfl⟩ := this
        exact hv
      · exact hL.valid e log h
  · exact ⟨hL, List.suffix_refl _⟩

theorem Logged.got {st : LinkState} (value : Int) (hL : Logged env data hi st) : Logged env data hi (gotAfter env value st) := by
  obtain ⟨h1, h2, h3, h4⟩ := got_fields env value st
  obtain ⟨hs, hk⟩ := got_frame env value st
  refine ⟨Nat.le_trans hL.size hs, fun o ho => ?_, ?_, ?_, fun entry he => ?_, fun e log hsuf => ?_⟩
  · rw [h1, hk o (Nat.lt_of_lt_of_le ho hL.size) ho]
    exact hL.agree o ho
  · rw [h1]; exact hL.bounds
  · rw [h2]; exact hL.fixed
  · rw [h3] at he
    rw [h1]
    exact hL.pending entry he
  · rw [h1] at hsuf
    exact (hL.valid e log hsuf).mono h4

/-- A relocation of a deferred kind reads its place. -/
theorem view_read {site : Site} {memory : ByteArray} (hm : env.machine = 8) (ht : site.rel.typ = 5 ∨ site.rel.typ = 9) (little : Bool)
    (hb : site.off + 0 + 4 ≤ site.limit) : view env site memory little (site.off + 0) 4 = readNat memory little (site.off + 0) 4 := by
  have hp : mipsPlace site.rel.typ = 4 := by rcases ht with h | h <;> rw [h] <;> decide
  simp only [view, placeLo, placeHi, hm, hp]
  exact cut_read _ _ _ (by omega) (by omega) hb

/-- What is read of a file doesn't depend on which of these says it. -/
theorem Logged.read {st : LinkState} (hL : Logged env data hi st) (little : Bool) {off n : Nat} (hb : off + n ≤ env.gotOff) :
    readNat st.memory little off n = readNat (overlay data st.applied) little off n :=
  readNat_congr fun _ _ => hL.agree _ (by omega)

/-- A deferred half is resolved at its own place, with its own addend. -/
theorem Logged.applyHi (hdata : data.size = env.gotOff) {st : LinkState} {site : Site} {ahl : Int} (hm : env.machine = 8) (ht : site.rel.typ = 5 ∨ site.rel.typ = 9)
    (hok : SiteOk env site) (hL : Logged env data hi st) (hA : AhlOf env data st.applied site ahl) :
    Logged env data hi (stateOf (mipsApplyHi env site ahl st)) ∧ st.applied <:+ (stateOf (mipsApplyHi env site ahl st)).applied := by
  unfold mipsApplyHi
  by_cases hb : inSection site 0 4 st.memory.size = true
  · rw [bind_ok (ld_ok hb)]
    have hb' := hb
    simp only [inSection, Bool.and_eq_true, decide_eq_true_eq] at hb'
    have hview := view_read (env := env) (site := site) (memory := overlay data st.applied) hm ht env.little hb'.1
    have hrd := hL.read env.little (off := site.off + 0) (n := 4) (Nat.le_trans hb'.1 hok)
    dsimp only
    split
    · next hty =>
      refine Logged.store hdata hL hok (.inr ⟨st, st.applied, GotLe.refl _, List.suffix_refl _, .inr ⟨ahl, hm, hA, ?_⟩⟩)
      simp only [hiWrites, hty, ite_true, hview, hrd]
    · next hty =>
      rw [bind_ok (gotEntry_run env _ st)]
      obtain ⟨h1, _, _, h4⟩ := got_fields env ((site.s + ahl + 0x8000) - (site.s + ahl + 0x8000) % 65536) st
      have hG := Logged.got ((site.s + ahl + 0x8000) - (site.s + ahl + 0x8000) % 65536) hL
      have := Logged.store (site := site) (writes := [stAt env site 0 4 (setLo16 (readNat st.memory env.little (site.off + 0) 4)
        (gotVal env ((site.s + ahl + 0x8000) - (site.s + ahl + 0x8000) % 65536) st - mipsGp env))]) hdata hG hok
        (.inr ⟨gotAfter env ((site.s + ahl + 0x8000) - (site.s + ahl + 0x8000) % 65536) st, st.applied, GotLe.refl _,
          by rw [h1]; exact List.suffix_refl _, .inr ⟨ahl, hm, by rw [h1]; exact hA, ?_⟩⟩)
      · have h2 := this.2
        rw [h1] at h2
        exact ⟨this.1, h2⟩
      · simp only [hiWrites, hty, ite_false, Bool.false_eq_true, hview, hrd, slotOf_gotAfter]
  · have hl : ld env site 0 4 st = .error (outside site) st := by
      simp only [ld, ElfLinker.load, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hb]
      rfl
    rw [bind_err hl]
    exact ⟨hL, List.suffix_refl _⟩

/-- The halves pending of a symbol are resolved, with the addend of what paired them. -/
theorem Logged.flush (hdata : data.size = env.gotOff) (hm : env.machine = 8) {st : LinkState} {lo : Int} {symbol : Nat}
    (hL : Logged env data hi st) (hlo : LoOf env data st.applied symbol lo) :
    Logged env data hi (stateOf (mipsFlush env lo symbol st)) ∧ st.applied <:+ (stateOf (mipsFlush env lo symbol st)).applied := by
  have hrest : st.mipsPending.partition (fun entry => entry.1.rel.symbol == symbol) =
      (st.mipsPending.filter fun entry => entry.1.rel.symbol == symbol,
        st.mipsPending.filter fun entry => !(entry.1.rel.symbol == symbol)) := by
    rw [List.partition_eq_filter_filter]
    rfl
  have hmid : Logged env data hi { st with mipsPending := st.mipsPending.filter (fun entry => !(entry.1.rel.symbol == symbol)) } :=
    ⟨hL.size, hL.agree, hL.bounds, hL.fixed, fun entry he => hL.pending entry (List.mem_filter.mp he).1, hL.valid⟩
  let P : LinkState → Prop := fun cur => Logged env data hi cur ∧ st.applied <:+ cur.applied
  have hloop : Preserves P (forIn (st.mipsPending.filter fun entry => entry.1.rel.symbol == symbol).reverse PUnit.unit
      fun entry _ => do
        mipsApplyHi env entry.1 ((entry.2 : Int) * 65536 + lo)
        pure (ForInStep.yield PUnit.unit)) := by
    apply Preserves.forIn
    intro entry hentry _
    refine Preserves.bind (fun cur hc => ?_) fun _ => Preserves.pure _
    have he := List.mem_filter.mp (List.mem_reverse.mp hentry)
    have hsym : entry.1.rel.symbol = symbol := by simpa using he.2
    obtain ⟨ht, hok, older, ho, hst⟩ := hL.pending entry he.1
    have hA : AhlOf env data cur.applied entry.1 ((entry.2 : Int) * 65536 + lo) :=
      .inr ⟨older, lo, ho.trans hc.2, hsym ▸ hlo.mono hc.2, by rw [hst]⟩
    obtain ⟨h1, h2⟩ := Logged.applyHi hdata hm ht hok hc.1 hA
    exact ⟨h1, hc.2.trans h2⟩
  have hgoal := (Preserves.bind hloop fun _ => Preserves.pure PUnit.unit) _ ⟨hmid, List.suffix_refl _⟩
  unfold mipsFlush
  have step : ∀ f : LinkState → LinkM Unit, ((get : LinkM LinkState) >>= f) st = f st st := fun _ => rfl
  rw [step]
  simp only [hrest]
  exact hgoal

end

/-- A property of what the driver writes down, which the GOT and the stores can't change for the worse. -/
theorem logInvariant (env : Env) (R : LinkState → Prop)
    (hw : ∀ state message, R state → R { state with warnings := message :: state.warnings })
    (hr : ∀ state entry, R state → R { state with references := entry :: state.references })
    (hp : ∀ state rest, R state → R { state with mipsPending := rest })
    (hcommit : ∀ (site : Site) (writes : List Write), Preserves R (commit site writes))
    (hgot : ∀ value, Preserves R (gotEntry env value)) : Invariant env R := by
  have happly : ∀ (site : Site) (ahl : Int), Preserves R (mipsApplyHi env site ahl) := by
    intro site ahl
    unfold mipsApplyHi
    refine Preserves.bind (preserves_ld _ _ _ _) fun _ => ?_
    dsimp only
    split
    · exact hcommit _ _
    · exact Preserves.bind (hgot _) fun _ => hcommit _ _
  have hflush : ∀ (lo : Int) (symbol : Nat), Preserves R (mipsFlush env lo symbol) := by
    intro lo symbol st hc
    unfold mipsFlush
    have step : ∀ f : LinkState → LinkM Unit, ((get : LinkM LinkState) >>= f) st = f st st := fun _ => rfl
    rw [step]
    have hloop : Preserves R (forIn (st.mipsPending.partition fun entry => entry.1.rel.symbol == symbol).1.reverse PUnit.unit
        fun entry _ => do
          mipsApplyHi env entry.1 ((entry.2 : Int) * 65536 + lo)
          pure (ForInStep.yield PUnit.unit)) :=
      Preserves.forIn fun _ _ _ => Preserves.bind (happly _ _) fun _ => Preserves.pure _
    exact (Preserves.bind hloop fun _ => Preserves.pure PUnit.unit) _ (hp _ _ hc)
  exact {
    warnings := hw
    references := hr
    got := hgot
    defer := fun _ _ _ _ _ h _ => hp _ _ h
    applyHi := fun site _ _ _ _ => happly site site.a
    flush := fun state site _ _ _ h _ => hflush _ _ state h
    finish := fun symbol _ => hflush 0 symbol
    store := fun _ site _ _ writes _ _ _ _ _ h => hcommit site writes _ h }

/-- A log only grows. -/
theorem suffix_invariant (env : Env) (A : List (Site × List Write)) : Invariant env (fun st => A <:+ st.applied) := by
  refine logInvariant env _ (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => h) (fun site writes st hs => ?_) (fun value st hs => ?_)
  · have hc := commit_run site writes st
    change commit site writes st = _ at hc
    rw [hc]
    split
    · exact hs.trans (List.suffix_cons _ _)
    · exact hs
  · have h1 := (got_fields env value st).1
    rw [gotEntry_run]
    show A <:+ (gotAfter env value st).applied
    rw [h1]
    exact hs

/-- A warning stays. -/
theorem warned_invariant (env : Env) : Invariant env (fun st => st.warnings ≠ []) := by
  refine logInvariant env _ (fun _ _ _ => by simp) (fun _ _ h => h) (fun _ _ h => h) (fun site writes st hs => ?_) (fun value st hs => ?_)
  · have hc := commit_run site writes st
    change commit site writes st = _ at hc
    rw [hc]
    split <;> exact hs
  · rw [gotEntry_run]
    simp only [gotAfter, stateOf, gotEntry, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
    cases hc : st.got[field value 0 64]? with
    | some slot => exact hs
    | none => exact hs

/-- **The log of a link holds what the tables say**, whichever machine it is. -/
theorem logged_invariant {env : Env} {data : ByteArray} {hi : Int → Option Int} (hdata : data.size = env.gotOff) :
    Invariant env (Logged env data hi) where
  warnings _ _ h := ⟨h.size, h.agree, h.bounds, h.fixed, h.pending, h.valid⟩
  references _ _ h := ⟨h.size, h.agree, h.bounds, h.fixed, h.pending, h.valid⟩
  got value st h := by
    rw [gotEntry_run]
    exact h.got value
  defer state site hm ht hok h hb := by
    have hb' := hb
    simp only [inSection, Bool.and_eq_true, decide_eq_true_eq] at hb'
    refine ⟨h.size, h.agree, h.bounds, h.fixed, fun entry he => ?_, h.valid⟩
    rcases List.mem_cons.mp he with rfl | he
    · refine ⟨ht, hok, state.applied, List.suffix_refl _, ?_⟩
      show _ &&& _ = _ &&& _
      rw [view_read hm ht _ hb'.1, h.read env.little (Nat.le_trans hb'.1 hok)]
    · exact h.pending entry he
  applyHi site hm ht hok he st h := (Logged.applyHi hdata hm ht hok h (.inl ⟨he, rfl⟩)).1
  flush state site hm ht hok h hb := by
    have hb' := hb
    simp only [inSection, Bool.and_eq_true, decide_eq_true_eq] at hb'
    refine (Logged.flush hdata hm h (.inr ⟨site, state.applied, List.suffix_refl _, ht, rfl, hok, ?_, ?_⟩)).1
    · simp only [inSection, Bool.and_eq_true, decide_eq_true_eq, hdata]
      exact ⟨hb'.1, Nat.le_trans hb'.1 hok⟩
    · simp only [mipsA16]
      rw [h.read env.little (Nat.le_trans hb'.1 hok)]
  finish symbol hm st h := (Logged.flush hdata hm h (.inl rfl)).1
  store apply site state mid writes warnings hh hok h hr hmid := by
    have hsays := handler_says hh hok h.size (site := site)
    unfold wp at hsays
    rw [hr] at hsays
    have hw := hsays writes rfl
    have hsuf := (suffix_invariant env state.applied).handler hh hok state (List.suffix_refl _)
    rw [hr] at hsuf
    have hview : view env site state.memory = view env site (overlay data state.applied) := by
      funext little o n
      simp only [view, cut]
      split
      · next hc => exact h.read little (Nat.le_trans hc.2.2 hok)
      · rfl
    rw [hview, h.fixed] at hw
    exact (Logged.store hdata hmid hok (.inr ⟨mid, state.applied, GotLe.refl _, hsuf, .inl hw⟩)).1

/-! ### The whole link -/

/-- The stores don't overlap, and none of them falls in the place of a later one. -/
def LogDisjoint (env : Env) (log : List (Site × List Write)) : Prop :=
  (flat log).Pairwise (fun a b => a.off + a.n ≤ b.off ∨ b.off + b.n ≤ a.off) ∧
    ∀ e older, (e :: older) <:+ log → e.2 ≠ [] → ∀ w ∈ flat older, w.off + w.n ≤ placeLo env e.1 ∨ placeHi env e.1 ≤ w.off

/-- Stores outside of a place leave what can be seen of it. -/
theorem view_overlay {env : Env} {data : ByteArray} {site : Site} {log : List (Site × List Write)} (hb : ∀ w ∈ flat log, w.off + w.n ≤ data.size)
    (h : ∀ w ∈ flat log, w.off + w.n ≤ placeLo env site ∨ placeHi env site ≤ w.off) :
    view env site (overlay data log) = view env site data := by
  funext little o n
  simp only [view, cut]
  split
  · next hc =>
    refine readNat_congr fun i hi => ?_
    refine (commit_fold (flat log) data hb).2 _ fun w hw => ?_
    have := h w hw
    omega
  · rfl

/-- The first pass stores nothing. -/
def Prescanned (env : Env) (data : ByteArray) (st : LinkState) : Prop :=
  st.applied = [] ∧ st.mipsPending = [] ∧ env.gotOff ≤ st.memory.size ∧ ∀ o, o < env.gotOff → st.memory.get! o = data.get! o

theorem prescanned_got (env : Env) (data : ByteArray) (value : Int) : Preserves (Prescanned env data) (gotEntry env value) := by
  intro st hs
  rw [gotEntry_run]
  obtain ⟨h1, _, h3, _⟩ := got_fields env value st
  obtain ⟨h5, h6⟩ := got_frame env value st
  obtain ⟨a, b, c, d⟩ := hs
  exact ⟨h1.trans a, h3.trans b, Nat.le_trans c h5, fun o ho => (h6 o (Nat.lt_of_lt_of_le ho c) ho).trans (d o ho)⟩

/-- **What a link stores**: each entry of its log is in its table, of the bytes of the input, and the memory is the input with these
stores. All that a relocation stores it stores at its place, and as a whole. -/
theorem relocate_image {tables : Tables} {apply : Site → Outcome} (hh : handler tables.env = some apply)
    (hdata : tables.input.data.size = tables.env.gotOff) :
    let env := tables.env
    let data := tables.input.data
    let prescanned := tables.input.relocations.foldl (fun state rel => stateOf (prescanOne tables rel state)) { memory := data }
    let final := stateOf (relocate tables { memory := data })
    LogDisjoint env final.applied →
      (∀ e ∈ final.applied, ∀ w ∈ e.2, readNat final.memory w.little w.off w.n = field w.value 0 (8 * w.n)) ∧
      (∀ o, o < data.size → (∀ e ∈ final.applied, ∀ w ∈ e.2, o < w.off ∨ w.off + w.n ≤ o) → final.memory.get! o = data.get! o) ∧
      (∀ e ∈ final.applied, e.2 ≠ [] → ∃ G, GotLe G final ∧
        (some e.2 = abi env e.1 (view env e.1 data) (slotOf G) (fun key => prescanned.riscvHi[key]?) ∨
          ∃ ahl, env.machine = 8 ∧ AhlOf env data final.applied e.1 ahl ∧
            e.2 = hiWrites env e.1 (view env e.1 data env.little (e.1.off + 0) 4) ahl (slotOf G))) := by
  intro env data prescanned final hdisjoint
  have hstart : Prescanned env data { memory := data } := ⟨rfl, rfl, Nat.le_of_eq hdata.symm, fun _ _ => rfl⟩
  have h0 : Prescanned env data prescanned := preserves_foldl (preserves_prescanOne (fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ h => h) tables
    (prescanned_got env data)) _ _ hstart
  have I := logged_invariant (env := env) (data := data) (hi := fun key => prescanned.riscvHi[key]?) hdata
  have hL0 : Logged env data (fun key => prescanned.riscvHi[key]?) prescanned := by
    obtain ⟨a, b, c, d⟩ := h0
    refine ⟨c, fun o ho => ?_, ?_, rfl, ?_, ?_⟩
    · rw [a]; exact d o ho
    · rw [a]; intro w hw; cases hw
    · rw [b]; intro _ he; cases he
    · rw [a]; intro _ _ hs; cases (List.suffix_nil.mp hs)
  have hL : Logged env data (fun key => prescanned.riscvHi[key]?) final := by
    have h2 := preserves_foldl (I.applyOne tables rfl hh) tables.input.relocations _ hL0
    have hfinal : final = (let applied := tables.input.relocations.foldl (fun state rel => stateOf (applyOne tables apply rel state)) prescanned
        if tables.env.machine == emMips then stateOf (ElfLinker.guard (mipsFinish tables.env) applied) else applied) := by
      show stateOf (relocate tables { memory := data }) = _
      rw [relocate_run hh]
      rfl
    rw [hfinal]
    dsimp only
    split
    · next hm => exact (Preserves.guard I.warnings (I.mipsFinish (by simpa [emMips] using hm))) _ h2
    · exact h2
  have hdata' : data.size = env.gotOff := hdata
  have hbounds : ∀ w ∈ flat final.applied, w.off + w.n ≤ data.size := by
    rw [hdata']
    exact hL.bounds
  have hmem : ∀ w, w ∈ flat final.applied ↔ ∃ e ∈ final.applied, w ∈ e.2 := by
    intro w
    simp [flat, List.mem_flatMap]
  refine ⟨fun e he w hw => ?_, fun o ho hout => ?_, fun e he hne => ?_⟩
  · have hin : w ∈ flat final.applied := (hmem w).2 ⟨e, he, hw⟩
    have hread := foldWrites_read (flat final.applied) data w hin hbounds hdisjoint.1
    refine (readNat_congr fun i hi => ?_).trans hread
    have := hbounds w hin
    exact hL.agree _ (by omega)
  · rw [hL.agree o (by omega)]
    exact (commit_fold (flat final.applied) data hbounds).2 o fun w hw => by
      obtain ⟨e, he, hw'⟩ := (hmem w).1 hw
      exact hout e he w hw'
  · obtain ⟨front, rest, heq⟩ := List.append_of_mem he
    have hsuf : (e :: rest) <:+ final.applied := ⟨front, heq.symm⟩
    have hd := hdisjoint.2 e rest hsuf hne
    have hsub : ∀ {older}, older <:+ rest → view env e.1 (overlay data older) = view env e.1 data := fun ho =>
      view_overlay (fun w hw => hbounds w (flat_suffix (ho.trans (List.suffix_cons _ _ |>.trans hsuf)) w hw))
        fun w hw => hd w (flat_suffix ho w hw)
    rcases hL.valid e rest hsuf with h | ⟨G, older, hG, ho, h⟩
    · exact absurd h hne
    · refine ⟨G, hG, ?_⟩
      rcases h with h | ⟨ahl, hm, hA, h⟩
      · exact .inl (hsub ho ▸ h)
      · refine .inr ⟨ahl, hm, hA.mono (List.suffix_cons _ _ |>.trans hsuf), ?_⟩
        rw [h, hsub ho]

/-- **The same of `link`**: for every machine with a handler, every relocation it applies stores what its table says, of the
bytes of the input, when the stores don't overlap: the final image holds these values and the original bytes elsewhere. -/
theorem link_image (input : Input) : ∃ tables : Tables, tables.input = input ∧
    tables.addrs = (layoutSections input.sections.toList input.base).addrs ∧ tables.env.machine = input.machine ∧
    ∀ apply, handler tables.env = some apply →
      let state := stateOf (relocate tables { memory := input.data })
      (link input).memory = state.memory ∧ (link input).applied = state.applied.reverse ∧
      (LogDisjoint tables.env state.applied →
        (∀ e ∈ state.applied, ∀ w ∈ e.2, readNat state.memory w.little w.off w.n = field w.value 0 (8 * w.n)) ∧
        (∀ o, o < input.data.size → (∀ e ∈ state.applied, ∀ w ∈ e.2, o < w.off ∨ w.off + w.n ≤ o) →
          state.memory.get! o = input.data.get! o) ∧
        (∀ e ∈ state.applied, e.2 ≠ [] → ∃ G, GotLe G state ∧
          (some e.2 = abi tables.env e.1 (view tables.env e.1 input.data) (slotOf G) (fun key =>
              (input.relocations.foldl (fun state rel => stateOf (prescanOne tables rel state)) { memory := input.data }).riscvHi[key]?) ∨
            ∃ ahl, tables.env.machine = 8 ∧ AhlOf tables.env input.data state.applied e.1 ahl ∧
              e.2 = hiWrites tables.env e.1 (view tables.env e.1 input.data tables.env.little (e.1.off + 0) 4) ahl (slotOf G)))) := by
  obtain ⟨tables, rfl, hg, hm, _, _, _, ha, hmem, _, _, _, happ⟩ := link_relocate input
  exact ⟨tables, rfl, ha, hm, fun apply hh => ⟨hmem, happ, relocate_image hh hg.symm⟩⟩

/-! ### Relaxed thread-local accesses -/

private theorem get!_set!_other (bytes : ByteArray) {i j : Nat} (value : UInt8) (hne : i ≠ j) :
    (bytes.set! i value).get! j = bytes.get! j := by
  by_cases hi : i < bytes.size
  · rw [get!_set! _ _ _ _ hi, ite_eq_right hne]
  · cases bytes with
    | mk array =>
      show (array.setIfInBounds i value)[j]! = array[j]!
      rw [Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_lt hi)]

private theorem writeBytes_fold (bytes : List Nat) (off k : Nat) (memory : ByteArray) :
    let result := (bytes.zipIdx k).foldl (init := memory) fun memory (byte, index) => memory.set! (off + index) (UInt8.ofNat byte)
    result.size = memory.size ∧ (∀ o, (o < off + k ∨ off + k + bytes.length ≤ o) → result.get! o = memory.get! o) ∧
      (off + k + bytes.length ≤ memory.size → ∀ i, (hi : i < bytes.length) → result.get! (off + k + i) = UInt8.ofNat bytes[i]) := by
  induction bytes generalizing k memory with
  | nil => exact ⟨rfl, fun _ _ => rfl, fun _ _ hi => by cases hi⟩
  | cons byte rest ih =>
    obtain ⟨h1, h2, h3⟩ := ih (k + 1) (memory.set! (off + k) (UInt8.ofNat byte))
    simp only [List.zipIdx_cons, List.foldl_cons, List.length_cons] at h1 h2 h3 ⊢
    have hs := size_set! memory (off + k) (UInt8.ofNat byte)
    refine ⟨h1.trans hs, fun o ho => ?_, fun hb i hi => ?_⟩
    · rw [h2 o (by omega), get!_set!_other _ _ (by omega)]
    · cases i with
      | zero =>
        rw [h2 _ (by omega), get!_set! _ _ _ _ (by omega), ite_eq_left (Nat.add_zero _).symm]
        rfl
      | succ i =>
        have := h3 (by omega) i (by simpa using hi)
        rw [show off + k + (i + 1) = off + (k + 1) + i by omega]
        exact this

/-- **What a patch does**: it stores its bytes and nothing else, in the bounds of the file. -/
theorem writeBytes_spec (memory : ByteArray) (off : Nat) (bytes : List Nat) :
    (writeBytes memory off bytes).size = memory.size ∧
      (∀ o, (o < off ∨ off + bytes.length ≤ o) → (writeBytes memory off bytes).get! o = memory.get! o) ∧
      (off + bytes.length ≤ memory.size → ∀ i, (hi : i < bytes.length) →
        (writeBytes memory off bytes).get! (off + i) = UInt8.ofNat bytes[i]) := by
  have := writeBytes_fold bytes off 0 memory
  simpa [writeBytes] using this

/-- **`R_X86_64_TLSGD`**: the sequence the psABI gives becomes the one of local-exec, and the call goes with it. -/
theorem relax_x86_64_gd {data : ByteArray} {sec : ElfLinker.Section} {rel call : Rel} (ht : rel.typ = 19) (h4 : 4 ≤ sec.off + rel.offset)
    (hlo : sec.off + 4 ≤ sec.off + rel.offset) (hhi : sec.off + rel.offset - 4 + 16 ≤ sec.off + sec.size)
    (hop : hasBytes data (sec.off + rel.offset - 4) [0x66, 0x48, 0x8d, 0x3d] = true)
    (hc : call.target = rel.target ∧ call.offset = rel.offset + 8 ∧ (call.typ = 2 ∨ call.typ = 4 ∨ call.typ = 9 ∨ call.typ = 41 ∨ call.typ = 42)) :
    relaxX86_64 data sec rel (some call) =
      some { patches := [(sec.off + rel.offset - 4, x86_64GdInsns)], rels := [relocated rel (rel.offset + 8) 23 (rel.addend + 4)], skip := true } := by
  have hle : sec.off ≤ sec.off + rel.offset - 4 := by omega
  simp [relaxX86_64, ht, h4, hle, hhi, hop, hc.1, hc.2.1]
  omega

/-- **`R_X86_64_TLSLD`** with a direct call: the call goes, and the block of the module is the thread pointer. -/
theorem relax_x86_64_ld {data : ByteArray} {sec : ElfLinker.Section} {rel call : Rel} (ht : rel.typ = 20) (h3 : 3 ≤ sec.off + rel.offset)
    (hlo : sec.off + 3 ≤ sec.off + rel.offset) (hhi : sec.off + rel.offset - 3 + 12 ≤ sec.off + sec.size)
    (hop : hasBytes data (sec.off + rel.offset - 3) [0x48, 0x8d, 0x3d] = true)
    (hc : call.target = rel.target ∧ call.offset = rel.offset + 5 ∧ (call.typ = 2 ∨ call.typ = 4)) :
    relaxX86_64 data sec rel (some call) =
      some { patches := [(sec.off + rel.offset - 3, x86_64LdInsns)], skip := true } := by
  have hle : sec.off ≤ sec.off + rel.offset - 3 := by omega
  simp [relaxX86_64, ht, h3, hle, hhi, hop, hc.1, hc.2.1]
  omega

/-- `R_X86_64_DTPOFF32` and `DTPOFF64` measure from the thread pointer, as the block of the module is there. -/
theorem relax_x86_64_dtpoff {data : ByteArray} {sec : ElfLinker.Section} {rel : Rel} {next : Option Rel} :
    (rel.typ = 21 → relaxX86_64 data sec rel next = some { rels := [{ rel with typ := 23 }] }) ∧
      (rel.typ = 17 → relaxX86_64 data sec rel next = some { rels := [{ rel with typ := 18 }] }) := by
  constructor <;> intro ht <;> simp [relaxX86_64, ht]

/-- **`R_X86_64_GOTPC32_TLSDESC`** and `TLSDESC_CALL`: `leaq x@tlsdesc(%rip),%reg` becomes `movq $x@tpoff,%reg`, with the register in
its right field, and the call a `nop`. -/
theorem relax_x86_64_desc {data : ByteArray} {sec : ElfLinker.Section} {rel : Rel} {next : Option Rel} (ht : rel.typ = 34)
    (hb : 3 ≤ sec.off + rel.offset ∧ sec.off ≤ sec.off + rel.offset - 3 ∧ sec.off + rel.offset - 3 + 7 ≤ sec.off + sec.size)
    (hrex : peek data (sec.off + rel.offset - 3) = 0x48 ∨ peek data (sec.off + rel.offset - 3) = 0x4c)
    (hlea : peek data (sec.off + rel.offset - 2) = 0x8d)
    (hrip : peek data (sec.off + rel.offset - 1) % 8 = 5 ∧ peek data (sec.off + rel.offset - 1) >>> 6 = 0) :
    let rex := peek data (sec.off + rel.offset - 3)
    let modrm := peek data (sec.off + rel.offset - 1)
    relaxX86_64 data sec rel next = some {
      patches := [(sec.off + rel.offset - 3, [0x48 + (rex >>> 2) % 2, 0xc7, 0xc0 + (modrm >>> 3) % 8])]
      rels := [relocated rel rel.offset 23 (rel.addend + 4)] } := by
  obtain ⟨h1, h2, h3⟩ := hb
  have hrex' : (peek data (sec.off + rel.offset - 3) == 0x48 || peek data (sec.off + rel.offset - 3) == 0x4c) = true := by
    rcases hrex with h | h <;> simp [h]
  simp [relaxX86_64, ht, h1, h2, h3, hrex', hlea, hrip.1, hrip.2]

/-- **AArch64's TLSDESC**: its first two instructions build the offset from the thread pointer in `x0`, the others are `nop`. -/
theorem relax_aarch64 {sec : ElfLinker.Section} {rel : Rel} (hb : sec.off + rel.offset + 4 ≤ sec.off + sec.size) :
    (rel.typ = 0x232 → relaxAArch64 sec rel = some { patches := [(sec.off + rel.offset, wordBytes aarch64Movz)], rels := [{ rel with typ := 0x222 }] }) ∧
    (rel.typ = 0x233 → relaxAArch64 sec rel = some { patches := [(sec.off + rel.offset, wordBytes aarch64Movk)], rels := [{ rel with typ := 0x224 }] }) ∧
    ((rel.typ = 0x234 ∨ rel.typ = 0x239) → relaxAArch64 sec rel = some { patches := [(sec.off + rel.offset, wordBytes aarch64Nop)] }) := by
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_⟩
  · simp [relaxAArch64, ht, hb]
  · simp [relaxAArch64, ht, hb]
  · rcases ht with ht | ht <;> simp [relaxAArch64, ht, hb]

/-- **`R_386_TLS_GD`**: `leal x@tlsgd(%ebx),%eax`, with or without an index, and its call become `movl %gs:0,%eax; subl $x@ntpoff,%eax`. -/
theorem relax_i386_gd {data : ByteArray} {sec : ElfLinker.Section} {rel call : Rel} (ht : rel.typ = 18) {start : Nat}
    (hstart : start = if peek data (sec.off + rel.offset - 2) == 0x04 then sec.off + rel.offset - 3 else sec.off + rel.offset - 2)
    (hb : 3 ≤ sec.off + rel.offset ∧ sec.off ≤ start ∧ start + 12 ≤ sec.off + sec.size ∧ sec.off + rel.offset + 4 ≤ data.size)
    (hc : call.target = rel.target ∧ (call.typ = 2 ∨ call.typ = 4 ∨ call.typ = 43)) :
    relaxI386 data sec rel (some call) = some {
      patches := [(start, i386GdInsns)]
      rels := [relocated rel (start + 8 - sec.off) 34
        (-(if rel.isExplicit then rel.addend else sext (readNat data true (sec.off + rel.offset) 4) 32))]
      skip := true } := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  have ht2 := hc.2
  subst hstart
  by_cases hp : peek data (sec.off + rel.offset - 2) = 4 <;> simp only [hp, beq_iff_eq, reduceIte] at h2 h3 <;>
    simp [relaxI386, ht, h1, h2, h3, h4, hc.1, hp] <;> omega

/-- **`R_386_TLS_LDM`**: the block of the module is the thread pointer, and `R_386_TLS_LDO_32` measures from it. -/
theorem relax_i386_ld {data : ByteArray} {sec : ElfLinker.Section} {rel call : Rel} (ht : rel.typ = 19)
    (hb : 2 ≤ sec.off + rel.offset ∧ sec.off ≤ sec.off + rel.offset - 2 ∧ sec.off + rel.offset - 2 + 11 ≤ sec.off + sec.size)
    (hc : call.target = rel.target ∧ (call.typ = 2 ∨ call.typ = 4 ∨ call.typ = 43)) :
    relaxI386 data sec rel (some call) = some { patches := [(sec.off + rel.offset - 2, i386LdInsns)], skip := true } := by
  obtain ⟨h1, h2, h3⟩ := hb
  have ht2 := hc.2
  simp [relaxI386, ht, h1, h2, h3, hc.1]
  omega

/-- The `movz` and `movk` of the relaxation say what they should, whatever the offset: `x0` is `(hi << 16) + lo` of it. -/
theorem aarch64_movz_movk (value : Int) :
    field (setBits aarch64Movz 5 16 (value >>> 16)) 5 16 = field value 16 16 ∧
      field (setBits aarch64Movk 5 16 value) 5 16 = field value 0 16 ∧
      field (setBits aarch64Movz 5 16 (value >>> 16)) 0 5 = 0 ∧ field (setBits aarch64Movk 5 16 value) 0 5 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [field_setBits_self]
    exact (field_shiftRight value 16 0 16).trans (by rfl)
  · rw [field_setBits_self]
  · rw [field_setBits_other _ _ _ _ 0 5 (.inl (by omega))]
    decide
  · rw [field_setBits_other _ _ _ _ 0 5 (.inl (by omega))]
    decide

/-- **Relaxing only changes the bytes and the relocations**, and not the size of the file: all of `link_image` applies to a relaxed
file with its GOT where it was. -/
theorem relaxTls_shape (input : Input) :
    (relaxTls input).data.size = input.data.size ∧ (relaxTls input).machine = input.machine ∧
      (relaxTls input).sections = input.sections ∧ (relaxTls input).symbols = input.symbols ∧ (relaxTls input).base = input.base := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  have key : ∀ (entries : List (Rel × Option Rel)) (state : RelaxState),
      (entries.foldl (relaxStep input) state).data.size = state.data.size := by
    intro entries
    induction entries with
    | nil => exact fun _ => rfl
    | cons entry rest ih =>
      intro state
      simp only [List.foldl_cons]
      rw [ih]
      unfold relaxStep
      have hpatch : ∀ (patches : List (Nat × List Nat)) (data : ByteArray),
          (patches.foldl (fun data patch => writeBytes data patch.1 patch.2) data).size = data.size := by
        intro patches
        induction patches with
        | nil => exact fun _ => rfl
        | cons patch more ih' =>
          intro data
          simp only [List.foldl_cons]
          rw [ih', (writeBytes_spec data patch.1 patch.2).1]
      split
      · rfl
      · split
        · exact hpatch _ _
        · rfl
  exact key _ _

/-- **Without a warning, nothing is skipped**: a relocation with a site stores at it. -/
theorem applyOne_applies {tables : Tables} {apply : Site → Outcome} {rel : Rel} {st : LinkState} {site : Site} {after : LinkState}
    (hsite : siteOf tables false rel st = .ok (some site) after)
    (hclean : (stateOf (applyOne tables apply rel st)).warnings = []) :
    ∃ writes mid, apply site after = .ok (some writes) mid ∧ fieldOk tables.env mid site = true ∧
      (site, writes) ∈ (stateOf (applyOne tables apply rel st)).applied := by
  unfold applyOne at hclean ⊢
  rw [guard_run, bind_ok hsite] at hclean ⊢
  dsimp only at hclean ⊢
  unfold ElfLinker.applySite at hclean ⊢
  cases hr : apply site after with
  | error e mid =>
    rw [bind_err hr] at hclean
    simp [stateOf] at hclean
  | ok outcome mid =>
    rw [bind_ok hr] at hclean ⊢
    cases outcome with
    | none => simp [stateOf, warn, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at hclean
    | some writes =>
      dsimp only at hclean ⊢
      rw [bind_ok (checkField_run tables.env site mid)] at hclean ⊢
      have hfits : fieldOk tables.env mid site = true := by
        cases hf : fieldOk tables.env mid site with
        | true => rfl
        | false =>
          exfalso
          simp only [hf, Bool.false_eq_true, ite_false] at hclean
          have hw : ∀ s : LinkState, s.warnings ≠ [] → (match commit site writes s with
              | EStateM.Result.ok _ after => after
              | EStateM.Result.error message after => { after with warnings := message :: after.warnings } : LinkState).warnings ≠ [] := by
            intro s h
            have hc := commit_run site writes s
            change commit site writes s = _ at hc
            rw [hc]
            by_cases hall : (writes.all fun write => decide (site.off ≤ write.off) && decide (write.off + write.n ≤ site.limit) &&
                decide (write.off + write.n ≤ s.memory.size)) = true
            · rw [ite_eq_left hall]
              exact h
            · rw [ite_eq_right hall]
              simp
          exact hw _ (by simp) hclean
      generalize (if fieldOk tables.env mid site = true then mid else _ : LinkState) = checked at hclean ⊢
      have hc := commit_run site writes checked
      change commit site writes checked = _ at hc
      rw [hc] at hclean ⊢
      by_cases hall : (writes.all fun write => decide (site.off ≤ write.off) && decide (write.off + write.n ≤ site.limit) &&
          decide (write.off + write.n ≤ checked.memory.size)) = true
      · rw [ite_eq_left hall]
        exact ⟨writes, mid, rfl, hfits, by simp [stateOf]⟩
      · rw [ite_eq_right hall] at hclean
        simp [stateOf] at hclean

/-- **A link without a warning applies every relocation that has a site**, on every machine with a handler, and what they store is
what `relocate_image` tells. -/
theorem relocate_applies_all {tables : Tables} {apply : Site → Outcome} (hh : handler tables.env = some apply) (state : LinkState)
    (hclean : (stateOf (relocate tables state)).warnings = []) {rel : Rel} (hrel : rel ∈ tables.input.relocations) {site : Site}
    {st after : LinkState} (hsite : siteOf tables false rel st = .ok (some site) after) :
    ∃ writes state' mid, apply site state' = .ok (some writes) mid ∧ fieldOk tables.env mid site = true ∧
      (site, writes) ∈ (stateOf (relocate tables state)).applied := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hrel
  have hany : ∀ s : LinkState, siteOf tables false rel s = .ok (some site) s := by
    intro s
    obtain ⟨sec, base, x, hsec, hoff, hsym, rfl⟩ := siteOf_some hsite
    unfold siteOf
    dsimp only
    rw [hsec]
    dsimp only
    rw [ite_eq_right (by omega), hsym]
    rfl
  let start := pre.foldl (fun state rel => stateOf (applyOne tables apply rel state))
    (tables.input.relocations.foldl (fun state rel => stateOf (prescanOne tables rel state)) state)
  let afterIt := stateOf (applyOne tables apply rel start)
  have hrun : ∀ {R : LinkState → Prop}, Invariant tables.env R → R afterIt → R (stateOf (relocate tables state)) := by
    intro R I hn
    have h2 := preserves_foldl (I.applyOne tables rfl hh) post afterIt hn
    have key : ∀ init : LinkState, tables.input.relocations.foldl (fun state rel => stateOf (applyOne tables apply rel state)) init =
        post.foldl (fun state rel => stateOf (applyOne tables apply rel state))
          (stateOf (applyOne tables apply rel (pre.foldl (fun state rel => stateOf (applyOne tables apply rel state)) init))) := by
      intro init
      rw [hsplit]
      simp only [List.foldl_append, List.foldl_cons]
    have heq := key (tables.input.relocations.foldl (fun state rel => stateOf (prescanOne tables rel state)) state)
    have hfin : stateOf (relocate tables state) = (if tables.env.machine == emMips then
        stateOf (ElfLinker.guard (mipsFinish tables.env) (post.foldl (fun state rel => stateOf (applyOne tables apply rel state)) afterIt))
        else post.foldl (fun state rel => stateOf (applyOne tables apply rel state)) afterIt) := by
      rw [relocate_run hh, ← heq]
      rfl
    rw [hfin]
    split
    · next hm => exact (Preserves.guard I.warnings (I.mipsFinish (by simpa [emMips] using hm))) _ h2
    · exact h2
  have hnext : afterIt.warnings = [] :=
    Classical.byContradiction fun hne => hrun (warned_invariant tables.env) hne hclean
  obtain ⟨writes, mid, hmid, hfits, hw⟩ := applyOne_applies (hany start) hnext
  obtain ⟨front, hfront⟩ := hrun (suffix_invariant tables.env afterIt.applied) (List.suffix_refl _)
  exact ⟨writes, start, mid, hmid, hfits, by rw [← hfront]; exact List.mem_append_right _ hw⟩

/-! ### Thunks -/

/-- **The thunk of AArch64** is `ldr x16, #8` and `br x16`: it loads the word eight bytes on and goes there. -/
theorem aarch64Thunk_decode :
    aarch64Thunk.length = 16 ∧ field (0x58000050 : Nat) 24 8 = 0x58 ∧ field (0x58000050 : Nat) 5 19 * 4 = 8 ∧
      field (0x58000050 : Nat) 0 5 = 16 ∧ field (0xd61f0200 : Nat) 10 22 = 0x3587c0 ∧ field (0xd61f0200 : Nat) 5 5 = 16 := by
  decide

/-- **It reaches any target**: the relocation of the word holds all of `S + A`. -/
theorem aarch64Thunk_reaches (env : Env) (site : Site) (rd : Bool → Nat → Nat → Nat) (slot : Int → Int) (ht : site.rel.typ = 0x101) :
    aarch64Spec env site rd slot = some [stAt env site 0 8 (site.s + site.a)] := by
  simp only [aarch64Spec, ht]

/-- **The thunk of ARM** is `ldr pc, [pc, #-4]`: `pc` reads as eight bytes on, so it loads the word four bytes on and goes there. -/
theorem armThunk_decode (little : Bool) :
    (armThunk little).length = 8 ∧ field (0xe51ff004 : Nat) 28 4 = 0xe ∧ field (0xe51ff004 : Nat) 20 8 = 0x51 ∧
      field (0xe51ff004 : Nat) 16 4 = 15 ∧ field (0xe51ff004 : Nat) 12 4 = 15 ∧ field (0xe51ff004 : Nat) 0 12 = 4 := by
  cases little <;> decide

/-- **It reaches any target, in its instruction set**: the word is `S + A` with the Thumb bit of the target, and the load of `pc`
goes to that state. -/
theorem armThunk_reaches (env : Env) (site : Site) (rd : Bool → Nat → Nat → Nat) (slot : Int → Int) (ht : site.rel.typ = 2)
    (he : site.rel.isExplicit = true) :
    armSpec env site rd slot = some [stAt env site 0 4 (armWithT site (armS site + site.a))] := by
  simp only [armSpec, ht, addendOf, he, ite_true]

/-- **The thunk of Thumb** is `movw ip, #lo; movt ip, #hi; bx ip`. -/
theorem thumbThunk_decode (little : Bool) :
    (thumbThunk little).length = 12 ∧ thumbMovImm 0xf240 0x0c00 = 0 ∧ thumbMovImm 0xf2c0 0x0c00 = 0 ∧ field (0x0c00 : Nat) 8 4 = 12 ∧
      field (0x4760 : Nat) 3 4 = 12 ∧ field (0x4760 : Nat) 7 9 = 0x8e := by
  cases little <;> decide

/-- **It reaches any 32-bit target, in its instruction set**: the two halves make up `(S + A) | T`, whose low bit `bx` takes for the
state. -/
theorem thumbThunk_reaches (env : Env) (site : Site) (rd : Bool → Nat → Nat → Nat) (slot : Int → Int) (he : site.rel.isExplicit = true) :
    let hw (at' : Nat) : Nat := rd env.little (site.off + at') 2
    (site.rel.typ = 0x2f → armSpec env site rd slot = some [stAt env site 0 2 (thumbMovSet1 (hw 0) (armWithT site (armS site + site.a)) : Nat),
      stAt env site 2 2 (thumbMovSet2 (hw 2) (armWithT site (armS site + site.a)) : Nat)]) ∧
    (site.rel.typ = 0x30 → armSpec env site rd slot = some [stAt env site 0 2 (thumbMovSet1 (hw 0) ((armS site + site.a) >>> 16) : Nat),
      stAt env site 2 2 (thumbMovSet2 (hw 2) ((armS site + site.a) >>> 16) : Nat)]) := by
  refine ⟨fun ht => ?_, fun ht => ?_⟩ <;> simp only [armSpec, ht, addendOf, he, ite_true]

theorem thunkKind_bits {machine typ : Nat} {kind : ThunkKind} (h : thunkKind machine typ = some kind) : 0 < kind.bits := by
  unfold thunkKind at h
  split at h <;> first | (cases h; decide) | cases h

/-- Finding a site that isn't reported changes nothing. -/
theorem siteOf_after {tables : Tables} {rel : Rel} {state after : LinkState} {site : Site}
    (h : siteOf tables false rel state = .ok (some site) after) : after = state := by
  unfold siteOf at h
  dsimp only at h
  cases hsec : relocatedSection tables rel.target with
  | none => rw [hsec] at h; cases h
  | some found =>
    obtain ⟨sec, base⟩ := found
    rw [hsec] at h
    dsimp only at h
    by_cases hoff : rel.offset ≥ sec.size
    · rw [ite_eq_left hoff] at h
      simp [pure, EStateM.pure] at h
    · rw [ite_eq_right hoff] at h
      cases hs : resolveBranchTarget tables rel ((tables.input.symbols[rel.symbol]?).getD nullSym) with
      | none => rw [hs] at h; simp [pure, EStateM.pure] at h
      | some x =>
        rw [hs] at h
        simp only [bind, pure, EStateM.pure, Bool.false_and, Bool.false_eq_true, ite_false] at h
        cases h
        rfl

/-- **A branch sent to its thunk reaches it**: the pass only does that if the offset is in the range of the branch, so that the
field keeps it, and whatever else it does it leaves the branch as it was. -/
theorem thunkStep_reaches {tables : Tables} {data : ByteArray} {secIndex : Nat} {state : ThunkState} {rel branch : Rel}
    (hb : (thunkStep tables data secIndex state rel).rels = branch :: state.rels) :
    branch = rel ∨ ∃ kind site offset, thunkKind tables.input.machine rel.typ = some kind ∧
      siteOf tables false rel { memory := data } = .ok (some site) { memory := data } ∧
      branch = { rel with symbol := state.symbols + offset / 4, addend := kind.bias, isExplicit := true } ∧
      sext (field ((state.base + offset : Int) + kind.bias - site.p) 0 kind.bits : Nat) kind.bits =
        (state.base + offset : Int) + kind.bias - site.p := by
  unfold thunkStep at hb
  dsimp only at hb
  split at hb
  · simp only [List.cons.injEq] at hb
    exact .inl hb.1.symm
  · next kind hk =>
    split at hb
    · next site after hsite =>
      obtain ⟨_, _, _, _, _, _, hsiteEq⟩ := siteOf_some hsite
      have hafter : after = { memory := data } := by
        have := siteOf_after hsite
        exact this
      subst hafter
      split at hb
      · split at hb
        · next hfit =>
          have hfits := (fits_signed_iff (thunkKind_bits hk) _).mp hfit
          refine .inr ⟨kind, site, _, hk, hsite, ?_, hfits⟩
          split at hb <;> (simp only [List.cons.injEq] at hb; exact hb.1.symm)
        · simp only [List.cons.injEq] at hb
          exact .inl hb.1.symm
      · simp only [List.cons.injEq] at hb
        exact .inl hb.1.symm
    · simp only [List.cons.injEq] at hb
      exact .inl hb.1.symm

/-- A file without a branch that needs a thunk stays as it is. -/
theorem addThunks_none {input : Input} (h : firstThunked input = none) : addThunks input = input := by
  simp only [addThunks, h]

/-- The section of thunks is laid out where the branches were computed for, as its size is what was reserved. -/
theorem withThunkSection_sections (input : Input) (at' size : Nat) :
    (withThunkSection input at' size).sections.toList =
      input.sections.toList.take (at' + 1) ++ ⟨".thunks", 1, shfAlloc + shfExecinstr, input.data.size, size, 16⟩ ::
        input.sections.toList.drop (at' + 1) := by
  simp [withThunkSection]

/-! ### Thunks in the layout they end up in -/

/-- What the thunks of a pass so far say: a known thunk has a symbol in its section, one for each word of the thunks. -/
structure ThunkInv (secIndex : Nat) (state : ThunkState) : Prop where
  known : ∀ key offset, (key, offset) ∈ state.known → ∃ sym, state.newSyms[offset / 4]? = some sym ∧ sym.shndx = secIndex ∧ sym.extended = false ∧
    sym.value = offset + (if key.2.2 then 1 else 0)
  sizes : state.bytes.length = 4 * state.newSyms.length

/-- A branch that a pass sent to its thunk. -/
def SentToThunk (tables : Tables) (data : ByteArray) (state : ThunkState) (branch : Rel) : Prop :=
  ∃ rel kind site offset key, thunkKind tables.input.machine rel.typ = some kind ∧
    siteOf tables false rel { memory := data } = .ok (some site) { memory := data } ∧
    (key, offset) ∈ state.known ∧ key.2.2 = kind.thumb ∧
    branch = { rel with symbol := state.symbols + offset / 4, addend := kind.bias, isExplicit := true } ∧
    sext (field ((state.base + offset : Int) + kind.bias - site.p) 0 kind.bits : Nat) kind.bits = (state.base + offset : Int) + kind.bias - site.p

private theorem thunkCode_length {machine : Nat} {little : Bool} {kind : ThunkKind} {secIndex offset symbol : Nat} {addend : Int} :
    ∃ n, (thunkCode machine little kind secIndex offset symbol addend).1.length = 4 * (n + 1) := by
  unfold thunkCode
  dsimp only
  split
  · split
    · exact ⟨2, by simp [thumbThunk, bytesOf]⟩
    · exact ⟨1, by simp [armThunk, bytesOf]⟩
  · exact ⟨3, by simp [aarch64Thunk, bytesOf]⟩

private theorem thunkOffset_known {state : ThunkState} {key : Nat × Int × Bool} (h : thunkIsNew state key = false) :
    (key, thunkOffset state key) ∈ state.known := by
  simp only [thunkIsNew, Option.isNone_eq_false_iff, Option.isSome_iff_exists] at h
  obtain ⟨entry, he⟩ := h
  have hmem := List.mem_of_find?_eq_some he
  have hkey : entry.1 = key := by simpa using List.find?_some he
  simp only [thunkOffset, he, Option.map_some, Option.getD_some]
  rw [← hkey]
  exact hmem

private theorem thunkOffset_new {state : ThunkState} {key : Nat × Int × Bool} (h : thunkIsNew state key = true) :
    thunkOffset state key = state.bytes.length := by
  simp only [thunkIsNew, Option.isNone_iff_eq_none] at h
  simp [thunkOffset, h]

/-- A step of a pass keeps what it says, and a branch it leaves is the one it had or one it sent to its thunk. -/
theorem thunkStep_inv {tables : Tables} {data : ByteArray} {secIndex : Nat} {state : ThunkState} {rel : Rel} (hi : ThunkInv secIndex state) :
    let next := thunkStep tables data secIndex state rel
    ThunkInv secIndex next ∧ next.symbols = state.symbols ∧ next.base = state.base ∧ (∀ entry ∈ state.known, entry ∈ next.known) ∧
      (∃ branch, next.rels = branch :: state.rels ∧ (branch = rel ∨ SentToThunk tables data next branch)) := by
  dsimp only
  unfold thunkStep
  dsimp only
  have hkeep : ThunkInv secIndex { state with rels := rel :: state.rels } := ⟨hi.known, hi.sizes⟩
  split
  · exact ⟨hkeep, rfl, rfl, fun _ h => h, _, rfl, .inl rfl⟩
  · next kind hk =>
    split
    · next site after hsite =>
      have hafter : after = { memory := data } := siteOf_after hsite
      subst hafter
      split
      · split
        · next hfit =>
          have hfits := (fits_signed_iff (thunkKind_bits hk) _).mp hfit
          split
          · next hnew =>
            generalize hkey : (rel.symbol, thunkTargetAddend tables data site kind, kind.thumb) = key at *
            obtain ⟨n, hn⟩ := thunkCode_length (machine := tables.input.machine) (little := tables.env.little) (kind := kind) (secIndex := secIndex)
              (offset := thunkOffset state key) (symbol := rel.symbol) (addend := thunkTargetAddend tables data site kind)
            generalize thunkCode tables.input.machine tables.env.little kind secIndex (thunkOffset state key) rel.symbol (thunkTargetAddend tables data site kind) = pair at hn ⊢
            obtain ⟨code, thunkRels⟩ := pair
            dsimp only at hn ⊢
            have hoff := thunkOffset_new hnew
            have hthumb : key.2.2 = kind.thumb := by rw [← hkey]
            have hindex : thunkOffset state key / 4 = state.newSyms.length := by
              rw [hoff, hi.sizes]
              omega
            refine ⟨⟨?_, ?_⟩, rfl, rfl, fun _ h => List.mem_cons_of_mem _ h, _, rfl, .inr ⟨rel, kind, site, thunkOffset state key, key, hk, hsite, List.mem_cons_self, hthumb, rfl, hfits⟩⟩
            · intro key' offset' hmem
              rcases List.mem_cons.1 hmem with he | hmem
              · obtain ⟨h1, h2⟩ := Prod.mk.inj he
                rw [h2, h1]
                refine ⟨⟨s!"__thunk_{site.sym.name}_{thunkOffset state key}", secIndex, false, thunkOffset state key + (if kind.thumb then 1 else 0), code.length, sttFunc, stbLocal, 0⟩, ?_, rfl, rfl, ?_⟩
                · rw [hindex]
                  simp
                · rw [hthumb]
              · obtain ⟨sym, h1, h2, h3, h4⟩ := hi.known key' offset' hmem
                obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.1 h1
                exact ⟨sym, by rw [List.getElem?_append_left hlt]; exact h1, h2, h3, h4⟩
            · simp only [List.length_append, List.length_cons, List.length_map, List.length_range, hn, hi.sizes]
              have : 4 * (n + 1) / 4 = n + 1 := by omega
              rw [this]
              omega
          · next hold =>
            have hnotnew : thunkIsNew state (rel.symbol, thunkTargetAddend tables data site kind, kind.thumb) = false := by simpa using hold
            exact ⟨⟨hi.known, hi.sizes⟩, rfl, rfl, fun _ h => h, _, rfl, .inr ⟨rel, kind, site, _, _, hk, hsite, thunkOffset_known hnotnew, rfl, rfl, hfits⟩⟩
        · exact ⟨hkeep, rfl, rfl, fun _ h => h, _, rfl, .inl rfl⟩
      · exact ⟨hkeep, rfl, rfl, fun _ h => h, _, rfl, .inl rfl⟩
    · exact ⟨hkeep, rfl, rfl, fun _ h => h, _, rfl, .inl rfl⟩

private theorem SentToThunk.later {tables : Tables} {data : ByteArray} {a b : ThunkState} {branch : Rel} (h : SentToThunk tables data a branch)
    (hs : b.symbols = a.symbols) (hb : b.base = a.base) (hk : ∀ entry ∈ a.known, entry ∈ b.known) : SentToThunk tables data b branch := by
  obtain ⟨rel, kind, site, offset, key, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨rel, kind, site, offset, key, h1, h2, hk _ h3, h4, by rw [hs]; exact h5, by rw [hb]; exact h6⟩

/-- A pass over relocations: what it leaves is what it had, or a branch it sent to its thunk. -/
theorem thunkPass_fold {tables : Tables} {data : ByteArray} {secIndex : Nat} (rels : List Rel) (init : ThunkState) (hi : ThunkInv secIndex init)
    {all : List Rel} (hrels : rels ⊆ all) (hold : ∀ branch ∈ init.rels, branch ∈ all ∨ SentToThunk tables data init branch) :
    let done := rels.foldl (thunkStep tables data secIndex) init
    ThunkInv secIndex done ∧ done.symbols = init.symbols ∧ done.base = init.base ∧ ∀ branch ∈ done.rels, branch ∈ all ∨ SentToThunk tables data done branch := by
  induction rels generalizing init with
  | nil => exact ⟨hi, rfl, rfl, hold⟩
  | cons rel rest ih =>
    obtain ⟨h1, h2, h3, h4, branch, h5, h6⟩ := thunkStep_inv (tables := tables) (data := data) (rel := rel) (secIndex := secIndex) hi
    simp only [List.foldl_cons]
    refine (fun ⟨g1, g2, g3, g4⟩ => ⟨g1, g2.trans h2, g3.trans h3, g4⟩) (ih _ h1 (fun _ hm => hrels (List.mem_cons_of_mem _ hm)) (fun b hb => ?_))
    rw [h5] at hb
    rcases List.mem_cons.1 hb with rfl | hb
    · rcases h6 with rfl | h6
      · exact .inl (hrels List.mem_cons_self)
      · exact .inr h6
    · rcases hold b hb with hm | hs
      · exact .inl hm
      · exact .inr (hs.later h2 h3 h4)

private theorem placeSection_addrs (layout : Layout) (sec : ElfLinker.Section) :
    (placeSection layout sec).addrs.size = layout.addrs.size + 1 ∧ (∀ i, i < layout.addrs.size → (placeSection layout sec).addrs[i]? = layout.addrs[i]?) ∧
      (hasFlag sec.flags shfAlloc = true → ∃ a, (placeSection layout sec).addrs[layout.addrs.size]? = some (some a)) := by
  unfold placeSection
  split
  · refine ⟨by simp, fun i hi => ?_, fun _ => ⟨alignUp layout.cursor sec.align, by simp⟩⟩
    simp [Array.getElem?_push, Nat.ne_of_lt hi]
  · next hf =>
    refine ⟨by simp, fun i hi => ?_, fun h => absurd h hf⟩
    simp [Array.getElem?_push, Nat.ne_of_lt hi]

/-- An allocated section has an address. -/
theorem layoutSections_addr (sections : List ElfLinker.Section) (base : Nat) {i : Nat} {sec : ElfLinker.Section} (hs : sections[i]? = some sec)
    (hf : hasFlag sec.flags shfAlloc = true) : ∃ a, ((layoutSections sections base).addrs[i]?) = some (some a) := by
  have key : ∀ (rest : List ElfLinker.Section) (init : Layout),
      (rest.foldl placeSection init).addrs.size = init.addrs.size + rest.length ∧
      (∀ j, j < init.addrs.size → (rest.foldl placeSection init).addrs[j]? = init.addrs[j]?) ∧
      ∀ j, rest[j]? = some sec → ∃ a, (rest.foldl placeSection init).addrs[init.addrs.size + j]? = some (some a) := by
    intro rest
    induction rest with
    | nil => intro init; simp
    | cons head tail ih =>
      intro init
      obtain ⟨p1, p2, p3⟩ := placeSection_addrs init head
      obtain ⟨g1, g2, g3⟩ := ih (placeSection init head)
      simp only [List.foldl_cons]
      refine ⟨by rw [g1, p1]; simp only [List.length_cons]; omega, fun j hj => ?_, fun j hj => ?_⟩
      · rw [g2 j (by omega), p2 j hj]
      · cases j with
        | zero =>
          obtain rfl : head = sec := by simpa using hj
          obtain ⟨a, ha⟩ := p3 hf
          exact ⟨a, by rw [g2 _ (by omega)]; simpa using ha⟩
        | succ j =>
          obtain ⟨a, ha⟩ := g3 j (by simpa using hj)
          exact ⟨a, by rw [p1] at ha; rw [← ha]; congr 1; omega⟩
  obtain ⟨_, _, h3⟩ := key sections { cursor := base }
  obtain ⟨a, ha⟩ := h3 i hs
  exact ⟨a, by simpa [layoutSections] using ha⟩

private theorem thunkKind_machine {machine typ : Nat} {kind : ThunkKind} (h : thunkKind machine typ = some kind) : machine = 183 ∨ machine = 40 := by
  unfold thunkKind at h
  split at h <;> first | (cases h; simp) | cases h

/-- **A branch sent to its thunk reaches it in the layout of the file that comes out.** The file is laid out where the pass worked out the
branch, as the thunks only add bytes and symbols after what's there: the place of the branch is the one it had, and its symbol is the one of
its thunk, at the offset of the thunk in its section, with the bit of its instruction set, and the distance is in the range of its field. -/
theorem thunk_reaches_layout {input : Input} {at' reserved : Nat} (hat : at' < input.sections.size) (hsmall : at' + 1 < shnLoreserve) (padding : ByteArray)
    {branch : Rel} (hb : branch ∈ (thunkPass input at' reserved).rels) :
    let laid := withThunkSection input at' reserved
    let done := thunkPass input at' reserved
    let output : Input := { laid with
      data := padding
      symbols := laid.symbols ++ done.newSyms.toArray
      relocations := done.rels.reverse ++ done.newRels }
    let tables := layoutTables output
    tables.addrs = (layoutTables laid).addrs ∧
    (branch ∈ laid.relocations ∨ ∃ kind address offset thumb sec placeBase sym,
      (tables.addrs[at' + 1]?).join = some address ∧ thunkKind input.machine branch.typ = some kind ∧ branch.addend = kind.bias ∧ branch.isExplicit = true ∧
      relocatedSection tables branch.target = some (sec, placeBase) ∧
      tables.input.symbols[branch.symbol]? = some sym ∧
      resolveBranchTarget tables branch sym = some (address + offset + thumb) ∧ thumb = (if kind.thumb then 1 else 0) ∧
      sext (field ((address + offset : Int) + kind.bias - (placeBase + branch.offset : Nat)) 0 kind.bits : Nat) kind.bits =
        (address + offset : Int) + kind.bias - (placeBase + branch.offset : Nat)) := by
  intro laid done output tables
  refine ⟨rfl, ?_⟩
  have hpass : ThunkInv (at' + 1) done ∧ done.symbols = laid.symbols.size ∧ done.base = (((layoutTables laid).addrs[at' + 1]?).join).getD 0 ∧
      ∀ branch ∈ done.rels, branch ∈ laid.relocations ∨ SentToThunk (layoutTables laid) laid.data done branch :=
    thunkPass_fold (all := laid.relocations) laid.relocations
      { base := ((((layoutTables laid).addrs)[at' + 1]?).join).getD 0, symbols := laid.symbols.size } ⟨by simp, by simp⟩ (fun _ h => h) (by simp)
  obtain ⟨g1, g2, g3, g4⟩ := hpass
  rcases g4 branch hb with hm | hsent
  · exact .inl hm
  right
  obtain ⟨rel, kind, site, offset, key, hk, hsite, hkn, hth, hbr, hfit⟩ := hsent
  obtain ⟨sec, placeBase, s, hrs, _, _, hs⟩ := siteOf_some hsite
  obtain ⟨sym, hsym1, hsym2, hsym3, hsym4⟩ := g1.known key offset hkn
  have hsec : laid.sections.toList[at' + 1]? = some ⟨".thunks", 1, shfAlloc + shfExecinstr, input.data.size, reserved, 16⟩ := by
    have hl : (input.sections.toList.take (at' + 1)).length = at' + 1 := by
      simp only [List.length_take, Array.length_toList]
      omega
    rw [show laid.sections.toList = _ from withThunkSection_sections input at' reserved, List.getElem?_append_right (by omega), hl]
    simp
  obtain ⟨address, haddr⟩ := layoutSections_addr laid.sections.toList laid.base hsec (by show hasFlag (shfAlloc + shfExecinstr) shfAlloc = true; decide)
  have htaddr : tables.addrs[at' + 1]? = some (some address) := haddr
  have hbase : done.base = address := by
    rw [g3]
    show (((layoutSections laid.sections.toList laid.base).addrs[at' + 1]?).join).getD 0 = address
    rw [haddr]
    rfl
  have hsyms : done.symbols = laid.symbols.size := g2
  have hmachine : input.machine = 183 ∨ input.machine = 40 := thunkKind_machine hk
  have hshn : at' + 1 ≠ shnUndef ∧ at' + 1 ≠ shnAbs ∧ at' + 1 ≠ shnCommon ∧ ¬ shnLoreserve ≤ at' + 1 := by
    simp only [shnUndef, shnAbs, shnCommon, shnLoreserve] at hsmall ⊢
    omega
  have hsymAt : tables.input.symbols[done.symbols + offset / 4]? = some sym := by
    show (laid.symbols ++ done.newSyms.toArray)[done.symbols + offset / 4]? = some sym
    rw [hsyms, Array.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    simpa using hsym1
  have hres : resolveBranchTarget tables { rel with symbol := done.symbols + offset / 4, addend := kind.bias, isExplicit := true } sym =
      some (address + offset + (if kind.thumb then 1 else 0)) := by
    have hnot : ∀ shn, at' + 1 ≠ shn → special sym shn = false := by
      intro shn hne
      simp [special, hsym2, hsym3, hne]
    have hppc : (tables.input.machine == emPpc64) = false := by
      show (input.machine == emPpc64) = false
      rcases hmachine with h | h <;> simp [h, emPpc64]
    simp only [resolveBranchTarget, hppc, Bool.false_and, Bool.false_eq_true, ↓reduceIte, resolve, hnot _ hshn.1, hnot _ hshn.2.1, hnot _ hshn.2.2.1, hsym2, hsym3]
    simp only [Bool.not_false, Bool.true_and, hshn.2.2.2, decide_false, Bool.false_eq_true, ↓reduceIte, htaddr, Option.join_some, Option.map_some, Nat.add_zero, hsym4, hth]
    congr 1
    omega
  refine ⟨kind, address, offset, _, sec, placeBase, sym, by rw [htaddr]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · rw [hbr]; exact hk
  · rw [hbr]
  · rw [hbr]
  · rw [hbr]
    exact hrs
  · rw [hbr]
    exact hsymAt
  · rw [hbr]
    exact hres
  · rw [hbr]
    have hp : site.p = placeBase + rel.offset := by rw [hs]
    rw [hp, hbase] at hfit
    exact hfit

/-- What comes out of `addThunks`: the file as it was, or the file of a pass that its branches go through `thunk_reaches_layout` for. -/
theorem addThunks_cases (input : Input) :
    addThunks input = input ∨ ∃ at' reserved, at' < input.sections.size ∧
      addThunks input = { withThunkSection input at' reserved with
        data := input.data ++ ByteArray.mk (((thunkPass input at' reserved).bytes ++ List.replicate (reserved - (thunkPass input at' reserved).bytes.length) 0).map UInt8.ofNat).toArray
        symbols := (withThunkSection input at' reserved).symbols ++ (thunkPass input at' reserved).newSyms.toArray
        relocations := (thunkPass input at' reserved).rels.reverse ++ (thunkPass input at' reserved).newRels } := by
  unfold addThunks
  split
  · exact .inl rfl
  · next at' hfirst =>
    have hat : at' < input.sections.size := by
      simp only [firstThunked, Option.map_eq_some_iff] at hfirst
      obtain ⟨rel, hf, rfl⟩ := hfirst
      have hfound := List.find?_some hf
      split at hfound
      · next site _ hsite =>
        obtain ⟨sec, _, _, hrs, _⟩ := siteOf_some hsite
        simp only [relocatedSection, bind, Option.bind_eq_some_iff] at hrs
        obtain ⟨sec', hsec', _⟩ := hrs
        exact (Array.getElem?_eq_some_iff.1 hsec').1
      · cases hfound
    dsimp only
    split
    · split
      · exact .inl rfl
      · exact .inr ⟨at', _, hat, rfl⟩
    · split
      · exact .inl rfl
      · exact .inr ⟨at', _, hat, rfl⟩

/-! ### Misalignment -/

/-- **`aligned` is exact**: a relocation is aligned when, and only when, its table asks for an alignment that its value has. -/
theorem aligned_iff (env : Env) (state : LinkState) (site : Site) :
    aligned env state site = true ↔ ∀ alignment value, alignCheck env state site = some (alignment, value) → value % (alignment : Int) = 0 := by
  unfold aligned
  cases alignCheck env state site with
  | none => simp
  | some x =>
    obtain ⟨n, v⟩ := x
    simp

/-- **A relocation warns exactly if it can't store what it says**, once, for its range if that is what's wrong, and else for its alignment. -/
theorem checkField_warnings (env : Env) (site : Site) (state : LinkState) :
    (stateOf (checkField env site state)).warnings =
      if fieldFits env state site = true ∧ aligned env state site = true then state.warnings else fieldProblem env state site :: state.warnings := by
  rw [checkField_run]
  simp only [stateOf, fieldOk, Bool.and_eq_true]
  split <;> rfl

/-- What it warns of. -/
theorem fieldProblem_alignment {env : Env} {state : LinkState} {site : Site} (hf : fieldFits env state site = true) {alignment : Nat} {value : Int}
    (ha : alignCheck env state site = some (alignment, value)) :
    fieldProblem env state site = s!"relocation of type {site.rel.typ} at {site.p} needs a value aligned to {alignment}" := by
  simp [fieldProblem, hf, ha]

/-- **What the instruction is decides what a `DS` relocation needs**: 16 of a `DQ` form, which has four low bits of its own, and 4 of the others. -/
theorem alignCheck_ds {env : Env} {state : LinkState} {site : Site} (hm : env.machine = 21) (ht : site.rel.typ = 56) :
    alignCheck env state site = some (if ppcIsDq (ppcInsnAt env state site) then 16 else 4, site.s + site.a) := by
  simp [alignCheck, hm, ht]

/-- `R_MIPS_26` stores the low bits of what it means to reach: it does, if that is in the 256 MiB of the place. -/
theorem mips26_region {env : Env} {state : LinkState} {site : Site} (hm : env.machine = 8) (ht : site.rel.typ = 4) :
    fieldOf env state site =
      some ⟨.unsigned, 28, mips26Target site (readNat state.memory env.little site.off 4) - ((site.p + 4) >>> 28) * 2 ^ 28⟩ := by
  simp [fieldOf, mipsField, hm, ht]

/-- What an alignment is for: a field that drops `k` low bits gives back its value only if they are 0. -/
theorem aligned_keeps_value (value : Int) (k : Nat) : (value >>> k) * (2 : Int) ^ k = value ↔ value % (((2 ^ k : Nat)) : Int) = 0 := by
  have hp : ((2 : Int) ^ k) = ((2 ^ k : Nat) : Int) := by simp
  rw [Int.shiftRight_eq_div_pow, hp]
  constructor
  · intro h
    exact Int.emod_eq_zero_of_dvd ⟨_, by rw [Int.mul_comm]; exact h.symm⟩
  · intro h
    exact Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero h)

end Bap.Proofs.Linker
