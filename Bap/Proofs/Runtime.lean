import Bap.Analysis.CallSites
import Bap.Analysis.Cff
import Bap.Analysis.Journal
import Bap.Linux.Contract

/-! What the journal, `Cff` and `Contract` say is so, as far as it is a matter of their pure parts:

* a return ends the innermost call that comes back there and the calls within it, and nothing else, and a call that was just made ends
  where it said it would (`CallSites.pop_spec`, `CallSites.push_pop`);
* a run compared with itself parts nowhere and is given nothing differently (`Journal.compare_self`);
* each cycle that `Cff` reports is the states as they were, each time round (`Cff.cyclesOf_sound`);
* each byte of a contract is one that changed, and what it is after (`Contract.changes_sound`).

What runs a machine, reads its memory or hooks it is `IO` and is tested, not proved. -/

namespace Bap.Analysis

/-! ### Call sites -/

namespace CallSites

/-- Coming back to `pc` ends the first site that is it, counting from `gone`, and leaves what is after it, and no site before that is it. -/
theorem popFrom_spec {pc : Nat} : ∀ {sites : List Nat} {gone _rest n : Nat} {left : List Nat},
    popFrom pc sites gone = some (left, n) →
    ∃ k, n = gone + k + 1 ∧ left = sites.drop (k + 1) ∧ (sites[k]? = some pc ∨ sites[k]? = some (pc + 1)) ∧
      ∀ j < k, sites[j]? ≠ some pc ∧ sites[j]? ≠ some (pc + 1)
  | [], _, _, _, _, h => by simp [popFrom] at h
  | site :: rest, gone, _, n, left, h => by
    simp only [popFrom] at h
    by_cases hit : (site == pc || site == pc + 1) = true
    · simp only [hit, ↓reduceIte] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hl, hn⟩ := h
      refine ⟨0, by omega, by simp [hl], ?_, by intro j hj; omega⟩
      simp only [Bool.or_eq_true, beq_iff_eq] at hit
      simpa using hit
    · have hmiss : (site == pc || site == pc + 1) = false := by simpa using hit
      simp only [hmiss, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨k, hn, hl, hk, hbefore⟩ := popFrom_spec (gone := gone + 1) (_rest := 0) h
      refine ⟨k + 1, by omega, by simpa using hl, by simpa using hk, ?_⟩
      intro j hj
      cases j with
      | zero =>
        simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hit
        simp [hit.1, hit.2]
      | succ j => simpa using hbefore j (by omega)

/-- A return takes off the innermost call that comes back to it and those within it, and the depth goes down by as many: one at least. -/
theorem pop_spec {calls rest : CallSites} {pc gone : Nat} (h : calls.pop pc = some (rest, gone)) :
    rest.sites = calls.sites.drop gone ∧ rest.depth = calls.depth - gone ∧ 0 < gone ∧
      (calls.sites[gone - 1]? = some pc ∨ calls.sites[gone - 1]? = some (pc + 1)) := by
  simp only [pop] at h
  split at h
  · cases h
  · split at h
    · next left n hfrom =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hrest, hgone⟩ := h
      obtain ⟨k, hn, hl, hk, _⟩ := popFrom_spec (gone := 0) (_rest := 0) hfrom
      subst hgone hrest
      refine ⟨by simp [hl, hn], by simp, by omega, ?_⟩
      have : n - 1 = k := by omega
      rw [this]
      exact hk
    · cases h

/-- What isn't a site doesn't end a call. -/
theorem pop_none {calls : CallSites} {pc : Nat} (h : calls.isSite pc = false) : calls.pop pc = none := by
  simp [pop, h]

/-- A call that has just been made ends where it said it would come back to, and takes off only itself. -/
theorem push_pop (calls : CallSites) (site : Nat) :
    ((calls.push site).pop site).map (fun result => (result.1.sites, result.1.depth, result.2)) = some (calls.sites, calls.depth, 1) := by
  have hsite : (calls.push site).isSite site = true := by
    simp [isSite, push]
  simp only [pop]
  simp only [hsite, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp [push, popFrom]

end CallSites

/-! ### Comparing runs -/

namespace Journal.Journal

/-- Each pair of threads of a run with itself is a thread with itself. -/
theorem threadPairs_self {record : Record} {pair : Nat × Option Emu.ThreadId × Option Emu.ThreadId}
    (h : pair ∈ threadPairs record record) : pair.2.1 = pair.2.2 := by
  simp only [threadPairs, List.mem_map, List.mem_range] at h
  obtain ⟨ordinal, _, rfl⟩ := h
  rfl

theorem branchAt_self (record : Record) (ordinal : Nat) (thread : Option Emu.ThreadId) :
    branchAt record record (ordinal, thread, thread) = none := by
  simp [branchAt, List.find?_eq_none]

theorem serviceAt_self (record : Record) (ordinal : Nat) (thread : Option Emu.ThreadId) :
    serviceAt record record (ordinal, thread, thread) = none := by
  simp [serviceAt, sameService, List.find?_eq_none]

/-- A run compared with itself parts nowhere, and is given nothing differently. -/
theorem compare_self (record : Record) : (compare record record).branch = none ∧ (compare record record).service = none := by
  have hbranches : (threadPairs record record).filterMap (branchAt record record) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro pair hpair
    obtain ⟨ordinal, thread, other⟩ := pair
    have := threadPairs_self hpair
    simp only at this
    subst this
    exact branchAt_self record ordinal thread
  have hservices : (threadPairs record record).filterMap (serviceAt record record) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro pair hpair
    obtain ⟨ordinal, thread, other⟩ := pair
    have := threadPairs_self hpair
    simp only at this
    subst this
    exact serviceAt_self record ordinal thread
  simp [compare, hbranches, hservices, earliest]

end Journal.Journal

/-! ### Cycles of a flattened machine -/

namespace Cff

/-- What `Cycle.holds` checks: it comes round twice at least, and each time round it is the states that it says. -/
theorem Cycle.holds_spec {states : Array Nat} {cycle : Cycle} (h : cycle.holds states = true) :
    cycle.repeats ≥ 2 ∧ cycle.states ≠ [] ∧
      ∀ round < cycle.repeats, ∀ offset < cycle.states.length,
        states[cycle.first + round * cycle.states.length + offset]? = cycle.states[offset]? := by
  simp only [Cycle.holds, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hrepeats, hempty⟩, hall⟩ := h
  refine ⟨hrepeats, ?_, fun round hround offset hoffset => hall round hround offset hoffset⟩
  simpa [List.isEmpty_iff] using hempty

/-- Each cycle that is reported is the states as they were, each time round. -/
theorem cyclesOf_sound {thread : Emu.ThreadId} {states : Array Nat} {longest : Nat} {cycle : Cycle}
    (h : cycle ∈ cyclesOf thread states longest) :
    cycle.repeats ≥ 2 ∧ cycle.states ≠ [] ∧
      ∀ round < cycle.repeats, ∀ offset < cycle.states.length,
        states[cycle.first + round * cycle.states.length + offset]? = cycle.states[offset]? := by
  simp only [cyclesOf, List.mem_filter] at h
  exact Cycle.holds_spec h.2

end Cff

/-! ### Contracts -/

namespace Contract

/-- Each address of a run is one of those that it was made of. -/
theorem runsOf_mem : ∀ {addresses : List Nat} {start count : Nat}, (start, count) ∈ runsOf addresses →
    ∀ offset < count, start + offset ∈ addresses
  | [], _, _, h => by simp [runsOf] at h
  | address :: rest, start, count, h => by
    simp only [runsOf] at h
    split at h
    · next s c more hruns =>
      have hfirst := runsOf_mem (addresses := rest) (start := s) (count := c) (by rw [hruns]; simp)
      have hmore : ∀ run ∈ more, ∀ offset < run.2, run.1 + offset ∈ rest := fun run hrun offset hoffset =>
        runsOf_mem (addresses := rest) (by rw [hruns]; simp [hrun]) offset hoffset
      split at h
      · next hnext =>
        simp only [beq_iff_eq] at hnext
        simp only [List.mem_cons, Prod.mk.injEq] at h
        rcases h with ⟨hs, hc⟩ | h
        · intro offset hoffset
          subst hs hc
          cases offset with
          | zero => simp
          | succ offset =>
            have := hfirst offset (by omega)
            simp only [List.mem_cons]
            right
            rw [← hnext] at this
            simpa [Nat.add_assoc, Nat.add_comm 1 offset] using this
        · intro offset hoffset
          exact List.mem_cons_of_mem _ (hmore _ h offset hoffset)
      · simp only [List.mem_cons, Prod.mk.injEq] at h
        rcases h with ⟨hs, hc⟩ | ⟨hs, hc⟩ | h
        · intro offset hoffset
          subst hs hc
          have : offset = 0 := by omega
          simp [this]
        · intro offset hoffset
          subst hs hc
          exact List.mem_cons_of_mem _ (hfirst offset hoffset)
        · intro offset hoffset
          exact List.mem_cons_of_mem _ (hmore _ h offset hoffset)
    · next hruns =>
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨hs, hc⟩ := h
      intro offset hoffset
      subst hs hc
      have : offset = 0 := by omega
      simp [this]

/-- Each byte of what a contract says changed did: it was something else before, and it is what it says after. -/
theorem changes_sound {before after : Nat → Option UInt8} {addresses : List Nat} {start : Nat} {bytes : ByteArray}
    (h : (start, bytes) ∈ changes before after addresses) :
    ∀ offset < bytes.size, before (start + offset) ≠ after (start + offset) ∧
      bytes.data[offset]? = some ((after (start + offset)).getD 0) := by
  simp only [changes, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨⟨first, count⟩, hrun, hs, hb⟩ := h
  subst hs hb
  intro offset hoffset
  simp only [ByteArray.size, List.size_toArray, List.length_map, List.length_range] at hoffset
  have hmem := runsOf_mem hrun offset hoffset
  simp only [List.mem_filter, bne_iff_ne, ne_eq] at hmem
  refine ⟨hmem.2, ?_⟩
  simp [hoffset]

end Contract

end Bap.Analysis
