import Bap.Emu.Core
import Bap.Bil.Observe
import Bap.Proofs.Bil
import Bap.Proofs.Core

/-! Proofs about the pure core of emulator execution. `IO.Ref`s are opaque, so the generic flows of
`Bap.Emu.Core` run here on a model: a state monad over `Machine`, whose fields stand for the references
of an emulator. `Bap.Emu.step` is `stepM` after it clears the budget of a stopped run (`stepOps` only says which reference is which), so what
holds of `stepM` for arbitrary hooks and blocks holds of the code that runs, given that references behave
as state and that native code computes the semantics of its BIL (see `Bap.Jit`). -/


namespace Bap.Emu.Model

/-- The references of an emulator, for one running thread. -/
structure Core where
  state : Bil.State := {}
  pc : Nat := 0
  regions : List Region := []
  stopped : Bool := false
  threads : List ThreadContext := []
  currentThread : ThreadId := 1
  nextThread : ThreadId := 2
  pending : Option PendingBranch := none
  skip : Option Nat := none
  /-- The pcs of completed instructions. -/
  trace : List Nat := []

/-- What the outside world saw, which no rollback can take back. -/
inductive Event where
  | code (address : Nat)
  | execute (address : Nat)
  deriving DecidableEq, Repr

structure Machine where
  core : Core
  log : List Event := []

abbrev CoreM := EStateM String Core
abbrev M := EStateM String Machine

/-- An action of a hook or a block, which may do anything to the references and may fail, but cannot
hide what it did from the log. -/
def lift {α : Type} (action : CoreM α) : M α := fun m =>
  match action m.core with
  | .ok value core => .ok value { m with core }
  | .error error core => .error error { m with core }

def emit (event : Event) : M Unit := fun m => .ok () { m with log := m.log ++ [event] }

def getCore {α : Type} (f : Core → α) : M α := fun m => .ok (f m.core) m

def modifyCore (f : Core → Core) : M Unit := fun m => .ok () { m with core := f m.core }

/-- The hooks and blocks of a program. -/
structure World where
  hook : Nat → CoreM Unit
  delay : Nat → CoreM DelayKind
  block : Nat → CoreM (Nat × Bil.Effect)
  dispatch : String → CoreM Bool

/-- `Bap.Emu.stepOps`, with the state of a `Machine` for the references. -/
def ops (w : World) : StepOps M Core where
  stopped := getCore (·.stopped)
  pc := getCore (·.pc)
  skip := getCore (·.skip)
  setSkip := fun skip => modifyCore fun core => { core with skip }
  notifyCode := fun address => emit (.code address) *> lift (w.hook address)
  save := getCore id
  pending := getCore (·.pending)
  delayFor := fun address => lift (w.delay address)
  mark := fun address => modifyCore fun core => { core with trace := core.trace ++ [address] }
  execute := fun address => emit (.execute address) *> lift (w.block address)
  dispatch := fun name => lift (w.dispatch name)
  setControl := fun pc pending => modifyCore fun core => { core with pc, pending }
  halt := modifyCore fun core => { core with stopped := true }
  restore := fun before => modifyCore fun _ => before
  faultAt := fun _ => pure ()

def step (w : World) : M Bool := stepM (ε := String) (ops w)

/-- The cells of the model. `Bap.Emu.controlCells` is the same record on references. -/
def cells : ControlCells M where
  stopped := getCore (·.stopped)
  setStopped := fun stopped => modifyCore fun core => { core with stopped }
  pc := getCore (·.pc)
  skip := getCore (·.skip)
  setSkip := fun skip => modifyCore fun core => { core with skip }
  pending := getCore (·.pending)
  setControl := fun pc pending => modifyCore fun core => { core with pc, pending }

/-- The operations of the model are `stepOpsOf`, as those of the emulator are, so that which cell is which is the same. -/
theorem ops_is_stepOpsOf (w : World) :
    ops w = stepOpsOf cells (fun address => emit (.code address) *> lift (w.hook address)) (getCore id)
      (fun address => lift (w.delay address))
      (fun address => modifyCore fun core => { core with trace := core.trace ++ [address] })
      (fun address => emit (.execute address) *> lift (w.block address)) (fun name => lift (w.dispatch name))
      (fun before => modifyCore fun _ => before) (fun _ => pure ()) := rfl

def Machine.withSkip (m : Machine) (skip : Option Nat) : Machine := { m with core := { m.core with skip } }

section Laws

variable {α β : Type}

private theorem run_pure (x : α) (m : Machine) : (pure x : M α) m = .ok x m := rfl

private theorem run_get (f : Core → α) (g : α → M β) (m : Machine) :
    (getCore f >>= g) m = g (f m.core) m := rfl

private theorem run_modify (f : Core → Core) (g : Unit → M β) (m : Machine) :
    (modifyCore f >>= g) m = g () { m with core := f m.core } := rfl

private theorem run_get1 (f : Core → α) (m : Machine) : (getCore f) m = .ok (f m.core) m := rfl

private theorem run_notify (e : Event) (a : CoreM α) (g : α → M β) (m : Machine) :
    ((emit e *> lift a) >>= g) m =
      match a m.core with
      | .ok value core => g value { core, log := m.log ++ [e] }
      | .error error core => .error error { core, log := m.log ++ [e] } := by
  cases h : a m.core <;>
    simp [bind, EStateM.bind, SeqRight.seqRight, EStateM.seqRight, emit, lift, h]

private theorem run_lift (a : CoreM α) (g : α → M β) (m : Machine) :
    (lift a >>= g) m =
      match a m.core with
      | .ok value core => g value { m with core }
      | .error error core => .error error { m with core } := by
  cases h : a m.core <;> simp [bind, EStateM.bind, lift, h]

private theorem run_ite (c : Prop) [Decidable c] (a b : M α) (m : Machine) :
    (if c then a else b) m = if c then a m else b m := by
  split <;> rfl

private theorem run_seq_ite (c : Prop) [Decidable c] (a b : M α) (g : α → M β) (m : Machine) :
    ((if c then a else b) >>= g) m = if c then (a >>= g) m else (b >>= g) m := by
  split <;> rfl

end Laws

/-- The rest of a step once the hooks of `address` ran. -/
def afterHooks (w : World) (address : Nat) (m : Machine) : EStateM.Result String Machine Bool :=
  match afterHook address m.core.pc m.core.stopped with
  | .halt skip => .ok false (m.withSkip skip)
  | .redirect => .ok true m
  | .proceed => stepExecute (ε := String) (ops w) address m

/-- A step as a function of the machine. -/
theorem step_eq (w : World) (m : Machine) :
    step w m =
      if m.core.stopped = true then .ok false m
      else if (m.core.skip != some m.core.pc) = true then
        match w.hook m.core.pc { m.core with skip := none } with
        | .ok _ core => afterHooks w m.core.pc { core, log := m.log ++ [.code m.core.pc] }
        | .error error core => .error error { core, log := m.log ++ [.code m.core.pc] }
      else afterHooks w m.core.pc (m.withSkip none) := by
  simp only [step, stepM, ops, run_get, run_modify, run_ite]
  split
  · rfl
  · split
    · simp only [run_notify]
      cases w.hook m.core.pc { m.core with skip := none } with
      | error e c => rfl
      | ok v c =>
        simp only [run_get, afterHooks]
        cases afterHook m.core.pc c.pc c.stopped <;> rfl
    · simp only [afterHooks, Machine.withSkip]
      cases afterHook m.core.pc m.core.pc m.core.stopped <;> rfl

/-- A stopped thread does not run: nothing happens at all. -/
theorem step_stopped (w : World) (m : Machine) (h : m.core.stopped = true) :
    step w m = .ok false m := by
  simp [step_eq, h]

/-- The hooks of the pc are skipped when they fired for this very instruction. -/
theorem step_skipped (w : World) (m : Machine) (h : m.core.stopped = false) (hs : m.core.skip = some m.core.pc) :
    step w m = afterHooks w m.core.pc (m.withSkip none) := by
  simp [step_eq, h, hs]

/-- Otherwise they fire, once, before anything else happens. -/
theorem step_fresh (w : World) (m : Machine) (h : m.core.stopped = false) (hs : m.core.skip ≠ some m.core.pc) :
    step w m =
      match w.hook m.core.pc { m.core with skip := none } with
      | .ok _ core => afterHooks w m.core.pc { core, log := m.log ++ [.code m.core.pc] }
      | .error error core => .error error { core, log := m.log ++ [.code m.core.pc] } := by
  simp [step_eq, h, hs]

theorem afterHooks_halt (w : World) (address : Nat) (m : Machine) (h : m.core.stopped = true)
    (hp : m.core.pc = address) : afterHooks w address m = .ok false (m.withSkip (some address)) := by
  simp [afterHooks, afterHook, h, hp]

theorem afterHooks_halt_moved (w : World) (address : Nat) (m : Machine) (h : m.core.stopped = true)
    (hp : m.core.pc ≠ address) : afterHooks w address m = .ok false (m.withSkip none) := by
  simp [afterHooks, afterHook, h, hp]

/-- A hook that moves the pc keeps the instruction from executing. -/
theorem afterHooks_redirect (w : World) (address : Nat) (m : Machine) (h : m.core.stopped = false)
    (hp : m.core.pc ≠ address) : afterHooks w address m = .ok true m := by
  simp [afterHooks, afterHook, h, hp]

theorem afterHooks_proceed (w : World) (address : Nat) (m : Machine) (h : m.core.stopped = false)
    (hp : m.core.pc = address) : afterHooks w address m = stepExecute (ε := String) (ops w) address m := by
  simp [afterHooks, afterHook, h, hp]

/-! ### Executing an instruction -/

/-- The delay kind of an instruction; a delay slot has no delay of its own. -/
def delayOf (w : World) (pending : Option PendingBranch) (address : Nat) : CoreM DelayKind :=
  match pending with
  | some _ => pure .none
  | none => w.delay address

/-- Only specials go to the handlers. -/
def dispatchOf (w : World) : Bil.Effect → CoreM Bool
  | .special name => w.dispatch name
  | _ => pure false

/-- The state that a successful instruction leaves. -/
def finish (address : Nat) (c : Core) (out : Advance) : Core :=
  { c with
    pc := out.pc
    pending := out.pending
    stopped := out.stop || c.stopped
    skip := if out.stop then some address else c.skip }

/-- The state that a failed instruction leaves: exactly the one before it, apart from the control flow of
`failControl`. -/
def rollback (address : Nat) (before : Core) : Core :=
  { before with
    pc := (failControl address before.pending).1
    pending := none
    skip := (failControl address before.pending).2 }

/-- The instruction, without the rollback. -/
def body (w : World) (address : Nat) (m : Machine) : EStateM.Result String Machine Advance :=
  match delayOf w m.core.pending address m.core with
  | .error error c => .error error { core := c, log := m.log }
  | .ok delay c₁ =>
    match w.block address { c₁ with trace := c₁.trace ++ [address] } with
    | .error error c => .error error { core := c, log := m.log ++ [.execute address] }
    | .ok (next, effect) c₂ =>
      match dispatchOf w effect c₂ with
      | .error error c => .error error { core := c, log := m.log ++ [.execute address] }
      | .ok handled c₃ =>
        .ok (commit address next effect handled c₃.pc delay m.core.pending)
          { core := c₃, log := m.log ++ [.execute address] }

private theorem run_try {α : Type} (x : M α) (h : String → M α) (m : Machine) :
    (tryCatch x h : M α) m =
      match x m with
      | .ok value s => .ok value s
      | .error error s => h error s := by
  show EStateM.tryCatch x h m = _
  simp only [EStateM.tryCatch]
  cases x m <;> rfl

private theorem run_pure_bind {α β : Type} (x : α) (g : α → M β) (m : Machine) : (pure x >>= g) m = g x m := rfl

private theorem run_throw {α : Type} (error : String) (m : Machine) : (throw error : M α) m = .error error m := rfl

private theorem run_pure_mod {α : Type} (x : α) (m : Machine) (f : Core → Core) :
    (modifyCore f *> (pure x : M α)) m = .ok x { m with core := f m.core } := rfl

/-- What happens after the handlers, in `stepExecute`. -/
private theorem commit_tail (address : Nat) (out : Advance) (m : Machine) :
    ((do
      modifyCore fun core => { core with pc := out.pc, pending := out.pending }
      if out.stop = true then do
        modifyCore fun core => { core with stopped := true }
        modifyCore fun core => { core with skip := some address }
        pure !out.stop
      else pure !out.stop) : M Bool) m =
      .ok (!out.stop) { m with core := finish address m.core out } := by
  cases h : out.stop <;> simp only [run_modify, h, finish, Bool.false_eq_true, ite_false, ite_true, run_pure,
    Bool.false_or, Bool.true_or] <;> rfl

/-- `stepExecute` as a function of the machine: atomic, with the effect of `commit` on success. -/
theorem stepExecute_eq (w : World) (address : Nat) (m : Machine) :
    stepExecute (ε := String) (ops w) address m =
      match body w address m with
      | .ok out s => .ok (!out.stop) { s with core := finish address s.core out }
      | .error error s => .error error { s with core := rollback address m.core } := by
  obtain ⟨⟨state, pc, regions, stopped, threads, current, nextThread, pending, skip, trace⟩, l⟩ := m
  generalize hc : (Core.mk state pc regions stopped threads current nextThread pending skip trace) = c
  have hpending : c.pending = pending := by rw [← hc]
  cases pending with
  | none =>
    simp only [stepExecute, ops, run_get, run_try, body, delayOf, hpending, run_lift]
    cases hd : w.delay address c with
    | error e c' =>
      subst hc
      rfl
    | ok delay c₁ =>
      simp only [run_modify, run_notify]
      cases hb : w.block address { c₁ with trace := c₁.trace ++ [address] } with
      | error e c' =>
        subst hc
        rfl
      | ok v c₂ =>
        obtain ⟨next, effect⟩ := v
        cases effect with
        | normal =>
          simp only [run_pure_bind, run_get, dispatchOf]
          rw [commit_tail address (commit address next .normal false c₂.pc delay none)]
          rfl
        | jump target =>
          simp only [run_pure_bind, run_get, dispatchOf]
          rw [commit_tail address (commit address next (.jump target) false c₂.pc delay none)]
          rfl
        | cpuExn number =>
          simp only [run_pure_bind, run_get, dispatchOf]
          rw [commit_tail address (commit address next (.cpuExn number) false c₂.pc delay none)]
          rfl
        | special name =>
          simp only [run_lift, dispatchOf]
          cases hs : w.dispatch name c₂ with
          | error e c' =>
            subst hc
            rfl
          | ok handled c₃ =>
            simp only [run_get]
            rw [commit_tail address (commit address next (.special name) handled c₃.pc delay none)]
  | some branch =>
    simp only [stepExecute, ops, run_get, run_try, body, delayOf, hpending, run_pure_bind]
    have hpure : (pure DelayKind.none : CoreM DelayKind) c = .ok .none c := rfl
    simp only [run_modify, run_notify, hpure]
    cases hb : w.block address { c with trace := c.trace ++ [address] } with
    | error e c' =>
      subst hc
      rfl
    | ok v c₂ =>
      obtain ⟨next, effect⟩ := v
      cases effect with
      | normal =>
          simp only [run_pure_bind, run_get, dispatchOf]
          rw [commit_tail address (commit address next .normal false c₂.pc .none (some branch))]
          rfl
      | jump target =>
          simp only [run_pure_bind, run_get, dispatchOf]
          rw [commit_tail address (commit address next (.jump target) false c₂.pc .none (some branch))]
          rfl
      | cpuExn number =>
          simp only [run_pure_bind, run_get, dispatchOf]
          rw [commit_tail address (commit address next (.cpuExn number) false c₂.pc .none (some branch))]
          rfl
      | special name =>
        simp only [run_lift, dispatchOf]
        cases hs : w.dispatch name c₂ with
        | error e c' =>
          subst hc
          rfl
        | ok handled c₃ =>
          simp only [run_get]
          rw [commit_tail address (commit address next (.special name) handled c₃.pc .none (some branch))]

/-! ### Control flow -/

theorem advance_fallthrough (address next : Nat) (handled : Bool) :
    advance address next .normal handled .none none = { pc := next } := rfl

theorem advance_jump {width : Nat} (address next : Nat) (target : BitVec width) (handled : Bool) :
    advance address next (.jump target) handled .none none = { pc := target.toNat } := rfl

/-- A taken delayed branch runs its slot, whatever the block reports as its fall-through, and remembers
where to go then. -/
theorem advance_delayed {width : Nat} (address next : Nat) (target : BitVec width) (handled : Bool) :
    advance address next (.jump target) handled .delayed none =
      { pc := address + 4, pending := some ⟨address, target.toNat⟩ } := rfl

/-- So does a taken likely branch. -/
theorem advance_likely_taken {width : Nat} (address next : Nat) (target : BitVec width) (handled : Bool) :
    advance address next (.jump target) handled .likely none =
      { pc := address + 4, pending := some ⟨address, target.toNat⟩ } := rfl

/-- An untaken likely branch skips its slot. -/
theorem advance_likely_skip (address next : Nat) (handled : Bool) :
    advance address next .normal handled .likely none = { pc := next + 4 } := rfl

/-- An untaken delayed branch falls through into its slot, as an ordinary instruction after it. -/
theorem advance_delayed_untaken (address next : Nat) (handled : Bool) :
    advance address next .normal handled .delayed none = { pc := next } := rfl

/-- The slot completes, and the branch is taken. -/
theorem advance_slot (address next : Nat) (branch : PendingBranch) (handled : Bool) (delay : DelayKind) :
    advance address next .normal handled delay (some branch) = { pc := branch.target } := rfl

/-- A special served in a slot completes the slot too. -/
theorem advance_slot_special (address next : Nat) (name : String) (branch : PendingBranch) (delay : DelayKind) :
    advance address next (.special name) true delay (some branch) = { pc := branch.target } := rfl

/-- A special nobody serves is a precise exception: the pc and the pending branch stay, and the thread
stops, so that a handler that shows up later can complete the slot and the branch. -/
theorem advance_unhandled (address next : Nat) (name : String) (delay : DelayKind) (pending : Option PendingBranch) :
    advance address next (.special name) false delay pending = { pc := address, pending, stop := true } := rfl

theorem advance_cpuExn (address next number : Nat) (handled : Bool) (delay : DelayKind)
    (pending : Option PendingBranch) :
    advance address next (.cpuExn number) handled delay pending = { pc := address, pending, stop := true } := rfl

/-- `stop` means exactly an instruction that could not complete. -/
theorem advance_stop_iff (address next : Nat) (effect : Bil.Effect) (handled : Bool) (delay : DelayKind)
    (pending : Option PendingBranch) :
    (advance address next effect handled delay pending).stop = true ↔
      match effect with
      | .special _ => handled = false
      | .cpuExn _ => True
      | _ => False := by
  cases effect with
  | normal => cases pending <;> simp [advance]
  | jump target => cases pending <;> (try cases delay) <;> simp [advance]
  | special name => cases handled <;> simp [advance] <;> cases pending <;> simp
  | cpuExn number => simp [advance]

/-- A handler that serves a special and moves the pc wins. -/
theorem commit_redirect (address next current : Nat) (effect : Bil.Effect) (delay : DelayKind)
    (pending : Option PendingBranch) (h : current ≠ address) :
    commit address next effect true current delay pending = { pc := current } := by
  simp [commit, h]

/-- Otherwise `commit` is `advance`. -/
theorem commit_unmoved (address next : Nat) (effect : Bil.Effect) (handled : Bool) (delay : DelayKind)
    (pending : Option PendingBranch) :
    commit address next effect handled address delay pending = advance address next effect handled delay pending := by
  simp [commit]

theorem commit_unhandled (address next current : Nat) (effect : Bil.Effect) (delay : DelayKind)
    (pending : Option PendingBranch) :
    commit address next effect false current delay pending = advance address next effect false delay pending := by
  simp [commit]

/-! ### A step and its log -/

/-- Fresh hooks that neither stop the thread nor move the pc: the hooks fire once, then the instruction
executes once, and the machine ends up as the instruction says. -/
theorem step_fresh_proceed (w : World) (m : Machine) {c₀ : Core} {u : Unit} {out : Advance} {s : Machine}
    (h : m.core.stopped = false) (hs : m.core.skip ≠ some m.core.pc)
    (hook : w.hook m.core.pc { m.core with skip := none } = .ok u c₀)
    (hc : c₀.stopped = false) (hp : c₀.pc = m.core.pc)
    (hb : body w m.core.pc { core := c₀, log := m.log ++ [.code m.core.pc] } = .ok out s) :
    step w m = .ok (!out.stop) { s with core := finish m.core.pc s.core out } := by
  rw [step_fresh w m h hs, hook]
  simp only
  rw [afterHooks_proceed w _ _ hc hp, stepExecute_eq, hb]

/-- The log of a block that ran: its execution comes after what was logged before, and is the only entry. -/
theorem body_log (w : World) (address : Nat) (m : Machine) {out : Advance} {s : Machine}
    (h : body w address m = .ok out s) : s.log = m.log ++ [.execute address] := by
  simp only [body] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · simp only [EStateM.Result.ok.injEq] at h
        rw [← h.2]

/-- The log of a failed block has at most that entry: a fetch failure runs nothing. -/
theorem body_error_log (w : World) (address : Nat) (m : Machine) {error : String} {s : Machine}
    (h : body w address m = .error error s) : s.log = m.log ∨ s.log = m.log ++ [.execute address] := by
  simp only [body] at h
  split at h
  · simp only [EStateM.Result.error.injEq] at h
    exact Or.inl (by rw [← h.2])
  · split at h
    · simp only [EStateM.Result.error.injEq] at h
      exact Or.inr (by rw [← h.2])
    · split at h
      · simp only [EStateM.Result.error.injEq] at h
        exact Or.inr (by rw [← h.2])
      · cases h

/-- In every step, the hooks fire once for a fresh instruction, and not at all otherwise; the instruction
executes at most once, and only after them. -/
theorem step_log (w : World) (m : Machine) {result : Bool} {s : Machine} (h : m.core.stopped = false)
    (hstep : step w m = .ok result s) :
    (s.log = m.log ++ (if m.core.skip = some m.core.pc then [] else [.code m.core.pc])) ∨
      (s.log = m.log ++ (if m.core.skip = some m.core.pc then [] else [.code m.core.pc]) ++ [.execute m.core.pc]) := by
  have after : ∀ (address : Nat) (n : Machine), afterHooks w address n = .ok result s →
      s.log = n.log ∨ s.log = n.log ++ [.execute address] := by
    intro address n ha
    simp only [afterHooks] at ha
    split at ha
    · simp only [EStateM.Result.ok.injEq] at ha
      exact Or.inl (by rw [← ha.2]; rfl)
    · simp only [EStateM.Result.ok.injEq] at ha
      exact Or.inl (by rw [← ha.2])
    · rw [stepExecute_eq] at ha
      split at ha
      · rename_i out s' hb
        simp only [EStateM.Result.ok.injEq] at ha
        exact Or.inr (by rw [← ha.2]; show s'.log = _; exact body_log w address n hb)
      · cases ha
  by_cases hs : m.core.skip = some m.core.pc
  · rw [step_skipped w m h hs] at hstep
    simpa [hs, Machine.withSkip] using after _ _ hstep
  · rw [step_fresh w m h hs] at hstep
    split at hstep
    · have := after _ _ hstep
      simpa [hs] using this
    · cases hstep

/-- Stopping in a hook keeps the instruction from running, and leaves the skip marker. -/
theorem step_hook_stops (w : World) (m : Machine) {c₀ : Core} {u : Unit}
    (h : m.core.stopped = false) (hs : m.core.skip ≠ some m.core.pc)
    (hook : w.hook m.core.pc { m.core with skip := none } = .ok u c₀)
    (hc : c₀.stopped = true) (hp : c₀.pc = m.core.pc) :
    step w m = .ok false { core := { c₀ with skip := some m.core.pc }, log := m.log ++ [.code m.core.pc] } := by
  rw [step_fresh w m h hs, hook]
  simp only
  rw [afterHooks_halt w _ _ hc hp]
  rfl

/-- Resuming does not fire the hooks again: no re-fires. After a hook stopped the thread at an instruction,
the next step, once resumed, goes straight to the instruction, so that the hooks ran once for it. -/
theorem resume_does_not_refire (w : World) (core : Core) (log : List Event) (address : Nat)
    (hp : core.pc = address) :
    step w { core := { core with skip := some address, stopped := false }, log } =
      stepExecute (ε := String) (ops w) address { core := { core with skip := none, stopped := false }, log } := by
  subst hp
  rw [step_skipped w _ rfl rfl]
  exact afterHooks_proceed w core.pc _ rfl rfl

/-- A failed instruction restores everything it found; only the control flow of `failControl` differs. -/
theorem stepExecute_error (w : World) (address : Nat) (m : Machine) {error : String} {s : Machine}
    (h : stepExecute (ε := String) (ops w) address m = .error error s) :
    s.core = rollback address m.core := by
  rw [stepExecute_eq] at h
  split at h
  · cases h
  · simp only [EStateM.Result.error.injEq] at h
    rw [← h.2]

/-- Exactness of the rollback, field by field. -/
theorem rollback_fields (address : Nat) (before : Core) :
    (rollback address before).state = before.state ∧ (rollback address before).regions = before.regions ∧
    (rollback address before).stopped = before.stopped ∧ (rollback address before).threads = before.threads ∧
    (rollback address before).currentThread = before.currentThread ∧
    (rollback address before).nextThread = before.nextThread ∧ (rollback address before).trace = before.trace ∧
    (rollback address before).pending = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A fault outside a slot retries the instruction, with no second firing of its hooks. -/
theorem rollback_no_pending (address : Nat) (before : Core) (h : before.pending = none) :
    (rollback address before).pc = address ∧ (rollback address before).skip = some address := by
  simp [rollback, failControl, h]

/-- A fault in a slot rewinds to the branch, which runs again, with its hooks, and the slot after it. -/
theorem rollback_slot (address : Nat) (before : Core) (branch : PendingBranch) (h : before.pending = some branch) :
    (rollback address before).pc = branch.branch ∧ (rollback address before).skip = none := by
  simp [rollback, failControl, h]

/-! ### Snapshots -/

/-- What `snapshot` reads from the references. -/
def capture (core : Core) (processMemory : List (Nat × List Region) := []) : Snapshot :=
  ⟨core.state, core.pc, core.regions, core.stopped, core.threads, core.currentThread, core.nextThread, core.pending,
    processMemory, core.skip⟩

/-- What `restore` writes to the references. -/
def restoreCore (snapshot : Snapshot) (core : Core) : Core :=
  { core with
    state := snapshot.state
    pc := snapshot.pc
    regions := snapshot.regions
    stopped := snapshot.stopped
    threads := snapshot.threads
    currentThread := snapshot.currentThread
    nextThread := snapshot.nextThread
    pending := snapshot.pending
    skip := snapshot.skip }

/-- Restoring a snapshot gives back the exact emulator, threads, pending branch and skip marker included,
whatever ran in between. The trace, which is an observation and no part of it, stays. -/
theorem restore_capture (core later : Core) (processMemory : List (Nat × List Region)) :
    restoreCore (capture core processMemory) later = { core with trace := later.trace } := rfl

/-- An emulator with its hooks, whatever they are. -/
structure WithHooks (β : Type) where
  core : Core
  hooks : List β

def WithHooks.restore {β : Type} (snapshot : Snapshot) (emu : WithHooks β) : WithHooks β :=
  { emu with core := restoreCore snapshot emu.core }

/-- Hooks are closures and are not saved, so that a restore keeps those in place. -/
theorem restore_keeps_hooks {β : Type} (snapshot : Snapshot) (emu : WithHooks β) :
    (emu.restore snapshot).hooks = emu.hooks := rfl

/-- A snapshot at a breakpoint causes no re-fire: its skip marker comes back, and the next step does not
fire the hooks again. -/
theorem restore_does_not_refire (w : World) (core later : Core) (log : List Event)
    (hskip : core.skip = some core.pc) (hstopped : core.stopped = false) :
    step w { core := restoreCore (capture core) later, log } =
      afterHooks w core.pc ({ core := restoreCore (capture core) later, log : Machine }.withSkip none) :=
  step_skipped w _ hstopped hskip

/-! ### Instructions as BIL -/

/-- A program as blocks of BIL, which an emulator runs through `Bil.run`, which native code must agree with
(see `Bap.Jit`). -/
def bilBlock (code : Nat → Option (Nat × Bil.Program)) (address : Nat) : CoreM (Nat × Bil.Effect) := fun c =>
  match code address with
  | none => .error "unmapped" c
  | some (next, program) =>
    match Bil.run program c.state with
    | .ok (state, effect) => .ok (next, effect) { c with state }
    | .error error => .error error c

/-- A world of BIL blocks. -/
def bilWorld (hook : Nat → CoreM Unit) (delay : Nat → CoreM DelayKind) (dispatch : String → CoreM Bool)
    (code : Nat → Option (Nat × Bil.Program)) : World :=
  ⟨hook, delay, bilBlock code, dispatch⟩

/-- A step agrees with `Bil.run` on the BIL of the instruction: the state after it is the state after the
BIL, the pc is what `commit` makes of the effect, and nothing else changes. -/
theorem step_agrees_with_bil {hook : Nat → CoreM Unit} {delay : Nat → CoreM DelayKind} {dispatch : String → CoreM Bool}
    {code : Nat → Option (Nat × Bil.Program)} (m : Machine) {next : Nat} {program : Bil.Program}
    {state : Bil.State} {effect : Bil.Effect} {kind : DelayKind} {handled : Bool} {c₃ : Core}
    (hstopped : m.core.stopped = false) (hskip : m.core.skip = some m.core.pc)
    (hcode : code m.core.pc = some (next, program))
    (hrun : Bil.run program m.core.state = .ok (state, effect))
    (hdelay : delayOf ⟨hook, delay, bilBlock code, dispatch⟩ m.core.pending m.core.pc { m.core with skip := none } =
      .ok kind { m.core with skip := none })
    (hdispatch : dispatchOf ⟨hook, delay, bilBlock code, dispatch⟩ effect
      { m.core with skip := none, state, trace := m.core.trace ++ [m.core.pc] } = .ok handled c₃) :
    step (bilWorld hook delay dispatch code) m =
      .ok (!(commit m.core.pc next effect handled c₃.pc kind m.core.pending).stop)
        { core := finish m.core.pc c₃ (commit m.core.pc next effect handled c₃.pc kind m.core.pending)
          log := m.log ++ [.execute m.core.pc] } := by
  rw [step_skipped _ m hstopped hskip, afterHooks_proceed _ m.core.pc (m.withSkip none) hstopped rfl, stepExecute_eq]
  simp only [body, bilWorld, Machine.withSkip]
  rw [hdelay]
  simp only [bilBlock, hcode, hrun]
  rw [hdispatch]

/-- A failing block rolls back: its BIL has no effect on the machine at all. -/
theorem step_bil_error {hook : Nat → CoreM Unit} {delay : Nat → CoreM DelayKind} {dispatch : String → CoreM Bool}
    {code : Nat → Option (Nat × Bil.Program)} (m : Machine) {next : Nat} {program : Bil.Program}
    {error : String} {kind : DelayKind}
    (hstopped : m.core.stopped = false) (hskip : m.core.skip = some m.core.pc)
    (hcode : code m.core.pc = some (next, program))
    (hrun : Bil.run program m.core.state = .error error)
    (hdelay : delayOf ⟨hook, delay, bilBlock code, dispatch⟩ m.core.pending m.core.pc { m.core with skip := none } =
      .ok kind { m.core with skip := none }) :
    step (bilWorld hook delay dispatch code) m =
      .error error { core := rollback m.core.pc { m.core with skip := none }, log := m.log ++ [.execute m.core.pc] } := by
  rw [step_skipped _ m hstopped hskip, afterHooks_proceed _ m.core.pc (m.withSkip none) hstopped rfl, stepExecute_eq]
  simp only [body, bilWorld, Machine.withSkip]
  rw [hdelay]
  simp only [bilBlock, hcode, hrun]

/-- The whole delayed-branch protocol, for BIL: the branch runs, the slot runs, and the pc is the target. -/
theorem delayed_branch_reaches_target {width : Nat} (address next : Nat) (target : BitVec width) (slotNext : Nat) :
    let branch := advance address next (.jump target) false .delayed none
    let slot := advance branch.pc slotNext .normal false .none branch.pending
    branch.pc = address + 4 ∧ slot.pc = target.toNat ∧ slot.pending = none := by
  simp [advance, delaySlotSize]

/-! ### Registers change only as the BIL says -/

mutual
  /-- The variables that a statement may assign. -/
  def stmtWrites : Bil.Stmt → List Bap.Var
    | .move var _ => [var]
    | .jmp _ | .special _ | .cpuExn _ => []
    | .ifElse _ yes no => programWrites yes ++ programWrites no
    | .while _ body => programWrites body

  def programWrites : Bil.Program → List Bap.Var
    | [] => []
    | stmt :: rest => stmtWrites stmt ++ programWrites rest
end

private theorem exec_frame (fuel : Nat) :
    (∀ state stmt result, Bil.execStmt fuel state stmt = .ok result →
      ∀ var, var ∉ stmtWrites stmt → Bil.lookup result.1.env var = Bil.lookup state.env var) ∧
    (∀ state program result, Bil.execProgram fuel state program = .ok result →
      ∀ var, var ∉ programWrites program → Bil.lookup result.1.env var = Bil.lookup state.env var) := by
  induction fuel with
  | zero =>
    constructor
    · intro state stmt result h
      simp [Bil.execStmt] at h
    · intro state program result h
      simp [Bil.execProgram] at h
  | succ fuel ih =>
    obtain ⟨ihs, ihp⟩ := ih
    constructor
    · intro state stmt result h var hvar
      cases stmt with
      | move target value =>
        simp only [Bil.execStmt, bind, Except.bind] at h
        cases hv : Bil.execExp state value with
        | error e => simp [hv] at h
        | ok v =>
          simp only [hv, Except.ok.injEq] at h
          subst h
          simp only [stmtWrites, List.mem_singleton] at hvar
          exact Proofs.Bil.lookup_bind_other _ _ hvar
      | jmp target =>
        simp only [Bil.execStmt, bind, Except.bind] at h
        cases hv : Bil.execExp state target with
        | error e => simp [hv] at h
        | ok v =>
          cases v <;> simp [hv, Value.asBits] at h
          rw [← h]
      | special message =>
        simp only [Bil.execStmt, Except.ok.injEq] at h
        rw [← h]
      | cpuExn number =>
        simp only [Bil.execStmt, Except.ok.injEq] at h
        rw [← h]
      | ifElse condition yes no =>
        simp only [Bil.execStmt, bind, Except.bind] at h
        cases hv : Bil.execExp state condition with
        | error e => simp [hv] at h
        | ok v =>
          cases v with
          | memory m => simp [hv, Value.asBits] at h
          | undefined => simp [hv, Value.asBits] at h
          | @bits w b =>
            simp only [hv, Value.asBits] at h
            by_cases hw : w = 1
            · subst hw
              simp only [↓reduceDIte] at h
              simp only [stmtWrites, List.mem_append, not_or] at hvar
              split at h
              · exact ihp _ _ _ h var hvar.1
              · exact ihp _ _ _ h var hvar.2
            · simp [hw] at h
      | «while» condition body =>
        simp only [Bil.execStmt, bind, Except.bind] at h
        cases hv : Bil.execExp state condition with
        | error e => simp [hv] at h
        | ok v =>
          cases v with
          | memory m => simp [hv, Value.asBits] at h
          | undefined => simp [hv, Value.asBits] at h
          | @bits w b =>
            simp only [hv, Value.asBits] at h
            by_cases hw : w = 1
            · subst hw
              simp only [↓reduceDIte] at h
              have hbody : var ∉ programWrites body := by simpa only [stmtWrites] using hvar
              split at h
              · cases hp : Bil.execProgram fuel state body with
                | error e => simp [hp] at h
                | ok r =>
                  obtain ⟨next, effect⟩ := r
                  have h1 := ihp _ _ _ hp var hbody
                  simp only [hp] at h
                  cases effect with
                  | normal => rw [ihs _ _ _ h var hvar]; exact h1
                  | jump target =>
                    simp only [Except.ok.injEq] at h
                    rw [← h]
                    exact h1
                  | special message =>
                    simp only [Except.ok.injEq] at h
                    rw [← h]
                    exact h1
                  | cpuExn number =>
                    simp only [Except.ok.injEq] at h
                    rw [← h]
                    exact h1
              · simp only [Except.ok.injEq] at h
                rw [← h]
            · simp [hw] at h
    · intro state program result h var hvar
      cases program with
      | nil =>
        simp only [Bil.execProgram, Except.ok.injEq] at h
        rw [← h]
      | cons stmt rest =>
        simp only [programWrites, List.mem_append, not_or] at hvar
        simp only [Bil.execProgram, bind, Except.bind] at h
        cases hp : Bil.execStmt fuel state stmt with
        | error e => simp [hp] at h
        | ok r =>
          obtain ⟨next, effect⟩ := r
          have h1 := ihs _ _ _ hp var hvar.1
          simp only [hp] at h
          cases effect with
          | normal => rw [ihp _ _ _ h var hvar.2]; exact h1
          | jump target =>
            simp only [Except.ok.injEq] at h
            rw [← h]
            exact h1
          | special message =>
            simp only [Except.ok.injEq] at h
            rw [← h]
            exact h1
          | cpuExn number =>
            simp only [Except.ok.injEq] at h
            rw [← h]
            exact h1

/-- Register frame: a variable that the BIL does not assign keeps its value. -/
theorem run_frame {program : Bil.Program} {state : Bil.State} {result : Bil.State × Bil.Effect}
    (h : Bil.run program state = .ok result) (var : Bap.Var) (hvar : var ∉ programWrites program) :
    Bil.lookup result.1.env var = Bil.lookup state.env var :=
  (exec_frame 100000).2 state program result h var hvar

/-- Memory frame: a store leaves every byte outside the stored range as it was. -/
theorem store_frame {w valueWidth : Nat} {memory updated : Memory w} (hm : Proofs.Core.MemoryLaws.PagesSized memory)
    {address other : BitVec w} {value : BitVec valueWidth} {endian : Endian} {size : Nat}
    (hw : Memory.write memory address value endian size = .ok updated)
    (hne : ∀ k, k < size → other ≠ address + BitVec.ofNat w k) :
    Memory.readByte updated other = Memory.readByte memory other :=
  Proofs.Core.MemoryLaws.readByte_write_frame hm hw hne

/-! ### Permissions -/

/-- An access has no fault in the search exactly when every byte lies in a region that allows it. -/
theorem accessFaultSlow_none_iff (regions : List Region) (write : Bool) (address size : Nat) :
    accessFaultSlow regions write address size = none ↔
      ∀ offset, offset < size → ∃ region, lookupRegion regions (address + offset) = some region ∧
        (if write then region.protection.writable else region.protection.readable) = true := by
  simp only [accessFaultSlow, List.find?_eq_none, List.mem_range]
  constructor
  · intro h offset ho
    have := h offset ho
    cases hl : lookupRegion regions (address + offset) with
    | none => simp [hl] at this
    | some region =>
      refine ⟨region, rfl, ?_⟩
      simp only [hl] at this
      cases write <;> simp_all
  · intro h offset ho
    obtain ⟨region, hl, hp⟩ := h offset ho
    simp only [hl]
    cases write <;> simp_all

/-- The search reports the first forbidden byte. -/
theorem accessFaultSlow_some {regions : List Region} {write : Bool} {address size offset : Nat}
    (h : accessFaultSlow regions write address size = some offset) :
    offset < size ∧ (match lookupRegion regions (address + offset) with
      | none => true
      | some region => if write then !region.protection.writable else !region.protection.readable) = true := by
  simp only [accessFaultSlow, List.find?_eq_some_iff_append] at h
  obtain ⟨hp, as, bs, heq, _⟩ := h
  have hm : offset ∈ List.range size := by rw [heq]; simp
  exact ⟨List.mem_range.1 hm, hp⟩

/-- Regions that share no byte. `create`, `map` and `overlay` refuse anything else. -/
def Disjoint (regions : List Region) : Prop :=
  ∀ left ∈ regions, ∀ right ∈ regions, ∀ address, left.contains address = true → right.contains address = true →
    left = right

private theorem lookup_of_contains {regions : List Region} (hd : Disjoint regions) {region : Region}
    (hm : region ∈ regions) {address : Nat} (hc : region.contains address = true) :
    lookupRegion regions address = some region := by
  cases hl : lookupRegion regions address with
  | none =>
    simp only [lookupRegion, List.find?_eq_none] at hl
    exact absurd hc (by simpa using hl region hm)
  | some other =>
    have ho := List.find?_some hl
    have hmo := List.mem_of_find?_eq_some hl
    rw [hd other hmo region hm address ho hc]

/-- The fast path changes nothing, in regions that do not overlap. -/
theorem accessFault_eq_slow {regions : List Region} (hd : Disjoint regions) (write : Bool) (address size : Nat) :
    accessFault regions write address size = accessFaultSlow regions write address size := by
  simp only [accessFault]
  cases hl : lookupRegion regions address with
  | none => rfl
  | some region =>
    simp only
    split
    · rename_i hallowed
      symm
      rw [accessFaultSlow_none_iff]
      intro offset ho
      simp only [accessAllowed, Bool.and_eq_true] at hallowed
      obtain ⟨⟨hc, hend⟩, hp⟩ := hallowed
      have hm : region ∈ regions := List.mem_of_find?_eq_some hl
      refine ⟨region, lookup_of_contains hd hm ?_, hp⟩
      simp only [Region.contains, Bool.and_eq_true, decide_eq_true_eq] at hc ⊢
      have := of_decide_eq_true hend
      omega
    · rfl

/-- Permissions are enforced: an access passes exactly when every byte is mapped and allows it. -/
theorem accessFault_none_iff {regions : List Region} (hd : Disjoint regions) (write : Bool) (address size : Nat) :
    accessFault regions write address size = none ↔
      ∀ offset, offset < size → ∃ region, lookupRegion regions (address + offset) = some region ∧
        (if write then region.protection.writable else region.protection.readable) = true := by
  rw [accessFault_eq_slow hd, accessFaultSlow_none_iff]

/-- A forbidden access does nothing but fault: no hook fires, nothing is recorded, nothing is written. -/
theorem notifyAccess_fault {m : Type → Type} [Monad m] (regions : List Region) (write : Bool) (address size : Nat)
    (fault : Nat → m Unit) (dirty record hooks : m Unit) {offset : Nat}
    (h : accessFault regions write address size = some offset) :
    notifyAccess regions write address size fault dirty record hooks = fault offset := by
  simp only [notifyAccess, h]

/-- An allowed access marks code as dirty if it writes some, records, and then fires its hooks. -/
theorem notifyAccess_allowed {m : Type → Type} [Monad m] (regions : List Region) (write : Bool) (address size : Nat)
    (fault : Nat → m Unit) (dirty record hooks : m Unit)
    (h : accessFault regions write address size = none) :
    notifyAccess regions write address size fault dirty record hooks = (do
      if write && size > 0 && writesCode regions address size then dirty
      record
      hooks) := by
  simp only [notifyAccess, h]

/-- `writesCode` finds every write that touches executable memory. -/
theorem writesCode_iff (regions : List Region) (address size : Nat) :
    writesCode regions address size = true ↔
      ∃ region ∈ regions, region.protection.executable = true ∧ region.address < address + size ∧
        address < region.address + region.data.size := by
  simp only [writesCode, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨region, hm, ⟨hx, h1⟩, h2⟩
    exact ⟨region, hm, hx, h1, h2⟩
  · rintro ⟨region, hm, hx, h1, h2⟩
    exact ⟨region, hm, ⟨hx, h1⟩, h2⟩

/-! ### Round robin -/

/-- `id` is the id of a thread that can run, with `p`. -/
def Runnable (threads : List ThreadContext) (p : Nat → Bool) (id : Nat) : Prop :=
  ∃ context ∈ threads, context.stopped = false ∧ p context.id = true ∧ context.id = id

private theorem lowerId_le_left {best : Nat} {id r : Nat} (h : lowerId (some best) id = some r) :
    r ≤ best ∧ r ≤ id ∧ (r = best ∨ r = id) := by
  simp only [lowerId] at h
  split at h <;> simp only [Option.some.injEq] at h <;> omega

private theorem minRunnable_foldl (threads : List ThreadContext) (p : Nat → Bool) (best : Option Nat) :
    let result := threads.foldl (init := best) fun best context =>
      if !context.stopped && p context.id then lowerId best context.id else best
    (result = none ↔ best = none ∧ ∀ id, ¬ Runnable threads p id) ∧
      ∀ r, result = some r → (best = some r ∨ Runnable threads p r) ∧ (∀ b, best = some b → r ≤ b) ∧
        ∀ id, Runnable threads p id → r ≤ id := by
  induction threads generalizing best with
  | nil =>
    simp only [List.foldl_nil, Runnable, List.not_mem_nil, false_and, exists_false, not_false_eq_true, implies_true,
      and_true, or_false, true_and]
    refine fun r h => ⟨h, fun b hb => ?_, fun _ h => h.elim⟩
    rw [h] at hb
    simp only [Option.some.injEq] at hb
    omega
  | cons context rest ih =>
    simp only [List.foldl_cons]
    have hrun : ∀ id, Runnable (context :: rest) p id ↔
        ((context.stopped = false ∧ p context.id = true ∧ context.id = id) ∨ Runnable rest p id) := by
      intro id
      simp [Runnable]
    by_cases hc : (!context.stopped && p context.id) = true
    · have hs : context.stopped = false ∧ p context.id = true := by simpa using hc
      simp only [hc, ite_true]
      have ih' := ih (lowerId best context.id)
      simp only at ih'
      constructor
      · rw [ih'.1]
        constructor
        · rintro ⟨h, _⟩
          cases best with
          | none => simp [lowerId] at h
          | some other =>
            simp only [lowerId] at h
            split at h <;> simp at h
        · rintro ⟨_, h⟩
          exact absurd ((hrun _).2 (Or.inl ⟨hs.1, hs.2, rfl⟩)) (h _)
      · intro r hr
        obtain ⟨h1, h2, h3⟩ := ih'.2 r hr
        cases best with
        | none =>
          have h20 := h2 context.id rfl
          refine ⟨?_, by simp, ?_⟩
          · rcases h1 with h1 | h1
            · simp only [lowerId, Option.some.injEq] at h1
              exact Or.inr ((hrun _).2 (Or.inl ⟨hs.1, hs.2, h1⟩))
            · exact Or.inr ((hrun _).2 (Or.inr h1))
          · intro id hi
            rcases (hrun _).1 hi with ⟨_, _, he⟩ | hi
            · rw [← he]
              exact h20
            · exact h3 id hi
        | some other =>
          have hlow : ∃ l, lowerId (some other) context.id = some l :=
            ⟨if other ≤ context.id then other else context.id, by simp only [lowerId]; split <;> rfl⟩
          obtain ⟨l, hl⟩ := hlow
          obtain ⟨l1, l2, l3⟩ := lowerId_le_left hl
          have h20 := h2 l hl
          refine ⟨?_, ?_, ?_⟩
          · rcases h1 with h1 | h1
            · rw [hl] at h1
              simp only [Option.some.injEq] at h1
              subst h1
              rcases l3 with l3 | l3
              · exact Or.inl (by rw [l3])
              · exact Or.inr ((hrun _).2 (Or.inl ⟨hs.1, hs.2, l3.symm⟩))
            · exact Or.inr ((hrun _).2 (Or.inr h1))
          · intro b hb
            simp only [Option.some.injEq] at hb
            omega
          · intro id hi
            rcases (hrun _).1 hi with ⟨_, _, he⟩ | hi
            · omega
            · exact h3 id hi
    · have hc' : (!context.stopped && p context.id) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ite_false]
      have hnot : ∀ id, Runnable (context :: rest) p id ↔ Runnable rest p id := by
        intro id
        rw [hrun]
        constructor
        · rintro (⟨h1, h2, _⟩ | h)
          · simp [h1, h2] at hc
          · exact h
        · exact Or.inr
      simp only [hnot]
      exact ih best

/-- What `minRunnable` finds: nothing exactly when no thread can run. -/
theorem minRunnable_none_iff (threads : List ThreadContext) (p : Nat → Bool) :
    minRunnable threads p = none ↔ ∀ id, ¬ Runnable threads p id := by
  have := (minRunnable_foldl threads p none).1
  simpa [minRunnable] using this

/-- And otherwise the smallest id of a thread that can run. -/
theorem minRunnable_some {threads : List ThreadContext} {p : Nat → Bool} {r : Nat}
    (h : minRunnable threads p = some r) : Runnable threads p r ∧ ∀ id, Runnable threads p id → r ≤ id := by
  have := (minRunnable_foldl threads p none).2 r h
  simp only [reduceCtorEq, false_or] at this
  exact ⟨this.1, this.2.2⟩

/-- A stopped thread is never picked, nor the current one: only another thread that can run. -/
theorem pickNext_runnable {threads : List ThreadContext} {current id : Nat}
    (h : pickNext threads current = some id) :
    id ≠ current ∧ ∃ context ∈ threads, context.id = id ∧ context.stopped = false := by
  simp only [pickNext] at h
  cases ha : minRunnable threads (fun id => decide (current < id)) with
  | some r =>
    simp only [ha, Option.some.injEq] at h
    subst h
    obtain ⟨⟨context, hm, hs, hp, he⟩, _⟩ := minRunnable_some ha
    have : current < context.id := by simpa using hp
    exact ⟨by omega, context, hm, he, hs⟩
  | none =>
    simp only [ha] at h
    obtain ⟨⟨context, hm, hs, hp, he⟩, _⟩ := minRunnable_some h
    have : context.id ≠ current := by simpa using hp
    exact ⟨by rw [← he]; exact this, context, hm, he, hs⟩

/-- There is nothing to pick only when no other thread can run. -/
theorem pickNext_none_iff (threads : List ThreadContext) (current : Nat) :
    pickNext threads current = none ↔
      ∀ context ∈ threads, context.id ≠ current → context.stopped = true := by
  simp only [pickNext]
  cases ha : minRunnable threads (fun id => decide (current < id)) with
  | some r =>
    simp only [reduceCtorEq, false_iff]
    obtain ⟨⟨context, hm, hs, hp, he⟩, _⟩ := minRunnable_some ha
    intro hall
    have : current < context.id := by simpa using hp
    have := hall context hm (by omega)
    simp_all
  | none =>
    simp only
    rw [minRunnable_none_iff]
    constructor
    · intro h context hm hne
      cases hs : context.stopped with
      | true => rfl
      | false => exact absurd ⟨context, hm, hs, by simpa using hne, rfl⟩ (h context.id)
    · rintro h id ⟨context, hm, hs, hp, he⟩
      have := h context hm (by simpa using hp)
      simp_all

/-- `roster` lists the threads that can run, in id order. -/
structure Roster (threads : List ThreadContext) (roster : List Nat) : Prop where
  sorted : roster.Pairwise (· < ·)
  mem : ∀ id, id ∈ roster ↔ ∃ context ∈ threads, context.id = id ∧ context.stopped = false

private theorem roster_lt {roster : List Nat} (h : roster.Pairwise (· < ·)) {i j : Nat}
    (hij : i < j) (hj : j < roster.length) : roster[i]'(by omega) < roster[j] :=
  List.pairwise_iff_getElem.1 h i j (by omega) hj hij

private theorem roster_le {roster : List Nat} (h : roster.Pairwise (· < ·)) {i j : Nat}
    (hij : i ≤ j) (hj : j < roster.length) : roster[i]'(by omega) ≤ roster[j] := by
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · exact Nat.le_of_lt (roster_lt h hlt hj)
  · exact Nat.le_refl _

/-- Round robin picks the next thread of the roster, wrapping around. -/
theorem pickNext_cycle {threads : List ThreadContext} {roster : List Nat} (hr : Roster threads roster)
    {i : Nat} (hi : i < roster.length) (hn : 2 ≤ roster.length) :
    pickNext threads roster[i] =
      some (roster[(i + 1) % roster.length]'(Nat.mod_lt _ (by omega))) := by
  have hrun : ∀ (p : Nat → Bool) (k : Nat) (hk : k < roster.length), p roster[k] = true →
      Runnable threads p roster[k] := by
    intro p k hk hp
    obtain ⟨context, hm, he, hs⟩ := (hr.mem _).1 (List.getElem_mem hk)
    exact ⟨context, hm, hs, by rw [he]; exact hp, he⟩
  have hindex : ∀ (p : Nat → Bool) (id : Nat), Runnable threads p id →
      ∃ k, ∃ hk : k < roster.length, roster[k] = id := by
    rintro p id ⟨context, hm, hs, _, he⟩
    have := (hr.mem id).2 ⟨context, hm, he, hs⟩
    obtain ⟨k, hk, hke⟩ := List.getElem_of_mem this
    exact ⟨k, hk, hke⟩
  simp only [pickNext]
  by_cases hlast : i + 1 < roster.length
  · simp only [Nat.mod_eq_of_lt hlast]
    have hgt := roster_lt hr.sorted (Nat.lt_succ_self i) hlast
    cases ha : minRunnable threads (fun id => decide (roster[i] < id)) with
    | none =>
      exact absurd (hrun _ (i + 1) hlast (by simpa using hgt)) ((minRunnable_none_iff _ _).1 ha _)
    | some r =>
      obtain ⟨h1, h2⟩ := minRunnable_some ha
      have hle := h2 _ (hrun _ (i + 1) hlast (by simpa using hgt))
      obtain ⟨k, hk, hke⟩ := hindex _ _ h1
      have hpr : roster[i] < r := by
        obtain ⟨context, _, _, hp, he⟩ := h1
        rw [← he]
        simpa using hp
      have hik : i < k := by
        refine Decidable.byContradiction fun hnot => ?_
        have := roster_le hr.sorted (Nat.le_of_not_lt hnot) hi
        rw [hke] at this
        omega
      have := roster_le hr.sorted (show i + 1 ≤ k by omega) hk
      rw [hke] at this
      simp only [Option.some.injEq]
      omega
  · have hl : i + 1 = roster.length := by omega
    simp only [hl, Nat.mod_self]
    have hnone : minRunnable threads (fun id => decide (roster[i] < id)) = none := by
      rw [minRunnable_none_iff]
      intro id hid
      obtain ⟨k, hk, hke⟩ := hindex _ _ hid
      have hle := roster_le hr.sorted (show k ≤ i by omega) hi
      obtain ⟨context, _, _, hp, he⟩ := hid
      have : roster[i] < context.id := by simpa using hp
      rw [he, ← hke] at this
      omega
    rw [hnone]
    simp only
    have h0 : 0 < roster.length := by omega
    have hne : roster[0] ≠ roster[i] := by
      have := roster_lt hr.sorted (show 0 < i by omega) hi
      omega
    cases ha : minRunnable threads (fun id => id != roster[i]) with
    | none =>
      exact absurd (hrun _ 0 h0 (by simpa using hne)) ((minRunnable_none_iff _ _).1 ha _)
    | some r =>
      obtain ⟨h1, h2⟩ := minRunnable_some ha
      have hle := h2 _ (hrun _ 0 h0 (by simpa using hne))
      obtain ⟨k, hk, hke⟩ := hindex _ _ h1
      have := roster_le hr.sorted (Nat.zero_le k) hk
      rw [hke] at this
      simp only [Option.some.injEq]
      omega

/-- `k` turns of round robin. -/
def turns (threads : List ThreadContext) : Nat → Nat → Option Nat
  | 0, current => some current
  | k + 1, current => (turns threads k current).bind (pickNext threads)

/-- After `k` turns, thread `i + k` of the roster runs, modulo its length. -/
theorem turns_cycle {threads : List ThreadContext} {roster : List Nat} (hr : Roster threads roster)
    {i : Nat} (hi : i < roster.length) (hn : 2 ≤ roster.length) (k : Nat) :
    turns threads k roster[i] = some (roster[(i + k) % roster.length]'(Nat.mod_lt _ (by omega))) := by
  induction k with
  | zero =>
    simp only [turns, Nat.add_zero, Nat.mod_eq_of_lt hi]
  | succ k ih =>
    simp only [turns, ih, Option.bind_some]
    rw [pickNext_cycle hr (Nat.mod_lt _ (by omega)) hn]
    congr 2
    rw [← Nat.add_assoc, Nat.mod_add_mod]

/-- Fairness of round robin: in any `n` consecutive turns among `n` threads that can run, each of them
gets exactly one. -/
theorem round_robin_fair {threads : List ThreadContext} {roster : List Nat} (hr : Roster threads roster)
    {i j : Nat} (hi : i < roster.length) (hj : j < roster.length) (hn : 2 ≤ roster.length) :
    ∃ k, k < roster.length ∧ turns threads (k + 1) roster[i] = some roster[j] ∧
      ∀ k', k' < roster.length → turns threads (k' + 1) roster[i] = some roster[j] → k' = k := by
  have hpos : 0 < roster.length := by omega
  have hnodup : ∀ (a b : Nat) (ha : a < roster.length) (hb : b < roster.length), roster[a] = roster[b] → a = b := by
    intro a b ha hb h
    rcases Nat.lt_trichotomy a b with hlt | he | hgt
    · have := roster_lt hr.sorted hlt hb
      omega
    · exact he
    · have := roster_lt hr.sorted hgt ha
      omega
  have hk0 : (j + roster.length + roster.length - i - 1) % roster.length < roster.length := Nat.mod_lt _ hpos
  have hmod : ∀ k, (i + (k + 1)) % roster.length =
      (i + 1 + k % roster.length) % roster.length := by
    intro k
    rw [show i + (k + 1) = i + 1 + k by omega, Nat.add_mod (i + 1) k, Nat.add_mod (i + 1) (k % _),
      Nat.mod_mod]
  have hexact : (i + ((j + roster.length + roster.length - i - 1) % roster.length + 1)) % roster.length = j := by
    have h1 := hmod (j + roster.length + roster.length - i - 1)
    rw [show i + (j + roster.length + roster.length - i - 1 + 1) = j + roster.length * 2 by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj] at h1
    rw [show i + ((j + roster.length + roster.length - i - 1) % roster.length + 1) =
      i + 1 + (j + roster.length + roster.length - i - 1) % roster.length by omega]
    exact h1.symm
  refine ⟨(j + roster.length + roster.length - i - 1) % roster.length, hk0, ?_, ?_⟩
  · rw [turns_cycle hr hi hn]
    simp only [hexact]
  · intro k' hk' h
    rw [turns_cycle hr hi hn] at h
    simp only [Option.some.injEq] at h
    have hm' := hnodup _ _ (Nat.mod_lt _ hpos) hj h
    generalize (j + roster.length + roster.length - i - 1) % roster.length = k at hexact hk0 ⊢
    have heq : (i + (k' + 1)) % roster.length = (i + (k + 1)) % roster.length := by rw [hm', hexact]
    rcases Nat.lt_trichotomy k' k with hlt | he | hgt
    · have hd := Nat.sub_mod_eq_zero_of_mod_eq heq.symm
      rw [show i + (k + 1) - (i + (k' + 1)) = k - k' by omega, Nat.mod_eq_of_lt (by omega)] at hd
      omega
    · exact he
    · have hd := Nat.sub_mod_eq_zero_of_mod_eq heq
      rw [show i + (k' + 1) - (i + (k + 1)) = k' - k by omega, Nat.mod_eq_of_lt (by omega)] at hd
      omega

/-! ### Preemption -/

/-- The scheduler's view: `n` threads in a roster, one of which runs. -/
structure Sched where
  current : Nat
  stopped : Bool := false
  /-- Who ran, and how many steps, latest first. -/
  turns : List (Nat × Nat) := []

abbrev SchedM := StateM Sched

/-- A turn: the thread runs for `limit` steps, or hits a stop, in thread `halts`, after no steps. -/
def schedRun (halts : Nat → Bool) (limit : Nat) : SchedM Nat := fun s =>
  if halts s.current then (0, { s with stopped := true, turns := (s.current, 0) :: s.turns })
  else (limit, { s with turns := (s.current, limit) :: s.turns })

def schedStopped : SchedM Bool := fun s => (s.stopped, s)

/-- The next thread of the roster, which is what `pickNext_cycle` says `switchNextThread` picks. -/
def schedSwitch (n : Nat) : SchedM Bool := fun s => (true, { s with current := (s.current + 1) % n })

/-- `preemptiveM`, which is `runPreemptive`, on the scheduler's view. -/
def schedule (halts : Nat → Bool) (n quantum fuel : Nat) (rounds remaining total : Nat) : SchedM Nat :=
  preemptiveM (schedRun halts) schedStopped (schedSwitch n) quantum fuel rounds remaining total

/-- All-stop: when the thread that runs stops, no other thread runs, and it stays current, even if others
could run. This is what a breakpoint needs: the caller finds the thread that hit it. -/
theorem preemptive_all_stop (halts : Nat → Bool) (n quantum fuel rounds remaining total : Nat) (s : Sched)
    (hr : 0 < remaining) (hstop : halts s.current = true) (hf : total ≠ fuel) :
    schedule halts n quantum fuel (rounds + 1) remaining total s =
      (total, { s with stopped := true, turns := (s.current, 0) :: s.turns }) := by
  have hr' : remaining ≠ 0 := by omega
  simp [schedule, preemptiveM, hr', bind, StateT.bind, schedRun, hstop, hf, schedStopped, pure, StateT.pure]

/-- The turns without stops, in order: each thread of the roster runs a quantum, then the next one. -/
def expectedTurns (n quantum : Nat) : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => []
  | rounds + 1, remaining, current =>
    if remaining = 0 then []
    else (current, min quantum remaining) ::
      expectedTurns n quantum rounds (remaining - min quantum remaining) ((current + 1) % n)

private theorem expectedTurns_zero (n quantum rounds current : Nat) : expectedTurns n quantum rounds 0 current = [] := by
  cases rounds <;> simp [expectedTurns]

/-- Without stops, `runPreemptive` runs exactly the expected turns, and takes the whole fuel. -/
theorem schedule_turns (halts : Nat → Bool) (n quantum fuel : Nat) (hq : 0 < quantum) (rounds remaining total : Nat)
    (s : Sched) (hall : ∀ id, halts id = false) (hstopped : s.stopped = false) (hf : total + remaining = fuel)
    (hrounds : remaining ≤ rounds) :
    let result := schedule halts n quantum fuel rounds remaining total s
    result.1 = fuel ∧ result.2.stopped = false ∧
      result.2.turns = (expectedTurns n quantum rounds remaining s.current).reverse ++ s.turns := by
  induction rounds generalizing remaining total s with
  | zero =>
    have : remaining = 0 := by omega
    subst this
    refine ⟨by simpa [schedule, preemptiveM, pure, StateT.pure] using hf, hstopped, ?_⟩
    rfl
  | succ rounds ih =>
    by_cases hr : remaining = 0
    · subst hr
      refine ⟨?_, hstopped, ?_⟩
      · simpa [schedule, preemptiveM, pure, StateT.pure] using hf
      · simp [schedule, preemptiveM, expectedTurns, pure, StateT.pure]
    · have hrun : schedRun halts (min quantum remaining) s =
          (min quantum remaining, { s with turns := (s.current, min quantum remaining) :: s.turns }) := by
        simp [schedRun, hall]
      have hlimit : 0 < min quantum remaining := by omega
      by_cases hdone : total + min quantum remaining = fuel
      · have hrem : remaining - min quantum remaining = 0 := by omega
        have hunfold : schedule halts n quantum fuel (rounds + 1) remaining total s =
            (fuel, { s with turns := (s.current, min quantum remaining) :: s.turns }) := by
          simp [schedule, preemptiveM, hr, bind, StateT.bind, hrun, hdone, pure, StateT.pure]
        simp only [hunfold]
        refine ⟨trivial, hstopped, ?_⟩
        simp [expectedTurns, hr, hrem, expectedTurns_zero]
      · have hunfold : schedule halts n quantum fuel (rounds + 1) remaining total s =
            schedule halts n quantum fuel rounds (remaining - min quantum remaining) (total + min quantum remaining)
              { s with current := (s.current + 1) % n, turns := (s.current, min quantum remaining) :: s.turns } := by
          simp [schedule, preemptiveM, hr, bind, StateT.bind, hrun, hdone, schedStopped, hstopped, schedSwitch,
            pure]
        simp only [hunfold]
        have := ih (remaining - min quantum remaining) (total + min quantum remaining)
          { s with current := (s.current + 1) % n, turns := (s.current, min quantum remaining) :: s.turns }
          hstopped (by omega) (by omega)
        refine ⟨this.1, this.2.1, ?_⟩
        rw [this.2.2]
        simp [expectedTurns, hr]

/-- As long as the fuel lasts, turn `k` is a full quantum of thread `current + k` of the roster. -/
theorem expectedTurns_getElem (n quantum : Nat) (hq : 0 < quantum) (k : Nat) :
    ∀ (rounds remaining current : Nat), current < n → k < rounds → (k + 1) * quantum ≤ remaining →
      (expectedTurns n quantum rounds remaining current)[k]? = some ((current + k) % n, quantum) := by
  induction k with
  | zero =>
    intro rounds remaining current hc hk hrem
    cases rounds with
    | zero => omega
    | succ rounds =>
      have hrem' : quantum ≤ remaining := by simpa using hrem
      have hne : remaining ≠ 0 := by omega
      have hmin : min quantum remaining = quantum := by omega
      simp [expectedTurns, hne, hmin, Nat.mod_eq_of_lt hc]
  | succ k ih =>
    intro rounds remaining current hc hk hrem
    cases rounds with
    | zero => omega
    | succ rounds =>
      have hsplit : (k + 1 + 1) * quantum = (k + 1) * quantum + quantum := by rw [Nat.add_mul]; omega
      have hpos : quantum ≤ (k + 1) * quantum := by rw [Nat.add_mul]; omega
      have hne : remaining ≠ 0 := by omega
      have hmin : min quantum remaining = quantum := by omega
      have hnext : (current + 1) % n < n := Nat.mod_lt _ (by omega)
      have := ih rounds (remaining - quantum) ((current + 1) % n) hnext (by omega) (by omega)
      simp only [expectedTurns, hne, ↓reduceIte, hmin, List.getElem?_cons_succ]
      rw [this]
      simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      rw [Nat.mod_add_mod]
      congr 1
      omega

/-- Fairness of `runPreemptive`: with fuel for a turn of each of its `n` threads, every one of them runs a
full quantum, whichever runs first. No thread starves. -/
theorem schedule_fair (halts : Nat → Bool) (n quantum fuel : Nat) (hq : 0 < quantum) (s : Sched)
    (hall : ∀ id, halts id = false) (hstopped : s.stopped = false) (hc : s.current < n) (hfuel : n * quantum ≤ fuel)
    {j : Nat} (hj : j < n) :
    (j, quantum) ∈ (schedule halts n quantum fuel (fuel + 1) fuel 0 s).2.turns := by
  have hspec := (schedule_turns halts n quantum fuel hq (fuel + 1) fuel 0 s hall hstopped (by omega) (by omega)).2.2
  rw [hspec]
  apply List.mem_append_left
  rw [List.mem_reverse]
  have hk : (j + n - s.current) % n < n := Nat.mod_lt _ (by omega)
  generalize hkk : (j + n - s.current) % n = k at hk
  have hn : (k + 1) * quantum ≤ fuel := by
    have : (k + 1) * quantum ≤ n * quantum := Nat.mul_le_mul_right _ (by omega)
    omega
  have hle : (k + 1) * quantum ≤ fuel := hn
  have hrounds : k < fuel + 1 := by
    have : (k + 1) * 1 ≤ (k + 1) * quantum := Nat.mul_le_mul_left _ hq
    omega
  have hget := expectedTurns_getElem n quantum hq k (fuel + 1) fuel s.current hc hrounds hle
  have hmod : (s.current + k) % n = j := by
    rw [← hkk, Nat.add_mod_mod, show s.current + (j + n - s.current) = j + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hj]
  rw [hmod] at hget
  exact List.mem_of_getElem? hget

/-! ### Fork and spawn -/

/-- A fork starts stopped, at its pc, with nothing pending or skipped. -/
theorem forkContext_fields (id : Nat) (state : Bil.State) (result : Bap.Var) (value : Value) (childPc : Nat) :
    (forkContext id state result value childPc).stopped = true ∧ (forkContext id state result value childPc).pc = childPc ∧
    (forkContext id state result value childPc).pending = none ∧ (forkContext id state result value childPc).skip = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- It has its parent's registers, except for the result. -/
theorem forkContext_registers (id : Nat) (state : Bil.State) (result : Bap.Var) (value : Value) (childPc : Nat)
    (var : Bap.Var) : Bil.lookup (forkContext id state result value childPc).state.env var =
      if var = result then .ok value else Bil.lookup state.env var :=
  Proofs.Bil.lookup_bind_eq _ _ _ _

/-- A spawned thread runs at once, with its argument. -/
theorem spawnContext_fields (id : Nat) (state : Bil.State) (argument : Bap.Var) (value : Value) (start : Nat) :
    (spawnContext id state argument value start).stopped = false ∧ (spawnContext id state argument value start).pc = start ∧
    (spawnContext id state argument value start).pending = none ∧ (spawnContext id state argument value start).skip = none :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem spawnContext_registers (id : Nat) (state : Bil.State) (argument : Bap.Var) (value : Value) (start : Nat)
    (var : Bap.Var) : Bil.lookup (spawnContext id state argument value start).state.env var =
      if var = argument then .ok value else Bil.lookup state.env var :=
  Proofs.Bil.lookup_bind_eq _ _ _ _

/-- `parkShared` gives the threads of the shared address space the memory, and leaves processes alone. -/
theorem parkShared_spec {β : Type} (threads : List ThreadContext) (processes : Std.HashMap Nat β) (memoryVar : Bap.Var)
    (memory : Value) (context : ThreadContext) (hm : context ∈ threads) :
    (processes.contains context.id = true → context ∈ parkShared threads processes memoryVar memory) ∧
    (processes.contains context.id = false →
      { context with state := { env := Bil.bind context.state.env memoryVar memory } } ∈
        parkShared threads processes memoryVar memory) := by
  simp only [parkShared, List.mem_map]
  exact ⟨fun h => ⟨context, hm, by simp [h]⟩, fun h => ⟨context, hm, by simp [h]⟩⟩

/-! ### Running -/

/-- `run` counts the steps that went on, and ends at the first that did not. -/
theorem runM_stops {m : Type → Type} [Monad m] (step : m Bool) (fuel total : Nat) :
    runM step (fuel + 1) total = (do if ← step then runM step fuel (total + 1) else pure total) := rfl

theorem runM_zero {m : Type → Type} [Monad m] (step : m Bool) (total : Nat) : runM step 0 total = pure total := rfl

/-- A stopped thread runs no steps, however much fuel it gets. -/
theorem run_stopped (w : World) (m : Machine) (h : m.core.stopped = true) (fuel total : Nat) :
    runM (step w) fuel total m = .ok total m := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    show EStateM.bind (step w) (fun go => if go = true then runM (step w) fuel (total + 1) else pure total) m = _
    simp only [EStateM.bind]
    rw [step_stopped w m h]
    rfl

/-! ### Runs that chain instructions -/

/-- With nothing chained, the fuel counts steps as `runM` does: at a range limit of 1, the two are one. -/
theorem runChainedM_no_chain {m : Type → Type} [Monad m] [LawfulMonad m] (step : m Bool) (rounds remaining total : Nat)
    (h : remaining ≤ rounds) :
    runChainedM step (fun _ => pure ()) (pure 0) rounds remaining total = runM step remaining total := by
  induction rounds generalizing remaining total with
  | zero =>
    have : remaining = 0 := by omega
    subst this
    simp [runChainedM, runM]
  | succ rounds ih =>
    cases remaining with
    | zero => simp [runChainedM, runM]
    | succ remaining =>
      rw [runChainedM, runM, ite_eq_right (by omega)]
      simp only [Nat.add_sub_cancel, pure_bind, Nat.zero_min, Nat.sub_zero, Nat.add_zero]
      congr 1
      funext go
      cases go with
      | true => simpa using ih remaining (total + 1) (by omega)
      | false => rfl

/-- The fuel is exact on a state monad, whatever the steps chain: the run ends with at most the instructions it was
given, and with exactly those when no step ends it. -/
theorem runChainedM_total {σ : Type} (step : StateM σ Bool) (allow : Nat → StateM σ Unit) (chained : StateM σ Nat)
    (rounds remaining total : Nat) (s : σ) (h : remaining ≤ rounds) :
    (runChainedM step allow chained rounds remaining total s).1 ≤ total + remaining ∧
      ((∀ s, (step s).1 = true) → (runChainedM step allow chained rounds remaining total s).1 = total + remaining) := by
  induction rounds generalizing remaining total s with
  | zero =>
    have : remaining = 0 := by omega
    subst this
    simp [runChainedM, pure, StateT.pure]
  | succ rounds ih =>
    cases remaining with
    | zero => simp [runChainedM, pure, StateT.pure]
    | succ remaining =>
      rw [runChainedM, ite_eq_right (by omega)]
      simp only [Nat.add_sub_cancel]
      generalize hs1 : (allow remaining s).2 = s1
      generalize hg : step s1 = g
      obtain ⟨go, s2⟩ := g
      have hgo : ∀ {α : Type} (f : Bool → StateM σ α),
          (allow remaining >>= fun _ => step >>= f) s = f go s2 := by
        intro α f
        show f (step (allow remaining s).2).1 (step (allow remaining s).2).2 = _
        rw [hs1, hg]
      rw [hgo]
      cases go with
      | false =>
        refine ⟨by show total ≤ _; omega, fun hall => ?_⟩
        have := hall s1
        rw [hg] at this
        simp at this
      | true =>
        generalize hc : chained s2 = c
        obtain ⟨extra, s3⟩ := c
        have hextra : ∀ {α : Type} (f : Nat → StateM σ α), (chained >>= f) s2 = f extra s3 := by
          intro α f
          show f (chained s2).1 (chained s2).2 = _
          rw [hc]
        simp only [↓reduceIte]
        rw [hextra]
        obtain ⟨h1, h2⟩ := ih (remaining - min extra remaining) (total + 1 + min extra remaining) s3 (by omega)
        refine ⟨by omega, fun hall => ?_⟩
        rw [h2 hall]
        omega

/-! ### Parallel rounds -/

/-- A round where all finished well commits, and nothing undoes it. -/
theorem roundM_commits {σ τ ω : Type} {save : EStateM String σ τ} {restore : τ → EStateM String σ Unit}
    {setUp : EStateM String σ ω} {runAll : ω → EStateM String σ (List (Except String Nat))}
    {report commit : ω → EStateM String σ Unit} {s s1 s2 s3 s4 : σ} {before : τ} {workers : ω}
    {results : List (Except String Nat)} {steps : Nat} (h0 : save s = .ok before s1) (h1 : setUp s1 = .ok workers s2)
    (h2 : runAll workers s2 = .ok results s3) (hj : joinWorkers results = .ok steps) (h3 : commit workers s3 = .ok () s4) :
    roundM (ε := String) save restore setUp runAll report commit s = .ok steps s4 := by
  simp [roundM, bind, EStateM.bind, h0, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch,
    h1, h2, hj, h3, pure, EStateM.pure]

/-- A round where a worker failed does not commit, reports the fault, undoes all of it after all ran, and fails. -/
theorem roundM_undoes {σ τ ω : Type} {save : EStateM String σ τ} {restore : τ → EStateM String σ Unit}
    {setUp : EStateM String σ ω} {runAll : ω → EStateM String σ (List (Except String Nat))}
    {report commit : ω → EStateM String σ Unit} {s s1 s2 s3 s4 s5 : σ} {before : τ} {workers : ω}
    {results : List (Except String Nat)} {error : String} (h0 : save s = .ok before s1) (h1 : setUp s1 = .ok workers s2)
    (h2 : runAll workers s2 = .ok results s3) (hj : joinWorkers results = .error error) (h3 : report workers s3 = .ok () s4)
    (h4 : restore before s4 = .ok () s5) :
    roundM (ε := String) save restore setUp runAll report commit s = .error error s5 := by
  simp [roundM, bind, EStateM.bind, h0, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch,
    EStateM.Backtrackable.restore, EStateM.dummyRestore, h1, h2, hj, h3, h4, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- A commit that fails undoes the round as well, as does a set-up that fails. -/
theorem roundM_commit_fails {σ τ ω : Type} {save : EStateM String σ τ} {restore : τ → EStateM String σ Unit}
    {setUp : EStateM String σ ω} {runAll : ω → EStateM String σ (List (Except String Nat))}
    {report commit : ω → EStateM String σ Unit} {s s1 s2 s3 s4 s5 : σ} {before : τ} {workers : ω}
    {results : List (Except String Nat)} {steps : Nat} {error : String} (h0 : save s = .ok before s1)
    (h1 : setUp s1 = .ok workers s2) (h2 : runAll workers s2 = .ok results s3) (hj : joinWorkers results = .ok steps)
    (h3 : commit workers s3 = .error error s4) (h4 : restore before s4 = .ok () s5) :
    roundM (ε := String) save restore setUp runAll report commit s = .error error s5 := by
  simp [roundM, bind, EStateM.bind, h0, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch,
    EStateM.Backtrackable.restore, EStateM.dummyRestore, h1, h2, hj, h3, h4, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-! ### Reading through to native memory -/

private theorem patchRange_unchanged {width : Nat} (native : Nat → UInt8) (start : Nat) (offsets : List Nat)
    (memory : Bap.Memory width) (changed : Bool) (result : Bap.Memory width)
    (h : patchRange (m := Id) (fun address => pure (native address)) start offsets (memory, changed) = (result, false)) :
    changed = false ∧ result = memory ∧ ∀ offset ∈ offsets,
      Bap.Memory.readByte memory (BitVec.ofNat width (start + offset)) = native (start + offset) := by
  induction offsets generalizing memory changed with
  | nil =>
    have h' : (memory, changed) = (result, false) := h
    simp only [Prod.mk.injEq] at h'
    exact ⟨h'.2, h'.1.symm, by simp⟩
  | cons head rest ih =>
    simp only [patchRange] at h
    by_cases he : Bap.Memory.readByte memory (BitVec.ofNat width (start + head)) == native (start + head)
    · simp only [pure, bind, he, ↓reduceIte] at h
      obtain ⟨h1, h2, h3⟩ := ih memory changed h
      refine ⟨h1, h2, ?_⟩
      intro offset ho
      rcases List.mem_cons.1 ho with rfl | ho
      · exact eq_of_beq he
      · exact h3 offset ho
    · simp only [pure, bind, he, Bool.false_eq_true, ↓reduceIte] at h
      have := ih _ true h
      simp at this

private theorem patchRanges_unchanged {width : Nat} (native : Nat → UInt8) (ranges : List (Nat × Nat))
    (memory : Bap.Memory width) (changed : Bool) (result : Bap.Memory width)
    (h : ranges.foldlM (m := Id) (init := (memory, changed)) (fun current range =>
      patchRange (fun address => pure (native address)) range.1 (List.range range.2) current) = (result, false)) :
    changed = false ∧ result = memory ∧ ∀ range ∈ ranges, ∀ offset, offset < range.2 →
      Bap.Memory.readByte memory (BitVec.ofNat width (range.1 + offset)) = native (range.1 + offset) := by
  induction ranges generalizing memory changed with
  | nil =>
    have h' : (memory, changed) = (result, false) := h
    simp only [Prod.mk.injEq] at h'
    exact ⟨h'.2, h'.1.symm, by simp⟩
  | cons head rest ih =>
    simp only [List.foldlM_cons] at h
    generalize hp : patchRange (m := Id) (fun address => pure (native address)) head.1 (List.range head.2) (memory, changed) = mid at h
    obtain ⟨m1, c1⟩ := mid
    obtain ⟨h1, h2, h3⟩ := ih m1 c1 h
    subst h1
    obtain ⟨h4, h5, h6⟩ := patchRange_unchanged native head.1 _ memory changed m1 hp
    subst h5
    refine ⟨h4, h2, ?_⟩
    intro range hr offset ho
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h6 offset (List.mem_range.2 ho)
    · exact h3 range hr offset ho

/-- What `readThroughM` settles on reads what `read` gives, at everything that a computation on that memory reads. So
an instruction that a worker interprets on it reads the native memory, whatever it wrote in the round. -/
theorem readThroughM_settled {width : Nat} (native : Nat → UInt8) (reads : Bap.Memory width → List (Nat × Nat)) (rounds : Nat)
    (memory result : Bap.Memory width)
    (h : readThroughM (m := Id) (fun cells => pure (reads cells)) (fun address => pure (native address)) rounds memory = some result) :
    ∀ range ∈ reads result, ∀ offset, offset < range.2 →
      Bap.Memory.readByte result (BitVec.ofNat width (range.1 + offset)) = native (range.1 + offset) := by
  induction rounds generalizing memory with
  | zero => simp [readThroughM, pure] at h
  | succ rounds ih =>
    simp [readThroughM, pure, bind] at h
    generalize hf : (List.foldlM (m := Id) (fun current range => patchRange (fun address => native address) range.fst
      (List.range range.snd) current) (memory, false) (reads memory)) = patched at h
    obtain ⟨m1, c1⟩ := patched
    cases c1 with
    | true =>
      simp only [↓reduceIte] at h
      exact ih m1 h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases h
      obtain ⟨_, _, h3⟩ := patchRanges_unchanged native _ result false m1 hf
      exact h3


theorem mem_activeThreads (threads : List ThreadContext) (context : ThreadContext) :
    context ∈ activeThreads threads ↔ context ∈ threads ∧ context.stopped = false := by
  simp [activeThreads]

/-- A worker reports its context: state, pc, pending branch and skip marker, with `stopThread` and
`resumeThread` of the round on top of its stopped flag. -/
theorem mergeRound_worker (contexts live : List ThreadContext) (results : List WorkerResult)
    (control : Std.HashMap Nat Bool) {context : ThreadContext} {result : WorkerResult} (hm : context ∈ contexts)
    (hr : results.find? (fun result => result.id == context.id) = some result) :
    { context with
      state := result.state
      pc := result.pc
      stopped := controlledStopped control context.id result.stopped
      pending := result.pending
      skip := result.skip } ∈ mergeRound contexts live results control := by
  simp only [mergeRound]
  apply List.mem_append_left
  rw [List.mem_map]
  exact ⟨context, hm, by simp only [hr]⟩

/-- A thread without a worker keeps its context. -/
theorem mergeRound_idle (contexts live : List ThreadContext) (results : List WorkerResult)
    (control : Std.HashMap Nat Bool) {context : ThreadContext} (hm : context ∈ contexts)
    (hr : ∀ result ∈ results, result.id ≠ context.id) :
    { context with stopped := controlledStopped control context.id context.stopped } ∈
      mergeRound contexts live results control := by
  have hnone : results.find? (fun result => result.id == context.id) = none := by
    rw [List.find?_eq_none]
    intro result hmr
    simpa using hr result hmr
  simp only [mergeRound]
  apply List.mem_append_left
  rw [List.mem_map]
  exact ⟨context, hm, by simp only [hnone]⟩

/-- A stopped thread doesn't run in a parallel round: workers exist for active threads, so that a stopped
thread with its own id keeps its state and pc. -/
theorem mergeRound_stopped_keeps (contexts live : List ThreadContext) (results : List WorkerResult)
    (control : Std.HashMap Nat Bool) {context : ThreadContext} (hm : context ∈ contexts)
    (hs : context.stopped = true) (hunique : ∀ other ∈ contexts, other.id = context.id → other = context)
    (hworkers : ∀ result ∈ results, ∃ active ∈ activeThreads contexts, active.id = result.id) :
    { context with stopped := controlledStopped control context.id context.stopped } ∈
      mergeRound contexts live results control := by
  apply mergeRound_idle contexts live results control hm
  intro result hmr he
  obtain ⟨active, ha, hid⟩ := hworkers result hmr
  obtain ⟨hma, hsa⟩ := (mem_activeThreads _ _).1 ha
  have := hunique active hma (by omega)
  rw [this, hs] at hsa
  cases hsa

/-- A thread that a hook created during the round survives it. -/
theorem mergeRound_new_thread (contexts live : List ThreadContext) (results : List WorkerResult)
    (control : Std.HashMap Nat Bool) {thread : ThreadContext} (hl : thread ∈ live)
    (hnew : ∀ context ∈ contexts, context.id ≠ thread.id) :
    { thread with stopped := controlledStopped control thread.id thread.stopped } ∈
      mergeRound contexts live results control := by
  simp only [mergeRound]
  apply List.mem_append_right
  rw [List.mem_map]
  refine ⟨thread, ?_, rfl⟩
  simp only [List.mem_filter, hl, true_and]
  simpa using hnew

/-- No thread comes out of nowhere, and none goes missing. -/
theorem mergeRound_ids (contexts live : List ThreadContext) (results : List WorkerResult)
    (control : Std.HashMap Nat Bool) (id : Nat) :
    (∃ c ∈ mergeRound contexts live results control, c.id = id) ↔
      (∃ c ∈ contexts, c.id = id) ∨ ∃ c ∈ live, c.id = id := by
  constructor
  · rintro ⟨c, hm, he⟩
    simp only [mergeRound, List.mem_append, List.mem_map, List.mem_filter] at hm
    rcases hm with ⟨c', hc', rfl⟩ | ⟨c', ⟨hc', _⟩, rfl⟩
    · refine Or.inl ⟨c', hc', ?_⟩
      rw [← he]
      split <;> rfl
    · exact Or.inr ⟨c', hc', he⟩
  · rintro (⟨c, hm, he⟩ | ⟨c, hm, he⟩)
    · simp only [mergeRound]
      refine ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨c, hm, rfl⟩), ?_⟩
      rw [← he]
      split <;> rfl
    · by_cases hnew : ∀ context ∈ contexts, context.id ≠ c.id
      · exact ⟨_, mergeRound_new_thread contexts live results control hm hnew, he⟩
      · simp only [ne_eq, Classical.not_forall, Classical.not_not] at hnew
        obtain ⟨c', hc', he'⟩ := hnew
        simp only [mergeRound]
        refine ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨c', hc', rfl⟩), ?_⟩
        rw [← he, ← he']
        split <;> rfl

/-! ### Saved contexts -/

/-- Saving a thread replaces its context. -/
theorem find_saveContext_same (threads : List ThreadContext) (context : ThreadContext) :
    (saveContext threads context).find? (fun thread => thread.id == context.id) = some context := by
  simp [saveContext]

/-- And leaves the others alone. -/
theorem find_saveContext_other (threads : List ThreadContext) (context : ThreadContext) {id : Nat}
    (h : id ≠ context.id) :
    (saveContext threads context).find? (fun thread => thread.id == id) =
      threads.find? (fun thread => thread.id == id) := by
  have hne : context.id ≠ id := fun he => h he.symm
  have hb : (context.id == id) = false := by simpa using hne
  simp only [saveContext, List.find?_cons, hb]
  induction threads with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.filter_cons, bne_iff_ne, ne_eq]
    by_cases hh : head.id = context.id
    · have hb' : (head.id == id) = false := by simpa using (by omega : head.id ≠ id)
      simp [hh, ih, hb]
    · simp only [hh, not_false_eq_true, ↓reduceIte, List.find?_cons, ih]

/-- A thread parked at a breakpoint gets its skip marker back: switching threads causes no re-fire. -/
theorem saveContext_keeps_skip (threads : List ThreadContext) (context : ThreadContext) {found : ThreadContext}
    (h : (saveContext threads context).find? (fun thread => thread.id == context.id) = some found) :
    found.skip = context.skip ∧ found.pc = context.pc ∧ found.pending = context.pending := by
  rw [find_saveContext_same] at h
  simp only [Option.some.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl⟩

theorem setThreadStopped_stopped (threads : List ThreadContext) (id : Nat) (stopped : Bool) (context : ThreadContext)
    (hm : context ∈ setThreadStopped threads id stopped) (he : context.id = id) : context.stopped = stopped := by
  simp only [setThreadStopped, List.mem_map] at hm
  obtain ⟨c, _, rfl⟩ := hm
  by_cases h : c.id = id
  · simp [h]
  · simp [h] at he

/-! ### Address spaces -/

section Spaces

variable {α : Type}

/-- The memories of the processes: the shared one, and those of the forks. `value` stands for what the
native memory and the memory variable hold. -/
structure Spaces (α : Type) where
  processes : Std.HashMap Nat α
  shared : α

/-- The memory that thread `id` sees. -/
def Spaces.read (s : Spaces α) (id : Nat) : α := s.processes[id]?.getD s.shared

/-- `read` is what the engine runs on: `nativeFor` of the thread. -/
theorem nativeFor_eq_read (s : Spaces α) (id : Nat) :
    nativeFor s.processes (some s.shared) id = some (s.read id) := by
  simp only [nativeFor, Spaces.read, Std.HashMap.get?_eq_getElem?]
  cases s.processes[id]? <;> rfl

/-- A store of thread `id`. -/
def Spaces.write (s : Spaces α) (id : Nat) (value : α) : Spaces α :=
  if s.processes.contains id then { s with processes := s.processes.insert id value }
  else { s with shared := value }

/-- `cloneProcessMemory`: the child gets a copy of the memory that the parent sees. -/
def Spaces.fork (s : Spaces α) (parent child : Nat) : Spaces α :=
  { s with processes := s.processes.insert child (s.read parent) }

private theorem getElem?_none {m : Std.HashMap Nat α} {id : Nat} (h : m.contains id = false) : m[id]? = none := by
  rw [Std.HashMap.contains_eq_isSome_getElem?] at h
  simpa using h

private theorem read_shared {s : Spaces α} {id : Nat} (h : s.processes.contains id = false) : s.read id = s.shared := by
  simp [Spaces.read, getElem?_none h]

/-- A store is seen by the thread that made it. -/
theorem Spaces.read_write_same (s : Spaces α) (id : Nat) (value : α) : (s.write id value).read id = value := by
  cases h : s.processes.contains id with
  | true => simp [Spaces.write, h, Spaces.read]
  | false => simp [Spaces.write, h, Spaces.read, getElem?_none h]

/-- Isolation: a store does not reach a thread of another address space. -/
theorem Spaces.read_write_isolated (s : Spaces α) {id other : Nat} (value : α) (hne : id ≠ other)
    (h : shouldShareMemory s.processes id other = false) :
    (s.write id value).read other = s.read other := by
  cases hc : s.processes.contains id with
  | true => simp [Spaces.write, hc, Spaces.read, Std.HashMap.getElem?_insert, hne]
  | false =>
    have ho : s.processes.contains other = true := by
      simpa [shouldShareMemory, hc] using h
    obtain ⟨v, hv⟩ : ∃ v, s.processes[other]? = some v := by
      rw [Std.HashMap.contains_eq_isSome_getElem?] at ho
      exact Option.isSome_iff_exists.1 ho
    simp [Spaces.write, hc, Spaces.read, hv]

/-- Threads that share memory see each other's stores. -/
theorem Spaces.read_write_shared (s : Spaces α) {id other : Nat} (value : α)
    (h : shouldShareMemory s.processes id other = true) :
    (s.write id value).read other = value := by
  have h' : s.processes.contains id = false ∧ s.processes.contains other = false := by
    simpa [shouldShareMemory] using h
  simp [Spaces.write, h'.1, Spaces.read, getElem?_none h'.2]

/-- A fork starts from what its parent sees. -/
theorem Spaces.read_fork_child (s : Spaces α) (parent child : Nat) : (s.fork parent child).read child = s.read parent := by
  simp [Spaces.fork, Spaces.read]

/-- A fork leaves everybody else where they are, its parent first of all. -/
theorem Spaces.read_fork_other (s : Spaces α) (parent child : Nat) {other : Nat} (h : other ≠ child) :
    (s.fork parent child).read other = s.read other := by
  have hne : child ≠ other := fun he => h he.symm
  simp [Spaces.fork, Spaces.read, Std.HashMap.getElem?_insert, hne]

/-- After a fork, parent and child are in different address spaces. -/
theorem Spaces.fork_isolated (s : Spaces α) (parent child : Nat) :
    shouldShareMemory (s.fork parent child).processes parent child = false := by
  simp [shouldShareMemory, Spaces.fork]

/-- What runs: stores of the current thread, thread switches, and forks. -/
inductive SpaceAction (α : Type) where
  | store (value : α)
  | switch (next : Nat)
  | fork (child : Nat)

/-- A machine with memory in its state, as an emulator has: `parked` is what each thread's context holds,
and `selectMemory` picks what the state holds after a switch. -/
structure SpaceMachine (α : Type) where
  spaces : Spaces α
  current : Nat
  /-- The memory variable of the state of the current thread. -/
  memory : α
  /-- The memory variable of the saved contexts. -/
  parked : Nat → α

/-- What `switchThread` saves: the context of the current thread and, on the way out of the shared address
space, what all threads of it hold (`parkMemory`). -/
def SpaceMachine.save (m : SpaceMachine α) (next : Nat) : Nat → α := fun id =>
  if id = m.current then m.memory
  else if shouldShareMemory m.spaces.processes m.current next then m.parked id
  else if !m.spaces.processes.contains m.current && !m.spaces.processes.contains id then m.memory
  else m.parked id

def SpaceMachine.apply (m : SpaceMachine α) : SpaceAction α → SpaceMachine α
  | .store value => { m with spaces := m.spaces.write m.current value, memory := value }
  | .switch next =>
    { m with
      current := next
      memory := selectMemory m.spaces.processes m.current next m.memory (m.save next next)
      parked := m.save next }
  | .fork child =>
    { m with
      spaces := m.spaces.fork m.current child
      parked := fun id => if id = child then m.memory else m.parked id }

/-- The state and the saved contexts hold what their address spaces hold. -/
structure SpaceMachine.Sound (m : SpaceMachine α) : Prop where
  current : m.memory = m.spaces.read m.current
  parked : ∀ id, m.spaces.processes.contains id = true → id ≠ m.current → m.parked id = m.spaces.read id
  shared : ∀ id, m.spaces.processes.contains id = false → m.spaces.processes.contains m.current = true →
    m.parked id = m.spaces.shared

private theorem contains_write (s : Spaces α) (id : Nat) (value : α) (x : Nat) :
    (s.write id value).processes.contains x = s.processes.contains x := by
  cases hc : s.processes.contains id with
  | false => simp [Spaces.write, hc]
  | true =>
    simp only [Spaces.write, hc, ↓reduceIte, Std.HashMap.contains_insert]
    by_cases he : id = x
    · subst he
      simp [hc]
    · simp [he]

theorem SpaceMachine.sound_store (m : SpaceMachine α) (h : m.Sound) (value : α) : (m.apply (.store value)).Sound := by
  refine ⟨(Spaces.read_write_same _ _ _).symm, ?_, ?_⟩
  · intro id hid hne
    have hid' : m.spaces.processes.contains id = true := by
      have : (m.spaces.write m.current value).processes.contains id = true := hid
      rwa [contains_write] at this
    have hne' : id ≠ m.current := hne
    show m.parked id = (m.spaces.write m.current value).read id
    rw [Spaces.read_write_isolated m.spaces value (fun he => hne' he.symm) (by simp [shouldShareMemory, hid'])]
    exact h.parked id hid' hne'
  · intro id hid hcur
    have hid' : m.spaces.processes.contains id = false := by
      have : (m.spaces.write m.current value).processes.contains id = false := hid
      rwa [contains_write] at this
    have hcur' : m.spaces.processes.contains m.current = true := by
      have : (m.spaces.write m.current value).processes.contains m.current = true := hcur
      rwa [contains_write] at this
    show m.parked id = (m.spaces.write m.current value).shared
    rw [h.shared id hid' hcur']
    simp [Spaces.write, hcur']

theorem SpaceMachine.sound_switch (m : SpaceMachine α) (h : m.Sound) (next : Nat) : (m.apply (.switch next)).Sound := by
  have hsaveNext : m.save next next = (if next = m.current then m.memory else
      if shouldShareMemory m.spaces.processes m.current next then m.parked next
      else if !m.spaces.processes.contains m.current && !m.spaces.processes.contains next then m.memory
      else m.parked next) := rfl
  refine ⟨?_, ?_, ?_⟩
  · show selectMemory m.spaces.processes m.current next m.memory (m.save next next) = m.spaces.read next
    cases hshare : shouldShareMemory m.spaces.processes m.current next with
    | true =>
      have hs' : m.spaces.processes.contains m.current = false ∧ m.spaces.processes.contains next = false := by
        simpa [shouldShareMemory] using hshare
      simp only [selectMemory, hshare, ite_true]
      rw [h.current, read_shared hs'.1, read_shared hs'.2]
    | false =>
      simp only [selectMemory, hshare, Bool.false_eq_true, ite_false, hsaveNext]
      by_cases he : next = m.current
      · subst he
        simp [h.current]
      · simp only [he, ite_false]
        cases hn : m.spaces.processes.contains next with
        | true =>
          simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]
          exact h.parked next hn he
        | false =>
          have hc : m.spaces.processes.contains m.current = true := by
            simpa [shouldShareMemory, hn] using hshare
          simp only [hc, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
          rw [read_shared hn]
          exact h.shared next hn hc
  · intro id hid hne
    have hne' : id ≠ next := hne
    have hid' : m.spaces.processes.contains id = true := hid
    show m.save next id = m.spaces.read id
    simp only [SpaceMachine.save]
    by_cases hcur : id = m.current
    · subst hcur
      simp [h.current]
    · simp only [hcur, ite_false, hid', Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_self]
      exact h.parked id hid' hcur
  · intro id hid hcur
    have hid' : m.spaces.processes.contains id = false := hid
    have hn : m.spaces.processes.contains next = true := hcur
    show m.save next id = m.spaces.shared
    have hshare : shouldShareMemory m.spaces.processes m.current next = false := by
      simp [shouldShareMemory, hn]
    simp only [SpaceMachine.save, hshare, Bool.false_eq_true, ite_false, hid', Bool.not_false, Bool.and_true]
    by_cases hc : id = m.current
    · subst hc
      simp [h.current, read_shared hid']
    · cases hcc : m.spaces.processes.contains m.current with
      | true =>
        simp only [hc, ite_false, Bool.not_true, Bool.false_eq_true]
        exact h.shared id hid' hcc
      | false =>
        simp only [hc, ite_false, Bool.not_false, ite_true]
        rw [h.current, read_shared hcc]

theorem SpaceMachine.sound_fork (m : SpaceMachine α) (h : m.Sound) (child : Nat) (hchild : child ≠ m.current) :
    (m.apply (.fork child)).Sound := by
  refine ⟨?_, ?_, ?_⟩
  · show m.memory = (m.spaces.fork m.current child).read m.current
    rw [Spaces.read_fork_other _ _ _ (fun he => hchild he.symm)]
    exact h.current
  · intro id hid hne
    have hne' : id ≠ m.current := hne
    show (if id = child then m.memory else m.parked id) = (m.spaces.fork m.current child).read id
    by_cases he : id = child
    · subst he
      simp only [ite_true]
      rw [Spaces.read_fork_child]
      exact h.current
    · simp only [he, ite_false]
      rw [Spaces.read_fork_other _ _ _ he]
      have hid' : m.spaces.processes.contains id = true := by
        have : (m.spaces.processes.insert child (m.spaces.read m.current)).contains id = true := hid
        simpa [Std.HashMap.contains_insert, Ne.symm he] using this
      exact h.parked id hid' hne'
  · intro id hid hcur
    have hid' : (m.spaces.processes.insert child (m.spaces.read m.current)).contains id = false := hid
    have hne : id ≠ child := by
      rintro rfl
      simp at hid'
    have hid'' : m.spaces.processes.contains id = false := by
      simpa [Std.HashMap.contains_insert, Ne.symm hne] using hid'
    have hcur' : m.spaces.processes.contains m.current = true := by
      have : (m.spaces.processes.insert child (m.spaces.read m.current)).contains m.current = true := hcur
      simpa [Std.HashMap.contains_insert, hchild] using this
    show (if id = child then m.memory else m.parked id) = m.spaces.shared
    simp only [hne, ite_false]
    exact h.shared id hid'' hcur'

/-- A run in which nothing writes to the address space of `p`, or replaces it. -/
def SpaceMachine.Spares (p : Nat) : SpaceMachine α → List (SpaceAction α) → Prop
  | _, [] => True
  | m, .store value :: rest =>
    (m.current ≠ p ∧ shouldShareMemory m.spaces.processes m.current p = false) ∧
      Spares p (m.apply (.store value)) rest
  | m, .switch next :: rest => Spares p (m.apply (.switch next)) rest
  | m, .fork child :: rest =>
    (child ≠ p ∧ child ≠ m.current) ∧ Spares p (m.apply (.fork child)) rest

/-- A whole run. -/
def SpaceMachine.run (m : SpaceMachine α) : List (SpaceAction α) → SpaceMachine α
  | [] => m
  | action :: rest => (m.apply action).run rest

/-- Memory isolation across forks, end to end: whatever other processes store, and however threads switch
and fork, a process comes back to the memory it left, and that is the memory in its state, which is
`selectMemory` at work with `nativeFor` and the stores of the machine. -/
theorem SpaceMachine.isolation (m : SpaceMachine α) (h : m.Sound) (p : Nat) (actions : List (SpaceAction α))
    (hspares : Spares p m actions) :
    (m.run actions).Sound ∧ (m.run actions).spaces.read p = m.spaces.read p := by
  induction actions generalizing m with
  | nil => exact ⟨h, rfl⟩
  | cons action rest ih =>
    cases action with
    | store value =>
      obtain ⟨⟨hne, hshare⟩, hrest⟩ := hspares
      obtain ⟨h1, h2⟩ := ih _ (m.sound_store h value) hrest
      refine ⟨h1, ?_⟩
      show ((m.apply (.store value)).run rest).spaces.read p = _
      rw [h2]
      exact Spaces.read_write_isolated m.spaces value hne hshare
    | switch next => exact ih _ (m.sound_switch h next) hspares
    | fork child =>
      obtain ⟨⟨hne, hcur⟩, hrest⟩ := hspares
      obtain ⟨h1, h2⟩ := ih _ (m.sound_fork h child hcur) hrest
      refine ⟨h1, ?_⟩
      show ((m.apply (.fork child)).run rest).spaces.read p = _
      rw [h2]
      exact Spaces.read_fork_other m.spaces m.current child (fun he => hne he.symm)

/-- So a process that comes back finds its memory in its state. -/
theorem SpaceMachine.isolation_memory (m : SpaceMachine α) (h : m.Sound) (p : Nat) (actions : List (SpaceAction α))
    (hspares : Spares p m actions) (hback : (m.run actions).current = p) :
    (m.run actions).memory = m.spaces.read p := by
  obtain ⟨h1, h2⟩ := m.isolation h p actions hspares
  rw [h1.current, hback, h2]

end Spaces

/-! ### Hooks -/

section Hooks

variable {β : Type}

theorem mem_hooksForAccess (first last : β → Nat) (hooks : List β) (address size : Nat) (hook : β) :
    hook ∈ hooksForAccess first last hooks address size ↔
      hook ∈ hooks ∧ accessTouches (first hook) (last hook) address size = true := by
  simp [hooksForAccess]

theorem mem_hooksForCode (first last : β → Nat) (hooks : List β) (address : Nat) (hook : β) :
    hook ∈ hooksForCode first last hooks address ↔ hook ∈ hooks ∧ first hook ≤ address ∧ address ≤ last hook := by
  simp [hooksForCode]

/-- Registration order: the hooks that fire come in the order of the table, which `onCode`, `onRead`,
`onWrite`, `onSyscall` and `onIntrinsic` keep by appending. -/
theorem hooksForAccess_sublist (first last : β → Nat) (hooks : List β) (address size : Nat) :
    (hooksForAccess first last hooks address size).Sublist hooks := List.filter_sublist

theorem hooksForCode_sublist (first last : β → Nat) (hooks : List β) (address : Nat) :
    (hooksForCode first last hooks address).Sublist hooks := List.filter_sublist

/-- How often a hook occurs among those a filter selects, with distinct ids. -/
private theorem count_filter (key : β → Nat) (p : β → Bool) (hooks : List β) (hnd : (hooks.map key).Nodup)
    {hook : β} (hm : hook ∈ hooks) :
    ((hooks.filter p).filter fun other => key other == key hook).length = if p hook then 1 else 0 := by
  induction hooks with
  | nil => cases hm
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    obtain ⟨hhead, htail⟩ := hnd
    rcases List.mem_cons.1 hm with rfl | hm'
    · have hnone : ∀ other ∈ tail, (key other == key hook) = false := by
        intro other ho
        have := hhead other ho
        simpa using this
      have hzero : ((tail.filter p).filter fun other => key other == key hook) = [] := by
        rw [List.filter_eq_nil_iff]
        intro other ho
        have := hnone other (List.mem_filter.1 ho).1
        simp [this]
      cases hp : p hook <;> simp [hp, hzero]
    · have hne : (key head == key hook) = false := by
        have := hhead hook hm'
        exact beq_false_of_ne (Ne.symm this)
      have := ih htail hm'
      cases hp : p head <;> simp only [List.filter_cons, hp, hne, Bool.false_eq_true, ite_false, ite_true] <;> exact this

/-- Exactly once: with distinct ids, an access fires a hook once if it touches the hook's range, and
never otherwise. -/
theorem access_fires_exactly_once (key first last : β → Nat) (hooks : List β) (address size : Nat)
    (hnd : (hooks.map key).Nodup) {hook : β} (hm : hook ∈ hooks) :
    ((hooksForAccess first last hooks address size).filter fun other => key other == key hook).length =
      if accessTouches (first hook) (last hook) address size then 1 else 0 :=
  count_filter key _ hooks hnd hm

/-- And an instruction fires a code hook once if its range covers the address. -/
theorem code_fires_exactly_once (key first last : β → Nat) (hooks : List β) (address : Nat)
    (hnd : (hooks.map key).Nodup) {hook : β} (hm : hook ∈ hooks) :
    ((hooksForCode first last hooks address).filter fun other => key other == key hook).length =
      if first hook ≤ address ∧ address ≤ last hook then 1 else 0 := by
  have := count_filter key (fun hook => decide (first hook ≤ address) && decide (address ≤ last hook)) hooks hnd hm
  simp only [hooksForCode]
  rw [this]
  by_cases h1 : first hook ≤ address <;> by_cases h2 : address ≤ last hook <;> simp [h1, h2]

/-- `forM` hands every hook the arguments of the access, in order, once each: here with a log for effect. -/
theorem forM_logs {γ : Type} (hooks : List β) (act : β → γ) (log : List γ) :
    (hooks.forM (fun hook => (modify (· ++ [act hook]) : StateM (List γ) Unit))).run log =
      ((), log ++ hooks.map act) := by
  induction hooks generalizing log with
  | nil => simp [pure, StateT.run, StateT.pure]
  | cons head tail ih =>
    simp only [List.map_cons]
    show (tail.forM (fun hook => (modify (· ++ [act hook]) : StateM (List γ) Unit))).run (log ++ [act head]) = _
    rw [ih]
    simp

/-- Fresh ids: `nextHook` counts, so that a table of hooks with ids below it stays free of duplicates. -/
theorem register_nodup (key : β → Nat) (hooks : List β) (next : Nat) (hook : β) (hnd : (hooks.map key).Nodup)
    (hbelow : ∀ other ∈ hooks, key other < next) (hkey : key hook = next) :
    ((hooks ++ [hook]).map key).Nodup ∧ ∀ other ∈ hooks ++ [hook], key other < next + 1 := by
  constructor
  · simp only [List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.2 ⟨hnd, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    obtain ⟨other, ho, rfl⟩ := List.mem_map.1 ha
    have := hbelow other ho
    omega
  · intro other ho
    rcases List.mem_append.1 ho with ho | ho
    · have := hbelow other ho
      omega
    · simp only [List.mem_singleton] at ho
      subst ho
      omega

end Hooks

end Bap.Emu.Model

namespace Bap.Emu

/-! ### Precise faults -/

section Precise

variable {ε σ : Type}

/-- Single steps from a state go `count` steps and then fail with `error`, in the state `final`. -/
inductive FaultsIn (single : EStateM ε σ Bool) : Nat → σ → ε → σ → Prop
  | now {state error final} : single state = .error error final → FaultsIn single 0 state error final
  | later {count state next error final} : single state = .ok true next → FaultsIn single count next error final →
      FaultsIn single (count + 1) state error final

/-- What a run of single steps comes to on such a state: the failure, with its state, whatever else the run was given. -/
theorem runM_faults {single : EStateM ε σ Bool} {count : Nat} {state : σ} {error : ε} {final : σ} (h : FaultsIn single count state error final)
    (fuel total : Nat) (hf : count < fuel) : runM single fuel total state = .error error final := by
  induction h generalizing fuel total with
  | now he =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [runM, bind, EStateM.bind, he]
  | later he _ ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [runM, bind, EStateM.bind, he]
      exact ih fuel (total + 1) (by omega)

/-- Single steps are a function of the state. -/
theorem FaultsIn.unique {single : EStateM ε σ Bool} {k₁ k₂ : Nat} {state : σ} {e₁ e₂ : ε} {f₁ f₂ : σ} (h₁ : FaultsIn single k₁ state e₁ f₁)
    (h₂ : FaultsIn single k₂ state e₂ f₂) : k₁ = k₂ ∧ e₁ = e₂ ∧ f₁ = f₂ := by
  induction h₁ generalizing k₂ with
  | now he =>
    cases h₂ with
    | now he' =>
      rw [he] at he'
      injection he' with h1 h2
      exact ⟨rfl, h1, h2⟩
    | later he' _ => rw [he] at he'; cases he'
  | later he _ ih =>
    cases h₂ with
    | now he' => rw [he] at he'; cases he'
    | later he' hr =>
      rw [he] at he'
      injection he' with _ hs
      subst hs
      obtain ⟨h1, h2, h3⟩ := ih hr
      exact ⟨by omega, h2, h3⟩

/-- What a step that may run a range does, as against single steps: `lowerGraph_correct` for the blocks it ran, `stepExecute_error` for its
failure. `allow` only tells it how far it may go, and what it did not run, single steps run next. A step that ran `chained + 1`
instructions is that many single steps, a step that reports the end of the thread has no fault to come, and a step that fails either did not chain, and
is the single step, or has rolled back to where single steps see what they would have seen. -/
structure RangeLaws (step single again : EStateM ε σ Bool) (allow : Nat → EStateM ε σ Unit) (chained : EStateM ε σ Nat) : Prop where
  allow_ok : ∀ budget state, ∃ next, allow budget state = .ok () next ∧
    ∀ count error final, FaultsIn single count state error final → FaultsIn single count next error final
  chained_ok : ∀ state, ∃ count, chained state = .ok count state
  ran : ∀ state next count, step state = .ok true next → chained next = .ok count next →
    ∀ k error final, FaultsIn single k state error final → count + 1 ≤ k ∧ FaultsIn single (k - (count + 1)) next error final
  halted : ∀ state next k error final, step state = .ok false next → ¬ FaultsIn single k state error final
  failed : ∀ state e r k error final, step state = .error e r → FaultsIn single k state error final →
    (∃ r', again r = .ok true r' ∧ ∃ k', k' ≤ k ∧ FaultsIn single k' r' error final) ∨ (∃ r', again r = .ok false r' ∧ e = error ∧ r' = final)

private theorem chained_faults {step single again : EStateM ε σ Bool} {allow : Nat → EStateM ε σ Unit} {chained : EStateM ε σ Nat}
    (laws : RangeLaws step single again allow chained) {error : ε} {final : σ} (rounds remaining total k : Nat) (state : σ)
    (hk : FaultsIn single k state error final) (hr : k < rounds) (hrem : k < remaining) :
    ∃ e r, runChainedM step allow chained rounds remaining total state = .error e r ∧
      ((∃ r', again r = .ok true r' ∧ ∃ k', k' ≤ k ∧ FaultsIn single k' r' error final) ∨ (∃ r', again r = .ok false r' ∧ e = error ∧ r' = final)) := by
  induction rounds generalizing remaining total k state with
  | zero => omega
  | succ rounds ih =>
    obtain ⟨s1, ha, hk1⟩ := laws.allow_ok (remaining - 1) state
    have hk1' := hk1 _ _ _ hk
    have hrun : runChainedM step allow chained (rounds + 1) remaining total state =
        match step s1 with
        | .ok true s2 => (do
            let extra := min (← chained) (remaining - 1)
            runChainedM step allow chained rounds (remaining - 1 - extra) (total + 1 + extra)) s2
        | .ok false s2 => .ok total s2
        | .error e r => .error e r := by
      rw [runChainedM, ite_eq_right (by omega)]
      show EStateM.bind (allow _) _ state = _
      simp only [EStateM.bind, ha]
      show EStateM.bind step _ s1 = _
      simp only [EStateM.bind]
      cases step s1 with
      | error e r => rfl
      | ok go s2 => cases go <;> rfl
    rw [hrun]
    cases hs : step s1 with
    | error e r => exact ⟨e, r, rfl, laws.failed s1 e r k error final hs hk1'⟩
    | ok go s2 =>
      cases go with
      | false => exact absurd hk1' (laws.halted s1 s2 k error final hs)
      | true =>
        obtain ⟨c, hc⟩ := laws.chained_ok s2
        obtain ⟨hle, hrest⟩ := laws.ran s1 s2 c hs hc k error final hk1'
        have hmin : min c (remaining - 1) = c := by omega
        obtain ⟨e, r, h1, h2⟩ := ih (remaining - 1 - c) (total + 1 + c) (k - (c + 1)) s2 hrest (by omega) (by omega)
        refine ⟨e, r, ?_, ?_⟩
        · show EStateM.bind chained _ s2 = _
          simp only [EStateM.bind, hc, hmin]
          exact h1
        · rcases h2 with ⟨r', h3, k', hk', h4⟩ | h2
          · exact Or.inl ⟨r', h3, k', by omega, h4⟩
          · exact Or.inr h2

private theorem tryCatch_error {α : Type} {x : EStateM ε σ α} {handle : ε → EStateM ε σ α} {s r : σ} {e : ε} (hx : x s = .error e r) :
    (tryCatch x handle : EStateM ε σ α) s = handle e r := by
  show EStateM.tryCatch x handle s = _
  simp only [EStateM.tryCatch, hx]
  rfl

/-- With nothing that chains, a step is a single step, and the laws hold. They are what the code that runs has to meet for ranges. -/
theorem rangeLaws_single (single : EStateM ε σ Bool) :
    RangeLaws single single (pure false) (fun _ => pure ()) (pure 0) where
  allow_ok := fun _ state => ⟨state, rfl, fun _ _ _ h => h⟩
  chained_ok := fun state => ⟨0, rfl⟩
  ran := by
    intro state next count hs hc k error final hk
    injection hc with hc _
    subst hc
    cases hk with
    | now he => rw [hs] at he; cases he
    | later he hr =>
      rw [hs] at he
      injection he with _ hn
      subst hn
      exact ⟨by omega, hr⟩
  halted := by
    intro state next k error final hs hk
    cases hk with
    | now he => rw [hs] at he; cases he
    | later he _ => rw [hs] at he; cases he
  failed := by
    intro state e r k error final hs hk
    refine Or.inr ⟨r, rfl, ?_⟩
    cases hk with
    | now he =>
      rw [hs] at he
      injection he with h1 h2
      exact ⟨h1, h2⟩
    | later he _ => rw [hs] at he; cases he

/-- **A fault in a range is a fault in single steps.** When single steps from a state fault within the fuel, with whatever error and in whatever state, a
run that chains them, for the same fuel, fails with that error, in that state: registers, memory and pc as single steps leave them, which is
what `Bap.Emu.run` does. -/
theorem runPreciseM_fault {step single again : EStateM ε σ Bool} {allow : Nat → EStateM ε σ Unit} {chained : EStateM ε σ Nat}
    (laws : RangeLaws step single again allow chained) {error : ε} {final : σ} {k fuel : Nat} {state : σ}
    (hk : FaultsIn single k state error final) (hf : k < fuel) :
    runPreciseM (runChainedM step allow chained fuel fuel 0) single again (fuel + 1) state = .error error final := by
  obtain ⟨e, r, h1, h2⟩ := chained_faults laws fuel fuel 0 k state hk hf hf
  unfold runPreciseM
  rw [tryCatch_error h1]
  show EStateM.bind again _ r = _
  rcases h2 with ⟨r', h3, k', hk', h4⟩ | ⟨r', h3, rfl, rfl⟩
  · simp only [EStateM.bind, h3]
    show EStateM.bind (runM single (fuel + 1) 0) _ r' = _
    simp only [EStateM.bind, runM_faults h4 (fuel + 1) 0 (by omega)]
  · simp only [EStateM.bind, h3]
    rfl

end Precise

theorem rangeSiteStops_hooked (dirty late : Bool) : rangeSiteStops dirty late true = true := by simp [rangeSiteStops]

/-- A block with no hook is entered, when no code was written and no hook arrived. -/
theorem rangeSiteStops_quiet : rangeSiteStops false false false = false := rfl

theorem rangeBudgetOf_watched (budget : Nat) : rangeBudgetOf budget true = 0 := rfl

theorem rangeBudgetOf_unwatched (budget : Nat) : rangeBudgetOf budget false = budget := rfl

/-! ### Steps that are taken back -/

/-- A step at an address that met a hook runs one instruction, as does any step of a worker while there are hooks. -/
theorem accessesWatched_restarted (deferred hasHooks : Bool) : accessesWatched true deferred hasHooks = true := rfl

theorem accessesWatched_deferred (restarted : Bool) : accessesWatched restarted true true = true := by
  simp [accessesWatched]

/-- Without hooks, nothing limits a step. -/
theorem accessesWatched_none (deferred : Bool) : accessesWatched false deferred false = false := by
  simp [accessesWatched]

/-- An access that no hook watches takes nothing back. -/
theorem accessRestarts_miss (budget : Nat) (deferred : Bool) : accessRestarts false budget deferred = false := rfl

/-- In a step of one instruction, hooks fire: it is not taken back, and neither is a worker, which fires them where they are. -/
theorem accessRestarts_single (hit deferred : Bool) : accessRestarts hit 0 deferred = false := by
  simp [accessRestarts]

theorem accessRestarts_deferred (hit : Bool) (budget : Nat) : accessRestarts hit budget true = false := by
  simp [accessRestarts]

/-- So a hook only ever runs in a step of one instruction, of a thread that can be rolled back: whenever a hook is hit in
a step that may chain, the step is taken back before the hook runs. -/
theorem accessRestarts_chained {budget : Nat} (h : budget ≠ 0) : accessRestarts true budget false = true := by
  simp [accessRestarts, h]

section Restart

variable {ε σ : Type}

/-- What `restart` must do: tell whether the step is to run again, change nothing that single steps see, and leave a state for
which the step, when told to run again, is as good as from where it started. `stepExecute_error` gives that for a failed step of the emulator. -/
structure RestartLaws (step single : EStateM ε σ Bool) (restart : EStateM ε σ Bool) : Prop where
  restart_ok : ∀ state, ∃ again next, restart state = .ok again next ∧ (again = false → next = state)
  taken_back : ∀ state error failed next, step state = .error error failed → restart failed = .ok true next →
    ∀ count faultError final, FaultsIn single count state faultError final → FaultsIn single count next faultError final

private theorem restartM_run (step restart : EStateM ε σ Bool) (state : σ) :
    (restartM step restart : EStateM ε σ Bool) state =
      match step state with
      | .ok value next => .ok value next
      | .error error failed =>
        match restart failed with
        | .ok true next => step next
        | .ok false next => .error error next
        | .error error next => .error error next := by
  unfold restartM
  show EStateM.tryCatch step _ state = _
  simp only [EStateM.tryCatch]
  cases step state with
  | ok value next => rfl
  | error error failed =>
    show EStateM.bind restart _ failed = _
    simp only [EStateM.bind]
    cases restart failed with
    | ok again next => cases again <;> rfl
    | error error next => rfl

/-- A step that is not told to run again is the step. -/
theorem restartM_ok {step restart : EStateM ε σ Bool} {state next : σ} {value : Bool} (h : step state = .ok value next) :
    (restartM step restart : EStateM ε σ Bool) state = .ok value next := by
  rw [restartM_run, h]

theorem restartM_error {step restart : EStateM ε σ Bool} {state failed next : σ} {error : ε} (h : step state = .error error failed)
    (hr : restart failed = .ok false next) : (restartM step restart : EStateM ε σ Bool) state = .error error next := by
  rw [restartM_run, h]
  simp only [hr]

/-- A step that is told to run again is its run from where the failure left it. -/
theorem restartM_again {step restart : EStateM ε σ Bool} {state failed next : σ} {error : ε} (h : step state = .error error failed)
    (hr : restart failed = .ok true next) : (restartM step restart : EStateM ε σ Bool) state = step next := by
  rw [restartM_run, h]
  simp only [hr]

/-- **Taking a step back keeps all that ranges promise.** If a step that may run a range meets `RangeLaws`, so does the step that runs
again from a hook of an access, so that `runPreciseM_fault` holds of it, and for the same reason: all that ran before the
hook was rolled back, and nothing saw it. -/
theorem rangeLaws_restartM {step single again restart : EStateM ε σ Bool} {allow : Nat → EStateM ε σ Unit} {chained : EStateM ε σ Nat}
    (laws : RangeLaws step single again allow chained) (hr : RestartLaws step single restart) :
    RangeLaws (restartM step restart) single again allow chained where
  allow_ok := laws.allow_ok
  chained_ok := laws.chained_ok
  ran := by
    intro state next count hs hc k error final hk
    cases h1 : step state with
    | ok value mid =>
      rw [restartM_ok h1] at hs
      injection hs with hv hm
      subst hv
      subst hm
      exact laws.ran state mid count h1 hc k error final hk
    | error e failed =>
      obtain ⟨go, r, h2, _⟩ := hr.restart_ok failed
      cases go with
      | false =>
        rw [restartM_error h1 h2] at hs
        cases hs
      | true =>
        rw [restartM_again h1 h2] at hs
        exact laws.ran r next count hs hc k error final (hr.taken_back state e failed r h1 h2 k error final hk)
  halted := by
    intro state next k error final hs hk
    cases h1 : step state with
    | ok value mid =>
      rw [restartM_ok h1] at hs
      injection hs with hv hm
      subst hv
      subst hm
      exact laws.halted state mid k error final h1 hk
    | error e failed =>
      obtain ⟨go, r, h2, _⟩ := hr.restart_ok failed
      cases go with
      | false =>
        rw [restartM_error h1 h2] at hs
        cases hs
      | true =>
        rw [restartM_again h1 h2] at hs
        exact laws.halted r next k error final hs (hr.taken_back state e failed r h1 h2 k error final hk)
  failed := by
    intro state e r k error final hs hk
    cases h1 : step state with
    | ok value mid =>
      rw [restartM_ok h1] at hs
      cases hs
    | error e1 failed =>
      obtain ⟨go, r1, h2, hkeep⟩ := hr.restart_ok failed
      cases go with
      | false =>
        rw [restartM_error h1 h2] at hs
        injection hs with he hrr
        subst he
        subst hrr
        rw [hkeep rfl]
        exact laws.failed state e1 failed k error final h1 hk
      | true =>
        rw [restartM_again h1 h2] at hs
        exact laws.failed r1 e r k error final hs (hr.taken_back state e1 failed r1 h1 h2 k error final hk)

end Restart

end Bap.Emu
