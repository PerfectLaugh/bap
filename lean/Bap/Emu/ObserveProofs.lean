import Bap.Bil.Observe
import Bap.Proofs.Bil
import Lean.Elab.Command

/-! What an interpreted instruction tells its memory hooks. `Bil.runObserved` is `IO`, and the observer is
arbitrary, but the monad laws suffice to show what it does: it calls the observer once for each access of
the pure trace `traceProgram`, in order, and then returns what `Bil.run` returns. So every load and store
is reported exactly once, with its address, size and value, before its effect takes place, and a failure
reports what happened up to it. -/

open Lean Elab Command in
local elab "open_private " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

set_option linter.unusedSimpArgs false

namespace Bap.Emu.Observe

open Bap.Bil

/-- A load or a store, as the observer sees it. -/
structure Access where
  write : Bool
  address : Nat
  size : Nat
  value : Nat
  deriving DecidableEq, Repr

/-- A computation with its accesses, up to its failure if it fails. -/
abbrev Traced (α : Type) := List Access × Except String α

def Traced.bind {α β : Type} (x : Traced α) (f : α → Traced β) : Traced β :=
  match x.2 with
  | .error error => (x.1, .error error)
  | .ok value =>
    let y := f value
    (x.1 ++ y.1, y.2)

def Traced.ofExcept {α : Type} (x : Except String α) : Traced α := ([], x)

/-- Runs the accesses through the observer. -/
def replay (observer : MemoryObserver) (accesses : List Access) : IO Unit :=
  accesses.forM fun access => observer access.write access.address access.size access.value

/-- `x` calls the observer for the accesses of `t`, and then returns what `t` returns. -/
def Obs {α : Type} (observer : MemoryObserver) (x : IO (Except String α)) (t : Traced α) : Prop :=
  x = replay observer t.1 >>= fun _ => pure t.2

private theorem io_pure_bind {α β : Type} (x : α) (f : α → IO β) : (pure x >>= f) = f x := rfl

private theorem io_bind_assoc {α β γ : Type} (x : IO α) (f : α → IO β) (g : β → IO γ) :
    ((x >>= f) >>= g) = x >>= fun a => f a >>= g := by
  funext world
  show EST.bind (EST.bind x f) g world = EST.bind x (fun a => EST.bind (f a) g) world
  simp only [EST.bind]
  cases x world <;> rfl

private theorem io_bind_pure {α : Type} (x : IO α) : (x >>= fun a => pure a) = x := by
  funext world
  show EST.bind x (fun a => EST.pure a) world = x world
  simp only [EST.bind, EST.pure]
  cases x world <;> rfl

private theorem replay_nil (observer : MemoryObserver) : replay observer [] = pure () := rfl

private theorem replay_cons (observer : MemoryObserver) (head : Access) (tail : List Access) :
    replay observer (head :: tail) =
      observer head.write head.address head.size head.value >>= fun _ => replay observer tail := rfl

private theorem replay_append (observer : MemoryObserver) (a b : List Access) :
    replay observer (a ++ b) = replay observer a >>= fun _ => replay observer b := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    rw [List.cons_append, replay_cons, ih, replay_cons, io_bind_assoc]

theorem Obs.pure {α : Type} (observer : MemoryObserver) (r : Except String α) :
    Obs observer (Pure.pure r) (Traced.ofExcept r) := rfl

theorem Obs.bind {α β : Type} {observer : MemoryObserver} {x : IO (Except String α)} {t : Traced α}
    {K : Except String α → IO (Except String β)} {f : α → Traced β} (hx : Obs observer x t)
    (he : ∀ error, K (.error error) = Pure.pure (.error error)) (hk : ∀ v, Obs observer (K (.ok v)) (f v)) :
    Obs observer (x >>= K) (t.bind f) := by
  simp only [Obs] at hx hk ⊢
  rw [hx, io_bind_assoc]
  simp only [io_pure_bind, Traced.bind]
  cases t.2 with
  | error e => simp only [he]
  | ok v =>
    simp only [hk v, replay_append, io_bind_assoc]

/-- `value` as a memory, as both evaluators see it. -/
def memoryOf : Value → Except String (Σ width, Memory width)
  | .memory value => .ok ⟨_, value⟩
  | _ => .error "expected memory"

/-- The accesses of an expression, and its value. -/
def traceExp (env : Env) : Exp → Traced Value
  | .int value => Traced.ofExcept (.ok (.bits value))
  | .var var => Traced.ofExcept (lookup env var)
  | .load memory address endian size =>
    (traceExp env memory).bind fun memory =>
    (Traced.ofExcept (memoryOf memory)).bind fun ⟨addressWidth, memory⟩ =>
    (traceExp env address).bind fun address =>
    (Traced.ofExcept (Value.asBits address)).bind fun ⟨actualWidth, address⟩ =>
      if h : actualWidth = addressWidth then
        let address : BitVec addressWidth := h ▸ address
        ([⟨false, address.toNat, size, 0⟩], .ok (.bits (Memory.read memory address endian size)))
      else
        ([], .error "address width does not match memory")
  | .store memory address value endian size =>
    (traceExp env memory).bind fun memory =>
    (Traced.ofExcept (memoryOf memory)).bind fun ⟨addressWidth, memory⟩ =>
    (traceExp env address).bind fun address =>
    (Traced.ofExcept (Value.asBits address)).bind fun ⟨actualWidth, address⟩ =>
    (traceExp env value).bind fun value =>
    (Traced.ofExcept (Value.asBits value)).bind fun stored =>
      if h : actualWidth = addressWidth then
        let address : BitVec addressWidth := h ▸ address
        ([⟨true, address.toNat, size, stored.2.toNat⟩], Memory.write memory address stored.2 endian size |>.map Value.memory)
      else
        ([], .error "address width does not match memory")
  | .bin op left right =>
    (traceExp env left).bind fun left =>
    (Traced.ofExcept (Value.asBits left)).bind fun left =>
    (traceExp env right).bind fun right =>
    (Traced.ofExcept (Value.asBits right)).bind fun right =>
      Traced.ofExcept (evalBin op left right)
  | .un op value =>
    (traceExp env value).bind fun value =>
      Traced.ofExcept (Value.asBits value |>.map fun value =>
        match op with
        | .neg => .bits (-value.2)
        | .not => .bits (~~~value.2))
  | .cast kind width value =>
    (traceExp env value).bind fun value =>
      Traced.ofExcept (Value.asBits value >>= fun value =>
        match kind with
        | .low => .ok (.bits (Word.low width value.2))
        | .unsigned => .ok (.bits (Word.unsigned width value.2))
        | .signed => .ok (.bits (Word.signed width value.2))
        | .high => Word.high width value.2 |>.map Value.bits)
  | .letIn var value body =>
    (traceExp env value).bind fun value => traceExp (bind env var value) body
  | .ite condition yes no =>
    (traceExp env condition).bind fun condition =>
    (Traced.ofExcept (Value.asBits condition)).bind fun ⟨width, condition⟩ =>
      if h : width = 1 then
        let condition : BitVec 1 := h ▸ condition
        if condition = 1 then traceExp env yes else traceExp env no
      else
        ([], .error "condition must be one bit")
  | .extract high low value =>
    (traceExp env value).bind fun value =>
      Traced.ofExcept (Value.asBits value >>= fun value =>
        Word.extract high low value.2 |>.map Value.bits)
  | .concat left right =>
    (traceExp env left).bind fun left =>
    (Traced.ofExcept (Value.asBits left)).bind fun left =>
    (traceExp env right).bind fun right =>
      Traced.ofExcept (Value.asBits right >>= fun right => .ok (.bits (Word.concat left.2 right.2)))
  | .unknown message _ => Traced.ofExcept (.error s!"cannot evaluate unknown value: {message}")

section Observed

open_private Bap.Bil.Observe Bap.Bil expectMemory notify

private theorem expect_eq : expectMemory = memoryOf := by
  funext value
  cases value <;> rfl

private theorem notify_some (observer : MemoryObserver) (write : Bool) (address size value : Nat)
    {α : Type} (r : Except String α) :
    Obs observer (notify (some observer) write address size value >>= fun _ => Pure.pure r)
      ([⟨write, address, size, value⟩], r) := by
  show _ = _
  simp only [notify]
  rw [replay_cons, replay_nil, io_bind_assoc]
  rfl

/-- The evaluator calls the observer for the accesses of `traceExp`, and returns its value. -/
theorem evalExpObserved_obs (observer : MemoryObserver) (env : Env) (exp : Exp) :
    Obs observer (evalExpObserved (some observer) env exp) (traceExp env exp) := by
  induction exp generalizing env with
  | int value => rw [evalExpObserved]; exact Obs.pure observer _
  | var var => rw [evalExpObserved]; exact Obs.pure observer _
  | unknown message typ => rw [evalExpObserved]; exact Obs.pure observer _
  | bin op left right ihl ihr =>
    rw [evalExpObserved]
    simp only [traceExp]
    refine Obs.bind (ihl env) (fun _ => rfl) fun lv => ?_
    cases lv with
    | memory m => exact rfl
    | undefined => exact rfl
    | @bits w l =>
      refine Obs.bind (ihr env) (fun _ => rfl) fun rv => ?_
      cases rv with
      | memory m => exact rfl
      | undefined => exact rfl
      | bits r => exact rfl
  | un op value ih =>
    rw [evalExpObserved]
    simp only [traceExp]
    exact Obs.bind (ih env) (fun _ => rfl) fun v => rfl
  | cast kind width value ih =>
    rw [evalExpObserved]
    simp only [traceExp]
    exact Obs.bind (ih env) (fun _ => rfl) fun v => rfl
  | extract high low value ih =>
    rw [evalExpObserved]
    simp only [traceExp]
    exact Obs.bind (ih env) (fun _ => rfl) fun v => rfl
  | concat left right ihl ihr =>
    rw [evalExpObserved]
    simp only [traceExp]
    refine Obs.bind (ihl env) (fun _ => rfl) fun lv => ?_
    cases lv with
    | memory m => exact rfl
    | undefined => exact rfl
    | @bits w l => exact Obs.bind (ihr env) (fun _ => rfl) fun rv => rfl
  | letIn var value body ihv ihb =>
    rw [evalExpObserved]
    simp only [traceExp]
    exact Obs.bind (ihv env) (fun _ => rfl) fun v => ihb (bind env var v)
  | ite condition yes no ihc ihy ihn =>
    rw [evalExpObserved]
    simp only [traceExp]
    refine Obs.bind (ihc env) (fun _ => rfl) fun c => ?_
    cases c with
    | memory m => exact rfl
    | undefined => exact rfl
    | @bits w b =>
      by_cases hw : w = 1
      · subst hw
        by_cases hb : b = 1
        · simp only [Value.asBits, ↓reduceDIte, hb, ↓reduceIte, Traced.ofExcept, Traced.bind, List.nil_append]
          exact ihy env
        · simp only [Value.asBits, ↓reduceDIte, hb, ↓reduceIte, Traced.ofExcept, Traced.bind, List.nil_append]
          exact ihn env
      · simp only [Value.asBits, hw, ↓reduceDIte, Traced.ofExcept, Traced.bind, List.nil_append]
        rfl
  | load memory address endian size ihm iha =>
    rw [evalExpObserved]
    simp only [traceExp, expect_eq]
    refine Obs.bind (ihm env) (fun _ => rfl) fun mv => ?_
    cases mv with
    | bits b => exact rfl
    | undefined => exact rfl
    | @memory w m =>
      refine Obs.bind (iha env) (fun _ => rfl) fun av => ?_
      cases av with
      | memory m => exact rfl
      | undefined => exact rfl
      | @bits aw a =>
        by_cases hw : aw = w
        · subst hw
          simp only [Value.asBits, ↓reduceDIte, Traced.ofExcept, Traced.bind, List.nil_append, memoryOf]
          exact notify_some observer false a.toNat size 0 _
        · simp only [Value.asBits, hw, ↓reduceDIte, Traced.ofExcept, Traced.bind, List.nil_append, memoryOf]
          rfl
  | store memory address value endian size ihm iha ihv =>
    rw [evalExpObserved]
    simp only [traceExp, expect_eq]
    refine Obs.bind (ihm env) (fun _ => rfl) fun mv => ?_
    cases mv with
    | bits b => exact rfl
    | undefined => exact rfl
    | @memory w m =>
      refine Obs.bind (iha env) (fun _ => rfl) fun av => ?_
      cases av with
      | memory m => exact rfl
      | undefined => exact rfl
      | @bits aw a =>
        refine Obs.bind (ihv env) (fun _ => rfl) fun vv => ?_
        cases vv with
        | memory m => exact rfl
        | undefined => exact rfl
        | @bits vw v =>
          by_cases hw : aw = w
          · subst hw
            simp only [Value.asBits, ↓reduceDIte, Traced.ofExcept, Traced.bind, List.nil_append, memoryOf]
            exact notify_some observer true a.toNat size v.toNat _
          · simp only [Value.asBits, hw, ↓reduceDIte, Traced.ofExcept, Traced.bind, List.nil_append, memoryOf]
            rfl

end Observed

/-! Statements. -/

mutual
  /-- The accesses of a statement, and its outcome. -/
  def traceStmt (fuel : Nat) (state : State) (stmt : Stmt) : Traced (State × Effect) :=
    match fuel with
    | 0 => Traced.ofExcept (.error "execution fuel exhausted")
    | fuel + 1 =>
      match stmt with
      | .move var value =>
        (traceExp state.env value).bind fun value => Traced.ofExcept (.ok ({ env := bind state.env var value }, .normal))
      | .jmp target =>
        (traceExp state.env target).bind fun target =>
          Traced.ofExcept (Value.asBits target |>.map fun target => (state, .jump target.2))
      | .special message => Traced.ofExcept (.ok (state, .special message))
      | .cpuExn number => Traced.ofExcept (.ok (state, .cpuExn number))
      | .ifElse condition yes no =>
        (traceExp state.env condition).bind fun condition =>
        (Traced.ofExcept (Value.asBits condition)).bind fun ⟨width, condition⟩ =>
          if h : width = 1 then
            let condition : BitVec 1 := h ▸ condition
            traceProgram fuel state (if condition = 1 then yes else no)
          else Traced.ofExcept (.error "condition must be one bit")
      | .while conditionExp body =>
        (traceExp state.env conditionExp).bind fun condition =>
        (Traced.ofExcept (Value.asBits condition)).bind fun ⟨width, conditionValue⟩ =>
          if h : width = 1 then
            let conditionValue : BitVec 1 := h ▸ conditionValue
            if conditionValue = 1 then
              (traceProgram fuel state body).bind fun result =>
                match result with
                | (next, .normal) => traceStmt fuel next (.while conditionExp body)
                | result => Traced.ofExcept (.ok result)
            else Traced.ofExcept (.ok (state, .normal))
          else Traced.ofExcept (.error "condition must be one bit")

  /-- The accesses of a program, and its outcome. -/
  def traceProgram (fuel : Nat) (state : State) (program : Program) : Traced (State × Effect) :=
    match fuel with
    | 0 => Traced.ofExcept (.error "execution fuel exhausted")
    | fuel + 1 =>
      match program with
      | [] => Traced.ofExcept (.ok (state, .normal))
      | stmt :: rest =>
        (traceStmt fuel state stmt).bind fun result =>
          match result with
          | (next, .normal) => traceProgram fuel next rest
          | result => Traced.ofExcept (.ok result)
end

private theorem obs_result {observer : MemoryObserver} {α : Type} (x : IO (Except String α)) (t t' : Traced α)
    (h : Obs observer x t) (he : t = t') : Obs observer x t' := he ▸ h

private theorem exec_obs (observer : MemoryObserver) (fuel : Nat) :
    (∀ state stmt, Obs observer (execStmtObserved (some observer) fuel state stmt) (traceStmt fuel state stmt)) ∧
    (∀ state program, Obs observer (execProgramObserved (some observer) fuel state program)
      (traceProgram fuel state program)) := by
  induction fuel with
  | zero =>
    constructor
    · intro state stmt
      rw [execStmtObserved]
      simp only [traceStmt]
      exact rfl
    · intro state program
      rw [execProgramObserved]
      simp only [traceProgram]
      exact rfl
  | succ fuel ih =>
    obtain ⟨ihs, ihp⟩ := ih
    constructor
    · intro state stmt
      rw [execStmtObserved.eq_def]
      simp only [traceStmt]
      cases stmt with
      | move var value => exact Obs.bind (evalExpObserved_obs observer _ _) (fun _ => rfl) fun v => rfl
      | jmp target => exact Obs.bind (evalExpObserved_obs observer _ _) (fun _ => rfl) fun v => rfl
      | special message => exact rfl
      | cpuExn number => exact rfl
      | ifElse condition yes no =>
        refine Obs.bind (evalExpObserved_obs observer _ _) (fun _ => rfl) fun c => ?_
        cases c with
        | memory m => exact rfl
        | undefined => exact rfl
        | @bits w b =>
          by_cases hw : w = 1
          · subst hw
            simp only [Value.asBits, ↓reduceDIte, Traced.ofExcept, Traced.bind, List.nil_append]
            exact ihp _ _
          · simp only [Value.asBits, hw, ↓reduceDIte, Traced.ofExcept, Traced.bind, List.nil_append]
            exact rfl
      | «while» condition body =>
        refine Obs.bind (evalExpObserved_obs observer _ _) (fun _ => rfl) fun c => ?_
        cases c with
        | memory m => exact rfl
        | undefined => exact rfl
        | @bits w b =>
          by_cases hw : w = 1
          · subst hw
            simp only [Value.asBits, ↓reduceDIte, Traced.ofExcept, Traced.bind, List.nil_append]
            by_cases hb : b = 1
            · simp only [hb, ↓reduceIte]
              refine Obs.bind (ihp _ _) (fun _ => rfl) fun result => ?_
              obtain ⟨next, effect⟩ := result
              cases effect with
              | normal => exact ihs _ _
              | jump target => exact rfl
              | special message => exact rfl
              | cpuExn number => exact rfl
            · simp only [hb, ↓reduceIte]
              exact rfl
          · simp only [Value.asBits, hw, ↓reduceDIte, Traced.ofExcept, Traced.bind, List.nil_append]
            exact rfl
    · intro state program
      rw [execProgramObserved.eq_def]
      simp only [traceProgram]
      cases program with
      | nil => exact rfl
      | cons stmt rest =>
        refine Obs.bind (ihs _ _) (fun _ => rfl) fun result => ?_
        obtain ⟨next, effect⟩ := result
        cases effect with
        | normal => exact ihp _ _
        | jump target => exact rfl
        | special message => exact rfl
        | cpuExn number => exact rfl

/-- The interpreter calls any observer for the accesses of `traceProgram`, one call each, in order, before
it returns; and if the observer throws, as the permission check of an emulator does, it stops there. -/
theorem runObserved_trace (observer : MemoryObserver) (program : Program) (state : State) (fuel : Nat) :
    runObserved (some observer) program state fuel =
      replay observer (traceProgram fuel state program).1 >>= fun _ => pure (traceProgram fuel state program).2 :=
  (exec_obs observer fuel).2 state program

/-! What the trace returns is what the pure semantics returns. -/

section Pure

open_private Bap.Bil.Eval Bap.Bil expectMemory evalUn

private theorem expect_eq' : expectMemory = memoryOf := by
  funext value
  cases value <;> rfl

private theorem bind_snd {α β : Type} (x : Traced α) (f : α → Traced β) :
    (x.bind f).2 = match x.2 with
      | .error error => .error error
      | .ok value => (f value).2 := by
  simp only [Traced.bind]
  cases x.2 <;> rfl

/-- The value of `traceExp` is the value of the evaluator. -/
theorem traceExp_value (env : Env) (exp : Exp) : (traceExp env exp).2 = evalExp env exp := by
  induction exp generalizing env with
  | int value => rfl
  | var var => rfl
  | unknown message typ => rfl
  | bin op left right ihl ihr =>
    simp only [traceExp, bind_snd, ihl, ihr, evalExp, Traced.ofExcept]
    cases evalExp env left with
    | error e => rfl
    | ok lv =>
      cases lv <;> try rfl
      cases evalExp env right with
      | error e => rfl
      | ok rv => cases rv <;> rfl
  | un op value ih =>
    simp only [traceExp, bind_snd, ih, evalExp, Traced.ofExcept]
    cases evalExp env value with
    | error e => rfl
    | ok v => cases v <;> (try cases op) <;> rfl
  | cast kind width value ih =>
    simp only [traceExp, bind_snd, ih, evalExp, Traced.ofExcept]
    cases evalExp env value with
    | error e => rfl
    | ok v =>
      cases v <;> (try cases kind) <;> try rfl
      all_goals
        simp only [Value.asBits, Bind.bind, Except.bind, Except.map, pure, Except.pure]
        split <;> simp_all
  | extract high low value ih =>
    simp only [traceExp, bind_snd, ih, evalExp, Traced.ofExcept]
    cases evalExp env value with
    | error e => rfl
    | ok v =>
      cases v <;> try rfl
      all_goals
        simp only [Value.asBits, Bind.bind, Except.bind, Except.map, pure, Except.pure]
        split <;> simp_all
  | concat left right ihl ihr =>
    simp only [traceExp, bind_snd, ihl, ihr, evalExp, Traced.ofExcept]
    cases evalExp env left with
    | error e => rfl
    | ok lv =>
      cases lv <;> try rfl
      cases evalExp env right with
      | error e => rfl
      | ok rv => cases rv <;> rfl
  | letIn var value body ihv ihb =>
    simp only [traceExp, bind_snd, ihv, ihb, evalExp]
    cases evalExp env value <;> rfl
  | ite condition yes no ihc ihy ihn =>
    simp only [traceExp, bind_snd, ihc, evalExp, Traced.ofExcept]
    cases evalExp env condition with
    | error e => rfl
    | ok c =>
      cases c with
      | memory m => rfl
      | undefined => rfl
      | @bits w b =>
        by_cases hw : w = 1
        · subst hw
          by_cases hb : b = 1
          · simp only [Value.asBits, ↓reduceDIte, hb, ↓reduceIte, Bind.bind, Except.bind, ihy]
          · simp only [Value.asBits, ↓reduceDIte, hb, ↓reduceIte, Bind.bind, Except.bind, ihn]
        · simp only [Value.asBits, hw, ↓reduceDIte, Bind.bind, Except.bind]
  | load memory address endian size ihm iha =>
    simp only [traceExp, bind_snd, ihm, iha, evalExp, Traced.ofExcept, expect_eq']
    cases evalExp env memory with
    | error e => rfl
    | ok mv =>
      cases mv with
      | bits b => rfl
      | undefined => rfl
      | @memory w m =>
        cases evalExp env address with
        | error e => rfl
        | ok av =>
          cases av with
          | memory m => rfl
          | undefined => rfl
          | @bits aw a =>
            by_cases hw : aw = w
            · subst hw
              simp only [memoryOf, Value.asBits, ↓reduceDIte, Bind.bind, Except.bind]
            · simp only [memoryOf, Value.asBits, hw, ↓reduceDIte, Bind.bind, Except.bind]
  | store memory address value endian size ihm iha ihv =>
    simp only [traceExp, bind_snd, ihm, iha, ihv, evalExp, Traced.ofExcept, expect_eq']
    cases evalExp env memory with
    | error e => rfl
    | ok mv =>
      cases mv with
      | bits b => rfl
      | undefined => rfl
      | @memory w m =>
        cases evalExp env address with
        | error e => rfl
        | ok av =>
          cases av with
          | memory m => rfl
          | undefined => rfl
          | @bits aw a =>
            cases evalExp env value with
            | error e => rfl
            | ok vv =>
              cases vv with
              | memory m => rfl
              | undefined => rfl
              | @bits vw v =>
                by_cases hw : aw = w
                · subst hw
                  simp only [memoryOf, Value.asBits, ↓reduceDIte, Bind.bind, Except.bind, Except.map]
                · simp only [memoryOf, Value.asBits, hw, ↓reduceDIte, Bind.bind, Except.bind]

private theorem exec_value (fuel : Nat) :
    (∀ state stmt, (traceStmt fuel state stmt).2 = execStmt fuel state stmt) ∧
    (∀ state program, (traceProgram fuel state program).2 = execProgram fuel state program) := by
  induction fuel with
  | zero =>
    constructor
    · intro state stmt
      simp only [traceStmt, execStmt]
      rfl
    · intro state program
      simp only [traceProgram, execProgram]
      rfl
  | succ fuel ih =>
    obtain ⟨ihs, ihp⟩ := ih
    constructor
    · intro state stmt
      cases stmt with
      | move var value =>
        simp only [traceStmt, execStmt, execExp, bind_snd, traceExp_value, Traced.ofExcept]
        cases evalExp state.env value <;> rfl
      | jmp target =>
        simp only [traceStmt, execStmt, execExp, bind_snd, traceExp_value, Traced.ofExcept]
        cases evalExp state.env target with
        | error e => rfl
        | ok v => cases v <;> rfl
      | special message => rfl
      | cpuExn number => rfl
      | ifElse condition yes no =>
        simp only [traceStmt, execStmt, execExp, bind_snd, traceExp_value, Traced.ofExcept]
        cases evalExp state.env condition with
        | error e => rfl
        | ok c =>
          cases c with
          | memory m => rfl
          | undefined => rfl
          | @bits w b =>
            by_cases hw : w = 1
            · subst hw
              simp only [Value.asBits, ↓reduceDIte, Bind.bind, Except.bind, ihp]
            · simp only [Value.asBits, hw, ↓reduceDIte, Bind.bind, Except.bind]
      | «while» condition body =>
        simp only [traceStmt, execStmt, execExp, bind_snd, traceExp_value, Traced.ofExcept]
        cases evalExp state.env condition with
        | error e => rfl
        | ok c =>
          cases c with
          | memory m => rfl
          | undefined => rfl
          | @bits w b =>
            by_cases hw : w = 1
            · subst hw
              by_cases hb : b = 1
              · simp only [Value.asBits, ↓reduceDIte, hb, ↓reduceIte, bind_snd, ihp, Bind.bind, Except.bind]
                cases execProgram fuel state body with
                | error e => rfl
                | ok r =>
                  obtain ⟨next, effect⟩ := r
                  cases effect with
                  | normal => simp only [ihs]
                  | jump target => rfl
                  | special message => rfl
                  | cpuExn number => rfl
              · simp only [Value.asBits, ↓reduceDIte, hb, ↓reduceIte, Bind.bind, Except.bind]
            · simp only [Value.asBits, hw, ↓reduceDIte, Bind.bind, Except.bind]
    · intro state program
      cases program with
      | nil => rfl
      | cons stmt rest =>
        simp only [traceProgram, execProgram, bind_snd, ihs, Bind.bind, Except.bind]
        cases execStmt fuel state stmt with
        | error e => rfl
        | ok r =>
          obtain ⟨next, effect⟩ := r
          cases effect with
          | normal => simp only [ihp]
          | jump target => rfl
          | special message => rfl
          | cpuExn number => rfl

/-- The trace returns what `Bil.run` returns. -/
theorem traceProgram_value (fuel : Nat) (state : State) (program : Program) :
    (traceProgram fuel state program).2 = run program state fuel :=
  (exec_value fuel).2 state program

/-- So an interpreted block with any observer returns what `Bil.run` returns, once the observer has seen
the accesses of the trace. This is how the emulator's memory hooks, permission checks and trace see an
interpreted instruction: exactly once per access, with its address, size and value, before its effect, as
the result only then goes on to be bound in the state. -/
theorem runObserved_eq (observer : MemoryObserver) (program : Program) (state : State) (fuel : Nat) :
    runObserved (some observer) program state fuel =
      replay observer (traceProgram fuel state program).1 >>= fun _ => pure (run program state fuel) := by
  rw [runObserved_trace, traceProgram_value]

end Pure

end Bap.Emu.Observe
