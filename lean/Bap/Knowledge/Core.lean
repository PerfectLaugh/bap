import Bap.Theory.Target
import Bap.IR.Cfg

namespace Bap.Knowledge

inductive PayloadKind where
  | unit
  | bool
  | nat
  | string
  | bitvec (width : Nat)
  | var
  | vars
  | target
  | exp
  | program
  | cfg
  deriving DecidableEq, Repr

abbrev PayloadKind.data : PayloadKind → Type
  | .unit => Unit
  | .bool => Option Bool
  | .nat => Nat
  | .string => String
  | .bitvec width => BitVec width
  | .var => Theory.Var
  | .vars => List Theory.Var
  | .target => Theory.Target
  | .exp => Bil.Exp
  | .program => Bil.Program
  | .cfg => IR.Cfg

structure Domain (α : Type) where
  empty : α
  eq : α → α → Bool
  join : α → α → Option α

structure Slot (kind : PayloadKind) where
  name : String
  domain : Domain kind.data

structure Object where
  cls : String
  name : String
  id : Nat
  deriving DecidableEq, Repr

structure Fact where
  object : Object
  slot : Σ kind, Slot kind
  value : slot.1.data

structure Agent where
  name : String
  trust : Nat
  deriving DecidableEq, Repr

structure Opinion where
  agent : Agent
  fact : Fact

inductive Conflict where
  | incompatible (slot : String)
  | typeMismatch (slot : String)
  | empty (slot : String)
  | exhausted
  | failed (message : String)
  deriving Repr

structure State where
  facts : List Fact := []
  opinions : List Opinion := []
  version : Nat := 0

/-- A rule that computes a slot from the table. `compute` is a pure function of the facts, so unlike
upstream's promises it cannot call `collect`; instead `deps` names the slots whose promises must run
first, what upstream's body would `collect`. Reading any other slot is upstream's `current`: it sees
what is already known and runs nothing. -/
structure Promise where
  slot : Σ kind, Slot kind
  compute : Object → List Fact → Except Conflict (Option slot.1.data)
  deps : List String := []

structure Observer where
  slot : Σ kind, Slot kind
  notify : Object → List Fact → Except Conflict Unit

structure Environment where
  promises : List Promise := []
  observers : List Observer := []

def maxDomain : Domain Nat where
  empty := 0
  eq := (· == ·)
  join left right := some (max left right)

/-- Flat with the empty string at the bottom, as upstream documents `Domain.string`: two different
names are a conflict. Upstream's code differs from its documentation: there the empty string is
above everything and other strings are ordered lexicographically, so `""` would absorb any value and
a name would silently replace another. -/
def stringDomain : Domain String where
  empty := ""
  eq := (· == ·)
  join left right := if left.isEmpty then some right else if right.isEmpty || left = right then some left else none

def unitDomain : Domain Unit where
  empty := ()
  eq _ _ := true
  join _ _ := some ()

def optionDomain [DecidableEq α] : Domain (Option α) where
  empty := none
  eq := (· == ·)
  join
    | none, value | value, none => some value
    | some left, some right => if left = right then some (some left) else none

/-- The tribool, as upstream's `Domain.bool`: `none` is unknown, and `some false` is knowledge that
contradicts `some true`. -/
def boolDomain : Domain (Option Bool) := optionDomain

def exactDomain [DecidableEq α] (empty : α) : Domain α where
  empty := empty
  eq := (· == ·)
  join left right := if left = empty then some right else if right = empty || left = right then some left else none

def lookupFact (slot : Slot kind) (object : Object) (facts : List Fact) :
    Except Conflict (Option kind.data) :=
  match facts.find? fun fact => fact.object = object ∧ fact.slot.2.name = slot.name with
  | none => .ok none
  | some fact =>
    if h : fact.slot.1 = kind then
      .ok (some (h ▸ fact.value))
    else
      .error (.typeMismatch slot.name)

private def putFact (fact : Fact) (facts : List Fact) : List Fact :=
  fact :: facts.filter fun old => old.object != fact.object || old.slot.2.name != fact.slot.2.name

def provideInFacts (slot : Slot kind) (object : Object) (value : kind.data) (facts : List Fact) :
    Except Conflict (Bool × List Fact) := do
  if slot.domain.eq value slot.domain.empty then
    return (false, facts)
  match ← lookupFact slot object facts with
  | none => .ok (true, putFact ⟨object, ⟨kind, slot⟩, value⟩ facts)
  | some existing =>
    match slot.domain.join existing value with
    | none => .error (.incompatible slot.name)
    | some joined =>
      if slot.domain.eq existing joined then
        .ok (false, facts)
      else
        .ok (true, putFact ⟨object, ⟨kind, slot⟩, joined⟩ facts)

def provide (slot : Slot kind) (object : Object) (value : kind.data) (state : State) :
    Except Conflict State := do
  let (changed, facts) ← provideInFacts slot object value state.facts
  .ok { state with facts := facts, version := state.version + changed.toNat }

def observe (slot : Slot kind) (notify : Object → List Fact → Except Conflict Unit) : Observer :=
  ⟨⟨kind, slot⟩, notify⟩

def notifyObservers (env : Environment) (slot : Slot kind) (object : Object) (state : State) :
    Except Conflict Unit := do
  for observer in env.observers do
    if observer.slot.2.name = slot.name then
      observer.notify object state.facts

/-- Provides a value and tells the slot's observers, if that refined the cell. Upstream documents
`observe` the same way ("calls `push` when the property changes"), although its `provide` calls them
on every non-empty value. An observer here is a pure function of the table, so telling it about a
table that did not change could only repeat an answer, and would make `provide` non-idempotent. -/
def provideWith (env : Environment) (slot : Slot kind) (object : Object) (value : kind.data)
    (state : State) : Except Conflict State := do
  let next ← provide slot object value state
  if next.version != state.version then
    notifyObservers env slot object next
  .ok next

/-- Whether an opinion already records this agent's vote for this value. -/
private def isVote (agent : Agent) (slot : Slot kind) (object : Object) (value : kind.data) (old : Opinion) :
    Bool :=
  decide (old.agent.name = agent.name ∧ old.fact.object = object ∧ old.fact.slot.2.name = slot.name) &&
    if h : old.fact.slot.1 = kind then slot.domain.eq (h ▸ old.fact.value) value else false

/-- Adds the agent's vote. An agent may vote for several values, as upstream's `Opinions.add`, and an
empty opinion or a repeated vote changes nothing. -/
def suggest (agent : Agent) (slot : Slot kind) (object : Object) (value : kind.data) (state : State) :
    State :=
  if slot.domain.eq value slot.domain.empty || state.opinions.any (isVote agent slot object value) then
    state
  else
    { state with
      opinions := ⟨agent, object, ⟨kind, slot⟩, value⟩ :: state.opinions
      version := state.version + 1 }

/-- The distinct agents voting for a value. -/
private def voters (slot : Slot kind) (votes : List (Agent × kind.data)) (value : kind.data) : List Agent :=
  ((votes.filter fun vote => slot.domain.eq vote.2 value).map Prod.fst).eraseDups

/-- The weight of a set of votes is the sum of the voters' trust. -/
private def weight (agents : List Agent) : Nat :=
  (agents.map Agent.trust).sum

/-- More weight wins. Equal weights fall back on the voters' names, a total choice like upstream's
comparison of vote sets, which orders agents by the digest of their names. -/
private def outweighs (left right : List Agent) : Bool :=
  let names (agents : List Agent) := (agents.map Agent.name).mergeSort
  weight left > weight right || (weight left = weight right && names left > names right)

private def chooseVote (slot : Slot kind) (votes : List (Agent × kind.data)) (best : kind.data)
    (rest : List (Agent × kind.data)) : kind.data :=
  rest.foldl (fun best vote =>
    if outweighs (voters slot votes vote.2) (voters slot votes best) then vote.2 else best) best

/-- The value whose voters weigh the most, as upstream's `Opinions.choice`. It never conflicts: a
disagreement is settled by the vote. -/
def resolve (slot : Slot kind) (object : Object) (state : State) : Except Conflict kind.data := do
  let relevant := state.opinions.filter fun opinion =>
    opinion.fact.object = object ∧ opinion.fact.slot.2.name = slot.name
  let votes ← relevant.mapM fun opinion =>
    if h : opinion.fact.slot.1 = kind then
      .ok (opinion.agent, h ▸ opinion.fact.value)
    else
      .error (.typeMismatch slot.name)
  match votes with
  | [] => .ok slot.domain.empty
  | vote :: rest => .ok (chooseVote slot (vote :: rest) vote.2 rest)

@[simp] theorem resolve_empty (slot : Slot kind) (object : Object) :
    resolve slot object {} = .ok slot.domain.empty := by
  rfl

/-- A promise's value. A failed `require` inside a promise means the promise has nothing to say. -/
private def promiseValue (promise : Promise) (object : Object) (facts : List Fact) :
    Except Conflict (Option promise.slot.1.data) :=
  match promise.compute object facts with
  | .error (.empty _) => .ok none
  | result => result

/-- Provides a promised value, notifying the slot's observers when that refines it. -/
private def providePromised (env : Environment) (slot : Slot kind) (object : Object) (value : kind.data)
    (facts : List Fact) : Except Conflict (Bool × List Fact) := do
  let (refined, next) ← provideInFacts slot object value facts
  if refined then
    notifyObservers env slot object { facts := next }
  .ok (refined, next)

private def runPromises (env : Environment) (object : Object) (facts : List Fact) :
    Except Conflict (Bool × List Fact) := do
  let mut changed := false
  let mut current := facts
  for promise in env.promises do
    let value ← promiseValue promise object current
    if let some value := value then
      let (refined, next) ← providePromised env promise.slot.2 object value current
      changed := changed || refined
      current := next
  .ok (changed, current)

private def normalize (env : Environment) (object : Object) : Nat → List Fact →
    Except Conflict (Bool × List Fact)
  | 0, _ => .error .exhausted
  | fuel + 1, facts => do
    let (changed, facts) ← runPromises env object facts
    if changed then do
      let (_, facts) ← normalize env object fuel facts
      .ok (true, facts)
    else
      .ok (false, facts)

private theorem length_filter_not_lt (test : α → Bool) (values : List α) (h : values.filter test ≠ []) :
    (values.filter fun value => !test value).length < values.length := by
  induction values with
  | nil => simp at h
  | cons head tail ih =>
    by_cases hhead : test head = true
    · have := List.length_filter_le (fun value => !test value) tail
      simp only [List.filter_cons, hhead, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · have hne : tail.filter test ≠ [] := by simpa [List.filter_cons, hhead] using h
      have := ih hne
      have hfalse : test head = false := by simpa using hhead
      simp only [List.filter_cons, hfalse, Bool.not_false, ↓reduceIte, List.length_cons]
      omega

set_option wf.preprocess false in
/-- The slot names that `names` depend on, through the `deps` of `pending`. Each promise is looked at
once, so this terminates on cyclic dependencies. -/
def demanded (pending : List Promise) (names : List String) : List String :=
  if _h : pending.filter (fun promise => names.contains promise.slot.2.name) = [] then
    names
  else
    demanded (pending.filter fun promise => !names.contains promise.slot.2.name)
      (names ++ (pending.filter fun promise => names.contains promise.slot.2.name).flatMap Promise.deps)
termination_by pending.length
decreasing_by exact length_filter_not_lt _ _ _h

/-- The environment of a collect of the named slot: the promises of that slot and of what it
transitively depends on, in their order. As upstream, the others do not run, so their conflicts,
failures and divergence are none of this slot's business. -/
def Environment.demanding (env : Environment) (name : String) : Environment :=
  let names := demanded env.promises [name]
  { env with promises := env.promises.filter fun promise => names.contains promise.slot.2.name }

/-- The slot's value at the least fixpoint of its promises and their dependencies. -/
def collect (env : Environment) (slot : Slot kind) (object : Object) (state : State) (fuel : Nat := 1000) :
    Except Conflict (kind.data × State) := do
  let (changed, facts) ← normalize (env.demanding slot.name) object fuel state.facts
  let value ← lookupFact slot object facts
  .ok (value.getD slot.domain.empty,
    { state with facts := facts, version := state.version + changed.toNat })

def require (env : Environment) (slot : Slot kind) (object : Object) (state : State) (fuel : Nat := 1000) :
    Except Conflict (kind.data × State) := do
  let (value, state) ← collect env slot object state fuel
  if slot.domain.eq value slot.domain.empty then
    .error (.empty slot.name)
  else
    .ok (value, state)

def objects (state : State) : List Object := (state.facts.map Fact.object).eraseDups

def promise (slot : Slot kind) (compute : Object → List Fact → Except Conflict (Option kind.data))
    (deps : List String := []) : Promise :=
  ⟨⟨kind, slot⟩, compute, deps⟩

@[simp] theorem maxDomain_join (left right : Nat) :
    maxDomain.join left right = some (max left right) := by
  rfl

@[simp] theorem stringDomain_empty_left (value : String) :
    stringDomain.join "" value = some value := by
  simp [stringDomain]

end Bap.Knowledge
