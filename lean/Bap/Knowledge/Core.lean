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
  | .bool => Bool
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

structure Promise where
  slot : Σ kind, Slot kind
  compute : Object → List Fact → Except Conflict (Option slot.1.data)

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

def stringDomain : Domain String where
  empty := ""
  eq := (· == ·)
  join left right := if left.isEmpty then some right else if right.isEmpty || left = right then some left else none

def boolDomain : Domain Bool where
  empty := false
  eq := (· == ·)
  join left right := some (left || right)

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

def provideWith (env : Environment) (slot : Slot kind) (object : Object) (value : kind.data)
    (state : State) : Except Conflict State := do
  let next ← provide slot object value state
  if next.version != state.version then
    notifyObservers env slot object next
  .ok next

private def putOpinion (opinion : Opinion) (opinions : List Opinion) : List Opinion :=
  opinion :: opinions.filter fun old =>
    old.agent.name != opinion.agent.name ||
    old.fact.object != opinion.fact.object ||
    old.fact.slot.2.name != opinion.fact.slot.2.name

def suggest (agent : Agent) (slot : Slot kind) (object : Object) (value : kind.data) (state : State) :
    State :=
  let opinion : Opinion := ⟨agent, object, ⟨kind, slot⟩, value⟩
  { state with opinions := putOpinion opinion state.opinions, version := state.version + 1 }

private def joinOpinions (slot : Slot kind) (current : kind.data) : List Opinion →
    Except Conflict kind.data
  | [] => .ok current
  | opinion :: rest =>
    if h : opinion.fact.slot.1 = kind then
      match slot.domain.join current (h ▸ opinion.fact.value) with
      | some joined => joinOpinions slot joined rest
      | none => .error (.incompatible slot.name)
    else
      .error (.typeMismatch slot.name)

def resolve (slot : Slot kind) (object : Object) (state : State) : Except Conflict kind.data := do
  let relevant := state.opinions.filter fun opinion =>
    opinion.fact.object = object ∧ opinion.fact.slot.2.name = slot.name
  if relevant.isEmpty then
    .ok slot.domain.empty
  else
    let trust := relevant.foldl (fun trust opinion => max trust opinion.agent.trust) 0
    let selected := relevant.filter fun opinion => opinion.agent.trust = trust
    joinOpinions slot slot.domain.empty selected

@[simp] theorem resolve_empty (slot : Slot kind) (object : Object) :
    resolve slot object {} = .ok slot.domain.empty := by
  rfl

private def runPromises (promises : List Promise) (object : Object) (facts : List Fact) :
    Except Conflict (Bool × List Fact) := do
  let mut changed := false
  let mut current := facts
  for promise in promises do
    let value ← promise.compute object current
    if let some value := value then
      let (refined, next) ← provideInFacts promise.slot.2 object value current
      changed := changed || refined
      current := next
  .ok (changed, current)

private def normalize (env : Environment) (object : Object) : Nat → List Fact →
    Except Conflict (Bool × List Fact)
  | 0, _ => .error .exhausted
  | fuel + 1, facts => do
    let (changed, facts) ← runPromises env.promises object facts
    if changed then do
      let (_, facts) ← normalize env object fuel facts
      .ok (true, facts)
    else
      .ok (false, facts)

def collect (env : Environment) (slot : Slot kind) (object : Object) (state : State) (fuel : Nat := 1000) :
    Except Conflict (kind.data × State) := do
  let (changed, facts) ← normalize env object fuel state.facts
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

def promise (slot : Slot kind)
    (compute : Object → List Fact → Except Conflict (Option kind.data)) : Promise :=
  ⟨⟨kind, slot⟩, compute⟩

@[simp] theorem maxDomain_join (left right : Nat) :
    maxDomain.join left right = some (max left right) := by
  rfl

@[simp] theorem stringDomain_empty_left (value : String) :
    stringDomain.join "" value = some value := by
  simp [stringDomain]

end Bap.Knowledge
