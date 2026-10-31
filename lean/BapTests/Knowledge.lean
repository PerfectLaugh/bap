import BapTests.Support

namespace Bap.Tests.Knowledge

open Bap
open Bap.Knowledge

private def natSlot (name : String) : Slot .nat := ⟨name, maxDomain⟩
private def stringSlot (name : String) : Slot .string := ⟨name, stringDomain⟩
private def address := natSlot "address"
private def answer := natSlot "answer"
private def object : Object := ⟨"program", "main", 1⟩

private def provideOrFail (slot : Slot kind) (value : kind.data) (state : State) : IO State :=
  match provide slot object value state with
  | .ok state => pure state
  | .error error => throw <| IO.userError s!"provide failed: {repr error}"

private def computedAnswer : Promise := promise answer fun obj facts => do
  let value ← lookupFact address obj facts
  .ok (some (value.getD 0 + 1))

def run : IO Unit := do
  let state ← provideOrFail address 10 {}
  let state ← provideOrFail address 5 state
  match lookupFact address object state.facts with
  | .ok value => assertEqual "monotonic join retains maximum" (some 10) value
  | .error error => throw <| IO.userError s!"lookup failed: {repr error}"
  assertEqual "unchanged provide is idempotent" 1 state.version
  let state ← provideOrFail address 20 state
  assertEqual "refinement increments version" 2 state.version
  match collect {} address object state with
  | .ok (value, next) =>
    assertEqual "collect reads provided fact" 20 value
    assertEqual "stable collect preserves version" state.version next.version
  | .error error => throw <| IO.userError s!"collect failed: {repr error}"
  assertEqual "empty provide is a no-op" state.version (← provideOrFail address 0 state).version
  assertEqual "empty provide stores no fact" 1 (← provideOrFail (natSlot "fresh") 0 state).facts.length
  let rejecting : Promise := promise answer fun _ _ => .error (.empty "dependency")
  match collect { promises := [rejecting, computedAnswer] } answer object state with
  | .ok (value, _) => assertEqual "failed require leaves other promises running" 21 value
  | .error error => throw <| IO.userError s!"empty promise was fatal: {repr error}"
  let failing : Promise := promise answer fun _ _ => .error (.failed "boom")
  match collect { promises := [failing] } answer object state with
  | .error (.failed "boom") => IO.println "ok: promise failure is fatal"
  | .error error => throw <| IO.userError s!"wrong promise failure: {repr error}"
  | .ok _ => throw <| IO.userError "promise failure was ignored"
  let vetoing : Observer := observe answer fun _ _ => .error (.failed "observed")
  match collect { promises := [computedAnswer], observers := [vetoing] } answer object state with
  | .error (.failed "observed") => IO.println "ok: promised refinement notifies observers"
  | .error error => throw <| IO.userError s!"wrong observer failure: {repr error}"
  | .ok _ => throw <| IO.userError "observer was not notified of a promised value"
  let env : Environment := { promises := [computedAnswer] }
  match collect env answer object state with
  | .ok (value, next) =>
    assertEqual "promise computes dependent property" 21 value
    assertEqual "refining collect increments version" (state.version + 1) next.version
    match collect env answer object next with
    | .ok (again, final) =>
      assertEqual "computed property is stable" value again
      assertEqual "stable promise preserves version" next.version final.version
    | .error error => throw <| IO.userError s!"second collect failed: {repr error}"
  | .error error => throw <| IO.userError s!"promise failed: {repr error}"
  match require {} (natSlot "missing") object state with
  | .error (.empty "missing") => IO.println "ok: require rejects empty property"
  | .error error => throw <| IO.userError s!"wrong require error: {repr error}"
  | .ok _ => throw <| IO.userError "require accepted empty property"
  let named := stringSlot "name"
  let namedState ← provideOrFail named "alpha" {}
  match provide named object "beta" namedState with
  | .error (.incompatible "name") => IO.println "ok: incompatible facts conflict"
  | .error error => throw <| IO.userError s!"wrong conflict: {repr error}"
  | .ok _ => throw <| IO.userError "incompatible facts were accepted"
  match lookupFact (stringSlot "address") object state.facts with
  | .error (.typeMismatch "address") => IO.println "ok: slot kind mismatch rejected"
  | .error error => throw <| IO.userError s!"wrong mismatch error: {repr error}"
  | .ok _ => throw <| IO.userError "slot kind mismatch was accepted"
  let a := natSlot "a"
  let b := natSlot "b"
  let cyclic : Environment := { promises := [
    promise a (deps := [b.name]) fun obj facts => do
      let value ← lookupFact b obj facts
      .ok (some (value.getD 0 + 1)),
    promise b (deps := [a.name]) fun obj facts => do
      let value ← lookupFact a obj facts
      .ok (some (value.getD 0 + 1))
  ] }
  match collect cyclic a object {} 10 with
  | .error .exhausted => IO.println "ok: cyclic promise exhausts fuel explicitly"
  | .error error => throw <| IO.userError s!"wrong cycle error: {repr error}"
  | .ok _ => throw <| IO.userError "cyclic promise unexpectedly normalized"
  assertEqual "objects enumerated from facts" [object] (objects state)
  -- Opinions are the value of a slot, and tell the observers of it, as upstream.
  let voted : Object := ⟨"program", "voted", 2⟩
  let named : Slot .string := stringSlot "named"
  assertEqual "an object with only an opinion is an object" [object, voted]
    (objects (suggest ⟨"agent", 1⟩ named voted "name" state))
  let sentinel : Environment := { observers := [observe named fun _ _ => .error (.failed "told")] }
  (match suggestWith sentinel ⟨"agent", 1⟩ named voted "name" state with
    | .error (.failed "told") => IO.println "ok: a new vote tells the observers of its slot"
    | _ => throw <| IO.userError "a new vote did not tell the observers of its slot")
  let votedState := suggest ⟨"agent", 1⟩ named voted "name" state
  (match suggestWith sentinel ⟨"agent", 1⟩ named voted "name" votedState with
    | .ok again => assertEqual "a repeated vote tells no one" votedState.version again.version
    | .error _ => throw <| IO.userError "a repeated vote told the observers")
  -- A saved slot that nothing here knows is skipped, and said to be.
  let known : List AnySlot := [⟨.nat, address⟩]
  let both : List AnySlot := [⟨.nat, address⟩, ⟨.nat, answer⟩]
  let saved : State := match provide answer object 7 state with | .ok next => next | .error _ => state
  match serialize both saved with
  | .error error => throw <| IO.userError error
  | .ok text =>
    match deserialize known text, Sexp.parse text with
    | .ok loaded, .ok parsed =>
      assertEqual "what is registered is read" (some 20) (match lookupFact address object loaded.facts with | .ok value => value | .error _ => none)
      assertEqual "what is not registered is skipped" none (match lookupFact answer object loaded.facts with | .ok value => value | .error _ => some 0)
      assertEqual "and said to be" ["answer"] (skippedSlots known parsed)
      assertEqual "nothing is skipped of what is known" ([] : List String) (skippedSlots both parsed)
    | _, _ => throw <| IO.userError "a state with a slot that is not registered does not load"
  let unrelated := natSlot "unrelated"
  let boom : Promise := promise unrelated fun _ _ => .error (.failed "boom")
  match collect { promises := [boom, computedAnswer] } answer object state with
  | .ok (value, _) => assertEqual "an unrelated failure cannot fail a collect" 21 value
  | .error error => throw <| IO.userError s!"unrelated promise failed a collect: {repr error}"
  let clashing : Environment := { promises := [
    promise (stringSlot "unrelated") fun _ _ => .ok (some "left"),
    promise (stringSlot "unrelated") fun _ _ => .ok (some "right"),
    computedAnswer
  ] }
  match collect clashing answer object state with
  | .ok (value, _) => assertEqual "an unrelated conflict cannot fail a collect" 21 value
  | .error error => throw <| IO.userError s!"unrelated conflict failed a collect: {repr error}"
  match collect clashing (stringSlot "unrelated") object state with
  | .error (.incompatible "unrelated") => IO.println "ok: a slot's own conflict fails its collect"
  | .error error => throw <| IO.userError s!"wrong conflict: {repr error}"
  | .ok _ => throw <| IO.userError "a slot's own conflict was ignored"
  match collect { cyclic with promises := computedAnswer :: cyclic.promises } answer object state 10 with
  | .ok (value, _) => assertEqual "unrelated divergence cannot fail a collect" 21 value
  | .error error => throw <| IO.userError s!"unrelated divergence failed a collect: {repr error}"
  let doubled : Promise := promise (natSlot "doubled") (deps := [answer.name]) fun obj facts => do
    let value ← lookupFact answer obj facts
    .ok (some (value.getD 0 * 2))
  match collect { promises := [doubled, computedAnswer] } (natSlot "doubled") object state with
  | .ok (value, next) =>
    assertEqual "a dependency's promise runs, whatever the order" 42 value
    match lookupFact answer object next.facts with
    | .ok stored => assertEqual "a dependency's value is stored" (some 21) stored
    | .error error => throw <| IO.userError s!"lookup failed: {repr error}"
  | .error error => throw <| IO.userError s!"dependent collect failed: {repr error}"
  let failingDep : Promise := promise answer fun _ _ => .error (.failed "dep")
  match collect { promises := [doubled, failingDep] } (natSlot "doubled") object state with
  | .error (.failed "dep") => IO.println "ok: a dependency's failure fails the collect"
  | .error error => throw <| IO.userError s!"wrong dependency failure: {repr error}"
  | .ok _ => throw <| IO.userError "a dependency's failure was ignored"
  let peeking : Promise := promise (natSlot "peeking") fun obj facts => do
    let value ← lookupFact answer obj facts
    .ok (some (value.getD 0 + 1))
  match collect { promises := [peeking, computedAnswer] } (natSlot "peeking") object state with
  | .ok (value, _) => assertEqual "an undeclared slot is read as it is, as upstream's current" 1 value
  | .error error => throw <| IO.userError s!"peeking collect failed: {repr error}"
  let known : Slot .bool := ⟨"known", boolDomain⟩
  let tribool ← provideOrFail known (some false) {}
  match lookupFact known object tribool.facts with
  | .ok value => assertEqual "false is knowledge" (some (some false)) value
  | .error error => throw <| IO.userError s!"lookup failed: {repr error}"
  assertEqual "providing false refines unknown" 1 tribool.version
  assertEqual "unknown is the empty element" 1 (← provideOrFail known none tribool).version
  match provide known object (some true) tribool with
  | .error (.incompatible "known") => IO.println "ok: true contradicts false"
  | .error error => throw <| IO.userError s!"wrong tribool conflict: {repr error}"
  | .ok _ => throw <| IO.userError "true was joined with false"

end Bap.Tests.Knowledge
