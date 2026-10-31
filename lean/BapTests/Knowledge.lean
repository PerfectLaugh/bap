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
    promise a fun obj facts => do
      let value ← lookupFact b obj facts
      .ok (some (value.getD 0 + 1)),
    promise b fun obj facts => do
      let value ← lookupFact a obj facts
      .ok (some (value.getD 0 + 1))
  ] }
  match collect cyclic a object {} 10 with
  | .error .exhausted => IO.println "ok: cyclic promise exhausts fuel explicitly"
  | .error error => throw <| IO.userError s!"wrong cycle error: {repr error}"
  | .ok _ => throw <| IO.userError "cyclic promise unexpectedly normalized"
  assertEqual "objects enumerated from facts" [object] (objects state)

end Bap.Tests.Knowledge
