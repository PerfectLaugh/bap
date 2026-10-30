import BapTests.Support

namespace Bap.Tests.Persistence

open Bap
open Bap.Knowledge

private def address : Slot .nat := ⟨"address", maxDomain⟩
private def named : Slot .string := ⟨"name", stringDomain⟩
private def bits : Slot (.bitvec 128) := ⟨"bits", exactDomain 0⟩
private def object : Object := ⟨"program", "main", 1⟩

private def provideOrFail (slot : Slot kind) (value : kind.data) (state : State) : IO State :=
  match provide slot object value state with
  | .ok state => pure state
  | .error error => throw <| IO.userError s!"provide failed: {repr error}"

def run : IO Unit := do
  let checked := observe address fun obj facts => do
    let value ← lookupFact address obj facts
    if value.getD 0 ≥ 10 then .ok () else .error (.failed "below observer threshold")
  let env : Environment := { observers := [checked] }
  match provideWith env address object 10 {} with
  | .ok _ => IO.println "ok: observer accepts refined value"
  | .error error => throw <| IO.userError s!"observer failed: {repr error}"
  let rejecting := observe address fun _ _ => .error (.failed "observer rejected update")
  let rejectingEnv : Environment := { observers := [rejecting] }
  match provideWith rejectingEnv address object 10 {} with
  | .error (.failed "observer rejected update") => IO.println "ok: observer rejection propagated"
  | .error error => throw <| IO.userError s!"wrong observer error: {repr error}"
  | .ok _ => throw <| IO.userError "observer rejection was ignored"
  let unrelatedEnv : Environment := { observers := [observe named fun _ _ => .error (.failed "wrong slot")] }
  match provideWith unrelatedEnv address object 10 {} with
  | .ok _ => IO.println "ok: unrelated observer not invoked"
  | .error error => throw <| IO.userError s!"unrelated observer invoked: {repr error}"
  let state ← provideOrFail address 42 {}
  let wide : Nat := 2 ^ 127 + 1
  let state ← provideOrFail bits wide state
  let state ← provideOrFail named "not persistent" state
  let persistent : List AnySlot := [⟨.nat, address⟩, ⟨.bitvec 128, bits⟩]
  let encoded ← match serialize persistent state with
    | .ok value => pure value
    | .error error => throw <| IO.userError error
  let restored ← match deserialize persistent encoded with
    | .ok value => pure value
    | .error error => throw <| IO.userError error
  match lookupFact address object restored.facts with
  | .ok value => assertEqual "persistent natural round trip" (some 42) value
  | .error error => throw <| IO.userError s!"restore failed: {repr error}"
  match lookupFact bits object restored.facts with
  | .ok (some value) => assertEqual "persistent wide bitvector round trip" wide value.toNat
  | .ok none => throw <| IO.userError "wide bitvector missing"
  | .error error => throw <| IO.userError s!"bitvector restore failed: {repr error}"
  match lookupFact named object restored.facts with
  | .ok value => assertEqual "non-persistent slot omitted" none value
  | .error error => throw <| IO.userError s!"optional restore failed: {repr error}"
  assertEqual "persistent version restored" state.version restored.version
  let factState ← provideOrFail address 42 {}
  let factState ← provideOrFail bits wide factState
  let factProject : Project.Project := { knowledge := factState }
  Project.save factProject "native/build/project-knowledge.sexp" persistent
  let restoredProject ← Project.loadSaved "native/build/project-knowledge.sexp" persistent
  match lookupFact address object restoredProject.knowledge.facts with
  | .ok value => assertEqual "project Knowledge natural round trip" (some 42) value
  | .error error => throw <| IO.userError s!"project Knowledge restore failed: {repr error}"
  match lookupFact bits object restoredProject.knowledge.facts with
  | .ok (some value) => assertEqual "project Knowledge bitvector round trip" wide value.toNat
  | .ok none => throw <| IO.userError "project Knowledge bitvector missing"
  | .error error => throw <| IO.userError s!"project Knowledge restore failed: {repr error}"
  assertEqual "project Knowledge version restored" factState.version restoredProject.knowledge.version
  let unregisteredProject : Project.Project := { knowledge := state }
  let unregisteredFailed ← try
    Project.save unregisteredProject "native/build/project-unregistered.sexp" persistent
    pure false
  catch _ => pure true
  assertTrue "project rejects unregistered Knowledge slots" unregisteredFailed
  let opinionState := suggest ⟨"test", 1⟩ address object 42 {}
  let opinionProject : Project.Project := { knowledge := opinionState }
  Project.save opinionProject "native/build/project-opinions.sexp" persistent
  let restoredOpinions ← Project.loadSaved "native/build/project-opinions.sexp" persistent
  match restoredOpinions.knowledge.opinions with
  | [opinion] =>
    assertEqual "project opinion agent round trip" "test" opinion.agent.name
    assertEqual "project opinion trust round trip" 1 opinion.agent.trust
  | _ => throw <| IO.userError "project opinion was not restored"
  match resolve address object restoredOpinions.knowledge with
  | .ok value => assertEqual "project opinion resolves after restore" 42 value
  | .error error => throw <| IO.userError s!"project opinion resolution failed: {repr error}"
  let unregisteredOpinion := suggest ⟨"test", 1⟩ named object "bad" opinionState
  let unregisteredOpinionFailed ← try
    Project.save { knowledge := unregisteredOpinion } "native/build/project-opinion-unregistered.sexp" persistent
    pure false
  catch _ => pure true
  assertTrue "project rejects unregistered opinion slots" unregisteredOpinionFailed
  match decodeValue (.bitvec 8) (.tagged "int" [.atom "8", .atom "ff"]) with
  | .ok value => assertEqual "largest bitvector value accepted" 0xff value.toNat
  | .error error => throw <| IO.userError s!"largest bitvector value rejected: {error}"
  match decodeValue (.bitvec 8) (.tagged "int" [.atom "8", .atom "1ff"]) with
  | .error _ => IO.println "ok: oversized bitvector rejected"
  | .ok _ => throw <| IO.userError "oversized bitvector was truncated"
  match encodeValue .target Theory.unknown with
  | .error _ => IO.println "ok: unsupported persistence kind rejected"
  | .ok _ => throw <| IO.userError "unsupported payload was serialized"

end Bap.Tests.Persistence
