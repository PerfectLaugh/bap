import Bap.Knowledge.Core
import Bap.Bil.Wire

namespace Bap.Knowledge

abbrev AnySlot := Σ kind, Slot kind

def encodeValue (kind : PayloadKind) (value : kind.data) : Except String Sexp :=
  match kind with
  | .unit => .ok (.atom "unit")
  | .bool => .ok (.atom (match value with | some flag => toString flag | none => "none"))
  | .nat => .ok (.atom (toString value))
  | .string => .ok (.atom value)
  | .bitvec width => .ok (.tagged "int" [.atom (toString width), .atom (Word.toHex value)])
  | _ => .error s!"persistent codec is not implemented for {repr kind}"

def decodeValue : (kind : PayloadKind) → Sexp → Except String kind.data
  | .unit, input =>
    match input with
    | .atom "unit" => .ok ()
    | _ => .error "invalid unit value"
  | .bool, input => do
    match ← Sexp.asAtom input with
    | "true" => .ok (some true)
    | "false" => .ok (some false)
    | "none" => .ok none
    | _ => .error "invalid boolean value"
  | .nat, input => Sexp.nat input
  | .string, input => Sexp.asAtom input
  | .bitvec width, input => do
    let args ← Sexp.expectTagged "int" 2 input
    match args with
    | [encodedWidth, value] =>
      let encodedWidth ← Sexp.nat encodedWidth
      if encodedWidth != width then
        .error "bitvector width mismatch"
      else
        let value ← Bil.Wire.parseHex (← Sexp.asAtom value)
        if value < 2 ^ width then
          .ok (BitVec.ofNat width value)
        else
          .error "bitvector value exceeds its width"
    | _ => .error "invalid bitvector"
  | kind, _ => .error s!"persistent codec is not implemented for {repr kind}"

def encodeFact (fact : Fact) : Except String Sexp := do
  let value ← encodeValue fact.slot.1 fact.value
  .ok (.tagged "fact" [
    .tagged "object" [.atom fact.object.cls, .atom fact.object.name, .atom (toString fact.object.id)],
    .atom fact.slot.2.name,
    value
  ])

def decodeFact (registry : List AnySlot) (input : Sexp) : Except String Fact := do
  let args ← Sexp.expectTagged "fact" 3 input
  match args with
  | [object, slotName, value] =>
    let objectArgs ← Sexp.expectTagged "object" 3 object
    match objectArgs with
    | [cls, name, id] =>
      let object : Object := ⟨← Sexp.asAtom cls, ← Sexp.asAtom name, ← Sexp.nat id⟩
      let slotName ← Sexp.asAtom slotName
      match registry.find? fun slot => slot.2.name = slotName with
      | none => .error s!"unknown persistent slot {slotName}"
      | some slot =>
        let value ← decodeValue slot.1 value
        .ok ⟨object, slot, value⟩
    | _ => .error "invalid persistent object"
  | _ => .error "invalid persistent fact"

def encodeOpinion (opinion : Opinion) : Except String Sexp := do
  let fact ← encodeFact opinion.fact
  .ok (.tagged "opinion" [.atom opinion.agent.name, .atom (toString opinion.agent.trust), fact])

def decodeOpinion (registry : List AnySlot) (input : Sexp) : Except String Opinion := do
  let args ← Sexp.expectTagged "opinion" 3 input
  match args with
  | [name, trust, fact] =>
    let name ← Sexp.asAtom name
    let trust ← Sexp.nat trust
    let fact ← decodeFact registry fact
    .ok ⟨⟨name, trust⟩, fact⟩
  | _ => .error "invalid persistent opinion"

def encodeState (persistent : List AnySlot) (state : State) : Except String Sexp := do
  let names := persistent.map fun slot => slot.2.name
  let facts := state.facts.filter fun fact => fact.slot.2.name ∈ names
  let facts ← facts.mapM encodeFact
  let opinions := state.opinions.filter fun opinion => opinion.fact.slot.2.name ∈ names
  let opinions ← opinions.mapM encodeOpinion
  .ok (.tagged "state" [.atom (toString state.version), .list facts, .list opinions])

def serialize (persistent : List AnySlot) (state : State) : Except String String := do
  .ok (toString (← encodeState persistent state))

def decodeState (registry : List AnySlot) (input : Sexp) : Except String State := do
  let args ← Sexp.expectTagged "state" 3 input
  match args with
  | [version, facts, opinions] =>
    let version ← Sexp.nat version
    let facts ← (← Sexp.asList facts).mapM (decodeFact registry)
    let opinions ← (← Sexp.asList opinions).mapM (decodeOpinion registry)
    .ok { facts := facts, opinions := opinions, version := version }
  | _ => .error "invalid persistent state"

def deserialize (registry : List AnySlot) (input : String) : Except String State := do
  decodeState registry (← Sexp.parse input)

end Bap.Knowledge
