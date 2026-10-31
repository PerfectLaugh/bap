import Bap.IR.Syntax
import Bap.Bil.Wire

namespace Bap.IR.Wire

open Bap

private def printDefWithTag (tag : String) (defn : Def) : Sexp :=
  .tagged tag [.atom (toString defn.tid), Bil.Wire.printVar defn.var, Bil.Wire.printExp defn.rhs]

private def parseDefWithTag (tag : String) (input : Sexp) : Except String Def := do
  let args ← Sexp.expectTagged tag 3 input
  match args with
  | [tid, var, rhs] => .ok ⟨← Sexp.nat tid, ← Bil.Wire.parseVar var, ← Bil.Wire.parseExp rhs⟩
  | _ => .error "invalid definition"

def printPhi (phi : Phi) : Sexp :=
  .tagged "phi" [
    .atom (toString phi.tid), Bil.Wire.printVar phi.var,
    .list <| phi.values.map fun (tid, value) => .list [.atom (toString tid), Bil.Wire.printExp value]
  ]

def parsePhi (input : Sexp) : Except String Phi := do
  let args ← Sexp.expectTagged "phi" 3 input
  match args with
  | [tid, var, values] =>
    let values ← Sexp.asList values
    let values ← values.mapM fun value => do
      match value with
      | .list [tid, exp] => .ok (← Sexp.nat tid, ← Bil.Wire.parseExp exp)
      | _ => .error "invalid phi input"
    .ok ⟨← Sexp.nat tid, ← Bil.Wire.parseVar var, values⟩
  | _ => .error "invalid phi"

def printLabel : Label → Sexp
  | .direct tid => .tagged "direct" [.atom (toString tid)]
  | .indirect exp => .tagged "indirect" [Bil.Wire.printExp exp]

def parseLabel (input : Sexp) : Except String Label := do
  match input with
  | .list [.atom "direct", tid] => .ok (.direct (← Sexp.nat tid))
  | .list [.atom "indirect", exp] => .ok (.indirect (← Bil.Wire.parseExp exp))
  | _ => .error "invalid label"

def printOptionalLabel : Option Label → Sexp
  | none => .atom "none"
  | some label => .tagged "some" [printLabel label]

def parseOptionalLabel (input : Sexp) : Except String (Option Label) := do
  match input with
  | .atom "none" => .ok none
  | .list [.atom "some", label] => .ok (some (← parseLabel label))
  | _ => .error "invalid optional label"

def printJmp (jmp : Jmp) : Sexp :=
  let condition := match jmp.condition with
    | none => .atom "none"
    | some exp => .tagged "some" [Bil.Wire.printExp exp]
  let kind := match jmp.kind with
    | .goto target => .tagged "goto" [printLabel target]
    | .ret target => .tagged "ret" [printLabel target]
    | .call target returnTo => .tagged "call" [printLabel target, printOptionalLabel returnTo]
    | .interrupt number returnTo =>
      .tagged "int" [.atom (toString number), .atom (toString returnTo)]
  .tagged "jmp" [.atom (toString jmp.tid), condition, kind]

def parseJmp (input : Sexp) : Except String Jmp := do
  let args ← Sexp.expectTagged "jmp" 3 input
  match args with
  | [tid, condition, kind] =>
    let condition ← match condition with
      | .atom "none" => .ok none
      | .list [.atom "some", exp] => .ok (some (← Bil.Wire.parseExp exp))
      | _ => .error "invalid jump condition"
    let kindItems ← Sexp.asList kind
    let kind ← match kindItems with
      | [.atom "goto", target] => .ok (.goto (← parseLabel target))
      | [.atom "ret", target] => .ok (.ret (← parseLabel target))
      | [.atom "call", target, returnTo] => .ok (.call (← parseLabel target) (← parseOptionalLabel returnTo))
      | [.atom "int", number, returnTo] => .ok (.interrupt (← Sexp.nat number) (← Sexp.nat returnTo))
      | _ => .error "invalid jump kind"
    .ok ⟨← Sexp.nat tid, condition, kind⟩
  | _ => .error "invalid jump"

def printBlk (blk : Blk) : Sexp :=
  .tagged "blk" [
    .atom (toString blk.tid), .list (blk.phis.map printPhi),
    .list (blk.defs.map (printDefWithTag "def")), .list (blk.jmps.map printJmp)
  ]

def parseBlk (input : Sexp) : Except String Blk := do
  let args ← Sexp.expectTagged "blk" 4 input
  match args with
  | [tid, phis, defs, jmps] =>
    .ok ⟨
      ← Sexp.nat tid,
      ← (← Sexp.asList phis).mapM parsePhi,
      ← (← Sexp.asList defs).mapM (parseDefWithTag "def"),
      ← (← Sexp.asList jmps).mapM parseJmp
    ⟩
  | _ => .error "invalid block"

def printSub (sub : Sub) : Sexp :=
  .tagged "sub" [
    .atom (toString sub.tid), .atom sub.name,
    .list (sub.args.map (printDefWithTag "arg")), .list (sub.blks.map printBlk)
  ]

def parseSub (input : Sexp) : Except String Sub := do
  let args ← Sexp.expectTagged "sub" 4 input
  match args with
  | [tid, name, args, blks] =>
    .ok ⟨
      ← Sexp.nat tid, ← Sexp.asAtom name,
      ← (← Sexp.asList args).mapM (parseDefWithTag "arg"),
      ← (← Sexp.asList blks).mapM parseBlk
    ⟩
  | _ => .error "invalid subroutine"

def parseSubString (input : String) : Except String Sub := do
  parseSub (← Sexp.parse input)

def renderSub (sub : Sub) : String := toString (printSub sub)

end Bap.IR.Wire
