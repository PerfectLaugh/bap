import Bap.Bil.Syntax
import Bap.Core.Sexp

namespace Bap.Bil.Wire

open Bap

private def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def parseHexLoop : List Char → Nat → Except String Nat
  | [], result => .ok result
  | c :: rest, result =>
    match hexDigit c with
    | some digit => parseHexLoop rest (result * 16 + digit)
    | none => .error s!"invalid hexadecimal digit {c}"

def parseHex (input : String) : Except String Nat :=
  if input.isEmpty then .error "empty hexadecimal value" else parseHexLoop input.toList 0

def parseTyp (input : Sexp) : Except String Typ := do
  match input with
  | .atom "unk" => .ok .unknown
  | .atom "unit" => .ok .unit
  | .list [.atom "imm", width] => .ok (.imm (← Sexp.nat width))
  | .list [.atom "mem", address, value] => .ok (.mem (← Sexp.nat address) (← Sexp.nat value))
  | _ => .error s!"invalid BIL type {input}"

def printTyp : Typ → Sexp
  | .unknown => .atom "unk"
  | .unit => .atom "unit"
  | .imm width => .tagged "imm" [.atom (toString width)]
  | .mem address value => .tagged "mem" [.atom (toString address), .atom (toString value)]

def parseVar (input : Sexp) : Except String Var := do
  let args ← Sexp.expectTagged "var" 4 input
  match args with
  | [name, index, typ, virtual] =>
    let name ← Sexp.asAtom name
    let index ← Sexp.nat index
    let typ ← parseTyp typ
    let virtual ← Sexp.asAtom virtual
    match virtual with
    | "0" => .ok ⟨name, typ, index, false⟩
    | "1" => .ok ⟨name, typ, index, true⟩
    | _ => .error "invalid virtual flag"
  | _ => .error "invalid variable"

def printVar (var : Var) : Sexp :=
  .tagged "var" [
    .atom var.name,
    .atom (toString var.index),
    printTyp var.typ,
    .atom (if var.isVirtual then "1" else "0")
  ]

def parseEndian (input : Sexp) : Except String Endian := do
  match ← Sexp.asAtom input with
  | "el" => .ok .little
  | "be" => .ok .big
  | _ => .error "invalid endian"

def printEndian : Endian → Sexp
  | .little => .atom "el"
  | .big => .atom "be"

def parseCast (input : Sexp) : Except String Cast := do
  match ← Sexp.asAtom input with
  | "LOW" => .ok .low
  | "HIGH" => .ok .high
  | "SIGNED" => .ok .signed
  | "UNSIGNED" => .ok .unsigned
  | _ => .error "invalid cast"

def printCast : Cast → Sexp
  | .low => .atom "LOW"
  | .high => .atom "HIGH"
  | .signed => .atom "SIGNED"
  | .unsigned => .atom "UNSIGNED"

def parseUnOp (input : Sexp) : Except String UnOp := do
  match ← Sexp.asAtom input with
  | "NEG" => .ok .neg
  | "NOT" => .ok .not
  | _ => .error "invalid unary operator"

def printUnOp : UnOp → Sexp
  | .neg => .atom "NEG"
  | .not => .atom "NOT"

private def binOpNames : List (BinOp × String) := [
  (.add, "PLUS"), (.sub, "MINUS"), (.mul, "TIMES"), (.div, "DIVIDE"),
  (.sdiv, "SDIVIDE"), (.rem, "MOD"), (.srem, "SREM"), (.smod, "SMOD"),
  (.lshift, "LSHIFT"), (.rshift, "RSHIFT"), (.ashift, "ARSHIFT"),
  (.and, "AND"), (.or, "OR"), (.xor, "XOR"), (.eq, "EQ"), (.neq, "NEQ"),
  (.lt, "LT"), (.le, "LE"), (.gt, "GT"), (.ge, "GE"),
  (.slt, "SLT"), (.sle, "SLE"), (.sgt, "SGT"), (.sge, "SGE")
]

def parseBinOp (input : Sexp) : Except String BinOp := do
  let name ← Sexp.asAtom input
  match binOpNames.find? fun entry => entry.2 == name with
  | some entry => .ok entry.1
  | none => .error s!"invalid binary operator {name}"

def printBinOp (op : BinOp) : Sexp :=
  match binOpNames.find? fun entry => entry.1 == op with
  | some entry => .atom entry.2
  | none => .atom "INVALID"

def parseExp (input : Sexp) : Except String Exp := do
  match input with
  | .list [.atom "int", .atom width, .atom value] =>
    let width ← match width.toNat? with | some n => .ok n | none => .error "invalid integer width"
    .ok (.int (BitVec.ofNat width (← parseHex value)))
  | .list (.atom "var" :: _) => .ok (.var (← parseVar input))
  | .list [.atom "load", memory, address, endian, size] =>
    .ok (.load (← parseExp memory) (← parseExp address) (← parseEndian endian) (← Sexp.nat size))
  | .list [.atom "store", memory, address, value, endian, size] =>
    .ok (.store (← parseExp memory) (← parseExp address) (← parseExp value)
      (← parseEndian endian) (← Sexp.nat size))
  | .list [.atom "binop", op, left, right] =>
    .ok (.bin (← parseBinOp op) (← parseExp left) (← parseExp right))
  | .list [.atom "unop", op, value] => .ok (.un (← parseUnOp op) (← parseExp value))
  | .list [.atom "cast", kind, width, value] =>
    .ok (.cast (← parseCast kind) (← Sexp.nat width) (← parseExp value))
  | .list [.atom "let", var, value, body] =>
    .ok (.letIn (← parseVar var) (← parseExp value) (← parseExp body))
  | .list [.atom "ite", condition, yes, no] =>
    .ok (.ite (← parseExp condition) (← parseExp yes) (← parseExp no))
  | .list [.atom "extract", high, low, value] =>
    .ok (.extract (← Sexp.nat high) (← Sexp.nat low) (← parseExp value))
  | .list [.atom "concat", left, right] => .ok (.concat (← parseExp left) (← parseExp right))
  | .list [.atom "unknown", message, typ] => .ok (.unknown (← Sexp.asAtom message) (← parseTyp typ))
  | _ => .error s!"invalid BIL expression {input}"

def printExp : Exp → Sexp
  | @Exp.int width value => .tagged "int" [.atom (toString width), .atom (Word.toHex value)]
  | .var var => printVar var
  | .load memory address endian size =>
    .tagged "load" [printExp memory, printExp address, printEndian endian, .atom (toString size)]
  | .store memory address value endian size =>
    .tagged "store" [printExp memory, printExp address, printExp value, printEndian endian,
      .atom (toString size)]
  | .bin op left right => .tagged "binop" [printBinOp op, printExp left, printExp right]
  | .un op value => .tagged "unop" [printUnOp op, printExp value]
  | .cast kind width value => .tagged "cast" [printCast kind, .atom (toString width), printExp value]
  | .letIn var value body => .tagged "let" [printVar var, printExp value, printExp body]
  | .ite condition yes no => .tagged "ite" [printExp condition, printExp yes, printExp no]
  | .extract high low value =>
    .tagged "extract" [.atom (toString high), .atom (toString low), printExp value]
  | .concat left right => .tagged "concat" [printExp left, printExp right]
  | .unknown message typ => .tagged "unknown" [.atom message, printTyp typ]

mutual
  def parseStmt (fuel : Nat) (input : Sexp) : Except String Stmt := do
    if fuel = 0 then
      .error "statement parser fuel exhausted"
    else
      match input with
      | .list [.atom "move", var, value] => .ok (.move (← parseVar var) (← parseExp value))
      | .list [.atom "jmp", target] => .ok (.jmp (← parseExp target))
      | .list [.atom "special", message] => .ok (.special (← Sexp.asAtom message))
      | .list [.atom "while", condition, body] =>
        .ok (.while (← parseExp condition) (← parseStmts (fuel - 1) body))
      | .list [.atom "if", condition, yes, no] =>
        .ok (.ifElse (← parseExp condition) (← parseStmts (fuel - 1) yes) (← parseStmts (fuel - 1) no))
      | .list [.atom "cpuexn", number] => .ok (.cpuExn (← Sexp.nat number))
      | _ => .error s!"invalid BIL statement {input}"

  def parseStmts (fuel : Nat) (input : Sexp) : Except String Program := do
    let items ← Sexp.asList input
    parseStmtList fuel items

  def parseStmtList (fuel : Nat) : List Sexp → Except String Program
    | [] => .ok []
    | item :: rest => do
      let stmt ← parseStmt fuel item
      let stmts ← parseStmtList fuel rest
      .ok (stmt :: stmts)
end

def printStmt : Stmt → Sexp
  | .move var value => .tagged "move" [printVar var, printExp value]
  | .jmp target => .tagged "jmp" [printExp target]
  | .special message => .tagged "special" [.atom message]
  | .while condition body => .tagged "while" [printExp condition, .list (body.map printStmt)]
  | .ifElse condition yes no =>
    .tagged "if" [printExp condition, .list (yes.map printStmt), .list (no.map printStmt)]
  | .cpuExn number => .tagged "cpuexn" [.atom (toString number)]

def printProgram (program : Program) : Sexp := .list (program.map printStmt)

def parseProgram (input : String) : Except String Program := do
  let sexp ← Sexp.parse input
  let args ← Sexp.expectTagged "bil" 1 sexp
  match args with
  | [program] => parseStmts 1000000 program
  | _ => .error "invalid BIL program"

def renderProgram (program : Program) : String :=
  toString (Sexp.tagged "bil" [printProgram program])

end Bap.Bil.Wire
