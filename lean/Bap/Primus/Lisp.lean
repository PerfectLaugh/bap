import Bap.Core.Sexp
import Bap.Core.Assoc
import Bap.Core.Word
import Bap.Bil.Syntax
import Bap.Primus.Literal

namespace Bap.Primus.Lisp

open Bap.Primus.Literal

mutual
  inductive Callable where
    | closure (params : List String) (body : Sexp) (env : List (String × Value))
    | primitive (name : String)

  inductive Value where
    | unit
    | int (value : BitVec 64)
    | bil (width : Nat) (value : Bil.Exp)
    | bool (value : Bool)
    | symbol (name : String)
    | list (items : List Value)
    | function (value : Callable)
end

abbrev Globals := List (String × Value)
abbrev Locals := List (String × Value)

private def primitiveNames : List String :=
  ["+", "-", "*", "/", "=", "<", "<=", ">", ">=", "not", "list", "cons", "car", "cdr",
    "length", "null?", "list?", "load", "store", "bitand", "bitor", "bitxor", "extract"]

private def renderValue : Value → String
  | .unit => "()"
  | .int value => s!"0x{Word.toHex value}"
  | .bil width _ => s!"<bil {width}>"
  | .bool value => if value then "true" else "false"
  | .symbol name => name
  | .list items => "(" ++ String.intercalate " " (items.map renderValue) ++ ")"
  | .function (.closure _ _ _) => "<closure>"
  | .function (.primitive name) => s!"<primitive {name}>"

private def atomValue (atom : String) : Value :=
  if atom = "true" then
    .bool true
  else if atom = "false" then
    .bool false
  else
    match parseInteger atom with
    | some (value, some width) => .bil width (.int (BitVec.ofInt width value))
    | some (value, none) => .int (BitVec.ofInt 64 value)
    | none => .symbol atom

private def quotedValue : Sexp → Value
  | .atom atom => atomValue atom
  | .list items => .list (items.map quotedValue)

private def lookup (name : String) (locals : Locals) (globals : Globals) : Except String Value :=
  match Assoc.get name locals with
  | some value => .ok value
  | none =>
    match Assoc.get name globals with
    | some value => .ok value
    | none =>
      if primitiveNames.contains name then
        .ok (.function (.primitive name))
      else
        .error s!"unknown symbol {name}"

private def expectBool : Value → Except String Bool
  | .bool value => .ok value
  | _ => .error "expected boolean"

private def expectInt : Value → Except String (BitVec 64)
  | .int value => .ok value
  | _ => .error "expected integer"

private def expectList : Value → Except String (List Value)
  | .list items => .ok items
  | _ => .error "expected list"

private def expectPair (name : String) (args : List Value) : Except String (Value × Value) :=
  match args with
  | [left, right] => .ok (left, right)
  | _ => .error s!"{name} expects two arguments"

private def expectBil : Value → Except String (Nat × Bil.Exp)
  | .int value => .ok (64, .int value)
  | .bil width value => .ok (width, value)
  | _ => .error "expected bitvector"

private def symbolic (value : Value) : Bool :=
  match value with
  | .bil _ _ => true
  | _ => false

private def foldBil (op : Bil.BinOp) (values : List (Nat × Bil.Exp)) : Except String Value := do
  match values with
  | [] => .error "expected a bitvector argument"
  | (width, first) :: rest =>
    let (width, result) ← rest.foldlM (init := (width, first)) fun state (nextWidth, next) => do
      if nextWidth != state.1 then
        .error "bitvector operands have different widths"
      else
        .ok (state.1, .bin op state.2 next)
    .ok (.bil width result)

private def compareBil (op : Bil.BinOp) (left right : Value) : Except String Value := do
  let (leftWidth, left) ← expectBil left
  let (rightWidth, right) ← expectBil right
  if leftWidth != rightWidth then
    .error "comparison operands have different widths"
  else
    .ok (.bil 1 (.bin op left right))

private def bitOperation (op : Bil.BinOp) (args : List Value) : Except String Value := do
  if args.any symbolic then
    foldBil op (← args.mapM expectBil)
  else
    let values ← args.mapM expectInt
    match op with
    | .and => .ok (.int (values.foldl (· &&& ·) 0xffffffffffffffff))
    | .or => .ok (.int (values.foldl (· ||| ·) 0))
    | .xor => .ok (.int (values.foldl (· ^^^ ·) 0))
    | _ => .error "invalid bitwise operation"

private def expectEndian : Value → Except String Endian
  | .symbol "little" => .ok .little
  | .symbol "big" => .ok .big
  | _ => .error "expected little or big endian"

private def expectSize : Value → Except String Nat
  | .int value =>
    if value.toNat = 0 then .error "memory access size must be positive" else .ok value.toNat
  | _ => .error "expected memory access size"

private def evalPrimitive (name : String) (args : List Value) : Except String Value := do
  match name with
  | "+" =>
    if args.any symbolic then
      let values ← args.mapM expectBil
      if values.isEmpty then .ok (.int 0) else foldBil .add values
    else
      let values ← args.mapM expectInt
      .ok (.int (values.foldl (· + ·) 0))
  | "*" =>
    if args.any symbolic then
      let values ← args.mapM expectBil
      if values.isEmpty then .ok (.int 1) else foldBil .mul values
    else
      let values ← args.mapM expectInt
      .ok (.int (values.foldl (· * ·) 1))
  | "-" =>
    if args.any symbolic then
      let values ← args.mapM expectBil
      match values with
      | [] => .error "- expects an argument"
      | [(width, value)] => .ok (.bil width (.un .neg value))
      | _ => foldBil .sub values
    else
      let values ← args.mapM expectInt
      match values with
      | [] => .error "- expects an argument"
      | [value] => .ok (.int (-value))
      | first :: rest => .ok (.int (rest.foldl (· - ·) first))
  | "/" =>
    if args.any symbolic then
      let values ← args.mapM expectBil
      foldBil .div values
    else
      let values ← args.mapM expectInt
      match values with
      | [] => .error "/ expects an argument"
      | first :: rest => .ok (.int (rest.foldl Word.udiv first))
  | "load" =>
    match args with
    | [memory, address, endian, size] => do
      let (memoryWidth, memory) ← expectBil memory
      let (addressWidth, address) ← expectBil address
      let endian ← expectEndian endian
      let size ← expectSize size
      if memoryWidth != 64 || addressWidth != 64 then
        .error "memory and address must be 64-bit"
      else
        .ok (.bil (size * 8) (.load memory address endian size))
    | _ => .error "load expects four arguments"
  | "store" =>
    match args with
    | [memory, address, value, endian, size] => do
      let (memoryWidth, memory) ← expectBil memory
      let (addressWidth, address) ← expectBil address
      let (valueWidth, value) ← expectBil value
      let endian ← expectEndian endian
      let size ← expectSize size
      if memoryWidth != 64 || addressWidth != 64 then
        .error "memory and address must be 64-bit"
      else if valueWidth != size * 8 then
        .error "stored value has the wrong width"
      else
        .ok (.bil 64 (.store memory address value endian size))
    | _ => .error "store expects five arguments"
  | "=" | "<" | "<=" | ">" | ">=" =>
    let (left, right) ← expectPair name args
    if args.any symbolic then
      let op := match name with
        | "=" => Bil.BinOp.eq
        | "<" => Bil.BinOp.lt
        | "<=" => Bil.BinOp.le
        | ">" => Bil.BinOp.gt
        | _ => Bil.BinOp.ge
      compareBil op left right
    else
      let left ← expectInt left
      let right ← expectInt right
      let result := match name with
        | "=" => left = right
        | "<" => left < right
        | "<=" => left ≤ right
        | ">" => left > right
        | _ => left ≥ right
      .ok (.bool result)
  | "not" =>
    match args with
    | [value] =>
      if symbolic value then
        let (_, value) ← expectBil value
        .ok (.bil 1 (.un .not value))
      else
        .ok (.bool (!(← expectBool value)))
    | _ => .error "not expects one argument"
  | "bitand" => bitOperation .and args
  | "bitor" => bitOperation .or args
  | "bitxor" => bitOperation .xor args
  | "extract" =>
    match args with
    | [value, high, low] => do
      let (width, value) ← expectBil value
      let high ← expectInt high
      let low ← expectInt low
      if high < low then
        .error "extract high bound is below low bound"
      else if high ≥ width then
        .error "extract high bound exceeds value width"
      else
        .ok (.bil (high.toNat - low.toNat + 1) (.extract high.toNat low.toNat value))
    | _ => .error "extract expects three arguments"
  | "list" => .ok (.list args)
  | "cons" =>
    let (head, tail) ← expectPair name args
    let tail ← expectList tail
    .ok (.list (head :: tail))
  | "car" =>
    match args with
    | [value] =>
      match ← expectList value with
      | head :: _ => .ok head
      | [] => .error "car of empty list"
    | _ => .error "car expects one argument"
  | "cdr" =>
    match args with
    | [value] =>
      match ← expectList value with
      | _ :: tail => .ok (.list tail)
      | [] => .error "cdr of empty list"
    | _ => .error "cdr expects one argument"
  | "length" =>
    match args with
    | [value] => .ok (.int (BitVec.ofNat 64 (← expectList value).length))
    | _ => .error "length expects one argument"
  | "null?" =>
    match args with
    | [value] => .ok (.bool (← expectList value).isEmpty)
    | _ => .error "null? expects one argument"
  | "list?" =>
    match args with
    | [.list _] => .ok (.bool true)
    | [_] => .ok (.bool false)
    | _ => .error "list? expects one argument"
  | _ => .error s!"unknown primitive {name}"

private def assignLocal (name : String) (value : Value) : Locals → Locals
  | [] => []
  | (key, old) :: rest =>
    if key = name then (key, value) :: rest else (key, old) :: assignLocal name value rest

/-- Evaluate `form`. Assignments to `let`-bound names change the enclosing bindings, so the
updated locals are returned along with the value and globals. -/
def evalExpr (fuel : Nat) (locals : Locals) (globals : Globals) (form : Sexp) :
    Except String (Value × Locals × Globals) := do
  match fuel with
  | 0 => .error "Lisp evaluation fuel exhausted"
  | fuel + 1 =>
    let evalList (forms : List Sexp) (locals : Locals) (globals : Globals) :
        Except String (List Value × Locals × Globals) :=
      forms.foldlM (init := ([], locals, globals)) fun state form => do
        let (value, locals, globals) ← evalExpr fuel state.2.1 state.2.2 form
        .ok (state.1 ++ [value], locals, globals)
    match form with
    | .atom atom =>
      -- `Bad_word_literal` upstream: an atom that starts like a number is not a symbol
      if atom = "true" || atom = "false" || (← readLiteral atom).isSome then
        .ok (atomValue atom, locals, globals)
      else
        .ok (← lookup atom locals globals, locals, globals)
    | .list [] => .ok (.list [], locals, globals)
    | .list (.atom "quote" :: args) =>
      match args with
      | [value] => .ok (quotedValue value, locals, globals)
      | _ => .error "quote expects one argument"
    | .list (.atom "if" :: args) =>
      match args with
      | [condition, yes, no] => do
        let (condition, locals, globals) ← evalExpr fuel locals globals condition
        if ← expectBool condition then
          evalExpr fuel locals globals yes
        else
          evalExpr fuel locals globals no
      | _ => .error "if expects three arguments"
    | .list (.atom "lambda" :: .list params :: [body]) => do
      let params ← params.mapM fun param =>
        match param with
        | .atom name => .ok name
        | _ => .error "lambda parameter must be a symbol"
      .ok (.function (.closure params body locals), locals, globals)
    | .list (.atom "defun" :: .atom name :: .list params :: [body]) => do
      let params ← params.mapM fun param =>
        match param with
        | .atom name => .ok name
        | _ => .error "function parameter must be a symbol"
      let callable : Value := .function (.closure params body locals)
      .ok (callable, locals, Assoc.put name callable globals)
    | .list (.atom "setq" :: [.atom name, value]) => do
      let (value, locals, globals) ← evalExpr fuel locals globals value
      if (Assoc.get name locals).isSome then
        .ok (value, assignLocal name value locals, globals)
      else
        .ok (value, locals, Assoc.put name value globals)
    | .list (.atom "let" :: .list bindings :: body) => do
      let (locals, globals) ← bindings.foldlM (init := (locals, globals)) fun state binding =>
        match binding with
        | .list [.atom name, value] => do
          let (value, locals, globals) ← evalExpr fuel state.1 state.2 value
          .ok ((name, value) :: locals, globals)
        | _ => .error "invalid let binding"
      let (values, locals, globals) ← evalList body locals globals
      .ok (values.getLast?.getD .unit, locals.drop bindings.length, globals)
    | .list (.atom "progn" :: body) => do
      let (values, locals, globals) ← evalList body locals globals
      .ok (values.getLast?.getD .unit, locals, globals)
    | .list (.atom "and" :: body) =>
      body.foldlM (init := (.bool true, locals, globals)) fun state form => do
        if !(← expectBool state.1) then
          .ok state
        else
          evalExpr fuel state.2.1 state.2.2 form
    | .list (.atom "or" :: body) =>
      body.foldlM (init := (.bool false, locals, globals)) fun state form => do
        if ← expectBool state.1 then
          .ok state
        else
          evalExpr fuel state.2.1 state.2.2 form
    | .list (operator :: operands) => do
      let (callable, locals, globals) ← evalExpr fuel locals globals operator
      let (args, locals, globals) ← evalList operands locals globals
      match callable with
      | .function (.primitive name) => .ok (← evalPrimitive name args, locals, globals)
      | .function (.closure params body env) =>
        if params.length != args.length then
          .error "closure arity mismatch"
        else
          let (value, _, globals) ← evalExpr fuel (params.zip args ++ env) globals body
          .ok (value, locals, globals)
      | _ => .error "attempted to call a non-function"
termination_by fuel

def evalProgram (fuel : Nat) (globals : Globals) (forms : List Sexp) : Except String (Value × Globals) := do
  let (value, _, globals) ← evalExpr fuel [] globals (.list (.atom "progn" :: forms))
  .ok (value, globals)

def evalString (input : String) (globals : Globals := []) (fuel : Nat := 100000) :
    Except String (Value × Globals) := do
  evalProgram fuel globals (← Sexp.parseMany input)

def render (value : Value) : String := renderValue value

end Bap.Primus.Lisp
