import Std

namespace Bap

inductive Sexp where
  | atom (value : String)
  | list (items : List Sexp)
  deriving BEq, Repr

mutual
  def Sexp.decEq : (x y : Sexp) → Decidable (x = y)
    | .atom a, .atom b =>
      if h : a = b then
        isTrue (congrArg Sexp.atom h)
      else
        isFalse fun eq => by cases eq; exact h rfl
    | .list xs, .list ys =>
      match listDecEq xs ys with
      | isTrue h => isTrue (congrArg Sexp.list h)
      | isFalse h => isFalse fun eq => by cases eq; exact h rfl
    | .atom _, .list _ => isFalse (by intro h; contradiction)
    | .list _, .atom _ => isFalse (by intro h; contradiction)

  def listDecEq : (xs ys : List Sexp) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
      match Sexp.decEq x y, listDecEq xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _ => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs => isFalse (by intro h; cases h; exact hxs rfl)
    | [], _ :: _ => isFalse (by intro h; contradiction)
    | _ :: _, [] => isFalse (by intro h; contradiction)
end

instance : DecidableEq Sexp := Sexp.decEq

namespace Sexp

def tagged (tag : String) (items : List Sexp := []) : Sexp :=
  .list (.atom tag :: items)

def asAtom : Sexp → Except String String
  | .atom value => .ok value
  | value => .error s!"expected an atom, got {repr value}"

def asList : Sexp → Except String (List Sexp)
  | .list items => .ok items
  | value => .error s!"expected a list, got {repr value}"

def expectTagged (tag : String) (arity : Nat) (value : Sexp) : Except String (List Sexp) := do
  let items ← asList value
  match items with
  | .atom actual :: args =>
    if actual = tag ∧ args.length = arity then
      .ok args
    else
      .error s!"expected ({tag} ...) with arity {arity}"
  | _ => .error s!"expected ({tag} ...) with arity {arity}"

def nat (value : Sexp) : Except String Nat := do
  let atom ← asAtom value
  match atom.toNat? with
  | some value => .ok value
  | none => .error s!"expected a natural number, got {atom}"

def dropComment : List Char → List Char
  | [] => []
  | '\n' :: rest => rest
  | _ :: rest => dropComment rest

partial def skipSpace : List Char → List Char
  | [] => []
  | c :: rest =>
    if c.isWhitespace then
      skipSpace rest
    else if c = ';' then
      skipSpace (dropComment rest)
    else
      c :: rest

private def escape : Char → List Char
  | '"' => ['\\', '"']
  | '\\' => ['\\', '\\']
  | '\n' => ['\\', 'n']
  | '\r' => ['\\', 'r']
  | '\t' => ['\\', 't']
  | c => [c]

private def parseEscaped : Char → Except String Char
  | 'n' => .ok '\n'
  | 'r' => .ok '\r'
  | 't' => .ok '\t'
  | '\\' => .ok '\\'
  | '"' => .ok '"'
  | c => .error s!"unsupported escape sequence \\{c}"

private def parseQuoted : Nat → List Char → Except String (String × List Char)
  | 0, _ => .error "unterminated quoted atom"
  | _ + 1, [] => .error "unterminated quoted atom"
  | _fuel + 1, '"' :: rest => .ok ("", rest)
  | fuel + 1, '\\' :: c :: rest => do
    let (tail, remaining) ← parseQuoted fuel rest
    .ok (String.ofList [← parseEscaped c] ++ tail, remaining)
  | fuel + 1, c :: rest => do
    let (tail, remaining) ← parseQuoted fuel rest
    .ok (String.ofList [c] ++ tail, remaining)

private def parseAtom (input : List Char) : String × List Char :=
  let atom := input.takeWhile fun c => !(c.isWhitespace ∨ c = '(' ∨ c = ')' ∨ c = ';')
  (String.ofList atom, input.drop atom.length)

mutual
  def parseOne : Nat → List Char → Except String (Sexp × List Char)
    | 0, _ => .error "S-expression parser fuel exhausted"
    | fuel + 1, input =>
      match skipSpace input with
      | [] => .error "expected an S-expression"
      | '(' :: rest => do
        let (items, remaining) ← parseList fuel rest
        .ok (.list items, remaining)
      | ')' :: _ => .error "unexpected closing parenthesis"
      | '\'' :: rest => do
        let (value, remaining) ← parseOne fuel rest
        .ok (.list [.atom "quote", value], remaining)
      | '"' :: rest => do
        let (value, remaining) ← parseQuoted (rest.length + 1) rest
        .ok (.atom value, remaining)
      | input =>
        let (value, remaining) := parseAtom input
        .ok (.atom value, remaining)

  def parseList : Nat → List Char → Except String (List Sexp × List Char)
    | 0, _ => .error "unterminated S-expression list"
    | fuel + 1, input =>
      match skipSpace input with
      | [] => .error "unterminated S-expression list"
      | ')' :: rest => .ok ([], rest)
      | input => do
        let (item, rest) ← parseOne fuel input
        let (items, remaining) ← parseList fuel rest
        .ok (item :: items, remaining)
end

private def parseManyAux : Nat → List Char → List Sexp → Except String (List Sexp)
  | 0, _, _ => .error "S-expression parser fuel exhausted"
  | fuel + 1, input, results =>
    match skipSpace input with
    | [] => .ok results.reverse
    | _ => do
      let (value, rest) ← parseOne fuel input
      parseManyAux fuel rest (value :: results)

def parseMany (input : String) : Except String (List Sexp) := do
  let chars := input.toList
  parseManyAux (chars.length * 2 + 2) chars []

def parse (input : String) : Except String Sexp := do
  let chars := input.toList
  let (value, rest) ← parseOne (chars.length * 2 + 2) chars
  match skipSpace rest with
  | [] => .ok value
  | _ => .error "trailing input after S-expression"

private def needsQuotes (value : String) : Bool :=
  value.isEmpty ∨ value.toList.any fun c =>
    c.isWhitespace ∨ c = '(' ∨ c = ')' ∨ c = ';' ∨ c = '"' ∨ c = '\\'

def render : Sexp → String
  | .atom value =>
    if needsQuotes value then
      "\"" ++ String.ofList (value.toList.flatMap escape) ++ "\""
    else
      value
  | .list items => "(" ++ String.intercalate " " (items.map render) ++ ")"

instance : ToString Sexp where
  toString := render

end Sexp
end Bap
