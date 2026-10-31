namespace Bap.Primus.Literal

def parseBasedNat (digits : String) (base : Nat) : Option Nat :=
  digits.toList.foldlM (fun value c => do
    let lower := c.toLower
    let digit := if c.isDigit then c.toNat - '0'.toNat
      else if lower ≥ 'a' && lower ≤ 'f' then lower.toNat - 'a'.toNat + 10
      else base
    if digit < base then some (value * base + digit) else none) 0

/-- `Z.of_string` of Zarith: optional sign, then an optional `0x`/`0o`/`0b` prefix, then digits that
may contain underscores but not start with one. No digits after a prefix reads as zero. -/
def parseZ (text : List Char) : Option Int :=
  let (negative, chars) := match text with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | chars => (false, chars)
  let (base, digits) := match chars with
    | '0' :: 'x' :: rest | '0' :: 'X' :: rest => (16, rest)
    | '0' :: 'o' :: rest | '0' :: 'O' :: rest => (8, rest)
    | '0' :: 'b' :: rest | '0' :: 'B' :: rest => (2, rest)
    | _ => (10, chars)
  if digits.head? = some '_' then none
  else
    (parseBasedNat (String.ofList (digits.filter (· != '_'))) base).map fun value =>
      if negative then -Int.ofNat value else Int.ofNat value

/-- Whether an atom starts like a number, which commits it to being one. -/
def startsNumeric : List Char → Bool
  | c :: rest => c.isDigit || (c = '-' && match rest with | d :: _ => d.isDigit | [] => false)
  | [] => false

private def malformed (atom : String) : Except String (Option (Int × Option Nat)) :=
  .error s!"malformed Primus literal {atom}"

/-- Reads the characters of an atom that is not a character literal. -/
def readNumeric (atom : String) (chars : List Char) : Except String (Option (Int × Option Nat)) :=
  if !startsNumeric chars then .ok none
  else
    match chars.span (· != ':') with
    | (value, []) =>
      match parseZ value with
      | some value => .ok (some (value, none))
      | none => malformed atom
    | (value, _ :: width) =>
      match parseZ value, parseZ width with
      | some value, some (.ofNat width) => .ok (some (value, some width))
      | _, _ => malformed atom

/-- Reads an atom like `bap_primus_lisp_word.ml`: `.ok none` is not a number and so a symbol, `?c` is the
8-bit code of one ASCII character, and an atom that starts like a number or a character but does not
parse is an error, not a symbol. -/
def readLiteral (atom : String) : Except String (Option (Int × Option Nat)) :=
  match atom.toList with
  | '?' :: [c] => if c.toNat < 128 then .ok (some (Int.ofNat c.toNat, some 8)) else malformed atom
  | '?' :: _ => malformed atom
  | chars => readNumeric atom chars

def parseInteger (atom : String) : Option (Int × Option Nat) :=
  match readLiteral atom with
  | .ok literal => literal
  | .error _ => none

end Bap.Primus.Literal
