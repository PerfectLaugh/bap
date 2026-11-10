import Bap.ABI

namespace Bap.API

inductive CType where
  | named (name : String)
  | pointer (type : CType)
  deriving DecidableEq, Repr

structure Parameter where
  name : String
  typ : CType
  deriving DecidableEq, Repr

structure Prototype where
  name : String
  result : CType
  params : List Parameter
  variadic : Bool := false
  deriving DecidableEq, Repr

private def trim (input : String) : String := (String.trimAscii input).copy
private def words (input : String) : List String := (trim input).splitOn " " |>.filter fun word => !word.isEmpty
private def unwords (inputs : List String) : String := String.intercalate " " inputs
private def identChar (c : Char) : Bool := c.isAlphanum || c = '_'

private def countChar (value : Char) : String → Nat
  | input => input.toList.count value

private def pointers : Nat → CType → CType
  | 0, base => base
  | count + 1, base => .pointer (pointers count base)

private def parseType (input : String) : Except String CType := do
  let count := countChar '*' input
  let base := input.toList.filter (· != '*') |> String.ofList |> trim
  if base.isEmpty then
    .error "C type has no base name"
  else
    .ok (pointers count (.named base))

/-- Of text after a `(`, what is before the `)` that closes it, past those that close others that open in it. -/
private def untilClose (input : String) : String :=
  let rec go : List Char → Nat → List Char
    | [], _ => []
    | ')' :: _, 0 => []
    | ')' :: rest, depth + 1 => ')' :: go rest depth
    | '(' :: rest, depth => '(' :: go rest (depth + 1)
    | c :: rest, depth => c :: go rest depth
  String.ofList (go input.toList 0)

/-- The pieces of text between the commas that no parenthesis is open across, as of the parameters of a function, of which one may be
a pointer to a function with parameters of its own. -/
private def splitTop (input : String) : List String :=
  let rec go : List Char → Nat → List Char → List String
    | [], _, piece => [String.ofList piece.reverse]
    | ',' :: rest, 0, piece => String.ofList piece.reverse :: go rest 0 []
    | '(' :: rest, depth, piece => go rest (depth + 1) ('(' :: piece)
    | ')' :: rest, depth, piece => go rest (depth - 1) (')' :: piece)
    | c :: rest, depth, piece => go rest depth (c :: piece)
  go input.toList 0 []

/-- A name that is an identifier, or none. -/
private def identifier (candidate : String) : String :=
  if !candidate.isEmpty && candidate.all identChar then candidate else ""

/-- What a parameter is that is neither an array nor a pointer to a function. -/
private def parsePlain (input : String) : Except String Parameter := do
  let tokens := words input
  match tokens with
  | [] => .error "empty C parameter"
  | [single] =>
    if single.all identChar then
      .ok ⟨"", .named single⟩
    else
      .ok ⟨"", ← parseType input⟩
  | _ =>
    let token := tokens.getLast!
    let stars := token.toList.takeWhile (· == '*') |> String.ofList
    let last := token.toList.dropWhile (· == '*') |> String.ofList
    if !last.isEmpty && last.all identChar then
      let typeTokens := tokens.take (tokens.length - 1) ++ [stars]
      .ok ⟨last, ← parseType (unwords typeTokens)⟩
    else
      .ok ⟨"", ← parseType input⟩

/-- A name of a type that isn't empty. -/
private def orFunction (name : String) : String := if name.isEmpty then "function" else name

/-- A pointer to a function, `int (*name)(int, char *)`: its name is in its first parentheses, and its type is named by the rest,
`int (*)(int, char *)`. -/
private def functionPointerName (input : String) : String :=
  String.ofList ((untilClose ((input.splitOn "(").getD 1 "")).toList.filter identChar)

private def functionPointerType (input : String) : String :=
  let pieces := input.splitOn "("
  s!"{trim (pieces.headD "")} (*)({trim (untilClose ("(".intercalate (pieces.drop 2)))})"

private def parseFunctionPointer (input : String) : Parameter :=
  ⟨identifier (functionPointerName input), .pointer (.named (orFunction (functionPointerType input)))⟩

/-- A parameter: a pointer to a function; an array, `char name[16]`, which C takes for a pointer to what it holds; or what is neither. -/
private def parseParameter (input : String) : Except String Parameter := do
  if input.contains '(' then .ok (parseFunctionPointer input)
  else if input.contains '[' then
    let element ← parsePlain ((input.splitOn "[").headD input)
    .ok { element with typ := .pointer element.typ }
  else parsePlain input

private def parseParameters (input : String) : Except String (List Parameter × Bool) := do
  let input := trim input
  if input.isEmpty || input = "void" then
    .ok ([], false)
  else
    let parts := splitTop input |>.map trim |>.filter fun part => !part.isEmpty
    let variadic := parts.contains "..."
    let parts := parts.filter fun part => part != "..."
    let params ← parts.mapM parseParameter
    .ok (params, variadic)

def parsePrototype (input : String) : Except String Prototype := do
  let input := trim input
  -- What is before the first `(` is the result and the name, and the parameters go to the `)` that closes it.
  match input.splitOn "(" with
  | signature :: first :: others =>
    let rest := "(".intercalate (first :: others)
    let signatureWords := words signature
    if signatureWords.length < 2 then
      .error "C prototype has no function name or result type"
    else
      let token := signatureWords.getLast!
      let stars := token.toList.takeWhile (· == '*') |> String.ofList
      let name := token.toList.dropWhile (· == '*') |> String.ofList
      if name.isEmpty || !name.all identChar then
        .error "invalid C function name"
      else
        let result := signatureWords.take (signatureWords.length - 1) ++ [stars]
        let arguments := untilClose rest
        let (params, variadic) ← parseParameters arguments
        .ok ⟨name, ← parseType (unwords result), params, variadic⟩
  | _ => .error "C prototype must have a parameter list"

private def stripLineComment : List Char → List Char
  | [] => []
  | '\n' :: rest => '\n' :: rest
  | _ :: rest => stripLineComment rest

private def stripBlockComment : List Char → List Char
  | [] => []
  | '*' :: '/' :: rest => rest
  | _ :: rest => stripBlockComment rest

private def stripCommentsAux : Nat → List Char → List Char
  | 0, _ => []
  | fuel + 1, input =>
    match input with
    | [] => []
    | '/' :: '*' :: rest => ' ' :: stripCommentsAux fuel (stripBlockComment rest)
    | '/' :: '/' :: rest => stripCommentsAux fuel (stripLineComment rest)
    | c :: rest => c :: stripCommentsAux fuel rest

private def stripComments (input : List Char) : List Char :=
  stripCommentsAux (input.length + 1) input

def parseHeader (input : String) : Except String (List Prototype) := do
  let input := String.ofList (stripComments input.toList)
  let declarations := input.splitOn ";" |>.map trim |>.filter fun declaration =>
    !declaration.isEmpty && declaration.contains '(' && !declaration.contains '{'
  declarations.mapM parsePrototype

def load (path : String) : IO (List Prototype) := do
  let input ← IO.FS.readFile path
  match parseHeader input with
  | .ok prototypes => pure prototypes
  | .error error => throw <| IO.userError error

/-- How many words of the stack a parameter of a type takes: on 32 bits, two of what is of 64 bits, `long long` or `double`, and three of
the `long double` of i386, as cdecl has them; and otherwise one. -/
def stackWords (abi : ABI.Convention) (type : CType) : Nat :=
  if abi.wordSize != 32 then 1 else
  match type with
  | .pointer _ => 1
  | .named name =>
    let name := " ".intercalate (words name)
    if name == "long double" then 3
    else if ["long long", "long long int", "signed long long", "unsigned long long", "unsigned long long int", "double", "int64_t",
        "uint64_t", "off64_t", "loff_t"].contains name then 2
    else 1

/-- Where the parameters of a function are when it is called: in the registers of the convention, as many as there are, and then on the
stack, each past the words of those before it there. -/
def argumentLocations (abi : ABI.Convention) (prototype : Prototype) : List ABI.Location :=
  let types := prototype.params.map (·.typ)
  (List.range types.length).map fun index =>
    match abi.functionArguments[index]? with
    | some var => .register var
    | none =>
      .stack (abi.stackArgumentsStart + (((types.take index).drop abi.functionArguments.length).map (stackWords abi)).sum * (abi.wordSize / 8))

end Bap.API
