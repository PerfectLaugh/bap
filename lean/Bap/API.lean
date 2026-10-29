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

private def parseParameter (input : String) : Except String Parameter := do
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

private def parseParameters (input : String) : Except String (List Parameter × Bool) := do
  let input := trim input
  if input.isEmpty || input = "void" then
    .ok ([], false)
  else
    let parts := input.splitOn "," |>.map trim |>.filter fun part => !part.isEmpty
    let variadic := parts.contains "..."
    let parts := parts.filter fun part => part != "..."
    let params ← parts.mapM parseParameter
    .ok (params, variadic)

def parsePrototype (input : String) : Except String Prototype := do
  let input := trim input
  let halves := input.splitOn "("
  match halves with
  | [signature, rest] =>
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
        let arguments := rest.splitOn ")" |>.head!
        let (params, variadic) ← parseParameters arguments
        .ok ⟨name, ← parseType (unwords result), params, variadic⟩
  | _ => .error "C prototype must contain one parameter list"

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
    | '/' :: '*' :: rest => stripCommentsAux fuel (stripBlockComment rest)
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

def argumentLocations (abi : ABI.Convention) (prototype : Prototype) : List ABI.Location :=
  (List.range prototype.params.length).map (ABI.argumentLocation abi)

end Bap.API
