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

/-- The declarations of a header that are prototypes: of what is between semicolons, what has parameters, but for the body of a
function, a type that `typedef` names, of a pointer to a function too, and what the preprocessor has, of lines that start with `#` and
those that a backslash at their end continues them into. -/
def headerDeclarations (input : String) : List String :=
  let input := String.ofList (stripComments input.toList)
  let (kept, _) := (input.splitOn "\n").foldl (init := ([], false)) fun (kept, continuing) line =>
    let directive := continuing || (trim line).startsWith "#"
    (if directive then kept else kept ++ [line], directive && (trim line).endsWith "\\")
  "\n".intercalate kept |>.splitOn ";" |>.map trim |>.filter fun declaration =>
    !declaration.isEmpty && declaration.contains '(' && !declaration.contains '{' && (words declaration).headD "" != "typedef"

/-- The prototypes of a header, of its `headerDeclarations`. -/
def parseHeader (input : String) : Except String (List Prototype) :=
  (headerDeclarations input).mapM parsePrototype

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

/-- Where the parameters of a function are by words alone: in the registers of the convention, as many as there are, and then on the
stack, each past the words of those before it there. This is `argumentLocations` of a convention of no ABI that it knows. -/
def wordLocations (abi : ABI.Convention) (prototype : Prototype) : List ABI.Location :=
  let types := prototype.params.map (·.typ)
  (List.range types.length).map fun index =>
    match abi.functionArguments[index]? with
    | some var => .register var
    | none =>
      .stack (abi.stackArgumentsStart + (((types.take index).drop abi.functionArguments.length).map (stackWords abi)).sum * (abi.wordSize / 8))

/-- What a parameter is, as an ABI passes it: of floating point, of `long double`, or of an integer, each of so many bytes. -/
private inductive Kind where
  | float (bytes : Nat)
  | longDouble
  | integer (bytes : Nat)
  deriving DecidableEq

/-- What a parameter of a type is, by its name without its qualifiers: what is of 64 bits takes two words on 32 bits. -/
private def kindOf (abi : ABI.Convention) (type : CType) : Kind :=
  let word := abi.wordSize / 8
  match type with
  | .pointer _ => .integer word
  | .named name =>
    let name := " ".intercalate ((words name).filter fun part => part != "const" && part != "volatile" && part != "register")
    if name == "float" then .float 4
    else if name == "double" then .float 8
    else if name == "long double" then .longDouble
    else if ["long long", "long long int", "signed long long", "unsigned long long", "unsigned long long int", "int64_t", "uint64_t",
        "off64_t", "loff_t"].contains name then .integer (max 8 word)
    else .integer word

/-- Where the arguments of a call are as far as `argumentLocations` has placed them: the next of the registers of integers and of
floating point, how far into the stack they are, and of ARM which halves of `D0` to `D7` are taken and whether one of floating point
went to the stack, after which none goes to them. -/
structure Placing where
  g : Nat := 0
  f : Nat := 0
  offset : Nat := 0
  singles : Array Bool := Array.replicate 16 false
  stacked : Bool := false

/-- Where one parameter of a function goes, the `index`th, after those before it, as `argumentLocations` has it. -/
def place (abi : ABI.Convention) (prototype : Prototype) (placing : Placing) (param : Parameter) (index : Nat) :
    ABI.Location × Placing := Id.run do
  let word := abi.wordSize / 8
  let start := abi.stackArgumentsStart
  let gprs := abi.functionArguments
  let fprs := abi.floatArguments
  let alignUp (value alignment : Nat) : Nat := (value + alignment - 1) / alignment * alignment
  let gpr (index : Nat) : ABI.Location := match gprs[index]? with
    | some var => .register var
    | none => .stack start
  let fpr (index : Nat) : ABI.Location := match fprs[index]? with
    | some var => .register var
    | none => .stack start
  let mut out : List ABI.Location := []
  let mut g := placing.g
  let mut f := placing.f
  let mut offset := placing.offset
  let mut singles := placing.singles
  let mut stacked := placing.stacked
  let kind := kindOf abi param.typ
  -- What goes on the stack, of `bytes` aligned to `alignment`, after what is there.
  let onStack (bytes alignment : Nat) (offset : Nat) : ABI.Location × Nat :=
    let at_ := alignUp offset (max alignment word)
    (.stack (start + at_), at_ + alignUp bytes word)
  match abi.arch with
  | .x86 =>
    let bytes := match kind with
      | .float bytes => bytes
      | .longDouble => 12
      | .integer bytes => bytes
    let (location, next) := onStack bytes 4 offset
    out := out ++ [location]
    offset := next
  | .x86_64 | .aarch64 =>
    let (registers, floats) := if abi.arch == .x86_64 then (6, 8) else (8, 8)
    match kind, abi.arch with
    | .longDouble, .x86_64 =>
      let (location, next) := onStack 16 16 offset
      out := out ++ [location]
      offset := next
    | .float _, _ | .longDouble, _ =>
      if f < floats then
        out := out ++ [fpr f]
        f := f + 1
      else
        let (location, next) := if kind == .longDouble then onStack 16 16 offset else onStack 8 8 offset
        out := out ++ [location]
        offset := next
    | .integer _, _ =>
      if g < registers then
        out := out ++ [gpr g]
        g := g + 1
      else
        let (location, next) := onStack 8 8 offset
        out := out ++ [location]
        offset := next
  | .riscv =>
    -- What isn't in a register of floating point is as an integer of its size; a `long double` of RV32 is by its address.
    let bytes := match kind with
      | .float bytes => bytes
      | .longDouble => if word == 8 then 16 else word
      | .integer bytes => bytes
    if (kind matches .float _) && f < 8 then
      out := out ++ [fpr f]
      f := f + 1
    else if bytes ≤ word then
      if g < 8 then
        out := out ++ [gpr g]
        g := g + 1
      else
        let (location, next) := onStack word word offset
        out := out ++ [location]
        offset := next
    else
      -- Of two words: in two registers, or in the last and the stack, or on the stack, aligned to them.
      if g < 8 then
        out := out ++ [gpr g]
        if g == 7 then offset := offset + word
        g := g + 2
      else
        let (location, next) := onStack bytes bytes offset
        out := out ++ [location]
        offset := next
  | .arm =>
    match kind with
    | .float 4 =>
      match (if stacked then none else (List.range 16).find? (!singles[·]!)) with
      | some half =>
        singles := singles.set! half true
        out := out ++ [.register ⟨s!"S{half}", .imm 32, 0, false⟩]
      | none =>
        stacked := true
        let (location, next) := onStack 4 4 offset
        out := out ++ [location]
        offset := next
    | .float _ | .longDouble =>
      match (if stacked then none else (List.range 8).find? fun pair => !singles[2 * pair]! && !singles[2 * pair + 1]!) with
      | some pair =>
        singles := (singles.set! (2 * pair) true).set! (2 * pair + 1) true
        out := out ++ [fpr pair]
      | none =>
        stacked := true
        let (location, next) := onStack 8 8 offset
        out := out ++ [location]
        offset := next
    | .integer bytes =>
      if bytes ≤ 4 then
        if g < 4 then
          out := out ++ [gpr g]
          g := g + 1
        else
          let (location, next) := onStack 4 4 offset
          out := out ++ [location]
          offset := next
      else
        let even := alignUp g 2
        if even + 2 ≤ 4 then
          out := out ++ [gpr even]
          g := even + 2
        else
          g := 4
          let (location, next) := onStack 8 8 offset
          out := out ++ [location]
          offset := next
  | .mips =>
    if word == 4 then
      -- The words of the area of the arguments, the first four of which are `R4` to `R7`.
      let bytes := match kind with
        | .float bytes => bytes
        | .longDouble => 8
        | .integer bytes => bytes
      let slot := if bytes == 8 then alignUp g 2 else g
      let leading := index < 2 && (prototype.params.take (index + 1)).all fun param =>
        match kindOf abi param.typ with
        | .float _ | .longDouble => true
        | .integer _ => false
      if leading then out := out ++ [fpr index]
      else if slot < 4 then out := out ++ [gpr slot]
      else out := out ++ [ABI.Location.stack (start + (slot - 4) * 4)]
      g := slot + bytes / 4
    else
      let slots := if kind == .longDouble then 2 else 1
      let slot := if slots == 2 then alignUp g 2 else g
      if slot < 8 then
        out := out ++ [if (kind matches .float _) then fpr slot else gpr slot]
      else out := out ++ [ABI.Location.stack (start + (slot - 8) * 8)]
      g := slot + slots
  | .powerpc =>
    if word == 4 then
      match kind with
      | .float _ | .longDouble =>
        if f < 8 then
          out := out ++ [fpr f]
          f := f + 1
        else
          let (location, next) := onStack 8 8 offset
          out := out ++ [location]
          offset := next
      | .integer bytes =>
        if bytes ≤ 4 then
          if g < 8 then
            out := out ++ [gpr g]
            g := g + 1
          else
            let (location, next) := onStack 4 4 offset
            out := out ++ [location]
            offset := next
        else
          let even := alignUp g 2
          if even + 2 ≤ 8 then
            out := out ++ [gpr even]
            g := even + 2
          else
            g := 8
            let (location, next) := onStack 8 8 offset
            out := out ++ [location]
            offset := next
    else
      -- Each has its doubleword, whether it is in a register or not.
      let isFloat := match kind with
        | .float _ | .longDouble => true
        | .integer _ => false
      if isFloat && f < 13 then
        out := out ++ [fpr f]
        f := f + 1
      else if g < 8 then out := out ++ [gpr g]
      else out := out ++ [ABI.Location.stack (start + (g - 8) * 8)]
      g := g + 1
  | .systemz =>
    match kind with
    | .float _ =>
      if f < 4 then
        out := out ++ [fpr f]
        f := f + 1
      else
        let (location, next) := onStack 8 8 offset
        out := out ++ [location]
        offset := next
    | .longDouble | .integer _ =>
      if g < 5 then
        out := out ++ [gpr g]
        g := g + 1
      else
        let (location, next) := onStack 8 8 offset
        out := out ++ [location]
        offset := next
  | .unknown => out := out ++ [gpr index]
  pure (out.headD (.stack start), { g, f, offset, singles, stacked })

/-- Each parameter of `params`, of the indices from `index`, where `place` puts it after those before it. -/
def placeAll (abi : ABI.Convention) (prototype : Prototype) : Placing → List Parameter → Nat → List ABI.Location
  | _, [], _ => []
  | placing, param :: rest, index =>
    let (location, next) := place abi prototype placing param index
    location :: placeAll abi prototype next rest (index + 1)

/-- Where the parameters of a function are when it is called, as the ABI of the convention has them: what is of integers in the
registers of the convention and what is of floating point in those of it, as many as there are, and then on the stack, each where those
before it leave it, aligned as it is. Of each architecture:
- i386: all on the stack, of a `long double` of 12 bytes.
- x86-64: a `long double` on the stack, aligned to 16.
- AArch64: floating point, `long double` too, in `V0` to `V7`.
- RISC-V: floating point in `FA0` to `FA7`, and then as an integer; of RV64, a `long double` in two registers, and of RV32 by its address.
- ARM, of hard floating point: a `float` in a half of `D0` to `D7` that is free, back-filled, and a `double` or `long double` in a whole
  one; of 64 bits of integers, an even pair of registers or 8 bytes of the stack aligned to 8, as of a `double` there.
- MIPS o32: the first two of floating point, of no integer before them, in `F12` and `F14`, and the rest as integers, in the words of
  the area of the arguments, of which the first four are registers; of n64, each argument in its place, of `F12` on or of `R4` on.
- PowerPC: floating point in `F1` on; of 32 bits, 64 bits of integers in a pair of registers that starts at an odd one; of 64 bits,
  each argument has a doubleword of the area of the arguments, of which the first eight are registers.
- s390x: floating point in `F0`, `F2`, `F4` and `F6`, and a `long double` by its address.
Of a convention of no ABI that it knows, `wordLocations`. -/
def argumentLocations (abi : ABI.Convention) (prototype : Prototype) : List ABI.Location :=
  if abi.arch == .unknown then wordLocations abi prototype else placeAll abi prototype {} prototype.params 0

end Bap.API
