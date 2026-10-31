import Bap.Bil.Syntax
import Bap.Core.Sexp

namespace Bap.Decompile

private def hex (value : Nat) : String := String.ofList (Nat.toDigits 16 value)

/-- `_0x` opens the escape of a character, closed by `_`; `_0v` opens a variable index and `_0t`
a variable's type. All three are escaped when they occur literally. -/
private def escape (c : Char) : List Char :=
  ['_', '0', 'x'] ++ Nat.toDigits 16 c.toNat ++ ['_']

private def escapeChars : List Char → List Char
  | [] => []
  | '_' :: '0' :: 'x' :: rest => escape '_' ++ '0' :: 'x' :: escapeChars rest
  | '_' :: '0' :: 'v' :: rest => escape '_' ++ '0' :: 'v' :: escapeChars rest
  | '_' :: '0' :: 't' :: rest => escape '_' ++ '0' :: 't' :: escapeChars rest
  | c :: rest => if c.isAlphanum || c = '_' then c :: escapeChars rest else escape c ++ escapeChars rest

/-- The keywords of C up to C23, with the common `asm` and `fortran` extensions. -/
private def keywords : List String := [
  "alignas", "alignof", "auto", "bool", "break", "case", "char", "const", "constexpr", "continue",
  "default", "do", "double", "else", "enum", "extern", "false", "float", "for", "goto", "if",
  "inline", "int", "long", "nullptr", "register", "restrict", "return", "short", "signed",
  "sizeof", "static", "static_assert", "struct", "switch", "thread_local", "true", "typedef",
  "typeof", "typeof_unqual", "union", "unsigned", "void", "volatile", "while",
  "_Alignas", "_Alignof", "_Atomic", "_BitInt", "_Bool", "_Complex", "_Decimal128", "_Decimal32",
  "_Decimal64", "_Generic", "_Imaginary", "_Noreturn", "_Static_assert", "_Thread_local",
  "asm", "fortran"
]

/-- A valid C identifier, distinct for distinct names and equal to `name` if it already is one. -/
private def identifier (name : String) : String :=
  String.ofList <| match name.toList with
    | [] => ['_', '0', 'x', '_']
    | c :: rest =>
      if c.isDigit || keywords.contains name then escape c ++ escapeChars rest
      else escapeChars (c :: rest)

private def typeCode : Typ → String
  | .unknown => "u"
  | .unit => "n"
  | .mem addressWidth valueWidth => s!"m{addressWidth}x{valueWidth}"
  | .imm width => s!"i{width}"

/-- The name of `var` where `scope` is every variable in sight. Most code has one type for a name,
so type and virtuality appear only to tell apart variables that would otherwise look the same. -/
private def varName (scope : List Bap.Var) (var : Bap.Var) : String :=
  let plain := identifier var.name ++ if var.index = 0 then "" else s!"_0v{var.index}"
  if scope.any fun other => other.name = var.name && other.index = var.index && other != var then
    plain ++ s!"_0t{typeCode var.typ}" ++ if var.isVirtual then "v" else ""
  else
    plain

private def quote (value : String) : String := Sexp.render (.atom value)

private def endianName : Endian → String
  | .little => "le"
  | .big => "be"

private def binName : Bil.BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*"
  | .div => "/" | .rem => "%"
  | .lshift => "<<" | .rshift => ">>"
  | .and => "&" | .or => "|" | .xor => "^"
  | .eq => "==" | .neq => "!="
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | _ => ""

private def signedBinName : Bil.BinOp → Option String
  | .sdiv => some "sdiv"
  | .srem => some "srem"
  | .smod => some "smod"
  | .ashift => some "ashr"
  | .slt => some "slt"
  | .sle => some "sle"
  | .sgt => some "sgt"
  | .sge => some "sge"
  | _ => none

private def unName : Bil.UnOp → String
  | .neg => "-"
  | .not => "~"

private def castName : Bil.Cast → String
  | .low => "low"
  | .high => "high"
  | .signed => "signed"
  | .unsigned => "unsigned"

private def ctype : Typ → String
  | .imm 8 => "uint8_t"
  | .imm 16 => "uint16_t"
  | .imm 32 => "uint32_t"
  | .imm 64 => "uint64_t"
  | .imm width => s!"unsigned _BitInt({width})"
  | .mem _ _ => "uint8_t *"
  | _ => "void *"

def expIn (scope : List Bap.Var) : Bil.Exp → String
  | .int value => s!"0x{hex value.toNat}"
  | .var var => varName scope var
  | .load memory address endian size =>
    s!"read{size * 8}_{endianName endian}({expIn scope memory}, {expIn scope address})"
  | .store memory address value endian size =>
    s!"write{size * 8}_{endianName endian}({expIn scope memory}, {expIn scope address}, {expIn scope value})"
  | .bin op left right =>
    match signedBinName op with
    | some name => s!"{name}({expIn scope left}, {expIn scope right})"
    | none => s!"({expIn scope left} {binName op} {expIn scope right})"
  | .un op value => s!"({unName op}{expIn scope value})"
  | .cast kind width value => s!"{castName kind}({expIn scope value}, {width})"
  | .letIn var value body => s!"let({varName scope var}, {expIn scope value}, {expIn scope body})"
  | .ite condition yes no => s!"({expIn scope condition} ? {expIn scope yes} : {expIn scope no})"
  | .extract high low value => s!"extract({expIn scope value}, {high}, {low})"
  | .concat left right => s!"concat({expIn scope left}, {expIn scope right})"
  | .unknown message typ => s!"unknown({quote message}, {ctype typ})"

private def expVars : Bil.Exp → List Bap.Var
  | .var var => [var]
  | .load memory address _ _ => expVars memory ++ expVars address
  | .store memory address value _ _ => expVars memory ++ expVars address ++ expVars value
  | .bin _ left right | .concat left right => expVars left ++ expVars right
  | .un _ value | .cast _ _ value | .extract _ _ value => expVars value
  | .letIn var value body => var :: expVars value ++ expVars body
  | .ite condition yes no => expVars condition ++ expVars yes ++ expVars no
  | .int _ | .unknown _ _ => []

def exp (value : Bil.Exp) : String := expIn (expVars value).eraseDups value

private def indentation (level : Nat) : String := String.ofList (List.replicate level ' ')

def stmtIn (scope : List Bap.Var) (level : Nat) : Bil.Stmt → String
  | .move var (.store memory address value endian size) =>
    let write := s!"write{size * 8}_{endianName endian}({expIn scope memory}, {expIn scope address}, {expIn scope value});"
    let inPlace : Bool := match memory with
      | .var source => source = var
      | _ => false
    if inPlace then s!"{indentation level}{write}" else s!"{indentation level}{varName scope var} = {write}"
  | .move var value => s!"{indentation level}{varName scope var} = {expIn scope value};"
  | .jmp (.int target) => s!"{indentation level}goto loc_{hex target.toNat};"
  | .jmp target => s!"{indentation level}goto *{expIn scope target};"
  | .special message => s!"{indentation level}special({quote message});"
  | .cpuExn number => s!"{indentation level}cpu_exception({number});"
  | .while condition body =>
    let body := body.map (stmtIn scope (level + 2))
    indentation level ++ "while (" ++ expIn scope condition ++ ") {\n" ++
      String.intercalate "\n" body ++ "\n" ++ indentation level ++ "}"
  | .ifElse condition yes no =>
    let yes := yes.map (stmtIn scope (level + 2))
    let no := no.map (stmtIn scope (level + 2))
    let elsePart := if no.isEmpty then "" else
      " else {\n" ++ String.intercalate "\n" no ++ "\n" ++ indentation level ++ "}"
    indentation level ++ "if (" ++ expIn scope condition ++ ") {\n" ++
      String.intercalate "\n" yes ++ "\n" ++ indentation level ++ "}" ++ elsePart

private def stmtVars : Bil.Stmt → List Bap.Var
  | .move var value => var :: expVars value
  | .jmp target => expVars target
  | .special _ | .cpuExn _ => []
  | .while condition body => expVars condition ++ body.flatMap stmtVars
  | .ifElse condition yes no => expVars condition ++ yes.flatMap stmtVars ++ no.flatMap stmtVars

def stmt (level : Nat) (statement : Bil.Stmt) : String :=
  stmtIn (stmtVars statement).eraseDups level statement

def program (code : Bil.Program) : String :=
  String.intercalate "\n" (code.map (stmtIn (code.flatMap stmtVars).eraseDups 2))

def function (name : String) (params : List Bap.Var) (code : Bil.Program) : String :=
  let scope := (params ++ code.flatMap stmtVars).eraseDups
  let params := params.map fun var => s!"{ctype var.typ} {varName scope var}"
  let header := "void " ++ identifier name ++ "(" ++ String.intercalate ", " params ++ ") {"
  header ++ "\n" ++ String.intercalate "\n" (code.map (stmtIn scope 2)) ++ "\n}"

end Bap.Decompile
