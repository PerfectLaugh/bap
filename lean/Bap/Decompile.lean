import Bap.Bil.Syntax
import Bap.Core.Sexp

namespace Bap.Decompile

private def hex (value : Nat) : String := String.ofList (Nat.toDigits 16 value)

private def identifier (name : String) : String :=
  let rendered := String.ofList (name.toList.map fun c => if c.isAlphanum || c = '_' then c else '_')
  if rendered.isEmpty then "v" else rendered

private def varName (var : Bap.Var) : String :=
  identifier (var.name ++ if var.index = 0 then "" else s!"_{var.index}")

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
  | .slt => "<" | .sle => "<=" | .sgt => ">" | .sge => ">="
  | _ => ""

private def signedBinName : Bil.BinOp → Option String
  | .sdiv => some "sdiv"
  | .srem => some "srem"
  | .smod => some "smod"
  | .ashift => some "ashr"
  | _ => none

private def unName : Bil.UnOp → String
  | .neg => "-"
  | .not => "~"

private def castName : Bil.Cast → String
  | .low => "low"
  | .high => "high"
  | .signed => "signed"
  | .unsigned => "unsigned"

def exp : Bil.Exp → String
  | .int value => s!"0x{hex value.toNat}"
  | .var var => varName var
  | .load memory address endian size =>
    s!"read{size * 8}_{endianName endian}({exp memory}, {exp address})"
  | .store memory address value endian size =>
    s!"write{size * 8}_{endianName endian}({exp memory}, {exp address}, {exp value})"
  | .bin op left right =>
    match signedBinName op with
    | some name => s!"{name}({exp left}, {exp right})"
    | none => s!"({exp left} {binName op} {exp right})"
  | .un op value => s!"({unName op}{exp value})"
  | .cast kind width value => s!"{castName kind}({exp value}, {width})"
  | .letIn var value body => s!"let({varName var}, {exp value}, {exp body})"
  | .ite condition yes no => s!"({exp condition} ? {exp yes} : {exp no})"
  | .extract high low value => s!"extract({exp value}, {high}, {low})"
  | .concat left right => s!"concat({exp left}, {exp right})"
  | .unknown message _ => s!"unknown({quote message})"

private def indentation (level : Nat) : String := String.ofList (List.replicate level ' ')

def stmt (level : Nat) : Bil.Stmt → String
  | .move _ (.store memory address value endian size) =>
    s!"{indentation level}write{size * 8}_{endianName endian}({exp memory}, {exp address}, {exp value});"
  | .move var value => s!"{indentation level}{varName var} = {exp value};"
  | .jmp (.int target) => s!"{indentation level}goto loc_{hex target.toNat};"
  | .jmp target => s!"{indentation level}return {exp target};"
  | .special message => s!"{indentation level}special({quote message});"
  | .cpuExn number => s!"{indentation level}cpu_exception({number});"
  | .while condition body =>
    let body := body.map (stmt (level + 2))
    indentation level ++ "while (" ++ exp condition ++ ") {\n" ++
      String.intercalate "\n" body ++ "\n" ++ indentation level ++ "}"
  | .ifElse condition yes no =>
    let yes := yes.map (stmt (level + 2))
    let no := no.map (stmt (level + 2))
    let elsePart := if no.isEmpty then "" else
      " else {\n" ++ String.intercalate "\n" no ++ "\n" ++ indentation level ++ "}"
    indentation level ++ "if (" ++ exp condition ++ ") {\n" ++
      String.intercalate "\n" yes ++ "\n" ++ indentation level ++ "}" ++ elsePart

def program (code : Bil.Program) : String :=
  String.intercalate "\n" (code.map (stmt 2))

private def ctype : Typ → String
  | .imm 8 => "uint8_t"
  | .imm 16 => "uint16_t"
  | .imm 32 => "uint32_t"
  | .imm 64 => "uint64_t"
  | .imm _ => "uint64_t"
  | .mem _ _ => "uint8_t *"
  | _ => "void *"

def function (name : String) (params : List Bap.Var) (code : Bil.Program) : String :=
  let params := params.map fun var => s!"{ctype var.typ} {varName var}"
  let header := "void " ++ identifier name ++ "(" ++ String.intercalate ", " params ++ ") {"
  header ++ "\n" ++ program code ++ "\n}"

end Bap.Decompile
