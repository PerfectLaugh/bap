import Bap.Core.Assoc
import Bap.Core.Sexp
import Bap.Bil.Syntax
import Bap.Bil.Eval
import Bap.LLVM
import Std.Data.HashMap

namespace Bap.Primus.Semantics

mutual
  inductive CExp where
    | value (value : Value)
    | local (slot : Nat)
    | global (slot : Nat)
    | primitive (operation : Nat) (args : List CExp)
    | apply (callable : CExp) (args : List CExp)
    | ifElse (condition : CExp) (yes no : List CExp)
    | letIn (value body : CExp)
    | sequence (forms : List CExp)

  inductive Callable where
    | function (params : List String) (body : List Sexp) (env : List (String × Value))
    | compiled (params : List String) (body : List CExp) (env : List (String × Value))
    | macro (params : List String) (body : List Sexp)
    | primitive (name : String)

  inductive Value where
    | unit
    | int (value : BitVec 64)
    | bil (width : Nat) (value : Bil.Exp)
    | bool (value : Bool)
    | register (name : String) (width baseWidth : Nat)
    | symbol (name : String)
    | list (items : List Value)
    | callable (value : Callable)
end

abbrev Locals := List (String × Value)
abbrev Globals := List (String × Value)

structure Environment where
  globals : Globals
  operations : Std.HashMap String Callable
  opcodes : Std.HashMap Nat Callable := {}
  registers : Std.HashMap Nat Value := {}
  signExtendedOpcodes : List Nat := []
  relativeOpcodes : List Nat := []

namespace Environment

def ofGlobals (globals : Globals) : Environment :=
  let operations := globals.reverse.foldl (init := ({} : Std.HashMap String Callable)) fun result binding =>
    match binding.2 with
    | .callable callable => result.insert binding.1 callable
    | _ => result
  { globals, operations }

def ofMachine (globals : Globals) (opcodes : List (Nat × Callable))
    (registers : List (Nat × Value)) : Environment :=
  let base := ofGlobals globals
  { base with
    opcodes := opcodes.reverse.foldl (init := {}) fun result binding => result.insert binding.1 binding.2
    registers := registers.reverse.foldl (init := {}) fun result binding => result.insert binding.1 binding.2 }

end Environment

structure Context where
  bits : Nat := 64
  pc : Nat := 0
  nextPc : Nat := 0
  endian : Endian := .little
  memory : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩

structure State where
  globals : Globals := []
  code : Bil.Program := []
  nextTemp : Nat := 0

private def primitiveNames : List String :=
  ["+", "-", "*", "/", "s/", "mod", "=", "/=", "<", "<=", ">", ">=", "not", "list",
    "cons", "car", "cdr", "length", "null?", "list?", "logand", "logor", "logxor",
    "bitand", "bitor", "bitxor", "lnot", "lshift", "rshift", "arshift", "extract",
    "select", "concat", "cast-low", "cast-high", "cast-signed", "cast-unsigned",
    "word-width", "set", "set$", "set-symbol-value", "alias-base-register", "symbol", "empty",
    "load-bits", "load-byte", "load-hword", "load-word", "store-word", "store-byte", "exec-addr", "intrinsic",
    "get-program-counter", "get-current-program-counter", "get-next-program-counter",
    "is-zero", "non-zero", "neg", "s<", "s<=", "s>", "s>=", "replicate", "clz"]

private def lookup (name : String) (locals : Locals) (globals : Globals) : Except String Value :=
  let primitiveName := if name.startsWith "core:" then (name.drop 5).toString else name
  if primitiveName = "replicate" then .ok (.callable (.primitive "replicate"))
  else
    match Assoc.get name locals with
    | some value => .ok value
    | none =>
      match Assoc.get name globals with
      | some value => .ok value
      | none =>
        if primitiveNames.contains primitiveName then .ok (.callable (.primitive primitiveName))
        else .error s!"unknown Primus symbol {name}"

private def parseBasedNat (digits : String) (base : Nat) : Option Nat :=
  digits.toList.foldlM (fun value c => do
    let lower := c.toLower
    let digit := if c.isDigit then c.toNat - '0'.toNat
      else if lower ≥ 'a' && lower ≤ 'f' then lower.toNat - 'a'.toNat + 10
      else base
    if digit < base then some (value * base + digit) else none) 0

private def parseInteger (atom : String) : Option (Int × Option Nat) :=
  let (value, width) := match atom.splitOn ":" with
    | [value, width] => (value, width.toNat?)
    | _ => (atom, none)
  let value := if value.startsWith "0x" || value.startsWith "0X" then
    (parseBasedNat (value.drop 2).toString 16).map Int.ofNat
  else if value.startsWith "0b" || value.startsWith "0B" then
    (parseBasedNat (value.drop 2).toString 2).map Int.ofNat
  else value.toInt?
  value.map fun value => (value, width)

private def atomValue (atom : String) : Value :=
  if atom = "true" then .bool true
  else if atom = "false" then .bool false
  else match parseInteger atom with
    | some (value, some width) => .bil width (.int (BitVec.ofInt width value))
    | some (value, none) => .int (BitVec.ofInt 64 value)
    | none => .symbol atom

private def expectBil (context : Context) : Value → Except String (Nat × Bil.Exp)
  | .int value => .ok (context.bits, .int (BitVec.ofNat context.bits value.toNat))
  | .bil width value => .ok (width, value)
  | .bool value => .ok (1, .int (BitVec.ofNat 1 value.toNat))
  | .register name width baseWidth =>
    if name = "XZR" then .ok (width, .int (BitVec.ofNat width 0))
    else
      let var : Bap.Var := ⟨name, .imm baseWidth, 0, false⟩
      .ok (width, if width = baseWidth then .var var else .cast .low width (.var var))
  | _ => .error "expected a Primus bitvector"

private def expectNat : Value → Except String Nat
  | .int value => .ok value.toNat
  | .bil _ value =>
    match Bil.evalExp [] value with
    | .ok (.bits value) => .ok value.toNat
    | _ => .error "expected a statically known Primus integer"
  | _ => .error "expected a statically known Primus integer"

private def truth : Value → Except String (Option Bool)
  | .bool value => .ok (some value)
  | .bil _ value =>
    match Bil.evalExp [] value with
    | .ok (.bits value) => .ok (some (value != 0))
    | _ => .ok none
  | .int value => .ok (some (value != 0))
  | .register .. => .ok none
  | _ => .error "expected a Primus condition"

private def condition (context : Context) (value : Value) : Except String Bil.Exp := do
  let (width, value) ← expectBil context value
  if width = 1 then .ok value else .error "Primus condition is not one bit"

private def extend (width : Nat) (value : Bil.Exp) : Bil.Exp := .cast .unsigned width value

private def binary (context : Context) (op : Bil.BinOp) (args : List Value) :
    Except String Value := do
  let values ← args.mapM (expectBil context)
  match values with
  | [] => .error "Primus arithmetic expects an argument"
  | (firstWidth, first) :: rest =>
    let width := values.foldl (fun width value => max width value.1) firstWidth
    let result ← rest.foldlM (init := extend width first) fun left (_, right) =>
      .ok (Bil.Exp.bin op left (extend width right))
    .ok (.bil width result)

private def compare (context : Context) (op : Bil.BinOp) (args : List Value) :
    Except String Value := do
  match args with
  | [.symbol left, .symbol right] =>
    if op = .eq || op = .neq then
      .ok (.bool ((left = right) = (op = .eq)))
    else .error "symbol comparison only supports equality"
  | [left, right] =>
    let (leftWidth, left) ← expectBil context left
    let (rightWidth, right) ← expectBil context right
    let width := max leftWidth rightWidth
    .ok (.bil 1 (.bin op (extend width left) (extend width right)))
  | _ => .error "Primus comparison expects two arguments"

private def unaryNot (context : Context) (args : List Value) : Except String Value := do
  match args with
  | [value] =>
    let (width, value) ← expectBil context value
    .ok (.bil width (.un .not value))
  | _ => .error "not expects one argument"

private def leadingZeros (context : Context) (args : List Value) : Except String Value := do
  match args with
  | [value] =>
    let (width, value) ← expectBil context value
    let rec leading (index : Nat) : Bil.Exp :=
      if index ≥ width then .int (BitVec.ofNat width width)
      else
        let bit := width - 1 - index
        .ite (.extract bit bit value) (.int (BitVec.ofNat width index)) (leading (index + 1))
    .ok (.bil width (leading 0))
  | _ => .error "clz expects one argument"

private def shift (context : Context) (op : Bil.BinOp) (args : List Value) : Except String Value := do
  match args with
  | [value, amount] =>
    let (width, value) ← expectBil context value
    let (amountWidth, amount) ← expectBil context amount
    let amount := if amountWidth = width then amount else .cast .unsigned width amount
    .ok (.bil width (.bin op value amount))
  | _ => .error "Primus shift expects two arguments"

private def cast (context : Context) (kind : Bil.Cast) (args : List Value) : Except String Value := do
  match args with
  | [width, value] =>
    let width ← expectNat width
    let (sourceWidth, value) ← expectBil context value
    match kind with
    | .low =>
      if width > sourceWidth then .ok (.bil width (.cast .unsigned width value))
      else .ok (.bil width (.cast .low width value))
    | .high =>
      if width = 0 || width > sourceWidth then .error "invalid Primus high cast"
      else .ok (.bil width (.cast .high width value))
    | _ => .ok (.bil width (.cast kind width value))
  | _ => .error "Primus cast expects width and value"

private def widthOf (_context : Context) : Value → Except String Nat
  | .int _ => .ok 64
  | .bil width _ => .ok width
  | .bool _ => .ok 1
  | .register _ width _ => .ok width
  | _ => .error "word-width expects a bitvector"

private def valueTag : Value → String
  | .unit => "unit"
  | .int _ => "integer"
  | .bil width _ => s!"BIL({width})"
  | .bool _ => "boolean"
  | .register name _ _ => s!"register({name})"
  | .symbol name => s!"symbol({name})"
  | .list _ => "list"
  | .callable _ => "callable"

private def assignRegister (context : Context) (name : String) (width baseWidth : Nat)
    (value : Value) : Except String Bil.Program := do
  if name = "XZR" then return []
  if width != baseWidth then
    throw s!"direct writes to subregisters must use the target's alias operation: {name} width={width} base={baseWidth}"
  let (valueWidth, value) ← expectBil context value
  if valueWidth != width then throw s!"Primus assignment width mismatch: {width} versus {valueWidth}"
  return [.move ⟨name, .imm width, 0, false⟩ value]

private def assign (context : Context) (destination value : Value) : Except String Bil.Program := do
  match destination with
  | .register name width baseWidth => assignRegister context name width baseWidth value
  | _ => throw s!"Primus assignment destination is not a register: {valueTag destination}"

private def emit (state : State) (code : Bil.Program) : State := { state with code := state.code ++ code }

private def loadMemory (context : Context) (bits : Nat) (args : List Value) : Except String Value := do
  match args with
  | [address] =>
    if bits % 8 != 0 then throw "Primus memory access is not byte-sized"
    let (addressWidth, address) ← expectBil context address
    if addressWidth != context.bits then throw "Primus memory address has the wrong width"
    .ok (.bil bits (.load (.var context.memory) address context.endian (bits / 8)))
  | _ => .error "Primus load expects an address"

private def storeMemory (context : Context) (args : List Value) : Except String Bil.Program := do
  match args with
  | [address, value] =>
    let (addressWidth, address) ← expectBil context address
    let (valueWidth, value) ← expectBil context value
    if addressWidth != context.bits then throw "Primus memory address has the wrong width"
    if valueWidth % 8 != 0 then throw "Primus store is not byte-sized"
    return [.move context.memory (.store (.var context.memory) address value context.endian (valueWidth / 8))]
  | _ => throw "Primus store expects address and value"

private def valueOnly (value : Value) : Except String (Value × Bil.Program) := pure (value, [])

private def applyPrimitive (context : Context) (name : String) (args : List Value) :
    Except String (Value × Bil.Program) := do
  match name with
  | "+" => valueOnly (← binary context .add args)
  | "*" => valueOnly (← binary context .mul args)
  | "-" =>
    match args with
    | [value] =>
      let (width, value) ← expectBil context value
      valueOnly (.bil width (.un .neg value))
    | _ => valueOnly (← binary context .sub args)
  | "neg" =>
    match args with
    | [value] =>
      let (width, value) ← expectBil context value
      valueOnly (.bil width (.un .neg value))
    | _ => throw "neg expects one argument"
  | "/" => valueOnly (← binary context .div args)
  | "s/" => valueOnly (← binary context .sdiv args)
  | "mod" => valueOnly (← binary context .smod args)
  | "=" => valueOnly (← compare context .eq args)
  | "/=" => valueOnly (← compare context .neq args)
  | "<" => valueOnly (← compare context .lt args)
  | "<=" => valueOnly (← compare context .le args)
  | ">" => valueOnly (← compare context .gt args)
  | ">=" => valueOnly (← compare context .ge args)
  | "s<" => valueOnly (← compare context .slt args)
  | "s<=" => valueOnly (← compare context .sle args)
  | "s>" => valueOnly (← compare context .sgt args)
  | "s>=" => valueOnly (← compare context .sge args)
  | "not" | "lnot" => valueOnly (← unaryNot context args)
  | "clz" => valueOnly (← leadingZeros context args)
  | "logand" | "bitand" => valueOnly (← binary context .and args)
  | "logor" | "bitor" => valueOnly (← binary context .or args)
  | "logxor" | "bitxor" => valueOnly (← binary context .xor args)
  | "lshift" => valueOnly (← shift context .lshift args)
  | "rshift" => valueOnly (← shift context .rshift args)
  | "arshift" => valueOnly (← shift context .ashift args)
  | "cast-low" => valueOnly (← cast context .low args)
  | "cast-high" => valueOnly (← cast context .high args)
  | "cast-signed" => valueOnly (← cast context .signed args)
  | "cast-unsigned" => valueOnly (← cast context .unsigned args)
  | "word-width" =>
    match args with
    | [] => valueOnly (.int (BitVec.ofNat 64 context.bits))
    | [value] => valueOnly (.int (BitVec.ofNat 64 (← widthOf context value)))
    | _ => throw "word-width expects zero or one arguments"
  | "extract" =>
    match args with
    | [high, low, value] =>
      let high ← expectNat high
      let low ← expectNat low
      let (width, value) ← expectBil context value
      if high < low || high ≥ width then throw "invalid Primus extraction"
      valueOnly (.bil (high - low + 1) (.extract high low value))
    | _ => throw "extract expects high, low, and value"
  | "select" =>
    match args with
    | [bit, value] =>
      let bit ← expectNat bit
      let (width, value) ← expectBil context value
      if bit ≥ width then throw "invalid Primus bit selection"
      valueOnly (.bil 1 (.extract bit bit value))
    | _ => throw "select expects bit and value"
  | "concat" =>
    match args with
    | first :: rest =>
      let (width, first) ← expectBil context first
      let (width, concatenated) ← rest.foldlM (init := (width, first)) fun current value => do
        let (rightWidth, right) ← expectBil context value
        .ok (current.1 + rightWidth, Bil.Exp.concat current.2 right)
      valueOnly (.bil width concatenated)
    | [] => throw "concat expects at least one value"
  | "replicate" =>
    match args with
    | [value, count] =>
      let count ← expectNat count
      let (width, value) ← expectBil context value
      if count = 0 then throw "Primus replicate count must be positive"
      else
        let repeated := (List.range (count - 1)).foldl (init := value) fun result _ =>
          .concat result value
        valueOnly (.bil (width * count) repeated)
    | _ => throw "replicate expects a value and count"
  | "set" | "set$" | "set-symbol-value" =>
    match args with
    | [destination, value] => pure (value, ← assign context destination value)
    | _ => throw "set expects destination and value"
  | "alias-base-register" =>
    match args with
    | [.register name _ baseWidth] => valueOnly (.register name baseWidth baseWidth)
    | _ => throw "alias-base-register expects a register"
  | "symbol" =>
    match args with
    | [.register name _ _] => valueOnly (.symbol name)
    | [.symbol name] => valueOnly (.symbol name)
    | _ => throw "symbol expects a register or symbol"
  | "empty" => valueOnly .unit
  | "load-bits" =>
    match args with
    | [bits, address] => valueOnly (← loadMemory context (← expectNat bits) [address])
    | _ => throw "load-bits expects width and address"
  | "load-byte" => valueOnly (← loadMemory context 8 args)
  | "load-hword" => valueOnly (← loadMemory context 32 args)
  | "load-word" => valueOnly (← loadMemory context context.bits args)
  | "store-word" => pure (.unit, ← storeMemory context args)
  | "store-byte" =>
    match args with
    | [address, value] =>
      let (width, value) ← expectBil context value
      if width < 8 then throw "store-byte value is too narrow"
      pure (.unit, ← storeMemory context [address, .bil 8 (.cast .low 8 value)])
    | _ => throw "store-byte expects address and value"
  | "intrinsic" =>
    let name := match args with
      | .symbol name :: _ => name
      | _ => "unknown"
    pure (.unit, [.special name])
  | "exec-addr" =>
    match args with
    | [target] =>
      let (width, target) ← expectBil context target
      if width != context.bits then throw "Primus jump target has the wrong width"
      pure (.unit, [.jmp target])
    | _ => throw "exec-addr expects a target"
  | "get-program-counter" | "get-current-program-counter" =>
    valueOnly (.bil context.bits (.int (BitVec.ofNat context.bits context.pc)))
  | "get-next-program-counter" =>
    valueOnly (.bil context.bits (.int (BitVec.ofNat context.bits context.nextPc)))
  | "is-zero" | "non-zero" =>
    match args with
    | [value] =>
      let (width, value) ← expectBil context value
      let zero := Bil.Exp.int (BitVec.ofNat width 0)
      valueOnly (.bil 1 (.bin (if name = "is-zero" then .eq else .neq) value zero))
    | _ => throw "zero predicate expects one argument"
  | "list" => valueOnly (.list args)
  | "cons" =>
    match args with
    | [head, .list tail] => valueOnly (.list (head :: tail))
    | _ => throw "cons expects a value and list"
  | "car" =>
    match args with
    | [.list (head :: _)] => valueOnly head
    | _ => throw "car expects a nonempty list"
  | "cdr" =>
    match args with
    | [.list (_ :: tail)] => valueOnly (.list tail)
    | _ => throw "cdr expects a nonempty list"
  | "length" =>
    match args with
    | [.list values] => valueOnly (.int (BitVec.ofNat 64 values.length))
    | _ => throw "length expects a list"
  | "null?" =>
    match args with
    | [.list values] => valueOnly (.bool values.isEmpty)
    | _ => throw "null? expects a list"
  | "list?" =>
    match args with
    | [.list _] => valueOnly (.bool true)
    | [_] => valueOnly (.bool false)
    | _ => throw "list? expects one argument"
  | _ => throw s!"unsupported Primus primitive {name}"

private def applyPrimitiveIndex (context : Context) (operation : Nat) (args : List Value) :
    Except String (Value × Bil.Program) := do
  match operation with
  | 0 => valueOnly (← binary context .add args)
  | 1 =>
    match args with
    | [value] =>
      let (width, value) ← expectBil context value
      valueOnly (.bil width (.un .neg value))
    | _ => valueOnly (← binary context .sub args)
  | 2 => valueOnly (← binary context .mul args)
  | 3 => valueOnly (← binary context .div args)
  | 4 => valueOnly (← binary context .sdiv args)
  | 5 => valueOnly (← binary context .smod args)
  | 6 => valueOnly (← compare context .eq args)
  | 7 => valueOnly (← compare context .neq args)
  | 8 => valueOnly (← compare context .lt args)
  | 9 => valueOnly (← compare context .le args)
  | 10 => valueOnly (← compare context .gt args)
  | 11 => valueOnly (← compare context .ge args)
  | 12 | 26 => valueOnly (← unaryNot context args)
  | 20 | 23 => valueOnly (← binary context .and args)
  | 21 | 24 => valueOnly (← binary context .or args)
  | 22 | 25 => valueOnly (← binary context .xor args)
  | 27 => valueOnly (← shift context .lshift args)
  | 28 => valueOnly (← shift context .rshift args)
  | 29 => valueOnly (← shift context .ashift args)
  | 30 =>
    match args with
    | [high, low, value] =>
      let high ← expectNat high
      let low ← expectNat low
      let (width, value) ← expectBil context value
      if high < low || high ≥ width then throw "invalid Primus extraction"
      valueOnly (.bil (high - low + 1) (.extract high low value))
    | _ => throw "extract expects high, low, and value"
  | 31 =>
    match args with
    | [bit, value] =>
      let bit ← expectNat bit
      let (width, value) ← expectBil context value
      if bit ≥ width then throw "invalid Primus bit selection"
      valueOnly (.bil 1 (.extract bit bit value))
    | _ => throw "select expects bit and value"
  | 32 =>
    match args with
    | first :: rest =>
      let (width, first) ← expectBil context first
      let (width, concatenated) ← rest.foldlM (init := (width, first)) fun current value => do
        let (rightWidth, right) ← expectBil context value
        .ok (current.1 + rightWidth, Bil.Exp.concat current.2 right)
      valueOnly (.bil width concatenated)
    | [] => throw "concat expects at least one value"
  | 33 => valueOnly (← cast context .low args)
  | 34 => valueOnly (← cast context .high args)
  | 35 => valueOnly (← cast context .signed args)
  | 36 => valueOnly (← cast context .unsigned args)
  | 37 =>
    match args with
    | [] => valueOnly (.int (BitVec.ofNat 64 context.bits))
    | [value] => valueOnly (.int (BitVec.ofNat 64 (← widthOf context value)))
    | _ => throw "word-width expects zero or one arguments"
  | 38 | 39 | 40 =>
    match args with
    | [destination, value] => pure (value, ← assign context destination value)
    | _ => throw "set expects destination and value"
  | 41 =>
    match args with
    | [.register name _ baseWidth] => valueOnly (.register name baseWidth baseWidth)
    | _ => throw "alias-base-register expects a register"
  | 42 =>
    match args with
    | [.register name _ _] | [.symbol name] => valueOnly (.symbol name)
    | _ => throw "symbol expects a register or symbol"
  | 43 => valueOnly .unit
  | 44 =>
    match args with
    | [bits, address] => valueOnly (← loadMemory context (← expectNat bits) [address])
    | _ => throw "load-bits expects width and address"
  | 45 => valueOnly (← loadMemory context 8 args)
  | 46 => valueOnly (← loadMemory context 32 args)
  | 47 => valueOnly (← loadMemory context context.bits args)
  | 48 => pure (.unit, ← storeMemory context args)
  | 49 =>
    match args with
    | [address, value] =>
      let (width, value) ← expectBil context value
      if width < 8 then throw "store-byte value is too narrow"
      pure (.unit, ← storeMemory context [address, .bil 8 (.cast .low 8 value)])
    | _ => throw "store-byte expects address and value"
  | 50 =>
    match args with
    | [target] =>
      let (width, target) ← expectBil context target
      if width != context.bits then throw "Primus jump target has the wrong width"
      pure (.unit, [.jmp target])
    | _ => throw "exec-addr expects a target"
  | 51 =>
    let name := match args with
      | .symbol name :: _ => name
      | _ => "unknown"
    pure (.unit, [.special name])
  | 52 | 53 =>
    valueOnly (.bil context.bits (.int (BitVec.ofNat context.bits context.pc)))
  | 54 => valueOnly (.bil context.bits (.int (BitVec.ofNat context.bits context.nextPc)))
  | 55 | 56 =>
    match args with
    | [value] =>
      let (width, value) ← expectBil context value
      let zero := Bil.Exp.int (BitVec.ofNat width 0)
      valueOnly (.bil 1 (.bin (if operation = 55 then .eq else .neq) value zero))
    | _ => throw "zero predicate expects one argument"
  | 57 =>
    match args with
    | [value] =>
      let (width, value) ← expectBil context value
      valueOnly (.bil width (.un .neg value))
    | _ => throw "neg expects one argument"
  | 58 => valueOnly (← compare context .slt args)
  | 59 => valueOnly (← compare context .sle args)
  | 60 => valueOnly (← compare context .sgt args)
  | 61 => valueOnly (← compare context .sge args)
  | 63 => valueOnly (← leadingZeros context args)
  | _ => throw s!"unsupported compiled Primus primitive {operation}"

private def freezeBil (state : State) (width : Nat) (expression : Bil.Exp) : Value × State :=
  match Bil.evalExp [] expression with
  | .ok _ => (.bil width expression, state)
  | .error _ =>
    let temporary : Bap.Var := ⟨s!"_primus_{state.nextTemp}", .imm width, 0, false⟩
    (.bil width (.var temporary), {
      globals := state.globals
      code := state.code ++ [.move temporary expression]
      nextTemp := state.nextTemp + 1
    })

private def freeze (context : Context) (state : State) (value : Value) : Value × State :=
  match value with
  | .bil width expression => freezeBil state width expression
  | .register .. =>
    match expectBil context value with
    | .ok (width, expression) => freezeBil state width expression
    | .error _ => (value, state)
  | _ => (value, state)

private def substitute (bindings : List (String × Sexp)) (form : Sexp) : Sexp :=
  match form with
  | .atom atom => (Assoc.get atom bindings).getD form
  | .list items => .list (items.map (substitute bindings))

private def contextMatches (bits : Nat) (body : List Sexp) : Bool :=
  body.all fun form => match form with
    | .list [.atom "declare", .list (.atom "context" :: conditions)] =>
      conditions.all fun condition => match condition with
        | .list [.atom "bits", .atom width] => width.toNat? = some bits
        | _ => false
    | _ => true

private def definitionBody (body : List Sexp) : List Sexp :=
  let body := body.filter fun form => match form with
    | .list (.atom "declare" :: _) => false
    | _ => true
  match body with
  | .atom _ :: rest@(_ :: _) => rest
  | _ => body

private def caseMatches (key : Value) (form : Sexp) : Except String Bool := do
  match form with
  | .list [.atom "quote", .atom expected] =>
    match parseInteger expected with
    | some (expected, _) => pure ((← expectNat key) = expected.toNat)
    | none =>
      match key with
      | .symbol actual | .register actual _ _ => pure (actual = expected)
      | _ => .ok false
  | .atom expected =>
    match parseInteger expected with
    | some (expected, _) => pure ((← expectNat key) = expected.toNat)
    | none =>
      match key with
      | .symbol actual | .register actual _ _ => pure (actual = expected)
      | _ => .error "invalid Primus case key"
  | _ => .error "invalid Primus case label"

mutual
  private def evalSequence (fuel : Nat) (locals : Locals) (context : Context)
      (state : State) (forms : List Sexp) : Except String (Value × State) := do
    match fuel with
    | 0 => .error "Primus evaluation fuel exhausted"
    | fuel + 1 =>
      match forms with
      | [] => .ok (.unit, state)
      | [form] => eval fuel locals context state form
      | form :: rest =>
        let (_, state) ← eval fuel locals context state form
        evalSequence fuel locals context state rest

  private def evalList (fuel : Nat) (locals : Locals) (context : Context)
      (state : State) (forms : List Sexp) : Except String (List Value × State) := do
    match fuel with
    | 0 => .error "Primus evaluation fuel exhausted"
    | fuel + 1 =>
      match forms with
      | [] => .ok ([], state)
      | form :: rest =>
        let (value, state) ← eval fuel locals context state form
        let (values, state) ← evalList fuel locals context state rest
        .ok (value :: values, state)

  private def evalConditional (fuel : Nat) (locals : Locals) (context : Context)
      (state : State) (test : Sexp) (yes no : List Sexp) : Except String (Value × State) := do
    match fuel with
    | 0 => .error "Primus evaluation fuel exhausted"
    | fuel + 1 =>
      let (test, state) ← eval fuel locals context state test
      match ← truth test with
      | some true => evalSequence fuel locals context state yes
      | some false => evalSequence fuel locals context state no
      | none =>
        let condition ← condition context test
        let (yesValue, yesState) ← evalSequence fuel locals context { state with code := [] } yes
        let (noValue, noState) ← evalSequence fuel locals context { state with code := [] } no
        let state := { state with nextTemp := max yesState.nextTemp noState.nextTemp }
        if yesState.code.isEmpty && noState.code.isEmpty then do
          let (yesWidth, yes) ← expectBil context yesValue
          let (noWidth, no) ← expectBil context noValue
          let width := max yesWidth noWidth
          .ok (.bil width (.ite condition (extend width yes) (extend width no)), state)
        else
          .ok (.unit, emit state [.ifElse condition yesState.code noState.code])

  private def apply (fuel : Nat) (context : Context) (state : State)
      (value : Value) (args : List Value) : Except String (Value × State) := do
    match fuel with
    | 0 => .error "Primus evaluation fuel exhausted"
    | fuel + 1 =>
      match value with
      | .callable (.primitive name) =>
        let (value, code) ← applyPrimitive context name args
        .ok (value, emit state code)
      | .callable (.function params body env) =>
        if params.length != args.length then .error "Primus function arity mismatch"
        else evalSequence fuel (params.zip args ++ env) context state body
      | .callable (.compiled params body env) =>
        if params.length != args.length then .error "Primus function arity mismatch"
        else evalCompiledSequence fuel (params.zip args ++ env) context state body
      | .callable (.macro ..) => .error "attempted to apply a Primus macro as a function"
      | _ => .error "attempted to call a non-function Primus value"

  private def eval (fuel : Nat) (locals : Locals) (context : Context)
      (state : State) (form : Sexp) : Except String (Value × State) := do
    match fuel with
    | 0 => .error "Primus evaluation fuel exhausted"
    | fuel + 1 =>
      match form with
      | .atom atom =>
        if atom = "true" || atom = "false" || atom.startsWith ":" || (parseInteger atom).isSome then
          .ok (atomValue atom, state)
        else .ok (← lookup atom locals state.globals, state)
      | .list [] => .ok (.list [], state)
      | .list (.atom "quote" :: [value]) =>
        let rec quoted : Sexp → Value
          | .atom atom => atomValue atom
          | .list items => .list (items.map quoted)
        .ok (quoted value, state)
      | .list [.atom "sizeof", .atom typeName] =>
        let bits := match typeName with
          | "word" | "ptr_t" | "int64_t" => context.bits
          | "int" | "int32_t" => 32
          | "hword" | "int16_t" => 16
          | "byte" | "int8_t" => 8
          | _ => 0
        if bits = 0 then .error s!"unknown Primus type {typeName}"
        else .ok (.int (BitVec.ofNat 64 (bits / 8)), state)
      | .list [.atom "assert-msg", test, .atom message] =>
        let (test, state) ← eval fuel locals context state test
        match ← truth test with
        | some true => .ok (.unit, state)
        | _ => .error message
      | .list [.atom "replicate", value, count] | .list [.atom "core:replicate", value, count] =>
        let (value, state) ← eval fuel locals context state value
        let (count, state) ← eval fuel locals context state count
        let count ← expectNat count
        let (width, value) ← expectBil context value
        if count = 0 then .error "Primus replicate count must be positive"
        else
          let repeated := (List.range (count - 1)).foldl (init := value) fun result _ =>
            .concat result value
          .ok (.bil (width * count) repeated, state)
      | .list [.atom "clz", value] =>
        let (value, state) ← eval fuel locals context state value
        .ok (← leadingZeros context [value], state)
      | .list (.atom "if" :: [test, yes, no]) =>
        evalConditional fuel locals context state test [yes] [no]
      | .list (.atom "when" :: test :: body) =>
        evalConditional fuel locals context state test body []
      | .list (.atom "unless" :: test :: body) =>
        evalConditional fuel locals context state test [] body
      | .list (.atom "progn" :: body) | .list (.atom "prog" :: body) =>
        evalSequence fuel locals context state body
      | .list (.atom "let" :: .list bindings :: body) =>
        let (locals, state) ← bindings.foldlM (init := (locals, state)) fun current binding => do
          match binding with
          | .list [.atom name, value] =>
            let (value, state) ← eval fuel current.1 context current.2 value
            let (value, state) := freeze context state value
            .ok ((name, value) :: current.1, state)
          | _ => .error "invalid Primus let binding"
        evalSequence fuel locals context state body
      | .list (.atom "lambda" :: .list params :: body) =>
        let params ← params.mapM Sexp.asAtom
        .ok (.callable (.function params (definitionBody body) locals), state)
      | .list (.atom "defun" :: .atom name :: .list params :: body) =>
        let params ← params.mapM Sexp.asAtom
        if !contextMatches context.bits body then .ok (.unit, state)
        else
          let callable := Callable.function params (definitionBody body) []
          .ok (.callable callable, { state with globals := Assoc.put name (.callable callable) state.globals })
      | .list (.atom "defmacro" :: .atom name :: .list params :: body) =>
        let params ← params.mapM Sexp.asAtom
        if !contextMatches context.bits body then .ok (.unit, state)
        else
          let callable := Callable.macro params (definitionBody body)
          .ok (.callable callable, { state with globals := Assoc.put name (.callable callable) state.globals })
      | .list (.atom "case" :: key :: branches) =>
        let (key, state) ← eval fuel locals context state key
        let rec select : List Sexp → Except String (List Sexp)
          | [] => .error "Primus case has no matching branch"
          | [fallback] => .ok [fallback]
          | label :: body :: rest => do
            if ← caseMatches key label then .ok [body] else select rest
        evalSequence fuel locals context state (← select branches)
      | .list (.atom operator :: operands) =>
        match ← lookup operator locals state.globals with
        | .callable (.macro params body) =>
          if params.length != operands.length then .error "Primus macro arity mismatch"
          else
            let expanded := body.map (substitute (params.zip operands))
            evalSequence fuel locals context state expanded
        | _ =>
          let (callable, state) ← eval fuel locals context state (.atom operator)
          let (args, state) ← evalList fuel locals context state operands
          apply fuel context state callable args
      | .list (operator :: operands) =>
        let (callable, state) ← eval fuel locals context state operator
        let (args, state) ← evalList fuel locals context state operands
        apply fuel context state callable args

  private def evalCompiledSequence (fuel : Nat) (locals : Locals) (context : Context)
      (state : State) (forms : List CExp) : Except String (Value × State) := do
    match fuel with
    | 0 => .error "compiled Primus evaluation fuel exhausted"
    | fuel + 1 =>
      match forms with
      | [] => .ok (.unit, state)
      | [form] => evalCompiled fuel locals context state form
      | form :: rest =>
        let (_, state) ← evalCompiled fuel locals context state form
        evalCompiledSequence fuel locals context state rest

  private def evalCompiledList (fuel : Nat) (locals : Locals) (context : Context)
      (state : State) (forms : List CExp) : Except String (List Value × State) := do
    match fuel with
    | 0 => .error "compiled Primus evaluation fuel exhausted"
    | fuel + 1 =>
      match forms with
      | [] => .ok ([], state)
      | form :: rest =>
        let (value, state) ← evalCompiled fuel locals context state form
        let (values, state) ← evalCompiledList fuel locals context state rest
        .ok (value :: values, state)

  private def evalCompiledConditional (fuel : Nat) (locals : Locals) (context : Context)
      (state : State) (test : CExp) (yes no : List CExp) : Except String (Value × State) := do
    match fuel with
    | 0 => .error "compiled Primus evaluation fuel exhausted"
    | fuel + 1 =>
      let (test, state) ← evalCompiled fuel locals context state test
      match ← truth test with
      | some true => evalCompiledSequence fuel locals context state yes
      | some false => evalCompiledSequence fuel locals context state no
      | none =>
        let condition ← condition context test
        let (yesValue, yesState) ← evalCompiledSequence fuel locals context { state with code := [] } yes
        let (noValue, noState) ← evalCompiledSequence fuel locals context { state with code := [] } no
        let state := { state with nextTemp := max yesState.nextTemp noState.nextTemp }
        if yesState.code.isEmpty && noState.code.isEmpty then do
          let (yesWidth, yes) ← expectBil context yesValue
          let (noWidth, no) ← expectBil context noValue
          let width := max yesWidth noWidth
          .ok (.bil width (.ite condition (extend width yes) (extend width no)), state)
        else
          .ok (.unit, emit state [.ifElse condition yesState.code noState.code])

  private def evalCompiled (fuel : Nat) (locals : Locals) (context : Context)
      (state : State) (form : CExp) : Except String (Value × State) := do
    match fuel with
    | 0 => .error "compiled Primus evaluation fuel exhausted"
    | fuel + 1 =>
      match form with
      | .value value => .ok (value, state)
      | .local slot =>
        match locals[slot]? with
        | some binding => .ok (binding.2, state)
        | none => .error "compiled Primus local slot is out of range"
      | .global slot =>
        match state.globals[slot]? with
        | some binding => .ok (binding.2, state)
        | none => .error "compiled Primus global slot is out of range"
      | .primitive operation operands =>
        let (args, state) ← evalCompiledList fuel locals context state operands
        let (value, code) ← applyPrimitiveIndex context operation args
        .ok (value, emit state code)
      | .apply callable operands =>
        let (callable, state) ← evalCompiled fuel locals context state callable
        let (args, state) ← evalCompiledList fuel locals context state operands
        apply fuel context state callable args
      | .ifElse test yes no => evalCompiledConditional fuel locals context state test yes no
      | .letIn value body =>
        let (value, state) ← evalCompiled fuel locals context state value
        let (value, state) := freeze context state value
        evalCompiled fuel (("", value) :: locals) context state body
      | .sequence forms => evalCompiledSequence fuel locals context state forms
end

private def primitiveIndex (name : String) : Option Nat := primitiveNames.findIdx? (· == name)

private def compilablePrimitive (operation : Nat) : Bool :=
  operation ≤ 12 || (20 ≤ operation && operation ≤ 61) || operation = 63

private def quotedValue : Sexp → Value
  | .atom atom => atomValue atom
  | .list items => .list (items.map quotedValue)

mutual
  private def compileExp (globals : Globals) (locals : List String) : Nat → Sexp → Option CExp
    | 0, _ => none
    | fuel + 1, form =>
      match form with
      | .atom atom =>
        if atom = "true" || atom = "false" || atom.startsWith ":" || (parseInteger atom).isSome then
          some (.value (atomValue atom))
        else
          match locals.findIdx? (· == atom) with
          | some slot => some (.local slot)
          | none => (globals.findIdx? fun binding => binding.1 == atom).map .global
      | .list [] => some (.value (.list []))
      | .list [.atom "quote", value] => some (.value (quotedValue value))
      | .list [.atom "clz", value] => do
        let value ← compileExp globals locals fuel value
        some (.primitive 63 [value])
      | .list [.atom "if", test, yes, no] => do
        let test ← compileExp globals locals fuel test
        let yes ← compileExp globals locals fuel yes
        let no ← compileExp globals locals fuel no
        some (.ifElse test [yes] [no])
      | .list (.atom "when" :: test :: body) => do
        let test ← compileExp globals locals fuel test
        some (.ifElse test (← compileSequence globals locals fuel body) [])
      | .list (.atom "unless" :: test :: body) => do
        let test ← compileExp globals locals fuel test
        some (.ifElse test [] (← compileSequence globals locals fuel body))
      | .list (.atom "progn" :: body) | .list (.atom "prog" :: body) =>
        .sequence <$> compileSequence globals locals fuel body
      | .list (.atom "let" :: .list bindings :: body) =>
        compileBindings globals locals fuel bindings body
      | .list (.atom operator :: operands) =>
        let visible := locals.map fun name => (name, Value.unit)
        match lookup operator visible globals with
        | .ok (.callable (.macro params body)) =>
          if params.length != operands.length then none
          else .sequence <$> compileSequence globals locals fuel (body.map (substitute (params.zip operands)))
        | .ok (.callable (.primitive name)) => do
          let operation ← primitiveIndex name
          if !compilablePrimitive operation then none
          let args ← operands.mapM (compileExp globals locals fuel)
          some (.primitive operation args)
        | _ => do
          let callable ← compileExp globals locals fuel (.atom operator)
          let args ← operands.mapM (compileExp globals locals fuel)
          some (.apply callable args)
      | .list (operator :: operands) => do
        let callable ← compileExp globals locals fuel operator
        let args ← operands.mapM (compileExp globals locals fuel)
        some (.apply callable args)

  private def compileSequence (globals : Globals) (locals : List String) (fuel : Nat)
      (forms : List Sexp) : Option (List CExp) :=
    forms.mapM (compileExp globals locals fuel)

  private def compileBindings (globals : Globals) (locals : List String) :
      Nat → List Sexp → List Sexp → Option CExp
    | 0, _, _ => none
    | fuel + 1, bindings, body =>
      match bindings with
      | [] => .sequence <$> compileSequence globals locals fuel body
      | .list [.atom name, value] :: rest => do
        let value ← compileExp globals locals fuel value
        .letIn value <$> compileBindings globals (name :: locals) fuel rest body
      | _ => none
end

private def compileValue (globals : Globals) (value : Value) : Value :=
  match value with
  | .callable (.function params body env) =>
    let locals := params ++ env.map Prod.fst
    match body.mapM (compileExp globals locals 1000) with
    | some body => .callable (.compiled params body env)
    | none => value
  | _ => value

def compileGlobals (globals : Globals) : Globals :=
  globals.map fun binding => (binding.1, compileValue globals binding.2)

def evalForms (context : Context) (globals : Globals) (forms : List Sexp) :
    Except String State := do
  let forms := forms.filter fun form => match form with
    | .list (.atom kind :: _) =>
      kind != "declare" && kind != "defpackage" && kind != "in-package" && kind != "require"
    | _ => true
  let (_, state) ← evalSequence 100000 [] context { globals := globals } forms
  .ok state

private def readForms (path : String) : IO (List Sexp) := do
  let source ← IO.FS.readFile path
  match Sexp.parseMany source with
  | .ok forms => pure forms
  | .error error => throw <| IO.userError s!"{path}: {error}"

private def requiredName : Sexp → Option String
  | .list [.atom "require", .atom name] => some name
  | _ => none

private def loadFiles (directories : List String) (visited : List String)
    (context : Context) (state : State) : Nat → List String → IO (List String × State)
  | 0, _ => throw <| IO.userError "Primus semantics loader fuel exhausted"
  | _, [] => pure (visited, state)
  | fuel + 1, name :: rest => do
    if visited.contains name then
      loadFiles directories visited context state fuel rest
    else
      let candidates : List System.FilePath := directories.map fun directory => s!"{directory}/{name}.lisp"
      let path? ← candidates.findM? fun path => System.FilePath.pathExists path
      let path ← match path? with
        | some path => pure path
        | none => throw <| IO.userError s!"Primus semantics file not found: {name}"
      let forms ← readForms path.toString
      let requirements := forms.filterMap requiredName
      let (visited, state) ← loadFiles directories (name :: visited) context state fuel requirements
      let state ← match evalForms context state.globals forms with
        | .ok loaded => pure { globals := loaded.globals, code := state.code ++ loaded.code }
        | .error error => throw <| IO.userError s!"{path}: {error}"
      loadFiles directories visited context state fuel rest

def loadMany (directories entries : List String) (context : Context) : IO Globals := do
  let (_, state) ← loadFiles directories [] context { } 1000 entries
  pure state.globals

def load (directories : List String) (entry : String) (context : Context) : IO Globals :=
  loadMany directories [entry] context

def liftWith (environment : Environment) (context : Context) (opcode : String)
    (operands : List Value) : IO Bil.Program := do
  let callable ← match environment.operations.get? opcode with
    | some callable => pure (.callable callable)
    | none =>
      match Assoc.get opcode environment.globals with
      | some callable => pure callable
      | none => throw <| IO.userError s!"Primus semantics has no definition for {opcode}"
  match apply 100000 context { globals := environment.globals } callable operands with
  | .ok (_, state) => pure state.code
  | .error error => throw <| IO.userError s!"{opcode}: {error}"

def lift (globals : Globals) (context : Context) (opcode : String) (operands : List Value) :
    IO Bil.Program :=
  liftWith (.ofGlobals (compileGlobals globals)) context opcode operands

def machineOperand (environment : Environment) (context : Context) : LLVM.MCOperand → Except String Value
  | .reg id =>
    match environment.registers.get? id with
    | some value => .ok value
    | none => .error s!"Primus semantics has no register for LLVM ID {id}"
  | .imm value => .ok (.bil context.bits (.int (BitVec.ofInt context.bits value)))

def liftMC (environment : Environment) (context : Context) (opcode : Nat)
    (operands : List Value) : IO Bil.Program := do
  let callable ← match environment.opcodes.get? opcode with
    | some callable => pure callable
    | none => throw <| IO.userError s!"Primus semantics has no definition for LLVM opcode {opcode}"
  match apply 100000 context { globals := environment.globals } (.callable callable) operands with
  | .ok (_, state) => pure state.code
  | .error error => throw <| IO.userError s!"LLVM opcode {opcode}: {error}"

def register (name : String) (width baseWidth : Nat) : Value := .register name width baseWidth

def immediate (value : Int) : Value := .bil 64 (.int (BitVec.ofInt 64 value))

end Bap.Primus.Semantics
