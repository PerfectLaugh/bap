import Bap.Core.Assoc
import Bap.Core.Sexp
import Bap.Bil.Syntax
import Bap.Bil.Eval
import Bap.LLVM
import Bap.Primus.Literal
import Std.Data.HashMap

namespace Bap.Primus.Semantics

open Bap.Primus.Literal

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
    /-- The definitions of one name, selected by the number of arguments or operands. -/
    | overloads (candidates : List Callable)

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
    -- It shadows what a later binding of the name defined.
    | _ => result.erase binding.1
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
  /-- The prefix bytes of the instruction, when the decoder provides them. -/
  prefixes : Option (List Nat) := none

structure State where
  globals : Globals := []
  operations : Std.HashMap String Callable := {}
  code : Bil.Program := []
  nextTemp : Nat := 0

private def indexGlobals (globals : Globals) : Std.HashMap String Callable :=
  globals.reverse.foldl (init := ({} : Std.HashMap String Callable)) fun result binding =>
    match binding.2 with
    | .callable callable => result.insert binding.1 callable
    | _ => result.erase binding.1

private def primitiveNames : List String :=
  ["+", "-", "*", "/", "s/", "mod", "=", "/=", "<", "<=", ">", ">=", "not", "list",
    "cons", "car", "cdr", "length", "null?", "list?", "logand", "logor", "logxor",
    "bitand", "bitor", "bitxor", "lnot", "lshift", "rshift", "arshift", "extract",
    "select", "concat", "cast-low", "cast-high", "cast-signed", "cast-unsigned",
    "word-width", "set", "set$", "set-symbol-value", "alias-base-register", "symbol", "empty",
    "load-bits", "load-byte", "load-hword", "load-word", "store-word", "store-byte", "exec-addr", "intrinsic",
    "get-program-counter", "get-current-program-counter", "get-next-program-counter",
    "is-zero", "non-zero", "neg", "s<", "s<=", "s>", "s>=", "replicate", "clz", "signed-mod", "signed-rem",
    "unquote", "symbol-concat", "cast-saturate", "x86-prefix",
    "+.", "-.", "*.", "/.", "fsqrt", "fround", "fconvert", "cast-float", "cast-sfloat", "cast-int", "cast-sint",
    "<.", ">.", ">=.", "=.", "is-nan", "is-inf", "is-fzero"]

private def lookup (name : String) (locals : Locals) (globals : Globals) : Except String Value :=
  let primitiveName := if name.startsWith "core:" then (name.drop 5).toString else name
  match Assoc.get name locals with
  | some value => .ok value
  | none =>
    if primitiveName = "replicate" then .ok (.callable (.primitive "replicate"))
    else
      match Assoc.get name globals with
      | some value => .ok value
      | none =>
        if primitiveNames.contains primitiveName then .ok (.callable (.primitive primitiveName))
        else .error s!"unknown Primus symbol {name}"

private def lookupState (name : String) (locals : Locals) (state : State) : Except String Value :=
  let primitiveName := if name.startsWith "core:" then (name.drop 5).toString else name
  match Assoc.get name locals with
  | some value => .ok value
  | none =>
    if primitiveName = "replicate" then .ok (.callable (.primitive "replicate"))
    else
      match state.operations.get? name with
      | some callable => .ok (.callable callable)
      | none =>
        match Assoc.get name state.globals with
        | some value => .ok value
        | none =>
          if primitiveNames.contains primitiveName then .ok (.callable (.primitive primitiveName))
          else .error s!"unknown Primus symbol {name}"

mutual
  /-- Rejects malformed literals in a parsed form, wherever they are, as the upstream parser does.
  Quoted data, documentation and message strings are not expressions. -/
  private def checkLiterals : Sexp → Except String Unit
    | .atom atom => (readLiteral atom).map fun _ => ()
    | .list [] => .ok ()
    | .list (.atom "quote" :: _) | .list (.atom "declare" :: _) => .ok ()
    | .list (.atom "msg" :: _) | .list (.atom "error" :: _) => .ok ()
    | .list [.atom "assert-msg", test, .atom _] => checkLiterals test
    | .list (.atom "defun" :: .atom _ :: .list _ :: body)
    | .list (.atom "defmacro" :: .atom _ :: .list _ :: body)
    | .list (.atom "defmethod" :: .atom _ :: .list _ :: body) => checkBody body
    | .list (.atom "defparameter" :: .atom _ :: value :: _) => checkLiterals value
    | .list (head :: rest) => do
      checkLiterals head
      checkForms rest

  private def checkForms : List Sexp → Except String Unit
    | [] => .ok ()
    | form :: rest => do
      checkLiterals form
      checkForms rest

  /-- The first atom of a longer definition body is its documentation string. -/
  private def checkBody : List Sexp → Except String Unit
    | .atom _ :: rest@(_ :: _) => checkForms rest
    | .list (.atom "declare" :: _) :: rest => checkBody rest
    | body => checkForms body
end

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
      -- the empty high part of a value, as when a whole register is assigned with its high part kept
      if width = 0 then .ok (.bil 0 (.int 0#0))
      else if width > sourceWidth then .error "invalid Primus high cast"
      else .ok (.bil width (.cast .high width value))
    | _ => .ok (.bil width (.cast kind width value))
  | _ => .error "Primus cast expects width and value"

private def widthOf (context : Context) : Value → Except String Nat
  | .int _ => .ok context.bits
  | .bil width _ => .ok width
  | .bool _ => .ok 1
  | .register _ width _ => .ok width
  | _ => .error "word-width expects a bitvector"

/-- `(word-width X ... Z)` is the widest argument, and with no arguments the machine word. -/
private def wordWidth (context : Context) (args : List Value) : Except String Value := do
  let widths ← args.mapM (widthOf context)
  .ok (.int (BitVec.ofNat 64 (match args with
    | [] => context.bits
    | _ => widths.foldl max 0)))

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
  let (valueWidth, value) ← expectBil context value
  if valueWidth != width then throw s!"Primus assignment width mismatch: {width} versus {valueWidth}"
  let var : Bap.Var := ⟨name, .imm baseWidth, 0, false⟩
  if width < baseWidth then
    -- a write through an alias keeps the other bits of the base, as Theory.Target.unalias does
    return [.move var (.concat (.extract (baseWidth - 1) width (.var var)) value)]
  else if width = baseWidth then
    return [.move var value]
  else
    throw s!"Primus assignment wider than the register: {name} width={width} base={baseWidth}"

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

private def concatStep (context : Context) (current : Nat × Bil.Exp) (value : Value) : Except String (Nat × Bil.Exp) := do
  let (rightWidth, right) ← expectBil context value
  -- an empty part leaves the other as it is
  if rightWidth = 0 then .ok current
  else if current.1 = 0 then .ok (rightWidth, right)
  else .ok (current.1 + rightWidth, Bil.Exp.concat current.2 right)

private def valueOnly (value : Value) : Except String (Value × Bil.Program) := pure (value, [])

private def intrinsicVar (kind : String) (index width : Nat) : Bap.Var :=
  ⟨s!"intrinsic:{kind}{index}", .imm width, 0, false⟩

/-- Splits the arguments of `intrinsic` at its keywords, as `Intrinsic.parse_args` does upstream. -/
private def intrinsicParams (key : String) (current : List Value) :
    List Value → List (String × List Value)
  | [] => [(key, current.reverse)]
  | .symbol keyword :: rest =>
    if keyword = ":result" || keyword = ":writes" || keyword = ":stores" || keyword = ":aborts" then
      (key, current.reverse) :: intrinsicParams keyword [] rest
    else intrinsicParams key (.symbol keyword :: current) rest
  | value :: rest => intrinsicParams key (value :: current) rest

private def intrinsicGroup (key : String) (params : List (String × List Value)) : List (List Value) :=
  params.filterMap fun param => if param.1 = key then some param.2 else none

private def mapIndexedM (f : Nat → α → Except String β) (index : Nat) : List α → Except String (List β)
  | [] => .ok []
  | item :: rest => do
    let item ← f index item
    return item :: (← mapIndexedM f (index + 1) rest)

private def assignInputs (context : Context) (inputs : List Value) : Except String Bil.Program :=
  mapIndexedM (fun index input => do
    let (width, input) ← expectBil context input
    return .move (intrinsicVar "x" index width) input) 0 inputs

/-- `(intrinsic 'NAME ARG .. :result W :writes REG WIDTH? :stores PTR WIDTH? :aborts)`: a call of the
subroutine NAME with the arguments in `intrinsic:x0`.., and the outputs in `intrinsic:y0`.. in the order
of the result, the writes and the stores. The result is a variable, which the callers copy. -/
private def intrinsicCall (context : Context) (name : String) (args : List Value) :
    Except String (Value × Bil.Program) := do
  let params := intrinsicParams ":inputs" [] args
  let inputs ← assignInputs context (intrinsicGroup ":inputs" params).flatten
  let results := intrinsicGroup ":result" params
  let base := results.length
  let writes ← mapIndexedM (fun index write => match write with
    | [.register reg width baseWidth] =>
      assignRegister context reg width baseWidth (.bil width (.var (intrinsicVar "y" (base + index) width)))
    | _ => throw "incorrect :writes parameters") 0 (intrinsicGroup ":writes" params)
  let base := base + writes.length
  let stores ← mapIndexedM (fun index store => match store with
    | [address] =>
      storeMemory context [address, .bil context.bits (.var (intrinsicVar "y" (base + index) context.bits))]
    | [address, width] => do
      let width ← expectNat width
      storeMemory context [address, .bil width (.var (intrinsicVar "y" (base + index) width))]
    | _ => throw "incorrect :stores parameters") 0 (intrinsicGroup ":stores" params)
  let code := inputs ++ [.special name] ++ writes.flatten ++ stores.flatten
  match results with
  | [] => pure (.unit, code)
  | [[width]] =>
    let width ← expectNat width
    pure (.bil width (.var (intrinsicVar "y" 0 width)), code)
  | _ => throw ":result may occur once and with a single argument"

private def symbolText : Value → Except String String
  | .symbol name | .register name _ _ => .ok name
  | .int value => .ok (toString value.toNat)
  | _ => .error "symbol-concat requires symbols"

/-- `(symbol-concat S1 .. SN :sep SEP)` joins the symbols with the optional separator. -/
private def symbolConcat (args : List Value) : Except String Value := do
  let names ← args.mapM symbolText
  match names.span (· != ":sep") with
  | (names, []) => .ok (.symbol (String.join names))
  | (names, [_, separator]) => .ok (.symbol (String.intercalate separator names))
  | _ => .error ":sep must be last and followed by an argument"

/-- The call of the IEEE 754 intrinsic that stands for a floating-point primitive, as `ieee754.lisp`
names them: BIL has no floating-point operations. -/
private def floatCall (context : Context) (name : String) (result : Nat) (inputs : List Value) :
    Except String (Value × Bil.Program) :=
  intrinsicCall context name (inputs ++ [.symbol ":result", .int (BitVec.ofNat 64 result)])

private def roundingMode : Value → Except String String
  | .symbol mode =>
    match mode.toList with
    | ':' :: mode => .ok (String.ofList mode)
    | _ => .error "expected a rounding mode"
  | _ => .error "expected a rounding mode"

private def floatOperation (context : Context) (name : String) (args : List Value) :
    Except String (Value × Bil.Program) := do
  let binaryName : Option String := match name with
    | "+." => some "fadd" | "-." => some "fsub" | "*." => some "fmul" | "/." => some "fdiv"
    | "fsqrt" => some "fsqrt" | "fround" => some "fround" | _ => none
  let castName : Option String := match name with
    | "fconvert" => some "fconvert" | "cast-float" => some "cast_float" | "cast-sfloat" => some "cast_sfloat"
    | "cast-int" => some "cast_int" | "cast-sint" => some "cast_sint" | _ => none
  let orderName : Option String := match name with
    | "<." => some "forder" | ">." => some "fgt" | ">=." => some "fge" | "=." => some "feq"
    | "is-nan" => some "is_nan" | "is-inf" => some "is_inf" | "is-fzero" => some "is_fzero" | _ => none
  match binaryName, castName, orderName, args with
  | some base, _, _, mode :: inputs@(first :: _) =>
    let mode ← roundingMode mode
    let width ← widthOf context first
    floatCall context s!"{base}_{mode}_ieee754_binary_{width}" width inputs
  | _, some base, _, [mode, width, value] =>
    let mode ← roundingMode mode
    let width ← expectNat width
    let source ← widthOf context value
    floatCall context s!"{base}_{mode}_ieee754_binary_{source}_{width}" width [value]
  | _, _, some base, inputs@(first :: _) =>
    let width ← widthOf context first
    floatCall context s!"{base}_ieee754_binary_{width}" 1 inputs
  | _, _, _, _ => throw s!"{name} has invalid arguments"

/-- `(cast-saturate :signed W X)` is X in W bits, or the closest W-bit value when X does not fit. An
`:unsigned` cast reads X as signed, as upstream's `Saturate.cast`, so a negative X saturates to zero. -/
private def castSaturate (context : Context) (args : List Value) : Except String Value := do
  match args with
  | [.symbol kind, width, value] =>
    let width ← expectNat width
    let (source, value) ← expectBil context value
    if width = 0 || source ≤ width then throw "cast-saturate requires a narrowing cast"
    let word (bits : Nat) : Bil.Exp := .int (BitVec.ofNat source bits)
    let sign := Bil.Exp.cast .unsigned source (.extract (source - 1) (source - 1) value)
    let signed := kind = ":signed"
    if !signed && kind != ":unsigned" then throw "expected :signed or :unsigned"
    let top := Bil.Exp.bin .ashift value (word (if signed then width - 1 else width))
    let isZero : Bil.Exp := .bin .eq top (word 0)
    let fits := if signed then Bil.Exp.bin .or isZero (.bin .eq top (word (2 ^ source - 1))) else isZero
    let upper := word (2 ^ (if signed then width - 1 else width) - 1)
    .ok (.bil width (.cast .low width (.ite fits value (.bin .add upper sign))))
  | _ => throw "cast-saturate expects a kind, width, and value"

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
  | "mod" => valueOnly (← binary context .rem args)
  | "signed-mod" => valueOnly (← binary context .smod args)
  | "signed-rem" => valueOnly (← binary context .srem args)
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
  | "word-width" => valueOnly (← wordWidth context args)
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
      let (width, concatenated) ← rest.foldlM (init := (width, first)) (concatStep context)
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
    match args with
    | .symbol name :: args => intrinsicCall context name args
    | _ => throw "intrinsic expects a symbol"
  | "exec-addr" =>
    match args with
    | [target] =>
      let (width, target) ← expectBil context target
      if width != context.bits then throw "Primus jump target has the wrong width"
      pure (.unit, [.jmp target])
    | _ => throw "exec-addr expects a target"
  | "unquote" =>
    match args with
    | [value@(.register ..)] => valueOnly value
    | [.symbol name] => throw s!"unquote of {name}, which is not a register"
    | _ => throw "unquote expects a symbol"
  | "symbol-concat" => valueOnly (← symbolConcat args)
  | "cast-saturate" => valueOnly (← castSaturate context args)
  | "x86-prefix" =>
    match args, context.prefixes with
    | [byte], some prefixes => valueOnly (.bool (prefixes.contains (← expectNat byte)))
    | [_], none => throw "the instruction prefixes are not available"
    | _, _ => throw "x86-prefix expects a byte"
  | "+." | "-." | "*." | "/." | "fsqrt" | "fround" | "fconvert" | "cast-float" | "cast-sfloat" | "cast-int"
  | "cast-sint" | "<." | ">." | ">=." | "=." | "is-nan" | "is-inf" | "is-fzero" =>
    floatOperation context name args
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
  | 5 => valueOnly (← binary context .rem args)
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
      let (width, concatenated) ← rest.foldlM (init := (width, first)) (concatStep context)
      valueOnly (.bil width concatenated)
    | [] => throw "concat expects at least one value"
  | 33 => valueOnly (← cast context .low args)
  | 34 => valueOnly (← cast context .high args)
  | 35 => valueOnly (← cast context .signed args)
  | 36 => valueOnly (← cast context .unsigned args)
  | 37 => valueOnly (← wordWidth context args)
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
    (.bil width (.var temporary), { state with
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

/-- Bind an assignable `let` variable: a machine variable of its own, so assignments in any later
control flow are seen by later reads. Upstream's `let_` also gives the name a fresh variable. -/
private def bindAssignable (context : Context) (state : State) (value : Value) : Except String (Value × State) := do
  let (width, expression) ← expectBil context value
  let name := s!"_primus_{state.nextTemp}"
  .ok (.register name width width, { state with
    code := state.code ++ [.move ⟨name, .imm width, 0, false⟩ expression]
    nextTemp := state.nextTemp + 1
  })

/-- `take_rest` of `bap_primus_lisp_def.ml`: binds parameters to operands one to one, and the last
parameter takes all remaining operands when there are several. -/
private def bindMacro : List String → List Sexp → Option (List (String × List Sexp))
  | [], [] => some []
  | [param], operands@(_ :: _ :: _) => some [(param, operands)]
  | param :: params, operand :: operands => ((param, [operand]) :: ·) <$> bindMacro params operands
  | _, _ => none

/-- How many operands the last parameter takes: the fewer, the more specific the definition. -/
private def macroRest (bindings : List (String × List Sexp)) : Nat :=
  match bindings.getLast? with
  | some binding => binding.2.length
  | none => 0

mutual
/-- `subst` of `bap_primus_lisp_def.ml`: a parameter inside of a list is spliced with its operands. -/
private def substitute (bindings : List (String × List Sexp)) : Sexp → List Sexp
  | .atom atom => (Assoc.get atom bindings).getD [.atom atom]
  | .list items => [.list (substituteList bindings items)]

private def substituteList (bindings : List (String × List Sexp)) : List Sexp → List Sexp
  | [] => []
  | form :: rest => substitute bindings form ++ substituteList bindings rest
end

/-- The macro definitions among a name's definitions. -/
private def macroCandidates : Callable → List Callable
  | candidate@(.macro ..) => [candidate]
  | .overloads candidates => candidates.filter fun candidate =>
    match candidate with
    | .macro .. => true
    | _ => false
  | _ => []

/-- Resolve a macro: the definition that accepts the operands with the fewest operands in the last
parameter. `overload_macro` of `bap_primus_lisp_resolve.ml`. -/
private def resolveMacro (operands : List Sexp) :
    List Callable → Option (Nat × List Sexp × List (String × List Sexp))
  | [] => none
  | .macro params body :: rest =>
    match bindMacro params operands, resolveMacro operands rest with
    | some bindings, some other =>
      if other.1 < macroRest bindings then some other else some (macroRest bindings, body, bindings)
    | some bindings, none => some (macroRest bindings, body, bindings)
    | none, other => other
  | _ :: rest => resolveMacro operands rest

/-- A macro body is a form, so a parameter alone in it must be bound to one operand. -/
private def expandBody (bindings : List (String × List Sexp)) (body : List Sexp) : Option (List Sexp) :=
  body.mapM fun form =>
    match substitute bindings form with
    | [expanded] => some expanded
    | _ => none

/-- The expansion of a call of a name with macro definitions; `none` if the name has no macros. As
upstream, macro definitions hide the functions of the same name. -/
private def macroExpansion (callable : Callable) (operands : List Sexp) :
    Except String (Option (List Sexp)) :=
  match macroCandidates callable with
  | [] => .ok none
  | candidates =>
    match resolveMacro operands candidates with
    | some (_, body, bindings) =>
      match expandBody bindings body with
      | some expanded => .ok (some expanded)
      | none => .error "a Primus macro parameter with several operands is the whole body"
    | none => .error "no Primus macro definition accepts these operands"

/-- The function a call with `count` arguments selects; `overload_defun` of
`bap_primus_lisp_resolve.ml` without the type check, since Primus values are not typed here. -/
private def resolveFunction (count : Nat) : List Callable → Option Callable
  | [] => none
  | candidate :: rest =>
    match candidate with
    | .function params .. | .compiled params .. =>
      if params.length = count then some candidate else resolveFunction count rest
    | _ => resolveFunction count rest

/-- Whether two definitions are alternatives of the same call, so that the later hides the earlier. -/
private def sameArity : Callable → Callable → Bool
  | .macro left _, .macro right _ => left.length == right.length
  | .function left .., .function right .. => left.length == right.length
  | .function left .., .compiled right .. => left.length == right.length
  | .compiled left .., .function right .. => left.length == right.length
  | .compiled left .., .compiled right .. => left.length == right.length
  | _, _ => false

/-- The definitions of a name after adding `callable`: a definition of the same arity is replaced,
which is how a later file overrides an earlier one, and one definition stays a plain callable. -/
private def addDefinition (callable : Callable) (previous : Option Value) : Callable :=
  let others := match previous with
    | some (.callable (.overloads candidates)) => candidates
    | some (.callable candidate) => [candidate]
    | _ => []
  match others.filter fun other => !sameArity callable other with
  | [] => callable
  | others => .overloads (callable :: others)

private def contextMatches (context : Context) (body : List Sexp) : Bool :=
  body.all fun form => match form with
    | .list [.atom "declare", .list (.atom "context" :: conditions)] =>
      conditions.all fun condition => match condition with
        | .list [.atom "bits", .atom width] => width.toNat? = some context.bits
        | .list [.atom "endianness", .atom "le"] => context.endian == .little
        | .list [.atom "endianness", .atom "eb"] => context.endian == .big
        | _ => false
    | _ => true

private def definitionBody (body : List Sexp) : List Sexp :=
  let body := body.filter fun form => match form with
    | .list (.atom "declare" :: _) => false
    | _ => true
  match body with
  | .atom _ :: rest@(_ :: _) => rest
  | _ => body

/-- Whether evaluating `form` may assign the `let` variable `name`, seeing through macros. -/
private def assignsLocal (globals : Globals) (name : String) : Nat → Sexp → Bool
  | 0, _ => true
  | _ + 1, .atom _ => false
  | fuel + 1, .list (.atom operator :: operands) =>
    if operator = "quote" then false else
    let assigned := match operator, operands with
      | "set", .atom target :: _ | "set$", .atom target :: _ | "set-symbol-value", .atom target :: _ => target = name
      | _, _ => false
    assigned ||
      (match Assoc.get operator globals with
       | some (.callable callable) =>
         match resolveMacro operands (macroCandidates callable) with
         | some (_, body, bindings) =>
           (substituteList bindings body).attach.any fun form => assignsLocal globals name fuel form.1
         | none => false
       | _ => false) ||
      operands.attach.any fun form => assignsLocal globals name fuel form.1
  | fuel + 1, .list items => items.attach.any fun form => assignsLocal globals name fuel form.1

/-- The target of an assignment or an `unquote` may be named by a symbol. -/
private def resolveSymbol (state : State) : List Value → List Value
  | value@(.symbol name) :: rest =>
    match Assoc.get name state.globals with
    | some register@(.register ..) => register :: rest
    | _ => value :: rest
  | args => args

private def resolveDestination (state : State) (name : String) (args : List Value) : List Value :=
  match args with
  | .symbol _ :: _ =>
    if name = "set" || name = "set$" || name = "set-symbol-value" || name = "unquote" then
      resolveSymbol state args
    else args
  | _ => args

/-- The primitives whose result is the output variable of an intrinsic. -/
private def intrinsicResult (name : String) : Bool :=
  name = "intrinsic" || name = "+." || name = "-." || name = "*." || name = "/." || name = "fsqrt" ||
    name = "fround" || name = "fconvert" || name = "cast-float" || name = "cast-sfloat" || name = "cast-int" ||
    name = "cast-sint" || name = "<." || name = ">." || name = ">=." || name = "=." || name = "is-nan" ||
    name = "is-inf" || name = "is-fzero"

private def quotedValue : Sexp → Value
  | .atom atom => atomValue atom
  | .list items => .list (items.map quotedValue)

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
        let (value, code) ← applyPrimitive context name (resolveDestination state name args)
        let state := emit state code
        -- the next call of an intrinsic overwrites its output variable
        if intrinsicResult name then .ok (freeze context state value) else .ok (value, state)
      | .callable (.overloads candidates) =>
        match resolveFunction args.length candidates with
        | some candidate => apply fuel context state (.callable candidate) args
        | none => .error "no Primus function definition accepts this number of arguments"
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
        if atom = "true" || atom = "false" || atom.startsWith ":" then .ok (atomValue atom, state)
        else
          match ← readLiteral atom with
          | some _ => .ok (atomValue atom, state)
          | none => .ok (← lookupState atom locals state, state)
      | .list [] => .ok (.list [], state)
      | .list (.atom "quote" :: [value]) =>
        .ok (quotedValue value, state)
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
      | .list (.atom "while" :: test :: body) =>
        let (test, testState) ← eval fuel locals context { state with code := [] } test
        match ← truth test with
        | some false => .ok (.unit, emit { testState with code := state.code } testState.code)
        | _ =>
          let condition ← condition context test
          let (_, bodyState) ← evalSequence fuel locals context { testState with code := [] } body
          -- the code computing the condition runs before every test of the condition
          .ok (.unit, emit { bodyState with code := state.code }
            (testState.code ++ [.while condition (bodyState.code ++ testState.code)]))
      | .list (.atom "error" :: _) =>
        match form with
        | .list [_, .atom message] => .error message
        | _ => .error "Primus error"
      | .list (.atom "msg" :: _) => .ok (.unit, state)
      | .list (.atom "let" :: .list bindings :: body) =>
        let (locals, state) ← bindings.foldlM (init := (locals, state)) fun current binding => do
          match binding with
          | .list [.atom name, value] =>
            let (value, state) ← eval fuel current.1 context current.2 value
            if (bindings ++ body).any (assignsLocal state.globals name 64) then
              let (value, state) ← bindAssignable context state value
              .ok ((name, value) :: current.1, state)
            else
              let (value, state) := freeze context state value
              .ok ((name, value) :: current.1, state)
          | _ => .error "invalid Primus let binding"
        evalSequence fuel locals context state body
      | .list (.atom "lambda" :: .list params :: body) =>
        let params ← params.mapM Sexp.asAtom
        .ok (.callable (.function params (definitionBody body) locals), state)
      | .list (.atom "case" :: key :: branches) =>
        let (key, state) ← eval fuel locals context state key
        let rec select : List Sexp → Except String (List Sexp)
          | [] => .error "Primus case has no matching branch"
          | [fallback] => .ok [fallback]
          | label :: body :: rest => do
            if ← caseMatches key label then .ok [body] else select rest
        evalSequence fuel locals context state (← select branches)
      | .list (.atom operator :: operands) =>
        let expansion ← match ← lookupState operator locals state with
          | .callable callable =>
            -- a local is a value, and macros are not values
            if (Assoc.get operator locals).isSome then .ok none else macroExpansion callable operands
          | _ => .ok none
        match expansion with
        | some expanded => evalSequence fuel locals context state expanded
        | none =>
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
        let args := if operation = 38 || operation = 39 || operation = 40 then resolveSymbol state args else args
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
  operation ≤ 12 || (20 ≤ operation && operation ≤ 50) || (52 ≤ operation && operation ≤ 61) || operation = 63

private def isSymbol (atom : String) : Bool :=
  match readLiteral atom with
  | .ok none => true
  | _ => false

mutual
  private def compileExp (globals : Globals) (locals : List String) : Nat → Sexp → Option CExp
    | 0, _ => none
    | fuel + 1, form =>
      match form with
      | .atom atom =>
        if atom = "true" || atom = "false" || atom.startsWith ":" then
          some (.value (atomValue atom))
        else
          match readLiteral atom with
          | .error _ => none
          | .ok (some _) => some (.value (atomValue atom))
          | .ok none =>
            match locals.findIdx? (· == atom) with
            | some slot => some (.local slot)
            | none =>
              -- the name of the built-in, which no definition hides
              if (if atom.startsWith "core:" then (atom.drop 5).toString else atom) = "replicate" then none
              else (globals.findIdx? fun binding => binding.1 == atom).map .global
      | .list [] => some (.value (.list []))
      | .list [.atom "quote", value] => some (.value (quotedValue value))
      | .list [.atom "replicate", _, _] | .list [.atom "core:replicate", _, _] => none
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
        compileBindings globals locals bindings fuel bindings body
      | .list (.atom "quote" :: _) | .list (.atom "sizeof" :: _) | .list (.atom "assert-msg" :: _)
      | .list (.atom "replicate" :: _) | .list (.atom "core:replicate" :: _)
      | .list (.atom "lambda" :: _) | .list (.atom "case" :: _) | .list (.atom "while" :: _)
      | .list (.atom "error" :: _) | .list (.atom "msg" :: _) | .list (.atom "let" :: _) => none
      | .list (.atom operator :: operands) =>
        let visible := locals.map fun name => (name, Value.unit)
        -- a literal does not name a function, whatever a definition says
        if operator = "true" || operator = "false" || operator.startsWith ":" || !isSymbol operator then none else
        match lookup operator visible globals with
        | .ok (.callable (.primitive name)) => do
          let operation ← primitiveIndex name
          if !compilablePrimitive operation then none
          let args ← operands.mapM (compileExp globals locals fuel)
          some (.primitive operation args)
        | .ok (.callable callable) => do
          -- a macro of a compiled function is expanded here, once
          match macroExpansion callable operands with
          | .ok (some expanded) => .sequence <$> compileSequence globals locals fuel expanded
          | .ok none =>
            let callable ← compileExp globals locals fuel (.atom operator)
            let args ← operands.mapM (compileExp globals locals fuel)
            some (.apply callable args)
          | .error _ => none
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

  private def compileBindings (globals : Globals) (locals : List String) (all : List Sexp) :
      Nat → List Sexp → List Sexp → Option CExp
    | 0, _, _ => none
    | fuel + 1, bindings, body =>
      match bindings with
      | [] => .sequence <$> compileSequence globals locals fuel body
      | .list [.atom name, value] :: rest => do
        -- Compiled locals are immutable slots, so assigned ones stay with the interpreter.
        if (all ++ body).any (assignsLocal globals name 64) then none
        let value ← compileExp globals locals fuel value
        .letIn value <$> compileBindings globals (name :: locals) all fuel rest body
      | _ => none
end

private def compileFunction (globals : Globals) : Callable → Callable
  | callable@(.function params body env) =>
    let locals := params ++ env.map Prod.fst
    match body.mapM (compileExp globals locals 1000) with
    | some body => .compiled params body env
    | none => callable
  | callable => callable

private def compileCallable (globals : Globals) : Callable → Callable
  | .overloads candidates => .overloads (candidates.map (compileFunction globals))
  | callable => compileFunction globals callable

private def compileValue (globals : Globals) (value : Value) : Value :=
  match value with
  | .callable callable => .callable (compileCallable globals callable)
  | _ => value

def compileGlobals (globals : Globals) : Globals :=
  globals.map fun binding => (binding.1, compileValue globals binding.2)

private def define (state : State) (name : String) (callable : Callable) : State :=
  let callable := addDefinition callable (Assoc.get name state.globals)
  { state with
    globals := Assoc.put name (.callable callable) state.globals
    operations := state.operations.insert name callable }

/-- A form of a source file. Only here definitions extend the globals, as upstream reads them with the
parser, so evaluating a form leaves the globals as they are. Methods handle the signals of the machine
and are not semantics. -/
private def evalTopLevel (context : Context) (state : State) (form : Sexp) : Except String State := do
  match form with
  | .list (.atom "defun" :: .atom name :: .list params :: body) =>
    let params ← params.mapM Sexp.asAtom
    if !contextMatches context body then .ok state
    else .ok (define state name (.function params (definitionBody body) []))
  | .list (.atom "defmacro" :: .atom name :: .list params :: body) =>
    let params ← params.mapM Sexp.asAtom
    if !contextMatches context body then .ok state
    else .ok (define state name (.macro params (definitionBody body)))
  | .list (.atom "defparameter" :: .atom name :: value :: _) =>
    let (value, state) ← eval 100000 [] context state value
    .ok { state with globals := Assoc.put name value state.globals }
  | .list (.atom "defmethod" :: _) => .ok state
  | form =>
    let (_, state) ← eval 100000 [] context state form
    .ok state

def evalForms (context : Context) (globals : Globals) (forms : List Sexp) :
    Except String State := do
  let forms := forms.filter fun form => match form with
    | .list (.atom kind :: _) =>
      kind != "declare" && kind != "defpackage" && kind != "in-package" && kind != "require"
    | _ => true
  forms.forM checkLiterals
  forms.foldlM (evalTopLevel context) { globals := globals, operations := indexGlobals globals }

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

/-- The core macros, which every program has upstream. -/
private def preludeName : String := "init"

def loadMany (directories entries : List String) (context : Context) : IO Globals := do
  let candidates : List System.FilePath := directories.map fun directory => s!"{directory}/{preludeName}.lisp"
  let prelude ← candidates.anyM fun path => System.FilePath.pathExists path
  let entries := if prelude then preludeName :: entries else entries
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
  match apply 100000 context { globals := environment.globals, operations := environment.operations } callable operands with
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
  match apply 100000 context { globals := environment.globals, operations := environment.operations } (.callable callable) operands with
  | .ok (_, state) => pure state.code
  | .error error => throw <| IO.userError s!"LLVM opcode {opcode}: {error}"

/-- The number of arguments a primitive takes, at least and, if bounded, at most. -/
private def primitiveArity (name : String) : Nat × Option Nat :=
  match name with
  | "not" | "lnot" | "neg" | "clz" | "car" | "cdr" | "length" | "null?" | "list?" | "load-byte" | "load-hword"
  | "load-word" | "is-zero" | "non-zero" | "unquote" | "alias-base-register" | "symbol" | "exec-addr"
  | "x86-prefix" | "fsqrt" | "fround" | "is-nan" | "is-inf" | "is-fzero" =>
    if name = "fsqrt" || name = "fround" then (2, some 2) else (1, some 1)
  | "=" | "/=" | "<" | "<=" | ">" | ">=" | "s<" | "s<=" | "s>" | "s>=" | "lshift" | "rshift" | "arshift"
  | "cast-low" | "cast-high" | "cast-signed" | "cast-unsigned" | "replicate" | "select" | "set" | "set$"
  | "set-symbol-value" | "cons" | "load-bits" | "store-word" | "store-byte" | "<." | ">." | ">=." | "=." =>
    (2, some 2)
  | "extract" | "cast-saturate" | "fconvert" | "cast-float" | "cast-sfloat" | "cast-int" | "cast-sint" =>
    (3, some 3)
  | "empty" | "get-program-counter" | "get-current-program-counter" | "get-next-program-counter" => (0, some 0)
  | "word-width" | "list" | "symbol-concat" => (0, none)
  | "+." | "-." | "*." | "/." => (2, none)
  | _ => (1, none)

mutual
  /-- Every name a form calls or reads, as the evaluator would resolve it, that has no definition, no
  definition of the right arity, or a body that cannot be expanded. Macros are checked as expanded. -/
  private def auditForm (context : Context) (globals : Globals) (locals : List String) :
      Nat → Sexp → List String
    | 0, _ => ["expansion too deep"]
    | fuel + 1, form =>
      let forms (items : List Sexp) := auditForms context globals locals fuel items
      match form with
      | .atom atom =>
        if atom = "true" || atom = "false" || atom.startsWith ":" || locals.contains atom then []
        else
          match readLiteral atom with
          | .error error => [error]
          | .ok (some _) => []
          | .ok none =>
            match lookup atom (locals.map fun name => (name, Value.unit)) globals with
            | .ok _ => []
            | .error _ => [s!"unknown symbol {atom}"]
      | .list [] => []
      | .list (.atom "quote" :: _) | .list (.atom "sizeof" :: _) | .list (.atom "msg" :: _)
      | .list (.atom "error" :: _) => []
      | .list [.atom "assert-msg", test, _] => forms [test]
      | .list [.atom "clz", value] => forms [value]
      | .list (.atom "if" :: items) | .list (.atom "when" :: items) | .list (.atom "unless" :: items)
      | .list (.atom "progn" :: items) | .list (.atom "prog" :: items) | .list (.atom "while" :: items) => forms items
      | .list (.atom "lambda" :: .list params :: body) =>
        let params := params.filterMap fun param => match param with
          | .atom name => some name
          | _ => none
        auditForms context globals (params ++ locals) fuel (definitionBody body)
      | .list (.atom "let" :: .list bindings :: body) => auditLet context globals locals fuel bindings body
      | .list (.atom "case" :: key :: branches) =>
        forms [key] ++ auditBranches context globals locals fuel branches
      | .list (.atom operator :: operands) =>
        let visible := locals.map fun name => (name, Value.unit)
        let call := match lookup operator visible globals with
          | .error _ => [s!"unknown function {operator}"]
          | .ok (.callable callable) =>
            if locals.contains operator then [] else
            match macroExpansion callable operands, callable with
            | .ok (some expanded), _ => auditForms context globals locals fuel expanded
            | .error error, _ => [s!"{operator} with {operands.length} operands: {error}"]
            | .ok none, .primitive name =>
              let (least, most) := primitiveArity name
              if least ≤ operands.length && (match most with
                  | some most => decide (operands.length ≤ most)
                  | none => decide (0 = 0)) then []
              else [s!"primitive {name} with {operands.length} arguments"]
            | .ok none, .function params .. | .ok none, .compiled params .. =>
              if params.length = operands.length then []
              else [s!"function {operator} with {operands.length} arguments, expects {params.length}"]
            | .ok none, .overloads candidates =>
              match resolveFunction operands.length candidates with
              | some _ => []
              | none => [s!"function {operator} has no definition for {operands.length} arguments"]
            | .ok none, .macro .. => []
          | .ok _ => if locals.contains operator then [] else [s!"{operator} is not a function"]
        let expandsMacro := match lookup operator visible globals with
          | .ok (.callable callable) => !locals.contains operator && !(macroCandidates callable).isEmpty
          | _ => false
        call ++ (if expandsMacro then [] else forms operands)
      | .list items => forms items

  private def auditForms (context : Context) (globals : Globals) (locals : List String) (fuel : Nat) :
      List Sexp → List String
    | [] => []
    | form :: rest => auditForm context globals locals fuel form ++ auditForms context globals locals fuel rest

  private def auditLet (context : Context) (globals : Globals) (locals : List String) (fuel : Nat)
      (bindings body : List Sexp) : List String :=
    match bindings with
    | [] => auditForms context globals locals fuel body
    | .list [.atom name, value] :: rest =>
      auditForm context globals locals fuel value ++ auditLet context globals (name :: locals) fuel rest body
    | _ :: _ => ["invalid let binding"]

  private def auditBranches (context : Context) (globals : Globals) (locals : List String) (fuel : Nat) :
      List Sexp → List String
    | [] => []
    | [fallback] => auditForm context globals locals fuel fallback
    | _ :: body :: rest =>
      auditForm context globals locals fuel body ++ auditBranches context globals locals fuel rest
end

/-- The findings of a static check of all loaded functions against the names of `globals`. -/
def auditGlobals (context : Context) (globals : Globals) : List (String × String) :=
  let functions (callable : Callable) : List Callable := match callable with
    | .overloads candidates => candidates
    | callable => [callable]
  globals.flatMap fun binding =>
    match binding.2 with
    | .callable callable =>
      (functions callable).flatMap fun candidate =>
        match candidate with
        | .function params body env =>
          (auditForms context globals (params ++ env.map Prod.fst) 64 body).map fun finding => (binding.1, finding)
        | _ => []
    | _ => []

def register (name : String) (width baseWidth : Nat) : Value := .register name width baseWidth

def immediate (value : Int) : Value := .bil 64 (.int (BitVec.ofInt 64 value))

end Bap.Primus.Semantics
