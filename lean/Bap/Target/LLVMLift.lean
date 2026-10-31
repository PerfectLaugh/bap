import Bap.LLVM
import Bap.Disasm.Basic
import Bap.Primus.Semantics

namespace Bap.Target.LLVMLift

/-- The status registers of AArch64 with their widths, and `R31`, the name of the stack pointer. -/
private def aarch64StatusRegister (name : String) : Option Primus.Semantics.Value :=
  match name with
  | "SPSel" | "PAN" | "UAO" => some (.register name 1 1)
  | "DAIF" => some (.register name 4 4)
  | "FPCR" | "FPSR" => some (.register name 32 32)
  | "SP_EL0" | "SP_EL1" | "CNTVCT_EL0" => some (.register name 64 64)
  | "R31" => some (.register "SP" 64 64)
  | _ => none

private def aarch64Register (name : String) : Primus.Semantics.Value :=
  let name := if name = "LR" then "X30" else if name = "FP" then "X29" else name
  if name = "XZR" || name = "WZR" then
    .register "XZR" 64 64
  else if name = "WSP" then
    .register "SP" 32 64
  else if let some register := aarch64StatusRegister name then
    register
  else if name.startsWith "B" && (name.drop 1).all Char.isDigit then
    .register ("Q" ++ name.drop 1) 8 128
  else if name.startsWith "H" && (name.drop 1).all Char.isDigit then
    .register ("Q" ++ name.drop 1) 16 128
  else if name.startsWith "S" && (name.drop 1).all Char.isDigit then
    .register ("Q" ++ name.drop 1) 32 128
  else if name.startsWith "D" && (name.drop 1).all Char.isDigit then
    .register ("Q" ++ name.drop 1) 64 128
  else if name.startsWith "Q" && (name.drop 1).all Char.isDigit then
    .register name 128 128
  else if name.startsWith "W" && (name.drop 1).all Char.isDigit then
    .register ("X" ++ name.drop 1) 32 64
  else if name.startsWith "X" && (name.drop 1).all Char.isDigit then
    .register name 64 64
  else if name = "SP" then
    .register name 64 64
  else if ["NF", "ZF", "CF", "VF"].contains name then
    .register name 1 1
  else
    .register name 64 64

/-- XMM and YMM are the low bits of ZMM, the one register they name. A mask register is a register of its own, of the
64 bits it has in both modes. -/
private def x86VectorRegister (name : String) : Option Primus.Semantics.Value :=
  match name.toList with
  | 'X' :: 'M' :: 'M' :: digit :: digits =>
    if (digit :: digits).all Char.isDigit then
      some (.register ("ZMM" ++ String.ofList (digit :: digits)) 128 512)
    else none
  | 'Y' :: 'M' :: 'M' :: digit :: digits =>
    if (digit :: digits).all Char.isDigit then
      some (.register ("ZMM" ++ String.ofList (digit :: digits)) 256 512)
    else none
  | 'Z' :: 'M' :: 'M' :: digit :: digits =>
    if (digit :: digits).all Char.isDigit then some (.register name 512 512) else none
  | ['K', digit] => if digit.isDigit then some (.register name 64 64) else none
  | _ => none

/-- The 64-bit base and the width of a low partial x86 general purpose register. -/
private def x86LowRegister (name : String) : Option (String × Nat) :=
  match name with
  | "EAX" => some ("RAX", 32) | "AX" => some ("RAX", 16) | "AL" => some ("RAX", 8)
  | "EBX" => some ("RBX", 32) | "BX" => some ("RBX", 16) | "BL" => some ("RBX", 8)
  | "ECX" => some ("RCX", 32) | "CX" => some ("RCX", 16) | "CL" => some ("RCX", 8)
  | "EDX" => some ("RDX", 32) | "DX" => some ("RDX", 16) | "DL" => some ("RDX", 8)
  | "ESI" => some ("RSI", 32) | "SI" => some ("RSI", 16) | "SIL" => some ("RSI", 8)
  | "EDI" => some ("RDI", 32) | "DI" => some ("RDI", 16) | "DIL" => some ("RDI", 8)
  | "EBP" => some ("RBP", 32) | "BP" => some ("RBP", 16) | "BPL" => some ("RBP", 8)
  | "ESP" => some ("RSP", 32) | "SP" => some ("RSP", 16) | "SPL" => some ("RSP", 8)
  | "R8D" => some ("R8", 32) | "R8W" => some ("R8", 16) | "R8B" => some ("R8", 8)
  | "R9D" => some ("R9", 32) | "R9W" => some ("R9", 16) | "R9B" => some ("R9", 8)
  | "R10D" => some ("R10", 32) | "R10W" => some ("R10", 16) | "R10B" => some ("R10", 8)
  | "R11D" => some ("R11", 32) | "R11W" => some ("R11", 16) | "R11B" => some ("R11", 8)
  | "R12D" => some ("R12", 32) | "R12W" => some ("R12", 16) | "R12B" => some ("R12", 8)
  | "R13D" => some ("R13", 32) | "R13W" => some ("R13", 16) | "R13B" => some ("R13", 8)
  | "R14D" => some ("R14", 32) | "R14W" => some ("R14", 16) | "R14B" => some ("R14", 8)
  | "R15D" => some ("R15", 32) | "R15W" => some ("R15", 16) | "R15B" => some ("R15", 8)
  | _ => none

/-- The 64-bit base of a high byte register. -/
private def x86HighByteBase (name : String) : Option String :=
  match name with
  | "AH" => some "RAX" | "BH" => some "RBX" | "CH" => some "RCX" | "DH" => some "RDX"
  | _ => none

/-- The 32-bit base of a high byte register. -/
private def x8632HighByteBase (name : String) : Option String :=
  match name with
  | "AH" => some "EAX" | "BH" => some "EBX" | "CH" => some "ECX" | "DH" => some "EDX"
  | _ => none

/-- The registers of x87, the control and status words and the segments, which have the same widths in both modes,
as in `x86_target` of the reference implementation. -/
private def x86FloatRegister (name : String) : Option Primus.Semantics.Value :=
  match name with
  | "ST0" | "ST1" | "ST2" | "ST3" | "ST4" | "ST5" | "ST6" | "ST7" => some (.register name 80 80)
  | "FPU_CONTROL" | "FPU_STATUS" | "FPU_TAG" | "CS" | "DS" | "ES" | "FS" | "GS" | "SS" => some (.register name 16 16)
  | "MXCSR" | "EFLAGS" => some (.register name 32 32)
  | _ => none

/-- `Value.register` views the low bits of its base, so a high byte keeps its own name while it is
lifted and `resolveAliases` turns it into bits 15 to 8 of the base afterwards. -/
private def x86Register (name : String) : Primus.Semantics.Value :=
  let name := if name.isEmpty || name = "NoRegister" then "Nil" else name
  if ["CF", "OF", "SF", "ZF", "AF", "PF", "DF", "IF"].contains name then
    .register name 1 1
  else if (x86HighByteBase name).isSome then
    .register name 8 8
  else
    match x86LowRegister name with
    | some (base, width) => .register base width 64
    | none =>
      match x86FloatRegister name with
      | some register => register
      | none => (x86VectorRegister name).getD (.register name 64 64)

/-- Bits `high` to `low` of a register of `width` bits: a part of a register that has no variable
of its own, as an alias of `Theory.Target` has. -/
structure AliasPart where
  base : String
  width : Nat
  high : Nat
  low : Nat
  deriving DecidableEq, Repr

namespace AliasPart

def var (part : AliasPart) : Bap.Var := ⟨part.base, .imm part.width, 0, false⟩

def size (part : AliasPart) : Nat := part.high + 1 - part.low

def read (part : AliasPart) : Bil.Exp :=
  if part.low = 0 ∧ part.high + 1 = part.width then .var part.var
  else .extract part.high part.low (.var part.var)

/-- Sets the part to `value` and keeps the other bits of the base. -/
def write (part : AliasPart) (value : Bil.Exp) : Bil.Stmt :=
  let below := if part.low = 0 then value else .concat value (.extract (part.low - 1) 0 (.var part.var))
  .move part.var
    (if part.high + 1 < part.width then
      .concat (.extract (part.width - 1) (part.high + 1) (.var part.var)) below
    else below)

end AliasPart

/-- An alias: the parts it consists of, from the most significant. -/
abbrev Alias := AliasPart × List AliasPart

/-- The value of an alias. -/
def aliasRead : Alias → Bil.Exp
  | (part, []) => part.read
  | (part, next :: rest) => .concat part.read (aliasRead (next, rest))
termination_by alias => alias.2.length
decreasing_by simp

/-- The variable an alias of several parts is computed into, as they can be in its value. -/
def aliasTemporary (typ : Typ) : Bap.Var := ⟨"_alias", typ, 0, false⟩

/-- Sets each of the parts, the lowest is at the bit `offset`, to their bits of `source`. -/
def aliasWrites (source : Bil.Exp) : Nat → List AliasPart → Bil.Program
  | _, [] => []
  | offset, part :: rest =>
    let low := offset - part.size
    part.write (.extract (offset - 1) low source) :: aliasWrites source low rest

/-- An assignment to an alias of a variable of the type `typ`. -/
def aliasWrite (typ : Typ) (value : Bil.Exp) : Alias → Bil.Program
  | (part, []) => [part.write value]
  | (part, rest) =>
    let temporary := aliasTemporary typ
    .move temporary value ::
      aliasWrites (.var temporary) ((part :: rest).foldr (fun part size => part.size + size) 0) (part :: rest)

private def aliasExp (aliases : String → Option Alias) : Bil.Exp → Bil.Exp
  | .var var =>
    match aliases var.name with
    | some alias => aliasRead alias
    | none => .var var
  | .load memory address endian size =>
    .load (aliasExp aliases memory) (aliasExp aliases address) endian size
  | .store memory address value endian size =>
    .store (aliasExp aliases memory) (aliasExp aliases address) (aliasExp aliases value) endian size
  | .bin op left right => .bin op (aliasExp aliases left) (aliasExp aliases right)
  | .un op value => .un op (aliasExp aliases value)
  | .cast kind size value => .cast kind size (aliasExp aliases value)
  | .letIn var value body => .letIn var (aliasExp aliases value) (aliasExp aliases body)
  | .ite condition yes no =>
    .ite (aliasExp aliases condition) (aliasExp aliases yes) (aliasExp aliases no)
  | .extract high low value => .extract high low (aliasExp aliases value)
  | .concat left right => .concat (aliasExp aliases left) (aliasExp aliases right)
  | exp => exp

/-- Rewrites the aliases of a lifted program to the registers they are parts of. -/
private def resolveAliases (aliases : String → Option Alias) : Bil.Program → Bil.Program
  | [] => []
  | .move var value :: rest =>
    let value := aliasExp aliases value
    match aliases var.name with
    | some alias => aliasWrite var.typ value alias ++ resolveAliases aliases rest
    | none => .move var value :: resolveAliases aliases rest
  | .jmp target :: rest => .jmp (aliasExp aliases target) :: resolveAliases aliases rest
  | .while condition body :: rest =>
    .while (aliasExp aliases condition) (resolveAliases aliases body) :: resolveAliases aliases rest
  | .ifElse condition yes no :: rest =>
    .ifElse (aliasExp aliases condition) (resolveAliases aliases yes) (resolveAliases aliases no) ::
      resolveAliases aliases rest
  | stmt :: rest => stmt :: resolveAliases aliases rest

/-- A flag of a single bit, the whole of its variable. -/
def flagPart (name : String) : AliasPart := ⟨name, 1, 0, 0⟩

/-- The bits of EFLAGS from the most significant one, as in `x86_target` of the reference implementation: each is a
variable of its own, and the reserved ones are kept as they are written. -/
private def x86FlagBits : List String :=
  ["AI", "AES", "EFLAGS_29", "EFLAGS_28", "EFLAGS_27", "EFLAGS_26", "EFLAGS_25", "EFLAGS_24", "EFLAGS_23", "EFLAGS_22",
    "ID", "VIP", "VIF", "AC", "VM", "RF", "MD", "NT", "IOPLH", "IOPLL", "OF", "DF", "IF", "TF", "SF", "ZF", "EFLAGS_5",
    "AF", "EFLAGS_3", "PF", "EFLAGS_1", "CF"]

/-- The aliases of x86 that the views of `Value.register` cannot express: the high bytes, in a base of `width` bits,
and EFLAGS, which is the flags. -/
private def x86Aliases (base : String → Option String) (width : Nat) (name : String) : Option Alias :=
  if name = "EFLAGS" then
    some (flagPart "AI", x86FlagBits.tail.map flagPart)
  else
    (base name).map fun base => (⟨base, width, 15, 8⟩, [])

private def aarch64Globals : Primus.Semantics.Globals :=
  let registers := (List.range 31).map fun n => s!"X{n}"
  let vectors := (List.range 32).flatMap fun n => [s!"B{n}", s!"H{n}", s!"S{n}", s!"D{n}", s!"Q{n}"]
  (registers ++ vectors ++ ["SP", "LR", "XZR", "NF", "ZF", "CF", "VF", "TPIDR_EL0", "TPIDRRO_EL0", "DAIF", "SPSel",
      "SP_EL0", "SP_EL1", "R31", "UAO", "PAN", "CNTVCT_EL0", "FPCR", "FPSR"]).map
    fun name => (name, aarch64Register name)

/-- The registers of x87 and the control and status words. -/
private def x86FloatNames : List String :=
  (List.range 8).map (fun n => s!"ST{n}") ++ ["FPU_CONTROL", "FPU_STATUS", "FPU_TAG", "MXCSR", "EFLAGS"]

/-- The vector registers that the semantics can name directly, e.g., the implicit result of `PCMPISTRM`. -/
private def x86VectorNames (count : Nat) : List String :=
  (List.range count).flatMap fun n => [s!"XMM{n}", s!"YMM{n}", s!"ZMM{n}"]

private def x86Globals : Primus.Semantics.Globals :=
  let registers := ["RAX", "RBX", "RCX", "RDX", "RSI", "RDI", "RBP", "RSP",
    "EAX", "EBX", "ECX", "EDX", "ESI", "EDI", "EBP", "ESP", "RIP",
    "AX", "BX", "CX", "DX", "SI", "DI", "BP", "SP",
    "AL", "BL", "CL", "DL", "SIL", "DIL", "BPL", "SPL", "AH", "BH", "CH", "DH",
    "CF", "OF", "SF", "ZF", "AF", "PF", "DF", "IF", "FS_BASE", "GS_BASE"] ++ x86FloatNames ++ x86VectorNames 32
  registers.map fun name => (name, x86Register name)

private def x8632Register (name : String) : Primus.Semantics.Value :=
  let name := if name.isEmpty || name = "NoRegister" then "Nil" else name
  if ["CF", "OF", "SF", "ZF", "AF", "PF", "DF", "IF"].contains name then
    .register name 1 1
  else if (x8632HighByteBase name).isSome then
    .register name 8 8
  else
    match name with
    | "AX" => .register "EAX" 16 32 | "AL" => .register "EAX" 8 32
    | "BX" => .register "EBX" 16 32 | "BL" => .register "EBX" 8 32
    | "CX" => .register "ECX" 16 32 | "CL" => .register "ECX" 8 32
    | "DX" => .register "EDX" 16 32 | "DL" => .register "EDX" 8 32
    | "SI" => .register "ESI" 16 32 | "DI" => .register "EDI" 16 32
    | "BP" => .register "EBP" 16 32 | "SP" => .register "ESP" 16 32
    | _ =>
      match x86FloatRegister name with
      | some register => register
      | none => (x86VectorRegister name).getD (.register name 32 32)

private def x8632Globals : Primus.Semantics.Globals :=
  let registers := ["EAX", "EBX", "ECX", "EDX", "ESI", "EDI", "EBP", "ESP", "EIP",
    "AX", "BX", "CX", "DX", "SI", "DI", "BP", "SP", "AL", "BL", "CL", "DL", "AH", "BH", "CH", "DH",
    "CF", "OF", "SF", "ZF", "AF", "PF", "DF", "IF", "FS_BASE", "GS_BASE"] ++ x86FloatNames ++ x86VectorNames 8
  registers.map fun name => (name, x8632Register name)

private def riscvRegister (name : String) : Primus.Semantics.Value :=
  if name = "X0" then .register "XZR" 64 64 else .register name 64 64

/-- The control and status registers, which have 32 bits in both widths of the architecture. -/
private def riscvStatusGlobals : Primus.Semantics.Globals :=
  [("FCSR", .register "FCSR" 32 32), ("VXRM", .register "VXRM" 32 32)]

/-- The floating point registers, which have 64 bits (FLEN) in both widths of the architecture. -/
private def riscvFloatGlobals : Primus.Semantics.Globals :=
  (List.range 32).map fun n => (s!"F{n}", .register s!"F{n}" 64 64)

private def riscvGlobals : Primus.Semantics.Globals :=
  (List.range 32).map (fun n => (s!"X{n}", riscvRegister s!"X{n}")) ++ riscvFloatGlobals ++ riscvStatusGlobals

private def riscv32Register (name : String) : Primus.Semantics.Value :=
  if name = "X0" then .register "XZR" 32 32 else .register name 32 32

private def riscv32Globals : Primus.Semantics.Globals :=
  (List.range 32).map (fun n => (s!"X{n}", riscv32Register s!"X{n}")) ++ riscvFloatGlobals ++ riscvStatusGlobals

/-- The flags of the floating point comparisons. -/
private def powerpcFloatFlags : List String := ["FL", "FG", "FE", "FU"]

/-- The fields of the condition register, e.g., `CR0`, are the aliases of their bits. -/
private def powerpcConditionField (name : String) : Bool :=
  ["CR0", "CR1", "CR2", "CR3", "CR4", "CR5", "CR6", "CR7"].contains name

private def powerpcAliases (name : String) : Option Alias :=
  if powerpcConditionField name then
    some (flagPart s!"{name}LT", [flagPart s!"{name}GT", flagPart s!"{name}EQ", flagPart s!"{name}UN"])
  else none

private def powerpcRegister (name : String) : Primus.Semantics.Value :=
  let isConditionBit := (name.startsWith "CR" &&
    (name.endsWith "LT" || name.endsWith "GT" || name.endsWith "EQ" || name.endsWith "UN")) ||
    ["SO", "OV", "CA", "OV32", "CA32"].contains name
  if powerpcFloatFlags.contains name then .register name 1 1
  else if powerpcConditionField name then .register name 4 4
  else if isConditionBit then .register name 1 1
  else if name = "ZERO" then .register "XZR" 64 64
  else if name.startsWith "X" && (name.drop 1).all Char.isDigit then
    .register ("R" ++ (name.drop 1).toString) 64 64
  else .register name 64 64

private def powerpcGlobals : Primus.Semantics.Globals :=
  let registers := (List.range 32).map fun n => s!"R{n}"
  let conditionFields := (List.range 8).flatMap fun n =>
    [s!"CR{n}LT", s!"CR{n}GT", s!"CR{n}EQ", s!"CR{n}UN"]
  let fields := (List.range 8).map fun n => s!"CR{n}"
  (registers ++ conditionFields ++ fields ++ powerpcFloatFlags ++ ["ZERO", "LR", "CTR", "TAR", "SO", "OV", "CA", "OV32", "CA32"]).map
    fun name => (name, powerpcRegister name)

private def powerpc32Register (name : String) : Primus.Semantics.Value :=
  let isConditionBit := (name.startsWith "CR" &&
    (name.endsWith "LT" || name.endsWith "GT" || name.endsWith "EQ" || name.endsWith "UN")) ||
    ["SO", "OV", "CA", "OV32", "CA32"].contains name
  if powerpcFloatFlags.contains name then .register name 1 1
  else if powerpcConditionField name then .register name 4 4
  else if isConditionBit then .register name 1 1
  else if name = "ZERO" then .register "XZR" 32 32
  else if name.startsWith "X" && (name.drop 1).all Char.isDigit then
    .register ("R" ++ (name.drop 1).toString) 32 32
  else .register name 32 32

private def powerpc32Globals : Primus.Semantics.Globals :=
  let registers := (List.range 32).map fun n => s!"R{n}"
  let conditionFields := (List.range 8).flatMap fun n =>
    [s!"CR{n}LT", s!"CR{n}GT", s!"CR{n}EQ", s!"CR{n}UN"]
  let fields := (List.range 8).map fun n => s!"CR{n}"
  (registers ++ conditionFields ++ fields ++ powerpcFloatFlags ++ ["ZERO", "LR", "CTR", "TAR", "SO", "OV", "CA", "OV32", "CA32"]).map
    fun name => (name, powerpc32Register name)

private def mipsRegisterName (name : String) : String :=
  match name with
  | "R0" | "ZERO" | "$zero" => "XZR"
  | "AT" => "R1" | "V0" => "R2" | "V1" => "R3"
  | "A0" => "R4" | "A1" => "R5" | "A2" => "R6" | "A3" => "R7"
  | "T0" => "R8" | "T1" => "R9" | "T2" => "R10" | "T3" => "R11"
  | "T4" => "R12" | "T5" => "R13" | "T6" => "R14" | "T7" => "R15"
  | "S0" => "R16" | "S1" => "R17" | "S2" => "R18" | "S3" => "R19"
  | "S4" => "R20" | "S5" => "R21" | "S6" => "R22" | "S7" => "R23"
  | "T8" => "R24" | "T9" => "R25" | "K0" => "R26" | "K1" => "R27"
  | "GP" => "R28" | "SP" => "R29" | "FP" | "S8" => "R30" | "RA" | "$ra" => "R31"
  | name => name

/-- A numeric spelling `$n` is the register `n`, and `$0` is the zero register. -/
private def mipsDollarName (name : String) : String :=
  match name.toList with
  | '$' :: digits =>
    if digits.all Char.isDigit then mipsRegisterName ("R" ++ String.ofList digits) else name
  | _ => name

/-- LLVM names the 64-bit view of a general purpose register with a suffix, e.g., `V0_64`. The
floating point registers `F0_64` and `D0_64` do not alias a canonical name and stay as they are. -/
private def mipsCanonicalName (name : String) : String :=
  let chars := name.toList
  let size := chars.length - 3
  let plain := if chars.drop size == ['_', '6', '4'] then String.ofList (chars.take size) else name
  let canonical := mipsRegisterName plain
  if canonical != plain then canonical else mipsDollarName (mipsRegisterName name)

/-- The condition codes of the FPU, which are bits. -/
private def mipsConditionCode (name : String) : Bool :=
  ["FCC0", "FCC1", "FCC2", "FCC3", "FCC4", "FCC5", "FCC6", "FCC7"].contains name

private def mipsRegister (name : String) : Primus.Semantics.Value :=
  if mipsConditionCode name then .register name 1 1 else .register (mipsCanonicalName name) 64 64

/-- The registers of both widths: the integer and floating point registers, which are words, and the condition codes. -/
private def mipsRegisterNames : List String :=
  (List.range 32).map (fun n => s!"R{n}") ++ (List.range 32).map (fun n => s!"F{n}") ++
    (List.range 8).map (fun n => s!"FCC{n}") ++ ["ZERO", "RA", "HI", "LO", "USERLOCAL"]

private def mipsGlobals : Primus.Semantics.Globals :=
  mipsRegisterNames.map fun name => (name, mipsRegister name)

private def mips32Register (name : String) : Primus.Semantics.Value :=
  if mipsConditionCode name then .register name 1 1 else .register (mipsCanonicalName name) 32 32

private def mips32Globals : Primus.Semantics.Globals :=
  mipsRegisterNames.map fun name => (name, mips32Register name)

/-- The floating point registers of release 6 have 64 bits also on MIPS32, see `fpr64` of the semantics. -/
private def mips32r6Register (name : String) : Primus.Semantics.Value :=
  match name.toList with
  | 'F' :: digit :: digits =>
    if (digit :: digits).all Char.isDigit then .register name 64 64 else mips32Register name
  | _ => mips32Register name

private def mips32r6Globals : Primus.Semantics.Globals :=
  mipsRegisterNames.map fun name => (name, mips32r6Register name)

private def mips32Operand (release6 : Bool) : LLVM.Operand → Primus.Semantics.Value
  | .reg name => if release6 then mips32r6Register name else mips32Register name
  | .imm value => .bil 32 (.int (BitVec.ofInt 32 value))

/-- The number that the digits are the decimal digits of. -/
private def decimalDigits (digits : List Char) : Option Nat :=
  if digits.isEmpty || !digits.all Char.isDigit then none
  else some (digits.foldl (fun value digit => value * 10 + (digit.toNat - '0'.toNat)) 0)

private def arm32Register (name : String) : Primus.Semantics.Value :=
  let name := if name.isEmpty || name = "NoRegister" then "Nil" else name
  if ["NF", "ZF", "CF", "VF", "QF"].contains name then .register name 1 1
  else
    match name.toList with
    | 'D' :: digits => .register name (if (decimalDigits digits).isSome then 64 else 32) (if (decimalDigits digits).isSome then 64 else 32)
    | 'Q' :: digits => .register name (if (decimalDigits digits).isSome then 128 else 32) (if (decimalDigits digits).isSome then 128 else 32)
    | _ => .register name 32 32

/-- A register of VFP, which has 64 bits. -/
private def armDoublePart (number high low : Nat) : AliasPart := ⟨s!"D{number}", 64, high, low⟩

/-- As in the architecture: `Sn` are the halves of `D0` to `D15`, and `Qn` the pairs of `D0` to `D31`. -/
private def armAliases (name : String) : Option Alias :=
  match name.toList with
  | 'S' :: digits =>
    (decimalDigits digits).bind fun number =>
      if number < 32 then
        some (if number % 2 = 1 then armDoublePart (number / 2) 63 32 else armDoublePart (number / 2) 31 0, [])
      else none
  | 'Q' :: digits =>
    (decimalDigits digits).bind fun number =>
      if number < 16 then some (armDoublePart (2 * number + 1) 63 0, [armDoublePart (2 * number) 63 0]) else none
  | _ => none

private def arm32Globals : Primus.Semantics.Globals :=
  let registers := (List.range 16).map fun n => s!"R{n}"
  let doubles := (List.range 32).map fun n => s!"D{n}"
  (registers ++ doubles ++ ["SP", "LR", "PC", "CPSR", "Nil", "NF", "ZF", "CF", "VF", "QF", "FPSCR", "TPIDRURO", "TPIDRURW"]).map
    fun name => (name, arm32Register name)

private def semanticsContext (address nextPc : Nat) : Primus.Semantics.Context :=
  { bits := 64, pc := address, nextPc := nextPc }

private def pluginDirectories (target : String) : IO (List String) := do
  let configured ← IO.getEnv "BAP_SEMANTICS_DIR"
  let roots := match configured with
    | some root => [root]
    | none => ["semantics", "lean/semantics"]
  pure (roots.flatMap fun root => [s!"{root}/{target}", s!"{root}/core"])

private def immediate (opcode : String) (value : Int) : Primus.Semantics.Value :=
  if opcode.endsWith "ri32" || opcode.endsWith "mi32" || opcode.endsWith "i32" then
    .bil 64 (.int (BitVec.signExtend 64 (BitVec.ofInt 32 value)))
  else
    Primus.Semantics.immediate value

private def operand (register : String → Primus.Semantics.Value)
    (opcode : String) : LLVM.Operand → Primus.Semantics.Value
  | .reg name => register name
  | .imm value => immediate opcode value

/-- The names of the primitives of the semantics, all but the one they handle before they look up a name. -/
def semanticsPrimitives : List String :=
  Primus.Semantics.primitiveNames.filter (· != "replicate")

/-- The primitives that no definition hides, as bindings, which is what a lookup of their names finds after the globals. -/
private def primitiveGlobals (definitions : Primus.Semantics.Globals) : Primus.Semantics.Globals :=
  (semanticsPrimitives.filter fun name => (Assoc.get name definitions).isNone).map fun name =>
    (name, .callable (.primitive name))

/-- The definitions of a target, and the instructions by the numbers of their LLVM opcodes and by name. Those that aren't
instructions, which the others call, are compiled, and each instruction is when it is first lifted. A lookup of a register
goes along the list, so the primitives and the registers come first, and last the instructions, which nothing calls. This
doesn't change what a name resolves to. `aliases` are the names that LLVM has for some definitions. -/
private def compiledDefinitions (aliases : List (String × String)) (triple : String)
    (registers definitions : Primus.Semantics.Globals) :
    IO (Primus.Semantics.Environment) := do
  let numbered ← definitions.mapM fun binding => do
    match binding.2 with
    | .callable _ => pure (binding, ← LLVM.opcodeId? triple ((Assoc.get binding.1 aliases).getD binding.1))
    | _ => pure (binding, none)
  let (instructions, others) := numbered.partition fun entry => entry.2.isSome
  let registers := primitiveGlobals definitions ++ registers
  let lazy := instructions.filterMap fun entry =>
    match entry.1.2, entry.2 with
    | .callable callable, some opcode => some ((entry.1.1, callable), opcode)
    | _, _ => none
  pure (Primus.Semantics.Environment.thunked (registers ++ others.map Prod.fst) lazy)

/-- A target whose instructions are lifted by the names of their LLVM opcodes. -/
private def makeEnvironment (triple : String) (registers definitions : Primus.Semantics.Globals) :
    IO Primus.Semantics.Environment := do
  let environment ← compiledDefinitions [] triple registers definitions
  pure { environment with opcodes := {} }

/-- The semantics take long to load and they are the same each time, so a program loads the ones of a target once. -/
private def cached (cache : IO.Ref (Option Primus.Semantics.Environment)) (build : IO Primus.Semantics.Environment) :
    IO Primus.Semantics.Environment := do
  match ← cache.get with
  | some environment => pure environment
  | none =>
    let environment ← build
    cache.set (some environment)
    pure environment

/-- The x86 opcodes whose first operand is a displacement from the next instruction. -/
private def x86RelativeOpcodes : List String :=
  ["JMP_1", "JMP_2", "JMP_4", "JCC_1", "JCC_2", "JCC_4", "JCXZ", "JECXZ", "JRCXZ",
    "LOOP", "LOOPE", "LOOPNE", "XBEGIN_2", "XBEGIN_4",
    "CALLpcrel16", "CALLpcrel32", "CALL64pcrel32"]

private initialize aarch64Cache : IO.Ref (Option Primus.Semantics.Environment) ← IO.mkRef none

def aarch64Environment : IO Primus.Semantics.Environment := cached aarch64Cache do
  let context := semanticsContext 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "arm") ["aarch64"] context
  let environment ← compiledDefinitions [] "aarch64" aarch64Globals definitions
  let names := (List.range 31).flatMap (fun n => [s!"X{n}", s!"W{n}"]) ++
    (List.range 32).flatMap (fun n => [s!"B{n}", s!"H{n}", s!"S{n}", s!"D{n}", s!"Q{n}"]) ++
    ["SP", "WSP", "XZR", "WZR"]
  let registers ← names.mapM fun name => do
    let llvmName := if name = "X29" then "FP" else if name = "X30" then "LR" else name
    let id ← LLVM.registerId "aarch64" llvmName
    pure (id, aarch64Register name)
  pure (environment.withRegisters registers)

private initialize x86Cache : IO.Ref (Option Primus.Semantics.Environment) ← IO.mkRef none

private def x86EnvironmentWith (extra : List String) : IO Primus.Semantics.Environment := do
  let context := semanticsContext 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "x86")
    (["bits", "x86-64", "x86-bits", "x86-move", "x86-arith", "x86-control", "x86-shift", "x86-bmi", "x86-sse", "x86-simd",
      "x86-pcmpstr", "x86-sse-intrinsics"] ++ extra) context
  let environment ← compiledDefinitions [("RETQ", "RET64"), ("NOP", "NOOP")] "x86_64" x86Globals definitions
  let registers ← LLVM.registerNames "x86_64"
  let registers := (0, x86Register "Nil") ::
    (registers.map fun binding => (binding.1, x86Register binding.2))
  let signExtendedOpcodes ← definitions.filterMapM fun binding =>
    if binding.1.endsWith "i32" then LLVM.opcodeId? "x86_64" binding.1 else pure none
  let relativeOpcodes ← x86RelativeOpcodes.filterMapM (LLVM.opcodeId? "x86_64")
  pure { environment.withRegisters registers with
    signExtendedOpcodes := Std.HashSet.ofList signExtendedOpcodes
    relativeOpcodes := Std.HashSet.ofList relativeOpcodes }

def x86Environment : IO Primus.Semantics.Environment := cached x86Cache (x86EnvironmentWith [])

private initialize x86AvxCache : IO.Ref (Option Primus.Semantics.Environment) ← IO.mkRef none

/-- With AVX-512. It is loaded when an instruction first needs it, as most programs have none of them. -/
def x86AvxEnvironment : IO Primus.Semantics.Environment := cached x86AvxCache (x86EnvironmentWith ["x86-avx512"])

/-- The names that LLVM has for the formats of a floating point register, e.g., `F10_D`, which `fpr-name` of the
semantics takes to the register. -/
private def riscvFloatRegisters (triple : String) : IO (List (Nat × Primus.Semantics.Value)) := do
  let names ← LLVM.registerNames triple
  pure (names.filterMap fun binding =>
    if binding.2.startsWith "F" && (binding.2.endsWith "_D" || binding.2.endsWith "_F" || binding.2.endsWith "_H") then
      some (binding.1, .register binding.2 64 64)
    else none)

private initialize riscvCache : IO.Ref (Option Primus.Semantics.Environment) ← IO.mkRef none

def riscvEnvironment : IO Primus.Semantics.Environment := cached riscvCache do
  let context := semanticsContext 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "riscv") ["riscv"] context
  let environment ← compiledDefinitions [] "riscv64" riscvGlobals definitions
  let registers ← (List.range 32).mapM fun n => do
    let id ← LLVM.registerId "riscv64" s!"X{n}"
    pure (id, riscvRegister s!"X{n}")
  let floats ← riscvFloatRegisters "riscv64"
  pure (environment.withRegisters (registers ++ floats))

/-- The semantics of a target of several variants, each loaded once. -/
private def cachedVariant [BEq α] (cache : IO.Ref (List (α × Primus.Semantics.Environment))) (variant : α)
    (build : IO Primus.Semantics.Environment) : IO Primus.Semantics.Environment := do
  match (← cache.get).lookup variant with
  | some environment => pure environment
  | none =>
    let environment ← build
    cache.modify ((variant, environment) :: ·)
    pure environment

/-- The PowerPC of a binary: its word size and its byte order, which are of its ELF header. -/
structure PowerPCVariant where
  bits : Nat := 64
  endian : Endian := .little
  deriving DecidableEq, Repr

/-- The MIPS of a binary: its word size, its byte order, and whether it is of release 6, whose encodings reuse those of
older instructions. All of these are of its ELF header. -/
structure MipsVariant where
  bits : Nat := 64
  endian : Endian := .big
  release6 : Bool := false
  deriving DecidableEq, Repr

/-- The LLVM target of a PowerPC. -/
def PowerPCVariant.triple (variant : PowerPCVariant) : String :=
  match variant.bits == 64, variant.endian with
  | true, .little => "powerpc64le"
  | true, .big => "powerpc64"
  | false, .little => "powerpcle"
  | false, .big => "powerpc"

/-- The LLVM target of a MIPS. Release 6 is the subarchitecture of the name, which picks the CPU of the decoder. -/
def MipsVariant.triple (variant : MipsVariant) : String :=
  match variant.bits == 64, variant.release6, variant.endian with
  | true, false, .big => "mips64"
  | true, false, .little => "mips64el"
  | true, true, .big => "mipsisa64r6"
  | true, true, .little => "mipsisa64r6el"
  | false, false, .big => "mips"
  | false, false, .little => "mipsel"
  | false, true, .big => "mipsisa32r6"
  | false, true, .little => "mipsisa32r6el"

private def arm32Context (address nextPc : Nat) : Primus.Semantics.Context :=
  { bits := 32, pc := address, nextPc := nextPc, memory := ⟨"mem", .mem 32 8, 0, false⟩ }

/-- The context of the semantics of a binary of a word size and a byte order. -/
private def wordContext (bits : Nat) (endian : Endian) (address nextPc : Nat) : Primus.Semantics.Context :=
  if bits == 64 then { semanticsContext address nextPc with endian := endian }
  else { arm32Context address nextPc with endian := endian }

private initialize powerpcCache : IO.Ref (List (PowerPCVariant × Primus.Semantics.Environment)) ← IO.mkRef []

def powerpcEnvironmentOf (variant : PowerPCVariant) : IO Primus.Semantics.Environment :=
  cachedVariant powerpcCache variant do
    let definitions ← Primus.Semantics.loadMany (← pluginDirectories "powerpc") ["bits", "powerpc"]
      (wordContext variant.bits variant.endian 0 0)
    let globals := if variant.bits == 64 then powerpcGlobals else powerpc32Globals
    let register := if variant.bits == 64 then powerpcRegister else powerpc32Register
    let environment ← compiledDefinitions [] variant.triple globals definitions
    let registers ← LLVM.registerNames variant.triple
    pure (environment.withRegisters ((0, register "Nil") :: registers.map fun binding => (binding.1, register binding.2)))

def powerpcEnvironment : IO Primus.Semantics.Environment := powerpcEnvironmentOf {}

def powerpc32Environment : IO Primus.Semantics.Environment := powerpcEnvironmentOf { bits := 32, endian := .big }

private initialize mipsCache : IO.Ref (List (MipsVariant × Primus.Semantics.Environment)) ← IO.mkRef []

/-- `mips-r6` says that the variant is of release 6, for what the instructions of both do differently. -/
def mipsEnvironmentOf (variant : MipsVariant) : IO Primus.Semantics.Environment :=
  cachedVariant mipsCache variant do
    let definitions ← Primus.Semantics.loadMany (← pluginDirectories "mips")
      (if variant.release6 then ["mips", "mips-r6"] else ["mips"])
      (wordContext variant.bits variant.endian 0 0)
    makeEnvironment variant.triple
      (if variant.bits == 64 then mipsGlobals else if variant.release6 then mips32r6Globals else mips32Globals) definitions

def mipsEnvironment : IO Primus.Semantics.Environment := mipsEnvironmentOf {}

def mips32Environment : IO Primus.Semantics.Environment := mipsEnvironmentOf { bits := 32 }

private initialize x8632Cache : IO.Ref (Option Primus.Semantics.Environment) ← IO.mkRef none

private def x8632EnvironmentWith (extra : List String) : IO Primus.Semantics.Environment := do
  let context := arm32Context 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "x86")
    (["bits", "x86-32", "x86-bits", "x86-move", "x86-arith", "x86-control", "x86-shift", "x86-bmi", "x86-sse", "x86-simd",
      "x86-pcmpstr", "x86-sse-intrinsics"] ++ extra) context
  let environment ← compiledDefinitions
    [("RETQ", "RET32"), ("RETL", "RET32"), ("NOP", "NOOP")] "i386" x8632Globals definitions
  let registers ← LLVM.registerNames "i386"
  let registers := (0, x8632Register "Nil") ::
    (registers.map fun binding => (binding.1, x8632Register binding.2))
  let relativeOpcodes ← x86RelativeOpcodes.filterMapM (LLVM.opcodeId? "i386")
  pure { environment.withRegisters registers with relativeOpcodes := Std.HashSet.ofList relativeOpcodes }

def x8632Environment : IO Primus.Semantics.Environment := cached x8632Cache (x8632EnvironmentWith [])

private initialize x8632AvxCache : IO.Ref (Option Primus.Semantics.Environment) ← IO.mkRef none

/-- With AVX-512, as `x86AvxEnvironment`. -/
def x8632AvxEnvironment : IO Primus.Semantics.Environment := cached x8632AvxCache (x8632EnvironmentWith ["x86-avx512"])

private initialize riscv32Cache : IO.Ref (Option Primus.Semantics.Environment) ← IO.mkRef none

def riscv32Environment : IO Primus.Semantics.Environment := cached riscv32Cache do
  let context := arm32Context 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "riscv") ["riscv"] context
  let environment ← compiledDefinitions [] "riscv32" riscv32Globals definitions
  let registers ← (List.range 32).mapM fun n => do
    let id ← LLVM.registerId "riscv32" s!"X{n}"
    pure (id, riscv32Register s!"X{n}")
  let floats ← riscvFloatRegisters "riscv32"
  pure (environment.withRegisters (registers ++ floats))

private initialize arm32Cache : IO.Ref (Option Primus.Semantics.Environment) ← IO.mkRef none

def arm32Environment : IO Primus.Semantics.Environment := cached arm32Cache do
  let context := arm32Context 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "arm") ["arm"] context
  makeEnvironment "armv7" arm32Globals definitions

private def arm32Immediate (value : Int) : Primus.Semantics.Value :=
  .bil 32 (.int (BitVec.ofInt 32 value))

private def arm32Operand : LLVM.Operand → Primus.Semantics.Value
  | .reg name => arm32Register name
  | .imm value => arm32Immediate value

private initialize thumbCache : IO.Ref (Option Primus.Semantics.Environment) ← IO.mkRef none

def thumbEnvironment : IO Primus.Semantics.Environment := cached thumbCache do
  let context := arm32Context 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "arm") ["thumb2", "thumb-vfp"] context
  makeEnvironment "thumbv7" arm32Globals definitions

/-- The addressing of an ARM load or store of multiple registers. -/
inductive ArmMultiple where
  | increaseAfter | increaseBefore | decreaseAfter | decreaseBefore
  deriving DecidableEq, Repr

/-- Parses the operands of an ARM load or store of multiple registers: whether it is a load, the
addressing, whether the base is written back, the base, the condition and the list of registers. -/
private def armMultipleOperands (opcode : String) (operands : List LLVM.Operand) :
    Option (Bool × ArmMultiple × Bool × String × Int × List String) :=
  let names (rest : List LLVM.Operand) : Option (List String) :=
    rest.mapM fun operand =>
      match operand with
      | .reg name => some name
      | .imm _ => none
  let mode : Option (Bool × ArmMultiple × Bool) :=
    match opcode with
    | "LDMIA" | "t2LDMIA" | "tLDMIA" => some (true, .increaseAfter, false)
    | "LDMIA_UPD" | "LDMIA_RET" | "t2LDMIA_UPD" | "t2LDMIA_RET" | "tLDMIA_UPD" =>
      some (true, .increaseAfter, true)
    | "LDMIB" => some (true, .increaseBefore, false)
    | "LDMIB_UPD" => some (true, .increaseBefore, true)
    | "LDMDA" => some (true, .decreaseAfter, false)
    | "LDMDA_UPD" => some (true, .decreaseAfter, true)
    | "LDMDB" | "t2LDMDB" => some (true, .decreaseBefore, false)
    | "LDMDB_UPD" | "t2LDMDB_UPD" => some (true, .decreaseBefore, true)
    | "STMIA" | "t2STMIA" => some (false, .increaseAfter, false)
    | "STMIA_UPD" | "t2STMIA_UPD" | "tSTMIA_UPD" => some (false, .increaseAfter, true)
    | "STMIB" => some (false, .increaseBefore, false)
    | "STMIB_UPD" => some (false, .increaseBefore, true)
    | "STMDA" => some (false, .decreaseAfter, false)
    | "STMDA_UPD" => some (false, .decreaseAfter, true)
    | "STMDB" | "t2STMDB" => some (false, .decreaseBefore, false)
    | "STMDB_UPD" | "t2STMDB_UPD" => some (false, .decreaseBefore, true)
    | _ => none
  match opcode, operands with
  | "tPOP", .imm condition :: _ :: rest =>
    (names rest).map fun list => (true, .increaseAfter, true, "SP", condition, list)
  | "tPUSH", .imm condition :: _ :: rest =>
    (names rest).map fun list => (false, .decreaseBefore, true, "SP", condition, list)
  | _, operands =>
    mode.bind fun (load, addressing, writeback) =>
      match writeback, operands with
      | true, _ :: .reg base :: .imm condition :: _ :: rest
      | false, .reg base :: .imm condition :: _ :: rest =>
        -- a narrow `LDM` writes back unless it loads its base
        (names rest).map fun list =>
          (load, addressing, writeback || (opcode == "tLDMIA" && !list.contains base), base, condition, list)
      | _, _ => none

/-- The condition of an A32 or T32 instruction, as `condition-holds` of `arm-bits`, `none` if it
always holds. -/
private def armCondition (condition : Int) : Option Bil.Exp :=
  let flag (name : String) : Bil.Exp := .var ⟨name, .imm 1, 0, false⟩
  let same : Bil.Exp := .bin .eq (flag "NF") (flag "VF")
  let different : Bil.Exp := .bin .neq (flag "NF") (flag "VF")
  match condition with
  | 0 => some (flag "ZF")
  | 1 => some (.un .not (flag "ZF"))
  | 2 => some (flag "CF")
  | 3 => some (.un .not (flag "CF"))
  | 4 => some (flag "NF")
  | 5 => some (.un .not (flag "NF"))
  | 6 => some (flag "VF")
  | 7 => some (.un .not (flag "VF"))
  | 8 => some (.bin .and (flag "CF") (.un .not (flag "ZF")))
  | 9 => some (.bin .or (.un .not (flag "CF")) (flag "ZF"))
  | 10 => some same
  | 11 => some different
  | 12 => some (.bin .and same (.un .not (flag "ZF")))
  | 13 => some (.bin .or different (flag "ZF"))
  | _ => none

/-- The base register of the address computations of a load or store of multiple registers. -/
def armMultipleBase : Bap.Var := ⟨"_arm_multiple_base", .imm 32, 0, false⟩

def armWord (value : Nat) : Bil.Exp := .int (BitVec.ofNat 32 value)

/-- The lowest address of a transfer of `size` bytes. -/
def armMultipleFirst (addressing : ArmMultiple) (size : Nat) : Bil.Exp :=
  match addressing with
  | .increaseAfter => .var armMultipleBase
  | .increaseBefore => .bin .add (.var armMultipleBase) (armWord 4)
  | .decreaseAfter => .bin .sub (.bin .add (.var armMultipleBase) (armWord 4)) (armWord size)
  | .decreaseBefore => .bin .sub (.var armMultipleBase) (armWord size)

/-- The base written back after a transfer of `size` bytes. -/
def armMultipleAfter (addressing : ArmMultiple) (size : Nat) : Bil.Exp :=
  match addressing with
  | .increaseAfter | .increaseBefore => .bin .add (.var armMultipleBase) (armWord size)
  | .decreaseAfter | .decreaseBefore => .bin .sub (.var armMultipleBase) (armWord size)

/-- The accesses of a load or store of multiple registers, the lowest register at the lowest
address, where a load of PC is a branch. As in `arm-a32-multiple`, the base is written back before
the loads, so a loaded base keeps the loaded value, and after the stores. -/
def armMultipleBody (pc : Nat) (context : Primus.Semantics.Context) (load : Bool) (addressing : ArmMultiple)
    (writeback : Bool) (base : String) (list : List String) : Bil.Program :=
  let baseVar : Bap.Var := ⟨base, .imm 32, 0, false⟩
  let size := 4 * list.length
  let first := armMultipleFirst addressing size
  let address (index : Nat) : Bil.Exp := .bin .add first (armWord (4 * index))
  let memory : Bil.Exp := .var context.memory
  let write : Bil.Program := if writeback then [.move baseVar (armMultipleAfter addressing size)] else []
  let loads := (List.range list.length).zip list |>.map fun (index, name) =>
    let value : Bil.Exp := .load memory (address index) context.endian 4
    if name = "PC" then Bil.Stmt.jmp (.bin .and value (armWord 0xfffffffe))
    else .move ⟨name, .imm 32, 0, false⟩ value
  let stores := (List.range list.length).zip list |>.map fun (index, name) =>
    let value : Bil.Exp := if name = "PC" then armWord pc else .var ⟨name, .imm 32, 0, false⟩
    Bil.Stmt.move context.memory (.store memory (address index) value context.endian 4)
  .move armMultipleBase (.var baseVar) :: (if load then write ++ loads else stores ++ write)

/-- A load or store of multiple registers, under its condition. `arm-a32-multiple` does the same on the A32 and the wide
T32 forms, which `testArmMultipleAgree` checks, but the semantics have no narrow forms, this is what the proofs of the
list of any length are about, as they can't be about a file, and it lifts 25 times faster. -/
private def armMultiple (pc : Nat) (context : Primus.Semantics.Context) (decoded : LLVM.Decoded) :
    Option Bil.Program :=
  (armMultipleOperands decoded.opcode decoded.operands).map
    fun (load, addressing, writeback, base, condition, list) =>
      let body := armMultipleBody pc context load addressing writeback base list
      match armCondition condition with
      | some holds => [.ifElse holds body []]
      | none => body

/-- An address is computed modulo the width of the address space, as the hardware does. -/
private def wrapAddress (bits : Nat) (target : Int) : Nat := (target % (2 ^ bits : Int)).toNat

/-- A Thumb branch or call: its displacement operand, from the pc, the address plus four. LLVM
gives BLX an A32 target, which is relative to the word-aligned pc. -/
private def thumbTarget (address : Nat) (decoded : LLVM.Decoded) : Option Nat :=
  let displacement :=
    if ["t2B", "t2Bcc", "tB", "tBcc"].contains decoded.opcode then decoded.operands.head?
    else if ["tBL", "tBLXi", "tCBZ", "tCBNZ"].contains decoded.opcode then decoded.operands.getLast?
    else none
  let pc := if decoded.opcode = "tBLXi" then (address + 4) / 4 * 4 else address + 4
  match displacement with
  | some (.imm displacement) => some (wrapAddress 32 (Int.ofNat pc + displacement))
  | _ => none

/-- An A32 branch or call: its displacement operand, from the pc, the address plus eight. -/
private def arm32Target (address : Nat) (decoded : LLVM.Decoded) : Option Nat :=
  match ["Bcc", "BL", "BL_pred", "BLXi"].contains decoded.opcode, decoded.operands.head? with
  | true, some (.imm displacement) => some (wrapAddress 32 (Int.ofNat (address + 8) + displacement))
  | _, _ => none

/-- A direct branch or call by the flags of LLVM. -/
private def directControl (flags : Nat) : Bool :=
  flags &&& 8 != 0 && flags &&& 16 == 0 || flags &&& 2 != 0

/-- `J`, `JAL` and `JALX` give the low 28 bits of the target, the upper bits are of the delay slot.
The other direct branches and calls give a displacement from the branch, which LLVM has already
adjusted for the delay slot. -/
private def mipsTarget (bits address : Nat) (decoded : LLVM.Decoded) : Option Nat :=
  match decoded.operands.getLast? with
  | some (.imm immediate) =>
    if ["J", "JAL", "JALX"].contains decoded.opcode then
      some (wrapAddress bits (Int.ofNat ((address + 4) / 0x10000000 * 0x10000000) + immediate))
    else if directControl decoded.flags then
      some (wrapAddress bits (Int.ofNat address + immediate))
    else none
  | _ => none

/-- The longest instruction of any target has 15 bytes, and decoding only needs that many. -/
def instructionBytes (data : ByteArray) (offset : Nat) : ByteArray := data.extract offset (offset + 16)

/-- The size of what decodes at an address in the code that starts at `base`, whether it can be lifted or not. -/
def sizeAt (triple : String) (base address : Nat) (data : ByteArray) : IO (Option Nat) := do
  try
    pure (some (← LLVM.disassemble triple (instructionBytes data (address - base)) address).size)
  catch _ =>
    pure none

/-- The MIPS jumps and conditional branches run their delay slot before the transfer. Calls reach the slot by falling
through, which is where the callee returns past it. `ERET` has no delay slot. -/
def mipsHasDelaySlot (insn : Disasm.Insn) : Bool :=
  (insn.flow == .jump || insn.flow == .indirectJump || insn.flow == .ret || insn.flow == .conditionalJump) &&
    !insn.asm.startsWith "eret" && !insn.asm.startsWith "deret"

/-- The mnemonics of the branches that annul their delay slots when they are not taken, including LLVM's aliases. -/
def mipsLikelyMnemonics : List String :=
  ["beql", "bnel", "beqzl", "bnezl", "blezl", "bgtzl", "bltzl", "bgezl", "bltzall", "bgezall", "bc1tl", "bc1fl", "bc2tl",
    "bc2fl"]

/-- Whether a branch annuls its delay slot when it is not taken. -/
def mipsAnnulsSlot (insn : Disasm.Insn) : Bool :=
  mipsLikelyMnemonics.contains ((insn.asm.takeWhile fun c => c != ' ' && c != '\t').toString)


/-- The instruction word at the start of `data`. -/
private def instructionWord (endian : Endian) (data : ByteArray) : Nat :=
  let byte (index : Nat) : Nat := (data.get! index).toNat
  match endian with
  | .little => byte 0 + byte 1 * 0x100 + byte 2 * 0x10000 + byte 3 * 0x1000000
  | .big => byte 3 + byte 2 * 0x100 + byte 1 * 0x10000 + byte 0 * 0x1000000

/-- The I-form and B-form branches have the displacement, of words, as the last operand, and the
absolute variants have the AA bit, which is what tells BA from B. The other branches that LLVM
marks as direct, e.g., `gBCLR`, go through a register. -/
private def powerpcMCTarget (bits address word : Nat) (operands : List LLVM.MCOperand) : Option Nat :=
  let primary := word / 0x4000000
  match primary == 16 || primary == 18, operands.getLast? with
  | true, some (.imm displacement) =>
    let origin : Int := if word &&& 2 != 0 then 0 else Int.ofNat address
    some (wrapAddress bits (origin + displacement * 4))
  | _, _ => none

/-- LLVM has no flags for `JAL`, whose major opcode this is. -/
private def riscvIsJal (word : Nat) : Bool := word % 0x80 == 0x6f

private def riscvMCTarget (bits address word flags : Nat) (operands : List LLVM.MCOperand) : Option Nat :=
  match riscvIsJal word || flags &&& 8 != 0 && flags &&& 16 == 0, operands.getLast? with
  | true, some (.imm displacement) => some (wrapAddress bits (Int.ofNat address + displacement))
  | _, _ => none

private def flow (flags : Nat) : Disasm.Flow :=
  if flags &&& 1 != 0 then .ret
  else if flags &&& 2 != 0 then .call
  else if flags &&& 32 != 0 then .conditionalJump
  else if flags &&& 16 != 0 then .indirectJump
  else if flags &&& 64 != 0 then .jump
  else if flags &&& 4 != 0 || flags &&& 512 != 0 then .barrier
  else .normal

/-- LLVM has no flags for `JAL` and `JALR`, their role comes from the registers, by the hints of the
RISC-V specification: `X1` and `X5` are the link registers. -/
private def riscvFlow (word flags : Nat) : Disasm.Flow :=
  let rd := word / 0x80 % 0x20
  let rs := word / 0x8000 % 0x20
  let major := word % 0x80
  if major == 0x6f then
    if rd == 0 then .jump else .call
  else if major == 0x67 then
    if rd != 0 then .call
    else if rs == 1 || rs == 5 then .ret
    else .indirectJump
  else flow flags

/-- LLVM marks `Bcc` as conditional even with the condition code `AL`, which is the plain `b`. -/
private def arm32Flow (decoded : LLVM.Decoded) : Disasm.Flow :=
  match decoded.opcode, decoded.operands with
  | "Bcc", _ :: .imm 14 :: _ => .jump
  | _, _ => flow decoded.flags

/-- `BEQ` of a register with itself and `BGEZ` of the zero register are the assembler's `b`, which
always branches. -/
private def mipsFlow (decoded : LLVM.Decoded) : Disasm.Flow :=
  match decoded.opcode, decoded.operands with
  | "BEQ", [left, right, _] | "BEQL", [left, right, _] =>
    if left == right then .jump else flow decoded.flags
  | "BGEZ", [.reg "ZERO", _] | "BGEZ", [.reg "ZERO_64", _]
  | "BGEZL", [.reg "ZERO", _] | "BGEZL", [.reg "ZERO_64", _] => .jump
  | _, _ => flow decoded.flags

/-- A lifted program transfers control: `some true` if always, `some false` under some condition. -/
private def programJump : Bil.Program → Option Bool
  | [] => none
  | .jmp _ :: _ => some true
  | .while _ body :: rest =>
    match programJump rest with
    | some true => some true
    | jump => if (programJump body).isSome then some false else jump
  | .ifElse _ yes no :: rest =>
    match programJump rest with
    | some true => some true
    | jump => if (programJump yes).isSome || (programJump no).isSome then some false else jump
  | _ :: rest => programJump rest

/-- LLVM has no flags for most writes to PC, e.g., `ldr pc, [sp]`, and it calls `bxeq lr` and
`moveq pc, lr` returns. The semantics lift all of them to jumps, under the condition if there is
one, so the lifted program decides whether control can fall through. -/
private def armControlFlow (flow : Disasm.Flow) (bil : Bil.Program) : Disasm.Flow :=
  match flow, programJump bil with
  | .normal, some true => .indirectJump
  | .normal, some false | .ret, some false | .indirectJump, some false => .conditionalJump
  | _, _ => flow

/-- The tokens of an assembly line, with one space between them. Whitespace is of bytes that aren't in any other
character of UTF-8, so it goes over the bytes. -/
private def normalizeAssembly (assembly : String) : String := Id.run do
  let mut out := ByteArray.emptyWithCapacity assembly.utf8ByteSize
  let mut pending := false
  for byte in assembly.toUTF8 do
    if byte == 0x20 || byte == 0x09 || byte == 0x0a || byte == 0x0d then
      pending := !out.isEmpty
    else
      if pending then
        out := out.push 0x20
      out := out.push byte
      pending := false
  (String.fromUTF8? out).getD assembly

private def aarch64MCTarget (address : Nat) (flags : Nat) (operands : List LLVM.MCOperand) : Option Nat :=
  let selected := if flags &&& 32 != 0 then operands.getLast? else operands.head?
  match directControl flags, selected with
  | true, some (.imm displacement) => some (wrapAddress 64 (Int.ofNat address + displacement * 4))
  | _, _ => none

private def aarch64MCOperands (globals : Primus.Semantics.Environment)
    (context : Primus.Semantics.Context) (flags : Nat) (operands : List LLVM.MCOperand) :
    IO (List Primus.Semantics.Value) := do
  if flags &&& 1 != 0 && operands.isEmpty then
    pure [aarch64Register "X30"]
  else
    match flags &&& 32 != 0, operands with
    | true, [.imm code, .imm displacement] =>
      pure [Primus.Semantics.immediate code, Primus.Semantics.immediate displacement]
    | _, _ => operands.mapM fun value =>
      match Primus.Semantics.machineOperand globals context value with
      | .ok operand => pure operand
      | .error error => throw <| IO.userError error

def decodeAArch64With (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let decoded ← LLVM.disassembleMC "aarch64" (instructionBytes data (address - base)) address
  let context := semanticsContext address (address + decoded.size)
  let machineOperands ← LLVM.mcOperands decoded.instruction
  let operands ← aarch64MCOperands globals context decoded.flags machineOperands
  let bil ← try
    Primus.Semantics.liftMC globals context (LLVM.mcOpcode decoded.instruction) operands
  catch error =>
    throw <| IO.userError s!"{decoded.assembly} operands={repr machineOperands}: {error}"
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := flow decoded.flags
    target := aarch64MCTarget address decoded.flags machineOperands
    bil := bil
  }

def decodeAArch64 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeAArch64With (← aarch64Environment) base address data

private def x86MCOperands (globals : Primus.Semantics.Environment)
    (opcode : Nat) (operands : List LLVM.MCOperand) :
    IO (List Primus.Semantics.Value) := do
  operands.mapM fun value =>
    match value with
    | .reg id =>
      match globals.registers.get? id with
      | some value => pure value
      | none => throw <| IO.userError s!"unknown x86 register ID {id}"
    | .imm value =>
      if globals.signExtendedOpcodes.contains opcode then
        pure (.bil 64 (.int (BitVec.signExtend 64 (BitVec.ofInt 32 value))))
      else
        pure (.bil 64 (.int (BitVec.ofInt 64 value)))

private def x86MCTarget (bits : Nat) (globals : Primus.Semantics.Environment) (next : Nat) (opcode : Nat)
    (operands : List LLVM.MCOperand) : Option Nat :=
  match globals.relativeOpcodes.contains opcode, operands.head? with
  | true, some (.imm displacement) => some (wrapAddress bits (Int.ofNat next + displacement))
  | _, _ => none

/-- The legacy prefix bytes: LOCK, the repetitions, the segments, and the sizes of operands and addresses. -/
def x86LegacyPrefix (byte : Nat) : Bool :=
  byte == 0xf0 || byte == 0xf2 || byte == 0xf3 || byte == 0x2e || byte == 0x36 || byte == 0x3e || byte == 0x26 ||
    byte == 0x64 || byte == 0x65 || byte == 0x66 || byte == 0x67

/-- The prefix group of REPNE and REP: of an instruction that has both, the last one counts. -/
def x86RepeatPrefix (byte : Nat) : Bool := byte == 0xf2 || byte == 0xf3

/-- The legacy prefixes that apply to an instruction with these first bytes. They are the bytes before its opcode, and
in the 64-bit mode a REX prefix before a legacy prefix is ignored, as it has to be next to the opcode. -/
def x86Prefixes (long : Bool) : List Nat → List Nat
  | [] => []
  | byte :: rest =>
    if x86LegacyPrefix byte then
      let others := x86Prefixes long rest
      if x86RepeatPrefix byte && others.any x86RepeatPrefix then others else byte :: others
    else if long && byte / 16 == 4 && (rest.head?.map x86LegacyPrefix).getD false then
      x86Prefixes long rest
    else []

/-- The context of an x86 instruction, which `x86-prefix` can ask for its prefixes. -/
private def x86Context (context : Primus.Semantics.Context) (long : Bool) (bytes : ByteArray) (size : Nat) :
    Primus.Semantics.Context :=
  let first := (bytes.get! 0).toNat
  -- what most instructions start with: neither a legacy prefix nor a REX one that can be before one
  if size ≠ 0 && !x86LegacyPrefix first && first / 16 != 4 then { context with prefixes := some [] }
  else { context with prefixes := some (x86Prefixes long ((bytes.toList.take size).map UInt8.toNat)) }

/-- What the name of an AVX-512 opcode says: `VPADDDZ256rmbkz` is the family `VPADDD` on 256 bits with a form `rmbkz`. -/
structure EvexOpcode where
  family : String
  /-- The size of the vector: `Z128`, `Z256` and `Z`, which is also the name of the scalar forms. -/
  width : Nat
  /-- All of the name after the size. -/
  suffix : String
  deriving DecidableEq, Repr

namespace EvexOpcode

/-- The form with its mask, without what follows a `_`, as `_Int` or `_REV`. -/
def maskedForm (opcode : EvexOpcode) : List Char := opcode.suffix.toList.takeWhile (· != '_')

/-- The masking: 0 none, 1 merging, 2 zeroing. -/
def masking (opcode : EvexOpcode) : Nat :=
  match opcode.maskedForm.reverse with
  | 'z' :: 'k' :: _ => 2
  | 'k' :: _ => 1
  | _ => 0

/-- The form without the mask. -/
def form (opcode : EvexOpcode) : List Char := opcode.maskedForm.take (opcode.maskedForm.length - opcode.masking)

/-- How the last source is given, the argument `MEM` of the semantics. -/
def memory (opcode : EvexOpcode) : Nat :=
  match opcode.form with
  | 'm' :: 'r' :: _ => 3
  | form =>
    if form.contains 'm' then (if form.contains 'b' then 2 else 1)
    else if form.getLast? == some 'b' then 4
    else 0

/-- Whether the last operand is an immediate, the argument `I` of the semantics. -/
def immediate (opcode : EvexOpcode) : Nat := if opcode.form.contains 'i' then 1 else 0

/-- The opcode of the same semantics with a VEX prefix or none, if the registers of an instruction are of the size it
has: the operands are the same. -/
def vexName (opcode : EvexOpcode) : String :=
  opcode.family ++ (if opcode.width = 256 then "Y" else "") ++ opcode.suffix

end EvexOpcode

/-- What is before and after the last `Z`, of reversed characters and of those after them. -/
def evexSplit : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | 'Z' :: before, after => some (before.reverse, after)
  | char :: before, after => evexSplit before (char :: after)

/-- The parts of the name of an AVX-512 opcode: the `Z` is the last one, a size and a form follow it. -/
def evexOpcode? (name : String) : Option EvexOpcode :=
  match evexSplit name.toList.reverse [] with
  | none => none
  | some (family, after) =>
    let (width, suffix) :=
      match after with
      | '1' :: '2' :: '8' :: rest => (128, rest)
      | '2' :: '5' :: '6' :: rest => (256, rest)
      | rest => (512, rest)
    match family, suffix with
    | _ :: _, char :: _ =>
      if char.isLower then some ⟨String.ofList family, width, String.ofList suffix⟩ else none
    | _, _ => none

/-- The instructions that aren't defined in the environment of a program: those of AVX-512, whose semantics it loads now.
A mask instruction is defined by its name. Another opcode is a form of a family, which is a definition that takes the form
and the operands, or the same as an opcode without EVEX, unless it has a register that only AVX-512 has. Anything else has
no semantics, which is an error. -/
private def liftAvx (triple : String) (environment : IO Primus.Semantics.Environment) (context : Primus.Semantics.Context)
    (bytes : ByteArray) (address : Nat) (operands : List Primus.Semantics.Value) : IO Bil.Program := do
  let name := (← LLVM.disassemble triple bytes address).opcode
  let globals ← environment
  let undefined := IO.userError s!"Primus semantics has no definition for LLVM opcode {name}"
  if globals.instructions.contains name then
    Primus.Semantics.liftWith globals context name operands
  else if name.endsWith "_EVEX" && globals.instructions.contains ((name.dropEnd 5).toString) then
    -- the same instruction with the prefix of APX, of the same operands
    Primus.Semantics.liftWith globals context ((name.dropEnd 5).toString) operands
  else
    match evexOpcode? name with
    | none => throw undefined
    | some opcode =>
      let family := s!"evex:{opcode.family}"
      if globals.operations.contains family then
        let word (value : Nat) : Primus.Semantics.Value := .int (BitVec.ofNat 64 value)
        -- a merging move in the other direction has its destination once, as the mask is its first source
        let operands := match opcode.masking, opcode.suffix.endsWith "_REV", operands with
          | 1, true, [destination, mask, source] => [destination, destination, mask, source]
          | _, _, _ => operands
        -- a static rounding mode is the last operand of the forms that have it, and BF16 is a format of its own
        let rounding := match opcode.memory, opcode.immediate, operands.getLast? with
          | 4, 0, some (.bil _ (.int mode)) =>
            let name := match mode.toNat % 4 with
              | 0 => "rne"
              | 1 => "rdn"
              | 2 => "rup"
              | _ => "rtz"
            [("*sse-rmode*", Primus.Semantics.Value.symbol name)]
          | _, _, _ => []
        let format := if (opcode.family.splitOn "BF16").length > 1 then [("*sse-format*", Primus.Semantics.Value.symbol "bfloat")] else []
        let globals := match rounding ++ format with
          | [] => globals
          | bound => { globals with globals := bound ++ globals.globals }
        Primus.Semantics.liftWith globals context family
          [.list (word opcode.width :: word opcode.memory :: word opcode.masking :: word opcode.immediate :: operands)]
      else
        let vexRegisters := operands.all fun operand =>
          match operand with
          | .register name width _ => width ≠ 512 && !name.startsWith "K"
          | _ => true
        if vexRegisters && globals.instructions.contains opcode.vexName then
          Primus.Semantics.liftWith globals context opcode.vexName operands
        else
          throw undefined

/-- The code of an instruction: what its opcode is defined as, or else what AVX-512 has. -/
private def x86Lift (triple : String) (avx : IO Primus.Semantics.Environment) (globals : Primus.Semantics.Environment)
    (context : Primus.Semantics.Context) (bytes : ByteArray) (address opcode : Nat)
    (operands : List Primus.Semantics.Value) : IO Bil.Program :=
  if globals.opcodes.contains opcode then Primus.Semantics.liftMC globals context opcode operands
  else liftAvx triple avx context bytes address operands

instance : Hashable LLVM.MCOperand where
  hash
    | .reg id => mixHash 1 (hash id)
    | .imm value => mixHash 2 (hash value)

/-- What the code of an x86 instruction is a function of, if it doesn't depend on where the instruction is. -/
structure LiftKey where
  opcode : Nat
  operands : List LLVM.MCOperand
  prefixes : Option (List Nat)
  deriving BEq, Hashable

/-- The code of the x86 instructions of one disassembler so far: most of a binary is the same few instructions. -/
abbrev LiftMemo := Std.HashMap LiftKey Bil.Program

/-- Whether the code of an instruction doesn't depend on its address. The semantics of x86 only ask for the program counter
in `relative`, for the opcodes in `relativeOpcodes`, in `call`, whose flow says so, and in `ea` for the base register RIP. -/
private def x86AnywhereCode (globals : Primus.Semantics.Environment) (decoded : LLVM.MCDecoded) (opcode : Nat)
    (operands : List Primus.Semantics.Value) : Bool :=
  (match flow decoded.flags with | .normal => true | _ => false) && !globals.relativeOpcodes.contains opcode &&
    operands.all fun operand =>
      match operand with
      | .register name _ _ => name != "RIP"
      | _ => true

/-- `lift`, unless it was done for the same instruction and it can't depend on where this one is. -/
private def x86Memoized (memo : IO.Ref LiftMemo) (anywhere : Bool) (key : LiftKey) (lift : IO Bil.Program) : IO Bil.Program := do
  if anywhere then
    match (← memo.get).get? key with
    | some program => pure program
    | none =>
      let program ← lift
      memo.modify (·.insert key program)
      pure program
  else
    lift

/-- `decodeX86With`, which it is for all that the tests compare, looking up what the same instruction was lifted to before. -/
def decodeX86Memo (memo : IO.Ref LiftMemo) (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let bytes := instructionBytes data (address - base)
  let decoded ← LLVM.disassembleMC "x86_64" bytes address
  let context := x86Context (semanticsContext address (address + decoded.size)) true bytes decoded.size
  let opcode := LLVM.mcOpcode decoded.instruction
  let machineOperands ← LLVM.mcOperands decoded.instruction
  let operands ← x86MCOperands globals opcode machineOperands
  let bil ← x86Memoized memo (x86AnywhereCode globals decoded opcode operands) ⟨opcode, machineOperands, context.prefixes⟩ do
    pure (resolveAliases (x86Aliases x86HighByteBase 64) (← x86Lift "x86_64" x86AvxEnvironment globals context bytes address opcode operands))
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := flow decoded.flags
    target := x86MCTarget 64 globals (address + decoded.size) opcode machineOperands
    bil := bil
  }

def decodeX86With (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let bytes := instructionBytes data (address - base)
  let decoded ← LLVM.disassembleMC "x86_64" bytes address
  let context := x86Context (semanticsContext address (address + decoded.size)) true bytes decoded.size
  let opcode := LLVM.mcOpcode decoded.instruction
  let machineOperands ← LLVM.mcOperands decoded.instruction
  let operands ← x86MCOperands globals opcode machineOperands
  let bil ← x86Lift "x86_64" x86AvxEnvironment globals context bytes address opcode operands
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := flow decoded.flags
    target := x86MCTarget 64 globals (address + decoded.size) opcode machineOperands
    bil := resolveAliases (x86Aliases x86HighByteBase 64) bil
  }

def decodeX86 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeX86With (← x86Environment) base address data

def decodeX8632With (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let bytes := instructionBytes data (address - base)
  let decoded ← LLVM.disassembleMC "i386" bytes address
  let context := x86Context (arm32Context address (address + decoded.size)) false bytes decoded.size
  let opcode := LLVM.mcOpcode decoded.instruction
  let machineOperands ← LLVM.mcOperands decoded.instruction
  let operands ← machineOperands.mapM fun value =>
    match Primus.Semantics.machineOperand globals context value with
    | .ok operand => pure operand
    | .error error => throw <| IO.userError error
  let bil ← x86Lift "i386" x8632AvxEnvironment globals context bytes address opcode operands
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := flow decoded.flags
    target := x86MCTarget 32 globals (address + decoded.size) opcode machineOperands
    bil := resolveAliases (x86Aliases x8632HighByteBase 32) bil
  }

/-- `decodeX8632With`, looking up what the same instruction was lifted to before. -/
def decodeX8632Memo (memo : IO.Ref LiftMemo) (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let bytes := instructionBytes data (address - base)
  let decoded ← LLVM.disassembleMC "i386" bytes address
  let context := x86Context (arm32Context address (address + decoded.size)) false bytes decoded.size
  let opcode := LLVM.mcOpcode decoded.instruction
  let machineOperands ← LLVM.mcOperands decoded.instruction
  let operands ← machineOperands.mapM fun value =>
    match Primus.Semantics.machineOperand globals context value with
    | .ok operand => pure operand
    | .error error => throw <| IO.userError error
  let bil ← x86Memoized memo (x86AnywhereCode globals decoded opcode operands) ⟨opcode, machineOperands, context.prefixes⟩ do
    pure (resolveAliases (x86Aliases x8632HighByteBase 32) (← x86Lift "i386" x8632AvxEnvironment globals context bytes address opcode operands))
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := flow decoded.flags
    target := x86MCTarget 32 globals (address + decoded.size) opcode machineOperands
    bil := bil
  }

def decodeX8632 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeX8632With (← x8632Environment) base address data

def decodeRISCVWith (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let bytes := instructionBytes data (address - base)
  let decoded ← LLVM.disassembleMC "riscv64" bytes address
  let word := instructionWord .little bytes
  let context := semanticsContext address (address + decoded.size)
  let machineOperands ← LLVM.mcOperands decoded.instruction
  let operands ← machineOperands.mapM fun value =>
    match Primus.Semantics.machineOperand globals context value with
    | .ok operand => pure operand
    | .error error => throw <| IO.userError error
  let bil ← Primus.Semantics.liftMC globals context (LLVM.mcOpcode decoded.instruction) operands
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := riscvFlow word decoded.flags
    target := riscvMCTarget 64 address word decoded.flags machineOperands
    bil := bil
  }

def decodeRISCV (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeRISCVWith (← riscvEnvironment) base address data

def decodeRISCV32With (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let bytes := instructionBytes data (address - base)
  let decoded ← LLVM.disassembleMC "riscv32" bytes address
  let word := instructionWord .little bytes
  let context := arm32Context address (address + decoded.size)
  let machineOperands ← LLVM.mcOperands decoded.instruction
  let operands ← machineOperands.mapM fun value =>
    match Primus.Semantics.machineOperand globals context value with
    | .ok operand => pure operand
    | .error error => throw <| IO.userError error
  let bil ← Primus.Semantics.liftMC globals context (LLVM.mcOpcode decoded.instruction) operands
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := riscvFlow word decoded.flags
    target := riscvMCTarget 32 address word decoded.flags machineOperands
    bil := bil
  }

def decodeRISCV32 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeRISCV32With (← riscv32Environment) base address data

/-- A PowerPC instruction of a variant, whose byte order is that of its encoding and of the accesses it makes. -/
def decodePowerPCOf (variant : PowerPCVariant) (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let bytes := instructionBytes data (address - base)
  let decoded ← LLVM.disassembleMC variant.triple bytes address
  let word := instructionWord variant.endian bytes
  let context := wordContext variant.bits variant.endian address (address + decoded.size)
  let machineOperands ← LLVM.mcOperands decoded.instruction
  let operands ← machineOperands.mapM fun value =>
    match Primus.Semantics.machineOperand globals context value with
    | .ok operand => pure operand
    | .error error => throw <| IO.userError error
  let bil ← Primus.Semantics.liftMC globals context (LLVM.mcOpcode decoded.instruction) operands
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := flow decoded.flags
    target := powerpcMCTarget variant.bits address word machineOperands
    bil := resolveAliases powerpcAliases bil
  }

def decodePowerPCWith : Primus.Semantics.Environment → Nat → Nat → ByteArray → IO Disasm.Insn :=
  decodePowerPCOf {}

def decodePowerPC (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodePowerPCWith (← powerpcEnvironment) base address data

def decodePowerPC32With : Primus.Semantics.Environment → Nat → Nat → ByteArray → IO Disasm.Insn :=
  decodePowerPCOf { bits := 32, endian := .big }

def decodePowerPC32 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodePowerPC32With (← powerpc32Environment) base address data

/-- A MIPS instruction of a variant, whose byte order is that of its encoding and of the accesses it makes. -/
def decodeMIPSOf (variant : MipsVariant) (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let decoded ← LLVM.disassemble variant.triple (instructionBytes data (address - base)) address
  let context := wordContext variant.bits variant.endian address (address + decoded.size)
  let operands := decoded.operands.map
    (if variant.bits == 64 then operand mipsRegister decoded.opcode else mips32Operand variant.release6)
  let bil ← Primus.Semantics.liftWith globals context decoded.opcode operands
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := mipsFlow decoded
    target := mipsTarget variant.bits address decoded
    bil := bil
  }

def decodeMIPSWith : Primus.Semantics.Environment → Nat → Nat → ByteArray → IO Disasm.Insn :=
  decodeMIPSOf {}

def decodeMIPS (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeMIPSWith (← mipsEnvironment) base address data

def decodeMIPS32With : Primus.Semantics.Environment → Nat → Nat → ByteArray → IO Disasm.Insn :=
  decodeMIPSOf { bits := 32 }

def decodeMIPS32 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeMIPS32With (← mips32Environment) base address data

def decodeARM32With (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let decoded ← LLVM.disassemble "armv7" (instructionBytes data (address - base)) address
  let context := arm32Context address (address + decoded.size)
  let bil ← match armMultiple (address + 8) context decoded with
    | some bil => pure bil
    | none =>
      resolveAliases armAliases <$>
        Primus.Semantics.liftWith globals context decoded.opcode (decoded.operands.map arm32Operand)
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := armControlFlow (arm32Flow decoded) bil
    target := arm32Target address decoded
    bil := bil
  }

def decodeARM32 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeARM32With (← arm32Environment) base address data

/-- The program of one Thumb instruction. -/
private def liftThumb (globals : Primus.Semantics.Environment) (address : Nat) (decoded : LLVM.Decoded) :
    IO Bil.Program := do
  let context := arm32Context address (address + decoded.size)
  match armMultiple (address + 4) context decoded with
  | some bil => pure bil
  | none =>
    resolveAliases armAliases <$>
      Primus.Semantics.liftWith globals context decoded.opcode (decoded.operands.map arm32Operand)

/-- The conditions of the instructions of an IT block, from the operands of the IT instruction as the architecture has
them: the first has `firstcond`, and each next its top three bits and the next bit of the mask, down to the lowest bit
that is set, which ends the block. The ARM ARM calls this `ITAdvance`. -/
def thumbItConditions (firstcond mask : Nat) : List Int :=
  let count := if mask % 2 == 1 then 4 else if mask % 4 == 2 then 3 else if mask % 8 == 4 then 2 else 1
  (List.range count).map fun index =>
    ((if index == 0 then firstcond else firstcond / 2 * 2 + (mask >>> (4 - index)) % 2 : Nat) : Int)

/-- The predicate of an instruction in an IT block. The semantics take the predicate AL for an instruction outside of
a block, whose narrow forms set the flags, so AL in a block is its other encoding, which also always holds. -/
def thumbBlockPredicate (condition : Int) : Int := if condition = 14 then 15 else condition

/-- An instruction as it is in an IT block: the predicate operand holds its condition and it does not set the flags,
which is what its narrow encoding means there. A decoder of a single instruction cannot know this. -/
def thumbPredicated (condition : Int) (operands : List LLVM.Operand) : List LLVM.Operand :=
  let rec go : List LLVM.Operand → List LLVM.Operand
    | [] => []
    | .reg "CPSR" :: rest => .reg "Nil" :: go rest
    | .imm 14 :: .reg "Nil" :: rest => .imm (thumbBlockPredicate condition) :: .reg "Nil" :: go rest
    | operand :: rest => operand :: go rest
  go operands

/-- The flow of a block whose last instruction has `last`: it may always be skipped, so it never replaces falling through. -/
def thumbItFlow : Disasm.Flow → Disasm.Flow
  | .normal => .normal
  | .call => .call
  | _ => .conditionalJump

/-- An IT instruction lifted with the instructions it predicates, each under its condition, as they mean nothing without
it and a jump into a block is not allowed. Each instruction reads the flags as they are when it runs. -/
private def decodeThumbIt (globals : Primus.Semantics.Environment) (base address : Nat) (data : ByteArray)
    (it : LLVM.Decoded) (firstcond mask : Nat) : IO Disasm.Insn := do
  let conditions := thumbItConditions firstcond mask
  let mut cursor := address + it.size
  let mut bil : Bil.Program := []
  let mut asm := normalizeAssembly it.assembly
  let mut last : Option (LLVM.Decoded × Nat) := none
  for condition in conditions do
    let decoded ← LLVM.disassemble "thumbv7" (instructionBytes data (cursor - base)) cursor
    let predicated := { decoded with operands := thumbPredicated condition decoded.operands }
    let body ← liftThumb globals cursor predicated
    bil := bil ++ (match armCondition condition with
      | some holds => [Bil.Stmt.ifElse holds body []]
      | none => body)
    asm := asm ++ "; " ++ normalizeAssembly decoded.assembly
    last := some (decoded, cursor)
    cursor := cursor + decoded.size
  let (flowOf, target) := match last with
    | some (decoded, at') => (flow decoded.flags, thumbTarget at' decoded)
    | none => (.normal, none)
  pure {
    address := address
    size := cursor - address
    asm := asm
    flow := thumbItFlow (armControlFlow flowOf bil)
    target := target
    bil := bil
  }

/-- The first condition and the mask of an IT instruction: its two operands, or the fields of its encoding. -/
private def thumbItFields (data : ByteArray) : Option (Nat × Nat) :=
  if data.size < 2 then none
  else
    let low := (data.get! 0).toNat
    some (low / 16, low % 16)

def decodeThumbWith (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let bytes := instructionBytes data (address - base)
  let decoded ← LLVM.disassemble "thumbv7" bytes address
  match decoded.opcode, thumbItFields bytes with
  | "t2IT", some (firstcond, mask) => decodeThumbIt globals base address data decoded firstcond mask
  | _, _ =>
    let bil ← liftThumb globals address decoded
    pure {
      address := address
      size := decoded.size
      asm := normalizeAssembly decoded.assembly
      flow := armControlFlow (flow decoded.flags) bil
      target := thumbTarget address decoded
      bil := bil
    }

def decodeThumb (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeThumbWith (← thumbEnvironment) base address data

end Bap.Target.LLVMLift
