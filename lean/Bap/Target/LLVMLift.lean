import Bap.LLVM
import Bap.Disasm.Basic
import Bap.Primus.Semantics

namespace Bap.Target.LLVMLift

private def aarch64Register (name : String) : Primus.Semantics.Value :=
  let name := if name = "LR" then "X30" else if name = "FP" then "X29" else name
  if name = "XZR" || name = "WZR" then
    .register "XZR" 64 64
  else if name = "WSP" then
    .register "SP" 32 64
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

/-- `Value.register` views the low bits of its base, so a high byte keeps its own name while it is
lifted and `resolveHighBytes` turns it into bits 15 to 8 of the base afterwards. -/
private def x86Register (name : String) : Primus.Semantics.Value :=
  let name := if name.isEmpty || name = "NoRegister" then "Nil" else name
  if ["CF", "OF", "SF", "ZF", "AF", "PF", "DF", "IF"].contains name then
    .register name 1 1
  else if (x86HighByteBase name).isSome then
    .register name 8 8
  else
    match x86LowRegister name with
    | some (base, width) => .register base width 64
    | none => .register name 64 64

mutual
  private def highBytesExp (base : String → Option String) (width : Nat) : Bil.Exp → Bil.Exp
    | .var var =>
      match base var.name with
      | some name => .extract 15 8 (.var ⟨name, .imm width, 0, false⟩)
      | none => .var var
    | .load memory address endian size =>
      .load (highBytesExp base width memory) (highBytesExp base width address) endian size
    | .store memory address value endian size =>
      .store (highBytesExp base width memory) (highBytesExp base width address)
        (highBytesExp base width value) endian size
    | .bin op left right => .bin op (highBytesExp base width left) (highBytesExp base width right)
    | .un op value => .un op (highBytesExp base width value)
    | .cast kind size value => .cast kind size (highBytesExp base width value)
    | .letIn var value body =>
      .letIn var (highBytesExp base width value) (highBytesExp base width body)
    | .ite condition yes no =>
      .ite (highBytesExp base width condition) (highBytesExp base width yes)
        (highBytesExp base width no)
    | .extract high low value => .extract high low (highBytesExp base width value)
    | .concat left right => .concat (highBytesExp base width left) (highBytesExp base width right)
    | exp => exp
end

/-- Rewrites the high byte registers of a lifted program to bits 15 to 8 of their bases: a write
keeps the other bits of the base. -/
private def resolveHighBytes (base : String → Option String) (width : Nat) : Bil.Program → Bil.Program
  | [] => []
  | .move var value :: rest =>
    let value := highBytesExp base width value
    let stmt : Bil.Stmt :=
      match base var.name with
      | some name =>
        let target : Bap.Var := ⟨name, .imm width, 0, false⟩
        .move target (.concat (.extract (width - 1) 16 (.var target))
          (.concat value (.extract 7 0 (.var target))))
      | none => .move var value
    stmt :: resolveHighBytes base width rest
  | .jmp target :: rest => .jmp (highBytesExp base width target) :: resolveHighBytes base width rest
  | .while condition body :: rest =>
    .while (highBytesExp base width condition) (resolveHighBytes base width body) ::
      resolveHighBytes base width rest
  | .ifElse condition yes no :: rest =>
    .ifElse (highBytesExp base width condition) (resolveHighBytes base width yes)
      (resolveHighBytes base width no) :: resolveHighBytes base width rest
  | stmt :: rest => stmt :: resolveHighBytes base width rest

private def aarch64Globals : Primus.Semantics.Globals :=
  let registers := (List.range 31).map fun n => s!"X{n}"
  let vectors := (List.range 32).flatMap fun n => [s!"B{n}", s!"H{n}", s!"S{n}", s!"D{n}", s!"Q{n}"]
  (registers ++ vectors ++ ["SP", "LR", "XZR", "NF", "ZF", "CF", "VF", "TPIDR_EL0", "TPIDRRO_EL0"]).map
    fun name => (name, aarch64Register name)

private def x86Globals : Primus.Semantics.Globals :=
  let registers := ["RAX", "RBX", "RCX", "RDX", "RSI", "RDI", "RBP", "RSP",
    "EAX", "EBX", "ECX", "EDX", "ESI", "EDI", "EBP", "ESP", "RIP",
    "AX", "BX", "CX", "DX", "SI", "DI", "BP", "SP",
    "AL", "BL", "CL", "DL", "SIL", "DIL", "BPL", "SPL", "AH", "BH", "CH", "DH",
    "CF", "OF", "SF", "ZF", "AF", "PF", "DF", "IF", "FS_BASE", "GS_BASE"]
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
    | _ => .register name 32 32

private def x8632Globals : Primus.Semantics.Globals :=
  let registers := ["EAX", "EBX", "ECX", "EDX", "ESI", "EDI", "EBP", "ESP", "EIP",
    "AX", "BX", "CX", "DX", "SI", "DI", "BP", "SP", "AL", "BL", "CL", "DL", "AH", "BH", "CH", "DH",
    "CF", "OF", "SF", "ZF", "AF", "PF", "DF", "IF", "FS_BASE", "GS_BASE"]
  registers.map fun name => (name, x8632Register name)

private def riscvRegister (name : String) : Primus.Semantics.Value :=
  if name = "X0" then .register "XZR" 64 64 else .register name 64 64

private def riscvGlobals : Primus.Semantics.Globals :=
  (List.range 32).map fun n => (s!"X{n}", riscvRegister s!"X{n}")

private def riscv32Register (name : String) : Primus.Semantics.Value :=
  if name = "X0" then .register "XZR" 32 32 else .register name 32 32

private def riscv32Globals : Primus.Semantics.Globals :=
  (List.range 32).map fun n => (s!"X{n}", riscv32Register s!"X{n}")

private def powerpcRegister (name : String) : Primus.Semantics.Value :=
  let isConditionBit := (name.startsWith "CR" &&
    (name.endsWith "LT" || name.endsWith "GT" || name.endsWith "EQ" || name.endsWith "UN")) ||
    ["SO", "OV", "CA", "OV32", "CA32"].contains name
  if isConditionBit then .register name 1 1
  else if name = "ZERO" then .register "XZR" 64 64
  else if name.startsWith "X" && (name.drop 1).all Char.isDigit then
    .register ("R" ++ (name.drop 1).toString) 64 64
  else .register name 64 64

private def powerpcGlobals : Primus.Semantics.Globals :=
  let registers := (List.range 32).map fun n => s!"R{n}"
  let conditionFields := (List.range 8).flatMap fun n =>
    [s!"CR{n}LT", s!"CR{n}GT", s!"CR{n}EQ", s!"CR{n}UN"]
  (registers ++ conditionFields ++ ["ZERO", "LR", "CTR", "TAR", "SO", "OV", "CA", "OV32", "CA32"]).map
    fun name => (name, powerpcRegister name)

private def powerpc32Register (name : String) : Primus.Semantics.Value :=
  let isConditionBit := (name.startsWith "CR" &&
    (name.endsWith "LT" || name.endsWith "GT" || name.endsWith "EQ" || name.endsWith "UN")) ||
    ["SO", "OV", "CA", "OV32", "CA32"].contains name
  if isConditionBit then .register name 1 1
  else if name = "ZERO" then .register "XZR" 32 32
  else if name.startsWith "X" && (name.drop 1).all Char.isDigit then
    .register ("R" ++ (name.drop 1).toString) 32 32
  else .register name 32 32

private def powerpc32Globals : Primus.Semantics.Globals :=
  let registers := (List.range 32).map fun n => s!"R{n}"
  let conditionFields := (List.range 8).flatMap fun n =>
    [s!"CR{n}LT", s!"CR{n}GT", s!"CR{n}EQ", s!"CR{n}UN"]
  (registers ++ conditionFields ++ ["ZERO", "LR", "CTR", "TAR", "SO", "OV", "CA", "OV32", "CA32"]).map
    fun name => (name, powerpc32Register name)

private def powerpc32Operand : LLVM.Operand → Primus.Semantics.Value
  | .reg name => powerpc32Register name
  | .imm value => .bil 32 (.int (BitVec.ofInt 32 value))

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

private def mipsRegister (name : String) : Primus.Semantics.Value :=
  .register (mipsCanonicalName name) 64 64

private def mipsGlobals : Primus.Semantics.Globals :=
  let registers := (List.range 32).map fun n => s!"R{n}"
  (registers ++ ["ZERO", "RA", "HI", "LO"]).map fun name => (name, mipsRegister name)

private def mips32Register (name : String) : Primus.Semantics.Value :=
  .register (mipsCanonicalName name) 32 32

private def mips32Globals : Primus.Semantics.Globals :=
  let registers := (List.range 32).map fun n => s!"R{n}"
  (registers ++ ["ZERO", "RA", "HI", "LO"]).map fun name => (name, mips32Register name)

private def mips32Operand : LLVM.Operand → Primus.Semantics.Value
  | .reg name => mips32Register name
  | .imm value => .bil 32 (.int (BitVec.ofInt 32 value))

private def arm32Register (name : String) : Primus.Semantics.Value :=
  let name := if name.isEmpty || name = "NoRegister" then "Nil" else name
  if ["NF", "ZF", "CF", "VF", "QF"].contains name then .register name 1 1
  else .register name 32 32

private def arm32Globals : Primus.Semantics.Globals :=
  let registers := (List.range 16).map fun n => s!"R{n}"
  (registers ++ ["SP", "LR", "PC", "CPSR", "Nil", "NF", "ZF", "CF", "VF", "QF"]).map
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

private def numericOperations (triple : String) (globals : Primus.Semantics.Globals) :
    IO (List (Nat × Primus.Semantics.Callable)) :=
  globals.filterMapM fun binding =>
    match binding.2 with
    | .callable callable => do
      let opcode ← LLVM.opcodeId? triple binding.1
      pure (opcode.map fun opcode => (opcode, callable))
    | _ => pure none

private def makeEnvironment (definitions globals : Primus.Semantics.Globals) :
    Primus.Semantics.Environment :=
  .ofGlobals (Primus.Semantics.compileGlobals (definitions ++ globals))

/-- The x86 opcodes whose first operand is a displacement from the next instruction. -/
private def x86RelativeOpcodes : List String :=
  ["JMP_1", "JMP_2", "JMP_4", "JCC_1", "JCC_2", "JCC_4", "JCXZ", "JECXZ", "JRCXZ",
    "LOOP", "LOOPE", "LOOPNE", "XBEGIN_2", "XBEGIN_4",
    "CALLpcrel16", "CALLpcrel32", "CALL64pcrel32"]

def aarch64Environment : IO Primus.Semantics.Environment := do
  let context := semanticsContext 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "arm") ["aarch64"] context
  let definitions := Primus.Semantics.compileGlobals definitions
  let opcodes ← numericOperations "aarch64" definitions
  let names := (List.range 31).flatMap (fun n => [s!"X{n}", s!"W{n}"]) ++
    (List.range 32).flatMap (fun n => [s!"B{n}", s!"H{n}", s!"S{n}", s!"D{n}", s!"Q{n}"]) ++
    ["SP", "WSP", "XZR", "WZR"]
  let registers ← names.mapM fun name => do
    let llvmName := if name = "X29" then "FP" else if name = "X30" then "LR" else name
    let id ← LLVM.registerId "aarch64" llvmName
    pure (id, aarch64Register name)
  pure (.ofMachine (definitions ++ aarch64Globals) opcodes registers)

private def numericOperationsWithAliases (aliases : List (String × String)) (triple : String)
    (globals : Primus.Semantics.Globals) : IO (List (Nat × Primus.Semantics.Callable)) :=
  let globals := globals.map fun binding =>
    match Assoc.get binding.1 aliases with
    | some name => (name, binding.2)
    | none => binding
  numericOperations triple globals

def x86Environment : IO Primus.Semantics.Environment := do
  let context := semanticsContext 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "x86")
    ["bits", "x86-64", "x86-bits", "x86-move", "x86-arith", "x86-control"] context
  let definitions := Primus.Semantics.compileGlobals definitions
  let opcodes ← numericOperationsWithAliases [("RETQ", "RET64"), ("NOP", "NOOP")] "x86_64" definitions
  let registers ← LLVM.registerNames "x86_64"
  let registers := (0, x86Register "Nil") ::
    (registers.map fun binding => (binding.1, x86Register binding.2))
  let signExtendedOpcodes ← definitions.filterMapM fun binding =>
    if binding.1.endsWith "ri32" || binding.1.endsWith "mi32" || binding.1.endsWith "i32" then
      LLVM.opcodeId? "x86_64" binding.1
    else pure none
  let relativeOpcodes ← x86RelativeOpcodes.filterMapM (LLVM.opcodeId? "x86_64")
  let environment := Primus.Semantics.Environment.ofMachine
    (definitions ++ x86Globals) opcodes registers
  pure { environment with signExtendedOpcodes, relativeOpcodes }

def riscvEnvironment : IO Primus.Semantics.Environment := do
  let context := semanticsContext 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "riscv") ["riscv"] context
  let definitions := Primus.Semantics.compileGlobals definitions
  let opcodes ← numericOperations "riscv64" definitions
  let registers ← (List.range 32).mapM fun n => do
    let id ← LLVM.registerId "riscv64" s!"X{n}"
    pure (id, riscvRegister s!"X{n}")
  pure (.ofMachine (definitions ++ riscvGlobals) opcodes registers)

def powerpcEnvironment : IO Primus.Semantics.Environment := do
  let context := semanticsContext 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "powerpc") ["bits", "powerpc"] context
  let definitions := Primus.Semantics.compileGlobals definitions
  let opcodes ← numericOperations "powerpc64le" definitions
  let registers ← LLVM.registerNames "powerpc64le"
  let registers := (0, powerpcRegister "Nil") ::
    (registers.map fun binding => (binding.1, powerpcRegister binding.2))
  pure (.ofMachine (definitions ++ powerpcGlobals) opcodes registers)

def mipsEnvironment : IO Primus.Semantics.Environment := do
  let context := { semanticsContext 0 0 with endian := .big }
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "mips") ["mips"] context
  pure (makeEnvironment definitions mipsGlobals)

private def arm32Context (address nextPc : Nat) : Primus.Semantics.Context :=
  { bits := 32, pc := address, nextPc := nextPc, memory := ⟨"mem", .mem 32 8, 0, false⟩ }

def x8632Environment : IO Primus.Semantics.Environment := do
  let context := arm32Context 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "x86")
    ["bits", "x86-32", "x86-bits", "x86-move", "x86-arith", "x86-control"] context
  let definitions := Primus.Semantics.compileGlobals definitions
  let opcodes ← numericOperationsWithAliases
    [("RETQ", "RET32"), ("RETL", "RET32"), ("NOP", "NOOP")] "i386" definitions
  let registers ← LLVM.registerNames "i386"
  let registers := (0, x8632Register "Nil") ::
    (registers.map fun binding => (binding.1, x8632Register binding.2))
  let relativeOpcodes ← x86RelativeOpcodes.filterMapM (LLVM.opcodeId? "i386")
  let environment := Primus.Semantics.Environment.ofMachine
    (definitions ++ x8632Globals) opcodes registers
  pure { environment with relativeOpcodes }

def riscv32Environment : IO Primus.Semantics.Environment := do
  let context := arm32Context 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "riscv") ["riscv"] context
  let definitions := Primus.Semantics.compileGlobals definitions
  let opcodes ← numericOperations "riscv32" definitions
  let registers ← (List.range 32).mapM fun n => do
    let id ← LLVM.registerId "riscv32" s!"X{n}"
    pure (id, riscv32Register s!"X{n}")
  pure (.ofMachine (definitions ++ riscv32Globals) opcodes registers)

def mips32Environment : IO Primus.Semantics.Environment := do
  let context := { arm32Context 0 0 with endian := .big }
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "mips") ["mips"] context
  pure (makeEnvironment definitions mips32Globals)

def powerpc32Environment : IO Primus.Semantics.Environment := do
  let context := { arm32Context 0 0 with endian := .big }
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "powerpc") ["bits", "powerpc"] context
  let definitions := Primus.Semantics.compileGlobals definitions
  let opcodes ← numericOperations "powerpc" definitions
  let registers ← LLVM.registerNames "powerpc"
  let registers := (0, powerpc32Register "Nil") ::
    (registers.map fun binding => (binding.1, powerpc32Register binding.2))
  pure (.ofMachine (definitions ++ powerpc32Globals) opcodes registers)

def arm32Environment : IO Primus.Semantics.Environment := do
  let context := arm32Context 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "arm") ["arm"] context
  pure (makeEnvironment definitions arm32Globals)

private def arm32Immediate (value : Int) : Primus.Semantics.Value :=
  .bil 32 (.int (BitVec.ofInt 32 value))

private def arm32Operand : LLVM.Operand → Primus.Semantics.Value
  | .reg name => arm32Register name
  | .imm value => arm32Immediate value

def thumbEnvironment : IO Primus.Semantics.Environment := do
  let context := arm32Context 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "arm") ["thumb2"] context
  pure (makeEnvironment definitions arm32Globals)

/-- A Thumb branch or call: its displacement operand, from the pc, the address plus four. LLVM
gives BLX an A32 target, which is relative to the word-aligned pc. -/
private def thumbTarget (address : Nat) (decoded : LLVM.Decoded) : Option Nat :=
  let displacement :=
    if ["t2B", "t2Bcc", "tB", "tBcc"].contains decoded.opcode then decoded.operands.head?
    else if ["tBL", "tBLXi", "tCBZ", "tCBNZ"].contains decoded.opcode then decoded.operands.getLast?
    else none
  let pc := if decoded.opcode = "tBLXi" then (address + 4) / 4 * 4 else address + 4
  match displacement with
  | some (.imm displacement) =>
    let target := Int.ofNat pc + displacement
    if target ≥ 0 then some target.toNat else none
  | _ => none

/-- An A32 branch or call: its displacement operand, from the pc, the address plus eight. -/
private def arm32Target (address : Nat) (decoded : LLVM.Decoded) : Option Nat :=
  match ["Bcc", "BL", "BL_pred", "BLXi"].contains decoded.opcode, decoded.operands.head? with
  | true, some (.imm displacement) =>
    let target := Int.ofNat (address + 8) + displacement
    if target ≥ 0 then some target.toNat else none
  | _, _ => none

/-- A direct branch or call by the flags of LLVM. -/
private def directControl (flags : Nat) : Bool :=
  flags &&& 8 != 0 && flags &&& 16 == 0 || flags &&& 2 != 0

/-- `J`, `JAL` and `JALX` give the low 28 bits of the target, the upper bits are of the delay slot.
The other direct branches and calls give a displacement from the branch, which LLVM has already
adjusted for the delay slot. -/
private def mipsTarget (address : Nat) (decoded : LLVM.Decoded) : Option Nat :=
  match decoded.operands.getLast? with
  | some (.imm immediate) =>
    if ["J", "JAL", "JALX"].contains decoded.opcode then
      if immediate ≥ 0 then some ((address + 4) / 0x10000000 * 0x10000000 + immediate.toNat)
      else none
    else if directControl decoded.flags then
      let target := Int.ofNat address + immediate
      if target ≥ 0 then some target.toNat else none
    else none
  | _ => none

/-- The instruction word at the start of `data`. -/
private def instructionWord (endian : Endian) (data : ByteArray) : Nat :=
  let byte (index : Nat) : Nat := (data.get! index).toNat
  match endian with
  | .little => byte 0 + byte 1 * 0x100 + byte 2 * 0x10000 + byte 3 * 0x1000000
  | .big => byte 3 + byte 2 * 0x100 + byte 1 * 0x10000 + byte 0 * 0x1000000

/-- The I-form and B-form branches have the displacement, of words, as the last operand, and the
absolute variants have the AA bit, which is what tells BA from B. The other branches that LLVM
marks as direct, e.g., `gBCLR`, go through a register. -/
private def powerpcMCTarget (address word : Nat) (operands : List LLVM.MCOperand) : Option Nat :=
  let primary := word / 0x4000000
  match primary == 16 || primary == 18, operands.getLast? with
  | true, some (.imm displacement) =>
    let origin : Int := if word &&& 2 != 0 then 0 else Int.ofNat address
    let target := origin + displacement * 4
    if target ≥ 0 then some target.toNat else none
  | _, _ => none

/-- LLVM has no flags for `JAL`, whose major opcode this is. -/
private def riscvIsJal (word : Nat) : Bool := word % 0x80 == 0x6f

private def riscvMCTarget (address word flags : Nat) (operands : List LLVM.MCOperand) : Option Nat :=
  match riscvIsJal word || flags &&& 8 != 0 && flags &&& 16 == 0, operands.getLast? with
  | true, some (.imm displacement) =>
    let target := Int.ofNat address + displacement
    if target ≥ 0 then some target.toNat else none
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

private def normalizeAssembly (assembly : String) : String :=
  let tokens := (assembly.split Char.isWhitespace).toList.map fun token => token.toString
  String.intercalate " " (tokens.filter fun token => !token.isEmpty)

private def aarch64MCTarget (address : Nat) (flags : Nat) (operands : List LLVM.MCOperand) : Option Nat :=
  let selected := if flags &&& 32 != 0 then operands.getLast? else operands.head?
  match directControl flags, selected with
  | true, some (.imm displacement) =>
    let target := Int.ofNat address + displacement * 4
    if target ≥ 0 then some target.toNat else none
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
  let decoded ← LLVM.disassembleMC "aarch64" (data.extract (address - base) data.size) address
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

private def x86MCTarget (globals : Primus.Semantics.Environment) (next : Nat) (opcode : Nat)
    (operands : List LLVM.MCOperand) : Option Nat :=
  match globals.relativeOpcodes.contains opcode, operands.head? with
  | true, some (.imm displacement) =>
    let target := Int.ofNat next + displacement
    if target ≥ 0 then some target.toNat else none
  | _, _ => none

def decodeX86With (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let decoded ← LLVM.disassembleMC "x86_64" (data.extract (address - base) data.size) address
  let context := semanticsContext address (address + decoded.size)
  let opcode := LLVM.mcOpcode decoded.instruction
  let machineOperands ← LLVM.mcOperands decoded.instruction
  let operands ← x86MCOperands globals opcode machineOperands
  let bil ← Primus.Semantics.liftMC globals context opcode operands
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := flow decoded.flags
    target := x86MCTarget globals (address + decoded.size) opcode machineOperands
    bil := resolveHighBytes x86HighByteBase 64 bil
  }

def decodeX86 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeX86With (← x86Environment) base address data

def decodeX8632With (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let decoded ← LLVM.disassembleMC "i386" (data.extract (address - base) data.size) address
  let context := arm32Context address (address + decoded.size)
  let opcode := LLVM.mcOpcode decoded.instruction
  let machineOperands ← LLVM.mcOperands decoded.instruction
  let operands ← machineOperands.mapM fun value =>
    match Primus.Semantics.machineOperand globals context value with
    | .ok operand => pure operand
    | .error error => throw <| IO.userError error
  let bil ← Primus.Semantics.liftMC globals context opcode operands
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := flow decoded.flags
    target := x86MCTarget globals (address + decoded.size) opcode machineOperands
    bil := resolveHighBytes x8632HighByteBase 32 bil
  }

def decodeX8632 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeX8632With (← x8632Environment) base address data

def decodeRISCVWith (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let bytes := data.extract (address - base) data.size
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
    target := riscvMCTarget address word decoded.flags machineOperands
    bil := bil
  }

def decodeRISCV (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeRISCVWith (← riscvEnvironment) base address data

def decodeRISCV32With (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let bytes := data.extract (address - base) data.size
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
    target := riscvMCTarget address word decoded.flags machineOperands
    bil := bil
  }

def decodeRISCV32 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeRISCV32With (← riscv32Environment) base address data

def decodePowerPCWith (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let bytes := data.extract (address - base) data.size
  let decoded ← LLVM.disassembleMC "powerpc64le" bytes address
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
    flow := flow decoded.flags
    target := powerpcMCTarget address word machineOperands
    bil := bil
  }

def decodePowerPC (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodePowerPCWith (← powerpcEnvironment) base address data

def decodePowerPC32With (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let bytes := data.extract (address - base) data.size
  let decoded ← LLVM.disassembleMC "powerpc" bytes address
  let word := instructionWord .big bytes
  let context := { arm32Context address (address + decoded.size) with endian := .big }
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
    target := powerpcMCTarget address word machineOperands
    bil := bil
  }

def decodePowerPC32 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodePowerPC32With (← powerpc32Environment) base address data

def decodeMIPSWith (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let decoded ← LLVM.disassemble "mips64" (data.extract (address - base) data.size) address
  let context := { semanticsContext address (address + decoded.size) with endian := .big }
  let operands := decoded.operands.map (operand mipsRegister decoded.opcode)
  let bil ← Primus.Semantics.liftWith globals context decoded.opcode operands
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := flow decoded.flags
    target := mipsTarget address decoded
    bil := bil
  }

def decodeMIPS (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeMIPSWith (← mipsEnvironment) base address data

def decodeMIPS32With (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let decoded ← LLVM.disassemble "mips" (data.extract (address - base) data.size) address
  let context := { arm32Context address (address + decoded.size) with endian := .big }
  let operands := decoded.operands.map mips32Operand
  let bil ← Primus.Semantics.liftWith globals context decoded.opcode operands
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := flow decoded.flags
    target := mipsTarget address decoded
    bil := bil
  }

def decodeMIPS32 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeMIPS32With (← mips32Environment) base address data

def decodeARM32With (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let decoded ← LLVM.disassemble "armv7" (data.extract (address - base) data.size) address
  let context := arm32Context address (address + decoded.size)
  let bil ← Primus.Semantics.liftWith globals context decoded.opcode
    (decoded.operands.map arm32Operand)
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := arm32Flow decoded
    target := arm32Target address decoded
    bil := bil
  }

def decodeARM32 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeARM32With (← arm32Environment) base address data

def decodeThumbWith (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let decoded ← LLVM.disassemble "thumbv7" (data.extract (address - base) data.size) address
  let context := arm32Context address (address + decoded.size)
  let bil ← Primus.Semantics.liftWith globals context decoded.opcode
    (decoded.operands.map arm32Operand)
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := flow decoded.flags
    target := thumbTarget address decoded
    bil := bil
  }

def decodeThumb (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeThumbWith (← thumbEnvironment) base address data

end Bap.Target.LLVMLift
