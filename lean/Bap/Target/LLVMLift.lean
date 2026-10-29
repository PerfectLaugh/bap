import Bap.LLVM
import Bap.Disasm.Basic
import Bap.Primus.Semantics

namespace Bap.Target.LLVMLift

private def aarch64Register (name : String) : Primus.Semantics.Value :=
  let name := if name = "LR" then "X30" else if name = "FP" then "X29" else name
  if name = "XZR" || name = "WZR" then
    .register "XZR" 64 64
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

private def x86BaseRegister (name : String) : String :=
  match name with
  | "EAX" => "RAX" | "EBX" => "RBX" | "ECX" => "RCX" | "EDX" => "RDX"
  | "ESI" => "RSI" | "EDI" => "RDI" | "EBP" => "RBP" | "ESP" => "RSP"
  | name => name

private def x86Register (name : String) : Primus.Semantics.Value :=
  let name := if name.isEmpty || name = "NoRegister" then "Nil" else name
  if ["CF", "OF", "SF", "ZF", "AF", "PF", "DF", "IF"].contains name then
    .register name 1 1
  else if ["EAX", "EBX", "ECX", "EDX", "ESI", "EDI", "EBP", "ESP"].contains name then
    .register (x86BaseRegister name) 32 64
  else
    .register name 64 64

private def aarch64Globals : Primus.Semantics.Globals :=
  let registers := (List.range 31).map fun n => s!"X{n}"
  (registers ++ ["SP", "LR", "XZR", "NF", "ZF", "CF", "VF"]).map fun name => (name, aarch64Register name)

private def x86Globals : Primus.Semantics.Globals :=
  let registers := ["RAX", "RBX", "RCX", "RDX", "RSI", "RDI", "RBP", "RSP",
    "EAX", "EBX", "ECX", "EDX", "ESI", "EDI", "EBP", "ESP", "RIP",
    "CF", "OF", "SF", "ZF", "AF", "PF", "DF", "IF", "FS_BASE", "GS_BASE"]
  registers.map fun name => (name, x86Register name)

private def x8632Register (name : String) : Primus.Semantics.Value :=
  let name := if name.isEmpty || name = "NoRegister" then "Nil" else name
  if ["CF", "OF", "SF", "ZF", "AF", "PF", "DF", "IF"].contains name then
    .register name 1 1
  else
    .register name 32 32

private def x8632Globals : Primus.Semantics.Globals :=
  let registers := ["EAX", "EBX", "ECX", "EDX", "ESI", "EDI", "EBP", "ESP", "EIP",
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

private def mipsRegister (name : String) : Primus.Semantics.Value :=
  let name := mipsRegisterName name
  if name.startsWith "$" && (name.drop 1).all Char.isDigit then
    .register ("R" ++ (name.drop 1).toString) 64 64
  else .register name 64 64

private def mipsGlobals : Primus.Semantics.Globals :=
  let registers := (List.range 32).map fun n => s!"R{n}"
  (registers ++ ["ZERO", "RA", "HI", "LO"]).map fun name => (name, mipsRegister name)

private def mips32Register (name : String) : Primus.Semantics.Value :=
  let name := mipsRegisterName name
  if name.startsWith "$" && (name.drop 1).all Char.isDigit then
    .register ("R" ++ (name.drop 1).toString) 32 32
  else .register name 32 32

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

def aarch64Environment : IO Primus.Semantics.Environment := do
  let context := semanticsContext 0 0
  let definitions ← Primus.Semantics.loadMany (← pluginDirectories "arm") ["aarch64"] context
  let definitions := Primus.Semantics.compileGlobals definitions
  let opcodes ← numericOperations "aarch64" definitions
  let names := (List.range 31).flatMap (fun n => [s!"X{n}", s!"W{n}"]) ++
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
  let relativeOpcodes ← ["JMP_1", "JMP_2", "JMP_4", "JCC_1", "JCC_2", "JCC_4",
    "CALLpcrel16", "CALLpcrel32", "CALL64pcrel32"].mapM (LLVM.opcodeId "x86_64")
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
  let relativeOpcodes ← ["JMP_1", "JMP_2", "JMP_4", "JCC_1", "JCC_2", "JCC_4",
    "CALLpcrel16", "CALLpcrel32", "CALL64pcrel32"].mapM (LLVM.opcodeId "i386")
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

private def thumbCall (address : Nat) (decoded : LLVM.Decoded) :
    String × List Primus.Semantics.Value :=
  if ["t2B", "t2Bcc"].contains decoded.opcode then
    match decoded.operands with
    | .imm target :: rest =>
      let displacement := target - Int.ofNat (address + 4)
      (decoded.opcode, arm32Immediate displacement :: rest.map arm32Operand)
    | _ => (decoded.opcode, decoded.operands.map arm32Operand)
  else
    (decoded.opcode, decoded.operands.map arm32Operand)

private def thumbTarget (decoded : LLVM.Decoded) : Option Nat :=
  match ["t2B", "t2Bcc"].contains decoded.opcode, decoded.operands.head? with
  | true, some (.imm target) => if target ≥ 0 then some target.toNat else none
  | _, _ => none

private def arm32Call (address : Nat) (decoded : LLVM.Decoded) :
    String × List Primus.Semantics.Value :=
  if ["Bcc", "BL", "BL_pred", "BLXi"].contains decoded.opcode then
    match decoded.operands with
    | .imm target :: rest =>
      let displacement := target - Int.ofNat (address + 8)
      (decoded.opcode, arm32Immediate displacement :: rest.map arm32Operand)
    | _ => (decoded.opcode, decoded.operands.map arm32Operand)
  else
    (decoded.opcode, decoded.operands.map arm32Operand)

private def arm32Target (decoded : LLVM.Decoded) : Option Nat :=
  match ["Bcc", "BL", "BL_pred", "BLXi"].contains decoded.opcode, decoded.operands.head? with
  | true, some (.imm target) => if target ≥ 0 then some target.toNat else none
  | _, _ => none

private def mipsTarget (address : Nat) (decoded : LLVM.Decoded) : Option Nat :=
  match ["BEQ", "BNE"].contains decoded.opcode, decoded.operands.getLast? with
  | true, some (.imm displacement) =>
    let target := Int.ofNat address + displacement
    if target ≥ 0 then some target.toNat else none
  | _, _ => none

private def powerpcMCTarget (address : Nat) (flags : Nat) (operands : List LLVM.MCOperand) : Option Nat :=
  match flags &&& 8 != 0 && flags &&& 16 == 0, operands.head? with
  | true, some (.imm displacement) =>
    let target := Int.ofNat address + displacement * 4
    if target ≥ 0 then some target.toNat else none
  | _, _ => none

private def riscvMCTarget (address : Nat) (flags : Nat) (operands : List LLVM.MCOperand) : Option Nat :=
  match flags &&& 8 != 0 && flags &&& 16 == 0, operands.getLast? with
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

private def normalizeAssembly (assembly : String) : String :=
  let tokens := (assembly.split Char.isWhitespace).toList.map fun token => token.toString
  String.intercalate " " (tokens.filter fun token => !token.isEmpty)

private def aarch64MCTarget (address : Nat) (flags : Nat) (operands : List LLVM.MCOperand) : Option Nat :=
  match flags &&& 8 != 0 && flags &&& 16 == 0, operands.head? with
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
    | true, [.imm displacement, .imm code] =>
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
  let bil ← Primus.Semantics.liftMC globals context (LLVM.mcOpcode decoded.instruction) operands
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
    bil := bil
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
    bil := bil
  }

def decodeX8632 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeX8632With (← x8632Environment) base address data

def decodeRISCVWith (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let decoded ← LLVM.disassembleMC "riscv64" (data.extract (address - base) data.size) address
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
    target := riscvMCTarget address decoded.flags machineOperands
    bil := bil
  }

def decodeRISCV (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeRISCVWith (← riscvEnvironment) base address data

def decodeRISCV32With (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let decoded ← LLVM.disassembleMC "riscv32" (data.extract (address - base) data.size) address
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
    flow := flow decoded.flags
    target := riscvMCTarget address decoded.flags machineOperands
    bil := bil
  }

def decodeRISCV32 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeRISCV32With (← riscv32Environment) base address data

def decodePowerPCWith (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let decoded ← LLVM.disassembleMC "powerpc64le" (data.extract (address - base) data.size) address
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
    target := powerpcMCTarget address decoded.flags machineOperands
    bil := bil
  }

def decodePowerPC (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodePowerPCWith (← powerpcEnvironment) base address data

def decodePowerPC32With (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let decoded ← LLVM.disassembleMC "powerpc" (data.extract (address - base) data.size) address
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
    target := powerpcMCTarget address decoded.flags machineOperands
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
  let call := arm32Call address decoded
  let bil ← Primus.Semantics.liftWith globals context call.1 call.2
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := flow decoded.flags
    target := arm32Target decoded
    bil := bil
  }

def decodeARM32 (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeARM32With (← arm32Environment) base address data

def decodeThumbWith (globals : Primus.Semantics.Environment) (base address : Nat)
    (data : ByteArray) : IO Disasm.Insn := do
  let decoded ← LLVM.disassemble "thumbv7" (data.extract (address - base) data.size) address
  let context := arm32Context address (address + decoded.size)
  let call := thumbCall address decoded
  let bil ← Primus.Semantics.liftWith globals context call.1 call.2
  pure {
    address := address
    size := decoded.size
    asm := normalizeAssembly decoded.assembly
    flow := flow decoded.flags
    target := thumbTarget decoded
    bil := bil
  }

def decodeThumb (base address : Nat) (data : ByteArray) : IO Disasm.Insn := do
  decodeThumbWith (← thumbEnvironment) base address data

end Bap.Target.LLVMLift
