import BapTests.Support

set_option maxRecDepth 4000

namespace Bap.Tests.LLVM

open Bap

private def reg (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩

private def executeEffect (insn : Disasm.Insn) (env : Bil.Env := []) : IO (Bil.State × Bil.Effect) :=
  match Bil.run insn.bil { env := env } with
  | .ok result => pure result
  | .error error => throw <| IO.userError error

private def execute (insn : Disasm.Insn) (env : Bil.Env := []) : IO Bil.State := do
  let (state, _) ← executeEffect insn env
  pure state

private def assertReg (label name : String) (expected : Nat) (state : Bil.State) : IO Unit :=
  match Bil.lookup state.env (reg name) with
  | .ok (.bits value) => assertEqual label expected value.toNat
  | .ok _ => throw <| IO.userError s!"{name} is not a bitvector"
  | .error error => throw <| IO.userError error

private def assertReg32 (label name : String) (expected : Nat) (state : Bil.State) : IO Unit :=
  let var : Bap.Var := ⟨name, .imm 32, 0, false⟩
  match Bil.lookup state.env var with
  | .ok (.bits value) => assertEqual label expected value.toNat
  | .ok _ => throw <| IO.userError s!"{name} is not a bitvector"
  | .error error => throw <| IO.userError error

private def assertFlag (label name : String) (expected : Nat) (state : Bil.State) : IO Unit :=
  let var : Bap.Var := ⟨name, .imm 1, 0, false⟩
  match Bil.lookup state.env var with
  | .ok (.bits value) => assertEqual label expected value.toNat
  | .ok _ => throw <| IO.userError s!"{name} is not a bit"
  | .error error => throw <| IO.userError error

private def assertNormal (label : String) : Bil.Effect → IO Unit
  | .normal => IO.println s!"ok: {label}"
  | _ => throw <| IO.userError s!"{label}: expected normal effect"

private def assertJump (label : String) (expected : Nat) : Bil.Effect → IO Unit
  | .jump target => assertEqual label expected target.toNat
  | _ => throw <| IO.userError s!"{label}: expected jump effect"

private def memVar : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩

private def assertMemory (label : String) (address expected : Nat) (state : Bil.State) : IO Unit :=
  match Bil.lookup state.env memVar with
  | .ok (@Value.memory 64 memory) =>
    assertEqual label expected (Memory.read memory (BitVec.ofNat 64 address) .little 8).toNat
  | .ok _ => throw <| IO.userError "memory is not mapped"
  | .error error => throw <| IO.userError error

private def expectBytes (label : String) (expected : List Nat) (actual : ByteArray) : IO Unit := do
  assertEqual label expected (actual.toList.map UInt8.toNat)

private def expectRoundTrip (label triple source : String) (expected : List Nat) : IO LLVM.Decoded := do
  let bytes ← LLVM.assemble triple source
  expectBytes s!"{label} assembly" expected bytes
  let decoded ← LLVM.disassemble triple bytes
  assertEqual s!"{label} decode size" expected.length decoded.size
  assertTrue s!"{label} decode text" (!decoded.assembly.isEmpty)
  assertTrue s!"{label} opcode" (!decoded.opcode.isEmpty)
  assertTrue s!"{label} operands" (!decoded.operands.isEmpty)
  pure decoded

def run : IO Unit := do
  let aarch64Environment ← Target.LLVMLift.aarch64Environment
  let x86Environment ← Target.LLVMLift.x86Environment
  let riscvEnvironment ← Target.LLVMLift.riscvEnvironment
  let powerpcEnvironment ← Target.LLVMLift.powerpcEnvironment
  let mipsEnvironment ← Target.LLVMLift.mipsEnvironment
  let arm32Environment ← Target.LLVMLift.arm32Environment
  let thumbEnvironment ← Target.LLVMLift.thumbEnvironment
  let x8632Environment ← Target.LLVMLift.x8632Environment
  let riscv32Environment ← Target.LLVMLift.riscv32Environment
  let mips32Environment ← Target.LLVMLift.mips32Environment
  let powerpc32Environment ← Target.LLVMLift.powerpc32Environment
  let decodeAArch64 := Target.LLVMLift.decodeAArch64With aarch64Environment 0 0
  let decodeX86 := Target.LLVMLift.decodeX86With x86Environment 0 0
  let decodeRISCV := Target.LLVMLift.decodeRISCVWith riscvEnvironment 0 0
  let decodePowerPC := Target.LLVMLift.decodePowerPCWith powerpcEnvironment 0 0
  let decodeMIPS := Target.LLVMLift.decodeMIPSWith mipsEnvironment 0 0
  let decodeARM32 := Target.LLVMLift.decodeARM32With arm32Environment 0 0
  let decodeThumb := Target.LLVMLift.decodeThumbWith thumbEnvironment 0 0
  let decodeX8632 := Target.LLVMLift.decodeX8632With x8632Environment 0 0
  let decodeRISCV32 := Target.LLVMLift.decodeRISCV32With riscv32Environment 0 0
  let decodeMIPS32 := Target.LLVMLift.decodeMIPS32With mips32Environment 0 0
  let decodePowerPC32 := Target.LLVMLift.decodePowerPC32With powerpc32Environment 0 0
  let aarch64 ← expectRoundTrip "LLVM AArch64" "aarch64" "add x0, x0, 1" [0x00, 0x04, 0x00, 0x91]
  assertEqual "LLVM AArch64 immediate operand" true (aarch64.operands.any fun operand => operand == .imm 1)
  let addInsn ← decodeAArch64 (← LLVM.assemble "aarch64" "add x0, x0, 1")
  let addState ← execute addInsn [(reg "X0", .bits (BitVec.ofNat 64 2))]
  assertReg "LLVM lifted AArch64 ADD" "X0" 3 addState
  let subInsn ← decodeAArch64 (← LLVM.assemble "aarch64" "sub x0, x0, 1")
  let subState ← execute subInsn [(reg "X0", .bits (BitVec.ofNat 64 3))]
  assertReg "LLVM lifted AArch64 SUB" "X0" 2 subState
  let addsInsn ← decodeAArch64 (← LLVM.assemble "aarch64" "adds x0, x0, 1")
  let addsState ← execute addsInsn [(reg "X0", .bits (BitVec.ofNat 64 0xffffffffffffffff))]
  assertReg "LLVM lifted AArch64 ADDS result" "X0" 0 addsState
  assertFlag "LLVM lifted AArch64 ADDS carry" "CF" 1 addsState
  assertFlag "LLVM lifted AArch64 ADDS zero" "ZF" 1 addsState
  assertFlag "LLVM lifted AArch64 ADDS negative" "NF" 0 addsState
  assertFlag "LLVM lifted AArch64 ADDS overflow" "VF" 0 addsState
  let addsOverflowState ← execute addsInsn [(reg "X0", .bits (BitVec.ofNat 64 0x7fffffffffffffff))]
  assertFlag "LLVM lifted AArch64 ADDS overflow sign" "NF" 1 addsOverflowState
  assertFlag "LLVM lifted AArch64 ADDS signed overflow" "VF" 1 addsOverflowState
  let cmpInsn ← decodeAArch64 (← LLVM.assemble "aarch64" "cmp x0, 1")
  let cmpState ← execute cmpInsn [(reg "X0", .bits (BitVec.ofNat 64 0))]
  assertReg "LLVM lifted AArch64 CMP has no destination" "X0" 0 cmpState
  assertFlag "LLVM lifted AArch64 CMP carry clear" "CF" 0 cmpState
  assertFlag "LLVM lifted AArch64 CMP zero clear" "ZF" 0 cmpState
  assertFlag "LLVM lifted AArch64 CMP negative" "NF" 1 cmpState
  assertFlag "LLVM lifted AArch64 CMP overflow clear" "VF" 0 cmpState
  let beqInsn ← decodeAArch64 (← LLVM.assemble "aarch64" "b.eq 0")
  let z : Bap.Var := ⟨"ZF", .imm 1, 0, false⟩
  let (_, beqTaken) ← executeEffect beqInsn [(z, .bits (BitVec.ofNat 1 1))]
  assertJump "LLVM lifted AArch64 b.eq taken" 0 beqTaken
  let (_, beqNotTaken) ← executeEffect beqInsn [(z, .bits (BitVec.ofNat 1 0))]
  assertNormal "LLVM lifted AArch64 b.eq not taken" beqNotTaken
  let backwardInsn ← Target.LLVMLift.decodeAArch64With aarch64Environment 0 0x1000
    (ByteArray.mk (Array.replicate 0x1000 0) ++ ByteArray.mk #[0x00, 0xfe, 0xff, 0x54])
  assertEqual "LLVM AArch64 backward conditional target" (some 0xfc0) backwardInsn.target
  let (_, backwardTaken) ← executeEffect backwardInsn [(z, .bits (BitVec.ofNat 1 1))]
  assertJump "LLVM lifted AArch64 backward b.eq taken" 0xfc0 backwardTaken
  let memory ← match Memory.write (Memory.empty 64) (BitVec.ofNat 64 0x1008)
    (BitVec.ofNat 64 0x1234) .little 8 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  let ldrInsn ← decodeAArch64 (← LLVM.assemble "aarch64" "ldr x0, [x1, 8]")
  let ldrState ← execute ldrInsn [(reg "X0", .bits (BitVec.ofNat 64 0xffffffffffffffff)),
    (reg "X1", .bits (BitVec.ofNat 64 0x1000)), (memVar, .memory memory)]
  assertReg "LLVM lifted AArch64 LDR" "X0" 0x1234 ldrState
  let indexedLdrInsn ← decodeAArch64 (← LLVM.assemble "aarch64" "ldr x0, [x1, w2, sxtw #3]")
  let indexedLdrState ← execute indexedLdrInsn [(reg "X0", .bits (BitVec.ofNat 64 0)),
    (reg "X1", .bits (BitVec.ofNat 64 0x1000)), (reg "X2", .bits (BitVec.ofNat 64 1)),
    (memVar, .memory memory)]
  assertReg "LLVM lifted AArch64 indexed LDR" "X0" 0x1234 indexedLdrState
  let byteLdrInsn ← decodeAArch64 (← LLVM.assemble "aarch64" "ldrb w0, [x1, x2]")
  let byteLdrState ← execute byteLdrInsn [(reg "X0", .bits (BitVec.ofNat 64 0xffffffffffffffff)),
    (reg "X1", .bits (BitVec.ofNat 64 0x1000)), (reg "X2", .bits (BitVec.ofNat 64 8)),
    (memVar, .memory memory)]
  assertReg "LLVM lifted AArch64 byte LDR zero-extends" "X0" 0x34 byteLdrState
  let ldr32Insn ← decodeAArch64 (← LLVM.assemble "aarch64" "ldr w0, [x1, 8]")
  let ldr32State ← execute ldr32Insn [(reg "X0", .bits (BitVec.ofNat 64 0xffffffffffffffff)),
    (reg "X1", .bits (BitVec.ofNat 64 0x1000)), (memVar, .memory memory)]
  assertReg "LLVM lifted AArch64 32-bit LDR" "X0" 0x1234 ldr32State
  let strInsn ← decodeAArch64 (← LLVM.assemble "aarch64" "str x0, [x1, 8]")
  let strState ← execute strInsn [(reg "X0", .bits (BitVec.ofNat 64 0x5678)),
    (reg "X1", .bits (BitVec.ofNat 64 0x1000)), (memVar, .memory memory)]
  assertMemory "LLVM lifted AArch64 STR" 0x1008 0x5678 strState
  let branchInsn ← decodeAArch64 (← LLVM.assemble "aarch64" "b 0")
  let (_, branchEffect) ← executeEffect branchInsn
  assertJump "LLVM lifted AArch64 B" 0 branchEffect
  let linkInsn ← decodeAArch64 (← LLVM.assemble "aarch64" "bl 0")
  let (linkState, linkEffect) ← executeEffect linkInsn
  assertReg "LLVM lifted AArch64 BL link" "X30" 4 linkState
  assertJump "LLVM lifted AArch64 BL target" 0 linkEffect
  let retInsn ← decodeAArch64 (ByteArray.mk #[0xc0, 0x03, 0x5f, 0xd6])
  let (_, retEffect) ← executeEffect retInsn [(reg "X30", .bits (BitVec.ofNat 64 0x1234))]
  assertJump "LLVM lifted AArch64 RET" 0x1234 retEffect
  let moviInsn ← decodeAArch64 (← LLVM.assemble "aarch64" "movi v2.4h, #0x68")
  let moviState ← execute moviInsn
  let vectorVar : Bap.Var := ⟨"Q2", .imm 128, 0, false⟩
  match Bil.lookup moviState.env vectorVar with
  | .ok (.bits value) => assertEqual "LLVM lifted AArch64 MOVI replication" 0x0068006800680068 value.toNat
  | .ok _ => throw <| IO.userError "Q2 is not a bitvector"
  | .error error => throw <| IO.userError error
  let bitmaskInsn ← decodeAArch64 (← LLVM.assemble "aarch64" "movi d1, #0xff00ff00ff00ff")
  let bitmaskState ← execute bitmaskInsn
  let vectorVar : Bap.Var := ⟨"Q1", .imm 128, 0, false⟩
  match Bil.lookup bitmaskState.env vectorVar with
  | .ok (.bits value) => assertEqual "LLVM lifted AArch64 MOVI bitmask" 0xff00ff00ff00ff value.toNat
  | .ok _ => throw <| IO.userError "Q1 is not a bitvector"
  | .error error => throw <| IO.userError error
  let reverseInsn ← decodeAArch64 (← LLVM.assemble "aarch64" "rev64 v3.4s, v3.4s")
  let reverseState ← execute reverseInsn [(⟨"Q3", .imm 128, 0, false⟩,
    .bits (BitVec.ofNat 128 0x0f0e0d0c0b0a09080706050403020100))]
  let vectorVar : Bap.Var := ⟨"Q3", .imm 128, 0, false⟩
  match Bil.lookup reverseState.env vectorVar with
  | .ok (.bits value) => assertEqual "LLVM lifted AArch64 REV64 lanes" 0x0b0a09080f0e0d0c0302010007060504 value.toNat
  | .ok _ => throw <| IO.userError "Q3 is not a bitvector"
  | .error error => throw <| IO.userError error
  let x86 ← expectRoundTrip "LLVM x86-64" "x86_64" "addq $-1, %rax" [0x48, 0x83, 0xc0, 0xff]
  assertEqual "LLVM x86 signed immediate operand" true (x86.operands.any fun operand => operand == .imm (-1))
  let x86AddInsn ← decodeX86 (← LLVM.assemble "x86_64" "addq $-1, %rax")
  let x86AddState ← execute x86AddInsn [(reg "RAX", .bits (BitVec.ofNat 64 0))]
  assertReg "LLVM lifted x86 ADD" "RAX" 0xffffffffffffffff x86AddState
  let x86SubInsn ← decodeX86 (← LLVM.assemble "x86_64" "subq $1, %rax")
  let x86SubState ← execute x86SubInsn [(reg "RAX", .bits (BitVec.ofNat 64 3))]
  assertReg "LLVM lifted x86 SUB" "RAX" 2 x86SubState
  let x86MovInsn ← decodeX86 (← LLVM.assemble "x86_64" "movq $42, %rax")
  let x86MovState ← execute x86MovInsn
  assertReg "LLVM lifted x86 MOV" "RAX" 42 x86MovState
  let x86MovSignedBytes ← LLVM.assemble "x86_64" "movq $-1, %rax"
  let x86MovSignedDecoded ← LLVM.disassemble "x86_64" x86MovSignedBytes
  assertEqual "LLVM x86 sign-extended MOV opcode" "MOV64ri32" x86MovSignedDecoded.opcode
  let x86MovSignedInsn ← decodeX86 x86MovSignedBytes
  let x86MovSignedState ← execute x86MovSignedInsn
  assertReg "LLVM lifted x86 sign-extended MOV" "RAX" 0xffffffffffffffff x86MovSignedState
  let x86MovUnsignedInsn ← decodeX86 (← LLVM.assemble "x86_64" "movq $4294967295, %rax")
  let x86MovUnsignedState ← execute x86MovUnsignedInsn
  assertReg "LLVM lifted x86 full-width MOV" "RAX" 0xffffffff x86MovUnsignedState
  let x86Mov32Insn ← decodeX86 (← LLVM.assemble "x86_64" "movl $-1, %eax")
  let x86Mov32State ← execute x86Mov32Insn [(reg "RAX", .bits (BitVec.ofNat 64 0xffffffffffffffff))]
  assertReg "LLVM lifted x86 32-bit write" "RAX" 0xffffffff x86Mov32State
  let x86XorInsn ← decodeX86 (← LLVM.assemble "x86_64" "xorq %rax, %rax")
  let x86XorState ← execute x86XorInsn [(reg "RAX", .bits (BitVec.ofNat 64 0x1234))]
  assertReg "LLVM lifted x86 XOR" "RAX" 0 x86XorState
  let x86RetInsn ← decodeX86 (ByteArray.mk #[0xc3])
  let x86RetMemory ← match Memory.write (Memory.empty 64) (BitVec.ofNat 64 0x1000)
    (BitVec.ofNat 64 0x5678) .little 8 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  let (x86RetState, x86RetEffect) ← executeEffect x86RetInsn
    [(reg "RSP", .bits (BitVec.ofNat 64 0x1000)), (memVar, .memory x86RetMemory)]
  assertReg "LLVM lifted x86 RET stack pointer" "RSP" 0x1008 x86RetState
  assertJump "LLVM lifted x86 RET target" 0x5678 x86RetEffect
  let _ ← expectRoundTrip "LLVM RISC-V" "riscv64" "addi a0, a0, 1" [0x13, 0x05, 0x15, 0x00]
  let riscvAddInsn ← decodeRISCV (← LLVM.assemble "riscv64" "addi a0, a0, 1")
  let riscvAddState ← execute riscvAddInsn [(reg "X10", .bits (BitVec.ofNat 64 2))]
  assertReg "LLVM lifted RISC-V ADDI" "X10" 3 riscvAddState
  let riscvZeroInsn ← decodeRISCV (← LLVM.assemble "riscv64" "addi zero, a0, 1")
  assertTrue "LLVM lifted RISC-V zero register" riscvZeroInsn.bil.isEmpty
  let riscvWordInsn ← decodeRISCV (← LLVM.assemble "riscv64" "addiw a0, a0, 1")
  let riscvWordState ← execute riscvWordInsn [(reg "X10", .bits (BitVec.ofNat 64 0x7fffffff))]
  assertReg "LLVM lifted RISC-V ADDIW sign extension" "X10" 0xffffffff80000000 riscvWordState
  let riscvLoadInsn ← decodeRISCV (← LLVM.assemble "riscv64" "ld a0, 8(a1)")
  let riscvLoadState ← execute riscvLoadInsn [(reg "X10", .bits (BitVec.ofNat 64 0)),
    (reg "X11", .bits (BitVec.ofNat 64 0x1000)), (memVar, .memory memory)]
  assertReg "LLVM lifted RISC-V LD" "X10" 0x1234 riscvLoadState
  let riscvStoreInsn ← decodeRISCV (← LLVM.assemble "riscv64" "sd a0, 8(a1)")
  let riscvStoreState ← execute riscvStoreInsn [(reg "X10", .bits (BitVec.ofNat 64 0x5678)),
    (reg "X11", .bits (BitVec.ofNat 64 0x1000)), (memVar, .memory memory)]
  assertMemory "LLVM lifted RISC-V SD" 0x1008 0x5678 riscvStoreState
  let riscvBranchInsn ← decodeRISCV (← LLVM.assemble "riscv64" "beq a0, a1, 0")
  let (_, riscvBranchTaken) ← executeEffect riscvBranchInsn
    [(reg "X10", .bits (BitVec.ofNat 64 1)), (reg "X11", .bits (BitVec.ofNat 64 1))]
  assertJump "LLVM lifted RISC-V BEQ taken" 0 riscvBranchTaken
  let (_, riscvBranchNotTaken) ← executeEffect riscvBranchInsn
    [(reg "X10", .bits (BitVec.ofNat 64 1)), (reg "X11", .bits (BitVec.ofNat 64 2))]
  assertNormal "LLVM lifted RISC-V BEQ not taken" riscvBranchNotTaken
  let riscvJalInsn ← decodeRISCV (← LLVM.assemble "riscv64" "jal ra, 0")
  let (riscvJalState, riscvJalEffect) ← executeEffect riscvJalInsn
  assertReg "LLVM lifted RISC-V JAL link" "X1" 4 riscvJalState
  assertJump "LLVM lifted RISC-V JAL target" 0 riscvJalEffect
  let riscvJalrInsn ← decodeRISCV (← LLVM.assemble "riscv64" "jalr ra, 0(a0)")
  let (riscvJalrState, riscvJalrEffect) ← executeEffect riscvJalrInsn
    [(reg "X10", .bits (BitVec.ofNat 64 0x1235))]
  assertReg "LLVM lifted RISC-V JALR link" "X1" 4 riscvJalrState
  assertJump "LLVM lifted RISC-V JALR target" 0x1234 riscvJalrEffect
  let _ ← expectRoundTrip "LLVM PowerPC" "powerpc64le" "addi 3, 3, 1" [0x01, 0x00, 0x63, 0x38]
  let powerpcAddInsn ← decodePowerPC (← LLVM.assemble "powerpc64le" "addi 3, 3, 1")
  let powerpcAddState ← execute powerpcAddInsn [(reg "R3", .bits (BitVec.ofNat 64 2))]
  assertReg "LLVM lifted PowerPC ADDI" "R3" 3 powerpcAddState
  let powerpcLoadInsn ← decodePowerPC (← LLVM.assemble "powerpc64le" "ld 3, 8(4)")
  let powerpcLoadState ← execute powerpcLoadInsn [(reg "R3", .bits (BitVec.ofNat 64 0)),
    (reg "R4", .bits (BitVec.ofNat 64 0x1000)), (memVar, .memory memory)]
  assertReg "LLVM lifted PowerPC LD" "R3" 0x1234 powerpcLoadState
  let powerpcStoreInsn ← decodePowerPC (← LLVM.assemble "powerpc64le" "std 3, 8(4)")
  let powerpcStoreState ← execute powerpcStoreInsn [(reg "R3", .bits (BitVec.ofNat 64 0x5678)),
    (reg "R4", .bits (BitVec.ofNat 64 0x1000)), (memVar, .memory memory)]
  assertMemory "LLVM lifted PowerPC STD" 0x1008 0x5678 powerpcStoreState
  let powerpcBranchInsn ← decodePowerPC (← LLVM.assemble "powerpc64le" "b 16")
  let (_, powerpcBranchEffect) ← executeEffect powerpcBranchInsn
  assertJump "LLVM lifted PowerPC B" 16 powerpcBranchEffect
  assertEqual "LLVM PowerPC branch metadata" (some 16) powerpcBranchInsn.target
  let powerpcLinkInsn ← decodePowerPC (← LLVM.assemble "powerpc64le" "bl 16")
  let (powerpcLinkState, powerpcLinkEffect) ← executeEffect powerpcLinkInsn
  assertReg "LLVM lifted PowerPC BL link" "LR" 4 powerpcLinkState
  assertJump "LLVM lifted PowerPC BL target" 16 powerpcLinkEffect
  let powerpcReturnInsn ← decodePowerPC (← LLVM.assemble "powerpc64le" "blr")
  let (_, powerpcReturnEffect) ← executeEffect powerpcReturnInsn
    [(reg "LR", .bits (BitVec.ofNat 64 0x1237))]
  assertJump "LLVM lifted PowerPC BLR aligned target" 0x1234 powerpcReturnEffect
  let _ ← expectRoundTrip "LLVM MIPS" "mips64" "addiu $2, $2, 1" [0x24, 0x42, 0x00, 0x01]
  let mipsAddInsn ← decodeMIPS (← LLVM.assemble "mips64" "addiu $2, $2, 1")
  let mipsAddState ← execute mipsAddInsn [(reg "R2", .bits (BitVec.ofNat 64 2))]
  assertReg "LLVM lifted MIPS ADDIU" "R2" 3 mipsAddState
  let mipsSignState ← execute mipsAddInsn [(reg "R2", .bits (BitVec.ofNat 64 0x7fffffff))]
  assertReg "LLVM lifted MIPS 32-bit sign extension" "R2" 0xffffffff80000000 mipsSignState
  let mipsMemory ← match Memory.write (Memory.empty 64) (BitVec.ofNat 64 0x1004)
    (BitVec.ofNat 32 0x12345678) .big 4 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  let mipsLoadInsn ← decodeMIPS (← LLVM.assemble "mips64" "lw $2, 4($3)")
  let mipsLoadState ← execute mipsLoadInsn [(reg "R2", .bits (BitVec.ofNat 64 0)),
    (reg "R3", .bits (BitVec.ofNat 64 0x1000)), (memVar, .memory mipsMemory)]
  assertReg "LLVM lifted MIPS big-endian LW" "R2" 0x12345678 mipsLoadState
  let mipsStoreInsn ← decodeMIPS (← LLVM.assemble "mips64" "sw $2, 4($3)")
  let mipsStoreState ← execute mipsStoreInsn [(reg "R2", .bits (BitVec.ofNat 64 0x89abcdef)),
    (reg "R3", .bits (BitVec.ofNat 64 0x1000)), (memVar, .memory mipsMemory)]
  match Bil.lookup mipsStoreState.env memVar with
  | .ok (@Value.memory 64 updated) =>
    assertEqual "LLVM lifted MIPS big-endian SW" 0x89abcdef
      (Memory.read updated (BitVec.ofNat 64 0x1004) .big 4).toNat
  | .ok _ => throw <| IO.userError "MIPS memory is not mapped"
  | .error error => throw <| IO.userError error
  let mipsBranchInsn ← decodeMIPS (ByteArray.mk #[0x10, 0x43, 0x00, 0x04])
  let (_, mipsBranchTaken) ← executeEffect mipsBranchInsn
    [(reg "R2", .bits (BitVec.ofNat 64 1)), (reg "R3", .bits (BitVec.ofNat 64 1))]
  assertJump "LLVM lifted MIPS BEQ taken" 20 mipsBranchTaken
  let (_, mipsBranchNotTaken) ← executeEffect mipsBranchInsn
    [(reg "R2", .bits (BitVec.ofNat 64 1)), (reg "R3", .bits (BitVec.ofNat 64 2))]
  assertNormal "LLVM lifted MIPS BEQ not taken" mipsBranchNotTaken
  let mipsReturnInsn ← decodeMIPS (← LLVM.assemble "mips64" "jr $31")
  let (_, mipsReturnEffect) ← executeEffect mipsReturnInsn [(reg "R31", .bits (BitVec.ofNat 64 0x1234))]
  assertJump "LLVM lifted MIPS JR" 0x1234 mipsReturnEffect
  let _ ← expectRoundTrip "LLVM ARM32" "armv7" "add r0, r0, 1" [0x01, 0x00, 0x80, 0xe2]
  let armAddInsn ← decodeARM32 (← LLVM.assemble "armv7" "add r0, r0, 1")
  let armAddState ← execute armAddInsn [(⟨"R0", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 2))]
  assertReg32 "LLVM lifted ARM32 ADD" "R0" 3 armAddState
  let armMemVar : Bap.Var := ⟨"mem", .mem 32 8, 0, false⟩
  let armMemory ← match Memory.write (Memory.empty 32) (BitVec.ofNat 32 0x1004)
    (BitVec.ofNat 32 0x12345678) .little 4 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  let armLoadInsn ← decodeARM32 (← LLVM.assemble "armv7" "ldr r0, [r1, #4]")
  let armLoadState ← execute armLoadInsn [(⟨"R1", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1000)),
    (armMemVar, .memory armMemory)]
  assertReg32 "LLVM lifted ARM32 LDR" "R0" 0x12345678 armLoadState
  let armStoreInsn ← decodeARM32 (← LLVM.assemble "armv7" "str r0, [r1, #4]")
  let armStoreState ← execute armStoreInsn [(⟨"R0", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x89abcdef)),
    (⟨"R1", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1000)), (armMemVar, .memory armMemory)]
  match Bil.lookup armStoreState.env armMemVar with
  | .ok (@Value.memory 32 updated) =>
    assertEqual "LLVM lifted ARM32 STR" 0x89abcdef
      (Memory.read updated (BitVec.ofNat 32 0x1004) .little 4).toNat
  | .ok _ => throw <| IO.userError "ARM32 memory is not mapped"
  | .error error => throw <| IO.userError error
  let armBranchInsn ← decodeARM32 (← LLVM.assemble "armv7" "beq 16")
  let armZ : Bap.Var := ⟨"ZF", .imm 1, 0, false⟩
  let (_, armBranchTaken) ← executeEffect armBranchInsn [(armZ, .bits (BitVec.ofNat 1 1))]
  assertJump "LLVM lifted ARM32 BEQ taken" 16 armBranchTaken
  assertEqual "LLVM ARM32 branch metadata" (some 16) armBranchInsn.target
  let (_, armBranchNotTaken) ← executeEffect armBranchInsn [(armZ, .bits (BitVec.ofNat 1 0))]
  assertNormal "LLVM lifted ARM32 BEQ not taken" armBranchNotTaken
  let armLinkInsn ← decodeARM32 (← LLVM.assemble "armv7" "bl 16")
  let (armLinkState, armLinkEffect) ← executeEffect armLinkInsn
  assertReg32 "LLVM lifted ARM32 BL link" "LR" 4 armLinkState
  assertJump "LLVM lifted ARM32 BL target" 16 armLinkEffect
  let armReturnInsn ← decodeARM32 (← LLVM.assemble "armv7" "bx r0")
  let (_, armReturnEffect) ← executeEffect armReturnInsn
    [(⟨"R0", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1235))]
  assertJump "LLVM lifted ARM32 BX" 0x1234 armReturnEffect
  let thumbAddInsn ← decodeThumb (← LLVM.assemble "thumbv7" "add.w r0, r0, 1")
  let thumbAddState ← execute thumbAddInsn [(⟨"R0", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 2))]
  assertReg32 "LLVM lifted Thumb ADD" "R0" 3 thumbAddState
  let thumbLoadInsn ← decodeThumb (← LLVM.assemble "thumbv7" "ldr.w r0, [r1, #4]")
  let thumbLoadState ← execute thumbLoadInsn [(⟨"R1", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1000)),
    (armMemVar, .memory armMemory)]
  assertReg32 "LLVM lifted Thumb LDR" "R0" 0x12345678 thumbLoadState
  let thumbStoreInsn ← decodeThumb (← LLVM.assemble "thumbv7" "str.w r0, [r1, #4]")
  let thumbStoreState ← execute thumbStoreInsn [(⟨"R0", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x89abcdef)),
    (⟨"R1", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1000)), (armMemVar, .memory armMemory)]
  match Bil.lookup thumbStoreState.env armMemVar with
  | .ok (@Value.memory 32 updated) =>
    assertEqual "LLVM lifted Thumb STR" 0x89abcdef
      (Memory.read updated (BitVec.ofNat 32 0x1004) .little 4).toNat
  | .ok _ => throw <| IO.userError "Thumb memory is not mapped"
  | .error error => throw <| IO.userError error
  let thumbBranchInsn ← decodeThumb (← LLVM.assemble "thumbv7" "beq.w 16")
  let (_, thumbBranchTaken) ← executeEffect thumbBranchInsn [(armZ, .bits (BitVec.ofNat 1 1))]
  assertJump "LLVM lifted Thumb BEQ taken" 16 thumbBranchTaken
  assertEqual "LLVM Thumb branch metadata" (some 16) thumbBranchInsn.target
  let (_, thumbBranchNotTaken) ← executeEffect thumbBranchInsn [(armZ, .bits (BitVec.ofNat 1 0))]
  assertNormal "LLVM lifted Thumb BEQ not taken" thumbBranchNotTaken
  let riscvSltInsn ← decodeRISCV (← LLVM.assemble "riscv64" "slt a0, a1, a2")
  let riscvSltState ← execute riscvSltInsn [(reg "X10", .bits (BitVec.ofNat 64 0)),
    (reg "X11", .bits (BitVec.ofNat 64 0xffffffffffffffff)), (reg "X12", .bits (BitVec.ofNat 64 1))]
  assertReg "LLVM lifted RISC-V SLT" "X10" 1 riscvSltState
  let riscvSltuInsn ← decodeRISCV (← LLVM.assemble "riscv64" "sltu a0, a1, a2")
  let riscvSltuState ← execute riscvSltuInsn [(reg "X10", .bits (BitVec.ofNat 64 0)),
    (reg "X11", .bits (BitVec.ofNat 64 0xffffffffffffffff)), (reg "X12", .bits (BitVec.ofNat 64 1))]
  assertReg "LLVM lifted RISC-V SLTU" "X10" 0 riscvSltuState
  let powerpcRecordInsn ← decodePowerPC (← LLVM.assemble "powerpc64le" "add. 3, 3, 3")
  let powerpcRecordState ← execute powerpcRecordInsn [(reg "R3", .bits (BitVec.ofNat 64 0xffffffffffffffff)),
    (⟨"SO", .imm 1, 0, false⟩, .bits (BitVec.ofNat 1 0))]
  assertReg "LLVM lifted PowerPC record result" "R3" 0xfffffffffffffffe powerpcRecordState
  assertFlag "LLVM lifted PowerPC record LT" "CR0LT" 1 powerpcRecordState
  assertFlag "LLVM lifted PowerPC record GT" "CR0GT" 0 powerpcRecordState
  assertFlag "LLVM lifted PowerPC record EQ" "CR0EQ" 0 powerpcRecordState
  assertFlag "LLVM lifted PowerPC record UN" "CR0UN" 0 powerpcRecordState
  let armByteStoreInsn ← decodeARM32 (← LLVM.assemble "armv7" "strb r0, [r1, #0]")
  let armByteStoreState ← execute armByteStoreInsn [(⟨"R0", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x89abcdef)),
    (⟨"R1", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1000)), (armMemVar, .memory armMemory)]
  match Bil.lookup armByteStoreState.env armMemVar with
  | .ok (@Value.memory 32 updated) =>
    assertEqual "LLVM lifted ARM32 byte store" 0xef
      (Memory.read updated (BitVec.ofNat 32 0x1000) .little 1).toNat
  | .ok _ => throw <| IO.userError "ARM32 memory is not mapped"
  | .error error => throw <| IO.userError error
  let x86Add32Insn ← decodeX8632 (← LLVM.assemble "i386" "addl $1, %eax")
  let x86Add32State ← execute x86Add32Insn [(⟨"EAX", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 2))]
  assertReg32 "LLVM lifted x86-32 ADD" "EAX" 3 x86Add32State
  let x86Mov32Insn ← decodeX8632 (← LLVM.assemble "i386" "movl $-1, %eax")
  let x86Mov32State ← execute x86Mov32Insn
  assertReg32 "LLVM lifted x86-32 MOV" "EAX" 0xffffffff x86Mov32State
  let x86StackMemory ← match Memory.write (Memory.empty 32) (BitVec.ofNat 32 0x1000)
    (BitVec.ofNat 32 0x5678) .little 4 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  let x86Push32Insn ← decodeX8632 (← LLVM.assemble "i386" "pushl %eax")
  let x86Push32State ← execute x86Push32Insn [(⟨"EAX", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x12345678)),
    (⟨"ESP", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1000)), (armMemVar, .memory (Memory.empty 32))]
  assertReg32 "LLVM lifted x86-32 PUSH stack pointer" "ESP" 0xffc x86Push32State
  match Bil.lookup x86Push32State.env armMemVar with
  | .ok (@Value.memory 32 updated) =>
    assertEqual "LLVM lifted x86-32 PUSH value" 0x12345678
      (Memory.read updated (BitVec.ofNat 32 0xffc) .little 4).toNat
  | .ok _ => throw <| IO.userError "x86-32 memory is not mapped"
  | .error error => throw <| IO.userError error
  let x86Pop32Insn ← decodeX8632 (← LLVM.assemble "i386" "popl %ebx")
  let x86Pop32State ← execute x86Pop32Insn [(⟨"ESP", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1000)),
    (armMemVar, .memory x86StackMemory)]
  assertReg32 "LLVM lifted x86-32 POP destination" "EBX" 0x5678 x86Pop32State
  assertReg32 "LLVM lifted x86-32 POP stack pointer" "ESP" 0x1004 x86Pop32State
  let x86Call32Insn ← decodeX8632 (ByteArray.mk #[0xe8, 0, 0, 0, 0])
  let (x86Call32State, x86Call32Effect) ← executeEffect x86Call32Insn
    [(⟨"ESP", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1000)), (armMemVar, .memory (Memory.empty 32))]
  assertReg32 "LLVM lifted x86-32 CALL stack pointer" "ESP" 0xffc x86Call32State
  assertJump "LLVM lifted x86-32 CALL target" 5 x86Call32Effect
  match Bil.lookup x86Call32State.env armMemVar with
  | .ok (@Value.memory 32 updated) =>
    assertEqual "LLVM lifted x86-32 CALL return address" 5
      (Memory.read updated (BitVec.ofNat 32 0xffc) .little 4).toNat
  | .ok _ => throw <| IO.userError "x86-32 memory is not mapped"
  | .error error => throw <| IO.userError error
  let x86Ret32Insn ← decodeX8632 (ByteArray.mk #[0xc3])
  let (x86Ret32State, x86Ret32Effect) ← executeEffect x86Ret32Insn
    [(⟨"ESP", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1000)), (armMemVar, .memory x86StackMemory)]
  assertReg32 "LLVM lifted x86-32 RET stack pointer" "ESP" 0x1004 x86Ret32State
  assertJump "LLVM lifted x86-32 RET target" 0x5678 x86Ret32Effect
  let x86Jcc32Insn ← decodeX8632 (ByteArray.mk #[0x74, 0])
  let x86Z32 : Bap.Var := ⟨"ZF", .imm 1, 0, false⟩
  let (_, x86Jcc32Taken) ← executeEffect x86Jcc32Insn [(x86Z32, .bits (BitVec.ofNat 1 1))]
  assertJump "LLVM lifted x86-32 JCC taken" 2 x86Jcc32Taken
  assertEqual "LLVM x86-32 JCC metadata" (some 2) x86Jcc32Insn.target
  let (_, x86Jcc32NotTaken) ← executeEffect x86Jcc32Insn [(x86Z32, .bits (BitVec.ofNat 1 0))]
  assertNormal "LLVM lifted x86-32 JCC not taken" x86Jcc32NotTaken
  let riscv32AddInsn ← decodeRISCV32 (← LLVM.assemble "riscv32" "addi a0, a0, 1")
  let riscv32AddState ← execute riscv32AddInsn [(⟨"X10", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 2))]
  assertReg32 "LLVM lifted RISC-V 32 ADDI" "X10" 3 riscv32AddState
  let riscv32LoadInsn ← decodeRISCV32 (← LLVM.assemble "riscv32" "lw a0, 4(a1)")
  let riscv32LoadState ← execute riscv32LoadInsn [(⟨"X10", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0)),
    (⟨"X11", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1000)), (armMemVar, .memory armMemory)]
  assertReg32 "LLVM lifted RISC-V 32 LW" "X10" 0x12345678 riscv32LoadState
  let riscv32StoreInsn ← decodeRISCV32 (← LLVM.assemble "riscv32" "sw a0, 4(a1)")
  let riscv32StoreState ← execute riscv32StoreInsn [(⟨"X10", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x89abcdef)),
    (⟨"X11", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1000)), (armMemVar, .memory armMemory)]
  match Bil.lookup riscv32StoreState.env armMemVar with
  | .ok (@Value.memory 32 updated) =>
    assertEqual "LLVM lifted RISC-V 32 SW" 0x89abcdef
      (Memory.read updated (BitVec.ofNat 32 0x1004) .little 4).toNat
  | .ok _ => throw <| IO.userError "RISC-V 32 memory is not mapped"
  | .error error => throw <| IO.userError error
  let riscv32BranchInsn ← decodeRISCV32 (← LLVM.assemble "riscv32" "beq a0, a1, 0")
  let (_, riscv32BranchTaken) ← executeEffect riscv32BranchInsn
    [(⟨"X10", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 1)), (⟨"X11", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 1))]
  assertJump "LLVM lifted RISC-V 32 BEQ taken" 0 riscv32BranchTaken
  let (_, riscv32BranchNotTaken) ← executeEffect riscv32BranchInsn
    [(⟨"X10", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 1)), (⟨"X11", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 2))]
  assertNormal "LLVM lifted RISC-V 32 BEQ not taken" riscv32BranchNotTaken
  let riscv32JalInsn ← decodeRISCV32 (← LLVM.assemble "riscv32" "jal ra, 0")
  let (riscv32JalState, riscv32JalEffect) ← executeEffect riscv32JalInsn
  assertReg32 "LLVM lifted RISC-V 32 JAL link" "X1" 4 riscv32JalState
  assertJump "LLVM lifted RISC-V 32 JAL target" 0 riscv32JalEffect
  let riscv32JalrInsn ← decodeRISCV32 (← LLVM.assemble "riscv32" "jalr ra, 0(a0)")
  let (riscv32JalrState, riscv32JalrEffect) ← executeEffect riscv32JalrInsn
    [(⟨"X10", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1235))]
  assertReg32 "LLVM lifted RISC-V 32 JALR link" "X1" 4 riscv32JalrState
  assertJump "LLVM lifted RISC-V 32 JALR target" 0x1234 riscv32JalrEffect
  let mips32AddInsn ← decodeMIPS32 (← LLVM.assemble "mips" "addiu $2, $2, 1")
  let mips32AddState ← execute mips32AddInsn [(⟨"R2", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 2))]
  assertReg32 "LLVM lifted MIPS 32 ADDIU" "R2" 3 mips32AddState
  let mips32SignState ← execute mips32AddInsn [(⟨"R2", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x7fffffff))]
  assertReg32 "LLVM lifted MIPS 32 sign extension" "R2" 0x80000000 mips32SignState
  let mips32Memory ← match Memory.write (Memory.empty 32) (BitVec.ofNat 32 0x1004)
    (BitVec.ofNat 32 0x12345678) .big 4 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  let mips32LoadInsn ← decodeMIPS32 (← LLVM.assemble "mips" "lw $2, 4($3)")
  let mips32LoadState ← execute mips32LoadInsn [(⟨"R2", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0)),
    (⟨"R3", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1000)), (armMemVar, .memory mips32Memory)]
  assertReg32 "LLVM lifted MIPS 32 big-endian LW" "R2" 0x12345678 mips32LoadState
  let mips32StoreInsn ← decodeMIPS32 (← LLVM.assemble "mips" "sw $2, 4($3)")
  let mips32StoreState ← execute mips32StoreInsn [(⟨"R2", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x89abcdef)),
    (⟨"R3", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1000)), (armMemVar, .memory mips32Memory)]
  match Bil.lookup mips32StoreState.env armMemVar with
  | .ok (@Value.memory 32 updated) =>
    assertEqual "LLVM lifted MIPS 32 big-endian SW" 0x89abcdef
      (Memory.read updated (BitVec.ofNat 32 0x1004) .big 4).toNat
  | .ok _ => throw <| IO.userError "MIPS 32 memory is not mapped"
  | .error error => throw <| IO.userError error
  let mips32BranchInsn ← decodeMIPS32 (ByteArray.mk #[0x10, 0x43, 0x00, 0x04])
  let (_, mips32BranchTaken) ← executeEffect mips32BranchInsn
    [(⟨"R2", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 1)), (⟨"R3", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 1))]
  assertJump "LLVM lifted MIPS 32 BEQ taken" 20 mips32BranchTaken
  let (_, mips32BranchNotTaken) ← executeEffect mips32BranchInsn
    [(⟨"R2", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 1)), (⟨"R3", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 2))]
  assertNormal "LLVM lifted MIPS 32 BEQ not taken" mips32BranchNotTaken
  let mips32ReturnInsn ← decodeMIPS32 (← LLVM.assemble "mips" "jr $31")
  let (_, mips32ReturnEffect) ← executeEffect mips32ReturnInsn
    [(⟨"R31", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1234))]
  assertJump "LLVM lifted MIPS 32 JR" 0x1234 mips32ReturnEffect
  let powerpc32AddInsn ← decodePowerPC32 (← LLVM.assemble "powerpc" "addi 3, 3, 1")
  let powerpc32AddState ← execute powerpc32AddInsn [(⟨"R3", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 2))]
  assertReg32 "LLVM lifted PowerPC 32 ADDI" "R3" 3 powerpc32AddState
  let powerpc32LoadInsn ← decodePowerPC32 (← LLVM.assemble "powerpc" "lwz 3, 4(4)")
  let powerpc32LoadState ← execute powerpc32LoadInsn [(⟨"R3", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0)),
    (⟨"R4", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1000)), (armMemVar, .memory mips32Memory)]
  assertReg32 "LLVM lifted PowerPC 32 LWZ" "R3" 0x12345678 powerpc32LoadState
  let powerpc32StoreInsn ← decodePowerPC32 (← LLVM.assemble "powerpc" "stw 3, 4(4)")
  let powerpc32StoreState ← execute powerpc32StoreInsn [(⟨"R3", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x89abcdef)),
    (⟨"R4", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1000)), (armMemVar, .memory mips32Memory)]
  match Bil.lookup powerpc32StoreState.env armMemVar with
  | .ok (@Value.memory 32 updated) =>
    assertEqual "LLVM lifted PowerPC 32 STW" 0x89abcdef
      (Memory.read updated (BitVec.ofNat 32 0x1004) .big 4).toNat
  | .ok _ => throw <| IO.userError "PowerPC 32 memory is not mapped"
  | .error error => throw <| IO.userError error
  let powerpc32BranchInsn ← decodePowerPC32 (← LLVM.assemble "powerpc" "b 16")
  let (_, powerpc32BranchEffect) ← executeEffect powerpc32BranchInsn
  assertJump "LLVM lifted PowerPC 32 B" 16 powerpc32BranchEffect
  assertEqual "LLVM PowerPC 32 branch metadata" (some 16) powerpc32BranchInsn.target
  let powerpc32LinkInsn ← decodePowerPC32 (← LLVM.assemble "powerpc" "bl 16")
  let (powerpc32LinkState, powerpc32LinkEffect) ← executeEffect powerpc32LinkInsn
  assertReg32 "LLVM lifted PowerPC 32 BL link" "LR" 4 powerpc32LinkState
  assertJump "LLVM lifted PowerPC 32 BL target" 16 powerpc32LinkEffect
  let powerpc32ReturnInsn ← decodePowerPC32 (← LLVM.assemble "powerpc" "blr")
  let (_, powerpc32ReturnEffect) ← executeEffect powerpc32ReturnInsn
    [(⟨"LR", .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 0x1237))]
  assertJump "LLVM lifted PowerPC 32 BLR" 0x1234 powerpc32ReturnEffect
  let _ ← expectRoundTrip "LLVM SystemZ" "systemz" "a %r2, 0(%r3)" [0x5a, 0x20, 0x30, 0x00]
  let branch ← LLVM.disassemble "aarch64" (ByteArray.mk #[0x00, 0x00, 0x00, 0x14])
  assertEqual "LLVM unconditional branch flag" true (branch.flags &&& 64 != 0)
  let ret ← LLVM.disassemble "x86_64" (ByteArray.mk #[0xc3])
  assertEqual "LLVM return flag" true (ret.flags &&& 1 != 0)

  let duplicates : Primus.Semantics.Environment := .ofGlobals [
    ("operation", .callable (.primitive "+")),
    ("operation", .callable (.primitive "-"))
  ]
  match duplicates.operations.get? "operation" with
  | some (.primitive "+") => assertTrue "Primus hash index preserves shadowing" true
  | _ => throw <| IO.userError "Primus hash index changed definition order"
  let indexed := x86Environment
  assertTrue "Primus opcode uses the typed hash index" (indexed.operations.get? "MOV64ri").isSome
  let indexedBytes ← LLVM.assemble "x86_64" "movq $42, %rax"
  let indexedFirst ← decodeX86 indexedBytes
  let indexedSecond ← decodeX86 indexedBytes
  assertEqual "reused Primus environment produces identical BIL"
    (Bil.Wire.renderProgram indexedFirst.bil) (Bil.Wire.renderProgram indexedSecond.bil)

  let mcBytes ← LLVM.assemble "riscv64" "addi a0, a1, 2"
  let mcDecoded ← LLVM.disassembleMC "riscv64" mcBytes
  let expectedOpcode ← LLVM.opcodeId "riscv64" "ADDI"
  let actualOpcode := LLVM.mcOpcode mcDecoded.instruction
  assertEqual "MCInst uses a numeric opcode" expectedOpcode actualOpcode
  assertTrue "MCInst opcode has numeric Primus semantics" (riscvEnvironment.opcodes.get? actualOpcode).isSome
  match riscvEnvironment.opcodes.get? actualOpcode with
  | some (.compiled ..) => assertTrue "RISC-V ADDI uses compiled Primus semantics" true
  | _ => throw <| IO.userError "RISC-V ADDI did not compile to Lean"
  let mcOperands ← LLVM.mcOperands mcDecoded.instruction
  match mcOperands with
  | [.reg dst, .reg src, .imm 2] =>
    let expectedDst ← LLVM.registerId "riscv64" "X10"
    let expectedSrc ← LLVM.registerId "riscv64" "X11"
    assertEqual "MCInst uses numeric register operands" (expectedDst, expectedSrc) (dst, src)
  | _ => throw <| IO.userError "unexpected RISC-V MCInst operands"

  let mc32Bytes ← LLVM.assemble "riscv32" "addi a0, a1, 2"
  let mc32Decoded ← LLVM.disassembleMC "riscv32" mc32Bytes
  let expected32Opcode ← LLVM.opcodeId "riscv32" "ADDI"
  let actual32Opcode := LLVM.mcOpcode mc32Decoded.instruction
  assertEqual "RISC-V 32 uses a numeric opcode" expected32Opcode actual32Opcode
  match riscv32Environment.opcodes.get? actual32Opcode with
  | some (.compiled ..) => assertTrue "RISC-V 32 ADDI uses compiled Primus semantics" true
  | _ => throw <| IO.userError "RISC-V 32 ADDI did not compile to Lean"

  let armMCBytes ← LLVM.assemble "aarch64" "add x0, x0, x1"
  let armMCDecoded ← LLVM.disassembleMC "aarch64" armMCBytes
  let armOpcode := LLVM.mcOpcode armMCDecoded.instruction
  match aarch64Environment.opcodes.get? armOpcode with
  | some (.compiled ..) => assertTrue "AArch64 ADD uses compiled MCInst semantics" true
  | _ => throw <| IO.userError "AArch64 ADD did not compile to Lean"

end Bap.Tests.LLVM
