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

private def testRiscvRem : IO Unit := do
  let riscv ← Target.LLVMLift.riscvEnvironment
  -- rem a0, a1, a2 truncates: the result takes the sign of the dividend.
  let insn ← Target.LLVMLift.decodeRISCVWith riscv 0 0 (ByteArray.mk #[0x33, 0xe5, 0xc5, 0x02])
  -- c.addi a0, 1 is a two-byte compressed instruction.
  let compressed ← Target.LLVMLift.decodeRISCVWith riscv 0 0 (ByteArray.mk #[0x05, 0x05])
  assertEqual "RISC-V compressed instruction size" 2 compressed.next
  let reg (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩
  let cases : List (Int × Int × Int) := [(-7, 3, -1), (7, -3, 1), (-7, -3, -1), (7, 3, 1), (-7, 0, -7)]
  for (dividend, divisor, expected) in cases do
    let env : Bil.Env := [
      (reg "X11", .bits (BitVec.ofInt 64 dividend)),
      (reg "X12", .bits (BitVec.ofInt 64 divisor))]
    let state ← execute insn env
    match Bil.lookup state.env (reg "X10") with
    | .ok (.bits (width := 64) value) =>
      if value = BitVec.ofInt 64 expected then
        IO.println s!"ok: RISC-V rem {dividend} {divisor}"
      else
        throw <| IO.userError s!"RISC-V rem {dividend} {divisor}: {value.toInt}"
    | _ => throw <| IO.userError "RISC-V rem result missing"

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

private def bytes (values : List Nat) : ByteArray := ByteArray.mk (values.map UInt8.ofNat).toArray

private def bit (name : String) (value : Nat) : Bap.Var × Value :=
  (⟨name, .imm 1, 0, false⟩, .bits (BitVec.ofNat 1 value))

private def word (name : String) (value : Nat) : Bap.Var × Value :=
  (reg name, .bits (BitVec.ofNat 64 value))

private def word32 (name : String) (value : Nat) : Bap.Var × Value :=
  (⟨name, .imm 32, 0, false⟩, .bits (BitVec.ofNat 32 value))

private def assertControl (label : String) (flow : Disasm.Flow) (target : Option Nat)
    (insn : Disasm.Insn) : IO Unit := do
  assertTrue s!"{label} flow" (insn.flow == flow)
  assertEqual s!"{label} target" target insn.target

private def thumbMemVar : Bap.Var := ⟨"mem", .mem 32 8, 0, false⟩

/-- A 32-bit stack at 0x1000 that holds the given words. -/
private def thumbStack (values : List Nat) : IO Bil.Env := do
  let mut memory : Memory 32 := Memory.empty 32
  for (index, value) in (List.range values.length).zip values do
    match Memory.write memory (BitVec.ofNat 32 (0x1000 + 4 * index)) (BitVec.ofNat 32 value) .little 4 with
    | .ok updated => memory := updated
    | .error error => throw <| IO.userError error
  pure [(thumbMemVar, .memory memory), word32 "SP" 0x1000]

/-- Control flow at a non-zero address, on encodings decoded by the linked LLVM. -/
private def testBranches : IO Unit := do
  let at0 := 0x2000
  let arm ← Target.LLVMLift.arm32Environment
  let decodeARM (address : Nat) (values : List Nat) :=
    Target.LLVMLift.decodeARM32With arm address address (bytes values)
  -- A32 immediates are relative to the pc, which is the address plus 8
  for (label, flow, values, target) in [
      ("Bcc", Disasm.Flow.conditionalJump, [0x04, 0, 0, 0x0a], at0 + 8 + 16),
      ("Bcc backward", .conditionalJump, [0xfc, 0xff, 0xff, 0x0a], at0 + 8 - 16),
      ("B self", .jump, [0xfe, 0xff, 0xff, 0xea], at0),
      ("BL", .call, [0x04, 0, 0, 0xeb], at0 + 8 + 16),
      ("BLX", .call, [0x04, 0, 0, 0xfa], at0 + 8 + 16)] do
    let insn ← decodeARM at0 values
    assertControl s!"ARM32 {label}" flow (some target) insn
    let (_, effect) ← executeEffect insn [bit "ZF" 1]
    assertJump s!"ARM32 {label} lifted target" target effect
  assertEqual "ARM32 target moves with the address" (some (0x3000 + 8 + 16))
    (← decodeARM 0x3000 [0x04, 0, 0, 0x0a]).target
  let thumb ← Target.LLVMLift.thumbEnvironment
  let decodeThumb (address : Nat) (values : List Nat) :=
    Target.LLVMLift.decodeThumbWith thumb address address (bytes values)
  -- T32 immediates are relative to the pc, which is the address plus 4
  for (label, flow, values, target) in [
      ("tBcc", Disasm.Flow.conditionalJump, [0x02, 0xd0], at0 + 4 + 4),
      ("tB", .jump, [0x02, 0xe0], at0 + 4 + 4),
      ("t2Bcc", .conditionalJump, [0x00, 0xf0, 0x08, 0x80], at0 + 4 + 16),
      ("t2B", .jump, [0x00, 0xf0, 0x08, 0xb8], at0 + 4 + 16),
      ("tBL", .call, [0x00, 0xf0, 0x08, 0xf8], at0 + 4 + 16)] do
    let insn ← decodeThumb at0 values
    assertControl s!"Thumb {label}" flow (some target) insn
    let (_, effect) ← executeEffect insn [bit "ZF" 1]
    assertJump s!"Thumb {label} lifted target" target effect
  let thumbCbz ← decodeThumb at0 [0x1a, 0xb1]
  assertControl "Thumb tCBZ" .conditionalJump (some (at0 + 4 + 6)) thumbCbz
  let (_, thumbCbzEffect) ← executeEffect thumbCbz [word32 "R2" 0]
  assertJump "Thumb tCBZ taken" (at0 + 4 + 6) thumbCbzEffect
  let (_, thumbCbzNot) ← executeEffect thumbCbz [word32 "R2" 1]
  assertNormal "Thumb tCBZ not taken" thumbCbzNot
  let thumbBl ← decodeThumb at0 [0x00, 0xf0, 0x08, 0xf8]
  let (thumbBlState, _) ← executeEffect thumbBl
  assertReg32 "Thumb tBL link keeps the T32 state" "LR" (at0 + 4 + 1) thumbBlState
  -- BLX computes from the word-aligned pc
  let thumbBlx ← decodeThumb (at0 + 2) [0x00, 0xf0, 0x08, 0xe8]
  assertControl "Thumb tBLXi" .call (some (at0 + 4 + 16)) thumbBlx
  let (_, thumbBlxEffect) ← executeEffect thumbBlx
  assertJump "Thumb tBLXi lifted target" (at0 + 4 + 16) thumbBlxEffect
  let thumbBx ← decodeThumb at0 [0x70, 0x47]
  assertControl "Thumb tBX" .indirectJump none thumbBx
  let (_, thumbBxEffect) ← executeEffect thumbBx [word32 "LR" 0x1235]
  assertJump "Thumb tBX clears the state bit" 0x1234 thumbBxEffect
  let ppc ← Target.LLVMLift.powerpcEnvironment
  let decodePPC (values : List Nat) :=
    Target.LLVMLift.decodePowerPCWith ppc at0 at0 (bytes values)
  -- the BO and BI operands of a conditional branch come before its displacement
  let ppcCond ← decodePPC [0x08, 0, 0x82, 0x41]
  assertControl "PowerPC conditional" .conditionalJump (some (at0 + 8)) ppcCond
  let (_, ppcCondEffect) ← executeEffect ppcCond [bit "CR0EQ" 1]
  assertJump "PowerPC conditional lifted target" (at0 + 8) ppcCondEffect
  assertControl "PowerPC b" .jump (some (at0 + 16)) (← decodePPC [0x10, 0, 0, 0x48])
  assertControl "PowerPC ba" .jump (some 16) (← decodePPC [0x12, 0, 0, 0x48])
  assertControl "PowerPC bl" .call (some (at0 + 16)) (← decodePPC [0x11, 0, 0, 0x48])
  assertControl "PowerPC bca" .conditionalJump (some 16) (← decodePPC [0x12, 0, 0x82, 0x41])
  assertControl "PowerPC bdnz" .conditionalJump (some (at0 + 16)) (← decodePPC [0x10, 0, 0, 0x42])
  assertEqual "PowerPC bclr has no static target" none (← decodePPC [0x20, 0, 0x82, 0x4d]).target
  assertEqual "PowerPC bcctr has no static target" none (← decodePPC [0x20, 0x04, 0x82, 0x4d]).target
  let ppc32 ← Target.LLVMLift.powerpc32Environment
  let ppc32Cond ← Target.LLVMLift.decodePowerPC32With ppc32 at0 at0 (bytes [0x41, 0x82, 0, 0x08])
  assertControl "PowerPC 32 conditional" .conditionalJump (some (at0 + 8)) ppc32Cond
  let mips ← Target.LLVMLift.mipsEnvironment
  let decodeMIPS (address : Nat) (values : List Nat) :=
    Target.LLVMLift.decodeMIPSWith mips address address (bytes values)
  -- the displacement of LLVM counts from the branch, and the region is of the delay slot
  for (label, flow, values, target) in [
      ("bgtz", Disasm.Flow.conditionalJump, [0x1c, 0x40, 0, 0x03], at0 + 16),
      ("blez", .conditionalJump, [0x18, 0x40, 0, 0x03], at0 + 16),
      ("bltz", .conditionalJump, [0x04, 0x40, 0, 0x03], at0 + 16),
      ("bgez", .conditionalJump, [0x04, 0x41, 0, 0x03], at0 + 16),
      ("beql", .conditionalJump, [0x50, 0x40, 0, 0x03], at0 + 16),
      ("bne", .conditionalJump, [0x14, 0x40, 0, 0x03], at0 + 16),
      ("bal", .call, [0x04, 0x11, 0, 0x03], at0 + 16),
      ("j", .jump, [0x08, 0, 0x10, 0], 0x4000),
      ("jal", .call, [0x0c, 0, 0x10, 0], 0x4000)] do
    assertControl s!"MIPS {label}" flow (some target) (← decodeMIPS at0 values)
  let mipsJ ← decodeMIPS 0x1ffffffc [0x08, 0, 0x10, 0]
  assertEqual "MIPS j uses the region of the delay slot" (some 0x20004000) mipsJ.target
  let (_, mipsJEffect) ← executeEffect mipsJ
  assertJump "MIPS j lifted target" 0x20004000 mipsJEffect
  let (_, mipsBgtzEffect) ← executeEffect (← decodeMIPS at0 [0x1c, 0x40, 0, 0x03]) [word "R2" 1]
  assertJump "MIPS bgtz lifted target" (at0 + 16) mipsBgtzEffect
  assertEqual "MIPS jr has no static target" none (← decodeMIPS at0 [0x03, 0xe0, 0, 0x08]).target
  let riscv ← Target.LLVMLift.riscvEnvironment
  let decodeRISCV (values : List Nat) :=
    Target.LLVMLift.decodeRISCVWith riscv at0 at0 (bytes values)
  -- LLVM has no flags for JAL and JALR
  assertControl "RISC-V j" .jump (some (at0 + 16)) (← decodeRISCV [0x6f, 0, 0, 0x01])
  assertControl "RISC-V jal" .call (some (at0 + 16)) (← decodeRISCV [0xef, 0, 0, 0x01])
  assertControl "RISC-V ret" .ret none (← decodeRISCV [0x67, 0x80, 0, 0])
  assertControl "RISC-V jr" .indirectJump none (← decodeRISCV [0x67, 0x80, 0x05, 0])
  assertControl "RISC-V jalr" .call none (← decodeRISCV [0xe7, 0x80, 0x05, 0])
  assertControl "RISC-V beq" .conditionalJump (some (at0 + 16)) (← decodeRISCV [0x63, 0x08, 0xb5, 0])
  let riscv32 ← Target.LLVMLift.riscv32Environment
  assertControl "RISC-V 32 j" .jump (some (at0 + 16))
    (← Target.LLVMLift.decodeRISCV32With riscv32 at0 at0 (bytes [0x6f, 0, 0, 0x01]))
  let aarch64 ← Target.LLVMLift.aarch64Environment
  let decodeAArch64 (values : List Nat) :=
    Target.LLVMLift.decodeAArch64With aarch64 at0 at0 (bytes values)
  assertControl "AArch64 bl" .call (some (at0 + 16)) (← decodeAArch64 [0x04, 0, 0, 0x94])
  assertControl "AArch64 blr" .call none (← decodeAArch64 [0x00, 0, 0x3f, 0xd6])
  assertControl "AArch64 tbz" .conditionalJump (some (at0 + 16)) (← decodeAArch64 [0x80, 0, 0, 0x36])
  let x86 ← Target.LLVMLift.x86Environment
  let decodeX86 (values : List Nat) := Target.LLVMLift.decodeX86With x86 at0 at0 (bytes values)
  assertControl "x86 jrcxz" .conditionalJump (some (at0 + 4)) (← decodeX86 [0xe3, 0x02])
  assertControl "x86 loop" .conditionalJump (some (at0 + 4)) (← decodeX86 [0xe2, 0x02])
  let x8632 ← Target.LLVMLift.x8632Environment
  assertControl "x86-32 jecxz" .conditionalJump (some (at0 + 4))
    (← Target.LLVMLift.decodeX8632With x8632 at0 at0 (bytes [0xe3, 0x02]))

/-- Writes through the partial registers keep the bits that they do not cover, except that the
writes of 32 bits clear the upper half in the 64-bit mode. -/
private def testPartialRegisters : IO Unit := do
  let x86 ← Target.LLVMLift.x86Environment
  let decodeX86 (values : List Nat) := Target.LLVMLift.decodeX86With x86 0 0 (bytes values)
  let full := 0x1122334455667788
  for (label, values, base, expected) in [
      ("R8D", [0x41, 0xb8, 1, 0, 0, 0], "R8", 1),
      ("R15D", [0x41, 0xbf, 1, 0, 0, 0], "R15", 1),
      ("EAX", [0xb8, 1, 0, 0, 0], "RAX", 1),
      ("R8W", [0x66, 0x41, 0xb8, 1, 0], "R8", 0x1122334455660001),
      ("R15W", [0x66, 0x41, 0xbf, 1, 0], "R15", 0x1122334455660001),
      ("AX", [0x66, 0xb8, 1, 0], "RAX", 0x1122334455660001),
      ("R8B", [0x41, 0xb0, 1], "R8", 0x1122334455667701),
      ("R15B", [0x41, 0xb7, 1], "R15", 0x1122334455667701),
      ("AL", [0xb0, 1], "RAX", 0x1122334455667701),
      ("BL", [0xb3, 1], "RBX", 0x1122334455667701),
      ("SIL", [0x40, 0xb6, 1], "RSI", 0x1122334455667701),
      ("DIL", [0x40, 0xb7, 1], "RDI", 0x1122334455667701),
      ("SPL", [0x40, 0xb4, 1], "RSP", 0x1122334455667701),
      ("BPL", [0x40, 0xb5, 1], "RBP", 0x1122334455667701),
      ("AH", [0xb4, 1], "RAX", 0x1122334455660188),
      ("BH", [0xb7, 1], "RBX", 0x1122334455660188),
      ("CH", [0xb5, 1], "RCX", 0x1122334455660188),
      ("DH", [0xb6, 1], "RDX", 0x1122334455660188)] do
    let state ← execute (← decodeX86 values) [word base full]
    assertReg s!"x86 write of {label}" base expected state
  -- mov bl, ah
  assertReg "x86 read of AH" "RBX" 0x77
    (← execute (← decodeX86 [0x88, 0xe3]) [word "RAX" 0x7700, word "RBX" 0])
  -- mov al, r9b
  assertReg "x86 read of R9B" "RAX" 0x42
    (← execute (← decodeX86 [0x44, 0x88, 0xc8]) [word "R9" 0xff42, word "RAX" 0])
  -- mov ax, r9w
  assertReg "x86 read of R9W" "RAX" 0xff42
    (← execute (← decodeX86 [0x66, 0x44, 0x89, 0xc8]) [word "R9" 0x1ff42, word "RAX" 0])
  -- mov r9d, eax
  assertReg "x86 read of EAX to R9D" "R9" 0x89abcdef
    (← execute (← decodeX86 [0x41, 0x89, 0xc1]) [word "RAX" 0x1234567889abcdef, word "R9" 1])
  -- add al, 1 keeps the upper bits and sets the flags
  let addAl ← execute (← decodeX86 [0x04, 0x01]) [word "RAX" 0x1ff]
  assertReg "x86 ADD8i8 result" "RAX" 0x100 addAl
  assertFlag "x86 ADD8i8 carry" "CF" 1 addAl
  let x8632 ← Target.LLVMLift.x8632Environment
  let decodeX8632 (values : List Nat) := Target.LLVMLift.decodeX8632With x8632 0 0 (bytes values)
  for (label, values, base, expected) in [
      ("AX", [0x66, 0xb8, 1, 0], "EAX", 0x55660001),
      ("AL", [0xb0, 1], "EAX", 0x55667701),
      ("AH", [0xb4, 1], "EAX", 0x55660188),
      ("BH", [0xb7, 1], "EBX", 0x55660188),
      ("SI", [0x66, 0xbe, 1, 0], "ESI", 0x55660001)] do
    let state ← execute (← decodeX8632 values) [word32 base 0x55667788]
    assertReg32 s!"x86-32 write of {label}" base expected state
  let aarch64 ← Target.LLVMLift.aarch64Environment
  let decodeAArch64 (values : List Nat) := Target.LLVMLift.decodeAArch64With aarch64 0 0 (bytes values)
  -- add w0, wsp, 0 reads the low half of SP
  assertReg "AArch64 read of WSP" "X0" 0x89abcdef
    (← execute (← decodeAArch64 [0xe0, 0x03, 0x00, 0x11]) [word "SP" 0x1234567889abcdef, word "X0" 0])
  -- add wsp, w2, 0 writes the low half of SP and clears the upper half
  assertReg "AArch64 write of WSP" "SP" 0x89abcdef
    (← execute (← decodeAArch64 [0x5f, 0x00, 0x00, 0x11])
      [word "SP" 0x1234567800000000, word "X2" 0x89abcdef])
  -- orr w0, wzr, w1 reads the zero register at the width of the operation
  assertReg "AArch64 read of WZR" "X0" 5
    (← execute (← decodeAArch64 [0xe0, 0x03, 0x01, 0x2a]) [word "X1" 5, word "X0" 0])
  let mips ← Target.LLVMLift.mipsEnvironment
  let decodeMIPS (values : List Nat) := Target.LLVMLift.decodeMIPSWith mips 0 0 (bytes values)
  -- LLVM names the 64-bit views of the general purpose registers with a suffix
  assertReg "MIPS daddu of the 64-bit views" "R2" 7
    (← execute (← decodeMIPS [0x00, 0x64, 0x10, 0x2d]) [word "R3" 3, word "R4" 4])
  assertReg "MIPS daddu of ZERO_64" "R2" 3
    (← execute (← decodeMIPS [0x00, 0x60, 0x10, 0x2d]) [word "R3" 3])

/-- Writes to PC that LLVM doesn't flag, on encodings decoded by the linked LLVM. -/
private def testPcWrites : IO Unit := do
  let arm ← Target.LLVMLift.arm32Environment
  let decodeARM (values : List Nat) := Target.LLVMLift.decodeARM32With arm 0x2000 0x2000 (bytes values)
  for (label, values) in [
      ("mov pc, r1", [0x01, 0xf0, 0xa0, 0xe1]),
      ("ldr pc, [sp], 4", [0x04, 0xf0, 0x9d, 0xe4]),
      ("ldr pc, [r0]", [0x00, 0xf0, 0x90, 0xe5]),
      ("ldm r0, {pc}", [0x00, 0x80, 0x90, 0xe8]),
      ("add pc, r0, r1", [0x01, 0xf0, 0x80, 0xe0])] do
    let insn ← decodeARM values
    assertTrue s!"ARM32 {label} is indirect" (insn.flow == .indirectJump)
    assertEqual s!"ARM32 {label} has no successors" [] insn.successors
  assertTrue "ARM32 pop pc does not fall through"
    (!(← decodeARM [0x00, 0x80, 0xbd, 0xe8]).fallsThrough)
  assertTrue "ARM32 mov pc, lr does not fall through"
    (!(← decodeARM [0x0e, 0xf0, 0xa0, 0xe1]).fallsThrough)
  for (label, values) in [
      ("moveq pc, lr", [0x0e, 0xf0, 0xa0, 0x01]),
      ("bxeq lr", [0x1e, 0xff, 0x2f, 0x01]),
      ("ldreq pc, [r0]", [0x00, 0xf0, 0x90, 0x05]),
      ("ldmeq r0, {pc}", [0x00, 0x80, 0x90, 0x08])] do
    assertTrue s!"ARM32 {label} is conditional" ((← decodeARM values).flow == .conditionalJump)
  let (armPopState, armPopEffect) ← executeEffect (← decodeARM [0x03, 0x80, 0xbd, 0xe8])
    (← thumbStack [0x11, 0x22, 0x1235])
  assertReg32 "ARM32 pop {r0, r1, pc} first" "R0" 0x11 armPopState
  assertReg32 "ARM32 pop {r0, r1, pc} second" "R1" 0x22 armPopState
  assertReg32 "ARM32 pop {r0, r1, pc} sp" "SP" 0x100c armPopState
  assertJump "ARM32 pop {r0, r1, pc} jumps" 0x1234 armPopEffect
  let armPushed ← execute (← decodeARM [0x03, 0x40, 0x2d, 0xe9])
    ((← thumbStack []) ++ [word32 "R0" 1, word32 "R1" 2, word32 "LR" 3])
  assertReg32 "ARM32 push {r0, r1, lr} sp" "SP" 0xff4 armPushed
  let armReload ← execute (← decodeARM [0x07, 0x00, 0xbd, 0xe8]) armPushed.env
  assertReg32 "ARM32 pop after push, the lowest register at the lowest address" "R0" 1 armReload
  assertReg32 "ARM32 pop after push, third" "R2" 3 armReload
  -- a loaded base keeps the loaded value
  let loadedBase ← execute (← decodeARM [0x03, 0x00, 0x90, 0xe8])
    ((← thumbStack [0x11, 0x22]) ++ [word32 "R0" 0x1000])
  assertReg32 "ARM32 ldm r0, {r0, r1} loads the base" "R0" 0x11 loadedBase
  assertReg32 "ARM32 ldm r0, {r0, r1} uses the old base" "R1" 0x22 loadedBase
  for (label, values) in [
      ("mov r0, r1", [0x01, 0x00, 0xa0, 0xe1]),
      ("str pc, [sp]", [0x00, 0xf0, 0x8d, 0xe5]),
      ("cmp pc, 0", [0x00, 0x00, 0x5f, 0xe3]),
      ("ldr r0, [sp]", [0x00, 0x00, 0x9d, 0xe5])] do
    assertTrue s!"ARM32 {label} is normal" ((← decodeARM values).flow == .normal)
  let thumb ← Target.LLVMLift.thumbEnvironment
  let decodeThumb (values : List Nat) :=
    Target.LLVMLift.decodeThumbWith thumb 0x2000 0x2000 (bytes values)
  for (label, values) in [
      ("mov pc, lr", [0xf7, 0x46]),
      ("add pc, r0", [0x87, 0x44]),
      ("ldr pc, [pc, 4]", [0xdf, 0xf8, 0x04, 0xf0]),
      ("ldr.w pc, [r0]", [0xd0, 0xf8, 0x00, 0xf0]),
      ("pop.w {pc}", [0xbd, 0xe8, 0x00, 0x80]),
      ("pop {r0, pc}", [0x01, 0xbd])] do
    let insn ← decodeThumb values
    assertTrue s!"Thumb {label} does not fall through" (!insn.fallsThrough)
    assertEqual s!"Thumb {label} has no successors" [] insn.successors
  assertTrue "Thumb pop {r0} is normal" ((← decodeThumb [0x01, 0xbc]).flow == .normal)
  let (popState, popEffect) ← executeEffect (← decodeThumb [0x01, 0xbd]) (← thumbStack [0x11, 0x1235])
  assertReg32 "Thumb pop {r0, pc} loads r0" "R0" 0x11 popState
  assertReg32 "Thumb pop {r0, pc} moves sp" "SP" 0x1008 popState
  assertJump "Thumb pop {r0, pc} jumps" 0x1234 popEffect

/-- Targets wrap around the address space, as they do in the lifted program. -/
private def testWrappedTargets : IO Unit := do
  let top64 := 2 ^ 64
  let top32 := 2 ^ 32
  let check (label : String) (target : Nat) (insn : Disasm.Insn) : IO Unit := do
    assertEqual s!"{label} target wraps" (some target) insn.target
  let ppc ← Target.LLVMLift.powerpcEnvironment
  let ppcBa ← Target.LLVMLift.decodePowerPCWith ppc 0x2000 0x2000 (bytes [0xf2, 0xff, 0xff, 0x4b])
  check "PowerPC negative ba" (top64 - 16) ppcBa
  let (_, ppcBaEffect) ← executeEffect ppcBa
  assertJump "PowerPC negative ba lifted target" (top64 - 16) ppcBaEffect
  check "PowerPC negative bca" (top64 - 16)
    (← Target.LLVMLift.decodePowerPCWith ppc 0x2000 0x2000 (bytes [0xf2, 0xff, 0x82, 0x41]))
  let ppc32 ← Target.LLVMLift.powerpc32Environment
  check "PowerPC 32 negative ba" (top32 - 16)
    (← Target.LLVMLift.decodePowerPC32With ppc32 0x2000 0x2000 (bytes [0x4b, 0xff, 0xff, 0xf2]))
  let x86 ← Target.LLVMLift.x86Environment
  let x86Jmp ← Target.LLVMLift.decodeX86With x86 0 0 (bytes [0xeb, 0xfb])
  check "x86 backward jmp" (top64 - 3) x86Jmp
  let (_, x86Effect) ← executeEffect x86Jmp
  assertJump "x86 backward jmp lifted target" (top64 - 3) x86Effect
  let x8632 ← Target.LLVMLift.x8632Environment
  check "x86-32 backward jmp" (top32 - 3)
    (← Target.LLVMLift.decodeX8632With x8632 0 0 (bytes [0xeb, 0xfb]))
  let arm ← Target.LLVMLift.arm32Environment
  let armB ← Target.LLVMLift.decodeARM32With arm 0 0 (bytes [0xfc, 0xff, 0xff, 0xea])
  check "ARM32 backward b" (top32 - 8) armB
  let (_, armEffect) ← executeEffect armB
  assertJump "ARM32 backward b lifted target" (top32 - 8) armEffect
  let thumb ← Target.LLVMLift.thumbEnvironment
  let thumbB ← Target.LLVMLift.decodeThumbWith thumb 0 0 (bytes [0xfc, 0xe7])
  check "Thumb backward b" (top32 - 4) thumbB
  let (_, thumbEffect) ← executeEffect thumbB
  assertJump "Thumb backward b lifted target" (top32 - 4) thumbEffect
  let riscv ← Target.LLVMLift.riscvEnvironment
  check "RISC-V backward j" (top64 - 16)
    (← Target.LLVMLift.decodeRISCVWith riscv 0 0 (bytes [0x6f, 0xf0, 0x1f, 0xff]))
  let riscv32 ← Target.LLVMLift.riscv32Environment
  check "RISC-V 32 backward j" (top32 - 16)
    (← Target.LLVMLift.decodeRISCV32With riscv32 0 0 (bytes [0x6f, 0xf0, 0x1f, 0xff]))
  let aarch64 ← Target.LLVMLift.aarch64Environment
  check "AArch64 backward b" (top64 - 16)
    (← Target.LLVMLift.decodeAArch64With aarch64 0 0 (bytes [0xfc, 0xff, 0xff, 0x17]))
  let mips ← Target.LLVMLift.mipsEnvironment
  check "MIPS backward beq" (top64 - 12)
    (← Target.LLVMLift.decodeMIPSWith mips 0 0 (bytes [0x10, 0x82, 0xff, 0xfc]))
  let mips32 ← Target.LLVMLift.mips32Environment
  check "MIPS 32 backward beq" (top32 - 12)
    (← Target.LLVMLift.decodeMIPS32With mips32 0 0 (bytes [0x10, 0x82, 0xff, 0xfc]))

/-- The vector registers have their widths, XMM is the low half of YMM. -/
private def testVectorRegisters : IO Unit := do
  let x86 ← Target.LLVMLift.x86Environment
  let view (triple name : String) (environment : Primus.Semantics.Environment) : IO String := do
    match environment.registers.get? (← LLVM.registerId triple name) with
    | some (.register base width baseWidth) => pure s!"{base} {width} {baseWidth}"
    | _ => throw <| IO.userError s!"{name} is not a register"
  assertEqual "x86 XMM0" "YMM0 128 256" (← view "x86_64" "XMM0" x86)
  assertEqual "x86 XMM15" "YMM15 128 256" (← view "x86_64" "XMM15" x86)
  assertEqual "x86 YMM1" "YMM1 256 256" (← view "x86_64" "YMM1" x86)
  assertEqual "x86 ZMM2" "ZMM2 512 512" (← view "x86_64" "ZMM2" x86)
  let x8632 ← Target.LLVMLift.x8632Environment
  assertEqual "x86-32 XMM7" "YMM7 128 256" (← view "i386" "XMM7" x8632)

/-- A memory with one word at an address. -/
private def thumbMemAt (address value : Nat) : IO Bil.Env :=
  match Memory.write (Memory.empty 32) (BitVec.ofNat 32 address) (BitVec.ofNat 32 value) .little 4 with
  | .ok memory => pure [(thumbMemVar, .memory memory)]
  | .error error => throw <| IO.userError error

/-- The 16-bit Thumb instructions, on encodings decoded by the linked LLVM. -/
private def testThumbNarrow : IO Unit := do
  let thumb ← Target.LLVMLift.thumbEnvironment
  let decode (values : List Nat) := Target.LLVMLift.decodeThumbWith thumb 0x2000 0x2000 (bytes values)
  let run (values : List Nat) (env : Bil.Env) := do execute (← decode values) env
  let r (name : String) (value : Nat) := word32 name value
  assertReg32 "tMOVi8" "R0" 1 (← run [0x01, 0x20] [])
  let adds ← run [0x01, 0x30] [r "R0" 0xffffffff]
  assertReg32 "tADDi8" "R0" 0 adds
  assertFlag "tADDi8 carry" "CF" 1 adds
  assertFlag "tADDi8 zero" "ZF" 1 adds
  let subs ← run [0x01, 0x38] [r "R0" 0]
  assertReg32 "tSUBi8" "R0" 0xffffffff subs
  assertFlag "tSUBi8 no carry after a borrow" "CF" 0 subs
  assertFlag "tSUBi8 negative" "NF" 1 subs
  assertReg32 "tADDrr" "R0" 7 (← run [0x88, 0x18] [r "R1" 3, r "R2" 4, r "R0" 0])
  assertReg32 "tADDi3" "R0" 4 (← run [0xc8, 0x1c] [r "R1" 1, r "R0" 0])
  assertReg32 "tSUBrr" "R0" 1 (← run [0x88, 0x1a] [r "R1" 4, r "R2" 3, r "R0" 0])
  assertFlag "tCMPi8 equal" "ZF" 1 (← run [0x01, 0x28] [r "R0" 1])
  assertFlag "tCMPr carry" "CF" 1 (← run [0x88, 0x42] [r "R0" 1, r "R1" 1])
  assertReg32 "tLSLri" "R0" 12 (← run [0x88, 0x00] [r "R1" 3, r "R0" 0])
  assertReg32 "tLSRri" "R0" 3 (← run [0x88, 0x08] [r "R1" 12, r "R0" 0])
  assertFlag "tLSRri carry" "CF" 1 (← run [0x88, 0x08] [r "R1" 2, r "R0" 0])
  assertReg32 "tASRri" "R0" 0xffffffff (← run [0x88, 0x10] [r "R1" 0xfffffffc, r "R0" 0])
  assertReg32 "tORR" "R0" 3 (← run [0x08, 0x43] [r "R0" 1, r "R1" 2])
  assertReg32 "tADC" "R0" 4 (← run [0x48, 0x41] [r "R0" 1, r "R1" 2, bit "CF" 1])
  assertReg32 "tUXTB" "R0" 0xff (← run [0xc8, 0xb2] [r "R1" 0x1ff, r "R0" 0])
  assertReg32 "tSXTB" "R0" 0xffffffff (← run [0x48, 0xb2] [r "R1" 0xff, r "R0" 0])
  assertReg32 "tADDspi" "SP" 0x1008 (← run [0x02, 0xb0] [r "SP" 0x1000])
  assertReg32 "tSUBspi" "SP" 0xff8 (← run [0x82, 0xb0] [r "SP" 0x1000])
  assertReg32 "tADDrSPi" "R0" 0x1004 (← run [0x01, 0xa8] [r "SP" 0x1000, r "R0" 0])
  let stack ← thumbStack [0x11, 0x22]
  assertReg32 "tLDRspi" "R0" 0x22 (← run [0x01, 0x98] (r "R0" 0 :: stack))
  assertReg32 "tLDRi" "R0" 0x22 (← run [0x48, 0x68] (r "R1" 0x1000 :: r "R0" 0 :: stack))
  assertReg32 "tLDRBi" "R0" 0x11 (← run [0x08, 0x78] (r "R1" 0x1000 :: r "R0" 0 :: stack))
  let pushed ← run [0x01, 0xb5] (r "R0" 0x55 :: r "LR" 0x77 :: stack)
  assertReg32 "tPUSH" "SP" 0xff8 pushed
  assertReg32 "tPOP after tPUSH" "R1" 0x55
    (← run [0x02, 0xbc] (pushed.env ++ [r "R1" 0]))
  assertReg32 "tSTRspi then tLDRspi" "R2" 0x99
    (← run [0x01, 0x9a] ((← run [0x01, 0x90] (r "R0" 0x99 :: r "R2" 0 :: stack)).env))
  -- the rest of the narrow encodings
  let moved ← run [0x08, 0x00] [r "R1" 0x80000000, r "R0" 0]
  assertReg32 "tMOVSr" "R0" 0x80000000 moved
  assertFlag "tMOVSr negative" "NF" 1 moved
  assertFlag "tMOVSr not zero" "ZF" 0 moved
  let moved0 ← run [0x08, 0x00] [r "R1" 0, r "R0" 7]
  assertFlag "tMOVSr zero" "ZF" 1 moved0
  let sub3 ← run [0xc8, 0x1e] [r "R1" 3, r "R0" 9]
  assertReg32 "tSUBi3" "R0" 0 sub3
  assertFlag "tSUBi3 zero" "ZF" 1 sub3
  assertFlag "tSUBi3 no borrow" "CF" 1 sub3
  assertReg32 "tSXTH" "R0" 0xffff8000 (← run [0x08, 0xb2] [r "R1" 0x18000, r "R0" 0])
  assertReg32 "tUXTH" "R0" 0x8000 (← run [0x88, 0xb2] [r "R1" 0x18000, r "R0" 0])
  let bytesAt (values : List Nat) : IO Bil.Env := thumbStack values
  -- memory from 0x1000: the words 0x8877ff80 and 0x44332211, with an offset register R2
  let mem ← bytesAt [0x8877ff80, 0x44332211]
  let at' (rest : Bil.Env) : Bil.Env := rest ++ r "R1" 0x1000 :: r "R0" 0 :: mem
  assertReg32 "tLDRr" "R0" 0x44332211 (← run [0x88, 0x58] (at' [r "R2" 4]))
  assertReg32 "tLDRBr" "R0" 0x80 (← run [0x88, 0x5c] (at' [r "R2" 0]))
  assertReg32 "tLDRSB" "R0" 0xffffff80 (← run [0x88, 0x56] (at' [r "R2" 0]))
  assertReg32 "tLDRSB of a positive byte" "R0" 0x77 (← run [0x88, 0x56] (at' [r "R2" 2]))
  assertReg32 "tLDRHi scales by two" "R0" 0x8877 (← run [0x48, 0x88] (at' []))
  assertReg32 "tLDRHr" "R0" 0xff80 (← run [0x88, 0x5a] (at' [r "R2" 0]))
  assertReg32 "tLDRSH" "R0" 0xffffff80 (← run [0x88, 0x5e] (at' [r "R2" 0]))
  assertReg32 "tLDRSH of a positive halfword" "R0" 0x2211 (← run [0x88, 0x5e] (at' [r "R2" 4]))
  -- a literal, from the word-aligned pc: at 0x2000 the pc is 0x2004
  assertReg32 "tLDRpci" "R0" 0x12345678 (← run [0x01, 0x48] (r "R0" 0 :: (← thumbMemAt 0x2008 0x12345678)))
  -- a store and the load of what it wrote, with the neighbours left alone
  let store (values : List Nat) (env : Bil.Env) := do pure (← run values (at' env)).env
  let afterStr ← store [0x48, 0x60] [r "R0" 0xaabbccdd]
  assertReg32 "tSTRi scales by four" "R3" 0xaabbccdd (← run [0x4b, 0x68] (r "R3" 0 :: afterStr))
  let afterStrr ← store [0x88, 0x50] [r "R0" 0xaabbccdd, r "R2" 4]
  assertReg32 "tSTRr" "R3" 0xaabbccdd (← run [0x4b, 0x68] (r "R3" 0 :: afterStrr))
  let storeWith (values : List Nat) (env : Bil.Env) := do
    pure (← run values (r "R1" 0x1000 :: env ++ mem)).env
  let afterStrb ← storeWith [0x48, 0x70] [r "R0" 0xaabbccdd]
  assertReg32 "tSTRBi writes one byte" "R3" 0x8877dd80 (← run [0x0b, 0x68] (r "R3" 0 :: afterStrb))
  let afterStrbr ← storeWith [0x88, 0x54] [r "R0" 0xaabbccdd, r "R2" 2]
  assertReg32 "tSTRBr writes one byte" "R3" 0x88ddff80 (← run [0x0b, 0x68] (r "R3" 0 :: afterStrbr))
  let afterStrh ← storeWith [0x48, 0x80] [r "R0" 0xaabbccdd]
  assertReg32 "tSTRHi writes two bytes" "R3" 0xccddff80 (← run [0x0b, 0x68] (r "R3" 0 :: afterStrh))
  let afterStrhr ← storeWith [0x88, 0x52] [r "R0" 0xaabbccdd, r "R2" 0]
  assertReg32 "tSTRHr writes two bytes" "R3" 0x8877ccdd (← run [0x0b, 0x68] (r "R3" 0 :: afterStrhr))
  -- load and store multiple: narrow LDM writes back unless the base is in the list
  let ldm ← run [0x05, 0xc9] (r "R2" 0 :: at' [])
  assertReg32 "tLDMIA first" "R0" 0x8877ff80 ldm
  assertReg32 "tLDMIA second" "R2" 0x44332211 ldm
  assertReg32 "tLDMIA writes back" "R1" 0x1008 ldm
  let ldmBase ← run [0x06, 0xc9] (r "R2" 0 :: at' [])
  assertReg32 "tLDMIA with the base in the list loads it" "R1" 0x8877ff80 ldmBase
  assertReg32 "tLDMIA with the base in the list, next" "R2" 0x44332211 ldmBase
  let stm ← run [0x05, 0xc1] (r "R1" 0x1000 :: r "R0" 0x10 :: r "R2" 0x20 :: mem)
  assertReg32 "tSTMIA_UPD writes back" "R1" 0x1008 stm
  assertReg32 "tSTMIA_UPD first" "R3" 0x10 (← run [0x0b, 0x68] (r "R3" 0 :: r "R1" 0x1000 :: stm.env))
  assertReg32 "tSTMIA_UPD second" "R3" 0x20 (← run [0x4b, 0x68] (r "R3" 0 :: r "R1" 0x1000 :: stm.env))
  -- an immediate of 0 of the right shifts is a shift by 32
  let lsr32 ← run [0x08, 0x08] [r "R1" 0x80000000, r "R0" 7]
  assertReg32 "tLSRri by 32" "R0" 0 lsr32
  assertFlag "tLSRri by 32 carries the top bit" "CF" 1 lsr32
  assertFlag "tLSRri by 32 is zero" "ZF" 1 lsr32
  let asr32 ← run [0x08, 0x10] [r "R1" 0x80000000, r "R0" 7]
  assertReg32 "tASRri by 32 fills with the sign" "R0" 0xffffffff asr32
  assertFlag "tASRri by 32 carries the sign" "CF" 1 asr32
  let asr32p ← run [0x08, 0x10] [r "R1" 0x40000000, r "R0" 7]
  assertReg32 "tASRri by 32 of a positive value" "R0" 0 asr32p
  assertFlag "tASRri by 32 of a positive value has no carry" "CF" 0 asr32p

/-- An IT instruction takes the instructions it predicates, each under its condition. -/
private def testThumbIt : IO Unit := do
  let thumb ← Target.LLVMLift.thumbEnvironment
  let decode (values : List Nat) := Target.LLVMLift.decodeThumbWith thumb 0x2000 0x2000 (bytes values)
  let run (values : List Nat) (env : Bil.Env) := do execute (← decode values) env
  let r (name : String) (value : Nat) := word32 name value
  -- ite eq; moveq r0, r1; movne r0, r2
  let ite := [0x0c, 0xbf, 0x08, 0x46, 0x10, 0x46]
  let block ← decode ite
  assertEqual "IT covers its block" 6 block.size
  assertEqual "IT has a normal flow" Disasm.Flow.normal block.flow
  let flags (z : Nat) : Bil.Env := [bit "ZF" z, bit "NF" 0, bit "VF" 0, bit "CF" 0, r "R1" 11, r "R2" 22, r "R0" 0]
  assertReg32 "ite: then" "R0" 11 (← run ite (flags 1))
  assertReg32 "ite: else" "R0" 22 (← run ite (flags 0))
  -- itte lt; addlt r0, #1; addlt r0, r1; subge r0, r0, #1: narrow instructions in a block do not set the flags
  let itte := [0xba, 0xbf, 0x01, 0x30, 0x08, 0x44, 0x40, 0x1e]
  let less : Bil.Env := [bit "NF" 1, bit "VF" 0, bit "ZF" 0, bit "CF" 0, r "R0" 0xffffffff, r "R1" 5]
  let taken ← run itte less
  assertReg32 "itte: both then branches run" "R0" 5 taken
  assertFlag "itte: adds in a block leaves the carry" "CF" 0 taken
  assertFlag "itte: adds in a block leaves zero" "ZF" 0 taken
  let notLess : Bil.Env := [bit "NF" 0, bit "VF" 0, bit "ZF" 0, bit "CF" 0, r "R0" 1, r "R1" 5]
  let other ← run itte notLess
  assertReg32 "itte: the else branch runs" "R0" 0 other
  assertFlag "itte: subs in a block leaves zero" "ZF" 0 other
  -- it eq; cmpeq r0, #1 changes the flags under the condition only
  let itCmp := [0x08, 0xbf, 0x01, 0x28]
  assertFlag "it: cmp under a false condition does nothing" "ZF" 0
    (← run itCmp [bit "ZF" 0, bit "CF" 0, bit "NF" 0, bit "VF" 0, r "R0" 1])
  -- it al; adds r0, #1: a narrow instruction in a block doesn't set the flags, even if it always runs
  let itAl := [0xe8, 0xbf, 0x01, 0x30]
  let always ← run itAl [bit "ZF" 0, bit "CF" 0, bit "NF" 0, bit "VF" 0, r "R0" 0xffffffff]
  assertReg32 "it al: the instruction runs" "R0" 0 always
  assertFlag "it al: adds in a block leaves zero" "ZF" 0 always
  assertFlag "it al: adds in a block leaves the carry" "CF" 0 always
  -- the same instruction out of a block sets them
  let plain ← run [0x01, 0x30] [bit "ZF" 0, bit "CF" 0, bit "NF" 0, bit "VF" 0, r "R0" 0xffffffff]
  assertFlag "adds out of a block sets zero" "ZF" 1 plain
  assertFlag "adds out of a block sets the carry" "CF" 1 plain
  -- it ne; bxne lr can be skipped
  let itBx ← decode [0x18, 0xbf, 0x70, 0x47]
  assertEqual "IT with a return is conditional" Disasm.Flow.conditionalJump itBx.flow
  assertEqual "IT with a return is its whole size" 4 itBx.size
  let (_, taken) ← executeEffect itBx [bit "ZF" 0, r "LR" 0x3000]
  assertJump "IT return taken" 0x3000 taken
  let (_, skipped) ← executeEffect itBx [bit "ZF" 1, r "LR" 0x3000]
  assertEqual "IT return skipped" true (skipped matches .normal)
  -- it eq; bleq: a call stays a call, with its own target, and the link is the one of its address
  let itBl ← decode [0x08, 0xbf, 0x00, 0xf0, 0x02, 0xf8]
  assertEqual "IT with a call is a call" Disasm.Flow.call itBl.flow
  assertEqual "IT with a call has its target" (some (0x2002 + 4 + 4)) itBl.target
  -- it eq; popeq {r0, pc}, of the semantics of multiple registers
  let itPop := [0x08, 0xbf, 0x01, 0xbd]
  let stack ← thumbStack [0x11, 0x2000]
  let (_, popped) ← executeEffect (← decode itPop) (bit "ZF" 1 :: stack)
  assertJump "IT with a pop to the pc" 0x2000 popped
  let (poppedState, notPopped) ← executeEffect (← decode itPop) (bit "ZF" 0 :: stack)
  assertEqual "IT with a pop under a false condition" true (notPopped matches .normal)
  assertReg32 "IT with a pop leaves the stack" "SP" 0x1000 poppedState
  -- the rest of the program scans past the block
  let scan ← Disasm.Recursive.scan (← Target.Thumb.disassembler 0) (bytes (ite ++ [0x70, 0x47])) 0
  assertEqual "scan treats a block as an instruction" [0, 6] (scan.instructions.map (·.address))

/-- The moves and the integer arithmetic of SSE, on the XMM registers in the low halves of YMM. -/
private def testX86Sse : IO Unit := do
  for (label, env) in [("x86-64", ← Target.LLVMLift.x86Environment), ("x86-32", ← Target.LLVMLift.x8632Environment)] do
    let decode (values : List Nat) :=
      if label == "x86-64" then Target.LLVMLift.decodeX86With env 0 0 (bytes values)
      else Target.LLVMLift.decodeX8632With env 0 0 (bytes values)
    let ymm (name : String) (value : Nat) : Bap.Var × Bap.Value :=
      (⟨name, .imm 256, 0, false⟩, .bits (BitVec.ofNat 256 value))
    let upper := 0xdddddddddddddddd_cccccccccccccccc * 2 ^ 128
    let x := 0x0000000400000003_0000000200000001
    let y := 0xffffffff00000010_0000002000000030
    let check (name : String) (values : List Nat) (expected : Nat) : IO Unit := do
      let state ← execute (← decode values) [ymm "YMM0" (upper + x), ymm "YMM1" y]
      match Bil.lookup state.env ⟨"YMM0", .imm 256, 0, false⟩ with
      | .ok (.bits value) => assertEqual s!"{label} {name}" (upper + expected) value.toNat
      | _ => throw <| IO.userError s!"{label} {name}: no YMM0"
    -- the moves between registers keep the upper half of YMM, as the instructions without a VEX prefix do
    check "movaps" [0x0f, 0x28, 0xc1] y
    check "movups" [0x0f, 0x10, 0xc1] y
    check "movapd" [0x66, 0x0f, 0x28, 0xc1] y
    check "movdqa" [0x66, 0x0f, 0x6f, 0xc1] y
    check "movdqu" [0xf3, 0x0f, 0x6f, 0xc1] y
    check "movq between registers clears the high half" [0xf3, 0x0f, 0x7e, 0xc1] 0x0000002000000030
    -- the bitwise operations
    check "pxor" [0x66, 0x0f, 0xef, 0xc1] (x ^^^ y)
    check "por" [0x66, 0x0f, 0xeb, 0xc1] (x ||| y)
    check "pand" [0x66, 0x0f, 0xdb, 0xc1] (x &&& y)
    check "xorps" [0x0f, 0x57, 0xc1] (x ^^^ y)
    check "andps" [0x0f, 0x54, 0xc1] (x &&& y)
    -- the lanes do not carry into each other
    check "paddd" [0x66, 0x0f, 0xfe, 0xc1] 0x0000000300000013_0000002200000031
    check "psubd" [0x66, 0x0f, 0xfa, 0xc1] 0x00000005fffffff3_ffffffe2ffffffd1
    check "paddq" [0x66, 0x0f, 0xd4, 0xc1] 0x0000000300000013_0000002200000031
    check "pcmpeqd" [0x66, 0x0f, 0x76, 0xc1] 0
    check "pshufd" [0x66, 0x0f, 0x70, 0xc1, 0x1b] 0x0000003000000020_00000010ffffffff
    check "punpcklqdq" [0x66, 0x0f, 0x6c, 0xc1] (0x0000002000000030 * 2 ^ 64 + 0x0000000200000001)
    check "pslld" [0x66, 0x0f, 0x72, 0xf0, 0x01] 0x0000000800000006_0000000400000002
  let x86 ← Target.LLVMLift.x86Environment
  let decode (values : List Nat) := Target.LLVMLift.decodeX86With x86 0 0 (bytes values)
  let word64 (name : String) (value : Nat) : Bap.Var × Bap.Value :=
    (⟨name, .imm 64, 0, false⟩, .bits (BitVec.ofNat 64 value))
  let ymm (name : String) (value : Nat) : Bap.Var × Bap.Value :=
    (⟨name, .imm 256, 0, false⟩, .bits (BitVec.ofNat 256 value))
  let readYmm (state : Bil.State) (name : String) : IO Nat :=
    match Bil.lookup state.env ⟨name, .imm 256, 0, false⟩ with
    | .ok (.bits value) => pure value.toNat
    | _ => throw <| IO.userError s!"no {name}"
  let upper := 0xdddddddddddddddd_cccccccccccccccc * 2 ^ 128
  assertEqual "movd to xmm clears the rest of xmm" (upper + 0x11223344)
    (← readYmm (← execute (← decode [0x66, 0x0f, 0x6e, 0xc0]) [ymm "YMM0" (upper + 0xffff * 2 ^ 64), word64 "RAX" 0x55667788_11223344]) "YMM0")
  assertEqual "movq to xmm clears the rest of xmm" (upper + 0x5566778811223344)
    (← readYmm (← execute (← decode [0x66, 0x48, 0x0f, 0x6e, 0xc0]) [ymm "YMM0" (upper + 0xffff * 2 ^ 64), word64 "RAX" 0x5566778811223344]) "YMM0")
  assertReg "movd from xmm clears the upper half of RAX" "RAX" 0x44332211
    (← execute (← decode [0x66, 0x0f, 0x7e, 0xc0]) [ymm "YMM0" 0x8877665544332211, word64 "RAX" (2 ^ 64 - 1)])
  assertReg "movq from xmm" "RAX" 0x8877665544332211
    (← execute (← decode [0x66, 0x48, 0x0f, 0x7e, 0xc0]) [ymm "YMM0" (0x99 * 2 ^ 64 + 0x8877665544332211), word64 "RAX" 0])
  -- with a VEX prefix, the upper half of YMM is cleared
  assertEqual "vmovaps clears the upper half" 0x1234
    (← readYmm (← execute (← decode [0xc5, 0xf8, 0x28, 0xc1]) [ymm "YMM0" upper, ymm "YMM1" 0x1234]) "YMM0")
  -- memory: a load and the store of what it loaded
  let cell : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
  let value := 0x00112233445566778899aabbccddeeff
  let memory ← match Memory.write (Memory.empty 64) (BitVec.ofNat 64 0x1000) (BitVec.ofNat 128 value) .little 16 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  let start : Bil.Env := [(cell, .memory memory), word64 "RAX" 0x1000, ymm "YMM0" upper, word64 "RBX" 0x2000]
  assertEqual "movaps from memory" (upper + value) (← readYmm (← execute (← decode [0x0f, 0x28, 0x00]) start) "YMM0")
  assertEqual "movdqu from memory" (upper + value) (← readYmm (← execute (← decode [0xf3, 0x0f, 0x6f, 0x00]) start) "YMM0")
  assertEqual "movss from memory clears the rest of xmm" (upper + 0xccddeeff)
    (← readYmm (← execute (← decode [0xf3, 0x0f, 0x10, 0x00]) start) "YMM0")
  assertEqual "movsd from memory clears the rest of xmm" (upper + 0x8899aabbccddeeff)
    (← readYmm (← execute (← decode [0xf2, 0x0f, 0x10, 0x00]) start) "YMM0")
  let loaded ← execute (← decode [0x0f, 0x28, 0x00]) start
  let stored ← execute (← decode [0x0f, 0x11, 0x03]) loaded.env
  assertEqual "movups to memory, read back" (upper * 0 + upper + value)
    (← readYmm (← execute (← decode [0xf3, 0x0f, 0x6f, 0x0b]) (ymm "YMM1" upper :: stored.env)) "YMM1")
  -- BIL has no floats: the floating point of SSE lifts to named intrinsics.
  let addsd ← decode [0xf2, 0x0f, 0x58, 0xc1]
  assertTrue "addsd calls its intrinsic" (addsd.bil.any fun stmt =>
    match stmt with
    | .special "fadd_rne_ieee754_binary_64" => true
    | _ => false)

/-- A memory of an address width with bytes at an address. -/
private def bytesAt {width : Nat} (start : Nat) (values : List Nat) (memory : Memory width := Memory.empty width) :
    IO (Memory width) := do
  let mut memory := memory
  for (index, value) in (List.range values.length).zip values do
    match Memory.write memory (BitVec.ofNat width (start + index)) (BitVec.ofNat 8 value) .little 1 with
    | .ok updated => memory := updated
    | .error error => throw <| IO.userError error
  pure memory

private def readByte {width : Nat} (state : Bil.State) (var : Bap.Var) (address : Nat) : IO Nat :=
  match Bil.lookup state.env var with
  | .ok (@Value.memory w memory) =>
    if h : w = width then
      pure (Memory.read (h ▸ memory) (BitVec.ofNat width address) .little 1).toNat
    else throw <| IO.userError "the memory has another width"
  | _ => throw <| IO.userError "memory is not mapped"

/-- The string instructions with their prefixes, on the real encodings, in both modes. -/
private def testX86Repeat : IO Unit := do
  let x86 ← Target.LLVMLift.x86Environment
  let x8632 ← Target.LLVMLift.x8632Environment
  let decode64 (values : List Nat) := Target.LLVMLift.decodeX86With x86 0 0 (bytes values)
  let decode32 (values : List Nat) := Target.LLVMLift.decodeX8632With x8632 0 0 (bytes values)
  let source := [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88]
  let mem32 : Bap.Var := thumbMemVar
  -- rep movsb
  let movsb := [0xf3, 0xa4]
  let m64 ← bytesAt (width := 64) 0x100 source
  let moved ← execute (← decode64 movsb)
    [(memVar, .memory m64), word "RSI" 0x100, word "RDI" 0x200, word "RCX" 3, bit "DF" 0]
  assertEqual "rep movsb copies" [0x11, 0x22, 0x33, 0]
    (← [0x200, 0x201, 0x202, 0x203].mapM (readByte (width := 64) moved memVar))
  assertReg "rep movsb counts down" "RCX" 0 moved
  assertReg "rep movsb moves the source" "RSI" 0x103 moved
  assertReg "rep movsb moves the destination" "RDI" 0x203 moved
  let m32 ← bytesAt (width := 32) 0x100 source
  let moved ← execute (← decode32 movsb)
    [(mem32, .memory m32), word32 "ESI" 0x100, word32 "EDI" 0x200, word32 "ECX" 3, bit "DF" 0]
  assertEqual "32-bit rep movsb copies" [0x11, 0x22, 0x33, 0]
    (← [0x200, 0x201, 0x202, 0x203].mapM (readByte (width := 32) moved mem32))
  assertReg32 "32-bit rep movsb counts down" "ECX" 0 moved
  assertReg32 "32-bit rep movsb moves the source" "ESI" 0x103 moved
  -- with no count nothing moves, and without the prefix it runs once
  let none ← execute (← decode64 movsb)
    [(memVar, .memory m64), word "RSI" 0x100, word "RDI" 0x200, word "RCX" 0, bit "DF" 0]
  assertEqual "rep movsb without a count stores nothing" 0 (← readByte (width := 64) none memVar 0x200)
  assertReg "rep movsb without a count keeps the source" "RSI" 0x100 none
  let once ← execute (← decode64 [0xa4])
    [(memVar, .memory m64), word "RSI" 0x100, word "RDI" 0x200, word "RCX" 3, bit "DF" 0]
  assertEqual "movsb moves one byte" [0x11, 0]
    (← [0x200, 0x201].mapM (readByte (width := 64) once memVar))
  assertReg "movsb keeps the count" "RCX" 3 once
  -- the direction flag
  let backward ← execute (← decode64 movsb)
    [(memVar, .memory m64), word "RSI" 0x102, word "RDI" 0x202, word "RCX" 2, bit "DF" 1]
  assertEqual "rep movsb backward" [0, 0x22, 0x33]
    (← [0x200, 0x201, 0x202].mapM (readByte (width := 64) backward memVar))
  assertReg "rep movsb backward moves down" "RDI" 0x200 backward
  -- rep stosd
  let stosd := [0xf3, 0xab]
  let stored ← execute (← decode64 stosd)
    [(memVar, .memory (Memory.empty 64)), word "RAX" 0xaabbccdd, word "RDI" 0x300, word "RCX" 2, bit "DF" 0]
  assertEqual "rep stosd stores words" [0xdd, 0xcc, 0xbb, 0xaa, 0xdd, 0xcc, 0xbb, 0xaa, 0]
    (← (List.range 9).mapM fun i => readByte (width := 64) stored memVar (0x300 + i))
  assertReg "rep stosd moves by words" "RDI" 0x308 stored
  assertReg "rep stosd counts down" "RCX" 0 stored
  let stored ← execute (← decode32 stosd)
    [(mem32, .memory (Memory.empty 32)), word32 "EAX" 0xaabbccdd, word32 "EDI" 0x300, word32 "ECX" 2, bit "DF" 0]
  assertEqual "32-bit rep stosd stores words" [0xdd, 0xaa, 0xdd, 0xaa, 0]
    (← [0, 3, 4, 7, 8].mapM fun i => readByte (width := 32) stored mem32 (0x300 + i))
  assertReg32 "32-bit rep stosd moves by words" "EDI" 0x308 stored
  -- rep stosq with its REX prefix
  let stored ← execute (← decode64 [0xf3, 0x48, 0xab])
    [(memVar, .memory (Memory.empty 64)), word "RAX" 0x1122334455667788, word "RDI" 0x300, word "RCX" 1, bit "DF" 0]
  assertReg "rep stosq moves by double words" "RDI" 0x308 stored
  assertEqual "rep stosq stores the top byte" 0x11 (← readByte (width := 64) stored memVar 0x307)
  -- repne scasb stops at the byte it looks for
  let scasb := [0xf2, 0xae]
  let scanned ← execute (← decode64 scasb)
    [(memVar, .memory m64), word "RAX" 0x33, word "RDI" 0x100, word "RCX" 8, bit "DF" 0]
  assertReg "repne scasb stops after the match" "RDI" 0x103 scanned
  assertReg "repne scasb counts the bytes" "RCX" 5 scanned
  assertFlag "repne scasb sets ZF at the match" "ZF" 1 scanned
  let scanned ← execute (← decode32 scasb)
    [(mem32, .memory m32), word32 "EAX" 0x33, word32 "EDI" 0x100, word32 "ECX" 8, bit "DF" 0]
  assertReg32 "32-bit repne scasb stops after the match" "EDI" 0x103 scanned
  assertReg32 "32-bit repne scasb counts the bytes" "ECX" 5 scanned
  assertFlag "32-bit repne scasb sets ZF at the match" "ZF" 1 scanned
  let missed ← execute (← decode64 scasb)
    [(memVar, .memory m64), word "RAX" 0xee, word "RDI" 0x100, word "RCX" 4, bit "DF" 0]
  assertReg "repne scasb runs out of the count" "RCX" 0 missed
  assertFlag "repne scasb without a match clears ZF" "ZF" 0 missed
  -- repe cmpsb stops at the first difference
  let other ← bytesAt 0x200 [0x11, 0x22, 0xff, 0x44] m64
  let compared ← execute (← decode64 [0xf3, 0xa6])
    [(memVar, .memory other), word "RSI" 0x100, word "RDI" 0x200, word "RCX" 8, bit "DF" 0]
  assertReg "repe cmpsb stops after the difference" "RSI" 0x103 compared
  assertReg "repe cmpsb counts the bytes" "RCX" 5 compared
  assertFlag "repe cmpsb clears ZF at the difference" "ZF" 0 compared
  -- the last of the repeat prefixes counts, as in the architecture and LLVM
  let last ← execute (← decode64 [0xf3, 0xf2, 0xae])
    [(memVar, .memory m64), word "RAX" 0x33, word "RDI" 0x100, word "RCX" 8, bit "DF" 0]
  assertReg "of REP and REPNE the last counts" "RDI" 0x103 last
  -- the prefix of the address size: the 32-bit registers and the count, which clears the upper half
  let short ← execute (← decode64 [0x67, 0xf3, 0xa4])
    [(memVar, .memory m64), word "RSI" 0x100, word "RDI" 0x200, word "RCX" 0x100000002, bit "DF" 0]
  assertEqual "rep movsb with the prefix 0x67 copies by ECX" [0x11, 0x22, 0]
    (← [0x200, 0x201, 0x202].mapM (readByte (width := 64) short memVar))
  assertReg "a 32-bit count clears the upper half" "RCX" 0 short
  assertReg "a 32-bit source clears the upper half" "RSI" 0x102 short
  let m32 ← bytesAt (width := 32) 0x100 source
  let short32 ← execute (← decode32 [0x67, 0xf3, 0xa4])
    [(mem32, .memory m32), word32 "ESI" 0x100, word32 "EDI" 0x200, word32 "ECX" 0x10002, bit "DF" 0]
  assertEqual "rep movsb with the prefix 0x67 copies by CX" [0x11, 0x22, 0]
    (← [0x200, 0x201, 0x202].mapM (readByte (width := 32) short32 mem32))
  assertReg32 "a 16-bit count keeps the upper half" "ECX" 0x10000 short32
  assertEqual "the prefixes that count" [0x66, 0xf3] (Target.LLVMLift.x86Prefixes true [0x66, 0xf3, 0xa5])
  assertEqual "a REX prefix before a prefix is ignored" [0xf3] (Target.LLVMLift.x86Prefixes true [0x48, 0xf3, 0xa4])
  assertEqual "the 32-bit mode has no REX prefix" ([] : List Nat) (Target.LLVMLift.x86Prefixes false [0x48, 0xf3, 0xa4])
  -- a repeated string instruction doesn't change the control flow
  assertEqual "rep movsb is a normal instruction" Disasm.Flow.normal (← decode64 movsb).flow
  assertEqual "rep movsb has its size" 2 (← decode64 movsb).size
  assertEqual "the size counts the prefixes" 3 (← decode64 [0x67, 0xf3, 0xa4, 0x90]).size

/-- The registers of x87 and the status words, with their widths, the flags in EFLAGS. -/
private def testX86Registers : IO Unit := do
  let x86 ← Target.LLVMLift.x86Environment
  let x8632 ← Target.LLVMLift.x8632Environment
  let st (name : String) (value : Nat) : Bap.Var × Value := (⟨name, .imm 80, 0, false⟩, .bits (BitVec.ofNat 80 value))
  let short (name : String) (value : Nat) : Bap.Var × Value := (⟨name, .imm 16, 0, false⟩, .bits (BitVec.ofNat 16 value))
  let stack := (List.range 8).map fun n => st s!"ST{n}" n
  -- fld st(1), which needs ST0-ST7, the status word and the tag word
  let fld ← Target.LLVMLift.decodeX86With x86 0 0 (bytes [0xd9, 0xc1])
  assertEqual "fld st(1) is what it is" "fld st(1)" fld.asm
  let pushed ← execute fld (stack ++ [short "FPU_STATUS" 0, short "FPU_TAG" 0xffff])
  let stValue (state : Bil.State) (name : String) : IO Nat :=
    match Bil.lookup state.env ⟨name, .imm 80, 0, false⟩ with
    | .ok (.bits value) => pure value.toNat
    | _ => throw <| IO.userError s!"{name} is not a register of 80 bits"
  assertEqual "fld pushes" 1 (← stValue pushed "ST0")
  assertEqual "fld rotates" 0 (← stValue pushed "ST1")
  let pushed32 ← execute (← Target.LLVMLift.decodeX8632With x8632 0 0 (bytes [0xd9, 0xc1]))
    (stack ++ [short "FPU_STATUS" 0, short "FPU_TAG" 0xffff])
  assertEqual "32-bit fld pushes" 1 (← stValue pushed32 "ST0")
  let _ ← Target.LLVMLift.decodeX86With x86 0 0 (bytes [0xdd, 0x00])
  let _ ← Target.LLVMLift.decodeX86With x86 0 0 (bytes [0xdb, 0x28])
  -- the control word and MXCSR
  let m64 ← bytesAt (width := 64) 0x100 [0x7f, 0x03, 0, 0]
  let loaded ← execute (← Target.LLVMLift.decodeX86With x86 0 0 (bytes [0xd9, 0x28])) [(memVar, .memory m64), word "RAX" 0x100]
  match Bil.lookup loaded.env ⟨"FPU_CONTROL", .imm 16, 0, false⟩ with
  | .ok (.bits value) => assertEqual "fldcw loads the control word" 0x37f value.toNat
  | _ => throw <| IO.userError "FPU_CONTROL is not a register of 16 bits"
  let loaded ← execute (← Target.LLVMLift.decodeX86With x86 0 0 (bytes [0x0f, 0xae, 0x10])) [(memVar, .memory m64), word "RAX" 0x100]
  assertReg32 "ldmxcsr loads MXCSR" "MXCSR" 0x37f loaded
  -- EFLAGS is the flags: what POPF loads is in the flags, and PUSHF stores the flags
  let flagNames := ["AI", "AES", "EFLAGS_29", "EFLAGS_28", "EFLAGS_27", "EFLAGS_26", "EFLAGS_25", "EFLAGS_24", "EFLAGS_23",
    "EFLAGS_22", "ID", "VIP", "VIF", "AC", "VM", "RF", "MD", "NT", "IOPLH", "IOPLL", "OF", "DF", "IF", "TF", "SF", "ZF",
    "EFLAGS_5", "AF", "EFLAGS_3", "PF", "EFLAGS_1", "CF"]
  let clear := flagNames.map fun name => bit name 0
  let stackWord ← bytesAt (width := 64) 0x1000 [0xc1, 0x08, 0, 0, 0, 0, 0, 0]
  let popped ← execute (← Target.LLVMLift.decodeX86With x86 0 0 (bytes [0x9d])) [(memVar, .memory stackWord), word "RSP" 0x1000]
  assertFlag "popf loads CF" "CF" 1 popped
  assertFlag "popf loads ZF" "ZF" 1 popped
  assertFlag "popf loads SF" "SF" 1 popped
  assertFlag "popf loads OF" "OF" 1 popped
  assertFlag "popf loads PF" "PF" 0 popped
  assertReg "popf moves the stack" "RSP" 0x1008 popped
  let flags := clear.map fun binding => if binding.1.name = "CF" || binding.1.name = "ZF" then (binding.1, .bits (BitVec.ofNat 1 1)) else binding
  let pushed ← execute (← Target.LLVMLift.decodeX86With x86 0 0 (bytes [0x9c]))
    ((memVar, .memory (Memory.empty 64)) :: word "RSP" 0x1000 :: flags)
  -- CF, the reserved bit 1, and ZF
  assertEqual "pushf stores the flags" [0x43, 0] (← [0xff8, 0xff9].mapM (readByte (width := 64) pushed memVar))
  let pushed ← execute (← Target.LLVMLift.decodeX8632With x8632 0 0 (bytes [0x9c]))
    ((thumbMemVar, .memory (Memory.empty 32)) :: word32 "ESP" 0x1000 :: flags)
  assertEqual "32-bit pushf stores the flags" 0x43 (← readByte (width := 32) pushed thumbMemVar 0xffc)

/-- The bank of VFP: `Sn` are the halves of `Dn`, and the writes through them keep the other half. -/
private def testArmVfpRegisters : IO Unit := do
  let arm ← Target.LLVMLift.arm32Environment
  let decode (values : List Nat) := Target.LLVMLift.decodeARM32With arm 0 0 (bytes values)
  let double (name : String) (value : Nat) : Bap.Var × Value := (⟨name, .imm 64, 0, false⟩, .bits (BitVec.ofNat 64 value))
  let doubleOf (state : Bil.State) (name : String) : IO Nat :=
    match Bil.lookup state.env ⟨name, .imm 64, 0, false⟩ with
    | .ok (.bits value) => pure value.toNat
    | _ => throw <| IO.userError s!"{name} is not a register of 64 bits"
  -- vmov s1, r0
  let moved ← execute (← decode [0x90, 0x0a, 0x00, 0xee]) [double "D0" 0x1111111122222222, word32 "R0" 0xaabbccdd]
  assertEqual "a write of S1 is the upper half of D0" (0xaabbccdd22222222 : Nat) (← doubleOf moved "D0")
  -- vmov s0, r0
  let moved ← execute (← decode [0x10, 0x0a, 0x00, 0xee]) [double "D0" 0x1111111122222222, word32 "R0" 0xaabbccdd]
  assertEqual "a write of S0 is the lower half of D0" 0x11111111aabbccdd (← doubleOf moved "D0")
  -- vmov r0, s3
  let read ← execute (← decode [0x90, 0x0a, 0x11, 0xee]) [double "D1" 0x1111111122222222, word32 "R0" 0]
  assertReg32 "a read of S3 is the upper half of D1" "R0" 0x11111111 read
  -- vadd.f64 d0, d1, d2 lifts on registers of 64 bits
  let _ ← decode [0x02, 0x0b, 0x31, 0xee]
  -- vmrs APSR_nzcv, fpscr, the only way to read FPSCR
  let flags ← execute (← decode [0x10, 0xfa, 0xf1, 0xee])
    [word32 "FPSCR" 0x60000000, bit "NF" 0, bit "ZF" 0, bit "CF" 0, bit "VF" 0]
  assertFlag "vmrs copies Z of FPSCR" "ZF" 1 flags
  assertFlag "vmrs copies C of FPSCR" "CF" 1 flags
  assertFlag "vmrs copies N of FPSCR" "NF" 0 flags
  -- the thread registers: mrc p15, 0, r0, c13, c0, 3 and 2
  assertReg32 "mrc reads TPIDRURO" "R0" 7 (← execute (← decode [0x70, 0x0f, 0x1d, 0xee]) [word32 "TPIDRURO" 7, word32 "R0" 0])
  assertReg32 "mrc reads TPIDRURW" "R0" 8 (← execute (← decode [0x50, 0x0f, 0x1d, 0xee]) [word32 "TPIDRURW" 8, word32 "R0" 0])
  assertReg32 "mcr writes TPIDRURW" "TPIDRURW" 9 (← execute (← decode [0x50, 0x0f, 0x0d, 0xee]) [word32 "R0" 9])

/-- The condition register fields of PowerPC are the aliases of their bits. -/
private def testPowerPCFields : IO Unit := do
  let powerpc ← Target.LLVMLift.powerpcEnvironment
  -- cmpw cr3, r4, r5 and mfcr r6, and the same in the 32-bit mode
  let compare ← Target.LLVMLift.decodePowerPCWith powerpc 0 0 (bytes [0x00, 0x28, 0x84, 0x7d])
  let state ← execute compare [word "R4" 1, word "R5" 2, bit "SO" 0]
  assertFlag "cmpw sets LT of its field" "CR3LT" 1 state
  assertFlag "cmpw clears GT of its field" "CR3GT" 0 state
  assertFlag "cmpw clears EQ of its field" "CR3EQ" 0 state
  assertFlag "cmpw copies SO in its field" "CR3UN" 0 state
  let powerpc32 ← Target.LLVMLift.powerpc32Environment
  let compare32 ← Target.LLVMLift.decodePowerPC32With powerpc32 0 0 (bytes [0x7d, 0x84, 0x28, 0x00])
  let state ← execute compare32 [word32 "R4" 2, word32 "R5" 2, bit "SO" 1]
  assertFlag "32-bit cmpw sets EQ of its field" "CR3EQ" 1 state
  assertFlag "32-bit cmpw copies SO in its field" "CR3UN" 1 state
  -- mfocrf and mtocrf name a field: mtocrf cr7, r3
  let fields := (List.range 8).flatMap fun n => [bit s!"CR{n}LT" 0, bit s!"CR{n}GT" 0, bit s!"CR{n}EQ" 0, bit s!"CR{n}UN" 0]
  let moved ← execute (← Target.LLVMLift.decodePowerPCWith powerpc 0 0 (bytes [0x20, 0x11, 0x70, 0x7c])) (word "R3" 0xa :: fields)
  assertFlag "mtocrf sets the first bit" "CR7LT" 1 moved
  assertFlag "mtocrf sets the third bit" "CR7EQ" 1 moved
  assertFlag "mtocrf clears the second bit" "CR7GT" 0 moved
  let read ← execute (← Target.LLVMLift.decodePowerPCWith powerpc 0 0 (bytes [0x26, 0x00, 0x60, 0x7c]))
    (word "R3" 0 :: (fields.map fun binding => if binding.1.name = "CR0EQ" then (binding.1, .bits (BitVec.ofNat 1 1)) else binding))
  assertReg "mfcr reads the fields" "R3" 0x20000000 read

/-- The status registers that the semantics name, with their widths, on the real encodings. -/
private def testStatusRegisters : IO Unit := do
  let word64 (name : String) (value : Nat) := word name value
  -- aarch64: mrs x0, daif and msr daifset, #2 and the banks of SP by SPSel
  let aarch64 ← Target.LLVMLift.aarch64Environment
  let decodeA (values : List Nat) := Target.LLVMLift.decodeAArch64With aarch64 0 0 (bytes values)
  let daif (value : Nat) : Bap.Var × Value := (⟨"DAIF", .imm 4, 0, false⟩, .bits (BitVec.ofNat 4 value))
  assertReg "mrs reads DAIF in its place" "X0" 0x2c0 (← execute (← decodeA [0x20, 0x42, 0x3b, 0xd5]) [daif 0xb])
  let masked ← execute (← decodeA [0xdf, 0x42, 0x03, 0xd5]) [daif 0x1]
  match Bil.lookup masked.env ⟨"DAIF", .imm 4, 0, false⟩ with
  | .ok (.bits value) => assertEqual "msr daifset sets the bits of DAIF" 3 value.toNat
  | _ => throw <| IO.userError "DAIF is not a register of 4 bits"
  -- msr spsel, #0: from SP_EL1 to SP_EL0, R31 is SP
  let banked ← execute (← decodeA [0xbf, 0x40, 0x00, 0xd5])
    [bit "SPSel" 1, word64 "SP" 0x1000, word64 "SP_EL0" 0x2000, word64 "SP_EL1" 0]
  assertReg "SP is banked" "SP" 0x2000 banked
  assertReg "SP_EL1 has the old stack" "SP_EL1" 0x1000 banked
  assertFlag "SPSel is a bit" "SPSel" 0 banked
  -- msr pan, #1
  assertFlag "PAN is a bit" "PAN" 1 (← execute (← decodeA [0x9f, 0x41, 0x00, 0xd5]) [])
  -- mrs x0, fpcr and msr fpsr, x0
  assertReg "mrs reads FPCR" "X0" 0x400000 (← execute (← decodeA [0x00, 0x44, 0x3b, 0xd5]) [word32 "FPCR" 0x400000])
  assertReg32 "msr writes FPSR" "FPSR" 0x8 (← execute (← decodeA [0x20, 0x44, 0x1b, 0xd5]) [word64 "X0" 0x8])
  -- mrs x0, cntvct_el0 advances the counter
  let counted ← execute (← decodeA [0x40, 0xe0, 0x3b, 0xd5]) [word64 "CNTVCT_EL0" 5]
  assertReg "the counter advances" "CNTVCT_EL0" 1005 counted
  assertReg "mrs reads the counter" "X0" 1005 counted
  -- riscv: csrr a0, fcsr; csrr a0, vxrm
  let riscv ← Target.LLVMLift.riscvEnvironment
  let riscv32 ← Target.LLVMLift.riscv32Environment
  assertReg "csrr reads FCSR" "X10" 0x65
    (← execute (← Target.LLVMLift.decodeRISCVWith riscv 0 0 (bytes [0x73, 0x25, 0x30, 0x00])) [word32 "FCSR" 0x65, word "X10" 0])
  assertReg "csrr reads VXRM" "X10" 2
    (← execute (← Target.LLVMLift.decodeRISCVWith riscv 0 0 (bytes [0x73, 0x25, 0xa0, 0x00])) [word32 "VXRM" 2, word "X10" 0])
  assertReg32 "csrw writes FCSR" "FCSR" 0x41
    (← execute (← Target.LLVMLift.decodeRISCVWith riscv 0 0 (bytes [0x73, 0x10, 0x35, 0x00])) [word32 "FCSR" 0xff, word "X10" 0x41, word "X0" 0])
  assertReg32 "csrw writes VXRM" "VXRM" 1
    (← execute (← Target.LLVMLift.decodeRISCVWith riscv 0 0 (bytes [0x73, 0x10, 0xa5, 0x00])) [word32 "VXRM" 3, word "X10" 0x5, word "X0" 0])
  assertReg32 "32-bit csrr reads FCSR" "X10" 0x65
    (← execute (← Target.LLVMLift.decodeRISCV32With riscv32 0 0 (bytes [0x73, 0x25, 0x30, 0x00])) [word32 "FCSR" 0x65, word32 "X10" 0])
  -- mips: rdhwr $3, $29
  let mips ← Target.LLVMLift.mipsEnvironment
  let mips32 ← Target.LLVMLift.mips32Environment
  assertReg "rdhwr reads USERLOCAL" "R3" 0x7000
    (← execute (← Target.LLVMLift.decodeMIPSWith mips 0 0 (bytes [0x7c, 0x03, 0xe8, 0x3b])) [word "USERLOCAL" 0x7000])
  assertReg32 "32-bit rdhwr reads USERLOCAL" "R3" 0x7000
    (← execute (← Target.LLVMLift.decodeMIPS32With mips32 0 0 (bytes [0x7c, 0x03, 0xe8, 0x3b])) [word32 "USERLOCAL" 0x7000])
  -- the floating point registers of RISC-V, MIPS, and of the T32 encodings: fadd.d fa0, fa1, fa2 and add.d $f0, $f1, $f2
  let added ← Target.LLVMLift.decodeRISCVWith riscv 0 0 (bytes [0x53, 0xf5, 0xc5, 0x02])
  assertEqual "the double registers of RISC-V lift" "fadd.d fa0, fa1, fa2" added.asm
  let _ ← Target.LLVMLift.decodeRISCV32With riscv32 0 0 (bytes [0x53, 0xf5, 0xc5, 0x02])
  let _ ← Target.LLVMLift.decodeMIPSWith mips 0 0 (bytes [0x46, 0x22, 0x08, 0x00])
  let _ ← Target.LLVMLift.decodeMIPS32With mips32 0 0 (bytes [0x46, 0x24, 0x10, 0x00])
  let thumb ← Target.LLVMLift.thumbEnvironment
  let _ ← Target.LLVMLift.decodeThumbWith thumb 0 0 (bytes [0x31, 0xee, 0x02, 0x0b])
  -- the likely calls lift: bltzall $2, 16, as a call whose slot is annulled when it isn't taken
  let likely ← Target.LLVMLift.decodeMIPSWith mips 0x100 0x100 (bytes [0x04, 0x52, 0, 0x03])
  assertEqual "a likely call is a call" Disasm.Flow.call likely.flow
  assertEqual "a likely call annuls its slot" true (Target.LLVMLift.mipsAnnulsSlot likely)
  assertEqual "a likely call has no slot of a jump" false (Target.LLVMLift.mipsHasDelaySlot likely)
  let (state, taken) ← executeEffect likely [word "R2" 0xffffffffffffffff]
  assertJump "a likely call is taken" 0x110 taken
  assertReg "a likely call links past its slot" "R31" 0x108 state
  let (state, skipped) ← executeEffect likely [word "R2" 1]
  assertNormal "a likely call is not taken" skipped
  assertReg "a likely call always links" "R31" 0x108 state
  let bgezall ← Target.LLVMLift.decodeMIPSWith mips 0x100 0x100 (bytes [0x04, 0x53, 0, 0x03])
  assertEqual "the other likely call annuls its slot" true (Target.LLVMLift.mipsAnnulsSlot bgezall)
  -- XMM0 named directly by the implicit result of pcmpistrm
  let x86 ← Target.LLVMLift.x86Environment
  let _ ← Target.LLVMLift.decodeX86With x86 0 0 (bytes [0x66, 0x0f, 0x3a, 0x62, 0xc1, 0x00])
  let x8632 ← Target.LLVMLift.x8632Environment
  let _ ← Target.LLVMLift.decodeX8632With x8632 0 0 (bytes [0x66, 0x0f, 0x3a, 0x62, 0xc1, 0x00])

/-- The load and store multiple of `arm-a32-multiple.lisp` and of `armMultiple` do the same on real encodings. -/
private def testArmMultipleAgree : IO Unit := do
  let arm ← Target.LLVMLift.arm32Environment
  let context : Primus.Semantics.Context := { bits := 32, memory := thumbMemVar }
  let operand : LLVM.Operand → Primus.Semantics.Value
    | .reg name => .register (if name.isEmpty || name = "NoRegister" then "Nil" else name) 32 32
    | .imm value => .bil 32 (.int (BitVec.ofInt 32 value))
  let names := (List.range 13).map (s!"R{·}") ++ ["SP", "LR", "PC"]
  let initial (zero : Nat) : IO Bil.Env := do
    let mut memory := Memory.empty 32
    for index in List.range 0x100 do
      let address := 0x1000 + index * 4
      match Memory.write memory (BitVec.ofNat 32 address) (BitVec.ofNat 32 (0xa0000000 + address * 3)) .little 4 with
      | .ok updated => memory := updated
      | .error error => throw <| IO.userError error
    pure ((thumbMemVar, .memory memory) :: bit "ZF" zero :: bit "NF" 0 :: bit "CF" 0 :: bit "VF" 0 ::
      (List.range names.length |>.zip names).map fun (index, name) => word32 name (0x1200 + index * 16))
  let observe (state : Bil.State × Bil.Effect) : IO (List Nat × Option Nat) := do
    let registers ← names.mapM fun name =>
      match Bil.lookup state.1.env ⟨name, .imm 32, 0, false⟩ with
      | .ok (.bits value) => pure value.toNat
      | _ => throw <| IO.userError s!"{name} is not a register"
    let cells ← (List.range 0x100).mapM fun index => do
      let address := 0x1000 + index * 4
      pure (((← readByte (width := 32) state.1 thumbMemVar address) +
        (← readByte (width := 32) state.1 thumbMemVar (address + 3)) * 256))
    pure (registers ++ cells, match state.2 with | .jump target => some target.toNat | _ => none)
  -- ldm, stm of the four addressings, with and without writeback, pop, push, conditions, and a load of pc
  let table : List (List Nat) := [
    [0x06, 0x00, 0x90, 0xe8], [0x06, 0x00, 0xb0, 0xe8], [0x06, 0x00, 0x90, 0xe9], [0x06, 0x00, 0xb0, 0xe9],
    [0x06, 0x00, 0x10, 0xe8], [0x06, 0x00, 0x30, 0xe8], [0x06, 0x00, 0x10, 0xe9], [0x06, 0x00, 0x30, 0xe9],
    [0x06, 0x00, 0x80, 0xe8], [0x06, 0x00, 0xa0, 0xe8], [0x06, 0x00, 0x80, 0xe9], [0x06, 0x00, 0xa0, 0xe9],
    [0x06, 0x00, 0x00, 0xe8], [0x06, 0x00, 0x20, 0xe8], [0x06, 0x00, 0x00, 0xe9], [0x06, 0x00, 0x20, 0xe9],
    [0x10, 0x80, 0xbd, 0xe8], [0x10, 0x40, 0x2d, 0xe9], [0x03, 0x00, 0x90, 0xe8], [0x06, 0x00, 0x90, 0x08],
    [0x10, 0x80, 0xbd, 0x18], [0x02, 0x80, 0x80, 0xe8], [0x00, 0x80, 0x90, 0xe8], [0x03, 0x00, 0xa0, 0xe8],
    [0xff, 0xff, 0x90, 0xe8], [0x01, 0x00, 0xbd, 0xe8], [0xf0, 0x5f, 0xbd, 0xe8], [0xf0, 0x5f, 0x2d, 0xe9]]
  for encoding in table do
    let data := bytes encoding
    let decoded ← LLVM.disassemble "armv7" data 0
    let lifted ← Target.LLVMLift.decodeARM32With arm 0 0 data
    let semantics ← Primus.Semantics.liftWith arm { context with nextPc := 4 } decoded.opcode (decoded.operands.map operand)
    for zero in [0, 1] do
      let env ← initial zero
      let first ← executeEffect lifted env
      let second ← match Bil.run semantics { env := env } with
        | .ok result => pure result
        | .error error => throw <| IO.userError error
      assertEqual s!"{decoded.opcode} does the same in both, ZF={zero}" (← observe first) (← observe second)

def run : IO Unit := do
  testStatusRegisters
  testArmMultipleAgree
  testX86Repeat
  testX86Registers
  testArmVfpRegisters
  testPowerPCFields
  testX86Sse
  testRiscvRem
  testPcWrites
  testWrappedTargets
  testVectorRegisters
  testThumbNarrow
  testThumbIt
  testBranches
  testPartialRegisters
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
  assertJump "LLVM lifted ARM32 BEQ taken" 24 armBranchTaken
  assertEqual "LLVM ARM32 branch metadata" (some 24) armBranchInsn.target
  let (_, armBranchNotTaken) ← executeEffect armBranchInsn [(armZ, .bits (BitVec.ofNat 1 0))]
  assertNormal "LLVM lifted ARM32 BEQ not taken" armBranchNotTaken
  let armLinkInsn ← decodeARM32 (← LLVM.assemble "armv7" "bl 16")
  let (armLinkState, armLinkEffect) ← executeEffect armLinkInsn
  assertReg32 "LLVM lifted ARM32 BL link" "LR" 4 armLinkState
  assertJump "LLVM lifted ARM32 BL target" 24 armLinkEffect
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
  assertJump "LLVM lifted Thumb BEQ taken" 20 thumbBranchTaken
  assertEqual "LLVM Thumb branch metadata" (some 20) thumbBranchInsn.target
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
