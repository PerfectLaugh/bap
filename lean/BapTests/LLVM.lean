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

def run : IO Unit := do
  testRiscvRem
  testPcWrites
  testWrappedTargets
  testVectorRegisters
  testThumbNarrow
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
