import BapTests.Support

namespace Bap.Tests.AArch64

open Bap
open Bap.Disasm

private def instruction (word : Nat) : ByteArray :=
  ByteArray.mk (List.range 4 |>.map (fun index => UInt8.ofNat (word / 256 ^ index % 256)) |>.toArray)

private def decodeWith (disassembler : Disassembler) (word : Nat) : IO Insn := do
  match ← disassembler.decode 0 (instruction word) with
  | .ok insn => pure insn
  | .error error => throw <| IO.userError error

private def reg (index : Nat) : Bap.Var := ⟨s!"X{index}", .imm 64, 0, false⟩

private def executeEffect (insn : Insn) (env : Bil.Env := []) : IO (Bil.State × Bil.Effect) :=
  match Bil.run insn.bil { env := env } with
  | .ok result => pure result
  | .error error => throw <| IO.userError error

private def execute (insn : Insn) (env : Bil.Env := []) : IO Bil.State := do
  let (state, _) ← executeEffect insn env
  pure state

private def assertReg (label : String) (index expected : Nat) (state : Bil.State) : IO Unit :=
  match Bil.lookup state.env (reg index) with
  | .ok (.bits value) => assertEqual label expected value.toNat
  | .ok _ => throw <| IO.userError "register is not a bitvector"
  | .error error => throw <| IO.userError error

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

def run : IO Unit := do
  let decode := decodeWith (← Target.AArch64.disassembler 0)
  let nop ← decode 0xd503201f
  assertEqual "AArch64 nop assembly" "nop" nop.asm
  assertEqual "AArch64 instruction size" 4 nop.size
  let movz ← decode 0xd2824680
  assertTrue "AArch64 MOVZ assembly"
    (movz.asm.startsWith "movz x0," || movz.asm.startsWith "mov x0,")
  let movzState ← execute movz
  assertReg "AArch64 MOVZ BIL" 0 0x1234 movzState
  let movz32 ← decode 0x529fffe0
  let movz32State ← execute movz32 [(reg 0, .bits (BitVec.ofNat 64 0xffffffffffffffff))]
  assertReg "AArch64 32-bit write zero extension" 0 0xffff movz32State
  let add ← decode 0x91000400
  assertTrue "AArch64 ADD assembly" (add.asm.startsWith "add x0,")
  let addState ← execute add [(reg 0, .bits (BitVec.ofNat 64 2))]
  assertReg "AArch64 ADD BIL" 0 3 addState
  let sub ← decode 0xd1000400
  let subState ← execute sub [(reg 0, .bits (BitVec.ofNat 64 3))]
  assertReg "AArch64 SUB BIL" 0 2 subState
  let memory ← match Memory.write (Memory.empty 64) (BitVec.ofNat 64 0x1008)
    (BitVec.ofNat 64 0x1234) .little 8 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  let ldr ← decode 0xf9400420
  assertTrue "AArch64 LDR assembly" (ldr.asm.startsWith "ldr x0,")
  let ldrState ← execute ldr [(reg 0, .bits (BitVec.ofNat 64 0xffffffffffffffff)),
    (reg 1, .bits (BitVec.ofNat 64 0x1000)), (memVar, .memory memory)]
  assertReg "AArch64 LDR BIL" 0 0x1234 ldrState
  let ldr32 ← decode 0xb9400820
  let ldr32State ← execute ldr32 [(reg 0, .bits (BitVec.ofNat 64 0xffffffffffffffff)),
    (reg 1, .bits (BitVec.ofNat 64 0x1000)), (memVar, .memory memory)]
  assertReg "AArch64 32-bit LDR zero extension" 0 0x1234 ldr32State
  let signedMemory ← match Memory.write (Memory.empty 64) (BitVec.ofNat 64 0x1063)
    (BitVec.ofNat 32 0xfffffff6) .little 4 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  let ldtrsw ← decode 0xb8963b0c
  assertTrue "AArch64 LDTRSW assembly" (ldtrsw.asm.startsWith "ldtrsw")
  let ldtrswState ← execute ldtrsw [(reg 24, .bits (BitVec.ofNat 64 0x1100)),
    (memVar, .memory signedMemory)]
  assertReg "AArch64 LDTRSW sign extension" 12 0xfffffffffffffff6 ldtrswState
  assertReg "AArch64 LDTRSW preserves base" 24 0x1100 ldtrswState
  let str ← decode 0xf9000420
  assertTrue "AArch64 STR assembly" (str.asm.startsWith "str x0,")
  let strState ← execute str [(reg 0, .bits (BitVec.ofNat 64 0x5678)),
    (reg 1, .bits (BitVec.ofNat 64 0x1000)), (memVar, .memory memory)]
  assertMemory "AArch64 STR BIL" 0x1008 0x5678 strState
  let branch ← decode 0x14000000
  let (_, branchEffect) ← executeEffect branch
  assertJump "AArch64 B target" 0 branchEffect
  let link ← decode 0x94000000
  let (linkState, linkEffect) ← executeEffect link
  assertReg "AArch64 BL link register" 30 4 linkState
  assertJump "AArch64 BL target" 0 linkEffect
  let ret ← decode 0xd65f03c0
  let (_, retEffect) ← executeEffect ret [(reg 30, .bits (BitVec.ofNat 64 0x1234))]
  assertJump "AArch64 RET target" 0x1234 retEffect
  let data := instruction 0xd503201f
  let image : Image.Image := {
    arch := .aarch64
    addrWidth := 64
    endian := .little
    entryPoint := 0
    data := data
    memory := Image.MemoryMap.add ⟨0, data, true, false, true⟩ () {}
  }
  let project ← Project.Project.fromImage image
  assertTrue "AArch64 project is disassembled" project.disassembled
  match project.disasm with
  | some disasm => assertEqual "AArch64 project instruction count" 1 disasm.instructions.length
  | none => throw <| IO.userError "missing AArch64 disassembly"

end Bap.Tests.AArch64
