import BapTests.Support

namespace Bap.Tests.Theory

open Bap
open Bap.Theory

private def reg (name : String) (width : Nat) : Theory.Var := ⟨name, .bitv width, 0, false⟩
private def flag (name : String) : Theory.Var := ⟨name, .bool, 0, false⟩
private def rax := reg "RAX" 64
private def eax := reg "EAX" 32
private def ax := reg "AX" 16
private def upper := reg "UPPER" 32
private def of := flag "OF"
private def cf := flag "CF"

private def convention (arch : Image.Arch) : IO ABI.Convention :=
  match ABI.convention arch with
  | some convention => pure convention
  | none => throw <| IO.userError "missing target ABI"

private def parent : Target := declare {
  name := "x86"
  bits := some 16
  byte := some 8
  vars := some [rax, eax, ax, upper, of, cf]
  regs := some [([.general], [rax])]
  endianness := some .le
  system := some .linux
}

private def child : Target := declare {
  name := "x86_64"
  parent := some parent
  nicknames := ["amd64", "x64"]
  bits := some 64
  aliases := some [
    ⟨rax, [.reg upper, .reg eax]⟩,
    ⟨eax, [.reg ax]⟩,
    ⟨reg "RFLAGS" 64, [.bit of, .bit cf]⟩
  ]
}

def run : IO Unit := do
  assertEqual "target width override" 64 child.bits
  assertEqual "target byte inheritance" 8 child.byte
  assertEqual "target system inheritance" SystemKind.linux child.system
  assertEqual "target endianness inheritance" Endianness.le child.endianness
  assertTrue "case-insensitive nickname" (child.matches "X64")
  assertTrue "target family membership" (parent.belongs child)
  assertTrue "unknown is the implicit root" (unknown.belongs parent)
  assertTrue "unknown is an ancestor of grandchildren" (unknown.belongs child)
  assertEqual "target parents end at unknown" ["x86", "unknown"] child.parents
  assertEqual "root inherits unknown width" 32 (declare { name := "bare" }).bits
  assertEqual "root inherits unknown endianness" Endianness.eb (declare { name := "bare" }).endianness
  let multiRole : Target := declare {
    name := "roles"
    regs := some [([.general], [rax]), ([.integer], [rax]), ([.general], [eax])]
  }
  assertTrue "roles may come from different groups" (multiRole.hasRoles [.general, .integer] rax)
  assertEqual "missing role is rejected" false (multiRole.hasRoles [.general, .integer] eax)
  assertEqual "absent variable has no role" false (multiRole.hasRoles [.general] of)
  assertTrue "empty role list holds vacuously" (multiRole.hasRoles [] of)
  assertEqual "register role query" [rax] (child.registers [.general])
  assertEqual "register exclusion" [] (child.registers [] [.general])
  assertEqual "unique register query" (some rax) (child.reg .general true)
  assertEqual "alias subregister range" (some (.sub rax 31 0 false)) (child.unalias eax)
  assertEqual "nested alias range" (some (.sub eax 15 0 true)) (child.unalias ax)
  assertEqual "alias superregister" (some (.sup [upper, eax])) (child.unalias rax)
  assertEqual "flag bit range" (some (.sub (reg "RFLAGS" 64) 0 0 false)) (child.unalias cf)
  assertEqual "flag set" (some (.set [of, cf])) (child.unalias (reg "RFLAGS" 64))
  let registry := register child [parent]
  assertEqual "registry nickname lookup" (some child) (get "amd64" registry)
  assertEqual "non-strict system selection" (some child)
    (select { parent := some child, system := some .linux, unique := true } registry)
  assertEqual "strict inherited system rejected" none
    (select { system := some .linux, strict := true, unique := true } [child])
  assertEqual "strict explicit system accepted" (some parent)
    (select { system := some .linux, strict := true, unique := true } [parent])
  assertEqual "unique selection rejects ambiguity" none
    (select { parent := some parent, unique := true } registry)
  let value := Theory.Value.bits (BitVec.ofNat 32 42)
  assertEqual "Core Theory value sort" (ValueSort.bitv 32) value.sort
  assertEqual "value resort accepts same sort" (some (ValueSort.bitv 32)) (value.resort (.bitv 32) |>.map Theory.Value.sort)
  assertEqual "value resort rejects other sort" none (value.resort (.bitv 64) |>.map Theory.Value.sort)
  assertEqual "bottom effect order" Effect.PartialOrder.less (Effect.EffectSort.order .bot Effect.rreg)
  let readWrite := Effect.EffectSort.both Effect.rreg Effect.wreg
  let writeRead := Effect.EffectSort.both Effect.wreg Effect.rreg
  assertEqual "effect order ignores atom order" Effect.PartialOrder.equal
    (Effect.EffectSort.order readWrite writeRead)
  assertEqual "empty join equals bottom" Effect.PartialOrder.equal
    (Effect.EffectSort.order (Effect.EffectSort.join [] []) .bot)
  assertEqual "top absorbs both" Effect.PartialOrder.equal
    (Effect.EffectSort.order (.both .top Effect.rreg) .top)
  assertEqual "effects below top" Effect.PartialOrder.less
    (Effect.EffectSort.order readWrite (.both Effect.rreg .top))
  assertEqual "combined effect order" Effect.PartialOrder.less
    (Effect.EffectSort.order Effect.rreg (.both Effect.rreg Effect.wreg))
  assertEqual "independent effects unordered" Effect.PartialOrder.unordered
    (Effect.EffectSort.order Effect.rreg Effect.wreg)
  let amd64 ← convention .x86_64
  assertEqual "x86-64 first argument register"
    (ABI.Location.register ⟨"RDI", .imm 64, 0, false⟩) (ABI.argumentLocation amd64 0)
  assertEqual "x86-64 sixth argument register"
    (ABI.Location.register ⟨"R9", .imm 64, 0, false⟩) (ABI.argumentLocation amd64 5)
  assertEqual "x86-64 seventh argument uses stack" (ABI.Location.stack 0) (ABI.argumentLocation amd64 6)
  assertEqual "x86-64 eighth argument stack offset" (ABI.Location.stack 8) (ABI.argumentLocation amd64 7)
  assertEqual "x86-64 stack pointer" "RSP" amd64.stackPointer.name
  assertEqual "x86-64 return address is on stack" none amd64.returnAddress
  assertEqual "x86-64 syscall register" (some "R10") ((amd64.syscallArguments.map Bap.Var.name)[3]?)
  let rv ← convention .riscv
  assertEqual "RISC-V has eight function arguments" 8 rv.functionArguments.length
  assertEqual "RISC-V has six syscall arguments" 6 rv.syscallArguments.length
  assertEqual "RISC-V syscall number register" "X17" rv.syscallNumber.name
  assertEqual "RISC-V result register" "X10" rv.result.name
  assertEqual "RISC-V return register" (some "X1") (rv.returnAddress.map Bap.Var.name)
  let arm64 ← convention .aarch64
  assertEqual "AArch64 argument register" (some "X0") (arm64.functionArguments.head?.map Bap.Var.name)
  assertEqual "AArch64 syscall number register" "X8" arm64.syscallNumber.name
  assertEqual "AArch64 stack alignment" 32 (ABI.alignStack 16 33)
  let mips ← convention .mips
  assertEqual "MIPS result register" "R2" mips.result.name
  assertEqual "MIPS n64 fifth argument register"
    (ABI.Location.register ⟨"R8", .imm 64, 0, false⟩) (ABI.argumentLocation mips 4)
  assertEqual "MIPS n64 ninth argument uses stack" (ABI.Location.stack 0) (ABI.argumentLocation mips 8)
  match ABI.convention .mips 32 with
  | some mips32 =>
    assertEqual "MIPS o32 fifth argument uses stack" (ABI.Location.stack 0)
      (ABI.argumentLocation mips32 4)
  | none => throw <| IO.userError "missing MIPS o32 ABI"
  let i386 ← convention .x86
  assertEqual "x86 word size" 32 i386.wordSize
  assertEqual "x86 stack slots are words" (ABI.Location.stack 4) (ABI.argumentLocation i386 1)
  let arm ← convention .arm
  assertEqual "ARM syscall number register" "R7" arm.syscallNumber.name
  assertEqual "ARM return register" (some "LR") (arm.returnAddress.map Bap.Var.name)
  assertEqual "ARM stack pointer" "SP" arm.stackPointer.name
  let ppc ← convention .powerpc
  assertEqual "PowerPC result register" "R3" ppc.result.name
  assertEqual "PowerPC stack pointer" "R1" ppc.stackPointer.name
  match API.parseHeader "int/* no space */add(int/**/x);" with
  | .ok [glued] =>
    assertEqual "API comment separates tokens, name" "add" glued.name
    assertEqual "API comment separates tokens, parameter" ["x"] (glued.params.map API.Parameter.name)
  | _ => throw <| IO.userError "a comment did not separate the tokens"
  let header := "/* API fixture */\nint add(int x, int y);\nvoid *malloc(size_t size);\nint printf(const char *fmt, ...);\n"
  IO.FS.writeFile "native/build/api-test.h" header
  let prototypes ← API.load "native/build/api-test.h"
  match prototypes with
  | [add, malloc, printf] =>
    assertEqual "API function name" "add" add.name
    assertEqual "API integer result" (API.CType.named "int") add.result
    assertEqual "API parameter names" ["x", "y"] (add.params.map API.Parameter.name)
    assertEqual "API pointer result" (API.CType.pointer (.named "void")) malloc.result
    assertTrue "API variadic marker" printf.variadic
    assertEqual "API variadic parameter" ["fmt"] (printf.params.map API.Parameter.name)
    assertEqual "API const pointer parameter" [API.CType.pointer (.named "const char")] (printf.params.map API.Parameter.typ)
    assertEqual "API maps parameters to ABI"
      [ABI.Location.register ⟨"RDI", .imm 64, 0, false⟩, ABI.Location.register ⟨"RSI", .imm 64, 0, false⟩]
      (API.argumentLocations amd64 add)
  | _ => throw <| IO.userError "API header did not produce three prototypes"

end Bap.Tests.Theory
