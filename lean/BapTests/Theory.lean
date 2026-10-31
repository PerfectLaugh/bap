import BapTests.Support

namespace Bap.Tests.Theory

open Bap
open Bap.Theory

private def reg (name : String) (width : Nat) : Theory.Var := ⟨name, .bitv width, 0, false, false⟩
private def flag (name : String) : Theory.Var := ⟨name, .bool, 0, false, false⟩
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
  nicknames := some ["amd64", "x64"]
  bits := some 64
}

private def ah := reg "AH" 8
private def al := reg "AL" 8
private def flags := reg "FLAGS" 2
private def status := reg "STATUS" 2

/-- The check that discharges `Free` for a concrete table, on the examples. -/
private def resolving : IO Unit := do
  let table := Proofs.Theory.TargetLaws.X86Table.table
  assertTrue "the table of RAX resolves" table.resolves
  assertEqual "the table of RAX has nothing to report" true (match table.validate with | .ok _ => true | .error _ => false)
  let general (name : String) (width : Nat) : Theory.Var := ⟨name, .bitv width, 0, false, false⟩
  -- two registers that share a part: the equations make bits of the basis equal, and `declare` stays total
  let shared : Target := declare {
    name := "shared"
    regs := some [([.general], [general "A" 16, general "B" 16]), ([.alias], [general "HI" 8, general "LA" 8, general "LB" 8])]
    aliases := some [⟨general "A" 16, [.reg (general "HI" 8), .reg (general "LA" 8)]⟩,
      ⟨general "B" 16, [.reg (general "HI" 8), .reg (general "LB" 8)]⟩] }
  assertEqual "a table that makes bits of the basis equal doesn't resolve" false shared.resolves
  assertEqual "it makes the eight high bits of its registers equal" 8 shared.conflicts.length
  assertEqual "validate reports the first pair"
    (some "the aliases of shared are overdetermined: they make bit 8 of A and bit 8 of B equal")
    (match shared.validate with | .ok _ => none | .error message => some message)
  -- equations between aliases only say nothing of the basis, which the search found no end for
  let closed : Target := declare {
    name := "closed"
    regs := some [([.alias], [general "X" 8, general "Y" 8])]
    aliases := some [⟨general "X" 8, [.reg (general "Y" 8)]⟩] }
  assertEqual "aliases without a basis leave the basis free" true closed.resolves
  -- a lookup through the classes is linear in the equations: a full 64-bit table of nested halves takes no time
  let nestedRegs := (List.range 8).flatMap fun i =>
    [general s!"R{i}" 64, general s!"E{i}" 32, general s!"U{i}" 32, general s!"W{i}" 16, general s!"H{i}" 8, general s!"L{i}" 8]
  let wide : Target := declare {
    name := "wide"
    regs := some [([.general], (List.range 8).map fun i => general s!"R{i}" 64), ([.alias], nestedRegs.filter fun reg => reg.sort != .bitv 64)]
    aliases := some ((List.range 8).flatMap fun i =>
      [⟨general s!"R{i}" 64, [.reg (general s!"U{i}" 32), .reg (general s!"E{i}" 32)]⟩,
       ⟨general s!"E{i}" 32, [.unknown, .reg (general s!"W{i}" 16)]⟩,
       ⟨general s!"W{i}" 16, [.reg (general s!"H{i}" 8), .reg (general s!"L{i}" 8)]⟩]) }
  let start ← IO.monoMsNow
  assertEqual "a table of eight 64-bit registers resolves" true wide.resolves
  let elapsed := (← IO.monoMsNow) - start
  assertTrue s!"and at once ({elapsed} ms)" (elapsed < 5000)
  assertEqual "AH in RAX" (some (.sub Proofs.Theory.TargetLaws.X86Table.rax 15 8 false))
    (table.unalias Proofs.Theory.TargetLaws.X86Table.ah)

/-- The example of upstream's documentation of `Origin`, with a flag register of each direction. -/
private def nested : Target := declare {
  name := "nested"
  regs := some [([.general], [rax]), ([.alias], [upper, eax, ax, ah, al, flags, cf])]
  aliases := some [
    ⟨rax, [.reg upper, .reg eax]⟩,
    ⟨eax, [.unknown, .reg ax]⟩,
    ⟨ax, [.reg ah, .reg al]⟩,
    ⟨flags, [.bit of, .bit (flag "ZF")]⟩,
    ⟨status, [.unknown, .bit cf]⟩
  ]
}

private def r25 := reg "r25" 8
private def r24 := reg "r24" 8
private def r25r24 := reg "r25r24" 16
private def w := reg "w" 16
private def whi := reg "whi" 8
private def wlo := reg "wlo" 8

/-- The example of upstream's documentation of `Alias`: equations hold in either direction. -/
private def equations : Target := declare {
  name := "equations"
  regs := some [([.general], [r25, r24]), ([.alias], [r25r24, w, whi, wlo])]
  aliases := some [⟨r25r24, [.reg r25, .reg r24]⟩, ⟨w, [.reg r25r24]⟩, ⟨w, [.reg whi, .reg wlo]⟩]
}

private def aliasing (regs : List Theory.Var) (aliases : List Alias) : Target :=
  declare { name := "aliasing", regs := some [([.alias], regs)], aliases := some aliases }

def run : IO Unit := do
  resolving
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
  assertEqual "several roles select the intersection" [rax] (multiRole.registers [.general, .integer])
  assertEqual "a single role selects all its registers" [rax, eax] (multiRole.registers [.general])
  assertEqual "exclusion applies across groups" [eax] (multiRole.registers [.general] [.integer])
  assertEqual "reg honours exclusion" (some eax) (multiRole.reg .general true [.integer])
  assertEqual "reg stays ambiguous without exclusion" none (multiRole.reg .general true)
  assertEqual "whole-register alias is an alias" (some (.sub eax 31 0 true))
    ((aliasing [reg "E" 32] [⟨eax, [.reg (reg "E" 32)]⟩]).unalias (reg "E" 32))
  assertEqual "missing role is rejected" false (multiRole.hasRoles [.general, .integer] eax)
  assertEqual "absent variable has no role" false (multiRole.hasRoles [.general] of)
  assertTrue "empty role list holds vacuously" (multiRole.hasRoles [] of)
  assertEqual "register role query" [rax] (child.registers [.general])
  assertEqual "register exclusion" [] (child.registers [] [.general])
  assertEqual "unique register query" (some rax) (child.reg .general true)
  assertEqual "alias subregister range" (some (.sub rax 31 0 false)) (nested.unalias eax)
  assertEqual "alias of the high half" (some (.sub rax 63 32 false)) (nested.unalias upper)
  assertEqual "nested alias resolved to original register" (some (.sub rax 15 0 false)) (nested.unalias ax)
  assertEqual "nested high byte adds offsets" (some (.sub rax 15 8 false)) (nested.unalias ah)
  assertEqual "nested low byte" (some (.sub rax 7 0 false)) (nested.unalias al)
  assertEqual "a basis register has no origin" none (nested.unalias rax)
  assertEqual "flag bit range" (some (.sub status 0 0 false)) (nested.unalias cf)
  assertEqual "flag set" (some (.set [of, flag "ZF"])) (nested.unalias flags)
  assertEqual "a flag of the basis has no origin" none (nested.unalias of)
  assertEqual "concatenation of basis registers" (some (.sup [r25, r24])) (equations.unalias r25r24)
  assertEqual "alias of a concatenation" (some (.sup [r25, r24])) (equations.unalias w)
  assertEqual "part of an alias is a synonym of a basis register" (some (.sub r25 7 0 true)) (equations.unalias whi)
  assertEqual "other part of an alias" (some (.sub r24 7 0 true)) (equations.unalias wlo)
  assertEqual "a register above an unknown part" (some (.sub rax 63 32 false))
    ((aliasing [upper] [⟨rax, [.reg upper, .unknown]⟩]).unalias upper)
  assertEqual "parts must add up to the register" none ((aliasing [ax] [⟨eax, [.reg ax]⟩]).unalias ax)
  assertEqual "an alias wider than its only part has no origin" none
    ((aliasing [eax] [⟨eax, [.unknown, .reg ax]⟩]).unalias eax)
  assertEqual "an alias across basis registers has no origin" none
    ((aliasing [r25r24, whi] [⟨r25r24, [.reg r25, .reg r24]⟩, ⟨r25r24, [.unknown, .reg whi, .unknown]⟩]).unalias whi)
  assertEqual "equations without an alias role have no solution" none
    ((declare { name := "unmarked", aliases := some [⟨rax, [.reg upper, .reg eax]⟩] }).unalias eax)
  assertEqual "a cycle of aliases has no origin" none
    ((aliasing [r25, r24] [⟨r25, [.reg r24]⟩, ⟨r24, [.reg r25]⟩]).unalias r25)
  let registry := register child [parent]
  assertEqual "registry lookup by name" (some child) (get "x86_64" registry)
  assertEqual "registry lookup is not by nickname" none (get "amd64" registry)
  assertEqual "registry lookup is not by ancestor" none (get "x86" [child])
  assertEqual "registry lookup is exact" none (get "X86_64" registry)
  assertEqual "matching finds own nickname" (some "x86_64") (child.matching "AMD64")
  assertEqual "matching finds closest ancestor" (some "x86") (child.matching "x86")
  assertEqual "matching finds nothing" none (child.matching "arm")
  assertTrue "matches walks to unknown" (child.matches "unknown")
  let tagged : Target := declare { name := "base", nicknames := some ["family"] }
  let inheriting : Target := declare { name := "middle", parent := some tagged }
  let leaf : Target := declare { name := "leaf", parent := some inheriting, nicknames := some ["other"] }
  assertEqual "nicknames inherited when none given" ["family"] inheriting.nicknames
  assertEqual "nicknames replaced when given" ["other"] leaf.nicknames
  assertEqual "ancestor nicknames still match" (some "middle") (leaf.matching "family")
  assertEqual "non-strict system selection" (some child)
    (select { parent := child, system := .linux, unique := true } registry)
  assertEqual "strict inherited system accepted" (some child)
    (select { system := .linux, strict := true, unique := true } [child])
  assertEqual "strict explicit system accepted" (some parent)
    (select { system := .linux, strict := true, unique := true } [parent])
  assertEqual "strict other system rejected" none
    (select { system := .darwin, strict := true } [child])
  assertEqual "strict unknown requires unknown" none
    (select { strict := true } [child])
  assertEqual "unique selection rejects ambiguity" none
    (select { parent := parent, unique := true } registry)
  assertEqual "unknown property fails a specific requirement" none
    (select { abi := .gnu } [child])
  assertEqual "unknown requirement accepts any property" (some child)
    (select { system := .unknown, unique := true } [child])
  assertEqual "selection never returns unknown" none (select {} [unknown])
  assertEqual "unknown has no system" SystemKind.unknown unknown.system
  assertEqual "unknown has no abi" Abi.unknown unknown.abi
  assertEqual "unknown has no fabi" Fabi.unknown unknown.fabi
  assertEqual "unknown has no filetype" Filetype.unknown unknown.filetype
  assertEqual "bare declaration inherits unknown abi" Abi.unknown (declare { name := "bare" }).abi
  assertTrue "declared registers are variables" (rax ∈ (declare { name := "vs", regs := some [([.general], [rax])] }).vars)
  assertTrue "memories are variables" ((declare { name := "bare" }).var "mem" |>.isSome)
  let bound : Theory.Var := { name := "x", sort := .bool, isVirtual := true, isLet := true }
  let temporary : Theory.Var := { name := "t", sort := .bool, isVirtual := true }
  assertEqual "scoped variable is immutable" false bound.isMutable
  assertEqual "scoped variable has no versions" bound (bound.version 3)
  assertEqual "temporary variable is mutable" true temporary.isMutable
  assertEqual "temporary variable has versions" 3 (temporary.version 3).index
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
    assertEqual "MIPS o32 fifth argument is above the home area" (ABI.Location.stack 16)
      (ABI.argumentLocation mips32 4)
    assertEqual "MIPS o32 sixth argument follows it" (ABI.Location.stack 20) (ABI.argumentLocation mips32 5)
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
