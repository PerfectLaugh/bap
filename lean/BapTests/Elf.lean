import BapTests.Support

namespace Bap.Tests.Elf

open Bap
open Bap.Image

private def appendNat (bytes : ByteArray) (value size : Nat) : ByteArray :=
  (List.range size).foldl (init := bytes) fun result index =>
    result.push (UInt8.ofNat (value / 256 ^ index % 256))

private def fixture : ByteArray :=
  let b := appendNat ByteArray.empty 0x464c457f 4
  let b := appendNat b 2 1
  let b := appendNat b 1 1
  let b := appendNat b 1 1
  let b := appendNat b 0 9
  let b := appendNat b 2 2
  let b := appendNat b 62 2
  let b := appendNat b 1 4
  let b := appendNat b 0x400000 8
  let b := appendNat b 64 8
  let b := appendNat b 0 8
  let b := appendNat b 0 4
  let b := appendNat b 64 2
  let b := appendNat b 56 2
  let b := appendNat b 1 2
  let b := appendNat b 0 6
  let b := appendNat b 1 4
  let b := appendNat b 5 4
  let b := appendNat b 120 8
  let b := appendNat b 0x400000 16
  let b := appendNat b 4 8
  let b := appendNat b 8 8
  let b := appendNat b 0x1000 8
  b.push 0xc3 |>.push 0x90 |>.push 0x90 |>.push 0x90

def run : IO Unit := do
  assertEqual "ELF fixture size" 124 fixture.size
  match Elf.decode fixture with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "ELF sectionless architecture" Arch.x86_64 image.arch
    assertEqual "ELF sectionless entry" 0x400000 image.entryPoint
    assertEqual "ELF sectionless sections" 0 image.sections.length
    assertEqual "ELF sectionless symbols" 0 image.symbols.length
    assertEqual "ELF PT_LOAD count" 1 image.segments.length
    assertEqual "ELF mapped file byte" (some 0xc3) (image.memory.readByte 0x400000)
    assertEqual "ELF zero-filled byte" (some 0) (image.memory.readByte 0x400004)
    assertEqual "ELF final zero-filled byte" (some 0) (image.memory.readByte 0x400007)
    assertEqual "ELF virtual memory end" none (image.memory.readByte 0x400008)
    match image.segments[0]? with
    | some segment =>
      assertEqual "ELF virtual segment size" 8 segment.size
      assertEqual "ELF segment permissions" (true, false, true)
        (segment.readable, segment.writable, segment.executable)
    | none => throw <| IO.userError "missing ELF LOAD segment"
  let host ← Elf.load "/bin/echo"
  assertEqual "host ELF filters non-LOAD headers" 3 host.segments.length
  assertEqual "host ELF zero-filled BSS" (some 0) (host.memory.readByte 0x900c)
  match Elf.dynamicRelocations host with
  | .error error => throw <| IO.userError error
  | .ok relocations =>
    assertTrue "host ELF has named dynamic references" (!relocations.references.isEmpty)
    assertTrue "host ELF has relative dynamic relocations" (!relocations.relative.isEmpty)
    match Elf.imports host relocations 0x700000 with
    | .error error => throw <| IO.userError error
    | .ok imports =>
      assertTrue "host ELF has linked imports" (!imports.isEmpty)
      assertEqual "host ELF import addresses are sequential" (some 0x700000) (imports.head?.map (·.address))

end Bap.Tests.Elf
