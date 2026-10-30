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

private def appendBig (bytes : ByteArray) (value size : Nat) : ByteArray :=
  (List.range size).foldl (init := bytes) fun result index =>
    result.push (UInt8.ofNat (value / 256 ^ (size - index - 1) % 256))

private def appendString (bytes : ByteArray) (value : String) : ByteArray :=
  (value.toUTF8.foldl (init := bytes) fun result byte => result.push byte).push 0

/-- The 52-byte header of an ELF32 file, with `e_phoff` and `e_shoff` distinct from what surrounds them. -/
private def elf32Header (append : ByteArray → Nat → Nat → ByteArray) (encoding typ machine entry phoff shoff phnum
    shnum shstrndx : Nat) : ByteArray :=
  let b := appendNat ByteArray.empty 0x464c457f 4
  let b := appendNat b 1 1
  let b := appendNat b encoding 1
  let b := appendNat b 1 1
  let b := appendNat b 0 9
  let b := append b typ 2
  let b := append b machine 2
  let b := append b 1 4
  let b := append b entry 4
  let b := append b phoff 4
  let b := append b shoff 4
  let b := append b 0 4
  let b := append b 52 2
  let b := append b 32 2
  let b := append b phnum 2
  let b := append b 40 2
  let b := append b shnum 2
  append b shstrndx 2

private def elf32Program (append : ByteArray → Nat → Nat → ByteArray) (bytes : ByteArray)
    (kind offset vaddr paddr fileSize memorySize flags : Nat) : ByteArray :=
  let b := append bytes kind 4
  let b := append b offset 4
  let b := append b vaddr 4
  let b := append b paddr 4
  let b := append b fileSize 4
  let b := append b memorySize 4
  let b := append b flags 4
  append b 0x1000 4

private def elf32Section (bytes : ByteArray) (name kind addr offset size link entrySize : Nat) : ByteArray :=
  let b := appendNat bytes name 4
  let b := appendNat b kind 4
  let b := appendNat b 0 4
  let b := appendNat b addr 4
  let b := appendNat b offset 4
  let b := appendNat b size 4
  let b := appendNat b link 4
  let b := appendNat b 0 4
  let b := appendNat b 4 4
  appendNat b entrySize 4

/-- An ARM ELF32: one LOAD, a Thumb function in `.symtab`, section names in `.shstrtab`. -/
private def elf32Fixture : ByteArray :=
  let b := elf32Header appendNat 1 2 40 0x8000 52 180 1 4 3
  let b := elf32Program appendNat b 1 84 0x8000 0x9000 4 8 5
  let b := b.push 0xc3 |>.push 0x90 |>.push 0x90 |>.push 0x90
  let b := appendNat b 0 16
  let b := appendNat b 1 4
  let b := appendNat b 0x8001 4
  let b := appendNat b 4 4
  let b := appendNat b 0x12 1
  let b := appendNat b 0 1
  let b := appendNat b 1 2
  let b := appendString (appendNat b 0 1) "f"
  let b := appendString (appendNat b 0 1) ".symtab"
  let b := appendString b ".shstrtab"
  let b := appendNat b 0 (180 - b.size)
  let b := appendNat b 0 40
  let b := elf32Section b 1 2 0 88 32 2 16
  let b := elf32Section b 0 3 0 120 3 0 0
  elf32Section b 9 3 0 123 19 0 0

/-- A big-endian ELF32 with a BSS, whose fields only agree if read at their own offsets. -/
private def elf32BigFixture : ByteArray :=
  let b := elf32Header appendBig 2 2 8 0x400000 52 0 1 0 0
  let b := elf32Program appendBig b 1 84 0x400000 0x500000 4 16 6
  b.push 0xde |>.push 0xad |>.push 0xbe |>.push 0xef

/-- An i386 ELF32 with REL dynamic relocations: a relative one and an `R_386_32` with a stored addend. -/
private def elf32DynamicFixture : ByteArray :=
  let b := elf32Header appendNat 1 3 3 0 52 0 2 0 0
  let b := elf32Program appendNat b 1 0 0 0 223 223 6
  let b := elf32Program appendNat b 2 116 116 116 48 48 6
  let b := [(17, 164), (18, 16), (6, 180), (5, 220), (10, 3), (0, 0)].foldl (init := b) fun result entry =>
    appendNat (appendNat result entry.1 4) entry.2 4
  let b := appendNat (appendNat b 212 4) 8 4
  let b := appendNat (appendNat b 216 4) 0x101 4
  let b := appendNat b 0 16
  let b := appendNat b 1 4
  let b := appendNat b 0x100 4
  let b := appendNat b 4 4
  let b := appendNat b 0x11 1
  let b := appendNat b 0 1
  let b := appendNat b 1 2
  let b := appendNat (appendNat b 0x50 4) 4 4
  appendString (appendNat b 0 1) "x"

/-- An ELF64 relocatable header, which has no program headers and so `e_phentsize = 0`. -/
private def elf64ObjectFixture : ByteArray :=
  let b := appendNat ByteArray.empty 0x464c457f 4
  let b := appendNat b 2 1
  let b := appendNat b 1 1
  let b := appendNat b 1 1
  let b := appendNat b 0 9
  let b := appendNat b 1 2
  let b := appendNat b 62 2
  let b := appendNat b 1 4
  let b := appendNat b 0 28
  let b := appendNat b 64 2
  let b := appendNat b 0 4
  let b := appendNat b 64 2
  appendNat b 0 4

private def runElf32 : IO Unit := do
  match Elf.decode elf32Fixture with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "ELF32 architecture" Arch.arm image.arch
    assertEqual "ELF32 address width" 32 image.addrWidth
    assertEqual "ELF32 entry" 0x8000 image.entryPoint
    assertEqual "ELF32 mapped file byte" (some 0xc3) (image.memory.readByte 0x8000)
    assertEqual "ELF32 zero-filled byte" (some 0) (image.memory.readByte 0x8007)
    assertEqual "ELF32 virtual memory end" none (image.memory.readByte 0x8008)
    assertEqual "ELF32 p_vaddr rather than p_paddr" none (image.memory.readByte 0x9000)
    assertEqual "ELF32 segment span" (some (0x8000, 8)) (image.segments[0]?.map fun segment => (segment.addr, segment.size))
    assertEqual "ELF32 segment permissions" (some (true, false, true))
      (image.segments[0]?.map fun segment => (segment.readable, segment.writable, segment.executable))
    assertEqual "ELF32 sections" [".symtab", ".shstrtab"]
      (image.sections.map (·.name) |>.filter (· != ""))
    assertEqual "ELF32 symbol names" ["f"] (image.symbols.map (·.name))
    assertEqual "ELF32 symbol clears the Thumb bit" [0x8000] (image.symbols.map (·.addr))
    assertEqual "ELF32 symbol size" [4] (image.symbols.map (·.size))
    assertEqual "ELF32 function symbol" [true] (image.symbols.map (·.isFunction))
  match Elf.programHeaders elf32Fixture with
  | .error error => throw <| IO.userError error
  | .ok headers =>
    assertEqual "ELF32 program header" [[1, 5, 84, 0x8000, 4, 8]]
      (headers.map fun header =>
        [header.kind, header.flags, header.offset, header.addr, header.fileSize, header.memorySize])
  match Elf.decode elf32BigFixture with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "ELF32 big-endian" Endian.big image.endian
    assertEqual "ELF32 big-endian architecture" Arch.mips image.arch
    assertEqual "ELF32 big-endian bytes" (some 0xbe) (image.memory.readByte 0x400002)
    assertEqual "ELF32 big-endian zero fill" (some 0) (image.memory.readByte 0x40000f)
    assertEqual "ELF32 big-endian permissions" (some (true, true, false))
      (image.segments[0]?.map fun segment => (segment.readable, segment.writable, segment.executable))
  match Elf.decode elf32DynamicFixture with
  | .error error => throw <| IO.userError error
  | .ok image =>
    match Elf.dynamicRelocations image with
    | .error error => throw <| IO.userError error
    | .ok relocations =>
      assertEqual "ELF32 relative relocation" [212] relocations.relative
      assertEqual "ELF32 named reference" [(216, "x")] relocations.references
      assertEqual "ELF32 R_386_32 target adds the stored addend" [(216, 0x104)] relocations.absolute
  match Elf.decode elf64ObjectFixture with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "ELF object has no segments" 0 image.segments.length
    assertEqual "ELF object has no mapped memory" 0 image.memory.entries.length
  assertEqual "ELF object has no program headers" (some 0) ((Elf.programHeaders elf64ObjectFixture).toOption.map (·.length))
  match Elf.decode (elf32Fixture.set! 42 0) with
  | .error _ => IO.println "ok: undersized ELF program entries rejected when present"
  | .ok _ => throw <| IO.userError "undersized ELF program entries accepted"

def run : IO Unit := do
  runElf32
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
