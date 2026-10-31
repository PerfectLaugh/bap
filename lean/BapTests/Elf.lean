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

private def ofHex (text : String) : ByteArray :=
  let digit (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
  let rec go : List Char → ByteArray → ByteArray
    | high :: low :: rest, bytes => go rest (bytes.push (UInt8.ofNat (digit high * 16 + digit low)))
    | _, bytes => bytes
  go text.toList ByteArray.empty

/-- `llvm-mc -triple=x86_64-linux-gnu` of: `f: call ext; movl value(%rip), %eax; ret`, `.data` with `value: .long 7`
and `ptr: .quad f`, `.bss` of 16 bytes. Its bytes below match `ld.lld` given this layout. -/
private def x86ObjectFixture : ByteArray := ofHex (
  "7f454c4602010100000000000000000001003e0001000000000000000000000000000000000000008801000000000000" ++
  "00000000400000000000400008000100e8000000008b0500000000c30700000000000000000000000000000000000000" ++
  "000000000000000000000000000000001d00000000000400000000000000000000000000000000000000000003000400" ++
  "000000000000000000000000000000001700000000000400040000000000000000000000000000001100000000000600" ++
  "000000000000000000000000000000001b00000012000200000000000000000000000000000000000800000010000000" ++
  "0000000000000000000000000000000001000000000000000400000006000000fcffffffffffffff0700000000000000" ++
  "0200000002000000fcffffffffffffff040000000000000001000000050000000000000000000000002e72656c612e74" ++
  "657874002e627373007a65726f730070747200660076616c7565002e737472746162002e73796d746162002e72656c61" ++
  "2e6461746100000000000000000000000000000000000000000000000000000000000000000000000000000000000000" ++
  "000000000000000000000000000000000000000000000000230000000300000000000000000000000000000000000000" ++
  "48010000000000003e000000000000000000000000000000010000000000000000000000000000000600000001000000" ++
  "0600000000000000000000000000000040000000000000000c0000000000000000000000000000000400000000000000" ++
  "000000000000000001000000040000004000000000000000000000000000000000010000000000003000000000000000" ++
  "070000000200000008000000000000001800000000000000380000000100000003000000000000000000000000000000" ++
  "4c000000000000000c000000000000000000000000000000010000000000000000000000000000003300000004000000" ++
  "400000000000000000000000000000003001000000000000180000000000000007000000040000000800000000000000" ++
  "18000000000000000c000000080000000300000000000000000000000000000058000000000000001000000000000000" ++
  "0000000000000000010000000000000000000000000000002b0000000200000000000000000000000000000000000000" ++
  "5800000000000000a800000000000000010000000500000008000000000000001800000000000000")

/-- `llvm-mc -triple=mips-linux-gnu` of: `g: lui $2, %hi(tab); addiu $2, $2, %lo(tab); jal ext; nop`, `.data` with
`tab: .word g`. Its bytes below match `ld.lld` given this layout. -/
private def mipsObjectFixture : ByteArray := ofHex (
  "7f454c460102010000000000000000000001000800000001000000000000000000000144500010050034000000000028" ++
  "000a00010000000000000000000000003c020000244200000c0000000000000000000000000000000000000000000000" ++
  "000000050000000000000000000000000000000000000000000020010101000100000000000000000000000100000000" ++
  "000000000000000000000000000000000000003600000000000000000000000400000000000000000000000003000004" ++
  "000000280000000000000000120000020000000700000000000000001000000000000000000002050000000400000206" ++
  "00000008000004040000000000000302002e72656c2e74657874002e627373002e4d4950532e616269666c616773002e" ++
  "726567696e666f0067002e737472746162002e73796d746162002e72656c2e6461746100000000000000000000000000" ++
  "000000000000000000000000000000000000000000000000000000000000002a00000003000000000000000000000100" ++
  "000000440000000000000000000000010000000000000005000000010000000600000000000000400000001000000000" ++
  "00000000000000100000000000000001000000090000004000000000000000e000000018000000090000000200000004" ++
  "000000080000003e0000000100000003000000000000005000000004000000000000000000000010000000000000003a" ++
  "000000090000004000000000000000f800000008000000090000000400000004000000080000000b0000000800000003" ++
  "000000000000006000000000000000000000000000000010000000000000001f70000006000000020000000000000060" ++
  "0000001800000000000000000000000400000018000000107000002a0000000200000000000000780000001800000000" ++
  "000000000000000800000018000000320000000200000000000000000000009000000050000000010000000300000004" ++
  "00000010")

private def bytesAt (image : Image) (address size : Nat) : List (Option UInt8) :=
  (List.range size).map fun index => image.memory.readByte (address + index)

private def runObjects : IO Unit := do
  match Elf.decode x86ObjectFixture, Elf.linkObject x86ObjectFixture with
  | .error error, _ | _, .error error => throw <| IO.userError error
  | .ok image, .ok output =>
    assertEqual "ELF object segments" [".text", ".data", ".bss", "EXTERNAL"] (image.segments.map (·.name))
    assertEqual "ELF object segment addresses" [0, 12, 24, 40] (image.segments.map (·.addr))
    assertEqual "ELF object segment sizes" [12, 12, 16, 8] (image.segments.map (·.size))
    assertEqual "ELF object PC32 and PLT32 against the layout"
      ([0xe8, 0x23, 0, 0, 0, 0x8b, 0x05, 1, 0, 0, 0, 0xc3].map some) (bytesAt image 0 12)
    assertEqual "ELF object data keeps its bytes and takes R_X86_64_64" ([7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].map some)
      (bytesAt image 12 12)
    assertEqual "ELF object BSS is zero" (some 0) (image.memory.readByte 39)
    assertEqual "ELF object end of memory" none (image.memory.readByte 48)
    assertEqual "ELF object symbol in its section" (some 16)
      ((image.symbols.find? (·.name == "ptr")).map (·.addr))
    assertEqual "ELF object external has a slot" (some 40) ((image.symbols.find? (·.name == "ext")).map (·.addr))
    assertEqual "ELF object function" (some true) ((image.symbols.find? (·.name == "f")).map (·.isFunction))
    assertEqual "ELF object section address" (some 12) ((image.sections.find? (·.name == ".data")).map (·.addr))
    assertEqual "ELF object external reference" [(1, "ext")] output.references
    assertEqual "ELF object has no warnings" ([] : List String) output.warnings
  match Elf.decode mipsObjectFixture with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "ELF32 big-endian object HI16, LO16 and 26"
      ([0x3c, 2, 0, 0, 0x24, 0x42, 0, 0x10, 0x0c, 0, 0, 0x14, 0, 0, 0, 0].map some) (bytesAt image 0 16)
  let truncated := x86ObjectFixture.extract 0 400
  match Elf.decode truncated with
  | .error _ => IO.println "ok: truncated ELF object rejected"
  | .ok _ => throw <| IO.userError "truncated ELF object accepted"

/-- A little-endian ELF64 of `machine` with a whole-file LOAD, a dynamic segment of `tags` and then `table`; each tag
value of `none` is the file offset of the table. -/
private def dynamic64 (machine : Nat) (tags : List (Nat × Option Nat)) (table : ByteArray) : ByteArray :=
  let tableOffset := 176 + 16 * (tags.length + 1)
  let total := tableOffset + table.size
  let b := appendNat ByteArray.empty 0x464c457f 4
  let b := appendNat (appendNat (appendNat b 2 1) 1 1) 1 1
  let b := appendNat b 0 9
  let b := appendNat (appendNat (appendNat b 3 2) machine 2) 1 4
  let b := appendNat (appendNat (appendNat b 0 8) 64 8) 0 8
  let b := appendNat (appendNat (appendNat b 0 4) 64 2) 56 2
  let b := appendNat (appendNat (appendNat (appendNat b 2 2) 64 2) 0 2) 0 2
  let segment (bytes : ByteArray) (kind flags offset size : Nat) :=
    let b := appendNat (appendNat bytes kind 4) flags 4
    let b := appendNat (appendNat (appendNat b offset 8) offset 8) offset 8
    appendNat (appendNat (appendNat b size 8) size 8) 8 8
  let b := segment b 1 6 0 total
  let b := segment b 2 6 176 (16 * (tags.length + 1))
  let b := tags.foldl (init := b) fun bytes tag =>
    appendNat (appendNat bytes tag.1 8) (tag.2.getD tableOffset) 8
  let b := appendNat b 0 16
  table.foldl (init := b) fun bytes byte => bytes.push byte

private def relocationsOf (bytes : ByteArray) : IO Elf.RelocationSpec := do
  match Elf.decode bytes with
  | .error error => throw <| IO.userError error
  | .ok image =>
    match Elf.dynamicRelocations image with
    | .error error => throw <| IO.userError error
    | .ok spec => pure spec

private def runPacked : IO Unit := do
  -- APS2: 2 relocations from 0x100, one group sharing offset delta 8 and type, with addend deltas 16 and 8
  let aps2 := ByteArray.mk #[65, 80, 83, 50, 2, 0x80, 0x02, 2, 11, 8, 0x83, 0x08, 16, 8]
  let tags (size : Nat) : List (Nat × Option Nat) := [(0x60000011, none), (0x60000012, some size)]
  let spec ← relocationsOf (dynamic64 183 (tags 14) aps2)
  assertEqual "APS2 relative relocations" [0x108, 0x110] spec.relative
  -- the last addend is missing: what was decoded stays, and nothing is made up from the rest
  let spec ← relocationsOf (dynamic64 183 (tags 13) (aps2.extract 0 13))
  assertEqual "APS2 truncated table keeps the complete relocations" [0x108] spec.relative
  let spec ← relocationsOf (dynamic64 183 (tags 4) (aps2.extract 0 4))
  assertEqual "APS2 without a count" ([] : List Nat) spec.relative
  let oversized := ByteArray.mk #[65, 80, 83, 50, 2, 0x80, 0x02, 3, 11, 8, 0x83, 0x08, 16, 8]
  let spec ← relocationsOf (dynamic64 183 (tags 14) oversized)
  assertEqual "APS2 group larger than the table" ([] : List Nat) spec.relative
  let bad := ByteArray.mk #[65, 80, 83, 51, 2, 0x80, 0x02, 2, 11, 8, 0x83, 0x08, 16, 8]
  let spec ← relocationsOf (dynamic64 183 (tags 14) bad)
  assertEqual "APS2 bad magic" ([] : List Nat) spec.relative
  -- RELR: the address 0x1000, then a bitmap marking the second word after it, and 63 words on another
  let relr := appendNat (appendNat (appendNat ByteArray.empty 0x1000 8) 5 8) 3 8
  let spec ← relocationsOf (dynamic64 183 [(36, none), (35, some 24)] relr)
  assertEqual "RELR relative relocations" [0x1000, 0x1010, 0x1008 + 63 * 8] spec.relative
  let spec ← relocationsOf (dynamic64 183 [(36, none), (35, some 8)] (relr.extract 0 8))
  assertEqual "RELR address entry" [0x1000] spec.relative
  -- mips64el: `r_sym` in the low word, `r_ssym, r_type3, r_type2, r_type` above it
  assertEqual "mips64el r_info" (0x1203, 7) (Elf.splitInfo true true 0x0312000000000007)
  assertEqual "mips64 big-endian r_info" (0x1203, 7) (Elf.splitInfo true false 0x0000000700001203)
  assertEqual "ELF32 r_info" (0x17, 0x12) (Elf.splitInfo false false 0x1217)
  -- a relocation table of mips64el: R_MIPS_REL32 / R_MIPS_64 with no symbol is relative
  let table := appendNat (appendNat ByteArray.empty 0x2000 8) 0x0312000000000000 8
  let spec ← relocationsOf (dynamic64 8 [(17, none), (18, some 16)] table)
  assertEqual "mips64el relative relocation" [0x2000] spec.relative

/-- A little-endian MIPS ELF32 with one local GOT entry and the imported `x` and defined `y` as global ones. -/
private def mipsGotFixture : ByteArray :=
  let b := elf32Header appendNat 1 3 8 0 52 0 2 0 0
  let b := elf32Program appendNat b 1 0 0 0 256 256 6
  let b := elf32Program appendNat b 2 116 116 116 72 72 6
  let b := [(6, 188), (5, 236), (10, 5), (3, 0x400), (0x7000000a, 2), (0x70000013, 1), (0x70000011, 3), (11, 16), (0, 0)]
    |>.foldl (init := b) fun result entry => appendNat (appendNat result entry.1 4) entry.2 4
  let b := appendNat b 0 16
  let symbol (bytes : ByteArray) (name value info shndx : Nat) :=
    let b := appendNat (appendNat (appendNat bytes name 4) value 4) 0 4
    appendNat (appendNat (appendNat b info 1) 0 1) shndx 2
  let b := symbol (symbol b 1 0 0x10 0) 3 0x100 0x11 1
  let b := appendString (appendString (appendNat b 0 1) "x") "y"
  appendNat b 0 (256 - b.size)

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
    assertEqual "ELF object without sections has no segments" 0 image.segments.length
    assertEqual "ELF object has no mapped memory" 0 image.memory.entries.length
  assertEqual "ELF object has no program headers" (some 0) ((Elf.programHeaders elf64ObjectFixture).toOption.map (·.length))
  match Elf.decode (elf32Fixture.set! 42 0) with
  | .error _ => IO.println "ok: undersized ELF program entries rejected when present"
  | .ok _ => throw <| IO.userError "undersized ELF program entries accepted"

def run : IO Unit := do
  runObjects
  runPacked
  let spec ← relocationsOf mipsGotFixture
  assertEqual "MIPS global GOT entries of imports are references" [(0x408, "x")] spec.references
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
