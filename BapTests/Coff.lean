import BapTests.Support

namespace Bap.Tests.Coff

open Bap
open Bap.Image

private def appendNat (bytes : ByteArray) (value size : Nat) : ByteArray :=
  (List.range size).foldl (init := bytes) fun result index =>
    result.push (UInt8.ofNat (value / 256 ^ index % 256))

private def appendFixed (bytes : ByteArray) (value : String) (size : Nat) : ByteArray :=
  let encoded := value.toUTF8
  (List.range size).foldl (init := bytes) fun result index =>
    result.push (if index < encoded.size then encoded.get! index else 0)

private def fixture : ByteArray :=
  let b := appendNat ByteArray.empty 0x8664 2
  let b := appendNat b 1 2
  let b := appendNat b 0 4
  let b := appendNat b 60 4
  let b := appendNat b 3 4
  let b := appendNat b 0 4
  let b := appendFixed b "/4" 8
  let b := appendNat b 0 4
  let b := appendNat b 0 4
  let b := appendNat b 7 4
  let b := appendNat b 147 4
  let b := appendNat b 154 4
  let b := appendNat b 0 4
  let b := appendNat b 1 2
  let b := appendNat b 0 2
  let b := appendNat b 0x60000020 4
  let b := appendFixed b "_start" 8
  let b := appendNat b 0 4
  let b := appendNat b 1 2
  let b := appendNat b 0x20 2
  let b := appendNat b 2 1
  let b := appendNat b 1 1
  let b := appendNat b 0 18
  let b := appendNat b 0 4
  let b := appendNat b 14 4
  let b := appendNat b 1 4
  let b := appendNat b 1 2
  let b := appendNat b 0x20 2
  let b := appendNat b 2 1
  let b := appendNat b 0 1
  let b := appendNat b 33 4
  let b := appendFixed b ".longtext" 10
  let b := appendFixed b "long_function_name" 19
  let b := b.push 0x55 |>.push 0x90 |>.push 0xc3
  let b := appendNat b 0 4
  let b := appendNat b 3 4
  let b := appendNat b 2 4
  appendNat b 4 2

private def ofHex (text : String) : ByteArray :=
  let digit (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
  let rec go : List Char → ByteArray → ByteArray
    | high :: low :: rest, bytes => go rest (bytes.push (UInt8.ofNat (digit high * 16 + digit low)))
    | _, bytes => bytes
  go text.toList ByteArray.empty

/-- `llvm-mc -triple=x86_64-pc-windows-msvc` of: `start: call ext; movl value(%rip), %eax; movl tv@SECREL32(%rax), %eax;
ret`, `.data` with `value: .long 7` and `ptr: .quad start`, `.tls$` with `tv: .long 1`, `.debug$S` with `.secrel32 start`
and `.secidx start`, and a `.bss` of 16 bytes. -/
private def objectFixture : ByteArray := ofHex (
  "64860500000000004401000010000000000000002e74657874000000000000000000000012000000dc000000ee000000" ++
  "0000000003000000200030602e6461746100000000000000000000000c0000000c010000180100000000000001000000" ++
  "400030c02e6273730000000000000000000000001000000000000000000000000000000000000000800030c02e746c73" ++
  "2400000000000000000000000400000022010000000000000000000000000000400010c02e6465627567245300000000" ++
  "000000000a0000002601000030010000000000000200000040001042e8000000008b05000000008b8000000000c30100" ++
  "00000b0000000400070000000c00000004000d0000000d0000000b00070000000000000000000000040000000a000000" ++
  "01000100000004000000000000000000040000000a0000000b00080000000a0000000a002e7465787400000000000000" ++
  "0100000003011200000003000000a3543d170100000000002e64617461000000000000000200000003010c0000000100" ++
  "00008fe998740200000000002e6273730000000000000000030000000301100000000000000000000000030000000000" ++
  "2e746c73240000000000000004000000030104000000000000006567bcb80400000000002e6465627567245300000000" ++
  "0500000003010a000000020000007aa0eb09050000000000737461727400000000000000010000000200657874000000" ++
  "00000000000000000000020076616c756500000000000000020000000300747600000000000000000000040000000300" ++
  "7074720000000000040000000200000003007a65726f730000000000000003000000030004000000")

/-- An `llvm-mc` object of AArch64 with each section's `VirtualAddress` the RVA `lld-link /base:0` gives it, and
what `lld-link` then makes of the sections. -/
private def a64Object : ByteArray := ofHex (
  "64aa040000000000640200000f000000000000002e74657874000000000000000010000050000000b4000000040100000000" ++
  "000014000000200030602e64617461000000000000000020000058000000cc010000240200000000000006000000400050c0" ++
  "2e6273730000000000000000000000000000000000000000000000000000000000000000800030c02e6b6f64650000000000" ++
  "000000300000040000006002000000000000000000000000000020001060000000940000001400000054000000b400001836" ++
  "0000001020000010000000900080009000000091002000910000403900004079000040b9000040f9000440f90000c03d0000" ++
  "009100004091000040f9000000000900000003000400000009000000030008000000090000000f000c000000090000000f00" ++
  "10000000090000001000140000000a0000000500180000000a00000005001c0000000a0000000400200000000a0000000400" ++
  "240000000a0000000600280000000a00000006002c0000000a0000000700300000000b0000000700340000000c0000000700" ++
  "380000000d00000007003c0000000d0000000700400000000e0000000700440000000a0000000900480000000a0000000a00" ++
  "4c0000000d0000000b0007000100010000000100000000000000020000000000000000000000000000000300000000000000" ++
  "040000000000000000000000ccffffff00000000000000000400000000000000080000000000000000000000000000003000" ++
  "00000a0000000200380000000a00000008003c0000000a0000000d0040000000090000000200440000000a00000001004800" ++
  "00000a0000000e00c0035fd62e746578740000000000000001000000030150000000140000005e6ce5da0100000000002e64" ++
  "617461000000000000000200000003015800000006000000bf45aae40200000000002e627373000000000000000003000000" ++
  "03010000000000000000000000000300000000002e6b6f646500000000000000040000000301040000000000000025669826" ++
  "04000000000066000000000000000000000001002000020067000000000000000000000004000000020076616c7565000000" ++
  "0000000002000000030076616c75653136000200000002000000030076616c75653332000400000002000000030076616c75" ++
  "653634000800000002000000030076616c75653132382000000002000000030004000000")

private def a64Sections : List (String × String) := [
  (".text",
  "00080094ff070014c0ff0054a0ff00b480ff1836607f0010607f0010000000b0000000d000000091002000910000403900044079000440b9000440f9000840f90008c03d0000009100004091000440f9"),
  (".data",
  "07000100010000000100000000000000020000000000000000000000000000000300000000000000040000000000000000200000ccffffff0000000002000000043000000020000008200000000000000000000000000000"),
  (".kode", "c0035fd6")]

/-- An `llvm-mc` object of Thumb with each section's `VirtualAddress` the RVA `lld-link /base:0` gives it, and
what `lld-link` then makes of the sections. -/
private def armObject : ByteArray := ofHex (
  "c4010300000000003c0100000a000000000000002e7465787400000000000000001000002a0000008c000000b60000000000" ++
  "000006000000200032602e64617461000000000000000020000018000000f20000000a0100000000000005000000400030c0" ++
  "2e6273730000000000000000000000000000000000000000000000000000000000000000800030c000f000f800f000b800f0" ++
  "008000f000e800bf40f20000c0f2000040f20001c0f2000100bf704700bf7047000000000700000014000400000007000000" ++
  "1400080000000700000012000c000000080000001500120000000900000011001a0000000700000011000700000000000000" ++
  "0000000004000000000000000000000004000000070000000100080000000900000001000c000000070000000a0010000000" ++
  "090000000f0014000000090000000e002e74657874000000000000000100000003012a00000006000000f9c373e701000000" ++
  "00002e64617461000000000000000200000003011800000005000000080c1e320200000000002e6273730000000000000000" ++
  "0300000003010000000000000000000000000300000000006600000000000000000000000100200002006700000000000000" ++
  "2400000001002000020068000000000000002800000001000000020076616c75650000000000000002000000030004000000")

private def armSections : List (String × String) := [
  (".text", "00f010f800f00eb800f00c8000f00ce800bf42f20000c0f2000041f22501c0f2000100bf704700bf7047"), (".data",
  "07000000251000000020000019f0ffff0000000002000000")]

/-- Every relocation of AArch64 and Thumb that `lld-link` knows of is in these two. -/
private def runInstructions : IO Unit := do
  for (name, object, sections) in [("AArch64", a64Object, a64Sections), ("Thumb", armObject, armSections)] do
    match Coff.decodeReport object with
    | .error error => throw <| IO.userError error
    | .ok (image, errors) =>
      assertEqual s!"COFF {name} applied every relocation" ([] : List String) errors
      for (sectionName, expected) in sections do
        match image.segments.find? (·.name == sectionName) with
        | none => throw <| IO.userError s!"COFF {name} has no {sectionName}"
        | some segment =>
          let bytes := ofHex expected
          assertEqual s!"COFF {name} {sectionName} matches lld-link" (bytes.toList.map some)
            ((List.range bytes.size).map fun index => image.memory.readByte (segment.addr + index))

private def runObject : IO Unit := do
  match Coff.decodeReport objectFixture with
  | .error error => throw <| IO.userError error
  | .ok (image, errors) =>
    assertEqual "COFF object applied every relocation" ([] : List String) errors
    assertEqual "COFF object maps what occupies memory, without .debug$S"
      [".text", ".data", ".bss", ".tls$", "EXTERNAL"] (image.segments.map (·.name))
    assertEqual "COFF object lays sections out" [0, 20, 32, 48, 56] (image.segments.map (·.addr))
    assertEqual "COFF object sizes" [18, 12, 16, 4, 8] (image.segments.map (·.size))
    assertEqual "COFF object keeps the section list" 5 image.sections.length
    assertEqual "COFF undefined symbol has a slot" (some 56) ((image.symbols.find? (·.name == "ext")).map (·.addr))
    assertEqual "COFF symbol moves with its section" (some 24) ((image.symbols.find? (·.name == "ptr")).map (·.addr))
    assertEqual "COFF REL32 to an external" (some 0x33) (image.memory.readByte 1)
    assertEqual "COFF REL32 across sections" (some 9) (image.memory.readByte 7)
    assertEqual "COFF SECREL is from the section start" (some 0) (image.memory.readByte 13)
    assertEqual "COFF ADDR64 across sections" (some 0) (image.memory.readByte 24)
  -- the relocations of a machine with no handlers are errors of their own, and the rest of the file decodes
  match Coff.decodeReport (objectFixture.set! 0 0x64 |>.set! 1 0x50) with
  | .error error => throw <| IO.userError error
  | .ok (image, errors) =>
    assertEqual "COFF RISC-V relocations are reported one by one" 4 errors.length
    assertEqual "COFF RISC-V object still decodes" Arch.riscv image.arch
    assertEqual "COFF unrelocated bytes stay" (some 0) (image.memory.readByte 1)
  assertTrue "COFF decode drops the report" (Coff.decode (objectFixture.set! 0 0x64 |>.set! 1 0x50) matches .ok _)
  -- old A32 and Thumb-1 branches stay reported rather than guessed at
  assertEqual "COFF A32 BRANCH24 is not applied" none (Coff.relocationKind 0x01c4 3)
  assertEqual "COFF ABSOLUTE does nothing" (some Coff.RelocationKind.ignored) (Coff.relocationKind 0xaa64 0)


/-- A field of `size` bytes of a fixture, little-endian or big, set to `value`. -/
private def setField (data : ByteArray) (offset size value : Nat) (big : Bool := false) : ByteArray :=
  (List.range size).foldl (init := data) fun data index =>
    data.set! (offset + (if big then size - 1 - index else index)) (UInt8.ofNat (value / 256 ^ index % 256))

private def fieldOf (data : ByteArray) (offset size : Nat) (big : Bool := false) : Nat :=
  (List.range size).foldl (init := 0) fun value index =>
    value + (data.get! (offset + (if big then size - 1 - index else index))).toNat * 256 ^ index

/-- An object of AMD64 whose `.text` has more relocations than its 16 bits can say: `IMAGE_SCN_LNK_NRELOC_OVFL`, with the count in the
first relocation, which is no relocation. Each is an `ADDR32` of a symbol at 0x10 to a slot that holds its index. -/
private def overflowObject (count : Nat) (symbols : Nat := 1) (slots : Nat := count) : ByteArray :=
  let le (size value : Nat) : ByteArray := ByteArray.mk ((List.range size).map fun index => (value >>> (8 * index)).toUInt8).toArray
  let rawOffset := 60
  let rawSize := 4 * slots
  let relocationOffset := rawOffset + rawSize
  let symbolOffset := relocationOffset + 10 * (count + 1)
  let header := le 2 0x8664 ++ le 2 1 ++ le 4 0 ++ le 4 symbolOffset ++ le 4 symbols ++ le 2 0 ++ le 2 0
  let sectionHeader := ".text".toUTF8 ++ le 3 0 ++ le 4 0 ++ le 4 0 ++ le 4 rawSize ++ le 4 rawOffset ++ le 4 relocationOffset ++
    le 4 0 ++ le 2 0xffff ++ le 2 0 ++ le 4 (0x60000020 ||| 0x01000000)
  let raw := (List.range slots).foldl (fun out index => out ++ le 4 index) ByteArray.empty
  -- each of the last of the symbols, which are all the same, to the slots in turn
  let relocations := (List.range count).foldl (fun out index => out ++ le 4 (4 * (index % slots)) ++ le 4 (symbols - 1) ++ le 2 2)
    (le 4 (count + 1) ++ le 4 0 ++ le 2 0)
  let symbol := "sym".toUTF8 ++ le 5 0 ++ le 4 0x10 ++ le 2 1 ++ le 2 0 ++ ByteArray.mk #[2, 0]
  (List.range symbols).foldl (fun out _ => out ++ symbol) (header ++ sectionHeader ++ raw ++ relocations) ++ le 4 4

/-- All of the relocations of a section that has more than 65535, and not the first, which says how many. -/
def runRelocationOverflow : IO Unit := do
  let count := 70000
  match Coff.decodeReport (overflowObject count) with
  | .error error => throw <| IO.userError error
  | .ok (image, errors) =>
    assertEqual "COFF of more relocations than 16 bits applies them all" ([] : List String) errors
    let word (address : Nat) : Nat :=
      (List.range 4).foldl (fun value index => value + ((image.memory.readByte (address + index)).getD 0).toNat * 256 ^ index) 0
    assertEqual "COFF of more relocations than 16 bits: the first and the last" (0x10, 0x10 + count - 1) (word 0, word (4 * (count - 1)))
  -- The symbol of a relocation is had of a table of them all, not of a search of them for each: 2000000 relocations of the last of
  -- 60000 symbols are 12 * 10^10 steps of that, three minutes of them, and take seconds. Only the time says so: it is given 60 s.
  -- They are all of one slot, which has the symbol's address added as often.
  let (count, symbols) := (2000000, 60000)
  let started ← IO.monoMsNow
  match Coff.decodeReport (overflowObject count symbols 1) with
  | .error error => throw <| IO.userError error
  | .ok (image, errors) =>
    assertEqual "COFF of many relocations of many symbols applies them all" ([] : List String) errors
    let word (address : Nat) : Nat :=
      (List.range 4).foldl (fun value index => value + ((image.memory.readByte (address + index)).getD 0).toNat * 256 ^ index) 0
    assertEqual "COFF of many relocations of many symbols: all of them" (0x10 * count % 2 ^ 32) (word 0)
    let elapsed := (← IO.monoMsNow) - started
    assertTrue s!"COFF of many relocations of many symbols is done in the time of what it has, not of their product: {elapsed} ms"
      (elapsed < 60000)
  -- and it is the first of the symbols of an index, as a search has it
  let named (name : String) : Symbol := ⟨name, 0, 0, false, false, false⟩
  let find := Coff.symbolFinder (Coff.symbolTable [(3, named "a"), (5, named "b"), (3, named "c")])
  assertEqual "COFF symbols are found by their indices, the first of each" [some "a", some "b", none]
    ([3, 5, 4].map fun index => (find index).map (·.2.name))

/-- An object of AMD64 with the symbols of its sections, as MSVC makes them, each with an auxiliary record of its definition: a
checksum where a symbol has its value, and no section where a symbol has its section, as it isn't of an associative COMDAT. -/
private def auxiliaryObject : ByteArray :=
  let le (size value : Nat) : ByteArray := ByteArray.mk ((List.range size).map fun index => (value >>> (8 * index)).toUInt8).toArray
  let rawOffset := 60
  let symbolOffset := rawOffset + 4
  let header := le 2 0x8664 ++ le 2 1 ++ le 4 0 ++ le 4 symbolOffset ++ le 4 4 ++ le 2 0 ++ le 2 0
  let sectionHeader := ".text".toUTF8 ++ le 3 0 ++ le 4 0 ++ le 4 0 ++ le 4 4 ++ le 4 rawOffset ++ le 4 0 ++ le 4 0 ++ le 2 0 ++ le 2 0 ++
    le 4 0x60000020
  -- A static symbol of the section, and its definition: its size, no relocations, its checksum, and no section that it goes with.
  let symbol := ".text".toUTF8 ++ le 3 0 ++ le 4 0 ++ le 2 1 ++ le 2 0 ++ ByteArray.mk #[3, 1]
  let definition := le 4 4 ++ le 2 0 ++ le 2 0 ++ le 4 0xf0000000 ++ le 2 0 ++ ByteArray.mk #[2] ++ le 3 0
  header ++ sectionHeader ++ le 4 0xc3c3c3c3 ++ symbol ++ definition ++ symbol ++ definition ++ le 4 4

/-- What follows a symbol as its auxiliary records is no symbol: no common, however large what is where its value would be. -/
def runAuxiliaryRecords : IO Unit := do
  match Coff.decodeReport auxiliaryObject with
  | .error error => throw <| IO.userError s!"COFF of auxiliary records of sections: {error}"
  | .ok (image, _) => assertEqual "COFF of auxiliary records of sections has its section" [".text"] (image.segments.map (·.name))

/-- Of objects that a compiler made, `testsuite/obj/pe`: a weak external is where its default is, in the object, rather than
with what nothing defines; symbols without a section that have a size count to what the regions take, whatever their class; and a
function of Thumb is one that runs in Thumb state, of an object and of an executable. -/
def runCompiled : IO Unit := do
  let weak ← IO.FS.readBinFile "testsuite/obj/pe/x86_64-windows-weak.obj"
  match Coff.decodeReport weak with
  | .error error => throw <| IO.userError s!"COFF of a weak external: {error}"
  | .ok (image, _) =>
    let default := image.symbols.find? (·.name.startsWith ".weak.weakf.default")
    assertTrue "COFF of a weak external has its default" default.isSome
    assertEqual "a COFF weak external is where its default is" (default.map (·.addr))
      ((image.symbols.find? (·.name == "weakf")).map (·.addr))
  let symbols := fieldOf weak 8 4
  let sized := (List.range (fieldOf weak 12 4)).foldl (init := weak) fun data index =>
    let at_ := symbols + index * 18
    if fieldOf weak (at_ + 12) 2 == 0 && fieldOf weak (at_ + 16) 1 == 2 && fieldOf weak (at_ + 17) 1 == 0 then
      setField (setField data (at_ + 16) 1 3) (at_ + 8) 4 0xc0000000
    else data
  assertTrue "COFF of a weak external has two symbols that nothing defines" (sized != weak)
  assertEqual "COFF symbols of any class too large together are refused" (some "the regions of the COFF file are too large")
    (match Coff.decodeReport sized with | .error message => some message | .ok _ => none)
  match Coff.decodeReport (← IO.FS.readBinFile "testsuite/obj/pe/thumb-windows.obj"),
      Image.decode (← IO.FS.readBinFile "testsuite/obj/pe/thumb-windows-pe.exe") with
  | .ok (object, _), .ok executable =>
    for (what, image) in [("object", object), ("executable", executable)] do
      assertEqual s!"a function of a Thumb COFF {what} runs in Thumb state" (some true)
        ((image.symbols.find? (·.name == "other")).map (·.thumb))
      assertEqual s!"and what isn't a function of a Thumb COFF {what} doesn't" (some false)
        ((image.symbols.find? (·.name == "arr")).map (·.thumb))
  | .error error, _ | _, .error error => throw <| IO.userError s!"COFF of Thumb: {error}"

/-- The names of the symbols of an object take no more than `namesLimit`, each as often as a symbol has it, and so do those of its
sections that are in the string table: 64 of either that each name a string of 64 KiB are refused, and 8 are read. -/
def runNames : IO Unit := do
  let length := 2 ^ 16
  let file (sections symbols : Nat) (tableSize : Nat := length + 5) : ByteArray :=
    let le (size value : Nat) : ByteArray := appendNat ByteArray.empty value size
    let header := le 2 0x8664 ++ le 2 sections ++ le 4 0 ++ le 4 (20 + 40 * sections) ++ le 4 symbols ++ le 2 0 ++ le 2 0
    let sectionHeader := "/4".toUTF8 ++ le 6 0 ++ le 28 0 ++ le 4 0x60000020
    let symbol := le 4 0 ++ le 4 4 ++ le 4 0 ++ le 2 1 ++ le 2 0x20 ++ le 1 2 ++ le 1 0
    let headers := (List.range sections).foldl (fun bytes _ => bytes ++ sectionHeader) header
    (List.range symbols).foldl (fun bytes _ => bytes ++ symbol) headers ++ le 4 tableSize ++
      ByteArray.mk (Array.replicate length 0x41) ++ ByteArray.mk #[0]
  let refused (data : ByteArray) : Option String := match Coff.decodeReport data with
    | .error message => some message
    | .ok _ => none
  assertEqual "COFF symbols and sections whose names are 8 times a string of 64 KiB are read"
    (some (List.replicate 8 length, List.replicate 8 length))
    ((Coff.decode (file 8 8)).toOption.map fun image => (image.sections.map (·.name.length), image.symbols.map (·.name.length)))
  assertEqual "COFF symbols whose names take more than the file is given are refused" (some namesTooLarge) (refused (file 1 64))
  assertEqual "COFF sections whose names take more than the file is given are refused" (some namesTooLarge) (refused (file 64 1))
  assertEqual "a COFF name that doesn't end in the string table is refused" (some "unterminated string") (refused (file 1 1 100))

def run : IO Unit := do
  runNames
  runCompiled
  -- Sections and commons whose headers ask for more zeros than a host can give, all together, aren't made.
  let table := 20 + fieldOf objectFixture 16 2
  let symbols := fieldOf objectFixture 8 4
  let huge := setField (setField (setField objectFixture (table + 8) 4 0xffffffff) (symbols + 12) 2 0) (symbols + 8) 4 0xffffffff
  assertTrue "COFF fixture has a symbol" (fieldOf objectFixture 12 4 ≥ 1)
  assertEqual "COFF regions too large are refused" (some "the regions of the COFF file are too large")
    (match Coff.decodeReport huge with | .error message => some message | .ok _ => none)
  runObject
  runInstructions
  assertEqual "COFF fixture size" 164 fixture.size
  match Coff.decode (ByteArray.mk #[1, 2, 3, 4]) with
  | .error _ => IO.println "ok: malformed COFF rejected"
  | .ok _ => throw <| IO.userError "malformed COFF accepted"
  match Coff.decode fixture with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "COFF architecture" Arch.x86_64 image.arch
    assertEqual "COFF address width" 64 image.addrWidth
    assertEqual "COFF entry point" 0 image.entryPoint
    assertEqual "COFF section count" 1 image.sections.length
    assertEqual "COFF symbol count excludes auxiliary" 2 image.symbols.length
    assertEqual "COFF mapped byte" (some 0x90) (image.memory.readByte 1)
    -- S + A - (P + 4) = 1 + 0 - (3 + 4), as lld-link computes for REL32
    assertEqual "COFF REL32 low byte" (some 0xfa) (image.memory.readByte 3)
    assertEqual "COFF REL32 sign extension" (some 0xff) (image.memory.readByte 4)
    assertEqual "COFF unmapped byte" none (image.memory.readByte 7)
    match image.sections[0]?, image.symbols with
    | some sec, [entry, long] =>
      assertEqual "COFF long section name" ".longtext" sec.name
      assertEqual "COFF section raw offset" 147 sec.offset
      assertEqual "COFF section size" 7 sec.size
      assertEqual "COFF short symbol name" "_start" entry.name
      assertEqual "COFF long symbol name" "long_function_name" long.name
      assertEqual "COFF long symbol address" 1 long.addr
      assertEqual "COFF function symbol" true long.isFunction
    | _, _ => throw <| IO.userError "missing decoded COFF metadata"
  match Coff.decode (fixture.set! 32 0x10 |>.set! 108 0) with
  | .error error => throw <| IO.userError error
  | .ok image =>
    -- a nonzero value of an undefined symbol is the size of a common block, placed after the sections
    assertEqual "COFF undefined symbol is not rebased onto section 1" (some 0x18) (image.symbols[1]?.map (·.addr))
    assertEqual "COFF undefined symbol is not a function" (some false) (image.symbols[1]?.map (·.isFunction))
    assertEqual "COFF defined symbol is rebased" (some 0x10) (image.symbols[0]?.map (·.addr))
  -- a .bss of an object: its size is SizeOfRawData, past the end of the file, and it has no file bytes
  match Coff.decode (fixture.set! 36 0 |>.set! 38 1 |>.set! 40 0 |>.set! 52 0) with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "COFF uninitialized segment size" (some 0x10000) (image.segments[0]?.map (·.size))
    assertEqual "COFF uninitialized section reads zero" (some 0) (image.memory.readByte 0)
    assertEqual "COFF uninitialized section last byte" (some 0) (image.memory.readByte 0xffff)
    assertEqual "COFF uninitialized section end" none (image.memory.readByte 0x10000)
  match Coff.decode (fixture.set! 28 16) with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "COFF virtual segment size" (some 16) (image.segments[0]?.map (·.size))
    assertEqual "COFF zero-filled byte" (some 0) (image.memory.readByte 15)
    assertEqual "COFF virtual memory end" none (image.memory.readByte 16)
  let path := "native/build/bap-lean-fixture.obj"
  IO.FS.writeBinFile path fixture
  let loaded ← Coff.load path
  IO.FS.removeFile path
  assertEqual "COFF filesystem load" 2 loaded.symbols.length

end Bap.Tests.Coff
