import Bap.Image.Basic
import Bap.IO.Reader

namespace Bap.Image.Coff

private structure Header where
  machine : Nat
  sectionCount : Nat
  sectionOffset : Nat
  symbolOffset : Nat
  symbolCount : Nat
  stringsOffset : Nat

private def parseHeader (data : ByteArray) : Except String Header := do
  let machine ← IO.Reader.u16 data .little 0
  let sectionCount ← IO.Reader.u16 data .little 2
  let symbolOffset ← IO.Reader.u32 data .little 8
  let symbolCount ← IO.Reader.u32 data .little 12
  let optionalSize ← IO.Reader.u16 data .little 16
  let sectionOffset := 20 + optionalSize
  let stringsOffset := symbolOffset + symbolCount * 18
  if sectionOffset + sectionCount * 40 > data.size then
    .error "COFF section table exceeds input"
  else if symbolCount > 0 && stringsOffset + 4 > data.size then
    .error "COFF symbol table exceeds input"
  else
    .ok ⟨machine, sectionCount, sectionOffset, symbolOffset, symbolCount, stringsOffset⟩

private def fixedString (data : ByteArray) (offset size : Nat) : Except String String := do
  let bytes ← IO.Reader.slice data offset size
  .ok (String.ofList ((bytes.toList.takeWhile fun byte => byte != 0).map fun byte => Char.ofNat byte.toNat))

private def tableString (data : ByteArray) (header : Header) (offset : Nat) : Except String String := do
  if header.symbolOffset = 0 then
    .error "COFF string table is missing"
  else
    let stringsSize ← IO.Reader.u32 data .little header.stringsOffset
    if offset ≥ stringsSize then
      .error "COFF name exceeds string table"
    else
      IO.Reader.cstring data (header.stringsOffset + offset)

private def sectionName (data : ByteArray) (header : Header) (offset : Nat) : Except String String := do
  let first ← IO.Reader.get8 data offset
  if first != '/'.toNat then
    fixedString data offset 8
  else
    let encoded ← fixedString data offset 8
    match (encoded.drop 1).toNat? with
    | some nameOffset => tableString data header nameOffset
    | none => .error "invalid COFF long section name"

private structure ObjectSection where
  info : Section
  segment : Segment
  region : MemRegion
  relocationOffset : Nat
  relocationCount : Nat

private def parseSection (data : ByteArray) (header : Header) (offset : Nat) :
    Except String ObjectSection := do
  let name ← sectionName data header offset
  let virtualSize ← IO.Reader.u32 data .little (offset + 8)
  let address ← IO.Reader.u32 data .little (offset + 12)
  let rawSize ← IO.Reader.u32 data .little (offset + 16)
  let rawOffset ← IO.Reader.u32 data .little (offset + 20)
  let relocationOffset ← IO.Reader.u32 data .little (offset + 24)
  let relocationCount ← IO.Reader.u16 data .little (offset + 32)
  let flags ← IO.Reader.u32 data .little (offset + 36)
  let fileSize := if rawOffset = 0 || flags &&& 0x80 != 0 then 0 else rawSize
  let fileBytes ← IO.Reader.slice data rawOffset fileSize
  if relocationOffset + relocationCount * 10 > data.size then
    .error "COFF relocation table exceeds input"
  else
    let readable := flags &&& 0x40000000 != 0
    let writable := flags &&& 0x80000000 != 0
    let executable := flags &&& 0x20000000 != 0
    let size := if virtualSize = 0 then rawSize else virtualSize
    let memorySize := max size rawSize
    let bytes := fileBytes.append (ByteArray.mk (Array.replicate (memorySize - fileSize) 0))
    .ok ⟨⟨name, address, rawOffset, size, flags, 0⟩,
      ⟨name, address, memorySize, readable, writable, executable⟩,
      ⟨address, bytes, readable, writable, executable⟩, relocationOffset, relocationCount⟩

private def parseSections (data : ByteArray) (header : Header) : Except String (List ObjectSection) :=
  (List.range header.sectionCount).mapM fun index =>
    parseSection data header (header.sectionOffset + index * 40)

private def symbolName (data : ByteArray) (header : Header) (offset : Nat) : Except String String := do
  let inline ← IO.Reader.u32 data .little offset
  if inline != 0 then
    fixedString data offset 8
  else
    let nameOffset ← IO.Reader.u32 data .little (offset + 4)
    tableString data header nameOffset

private def parseSymbol (data : ByteArray) (header : Header) (sections : List Section)
    (offset : Nat) : Except String Symbol := do
  let name ← symbolName data header offset
  let value ← IO.Reader.u32 data .little (offset + 8)
  let sectionIndex ← IO.Reader.u16 data .little (offset + 12)
  let symbolType ← IO.Reader.u16 data .little (offset + 14)
  let storageClass ← IO.Reader.get8 data (offset + 16)
  let address := match sectionOfNumber sections sectionIndex with
    | some sec => sec.addr + value
    | none => value
  .ok ⟨name, address, 0, sectionIndex != 0 && symbolType &&& 0x30 = 0x20, storageClass = 103⟩

private def parseSymbols (data : ByteArray) (header : Header) (sections : List Section) :
    Nat → Nat → List (Nat × Symbol) → Except String (List (Nat × Symbol))
  | _, 0, symbols => .ok symbols
  | index, remaining + 1, symbols => do
    let offset := header.symbolOffset + index * 18
    let symbol ← parseSymbol data header sections offset
    let auxiliaryCount ← IO.Reader.get8 data (offset + 17)
    if auxiliaryCount > remaining then
      .error "COFF auxiliary symbol exceeds symbol table"
    else
      parseSymbols data header sections (index + auxiliaryCount + 1)
        (remaining - auxiliaryCount) (symbols ++ [(index, symbol)])

private def writeNat (data : ByteArray) (offset size value : Nat) : Except String ByteArray :=
  if offset + size > data.size then
    .error "COFF relocation exceeds section data"
  else
    .ok ((List.range size).foldl (init := data) fun result index =>
      result.set! (offset + index) (UInt8.ofNat (value / 256 ^ index % 256)))

private def applyRelocation (data : ByteArray) (header : Header) (symbols : List (Nat × Symbol))
    (object : ObjectSection) (region : MemRegion) (index : Nat) : Except String MemRegion := do
  let offset := object.relocationOffset + index * 10
  let rva ← IO.Reader.u32 data .little offset
  let symbolIndex ← IO.Reader.u32 data .little (offset + 4)
  let kind ← IO.Reader.u16 data .little (offset + 8)
  let (relative, size) ← match header.machine, kind with
    | 0x8664, 1 => .ok (false, 8)
    | 0x8664, 2 => .ok (false, 4)
    | 0x8664, 3 => .ok (false, 4)
    | 0x8664, 4 => .ok (true, 4)
    | 0x8664, 5 => .ok (true, 4)
    | 0x8664, 6 => .ok (true, 4)
    | 0x8664, 7 => .ok (true, 4)
    | 0x8664, 8 => .ok (true, 4)
    | 0x8664, 9 => .ok (true, 4)
    | _, _ => .error s!"unsupported COFF relocation type {kind}"
  match symbols.find? fun entry => entry.1 = symbolIndex with
  | none => .error s!"COFF relocation references missing symbol {symbolIndex}"
  | some (_, symbol) =>
    let addend ← IO.Reader.read region.data .little rva size
    let modulus := 2 ^ (size * 8)
    let value := if relative then
      -- REL32_n is relative to the end of the instruction, which is `kind` bytes past the field
      (symbol.addr % modulus + addend % modulus + modulus - (object.info.addr + rva + kind) % modulus) % modulus
    else
      (symbol.addr + addend) % modulus
    let bytes ← writeNat region.data rva size value
    .ok { region with data := bytes }

private def applyRelocations (data : ByteArray) (header : Header) (symbols : List (Nat × Symbol))
    (object : ObjectSection) : Except String ObjectSection := do
  let region ← (List.range object.relocationCount).foldlM (init := object.region) fun region index =>
    applyRelocation data header symbols object region index
  .ok { object with region := region }

private def architecture (machine : Nat) : Arch × Nat :=
  match machine with
  | 0x8664 => (.x86_64, 64)
  | 0xaa64 => (.aarch64, 64)
  | 0x014c => (.x86, 32)
  | 0x01c0 | 0x01c4 => (.arm, 32)
  | 0x5032 => (.riscv, 32)
  | 0x5064 => (.riscv, 64)
  | _ => (.unknown, 32)

def decode (data : ByteArray) : Except String Image := do
  let header ← parseHeader data
  let objects ← parseSections data header
  let sections := objects.map fun object => object.info
  let indexedSymbols ← parseSymbols data header sections 0 header.symbolCount []
  let objects ← objects.mapM (applyRelocations data header indexedSymbols)
  let segments := objects.map fun object => object.segment
  let regions := objects.map fun object => object.region
  let symbols := indexedSymbols.map Prod.snd
  let memory := regions.foldl (fun memory region => MemoryMap.add region () memory) {}
  let (arch, addrWidth) := architecture header.machine
  .ok {
    arch := arch
    addrWidth := addrWidth
    endian := .little
    entryPoint := 0
    data := data
    sections := sections
    segments := segments
    symbols := symbols
    memory := memory
  }

def load (path : String) : IO Image := do
  let data ← IO.FS.readBinFile path
  match decode data with
  | .ok image => pure image
  | .error error => throw <| IO.userError error

end Bap.Image.Coff
