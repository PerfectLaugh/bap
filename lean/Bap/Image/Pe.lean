import Bap.Image.Basic
import Bap.IO.Reader

namespace Bap.Image.Pe

private structure Header where
  machine : Nat
  /-- The address width of the image: 32 for PE32 and 64 for PE32+. -/
  width : Nat
  imageBase : Nat
  entryPoint : Nat
  sectionOffset : Nat
  sectionCount : Nat
  symbolOffset : Nat
  symbolCount : Nat
  stringsOffset : Nat

/-- The width and the image base of an optional header, by its magic. PE32 has a `BaseOfData` field where PE32+ has the
upper half of a 64-bit `ImageBase`, and its windows-specific fields are smaller, 96 bytes in all up to the data
directories against 112. -/
private def optionalLayout (data : ByteArray) (offset size : Nat) : Except String (Nat × Nat) := do
  let magic ← IO.Reader.u16 data .little offset
  if magic == 0x10b then
    if size < 96 then
      .error "PE optional header is too small"
    else
      let base ← IO.Reader.u32 data .little (offset + 28)
      .ok (32, base)
  else if magic == 0x20b then
    if size < 112 then
      .error "PE optional header is too small"
    else
      let base ← IO.Reader.u64 data .little (offset + 24)
      .ok (64, base)
  else
    .error "unknown PE optional header magic"

private def parseHeader (data : ByteArray) : Except String Header := do
  let dosMagic ← IO.Reader.u16 data .little 0
  if dosMagic != 0x5a4d then
    .error "not a PE file"
  else
    let peOffset ← IO.Reader.u32 data .little 60
    let signature ← IO.Reader.u32 data .little peOffset
    if signature != 0x00004550 then
      .error "invalid PE signature"
    else
      let coffOffset := peOffset + 4
      let machine ← IO.Reader.u16 data .little coffOffset
      let sectionCount ← IO.Reader.u16 data .little (coffOffset + 2)
      let symbolOffset ← IO.Reader.u32 data .little (coffOffset + 8)
      let symbolCount ← IO.Reader.u32 data .little (coffOffset + 12)
      let optionalSize ← IO.Reader.u16 data .little (coffOffset + 16)
      let optionalOffset := coffOffset + 20
      let (width, imageBase) ← optionalLayout data optionalOffset optionalSize
      let entryRva ← IO.Reader.u32 data .little (optionalOffset + 16)
      let sectionOffset := optionalOffset + optionalSize
      if sectionOffset + sectionCount * 40 > data.size then
        .error "PE section table exceeds input"
      else
        let stringsOffset := symbolOffset + symbolCount * 18
        if symbolCount > 0 && stringsOffset + 4 > data.size then
          .error "PE symbol table exceeds input"
        else
          .ok ⟨machine, width, imageBase, imageBase + entryRva, sectionOffset, sectionCount,
            symbolOffset, symbolCount, stringsOffset⟩

private def fixedString (data : ByteArray) (offset size : Nat) : Except String String := do
  let bytes ← IO.Reader.slice data offset size
  .ok (String.ofList ((bytes.toList.takeWhile fun byte => byte != 0).map fun byte => Char.ofNat byte.toNat))

private def parseSection (data : ByteArray) (imageBase offset : Nat) :
    Except String (Section × Segment × MemRegion) := do
  let name ← fixedString data offset 8
  let virtualSize ← IO.Reader.u32 data .little (offset + 8)
  let rva ← IO.Reader.u32 data .little (offset + 12)
  let rawSize ← IO.Reader.u32 data .little (offset + 16)
  let rawOffset ← IO.Reader.u32 data .little (offset + 20)
  let flags ← IO.Reader.u32 data .little (offset + 36)
  let fileBytes ← IO.Reader.slice data rawOffset rawSize
  let memorySize := max virtualSize rawSize
  let bytes := fileBytes.append (ByteArray.mk (Array.replicate (memorySize - rawSize) 0))
  let address := imageBase + rva
  let readable := flags &&& 0x40000000 != 0
  let writable := flags &&& 0x80000000 != 0
  let executable := flags &&& 0x20000000 != 0
  .ok (⟨name, address, rawOffset, virtualSize, flags, 0⟩,
    ⟨name, address, max virtualSize rawSize, readable, writable, executable⟩,
    ⟨address, bytes, readable, writable, executable⟩)

private def parseSections (data : ByteArray) (header : Header) :
    Except String (List Section × List Segment × List MemRegion) := do
  let entries ← (List.range header.sectionCount).mapM fun index =>
    parseSection data header.imageBase (header.sectionOffset + index * 40)
  .ok (entries.map Prod.fst, entries.map fun entry => entry.2.1, entries.map fun entry => entry.2.2)

private def symbolName (data : ByteArray) (header : Header) (offset : Nat) : Except String String := do
  let inline ← IO.Reader.u32 data .little offset
  if inline != 0 then
    fixedString data offset 8
  else
    let nameOffset ← IO.Reader.u32 data .little (offset + 4)
    let stringsSize ← IO.Reader.u32 data .little header.stringsOffset
    if nameOffset ≥ stringsSize then
      .error "PE symbol name exceeds string table"
    else
      IO.Reader.cstring data (header.stringsOffset + nameOffset)

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
    Nat → Nat → List Symbol → Except String (List Symbol)
  | _, 0, symbols => .ok symbols
  | index, remaining + 1, symbols => do
    let offset := header.symbolOffset + index * 18
    let symbol ← parseSymbol data header sections offset
    let auxiliaryCount ← IO.Reader.get8 data (offset + 17)
    if auxiliaryCount > remaining then
      .error "PE auxiliary symbol exceeds symbol table"
    else
      parseSymbols data header sections (index + auxiliaryCount + 1)
        (remaining - auxiliaryCount) (symbols ++ [symbol])

private def architecture (machine : Nat) : Arch :=
  match machine with
  | 0x8664 => .x86_64
  | 0xaa64 => .aarch64
  | 0x014c => .x86
  | 0x01c0 | 0x01c2 | 0x01c4 => .arm
  | _ => .unknown

def decode (data : ByteArray) : Except String Image := do
  let header ← parseHeader data
  let (sections, segments, regions) ← parseSections data header
  let symbols ← parseSymbols data header sections 0 header.symbolCount []
  let memory := regions.foldl (fun memory region => MemoryMap.add region () memory) {}
  .ok {
    arch := architecture header.machine
    addrWidth := header.width
    endian := .little
    entryPoint := header.entryPoint
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

end Bap.Image.Pe
