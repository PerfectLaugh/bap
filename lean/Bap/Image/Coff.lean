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

/-- What a relocation stores. The numbers are `IMAGE_REL_*` of the machine. -/
inductive RelocationKind where
  /-- `S + A` in `size` bytes: an object has no image base, so `ADDR` and `ADDR_NB` agree. -/
  | absolute (size : Nat)
  /-- `S + A - (P + extra)`: displacements count from the end of the instruction. -/
  | relative (extra : Nat)
  /-- The number of the symbol's section plus `A`, in 16 bits (debug information). -/
  | section
  /-- `S + A` from the start of the symbol's section (debug information and thread-local storage). -/
  | sectionRelative
  deriving DecidableEq, Repr

/-- The relocations that can be applied; ARM and AArch64 ones patch instructions and are reported instead. -/
def relocationKind (machine kind : Nat) : Option RelocationKind :=
  match machine, kind with
  | 0x8664, 1 => some (.absolute 8)
  | 0x8664, 2 => some (.absolute 4)
  | 0x8664, 3 => some (.absolute 4)
  | 0x8664, 4 => some (.relative 4)
  | 0x8664, 5 => some (.relative 5)
  | 0x8664, 6 => some (.relative 6)
  | 0x8664, 7 => some (.relative 7)
  | 0x8664, 8 => some (.relative 8)
  | 0x8664, 9 => some (.relative 9)
  | 0x8664, 0xa => some .section
  | 0x8664, 0xb => some .sectionRelative
  | 0x014c, 6 => some (.absolute 4)
  | 0x014c, 7 => some (.absolute 4)
  | 0x014c, 0xa => some .section
  | 0x014c, 0xb => some .sectionRelative
  | 0x014c, 0x14 => some (.relative 4)
  | _, _ => none

/-- The value and width that a relocation stores. -/
def relocationValue (kind : RelocationKind) (symbol place addend sectionNumber sectionAddr : Nat) : Nat × Nat :=
  match kind with
  | .absolute size => ((symbol + addend) % 2 ^ (size * 8), size)
  | .relative extra =>
    let modulus := 2 ^ 32
    ((symbol % modulus + addend % modulus + modulus - (place + extra) % modulus) % modulus, 4)
  | .section => ((sectionNumber + addend) % 2 ^ 16, 2)
  | .sectionRelative => ((symbol - sectionAddr + addend) % 2 ^ 32, 4)

private def relocationSize : RelocationKind → Nat
  | .absolute size => size
  | .relative _ => 4
  | .section => 2
  | .sectionRelative => 4

private def applyRelocation (data : ByteArray) (header : Header) (sections : List Section)
    (symbols : List (Nat × Symbol)) (object : ObjectSection) (region : MemRegion) (index : Nat) :
    Except String MemRegion := do
  let offset := object.relocationOffset + index * 10
  let rva ← IO.Reader.u32 data .little offset
  let symbolIndex ← IO.Reader.u32 data .little (offset + 4)
  let number ← IO.Reader.u16 data .little (offset + 8)
  match relocationKind header.machine number with
  | none => .error s!"unsupported COFF relocation type {number} at {region.addr + rva}"
  | some kind =>
    match symbols.find? fun entry => entry.1 = symbolIndex with
    | none => .error s!"COFF relocation references missing symbol {symbolIndex}"
    | some (_, symbol) =>
      let sectionNumber ← IO.Reader.u16 data .little (header.symbolOffset + symbolIndex * 18 + 12)
      let sectionAddr := match sectionOfNumber sections sectionNumber with
        | some sec => sec.addr
        | none => 0
      let addend ← IO.Reader.read region.data .little rva (relocationSize kind)
      let (value, size) := relocationValue kind symbol.addr (object.info.addr + rva) addend sectionNumber sectionAddr
      let bytes ← writeNat region.data rva size value
      .ok { region with data := bytes }

/-- Applies the relocations of a section, one failing leaving its place as it is and adding an error. -/
private def applyRelocations (data : ByteArray) (header : Header) (sections : List Section)
    (symbols : List (Nat × Symbol)) (object : ObjectSection) : ObjectSection × List String :=
  let (region, errors) := (List.range object.relocationCount).foldl (init := (object.region, []))
    fun (region, errors) index =>
      match applyRelocation data header sections symbols object region index with
      | .ok next => (next, errors)
      | .error error => (region, error :: errors)
  ({ object with region := region }, errors.reverse)

/-- Sections that do not occupy memory: `IMAGE_SCN_LNK_REMOVE`, `IMAGE_SCN_LNK_INFO`, `IMAGE_SCN_MEM_DISCARDABLE`. -/
private def isDiscarded (flags : Nat) : Bool :=
  flags &&& 0x800 != 0 || flags &&& 0x200 != 0 || flags &&& 0x02000000 != 0

private def isMapped (object : ObjectSection) : Bool :=
  !isDiscarded object.info.flags

/-- `IMAGE_SCN_ALIGN_*`: bits 20-23 hold the logarithm of the alignment plus one. -/
private def sectionAlignment (flags : Nat) : Nat :=
  match (flags >>> 20) % 16 with
  | 0 => 1
  | shift + 1 => 2 ^ shift

/-- Lays a section out at the cursor. All sections of an object claim address 0, so unlike an image's they have to be
placed for relocations between them to mean anything. A nonzero `VirtualAddress` is a lower bound. -/
private def placeObject (cursor : Nat) (object : ObjectSection) : ObjectSection × Nat :=
  if isMapped object then
    let addr := alignUp (max cursor object.info.addr) (sectionAlignment object.info.flags)
    ({ object with
      info := { object.info with addr }
      segment := { object.segment with addr }
      region := { object.region with addr } }, addr + object.segment.size)
  else
    (object, cursor)

private def placeObjects (cursor : Nat) : List ObjectSection → List ObjectSection
  | [] => []
  | object :: rest =>
    let (placed, cursor) := placeObject cursor object
    placed :: placeObjects cursor rest

private def architecture (machine : Nat) : Arch × Nat :=
  match machine with
  | 0x8664 => (.x86_64, 64)
  | 0xaa64 => (.aarch64, 64)
  | 0x014c => (.x86, 32)
  | 0x01c0 | 0x01c4 => (.arm, 32)
  | 0x5032 => (.riscv, 32)
  | 0x5064 => (.riscv, 64)
  | _ => (.unknown, 32)

/-- Whether a symbol is undefined, as its section number says. -/
private def isUndefined (data : ByteArray) (header : Header) (entry : Nat × Symbol) : Bool :=
  !entry.2.name.isEmpty && (IO.Reader.u16 data .little (header.symbolOffset + entry.1 * 18 + 12)).toOption == some 0

/-- Gives the undefined symbols that `select` picks storage after the cursor, each of `size` bytes, so that nothing
relocated against them lands on a section. The storage is reported as a region, of which they are the only contents. -/
private def placeUndefined (data : ByteArray) (header : Header) (word : Nat) (select : Nat → Bool) (size : Nat → Nat)
    (cursor : Nat) : List (Nat × Symbol) → List (Nat × Symbol) × Nat
  | [] => ([], cursor)
  | entry :: rest =>
    if isUndefined data header entry && select entry.2.addr then
      let addr := alignUp cursor word
      let (placed, cursor) := placeUndefined data header word select size (addr + size entry.2.addr) rest
      ((entry.1, { entry.2 with addr }) :: placed, cursor)
    else
      let (placed, cursor) := placeUndefined data header word select size cursor rest
      (entry :: placed, cursor)

private def zeroRegion (name : String) (start stop : Nat) (writable : Bool) : List (Segment × MemRegion) :=
  if stop > start then
    [(⟨name, start, stop - start, true, writable, false⟩,
      ⟨start, ByteArray.mk (Array.replicate (stop - start) 0), true, writable, false⟩)]
  else []

/-- Decodes an object file, with the relocations that could not be applied. Like upstream's linker for ELF files,
it maps what occupies memory after laying it out, then commons (undefined symbols with a size) in `%common` and
externals in `EXTERNAL`. Upstream's COFF loader instead hides all but the executable sections, as they all have the
same address, and applies no relocations; once the sections are laid out there is nothing left to hide. -/
def decodeReport (data : ByteArray) : Except String (Image × List String) := do
  let header ← parseHeader data
  let parsed ← parseSections data header
  let placed := placeObjects 0 parsed
  let sections := placed.map fun object => object.info
  let word := (architecture header.machine).2 / 8
  let parsedSymbols ← parseSymbols data header sections 0 header.symbolCount []
  let commonsStart := alignUp (placed.foldl (fun cursor object =>
    if isMapped object then max cursor (object.info.addr + object.segment.size) else cursor) 0) word
  let (commons, commonsEnd) := placeUndefined data header word (· != 0) id commonsStart parsedSymbols
  let externalsStart := alignUp commonsEnd word
  let (indexedSymbols, externalsEnd) := placeUndefined data header word (· == 0) (fun _ => word) externalsStart commons
  let relocated := placed.map fun object =>
    if isMapped object then applyRelocations data header sections indexedSymbols object else (object, [])
  let mapped := (relocated.map Prod.fst).filter fun object => isMapped object && object.segment.size != 0
  let extra := zeroRegion "%common" commonsStart commonsEnd true ++ zeroRegion "EXTERNAL" externalsStart externalsEnd false
  let segments := mapped.map (fun object => object.segment) ++ extra.map Prod.fst
  let regions := mapped.map (fun object => object.region) ++ extra.map Prod.snd
  let symbols := indexedSymbols.map Prod.snd
  let memory := regions.foldl (fun memory region => MemoryMap.add region () memory) {}
  let (arch, addrWidth) := architecture header.machine
  .ok ({
    arch := arch
    addrWidth := addrWidth
    endian := .little
    entryPoint := 0
    data := data
    sections := sections
    segments := segments
    symbols := symbols
    memory := memory
  }, relocated.flatMap Prod.snd)

def decode (data : ByteArray) : Except String Image := do
  let (image, _) ← decodeReport data
  .ok image

def load (path : String) : IO Image := do
  let data ← IO.FS.readBinFile path
  match decode data with
  | .ok image => pure image
  | .error error => throw <| IO.userError error

end Bap.Image.Coff
