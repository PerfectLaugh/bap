import Bap.Image.Raw
import Bap.IO.Reader

namespace Bap.Image.Elf

structure Header where
  is64 : Bool
  endian : Endian
  machine : Nat
  entryPoint : Nat
  programOffset : Nat
  sectionOffset : Nat
  programEntrySize : Nat
  programCount : Nat
  sectionEntrySize : Nat
  sectionCount : Nat
  stringSectionIndex : Nat

structure SectionHeader where
  nameOffset : Nat
  kind : Nat
  flags : Nat
  addr : Nat
  offset : Nat
  size : Nat
  link : Nat
  entrySize : Nat

private def word (data : ByteArray) (endian : Endian) (is64 : Bool) (offset : Nat) : Except String Nat :=
  if is64 then IO.Reader.u64 data endian offset else IO.Reader.u32 data endian offset

private def parseHeader (data : ByteArray) : Except String Header := do
  let magic ← IO.Reader.read data .big 0 4
  if magic != 0x7f454c46 then
    .error "not an ELF file"
  else
    let elfClass ← IO.Reader.get8 data 4
    let encoding ← IO.Reader.get8 data 5
    let is64 ← match elfClass with
      | 1 => .ok false
      | 2 => .ok true
      | _ => .error s!"unsupported ELF class {elfClass}"
    let endian ← match encoding with
      | 1 => .ok .little
      | 2 => .ok .big
      | _ => .error s!"unsupported ELF encoding {encoding}"
    let machine ← IO.Reader.u16 data endian 18
    let entryPoint ← word data endian is64 24
    let programOffset ← word data endian is64 (if is64 then 32 else 40)
    let sectionOffset ← word data endian is64 (if is64 then 40 else 48)
    let programEntrySize ← IO.Reader.u16 data endian (if is64 then 54 else 42)
    let programCount ← IO.Reader.u16 data endian (if is64 then 56 else 44)
    let sectionEntrySize ← IO.Reader.u16 data endian (if is64 then 58 else 46)
    let sectionCount ← IO.Reader.u16 data endian (if is64 then 60 else 48)
    let stringSectionIndex ← IO.Reader.u16 data endian (if is64 then 62 else 50)
    .ok {
      is64 := is64
      endian := endian
      machine := machine
      entryPoint := entryPoint
      programOffset := programOffset
      sectionOffset := sectionOffset
      programEntrySize := programEntrySize
      programCount := programCount
      sectionEntrySize := sectionEntrySize
      sectionCount := sectionCount
      stringSectionIndex := stringSectionIndex
    }

private def parseProgramHeader (data : ByteArray) (header : Header) (offset : Nat) :
    Except String (Option (Segment × MemRegion)) := do
  let kind ← IO.Reader.u32 data header.endian offset
  if kind != 1 then
    .ok none
  else
    let flags ← IO.Reader.u32 data header.endian (offset + 4)
    let offset' ← word data header.endian header.is64 (offset + 8)
    let address ← word data header.endian header.is64 (offset + if header.is64 then 16 else 12)
    let fileSize ← word data header.endian header.is64 (offset + if header.is64 then 32 else 20)
    let memorySize ← word data header.endian header.is64 (offset + if header.is64 then 40 else 24)
    if fileSize > memorySize then
      .error "ELF LOAD file size exceeds memory size"
    else
      let fileBytes ← IO.Reader.slice data offset' fileSize
      let bytes := fileBytes.append (ByteArray.mk (Array.replicate (memorySize - fileSize) 0))
      let readable := flags &&& 4 != 0
      let writable := flags &&& 2 != 0
      let executable := flags &&& 1 != 0
      .ok (some (⟨"LOAD", address, memorySize, readable, writable, executable⟩,
        ⟨address, bytes, readable, writable, executable⟩))

private def parseSections (data : ByteArray) (header : Header) : Except String (List SectionHeader) := do
  let minimum := if header.is64 then 64 else 40
  if header.sectionCount = 0 then
    .ok []
  else if header.sectionEntrySize < minimum then
    .error "ELF section entries are too small"
  else
    (List.range header.sectionCount).mapM fun index => do
      let offset := header.sectionOffset + index * header.sectionEntrySize
      let nameOffset ← IO.Reader.u32 data header.endian offset
      let kind ← IO.Reader.u32 data header.endian (offset + 4)
      let flags ← word data header.endian header.is64 (offset + 8)
      let addr ← word data header.endian header.is64 (offset + if header.is64 then 16 else 12)
      let offset' ← word data header.endian header.is64 (offset + if header.is64 then 24 else 16)
      let size ← word data header.endian header.is64 (offset + if header.is64 then 32 else 20)
      let link ← IO.Reader.u32 data header.endian (offset + if header.is64 then 40 else 24)
      let entrySize ← word data header.endian header.is64 (offset + if header.is64 then 56 else 36)
      .ok ⟨nameOffset, kind, flags, addr, offset', size, link, entrySize⟩

private def parseSegments (data : ByteArray) (header : Header) :
    Except String (List Segment × List MemRegion) := do
  let minimum := if header.is64 then 56 else 32
  if header.programEntrySize < minimum then
    .error "ELF program entries are too small"
  else
    let entries ← (List.range header.programCount).mapM fun index =>
      parseProgramHeader data header (header.programOffset + index * header.programEntrySize)
    .ok (entries.filterMap id).unzip

private def resolveSectionNames (data : ByteArray) (header : Header) (sections : List SectionHeader) :
    Except String (List Section) := do
  match sections with
  | [] => .ok []
  | _ =>
    match sections[header.stringSectionIndex]? with
    | none => .error "missing ELF section-name string table"
    | some strings =>
      sections.mapM fun sh => do
        let name ← IO.Reader.cstring data (strings.offset + sh.nameOffset)
        .ok ⟨name, sh.addr, sh.offset, sh.size, sh.flags, sh.kind⟩

private def parseSymbol (data : ByteArray) (header : Header) (strings : SectionHeader)
    (offset : Nat) : Except String (Option Symbol) := do
  let nameOffset ← IO.Reader.u32 data header.endian offset
  let info ← IO.Reader.get8 data (offset + if header.is64 then 4 else 12)
  let size ← word data header.endian header.is64 (offset + if header.is64 then 16 else 8)
  let value ← word data header.endian header.is64 (offset + if header.is64 then 8 else 4)
  if nameOffset = 0 then
    .ok none
  else
    let name ← IO.Reader.cstring data (strings.offset + nameOffset)
    .ok (some ⟨name, value, size, info &&& 0xf = 2, false⟩)

private def parseSymbols (data : ByteArray) (header : Header) (sections : List SectionHeader) :
    Except String (List Symbol) := do
  let symbols ← sections.foldlM (init := []) fun symbols sh => do
    if sh.kind != 2 && sh.kind != 11 then
      .ok symbols
    else
      match sections[sh.link]? with
      | none => .error "missing ELF symbol string table"
      | some strings =>
        let entrySize := if sh.entrySize = 0 then (if header.is64 then 24 else 16) else sh.entrySize
        let count := sh.size / entrySize
        let parsed ← (List.range count).mapM fun index =>
          parseSymbol data header strings (sh.offset + index * entrySize)
        .ok (symbols ++ parsed.filterMap id)
  .ok symbols

private def architecture (machine : Nat) : Arch :=
  match machine with
  | 3 => .x86
  | 62 => .x86_64
  | 40 => .arm
  | 183 => .aarch64
  | 8 => .mips
  | 20 | 21 => .powerpc
  | 243 => .riscv
  | 22 => .systemz
  | _ => .unknown

def decode (data : ByteArray) : Except String Image := do
  let header ← parseHeader data
  let (segments, regions) ← parseSegments data header
  let sectionHeaders ← parseSections data header
  let sections ← resolveSectionNames data header sectionHeaders
  let symbols ← parseSymbols data header sectionHeaders
  let memory := regions.foldl (fun memory region => MemoryMap.add region () memory) {}
  .ok {
    arch := architecture header.machine
    addrWidth := if header.is64 then 64 else 32
    endian := header.endian
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

end Bap.Image.Elf
