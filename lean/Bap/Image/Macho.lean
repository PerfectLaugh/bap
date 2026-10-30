import Bap.Image.Basic
import Bap.IO.Reader

namespace Bap.Image.Macho

private structure Header where
  endian : Endian
  cpuType : Nat
  commandCount : Nat
  commandBytes : Nat

private structure FileMapping where
  offset : Nat
  size : Nat
  address : Nat

private structure SymbolTable where
  offset : Nat
  count : Nat
  stringsOffset : Nat
  stringsSize : Nat

private structure ParseState where
  segments : List Segment := []
  regions : List MemRegion := []
  sections : List Section := []
  mappings : List FileMapping := []
  symbolTables : List SymbolTable := []
  entryOffset : Option Nat := none

private def parseHeader (data : ByteArray) : Except String Header := do
  let magic ← IO.Reader.read data .big 0 4
  let endian ← match magic with
    | 0xcffaedfe => .ok Endian.little
    | 0xfeedfacf => .ok Endian.big
    | _ => .error "not a 64-bit Mach-O file"
  let cpuType ← IO.Reader.u32 data endian 4
  let commandCount ← IO.Reader.u32 data endian 16
  let commandBytes ← IO.Reader.u32 data endian 20
  if 32 + commandBytes > data.size then
    .error "Mach-O load commands exceed input"
  else
    .ok ⟨endian, cpuType, commandCount, commandBytes⟩

private def fixedString (data : ByteArray) (offset size : Nat) : Except String String := do
  let bytes ← IO.Reader.slice data offset size
  .ok (String.ofList ((bytes.toList.takeWhile fun byte => byte != 0).map fun byte => Char.ofNat byte.toNat))

private def parseSection (data : ByteArray) (endian : Endian) (offset : Nat) :
    Except String Section := do
  let name ← fixedString data offset 16
  let address ← IO.Reader.u64 data endian (offset + 32)
  let size ← IO.Reader.u64 data endian (offset + 40)
  let fileOffset ← IO.Reader.u32 data endian (offset + 48)
  let flags ← IO.Reader.u32 data endian (offset + 64)
  .ok ⟨name, address, fileOffset, size, flags, flags &&& 0xff⟩

private def parseSegment (data : ByteArray) (endian : Endian) (offset commandSize : Nat) :
    Except String (Segment × MemRegion × FileMapping × List Section) := do
  if commandSize < 72 then
    .error "Mach-O segment command is too small"
  else
    let name ← fixedString data (offset + 8) 16
    let address ← IO.Reader.u64 data endian (offset + 24)
    let memorySize ← IO.Reader.u64 data endian (offset + 32)
    let fileOffset ← IO.Reader.u64 data endian (offset + 40)
    let fileSize ← IO.Reader.u64 data endian (offset + 48)
    let protection ← IO.Reader.u32 data endian (offset + 60)
    let sectionCount ← IO.Reader.u32 data endian (offset + 64)
    if 72 + sectionCount * 80 > commandSize then
      .error "Mach-O sections exceed segment command"
    else if fileSize > memorySize then
      .error "Mach-O segment file size exceeds memory size"
    else
      let fileBytes ← IO.Reader.slice data fileOffset fileSize
      let bytes := fileBytes.append (ByteArray.mk (Array.replicate (memorySize - fileSize) 0))
      let sections ← (List.range sectionCount).mapM fun index =>
        parseSection data endian (offset + 72 + index * 80)
      let readable := protection &&& 1 != 0
      let writable := protection &&& 2 != 0
      let executable := protection &&& 4 != 0
      .ok (⟨name, address, memorySize, readable, writable, executable⟩,
        ⟨address, bytes, readable, writable, executable⟩,
        ⟨fileOffset, fileSize, address⟩, sections)

private def parseCommands (data : ByteArray) (header : Header) (offset : Nat) :
    Nat → ParseState → Except String (Nat × ParseState)
  | 0, state => .ok (offset, state)
  | remaining + 1, state => do
    let command ← IO.Reader.u32 data header.endian offset
    let commandSize ← IO.Reader.u32 data header.endian (offset + 4)
    if commandSize < 8 then
      .error "Mach-O load command is too small"
    else if offset + commandSize > 32 + header.commandBytes then
      .error "Mach-O load command exceeds command region"
    else
      let state ← match command with
        | 0x19 => do
          let (segment, region, mapping, sections) ← parseSegment data header.endian offset commandSize
          .ok { state with
            segments := state.segments ++ [segment]
            regions := state.regions ++ [region]
            mappings := state.mappings ++ [mapping]
            sections := state.sections ++ sections }
        | 0x80000028 => do
          if commandSize < 24 then
            .error "Mach-O entry command is too small"
          else
            let entryOffset ← IO.Reader.u64 data header.endian (offset + 8)
            .ok { state with entryOffset := some entryOffset }
        | 2 => do
          if commandSize < 24 then
            .error "Mach-O symbol table command is too small"
          else
            let tableOffset ← IO.Reader.u32 data header.endian (offset + 8)
            let count ← IO.Reader.u32 data header.endian (offset + 12)
            let stringsOffset ← IO.Reader.u32 data header.endian (offset + 16)
            let stringsSize ← IO.Reader.u32 data header.endian (offset + 20)
            if tableOffset + count * 16 > data.size || stringsOffset + stringsSize > data.size then
              .error "Mach-O symbol table exceeds input"
            else
              .ok { state with symbolTables := state.symbolTables ++ [⟨tableOffset, count, stringsOffset, stringsSize⟩] }
        | _ => .ok state
      parseCommands data header (offset + commandSize) remaining state

private def parseSymbol (data : ByteArray) (endian : Endian) (stringsOffset stringsSize : Nat)
    (sections : List Section) (offset : Nat) : Except String (Option Symbol) := do
  let nameOffset ← IO.Reader.u32 data endian offset
  if nameOffset = 0 then
    .ok none
  else if nameOffset ≥ stringsSize then
    .error "Mach-O symbol name exceeds string table"
  else
    let name ← IO.Reader.cstring data (stringsOffset + nameOffset)
    let kind ← IO.Reader.get8 data (offset + 4)
    let sectionIndex ← IO.Reader.get8 data (offset + 5)
    let address ← IO.Reader.u64 data endian (offset + 8)
    let isFunction := match sectionOfNumber sections sectionIndex with
      | some sec => sec.flags &&& 0x00000400 != 0
      | none => false
    .ok (some ⟨name, address, 0, isFunction, kind &&& 0xe0 != 0⟩)

private def parseSymbols (data : ByteArray) (header : Header) (state : ParseState) :
    Except String (List Symbol) :=
  state.symbolTables.foldlM (init := []) fun symbols table => do
    let parsed ← (List.range table.count).mapM fun index =>
      parseSymbol data header.endian table.stringsOffset table.stringsSize state.sections
        (table.offset + index * 16)
    .ok (symbols ++ parsed.filterMap id)

private def architecture (cpuType : Nat) : Arch :=
  match cpuType with
  | 0x01000007 => .x86_64
  | 0x0100000c => .aarch64
  | _ => .unknown

def decode (data : ByteArray) : Except String Image := do
  let header ← parseHeader data
  let (finalOffset, state) ← parseCommands data header 32 header.commandCount {}
  if finalOffset != 32 + header.commandBytes then
    .error "Mach-O load command size mismatch"
  else
    let entryPoint ← match state.entryOffset with
      | none => .ok 0
      | some entryOffset =>
        match state.mappings.find? fun mapping =>
          mapping.offset ≤ entryOffset && entryOffset < mapping.offset + mapping.size with
        | some mapping => .ok (mapping.address + entryOffset - mapping.offset)
        | none => .error "Mach-O entry point is outside mapped segments"
    let symbols ← parseSymbols data header state
    let memory := state.regions.foldl (fun memory region => MemoryMap.add region () memory) {}
    .ok {
      arch := architecture header.cpuType
      addrWidth := 64
      endian := header.endian
      entryPoint := entryPoint
      data := data
      sections := state.sections
      segments := state.segments
      symbols := symbols
      memory := memory
    }

def load (path : String) : IO Image := do
  let data ← IO.FS.readBinFile path
  match decode data with
  | .ok image => pure image
  | .error error => throw <| IO.userError error

end Bap.Image.Macho
