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
    let programOffset ← word data endian is64 (if is64 then 32 else 28)
    let sectionOffset ← word data endian is64 (if is64 then 40 else 32)
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
    let flags ← IO.Reader.u32 data header.endian (offset + if header.is64 then 4 else 24)
    let offset' ← word data header.endian header.is64 (offset + if header.is64 then 8 else 4)
    let address ← word data header.endian header.is64 (offset + if header.is64 then 16 else 8)
    let fileSize ← word data header.endian header.is64 (offset + if header.is64 then 32 else 16)
    let memorySize ← word data header.endian header.is64 (offset + if header.is64 then 40 else 20)
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
  if header.programCount = 0 then
    .ok ([], [])
  else if header.programEntrySize < minimum then
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

/-- The address of a symbol: bit 0 of an ARM function's value is the Thumb flag, not part of its address. -/
private def codeAddress (machine typ value : Nat) : Nat :=
  if machine = 40 && typ = 2 then value - value % 2 else value

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
    .ok (some ⟨name, codeAddress header.machine (info &&& 0xf) value, size, info &&& 0xf = 2, false⟩)

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

structure DynamicSymbol where
  name : String
  value : Nat
  size : Nat
  typ : Nat
  binding : Nat
  sectionIndex : Nat
  deriving Repr

structure DynamicRelocation where
  offset : Nat
  typ : Nat
  symbol : Nat
  addend : Nat
  explicitAddend : Bool
  deriving Repr

structure RelocationSpec where
  references : List (Nat × String) := []
  absolute : List (Nat × Nat) := []
  relative : List Nat := []
  relativeAddends : List (Nat × Nat) := []
  irelative : List (Nat × Nat) := []
  deriving Repr

structure Import where
  slot : Nat
  name : String
  address : Nat
  isObject : Bool
  deriving Repr

structure ProgramHeader where
  kind : Nat
  flags : Nat
  offset : Nat
  addr : Nat
  fileSize : Nat
  memorySize : Nat

def programHeaders (data : ByteArray) : Except String (List ProgramHeader) := do
  let header ← parseHeader data
  let minimum := if header.is64 then 56 else 32
  if header.programCount = 0 then
    .ok []
  else if header.programEntrySize < minimum then
    .error "ELF program entries are too small"
  else
    (List.range header.programCount).mapM fun index => do
      let entry := header.programOffset + index * header.programEntrySize
      let kind ← IO.Reader.u32 data header.endian entry
      let flags ← IO.Reader.u32 data header.endian (entry + if header.is64 then 4 else 24)
      let offset ← word data header.endian header.is64 (entry + if header.is64 then 8 else 4)
      let addr ← word data header.endian header.is64 (entry + if header.is64 then 16 else 8)
      let fileSize ← word data header.endian header.is64 (entry + if header.is64 then 32 else 16)
      let memorySize ← word data header.endian header.is64 (entry + if header.is64 then 40 else 20)
      .ok ⟨kind, flags, offset, addr, fileSize, memorySize⟩

private def offsetOf (headers : List ProgramHeader) (dataSize addr size : Nat) : Option Nat :=
  headers.findSome? fun header =>
    if header.kind != 1 || addr < header.addr then none
    else
      let delta := addr - header.addr
      if delta > header.fileSize || header.fileSize - delta < size then none
      else
        let offset := header.offset + delta
        if offset ≤ dataSize && dataSize - offset ≥ size then some offset else none

def dynamicTags (data : ByteArray) (headers : List ProgramHeader) (is64 : Bool) (endian : Endian) :
    Except String (List (Nat × Nat)) := do
  match headers.find? fun header => header.kind = 2 with
  | none => .ok []
  | some segment =>
    if segment.offset > data.size || data.size - segment.offset < segment.fileSize then
      .error "ELF dynamic segment exceeds input"
    else
      let entrySize := if is64 then 16 else 8
      let rec readEntries (remaining offset : Nat) (tags : List (Nat × Nat)) : Except String (List (Nat × Nat)) := do
        match remaining with
        | 0 => .ok tags.reverse
        | remaining + 1 =>
          let tag ← word data endian is64 offset
          if tag = 0 then .ok tags.reverse
          else
            let value ← word data endian is64 (offset + if is64 then 8 else 4)
            readEntries remaining (offset + entrySize) ((tag, value) :: tags)
      readEntries (segment.fileSize / entrySize) segment.offset []

private def tagValue (tags : List (Nat × Nat)) (tag : Nat) : Option Nat :=
  (tags.find? fun entry => entry.1 = tag).map Prod.snd

private def dynamicString (image : Image) (headers : List ProgramHeader) (strings size offset : Nat) : String :=
  if offset ≥ size then ""
  else
    match offsetOf headers image.data.size (strings + offset) (size - offset) with
    | none => ""
    | some fileOffset =>
      let bytes := image.data.extract fileOffset (fileOffset + size - offset)
      String.ofList (bytes.toList.takeWhile (· != 0) |>.map fun byte => Char.ofNat byte.toNat)

def dynamicSymbol (image : Image) (headers : List ProgramHeader) (tags : List (Nat × Nat))
    (index : Nat) : Except String (Option DynamicSymbol) := do
  let header ← parseHeader image.data
  let minimum := if header.is64 then 24 else 16
  match tagValue tags 6 with
  | none => .ok none
  | some symbols =>
    let entrySize := (tagValue tags 11).getD minimum
    if entrySize < minimum then .ok none
    else
      match offsetOf headers image.data.size (symbols + index * entrySize) minimum with
      | none => .ok none
      | some offset =>
        let nameOffset ← IO.Reader.u32 image.data image.endian offset
        let info ← IO.Reader.get8 image.data (offset + if header.is64 then 4 else 12)
        let sectionIndex ← IO.Reader.u16 image.data image.endian (offset + if header.is64 then 6 else 14)
        let value ← word image.data image.endian header.is64 (offset + if header.is64 then 8 else 4)
        let size ← word image.data image.endian header.is64 (offset + if header.is64 then 16 else 8)
        let name := match tagValue tags 5, tagValue tags 10 with
          | some strings, some size => dynamicString image headers strings size nameOffset
          | _, _ => ""
        .ok (some ⟨name, value, size, info &&& 0xf, info >>> 4, sectionIndex⟩)

def readRelocationTable (image : Image) (headers : List ProgramHeader) (addr size : Nat)
    (rela : Bool) : Except String (List DynamicRelocation) := do
  let header ← parseHeader image.data
  match offsetOf headers image.data.size addr size with
  | none => .ok []
  | some offset =>
    let entrySize := if header.is64 then (if rela then 24 else 16) else (if rela then 12 else 8)
    (List.range (size / entrySize)).mapM fun index => do
      let entry := offset + index * entrySize
      let offset ← word image.data image.endian header.is64 entry
      let info ← word image.data image.endian header.is64 (entry + if header.is64 then 8 else 4)
      let addend ← if rela then word image.data image.endian header.is64 (entry + if header.is64 then 16 else 8) else .ok 0
      let typ := if header.is64 then info % 0x100000000 else info % 0x100
      let symbol := if header.is64 then info / 0x100000000 else info / 0x100
      .ok ⟨offset, typ, symbol, addend, rela⟩

private def sleb128 (data : ByteArray) (offset : Nat) : Option (Nat × Nat) :=
  let rec loop (fuel offset shift value : Nat) : Option (Nat × Nat) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if offset ≥ data.size then none
      else
        let byte := data[offset]!.toNat
        let digit := if shift < 64 then (byte &&& 0x7f) * 2 ^ shift else 0
        let value := (value + digit) % 0x10000000000000000
        let shift := shift + 7
        if byte &&& 0x80 != 0 then loop fuel (offset + 1) shift value
        else
          let value := if shift < 64 && byte &&& 0x40 != 0 then
            (value + 0x10000000000000000 - 2 ^ shift) % 0x10000000000000000
          else value
          some (value, offset + 1)
  loop (data.size - offset + 1) offset 0 0

private def readAndroidRelocations (image : Image) (headers : List ProgramHeader) (addr size : Nat)
    (rela : Bool) : List DynamicRelocation :=
  let machine := (parseHeader image.data).toOption.map (·.machine) |>.getD 0
  let is64 := (parseHeader image.data).toOption.map (·.is64) |>.getD true
  match offsetOf headers image.data.size addr size with
  | none => []
  | some offset =>
    let bytes := image.data.extract offset (offset + size)
    if size < 4 || bytes.extract 0 4 != (ByteArray.mk #[65, 80, 83, 50]) then []
    else
      match sleb128 bytes 4 with
      | none => []
      | some (count, afterCount) =>
        match sleb128 bytes afterCount with
        | none => []
        | some (initialOffset, cursor) =>
          if count > 16777216 then []
          else
            let rec groups (remaining cursor offset addend : Nat) (result : List DynamicRelocation) :
                Option (List DynamicRelocation) :=
              if remaining = 0 then some result
              else
                match sleb128 bytes cursor with
                | none => none
                | some (group, cursor) =>
                  match sleb128 bytes cursor with
                  | none => none
                  | some (flags, cursor) =>
                    if h : group = 0 || group > remaining then none
                    else
                      have bounds : group ≠ 0 ∧ group ≤ remaining := by
                        simp only [decide_eq_true_eq, Bool.or_eq_true, not_or] at h
                        exact ⟨h.1, Nat.le_of_not_gt h.2⟩
                      let byInfo := flags &&& 1 != 0
                      let byOffset := flags &&& 2 != 0
                      let byAddend := flags &&& 4 != 0
                      let hasAddend := flags &&& 8 != 0
                      let offsetDelta := if byOffset then (sleb128 bytes cursor).map Prod.fst else some 0
                      let afterOffset := if byOffset then (sleb128 bytes cursor).map Prod.snd else some cursor
                      match offsetDelta, afterOffset with
                      | some offsetDelta, some cursor =>
                        let info := if byInfo then (sleb128 bytes cursor).map Prod.fst else some 0
                        let afterInfo := if byInfo then (sleb128 bytes cursor).map Prod.snd else some cursor
                        match info, afterInfo with
                        | some sharedInfo, some cursor =>
                          let (addend, cursor) := if rela && byAddend && hasAddend then
                            match sleb128 bytes cursor with
                            | some (delta, next) => ((addend + delta) % 0x10000000000000000, next)
                            | none => (addend, bytes.size + 1)
                          else (if hasAddend then addend else 0, cursor)
                          let rec entries (left cursor offset addend : Nat) (result : List DynamicRelocation) :
                              Option (Nat × Nat × Nat × List DynamicRelocation) :=
                            if left = 0 then some (cursor, offset, addend, result)
                            else
                              let delta := if byOffset then some offsetDelta else (sleb128 bytes cursor).map Prod.fst
                              let next := if byOffset then some cursor else (sleb128 bytes cursor).map Prod.snd
                              match delta, next with
                              | some delta, some cursor =>
                                let offset := (offset + delta) % 0x10000000000000000
                                let info := if byInfo then some sharedInfo else (sleb128 bytes cursor).map Prod.fst
                                let next := if byInfo then some cursor else (sleb128 bytes cursor).map Prod.snd
                                match info, next with
                                | some info, some cursor =>
                                  let (addend, cursor) := if rela && hasAddend && !byAddend then
                                    match sleb128 bytes cursor with
                                    | some (delta, next) => ((addend + delta) % 0x10000000000000000, next)
                                    | none => (addend, bytes.size + 1)
                                  else (addend, cursor)
                                  let typ := if is64 then info % 0x100000000 else info % 0x100
                                  let symbol := if is64 then info / 0x100000000 else info / 0x100
                                  entries (left - 1) cursor offset addend
                                    (result ++ [⟨offset, typ, symbol, addend, rela⟩])
                                | _, _ => none
                              | _, _ => none
                          match entries group cursor offset addend result with
                          | none => none
                          | some (cursor, offset, addend, result) =>
                            have groupPositive : 0 < group := by omega
                            have groupWithin : group ≤ remaining := by omega
                            groups (remaining - group) cursor offset addend result
                        | _, _ => none
                      | _, _ => none
            termination_by remaining
            decreasing_by omega
            (groups count cursor initialOffset 0 []).getD []

private def relativeType (machine : Nat) : Nat :=
  match machine with
  | 3 => 8
  | 8 => 3
  | 40 => 23
  | 62 => 8
  | 183 => 1027
  | 20 | 21 => 22
  | 243 => 3
  | _ => 0

private def irelativeType (machine : Nat) : Nat :=
  match machine with
  | 3 => 42
  | 40 => 160
  | 62 => 37
  | 183 => 1032
  | 20 | 21 => 248
  | 243 => 58
  | _ => 0

private def symbolRelocationKind (machine typ : Nat) (is64 : Bool) : Nat :=
  match machine with
  | 3 => if typ = 1 then 1 else if typ = 6 || typ = 7 then 2 else 0
  | 40 => if typ = 2 then 1 else if typ = 21 || typ = 22 then 2 else 0
  | 62 => if typ = 1 then 1 else if typ = 6 || typ = 7 then 2 else 0
  | 183 => if typ = 257 then 1 else if typ = 1025 || typ = 1026 then 2 else 0
  | 20 => if typ = 1 then 1 else if typ = 20 || typ = 21 then 2 else 0
  | 21 => if typ = 38 then 1 else if typ = 20 || typ = 21 then 2 else 0
  | 243 => if typ = (if is64 then 2 else 1) then 1 else if typ = 5 then 2 else 0
  | _ => 0

private def readRelrRelocations (image : Image) (headers : List ProgramHeader) (addr size machine : Nat) :
    Except String (List DynamicRelocation) := do
  let header ← parseHeader image.data
  let width := if header.is64 then 8 else 4
  match offsetOf headers image.data.size addr size with
  | none => .ok []
  | some offset =>
    let entries ← (List.range (size / width)).mapM fun index =>
      word image.data image.endian header.is64 (offset + index * width)
    let rec decode (entries : List Nat) (base : Nat) (result : List DynamicRelocation) : List DynamicRelocation :=
      match entries with
      | [] => result.reverse
      | entry :: rest =>
        if entry % 2 = 0 then
          decode rest (entry + width) (⟨entry, relativeType machine, 0, 0, false⟩ :: result)
        else
          let rec bits (value index : Nat) (result : List DynamicRelocation) : List DynamicRelocation :=
            if value = 0 then result
            else
              let result := if value % 2 = 1 then
                ⟨base + index * width, relativeType machine, 0, 0, false⟩ :: result
              else result
              bits (value / 2) (index + 1) result
          let result := bits (entry / 2) 0 result
          decode rest (base + (8 * width - 1) * width) result
    .ok (decode entries 0 [])

private def storedWord (image : Image) (headers : List ProgramHeader) (address : Nat) : Option Nat :=
  match offsetOf headers image.data.size address (image.addrWidth / 8) with
  | none => none
  | some offset =>
    (if image.addrWidth = 64 then IO.Reader.u64 image.data image.endian offset
      else IO.Reader.u32 image.data image.endian offset).toOption

def initializerArray (image : Image) : Except String (Option (Nat × Nat)) := do
  let header ← parseHeader image.data
  let headers ← programHeaders image.data
  let tags ← dynamicTags image.data headers header.is64 image.endian
  match tagValue tags 25, tagValue tags 27 with
  | some address, some size =>
    if size % (image.addrWidth / 8) = 0 then .ok (some (address, size))
    else .error "ELF initializer array size is not pointer-aligned"
  | none, none => .ok none
  | _, _ => .error "ELF initializer array tags are incomplete"

def dynamicRelocations (image : Image) : Except String RelocationSpec := do
  let header ← parseHeader image.data
  let headers ← programHeaders image.data
  let tags ← dynamicTags image.data headers header.is64 image.endian
  if tags.isEmpty then .ok {}
  else
    let mut relocations : List DynamicRelocation := []
    match tagValue tags 7, tagValue tags 8 with
    | some addr, some size => relocations := relocations ++ (← readRelocationTable image headers addr size true)
    | _, _ => pure ()
    match tagValue tags 17, tagValue tags 18 with
    | some addr, some size => relocations := relocations ++ (← readRelocationTable image headers addr size false)
    | _, _ => pure ()
    match tagValue tags 23, tagValue tags 2 with
    | some addr, some size =>
      let rela := match tagValue tags 20 with
        | some kind => kind = 7
        | none => (tagValue tags 7).isSome
      relocations := relocations ++ (← readRelocationTable image headers addr size rela)
    | _, _ => pure ()
    match tagValue tags 0x60000011, tagValue tags 0x60000012 with
    | some addr, some size => relocations := relocations ++ readAndroidRelocations image headers addr size true
    | _, _ => pure ()
    match tagValue tags 0x6000000f, tagValue tags 0x60000010 with
    | some addr, some size => relocations := relocations ++ readAndroidRelocations image headers addr size false
    | _, _ => pure ()
    match tagValue tags 36, tagValue tags 35 with
    | some addr, some size => relocations := relocations ++ (← readRelrRelocations image headers addr size header.machine)
    | _, _ => pure ()
    match tagValue tags 0x6fffe000, tagValue tags 0x6fffe001 with
    | some addr, some size => relocations := relocations ++ (← readRelrRelocations image headers addr size header.machine)
    | _, _ => pure ()
    let result ← relocations.foldlM (init := ({} : RelocationSpec)) fun result relocation => do
      let stored := storedWord image headers relocation.offset
      let addend := if relocation.explicitAddend then relocation.addend else stored.getD 0
      if relocation.symbol = 0 then
        if relocation.typ = irelativeType header.machine && irelativeType header.machine != 0 then
          .ok { result with irelative :=
            if relocation.explicitAddend || stored.isSome then (relocation.offset, addend) :: result.irelative
            else result.irelative }
        else if relativeType header.machine = 0 || relocation.typ != relativeType header.machine then .ok result
        else
          let relativeAddends := match stored with
            | some value => if relocation.explicitAddend && value != addend then
                (relocation.offset, addend) :: result.relativeAddends
              else result.relativeAddends
            | none => result.relativeAddends
          .ok { result with relative := relocation.offset :: result.relative, relativeAddends }
      else
        match ← dynamicSymbol image headers tags relocation.symbol with
        | none => .ok result
        | some symbol =>
          let kind := symbolRelocationKind header.machine relocation.typ header.is64
          if symbol.typ = 10 && symbol.sectionIndex != 0 && kind != 0 then
            .ok { result with irelative := (relocation.offset, symbol.value) :: result.irelative }
          else if ![0, 1, 2, 5].contains symbol.typ then .ok result
          else
            let weakUndefined := symbol.sectionIndex = 0 && symbol.binding = 2
            let references := if !symbol.name.isEmpty && !weakUndefined then
              (relocation.offset, symbol.name) :: result.references
            else result.references
            if symbol.sectionIndex = 0 || kind = 0 then .ok { result with references }
            else
              let addend := if relocation.explicitAddend then relocation.addend
                else if kind = 1 then stored.getD 0 else 0
              let target := (codeAddress header.machine symbol.typ symbol.value + addend) % (2 ^ image.addrWidth)
              .ok { result with references, absolute := (relocation.offset, target) :: result.absolute }
    .ok { result with
      references := result.references.reverse
      absolute := result.absolute.reverse
      relative := result.relative.reverse
      relativeAddends := result.relativeAddends.reverse
      irelative := result.irelative.reverse }

private def unversioned (name : String) : String :=
  (name.splitOn "@").headD name

private def importedDataName (name : String) : Bool :=
  ["stdin", "stdout", "stderr", "environ", "__environ", "optarg", "optind", "opterr",
    "optopt", "__stack_chk_guard", "__progname", "program_invocation_name",
    "program_invocation_short_name"].contains name

private def alignUp (value alignment : Nat) : Nat :=
  if alignment ≤ 1 then value else (value + alignment - 1) / alignment * alignment

def imports (image : Image) (spec : RelocationSpec) (endp : Nat) : Except String (List Import) := do
  let headers ← programHeaders image.data
  let inFile (address : Nat) : Bool := headers.any fun header =>
    header.kind = 1 && header.fileSize != 0 && address ≥ header.addr && address < header.addr + header.fileSize
  let inCode (address : Nat) : Bool :=
    headers.any (fun header => header.kind = 1 && header.fileSize != 0 && header.flags &&& 1 != 0 &&
      address ≥ header.addr && address < header.addr + header.fileSize) ||
    image.sections.any (fun sec => sec.flags &&& 4 != 0 &&
      address ≥ sec.addr && address < sec.addr + sec.size)
  let references := spec.references.map (fun entry => (entry.1, unversioned entry.2)) |>.mergeSort fun left right =>
    left.1 < right.1 || (left.1 = right.1 && left.2 ≤ right.2)
  let unique (entries : List (Nat × String)) := entries.foldl (init := []) fun result entry =>
    if result.contains entry then result else result ++ [entry]
  let references := unique references
  let objects := references.filter fun entry =>
    importedDataName entry.2 && inFile entry.1 && storedWord image headers entry.1 = some 0
  let functions := references.filter (fun entry =>
    !importedDataName entry.2 && inFile entry.1 && !inCode entry.1) |>.mergeSort fun left right => left.1 ≤ right.1
  let functions := unique functions
  let all : List (Nat × String × Bool) :=
    objects.map (fun entry => (entry.1, entry.2, true)) ++ functions.map (fun entry => (entry.1, entry.2, false))
  .ok ((List.range all.length).map fun index =>
    let entry := all[index]!
    ⟨entry.1, entry.2.1, endp + index * (image.addrWidth / 8), entry.2.2⟩)

def importBytes (image : Image) (count : Nat) : Nat :=
  alignUp (count * (image.addrWidth / 8)) 0x1000

def load (path : String) : IO Image := do
  let data ← IO.FS.readBinFile path
  match decode data with
  | .ok image => pure image
  | .error error => throw <| IO.userError error

end Bap.Image.Elf
