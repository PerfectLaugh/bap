import Bap.Emu
import Bap.Bil.Wire

namespace Bap.Emu

private def nat (value : Nat) : Sexp := .atom (toString value)
private def bool (value : Bool) : Sexp := .atom (toString value)
private def hex (value : Nat) : Sexp := .atom (String.ofList (Nat.toDigits 16 value))

private def boolValue (input : Sexp) : Except String Bool := do
  match ← Sexp.asAtom input with
  | "true" => .ok true
  | "false" => .ok false
  | _ => .error "invalid checkpoint boolean"

private def encodeTyp : Typ → Sexp
  | .unknown => .atom "unknown"
  | .unit => .atom "unit"
  | .mem addressWidth valueWidth => .tagged "mem" [nat addressWidth, nat valueWidth]
  | .imm width => .tagged "imm" [nat width]

private def decodeTyp (input : Sexp) : Except String Typ := do
  match input with
  | .atom "unknown" => .ok .unknown
  | .atom "unit" => .ok .unit
  | .list [.atom "imm", width] => .ok (.imm (← Sexp.nat width))
  | .list [.atom "mem", addressWidth, valueWidth] =>
    .ok (.mem (← Sexp.nat addressWidth) (← Sexp.nat valueWidth))
  | _ => .error "invalid checkpoint type"

private def encodeValue : Value → Sexp
  | @Value.bits width value => .tagged "bits" [nat width, hex value.toNat]
  | @Value.memory addressWidth memory => .tagged "memory" [nat addressWidth,
      .list ((Memory.cells memory).map fun cell => .tagged "cell" [hex cell.1.toNat, nat cell.2.toNat])]
  | .undefined => .atom "undefined"

private def decodeCells (width : Nat) (input : Sexp) : Except String (List (BitVec width × UInt8)) := do
  let inputs ← Sexp.asList input
  inputs.mapM fun input => do
    let args ← Sexp.expectTagged "cell" 2 input
    match args with
    | [address, value] =>
      let address ← Bil.Wire.parseHex (← Sexp.asAtom address)
      let value ← Sexp.nat value
      if value ≥ 256 then
        .error "checkpoint byte is out of range"
      else
        .ok (BitVec.ofNat width address, UInt8.ofNat value)
    | _ => .error "invalid checkpoint cell"

private def decodeValue (input : Sexp) : Except String Value := do
  match input with
  | .atom "undefined" => .ok .undefined
  | .list [.atom "bits", width, value] =>
    let width ← Sexp.nat width
    let value ← Bil.Wire.parseHex (← Sexp.asAtom value)
    if value < 2 ^ width then .ok (.bits (BitVec.ofNat width value))
    else .error s!"checkpoint value {value} does not fit in {width} bits"
  | .list [.atom "memory", width, cells] =>
    let width ← Sexp.nat width
    .ok (.memory (Memory.ofCells (← decodeCells width cells)))
  | _ => .error "invalid checkpoint value"

private def encodeBinding (binding : Bap.Var × Value) : Sexp :=
  let (var, value) := binding
  .tagged "binding" [.atom var.name, encodeTyp var.typ, nat var.index, bool var.isVirtual, encodeValue value]

private def decodeBinding (input : Sexp) : Except String (Bap.Var × Value) := do
  let args ← Sexp.expectTagged "binding" 5 input
  match args with
  | [name, typ, index, isVirtual, value] =>
    let name ← Sexp.asAtom name
    let typ ← decodeTyp typ
    let index ← Sexp.nat index
    let isVirtual ← boolValue isVirtual
    let value ← decodeValue value
    .ok (⟨name, typ, index, isVirtual⟩, value)
  | _ => .error "invalid checkpoint binding"

private def encodeBytes (data : ByteArray) : String :=
  String.intercalate "" (data.toList.map fun byte =>
    let digits := Nat.toDigits 16 byte.toNat
    String.ofList (if digits.length = 1 then ['0'] ++ digits else digits))

private def decodeHex (text : String) : Except String ByteArray := do
  let rec loop (chars : List Char) (result : List UInt8) := do
    match chars with
    | [] => .ok (ByteArray.mk result.reverse.toArray)
    | high :: low :: rest =>
      let value ← Bil.Wire.parseHex (String.ofList [high, low])
      if value ≥ 256 then .error "checkpoint region byte is out of range"
      else loop rest (UInt8.ofNat value :: result)
    | [_] => .error "checkpoint region has an odd hex length"
  loop text.toList []

private def decodeRegionBytes (input : Sexp) : Except String ByteArray := do
  match input with
  | .atom text => decodeHex text
  | .list values =>
    let bytes ← values.mapM fun byte => Sexp.nat byte
    if bytes.any fun byte => byte ≥ 256 then .error "checkpoint region byte is out of range"
    else .ok (ByteArray.mk (bytes.map UInt8.ofNat).toArray)

private def encodeRegion (region : Region) : Sexp :=
  .tagged "region" [
    nat region.address,
    bool region.protection.readable,
    bool region.protection.writable,
    bool region.protection.executable,
    .atom (encodeBytes region.data)
  ]

private def decodeRegion (input : Sexp) : Except String Region := do
  let args ← Sexp.expectTagged "region" 5 input
  match args with
  | [address, readable, writable, executable, data] =>
    let address ← Sexp.nat address
    let readable ← boolValue readable
    let writable ← boolValue writable
    let executable ← boolValue executable
    let bytes ← decodeRegionBytes data
    .ok ⟨address, bytes, ⟨readable, writable, executable⟩⟩
  | _ => .error "invalid checkpoint region"

private def encodePending : Option PendingBranch → Sexp
  | none => .atom "none"
  | some pending => .tagged "pending" [nat pending.branch, nat pending.target]

private def decodePending (input : Sexp) : Except String (Option PendingBranch) := do
  match input with
  | .atom "none" => .ok none
  | _ =>
    let args ← Sexp.expectTagged "pending" 2 input
    match args with
    | [branch, target] => .ok (some ⟨← Sexp.nat branch, ← Sexp.nat target⟩)
    | _ => .error "invalid checkpoint pending branch"

private def encodeSkip : Option Nat → Sexp
  | none => .atom "none"
  | some address => .tagged "skip" [nat address]

private def decodeSkip (input : Sexp) : Except String (Option Nat) := do
  match input with
  | .atom "none" => .ok none
  | _ =>
    let args ← Sexp.expectTagged "skip" 1 input
    match args with
    | [address] => .ok (some (← Sexp.nat address))
    | _ => .error "invalid checkpoint skip marker"

private def encodeThread (context : ThreadContext) : Sexp :=
  .tagged "thread" [
    nat context.id,
    nat context.pc,
    bool context.stopped,
    .list (context.state.env.map encodeBinding),
    encodePending context.pending,
    encodeSkip context.skip
  ]

private def decodeThread (input : Sexp) : Except String ThreadContext := do
  let args ← Sexp.expectTagged "thread" 6 input
  match args with
  | [id, pc, stopped, env, pending, skip] =>
    let id ← Sexp.nat id
    let pc ← Sexp.nat pc
    let stopped ← boolValue stopped
    let env ← (← Sexp.asList env).mapM decodeBinding
    let pending ← decodePending pending
    let skip ← decodeSkip skip
    .ok ⟨id, { env := env }, pc, stopped, pending, skip⟩
  | _ => .error "invalid checkpoint thread"

private def encodeProcess (process : ThreadId × List Region) : Sexp :=
  .tagged "process" [nat process.1, .list (process.2.map encodeRegion)]

private def decodeProcess (input : Sexp) : Except String (ThreadId × List Region) := do
  let args ← Sexp.expectTagged "process" 2 input
  match args with
  | [id, regions] =>
    let id ← Sexp.nat id
    let regions ← (← Sexp.asList regions).mapM decodeRegion
    .ok (id, regions)
  | _ => .error "invalid checkpoint process"

def encodeSnapshot (snapshot : Snapshot) : Sexp :=
  .tagged "snapshot" [
    nat snapshot.pc,
    bool snapshot.stopped,
    .list (snapshot.regions.map encodeRegion),
    .list (snapshot.state.env.map encodeBinding),
    .list (snapshot.threads.map encodeThread),
    nat snapshot.currentThread,
    nat snapshot.nextThread,
    encodePending snapshot.pending,
    .list (snapshot.processMemory.map encodeProcess),
    encodeSkip snapshot.skip
  ]

def decodeSnapshot (input : Sexp) : Except String Snapshot := do
  let input ← Sexp.asList input
  match input with
  | .atom "snapshot" :: rest =>
    if rest.length != 10 then
      .error "invalid checkpoint snapshot"
    else
      match rest with
      | [pc, stopped, regions, env, threads, currentThread, nextThread, pending, processes, skip] =>
        let pc ← Sexp.nat pc
        let stopped ← boolValue stopped
        let regions ← (← Sexp.asList regions).mapM decodeRegion
        let env ← (← Sexp.asList env).mapM decodeBinding
        let threads ← (← Sexp.asList threads).mapM decodeThread
        let currentThread ← Sexp.nat currentThread
        let nextThread ← Sexp.nat nextThread
        let pending ← decodePending pending
        let processMemory ← (← Sexp.asList processes).mapM decodeProcess
        let skip ← decodeSkip skip
        .ok ⟨{ env := env }, pc, regions, stopped, threads, currentThread, nextThread, pending, processMemory, skip⟩
      | _ => .error "invalid checkpoint snapshot"
  | _ => .error "invalid checkpoint snapshot"

private structure Writer where
  data : ByteArray := ByteArray.empty

private def putBytes (writer : Writer) (bytes : ByteArray) : Writer :=
  { data := writer.data ++ bytes }

private def putByte (writer : Writer) (value : Nat) : Writer :=
  putBytes writer (ByteArray.mk #[UInt8.ofNat value])

private def natBytes (value : Nat) : ByteArray :=
  ByteArray.mk ((List.range 8).map fun index => UInt8.ofNat (value / 256 ^ index % 256)).toArray

private def putNat (writer : Writer) (value : Nat) : Writer :=
  putBytes writer (natBytes value)

private def putBool (writer : Writer) (value : Bool) : Writer :=
  putByte writer (if value then 1 else 0)

private def putText (writer : Writer) (text : String) : Writer :=
  putBytes (putNat writer text.utf8ByteSize) text.toUTF8

private def putPendingBin (writer : Writer) (pending : Option PendingBranch) : Writer :=
  match pending with
  | none => putByte writer 0
  | some pending => putNat (putNat (putByte writer 1) pending.branch) pending.target

private def putSkipBin (writer : Writer) (skip : Option Nat) : Writer :=
  match skip with
  | none => putByte writer 0
  | some address => putNat (putByte writer 1) address

private def putTypBin (writer : Writer) (typ : Typ) : Writer :=
  match typ with
  | .unknown => putByte writer 0
  | .unit => putByte writer 1
  | .mem addressWidth valueWidth => putNat (putNat (putByte writer 2) addressWidth) valueWidth
  | .imm width => putNat (putByte writer 3) width

private def putCellsBin (writer : Writer) (cells : List (BitVec width × UInt8)) : Writer :=
  cells.foldl (init := putNat writer cells.length) fun writer cell =>
    putByte (putNat writer cell.1.toNat) cell.2.toNat

/-- The bytes that a value of `width` bits takes. -/
def valueBytes (width : Nat) : Nat := (width + 7) / 8

private def putValueBin (writer : Writer) (value : Value) : Writer :=
  match value with
  | .undefined => putByte writer 0
  | @Value.bits width value =>
    let valueBytes := (List.range (valueBytes width)).foldl (init := ByteArray.empty) fun bytes index =>
      bytes.push (UInt8.ofNat (value.toNat / 256 ^ index % 256))
    putBytes (putNat (putByte writer 1) width) valueBytes
  | @Value.memory addressWidth memory =>
    putCellsBin (putNat (putByte writer 2) addressWidth) (Memory.cells memory)

private def putBindingBin (writer : Writer) (binding : Bap.Var × Value) : Writer :=
  let (var, value) := binding
  putValueBin (putBool (putNat (putTypBin (putText writer var.name) var.typ) var.index) var.isVirtual) value

private def putRegionBin (writer : Writer) (region : Region) : Writer :=
  let writer := putNat writer region.address
  let writer := putBool writer region.protection.readable
  let writer := putBool writer region.protection.writable
  let writer := putBool writer region.protection.executable
  putBytes (putNat writer region.data.size) region.data

private def putThreadBin (writer : Writer) (context : ThreadContext) : Writer :=
  let writer := putNat writer context.id
  let writer := putNat writer context.pc
  let writer := putBool writer context.stopped
  let writer := putNat writer context.state.env.length
  let writer := context.state.env.foldl putBindingBin writer
  putSkipBin (putPendingBin writer context.pending) context.skip

private def putProcessBin (writer : Writer) (process : ThreadId × List Region) : Writer :=
  let writer := putNat writer process.1
  let writer := putNat writer process.2.length
  process.2.foldl putRegionBin writer

private structure Reader where
  data : ByteArray
  offset : Nat := 0

private def takeBytes (reader : Reader) (count : Nat) : Except String (ByteArray × Reader) := do
  if reader.offset + count > reader.data.size then
    .error "truncated binary checkpoint"
  else
    .ok (reader.data.extract reader.offset (reader.offset + count), { reader with offset := reader.offset + count })

private def getByte (reader : Reader) : Except String (Nat × Reader) := do
  let (bytes, reader) ← takeBytes reader 1
  .ok (bytes[0]!.toNat, reader)

private def getNat (reader : Reader) : Except String (Nat × Reader) := do
  let (bytes, reader) ← takeBytes reader 8
  let value := (List.range 8).foldl (init := 0) fun value index => value + bytes[index]!.toNat * 256 ^ index
  .ok (value, reader)

private def getBool (reader : Reader) : Except String (Bool × Reader) := do
  let (value, reader) ← getByte reader
  match value with
  | 0 => .ok (false, reader)
  | 1 => .ok (true, reader)
  | _ => .error "invalid binary checkpoint boolean"

private def getText (reader : Reader) : Except String (String × Reader) := do
  let (size, reader) ← getNat reader
  let (bytes, reader) ← takeBytes reader size
  .ok (String.fromUTF8! bytes, reader)

private def getList (reader : Reader) (decode : Reader → Except String (α × Reader)) :
    Except String (List α × Reader) := do
  let (count, reader) ← getNat reader
  let rec loop (remaining : Nat) (reader : Reader) (result : List α) := do
    match remaining with
    | 0 => .ok (result.reverse, reader)
    | remaining + 1 =>
      let (value, reader) ← decode reader
      loop remaining reader (value :: result)
  loop count reader []

private def getPendingBin (reader : Reader) : Except String (Option PendingBranch × Reader) := do
  let (tag, reader) ← getByte reader
  match tag with
  | 0 => .ok (none, reader)
  | 1 =>
    let (branch, reader) ← getNat reader
    let (target, reader) ← getNat reader
    .ok (some ⟨branch, target⟩, reader)
  | _ => .error "invalid binary checkpoint pending branch"

private def getSkipBin (reader : Reader) : Except String (Option Nat × Reader) := do
  let (tag, reader) ← getByte reader
  match tag with
  | 0 => .ok (none, reader)
  | 1 =>
    let (address, reader) ← getNat reader
    .ok (some address, reader)
  | _ => .error "invalid binary checkpoint skip marker"

private def getTypBin (reader : Reader) : Except String (Typ × Reader) := do
  let (tag, reader) ← getByte reader
  match tag with
  | 0 => .ok (.unknown, reader)
  | 1 => .ok (.unit, reader)
  | 2 =>
    let (addressWidth, reader) ← getNat reader
    let (valueWidth, reader) ← getNat reader
    .ok (.mem addressWidth valueWidth, reader)
  | 3 =>
    let (width, reader) ← getNat reader
    .ok (.imm width, reader)
  | _ => .error "invalid binary checkpoint type"

private def getValueBin (reader : Reader) : Except String (Value × Reader) := do
  let (tag, reader) ← getByte reader
  match tag with
  | 0 => .ok (.undefined, reader)
  | 1 =>
    let (width, reader) ← getNat reader
    let (bytes, reader) ← takeBytes reader (valueBytes width)
    let value := (List.range (valueBytes width)).foldl (init := 0) fun value index =>
      value + bytes[index]!.toNat * 256 ^ index
    .ok (.bits (BitVec.ofNat width value), reader)
  | 2 =>
    let (width, reader) ← getNat reader
    let (cells, reader) ← getList reader fun reader => do
      let (address, reader) ← getNat reader
      let (value, reader) ← getByte reader
      .ok ((BitVec.ofNat width address, UInt8.ofNat value), reader)
    .ok (.memory (Memory.ofCells cells), reader)
  | _ => .error "invalid binary checkpoint value"

private def getBindingBin (reader : Reader) : Except String ((Bap.Var × Value) × Reader) := do
  let (name, reader) ← getText reader
  let (typ, reader) ← getTypBin reader
  let (index, reader) ← getNat reader
  let (isVirtual, reader) ← getBool reader
  let (value, reader) ← getValueBin reader
  .ok ((⟨name, typ, index, isVirtual⟩, value), reader)

private def getRegionBin (reader : Reader) : Except String (Region × Reader) := do
  let (address, reader) ← getNat reader
  let (readable, reader) ← getBool reader
  let (writable, reader) ← getBool reader
  let (executable, reader) ← getBool reader
  let (size, reader) ← getNat reader
  let (data, reader) ← takeBytes reader size
  .ok (⟨address, data, ⟨readable, writable, executable⟩⟩, reader)

private def getThreadBin (reader : Reader) : Except String (ThreadContext × Reader) := do
  let (id, reader) ← getNat reader
  let (pc, reader) ← getNat reader
  let (stopped, reader) ← getBool reader
  let (env, reader) ← getList reader getBindingBin
  let (pending, reader) ← getPendingBin reader
  let (skip, reader) ← getSkipBin reader
  .ok (⟨id, { env := env }, pc, stopped, pending, skip⟩, reader)

private def getProcessBin (reader : Reader) : Except String ((ThreadId × List Region) × Reader) := do
  let (id, reader) ← getNat reader
  let (regions, reader) ← getList reader getRegionBin
  .ok ((id, regions), reader)

private def binaryMagic : ByteArray := "BAPCKPT3".toUTF8

private def encodeBinaryUnchecked (snapshot : Snapshot) : ByteArray :=
  let writer := putBytes ⟨binaryMagic⟩ (natBytes snapshot.pc)
  let writer := putBool writer snapshot.stopped
  let writer := putNat writer snapshot.regions.length
  let writer := snapshot.regions.foldl putRegionBin writer
  let writer := putNat writer snapshot.state.env.length
  let writer := snapshot.state.env.foldl putBindingBin writer
  let writer := putNat writer snapshot.threads.length
  let writer := snapshot.threads.foldl putThreadBin writer
  let writer := putNat writer snapshot.currentThread
  let writer := putNat writer snapshot.nextThread
  let writer := putPendingBin writer snapshot.pending
  let writer := putNat writer snapshot.processMemory.length
  (putSkipBin (snapshot.processMemory.foldl putProcessBin writer) snapshot.skip).data

private def fitsWord (value : Nat) : Bool := value < 2 ^ 64

private def pendingFits : Option PendingBranch → Bool
  | none => true
  | some pending => fitsWord pending.branch && fitsWord pending.target

private def skipFits : Option Nat → Bool
  | none => true
  | some address => fitsWord address

private def typFits : Typ → Bool
  | .mem addressWidth valueWidth => fitsWord addressWidth && fitsWord valueWidth
  | .imm width => fitsWord width
  | _ => true

private def valueFits : Value → Bool
  | .undefined => true
  | @Value.bits width _ => fitsWord width
  | @Value.memory addressWidth memory => addressWidth ≤ 64 && fitsWord (Memory.cells memory).length

private def bindingFits (binding : Bap.Var × Value) : Bool :=
  fitsWord binding.1.name.utf8ByteSize && typFits binding.1.typ && fitsWord binding.1.index && valueFits binding.2

private def regionFits (region : Region) : Bool :=
  fitsWord region.address && fitsWord region.data.size

private def threadFits (context : ThreadContext) : Bool :=
  fitsWord context.id && fitsWord context.pc && fitsWord context.state.env.length &&
    context.state.env.all bindingFits && pendingFits context.pending && skipFits context.skip

private def processFits (process : ThreadId × List Region) : Bool :=
  fitsWord process.1 && fitsWord process.2.length && process.2.all regionFits

/-- Whether the fixed-width fields of the binary format can hold every part of the snapshot. -/
def binaryFits (snapshot : Snapshot) : Bool :=
  fitsWord snapshot.pc &&
    fitsWord snapshot.regions.length && snapshot.regions.all regionFits &&
    fitsWord snapshot.state.env.length && snapshot.state.env.all bindingFits &&
    fitsWord snapshot.threads.length && snapshot.threads.all threadFits &&
    fitsWord snapshot.currentThread && fitsWord snapshot.nextThread && pendingFits snapshot.pending &&
    fitsWord snapshot.processMemory.length && snapshot.processMemory.all processFits && skipFits snapshot.skip

/-- Encode a snapshot, refusing one that the binary format could only store truncated. -/
def encodeBinarySnapshot (snapshot : Snapshot) : Except String ByteArray :=
  if binaryFits snapshot then .ok (encodeBinaryUnchecked snapshot)
  else .error "snapshot has a value too wide for the binary checkpoint format"

def decodeBinarySnapshot (data : ByteArray) : Except String Snapshot := do
  if data.extract 0 binaryMagic.size != binaryMagic then
    .error "not a binary checkpoint"
  else
    let reader : Reader := { data, offset := binaryMagic.size }
    let (pc, reader) ← getNat reader
    let (stopped, reader) ← getBool reader
    let (regions, reader) ← getList reader getRegionBin
    let (env, reader) ← getList reader getBindingBin
    let (threads, reader) ← getList reader getThreadBin
    let (currentThread, reader) ← getNat reader
    let (nextThread, reader) ← getNat reader
    let (pending, reader) ← getPendingBin reader
    let (processMemory, reader) ← getList reader getProcessBin
    let (skip, reader) ← getSkipBin reader
    if reader.offset != data.size then
      .error "trailing bytes in binary checkpoint"
    else
      .ok ⟨{ env := env }, pc, regions, stopped, threads, currentThread, nextThread, pending, processMemory, skip⟩

/-- The memory holding the bytes of `regions`. -/
def regionsMemory (width : Nat) (regions : List Region) : Bap.Memory width :=
  regions.foldl (init := Bap.Memory.empty width) fun memory region =>
    Bap.Memory.writeRegion memory region.address region.data

/-- The bytes of the address space of thread `id`: its own, or else the shared ones. -/
def spaceRegions (snapshot : Snapshot) (id : ThreadId) : List Region :=
  (snapshot.processMemory.lookup id).getD snapshot.regions

/-- Gives a loaded snapshot the memory that `save` left out: every thread gets that of its address space,
and a forked process does not get the memory of its parent. -/
def materializeState (memoryVar : Bap.Var) (width : Nat) (snapshot : Snapshot) : Snapshot :=
  let memoryOf (id : ThreadId) : Value := .memory (regionsMemory width (spaceRegions snapshot id))
  { snapshot with
    state := { env := (memoryVar, memoryOf snapshot.currentThread) :: snapshot.state.env }
    threads := snapshot.threads.map fun thread =>
      { thread with state := { env := Bil.bind thread.state.env memoryVar (memoryOf thread.id) } }
  }

def materializeSnapshot (emu : Emu) (snapshot : Snapshot) : IO Snapshot := do
  if snapshot.state.env.any fun binding => binding.1 == emu.config.memory then
    pure snapshot
  else
    let width ← match emu.config.memory.typ with
      | .mem width 8 => pure width
      | _ => throw <| IO.userError "Emu memory must have byte-wide cells"
    pure (materializeState emu.config.memory width snapshot)

/-- What `save` writes: the memory variable stays out, as the regions and processes hold the bytes. -/
def withoutMemory (memoryVar : Bap.Var) (snapshot : Snapshot) : Snapshot :=
  { snapshot with
    state := { env := snapshot.state.env.filter fun binding => binding.1 != memoryVar }
    threads := snapshot.threads.map fun thread =>
      { thread with state := { env := thread.state.env.filter fun binding => binding.1 != memoryVar } }
  }

def save (emu : Emu) (path : String) : IO Unit := do
  let originalRegions ← emu.regions.get
  refreshSharedRegions emu
  let snapshot ← snapshot emu
  let encoded := encodeBinarySnapshot (withoutMemory emu.config.memory snapshot)
  emu.regions.set originalRegions
  match encoded with
  | .ok data => IO.FS.writeBinFile path data
  | .error error => throw <| IO.userError error

private def timed (label : String) (action : IO α) : IO α := do
  let start ← IO.monoMsNow
  let result ← action
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"checkpoint {label}: {elapsed} ms"
  pure result

def loadSnapshot (emu : Emu) (path : String) : IO Snapshot := do
  let data ← timed "read" (IO.FS.readBinFile path)
  if data.extract 0 binaryMagic.size = binaryMagic then
    match ← timed "binary decode" (pure (decodeBinarySnapshot data)) with
    | .error error => throw <| IO.userError error
    | .ok snapshot => timed "memory materialize" (materializeSnapshot emu snapshot)
  else
    match ← timed "S-expression parse" (pure (Sexp.parse (String.fromUTF8! data))) with
    | .error error => throw <| IO.userError error
    | .ok input =>
      match ← timed "snapshot decode" (pure (decodeSnapshot input)) with
      | .error error => throw <| IO.userError error
      | .ok snapshot => timed "memory materialize" (materializeSnapshot emu snapshot)

def load (emu : Emu) (path : String) : IO Unit := do
  let snapshot ← loadSnapshot emu path
  timed "restore" (restore emu snapshot)

end Bap.Emu
