import Bap.IO.Reader

namespace Bap.Checkpoint.BinProt

structure Reader where
  data : ByteArray
  offset : Nat := 0

def byte (reader : Reader) : Except String (Nat × Reader) := do
  let value ← IO.Reader.get8 reader.data reader.offset
  .ok (value, { reader with offset := reader.offset + 1 })

def bytes (reader : Reader) (size : Nat) : Except String (ByteArray × Reader) := do
  let value ← IO.Reader.slice reader.data reader.offset size
  .ok (value, { reader with offset := reader.offset + size })

def int (reader : Reader) : Except String (Nat × Reader) := do
  let (tag, reader) ← byte reader
  match tag with
  | 0xfe =>
    let (data, reader) ← bytes reader 2
    .ok ((data[0]!.toNat + data[1]!.toNat * 256), reader)
  | 0xfd =>
    let (data, reader) ← bytes reader 4
    .ok ((List.range 4).foldl (init := 0) fun value index => value + data[index]!.toNat * 256 ^ index, reader)
  | 0xfc =>
    let (data, reader) ← bytes reader 8
    .ok ((List.range 8).foldl (init := 0) fun value index => value + data[index]!.toNat * 256 ^ index, reader)
  | 0xff => .error "bin_prot negative integer is outside the supported address range"
  | value =>
    if value < 128 then .ok (value, reader)
    else .error s!"invalid bin_prot integer tag {value} at {reader.offset - 1}"

def string (reader : Reader) : Except String (ByteArray × Reader) := do
  let (size, reader) ← int reader
  bytes reader size

def word (reader : Reader) : Except String (ByteArray × Reader) := string reader

def packedNat (data : ByteArray) : Nat :=
  (List.range data.size).foldl (init := 0) fun value index =>
    value + data[index]!.toNat * 256 ^ index

def wordWidth (data : ByteArray) : Nat := (packedNat data % 65536) / 2

def wordNat (data : ByteArray) : Except String Nat :=
  if data.size = 0 then .error "empty bin_prot word"
  else .ok (packedNat data / 65536)

def valuePair (reader : Reader) : Except String ((Nat × Nat) × Reader) := do
  let (address, reader) ← word reader
  let (value, reader) ← word reader
  let address ← wordNat address
  let value ← wordNat value
  .ok ((address, value), reader)

def bool (reader : Reader) : Except String (Bool × Reader) := do
  let (value, reader) ← byte reader
  match value with
  | 0 => .ok (false, reader)
  | 1 => .ok (true, reader)
  | _ => .error s!"invalid bin_prot boolean {value}"

def option (reader : Reader) (decode : Reader → Except String (α × Reader)) :
    Except String (Option α × Reader) := do
  let (tag, reader) ← byte reader
  match tag with
  | 0 => .ok (none, reader)
  | 1 =>
    let (value, reader) ← decode reader
    .ok (some value, reader)
  | _ => .error s!"invalid bin_prot option tag {tag}"

def list (reader : Reader) (decode : Reader → Except String (α × Reader)) :
    Except String (List α × Reader) := do
  let (count, reader) ← int reader
  let rec loop (remaining : Nat) (reader : Reader) (result : List α) := do
    match remaining with
    | 0 => .ok (result.reverse, reader)
    | remaining + 1 =>
      let (value, reader) ← decode reader
      loop remaining reader (value :: result)
  loop count reader []

structure Descriptor where
  name : ByteArray
  addr : Nat
  size : Nat

def descriptor (reader : Reader) : Except String (Descriptor × Reader) := do
  let (name, reader) ← string reader
  let (addr, reader) ← int reader
  let (size, reader) ← int reader
  .ok (⟨name, addr, size⟩, reader)

structure Area where
  lower : ByteArray
  upper : ByteArray
  readonly : Bool
  executable : Bool
  allocated : Bool
  width : Option Nat
  fill : Option ByteArray

def area (reader : Reader) : Except String (Area × Reader) := do
  let (lower, reader) ← word reader
  let (upper, reader) ← word reader
  let (readonly, reader) ← bool reader
  let (executable, reader) ← bool reader
  let (kind, reader) ← byte reader
  match kind with
  | 0 => .ok (⟨lower, upper, readonly, executable, false, none, none⟩, reader)
  | 1 =>
    let (width, reader) ← int reader
    let (fill, reader) ← option reader word
    .ok (⟨lower, upper, readonly, executable, true, some width, fill⟩, reader)
  | _ => .error s!"invalid checkpoint area kind {kind}"

structure MemoryPrefix where
  current : Descriptor
  memories : Nat
  descriptor : Descriptor
  layers : List Area
  values : Nat
  valuesOffset : Nat

def memoryPrefix (reader : Reader) : Except String (MemoryPrefix × Reader) := do
  let (current, reader) ← descriptor reader
  let (memories, reader) ← int reader
  if memories != 1 then .error s!"expected one checkpoint memory, got {memories}"
  let (descriptor, reader) ← descriptor reader
  let (layers, reader) ← list reader area
  let (values, next) ← int reader
  .ok (⟨current, memories, descriptor, layers, values, next.offset⟩, next)

end Bap.Checkpoint.BinProt
