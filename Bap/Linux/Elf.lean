/-! What a kernel reads of an ELF file to start it: its segments, the interpreter that it asks for and the libraries that it
needs. Little-endian 64-bit files only. -/

namespace Bap.Linux.Elf

/-- A `PT_LOAD`. -/
structure Segment where
  address : Nat
  offset : Nat
  fileSize : Nat
  memorySize : Nat
  flags : Nat
  deriving DecidableEq, Repr

structure Program where
  /-- Whether it can go anywhere: `ET_DYN`. -/
  relocatable : Bool
  entry : Nat
  headerOffset : Nat
  headerCount : Nat
  segments : List Segment
  interpreter : Option String
  deriving DecidableEq, Repr

private def little (data : ByteArray) (offset size : Nat) : Nat :=
  (List.range size).foldl (fun value index => value + (data.get! (offset + index)).toNat * 256 ^ index) 0

private def text (data : ByteArray) (offset : Nat) : String :=
  let rec length : Nat → Nat → Nat
    | 0, count => count
    | fuel + 1, count =>
      if offset + count < data.size && data.get! (offset + count) != 0 then length fuel (count + 1) else count
  String.fromUTF8? (data.extract offset (offset + length (data.size - offset) 0)) |>.getD ""

/-- What is in the program headers of type `kind`, as offset, address, file size, memory size and flags. -/
private def headers (data : ByteArray) (kind : Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  let start := little data 32 8
  let size := little data 54 2
  let count := little data 56 2
  (List.range count).filterMap fun index =>
    let at_ := start + index * size
    if little data at_ 4 == kind then
      some (little data (at_ + 8) 8, little data (at_ + 16) 8, little data (at_ + 32) 8, little data (at_ + 40) 8,
        little data (at_ + 4) 4)
    else none

def parse (data : ByteArray) : Except String Program := do
  if data.size < 64 || data.get! 0 != 0x7f || data.get! 1 != 0x45 || data.get! 2 != 0x4c || data.get! 3 != 0x46 then
    .error "not an ELF file"
  if data.get! 4 != 2 || data.get! 5 != 1 then
    .error "not a little-endian 64-bit ELF file"
  let kind := little data 16 2
  if kind != 2 && kind != 3 then
    .error "not an executable ELF file"
  let segments := (headers data 1).map fun header =>
    { offset := header.1, address := header.2.1, fileSize := header.2.2.1, memorySize := header.2.2.2.1,
      flags := header.2.2.2.2 }
  pure {
    relocatable := kind == 3
    entry := little data 24 8
    headerOffset := little data 32 8
    headerCount := little data 56 2
    segments
    interpreter := (headers data 3).head?.map fun header => text data header.1 }

/-- Where the address of a loaded file is in the file. -/
private def fileOffset (segments : List Segment) (address : Nat) : Option Nat :=
  (segments.find? fun segment => segment.address ≤ address && address < segment.address + segment.fileSize).map
    fun segment => segment.offset + address - segment.address

/-- The names of the libraries that it needs: its `DT_NEEDED`. -/
def needed (data : ByteArray) : List String :=
  match parse data with
  | .error _ => []
  | .ok program =>
    match (headers data 2).head? with
    | none => []
    | some dynamic =>
      let entries := (List.range (dynamic.2.2.1 / 16)).map fun index =>
        (little data (dynamic.1 + index * 16) 8, little data (dynamic.1 + index * 16 + 8) 8)
      let strings := (entries.find? (·.1 == 5)).bind fun entry => fileOffset program.segments entry.2
      match strings with
      | none => []
      | some table =>
        entries.filterMap fun entry => if entry.1 == 1 then some (text data (table + entry.2)) else none

end Bap.Linux.Elf
