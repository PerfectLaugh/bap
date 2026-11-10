/-! What a kernel reads of an ELF file to start it: its segments, the interpreter that it asks for and the libraries that it
needs, of files of either width and order. -/

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
  /-- `e_machine`. -/
  machine : Nat
  /-- 32 or 64. -/
  bits : Nat
  big : Bool
  /-- `e_flags`. -/
  flags : Nat
  headerSize : Nat
  entry : Nat
  headerOffset : Nat
  headerCount : Nat
  segments : List Segment
  interpreter : Option String
  /-- That its `PT_GNU_STACK` asks for a stack that runs, as `-z execstack` and the trampolines of GCC's nested functions have it, which
  Linux gives it (`EXSTACK_ENABLE_X`). -/
  executableStack : Bool := false
  deriving DecidableEq, Repr

private def little (data : ByteArray) (offset size : Nat) : Nat :=
  (List.range size).foldl (fun value index => value + (data.get! (offset + index)).toNat * 256 ^ index) 0

/-- A field, in the order of the file. -/
private def field (data : ByteArray) (big : Bool) (offset size : Nat) : Nat :=
  if big then (List.range size).foldl (fun value index => value * 256 + (data.get! (offset + index)).toNat) 0
  else little data offset size

private def isBig (data : ByteArray) : Bool := data.get! 5 == 2
private def is64 (data : ByteArray) : Bool := data.get! 4 == 2

private def text (data : ByteArray) (offset : Nat) : String :=
  let rec length : Nat → Nat → Nat
    | 0, count => count
    | fuel + 1, count =>
      if offset + count < data.size && data.get! (offset + count) != 0 then length fuel (count + 1) else count
  String.fromUTF8? (data.extract offset (offset + length (data.size - offset) 0)) |>.getD ""

/-- What is in the program headers of type `kind`, as offset, address, file size, memory size and flags. -/
private def headers (data : ByteArray) (kind : Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  let big := isBig data
  let get := field data big
  let wide := is64 data
  let start := if wide then get 32 8 else get 28 4
  let size := if wide then get 54 2 else get 42 2
  let count := if wide then get 56 2 else get 44 2
  (List.range count).filterMap fun index =>
    let at_ := start + index * size
    if get at_ 4 != kind then none
    else if wide then some (get (at_ + 8) 8, get (at_ + 16) 8, get (at_ + 32) 8, get (at_ + 40) 8, get (at_ + 4) 4)
    else some (get (at_ + 4) 4, get (at_ + 8) 4, get (at_ + 16) 4, get (at_ + 20) 4, get (at_ + 24) 4)

def parse (data : ByteArray) : Except String Program := do
  if data.size < 52 || data.get! 0 != 0x7f || data.get! 1 != 0x45 || data.get! 2 != 0x4c || data.get! 3 != 0x46 then
    .error "not an ELF file"
  let wide := data.get! 4 == 2
  let big := data.get! 5 == 2
  if data.get! 4 != 1 && data.get! 4 != 2 || data.get! 5 != 1 && data.get! 5 != 2 then
    .error "an ELF file of no known width or order"
  if wide && data.size < 64 then
    .error "not an ELF file"
  let get := field data big
  let kind := get 16 2
  if kind != 2 && kind != 3 then
    .error "not an executable ELF file"
  let segments := (headers data 1).map fun header =>
    { offset := header.1, address := header.2.1, fileSize := header.2.2.1, memorySize := header.2.2.2.1,
      flags := header.2.2.2.2 }
  pure {
    relocatable := kind == 3
    machine := get 18 2
    bits := if wide then 64 else 32
    big
    flags := if wide then get 48 4 else get 36 4
    headerSize := if wide then get 54 2 else get 42 2
    entry := if wide then get 24 8 else get 24 4
    headerOffset := if wide then get 32 8 else get 28 4
    headerCount := if wide then get 56 2 else get 44 2
    segments
    interpreter := (headers data 3).head?.map fun header => text data header.1
    executableStack := (headers data 0x6474e551).any fun header => header.2.2.2.2 &&& 1 != 0 }

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
      let size := program.bits / 4
      let entries := (List.range (dynamic.2.2.1 / size)).map fun index =>
        (field data program.big (dynamic.1 + index * size) (size / 2), field data program.big (dynamic.1 + index * size + size / 2) (size / 2))
      let strings := (entries.find? (·.1 == 5)).bind fun entry => fileOffset program.segments entry.2
      match strings with
      | none => []
      | some table =>
        entries.filterMap fun entry => if entry.1 == 1 then some (text data (table + entry.2)) else none

end Bap.Linux.Elf
