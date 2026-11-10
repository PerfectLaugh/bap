import BapTests.Support

namespace Bap.Tests.Macho

open Bap
open Bap.Image

private def appendNat (bytes : ByteArray) (value size : Nat) : ByteArray :=
  (List.range size).foldl (init := bytes) fun result index =>
    result.push (UInt8.ofNat (value / 256 ^ index % 256))

private def appendFixed (bytes : ByteArray) (value : String) (size : Nat) : ByteArray :=
  let encoded := value.toUTF8
  (List.range size).foldl (init := bytes) fun result index =>
    result.push (if index < encoded.size then encoded.get! index else 0)

private def fixture : ByteArray :=
  let b := ByteArray.empty
  let b := appendNat b 0xfeedfacf 4
  let b := appendNat b 0x01000007 4
  let b := appendNat b 3 4
  let b := appendNat b 2 4
  let b := appendNat b 3 4
  let b := appendNat b 200 4
  let b := appendNat b 0 8
  let b := appendNat b 0x19 4
  let b := appendNat b 152 4
  let b := appendFixed b "__TEXT" 16
  let b := appendNat b 0x1000 8
  let b := appendNat b 8 8
  let b := appendNat b 232 8
  let b := appendNat b 4 8
  let b := appendNat b 7 4
  let b := appendNat b 5 4
  let b := appendNat b 1 4
  let b := appendNat b 0 4
  let b := appendFixed b "__text" 16
  let b := appendFixed b "__TEXT" 16
  let b := appendNat b 0x1000 8
  let b := appendNat b 4 8
  let b := appendNat b 232 4
  let b := appendNat b 0 12
  let b := appendNat b 0x80000400 4
  let b := appendNat b 0 12
  let b := appendNat b 0x80000028 4
  let b := appendNat b 24 4
  let b := appendNat b 232 8
  let b := appendNat b 0 8
  let b := appendNat b 2 4
  let b := appendNat b 24 4
  let b := appendNat b 236 4
  let b := appendNat b 1 4
  let b := appendNat b 252 4
  let b := appendNat b 8 4
  let b := b.push 0x90 |>.push 0xcc |>.push 0xc3 |>.push 0x90
  let b := appendNat b 1 4
  let b := appendNat b 0x0f 1
  let b := appendNat b 1 1
  let b := appendNat b 0 2
  let b := appendNat b 0x1000 8
  ByteArray.mk #[0, 0x5f, 0x73, 0x74, 0x61, 0x72, 0x74, 0] |>.foldl (init := b) fun result byte => result.push byte


/-- A field of `size` bytes of a fixture, little-endian or big, set to `value`. -/
private def setField (data : ByteArray) (offset size value : Nat) (big : Bool := false) : ByteArray :=
  (List.range size).foldl (init := data) fun data index =>
    data.set! (offset + (if big then size - 1 - index else index)) (UInt8.ofNat (value / 256 ^ index % 256))

private def fieldOf (data : ByteArray) (offset size : Nat) (big : Bool := false) : Nat :=
  (List.range size).foldl (init := 0) fun value index =>
    value + (data.get! (offset + (if big then size - 1 - index else index))).toNat * 256 ^ index

/-- A Mach-O executable of x86_64 that starts as `LC_UNIXTHREAD` says, as one built for macOS 10.7 or before, a static one or `dyld` does:
its `rip`, which is an address, rather than an offset of `LC_MAIN`. -/
def runUnixThread : IO Unit := do
  let le (size value : Nat) : ByteArray := ByteArray.mk ((List.range size).map fun index => (value >>> (8 * index)).toUInt8).toArray
  let pad (bytes : ByteArray) (size : Nat) : ByteArray := bytes ++ ByteArray.mk (Array.replicate (size - bytes.size) 0)
  let segment := le 4 0x19 ++ le 4 72 ++ pad "__TEXT".toUTF8 16 ++ le 8 0x100000000 ++ le 8 0x1000 ++ le 8 0 ++ le 8 0x200 ++
    le 4 5 ++ le 4 5 ++ le 4 0 ++ le 4 0
  -- x86_THREAD_STATE64, of 42 words: rax to r15, then rip.
  let state := (List.range 21).foldl (fun out index => out ++ le 8 (if index == 16 then 0x100000100 else 0)) ByteArray.empty
  let thread := le 4 5 ++ le 4 (16 + state.size) ++ le 4 4 ++ le 4 42 ++ state
  let commands := segment ++ thread
  let header := le 4 0xfeedfacf ++ le 4 0x01000007 ++ le 4 3 ++ le 4 2 ++ le 4 2 ++ le 4 commands.size ++ le 4 0 ++ le 4 0
  match Macho.decode (pad (header ++ commands) 0x200) with
  | .error error => throw <| IO.userError s!"Mach-O of LC_UNIXTHREAD: {error}"
  | .ok image => assertEqual "Mach-O of LC_UNIXTHREAD starts at its rip" 0x100000100 image.entryPoint

def run : IO Unit := do
  assertEqual "Mach-O fixture size" 260 fixture.size
  -- A segment whose command asks for more zeros than a host can give isn't made.
  let big := fixture.get! 0 == 0xfe
  let (_, huge, found) := (List.range (fieldOf fixture 16 4 big)).foldl (init := (32, fixture, false)) fun (offset, data, found) _ =>
    let size := fieldOf data (offset + 4) 4 big
    if fieldOf data offset 4 big == 0x19 then
      (offset + size, setField (setField data (offset + 32) 8 (2 ^ 40) big) (offset + 60) 4 7 big, true)
    else (offset + size, data, found)
  assertTrue "Mach-O fixture has a segment" found
  assertEqual "Mach-O segments too large are refused" (some "the regions of the file are too large")
    (match Image.decode huge with | .error message => some message | .ok _ => none)
  match Macho.decode (ByteArray.mk #[1, 2, 3, 4]) with
  | .error _ => IO.println "ok: malformed Mach-O rejected"
  | .ok _ => throw <| IO.userError "malformed Mach-O accepted"
  match Macho.decode (fixture.set! 80 9) with
  | .error _ => IO.println "ok: oversized Mach-O file mapping rejected"
  | .ok _ => throw <| IO.userError "oversized Mach-O file mapping accepted"
  match Macho.decode fixture with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "Mach-O architecture" Arch.x86_64 image.arch
    assertEqual "Mach-O address width" 64 image.addrWidth
    assertEqual "Mach-O endianness" Endian.little image.endian
    assertEqual "Mach-O entry point" 0x1000 image.entryPoint
    assertEqual "Mach-O section count" 1 image.sections.length
    assertEqual "Mach-O segment count" 1 image.segments.length
    assertEqual "Mach-O symbol count" 1 image.symbols.length
    assertEqual "Mach-O mapped instruction" (some 0xc3) (image.memory.readByte 0x1002)
    assertEqual "Mach-O zero-filled byte" (some 0) (image.memory.readByte 0x1004)
    assertEqual "Mach-O virtual memory end" none (image.memory.readByte 0x1008)
    match image.sections[0]?, image.segments[0]?, image.symbols[0]? with
    | some sec, some segment, some symbol =>
      assertEqual "Mach-O section name" "__text" sec.name
      assertEqual "Mach-O section file offset" 232 sec.offset
      assertEqual "Mach-O section type" 0 sec.kind
      assertEqual "Mach-O segment name" "__TEXT" segment.name
      assertEqual "Mach-O segment permissions" (true, false, true)
        (segment.readable, segment.writable, segment.executable)
      assertEqual "Mach-O symbol name" "_start" symbol.name
      assertEqual "Mach-O symbol address" 0x1000 symbol.addr
      assertEqual "Mach-O function symbol" true symbol.isFunction
      assertEqual "Mach-O non-debug symbol" false symbol.isDebug
    | _, _, _ => throw <| IO.userError "missing decoded Mach-O metadata"
  match Macho.decode (fixture.set! 241 0) with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "Mach-O NO_SECT symbol is not in section 1" (some false) (image.symbols[0]?.map (·.isFunction))
  let path := "native/build/bap-lean-fixture.macho"
  IO.FS.writeBinFile path fixture
  let loaded ← Image.load path
  IO.FS.removeFile path
  assertEqual "Mach-O common filesystem load" 0x1000 loaded.entryPoint

end Bap.Tests.Macho
