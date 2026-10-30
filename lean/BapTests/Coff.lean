import BapTests.Support

namespace Bap.Tests.Coff

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
  let b := appendNat ByteArray.empty 0x8664 2
  let b := appendNat b 1 2
  let b := appendNat b 0 4
  let b := appendNat b 60 4
  let b := appendNat b 3 4
  let b := appendNat b 0 4
  let b := appendFixed b "/4" 8
  let b := appendNat b 0 4
  let b := appendNat b 0 4
  let b := appendNat b 7 4
  let b := appendNat b 147 4
  let b := appendNat b 154 4
  let b := appendNat b 0 4
  let b := appendNat b 1 2
  let b := appendNat b 0 2
  let b := appendNat b 0x60000020 4
  let b := appendFixed b "_start" 8
  let b := appendNat b 0 4
  let b := appendNat b 1 2
  let b := appendNat b 0x20 2
  let b := appendNat b 2 1
  let b := appendNat b 1 1
  let b := appendNat b 0 18
  let b := appendNat b 0 4
  let b := appendNat b 14 4
  let b := appendNat b 1 4
  let b := appendNat b 1 2
  let b := appendNat b 0x20 2
  let b := appendNat b 2 1
  let b := appendNat b 0 1
  let b := appendNat b 33 4
  let b := appendFixed b ".longtext" 10
  let b := appendFixed b "long_function_name" 19
  let b := b.push 0x55 |>.push 0x90 |>.push 0xc3
  let b := appendNat b 0 4
  let b := appendNat b 3 4
  let b := appendNat b 2 4
  appendNat b 4 2

def run : IO Unit := do
  assertEqual "COFF fixture size" 164 fixture.size
  match Coff.decode (ByteArray.mk #[1, 2, 3, 4]) with
  | .error _ => IO.println "ok: malformed COFF rejected"
  | .ok _ => throw <| IO.userError "malformed COFF accepted"
  match Coff.decode fixture with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "COFF architecture" Arch.x86_64 image.arch
    assertEqual "COFF address width" 64 image.addrWidth
    assertEqual "COFF entry point" 0 image.entryPoint
    assertEqual "COFF section count" 1 image.sections.length
    assertEqual "COFF symbol count excludes auxiliary" 2 image.symbols.length
    assertEqual "COFF mapped byte" (some 0x90) (image.memory.readByte 1)
    -- S + A - (P + 4) = 1 + 0 - (3 + 4), as lld-link computes for REL32
    assertEqual "COFF REL32 low byte" (some 0xfa) (image.memory.readByte 3)
    assertEqual "COFF REL32 sign extension" (some 0xff) (image.memory.readByte 4)
    assertEqual "COFF unmapped byte" none (image.memory.readByte 7)
    match image.sections[0]?, image.symbols with
    | some sec, [entry, long] =>
      assertEqual "COFF long section name" ".longtext" sec.name
      assertEqual "COFF section raw offset" 147 sec.offset
      assertEqual "COFF section size" 7 sec.size
      assertEqual "COFF short symbol name" "_start" entry.name
      assertEqual "COFF long symbol name" "long_function_name" long.name
      assertEqual "COFF long symbol address" 1 long.addr
      assertEqual "COFF function symbol" true long.isFunction
    | _, _ => throw <| IO.userError "missing decoded COFF metadata"
  match Coff.decode (fixture.set! 32 0x10 |>.set! 108 0) with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "COFF undefined symbol is not rebased onto section 1" (some 1) (image.symbols[1]?.map (·.addr))
    assertEqual "COFF undefined symbol is not a function" (some false) (image.symbols[1]?.map (·.isFunction))
    assertEqual "COFF defined symbol is rebased" (some 0x10) (image.symbols[0]?.map (·.addr))
  -- a .bss of an object: its size is SizeOfRawData, past the end of the file, and it has no file bytes
  match Coff.decode (fixture.set! 36 0 |>.set! 38 1 |>.set! 40 0 |>.set! 52 0) with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "COFF uninitialized segment size" (some 0x10000) (image.segments[0]?.map (·.size))
    assertEqual "COFF uninitialized section reads zero" (some 0) (image.memory.readByte 0)
    assertEqual "COFF uninitialized section last byte" (some 0) (image.memory.readByte 0xffff)
    assertEqual "COFF uninitialized section end" none (image.memory.readByte 0x10000)
  match Coff.decode (fixture.set! 28 16) with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "COFF virtual segment size" (some 16) (image.segments[0]?.map (·.size))
    assertEqual "COFF zero-filled byte" (some 0) (image.memory.readByte 15)
    assertEqual "COFF virtual memory end" none (image.memory.readByte 16)
  let path := "/tmp/bap-lean-fixture.obj"
  IO.FS.writeBinFile path fixture
  let loaded ← Coff.load path
  IO.FS.removeFile path
  assertEqual "COFF filesystem load" 2 loaded.symbols.length

end Bap.Tests.Coff
