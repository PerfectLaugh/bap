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

private def ofHex (text : String) : ByteArray :=
  let digit (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
  let rec go : List Char → ByteArray → ByteArray
    | high :: low :: rest, bytes => go rest (bytes.push (UInt8.ofNat (digit high * 16 + digit low)))
    | _, bytes => bytes
  go text.toList ByteArray.empty

/-- `llvm-mc -triple=x86_64-pc-windows-msvc` of: `start: call ext; movl value(%rip), %eax; movl tv@SECREL32(%rax), %eax;
ret`, `.data` with `value: .long 7` and `ptr: .quad start`, `.tls$` with `tv: .long 1`, `.debug$S` with `.secrel32 start`
and `.secidx start`, and a `.bss` of 16 bytes. -/
private def objectFixture : ByteArray := ofHex (
  "64860500000000004401000010000000000000002e74657874000000000000000000000012000000dc000000ee000000" ++
  "0000000003000000200030602e6461746100000000000000000000000c0000000c010000180100000000000001000000" ++
  "400030c02e6273730000000000000000000000001000000000000000000000000000000000000000800030c02e746c73" ++
  "2400000000000000000000000400000022010000000000000000000000000000400010c02e6465627567245300000000" ++
  "000000000a0000002601000030010000000000000200000040001042e8000000008b05000000008b8000000000c30100" ++
  "00000b0000000400070000000c00000004000d0000000d0000000b00070000000000000000000000040000000a000000" ++
  "01000100000004000000000000000000040000000a0000000b00080000000a0000000a002e7465787400000000000000" ++
  "0100000003011200000003000000a3543d170100000000002e64617461000000000000000200000003010c0000000100" ++
  "00008fe998740200000000002e6273730000000000000000030000000301100000000000000000000000030000000000" ++
  "2e746c73240000000000000004000000030104000000000000006567bcb80400000000002e6465627567245300000000" ++
  "0500000003010a000000020000007aa0eb09050000000000737461727400000000000000010000000200657874000000" ++
  "00000000000000000000020076616c756500000000000000020000000300747600000000000000000000040000000300" ++
  "7074720000000000040000000200000003007a65726f730000000000000003000000030004000000")

private def runObject : IO Unit := do
  match Coff.decodeReport objectFixture with
  | .error error => throw <| IO.userError error
  | .ok (image, errors) =>
    assertEqual "COFF object applied every relocation" ([] : List String) errors
    assertEqual "COFF object maps what occupies memory, without .debug$S"
      [".text", ".data", ".bss", ".tls$", "EXTERNAL"] (image.segments.map (·.name))
    assertEqual "COFF object lays sections out" [0, 20, 32, 48, 56] (image.segments.map (·.addr))
    assertEqual "COFF object sizes" [18, 12, 16, 4, 8] (image.segments.map (·.size))
    assertEqual "COFF object keeps the section list" 5 image.sections.length
    assertEqual "COFF undefined symbol has a slot" (some 56) ((image.symbols.find? (·.name == "ext")).map (·.addr))
    assertEqual "COFF symbol moves with its section" (some 24) ((image.symbols.find? (·.name == "ptr")).map (·.addr))
    assertEqual "COFF REL32 to an external" (some 0x33) (image.memory.readByte 1)
    assertEqual "COFF REL32 across sections" (some 9) (image.memory.readByte 7)
    assertEqual "COFF SECREL is from the section start" (some 0) (image.memory.readByte 13)
    assertEqual "COFF ADDR64 across sections" (some 0) (image.memory.readByte 24)
  -- the relocations of an unknown machine are errors of their own, and the rest of the file decodes
  match Coff.decodeReport (objectFixture.set! 0 0x64 |>.set! 1 0xaa) with
  | .error error => throw <| IO.userError error
  | .ok (image, errors) =>
    assertEqual "COFF AArch64 relocations are reported one by one" 4 errors.length
    assertEqual "COFF AArch64 object still decodes" Arch.aarch64 image.arch
    assertEqual "COFF unrelocated bytes stay" (some 0) (image.memory.readByte 1)
  assertTrue "COFF decode drops the report" (Coff.decode (objectFixture.set! 0 0x64 |>.set! 1 0xaa) matches .ok _)

def run : IO Unit := do
  runObject
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
    -- a nonzero value of an undefined symbol is the size of a common block, placed after the sections
    assertEqual "COFF undefined symbol is not rebased onto section 1" (some 0x18) (image.symbols[1]?.map (·.addr))
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
