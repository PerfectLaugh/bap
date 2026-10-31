import BapTests.Support

namespace Bap.Tests.Pe

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
  let b := appendNat ByteArray.empty 0x5a4d 2
  let b := appendNat b 0 58
  let b := appendNat b 64 4
  let b := appendNat b 0x00004550 4
  let b := appendNat b 0x8664 2
  let b := appendNat b 1 2
  let b := appendNat b 0 4
  let b := appendNat b 372 4
  let b := appendNat b 1 4
  let b := appendNat b 240 2
  let b := appendNat b 0x22 2
  let b := appendNat b 0x20b 2
  let b := appendNat b 0 2
  let b := appendNat b 4 4
  let b := appendNat b 0 8
  let b := appendNat b 0x1000 8
  let b := appendNat b 0x400000 8
  let b := appendNat b 0x1000 4
  let b := appendNat b 0x200 4
  let b := appendNat b 0 200
  let b := appendFixed b ".text" 8
  let b := appendNat b 8 4
  let b := appendNat b 0x1000 4
  let b := appendNat b 4 4
  let b := appendNat b 368 4
  let b := appendNat b 0 8
  let b := appendNat b 0 4
  let b := appendNat b 0x60000020 4
  let b := b.push 0xb0 |>.push 0x2a |>.push 0xc3 |>.push 0x90
  let b := appendFixed b "_start" 8
  let b := appendNat b 0 4
  let b := appendNat b 1 2
  let b := appendNat b 0x20 2
  let b := appendNat b 2 1
  let b := appendNat b 0 1
  appendNat b 4 4

/-- A PE32 for i386, laid out as `lld-link /machine:x86` does: the image base in the 32-bit field at offset 28 of the
optional header, 224 bytes of it with the data directories, `BaseOfData` at offset 24. -/
private def pe32Fixture : ByteArray :=
  let b := appendNat ByteArray.empty 0x5a4d 2
  let b := appendNat b 0 58
  let b := appendNat b 64 4
  let b := appendNat b 0x00004550 4
  let b := appendNat b 0x014c 2
  let b := appendNat b 1 2
  let b := appendNat b 0 12
  let b := appendNat b 224 2
  let b := appendNat b 0x102 2
  let b := appendNat b 0x10b 2
  let b := appendNat b 0 2
  let b := appendNat b 0x20 4
  let b := appendNat b 0 8
  let b := appendNat b 0x1010 4
  let b := appendNat b 0x1000 4
  let b := appendNat b 0x2000 4
  let b := appendNat b 0x400000 4
  let b := appendNat b 0x1000 4
  let b := appendNat b 0x200 4
  let b := appendNat b 0 184
  let b := appendFixed b ".text" 8
  let b := appendNat b 0x20 4
  let b := appendNat b 0x1000 4
  let b := appendNat b 0x20 4
  let b := appendNat b 0x160 4
  let b := appendNat b 0 12
  let b := appendNat b 0x60000020 4
  let b := appendNat b 0 16
  let b := appendNat b 0xc3 1
  appendNat b 0 15

def run : IO Unit := do
  assertEqual "PE fixture size" 394 fixture.size
  match Pe.decode (ByteArray.mk #[1, 2, 3, 4]) with
  | .error _ => IO.println "ok: malformed PE rejected"
  | .ok _ => throw <| IO.userError "malformed PE accepted"
  -- the same headers read as PE32: the image base is the 32-bit field past `BaseOfData`, not the one of PE32+
  match Pe.decode (fixture.set! 88 0x0b |>.set! 89 0x01) with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "PE32 address width" 32 image.addrWidth
    assertEqual "PE32 entry point" 0x1000 image.entryPoint
    assertEqual "PE32 section is at the 32-bit image base" (some 0x1000) (image.sections[0]?.map (·.addr))
  -- an unknown optional header
  match Pe.decode (fixture.set! 88 0x07 |>.set! 89 0x01) with
  | .error _ => IO.println "ok: unknown PE optional header rejected"
  | .ok _ => throw <| IO.userError "unknown PE optional header accepted"
  match Pe.decode pe32Fixture with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "PE32 i386 architecture" Arch.x86 image.arch
    assertEqual "PE32 i386 address width" 32 image.addrWidth
    assertEqual "PE32 i386 entry point" 0x401010 image.entryPoint
    assertEqual "PE32 i386 sections" [".text"] (image.sections.map (·.name))
    assertEqual "PE32 i386 section address" [0x401000] (image.sections.map (·.addr))
    assertEqual "PE32 i386 instruction" (some 0xc3) (image.memory.readByte 0x401010)
  match Pe.decode (pe32Fixture.set! 70 8) with
  | .error _ => IO.println "ok: PE32 section table past the input rejected"
  | .ok _ => throw <| IO.userError "PE32 section table past the input accepted"
  match Pe.decode fixture with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "PE architecture" Arch.x86_64 image.arch
    assertEqual "PE address width" 64 image.addrWidth
    assertEqual "PE endianness" Endian.little image.endian
    assertEqual "PE entry point" 0x401000 image.entryPoint
    assertEqual "PE section count" 1 image.sections.length
    assertEqual "PE segment count" 1 image.segments.length
    assertEqual "PE symbol count" 1 image.symbols.length
    assertEqual "PE mapped instruction" (some 0x2a) (image.memory.readByte 0x401001)
    assertEqual "PE zero-filled byte" (some 0) (image.memory.readByte 0x401004)
    assertEqual "PE virtual memory end" none (image.memory.readByte 0x401008)
    match image.sections[0]?, image.segments[0]?, image.symbols[0]? with
    | some sec, some segment, some symbol =>
      assertEqual "PE section name" ".text" sec.name
      assertEqual "PE section raw offset" 368 sec.offset
      assertEqual "PE section address" 0x401000 sec.addr
      assertEqual "PE segment permissions" (true, false, true)
        (segment.readable, segment.writable, segment.executable)
      assertEqual "PE symbol name" "_start" symbol.name
      assertEqual "PE symbol address" 0x401000 symbol.addr
      assertEqual "PE function symbol" true symbol.isFunction
      assertEqual "PE non-debug symbol" false symbol.isDebug
    | _, _, _ => throw <| IO.userError "missing decoded PE metadata"
  match Pe.decode (fixture.set! 384 0) with
  | .error error => throw <| IO.userError error
  | .ok image =>
    assertEqual "PE undefined symbol is not rebased onto section 1" (some 0) (image.symbols[0]?.map (·.addr))
    assertEqual "PE undefined symbol is not a function" (some false) (image.symbols[0]?.map (·.isFunction))
  let path := "native/build/bap-lean-fixture.exe"
  IO.FS.writeBinFile path fixture
  let loaded ← Image.load path
  let cli ← IO.Process.output { cmd := ".lake/build/bin/bap", args := #["image", path] }
  IO.FS.removeFile path
  assertEqual "PE common filesystem load" 0x401000 loaded.entryPoint
  assertEqual "PE CLI auto-detection" 0 cli.exitCode

end Bap.Tests.Pe
