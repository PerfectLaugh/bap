import BapTests.Support

namespace Bap.Tests.Image

open Bap
open Bap.Image

private def bytes : ByteArray := ByteArray.mk #[0x7f, 0x45, 0x4c, 0x46]
private def small : ByteArray := ByteArray.mk #[1, 2, 3, 4]

def run : IO Unit := do
  match IO.Reader.read small .little 0 2 with
  | .ok value => assertEqual "little-endian integer reader" 0x0201 value
  | .error error => throw <| IO.userError error
  match IO.Reader.read small .big 0 2 with
  | .ok value => assertEqual "big-endian integer reader" 0x0102 value
  | .error error => throw <| IO.userError error
  match IO.Reader.read bytes .big 0 4 with
  | .ok value => assertEqual "ELF magic integer reader" 0x7f454c46 value
  | .error error => throw <| IO.userError error
  match IO.Reader.slice small 3 2 with
  | .error _ => IO.println "ok: out-of-bounds slice rejected"
  | .ok _ => throw <| IO.userError "out-of-bounds slice accepted"
  let image := Raw.load small 0x400000 .little
  assertEqual "raw image entry" 0x400000 image.entryPoint
  assertTrue "raw memory contains address" (image.memory.contains 0x400001)
  assertEqual "raw memory byte" (some 2) (image.memory.readByte 0x400001)
  assertEqual "raw memory outside region" none (image.memory.readByte 0x400004)
  assertEqual "raw Ogre fields generated" true (!(Ogre.ofImage image).fields.isEmpty)
  let rich : Image := { image with
    sections := [⟨"text", 0x400000, 0, 4, 5, 1⟩]
    symbols := [⟨"main", 0x400000, 4, true, false, false⟩]
  }
  let doc := Ogre.ofImage rich
  let rendered := Ogre.render doc
  assertTrue "Ogre uses BAP endianness field" ((rendered.splitOn "is-little-endian").length > 1)
  let parsed ← match Ogre.parse rendered with
    | .ok doc => pure doc
    | .error error => throw <| IO.userError error
  assertEqual "Ogre document round trip" doc parsed
  match Ogre.toImage parsed with
  | .error error => throw <| IO.userError error
  | .ok restored =>
    assertEqual "Ogre restores architecture" rich.arch restored.arch
    assertEqual "Ogre restores entry point" rich.entryPoint restored.entryPoint
    assertEqual "Ogre restores sections" rich.sections restored.sections
    assertEqual "Ogre restores segments" rich.segments restored.segments
    assertEqual "Ogre restores symbols" rich.symbols restored.symbols
    assertEqual "Ogre restores code-region size" [4] (restored.memory.entries.map fun entry => entry.1.size)
    assertEqual "Ogre reconstructs zero-filled code" (some 0) (restored.memory.readByte 0x400000)
  let textBytes := ByteArray.mk ("hello world".toList.map (fun c => UInt8.ofNat c.toNat)).toArray
  let utf16le : ByteArray := ByteArray.mk #[65, 0, 66, 0, 67, 0, 68, 0, 0, 0]
  let utf16be : ByteArray := ByteArray.mk #[0, 88, 0, 89, 0, 0]
  let asciiRecords := Analysis.Strings.strings (Raw.load (textBytes ++ (ByteArray.mk #[0])) 0x1000 .little) 2
  assertEqual "string scanner finds ASCII" [⟨0x1000, "hello world", Analysis.Strings.Encoding.ascii⟩]
    (asciiRecords.filter fun record => record.encoding = .ascii)
  let leRecords := Analysis.Strings.strings (Raw.load utf16le 0x2000 .little) 2
  assertEqual "string scanner finds UTF-16LE" [⟨0x2000, "ABCD", Analysis.Strings.Encoding.utf16le⟩]
    (leRecords.filter fun record => record.encoding = .utf16le)
  let beRecords := Analysis.Strings.strings (Raw.load utf16be 0x3000 .little) 2
  assertTrue "string scanner finds UTF-16BE"
    (beRecords.any fun record => record.address = 0x3000 && record.text = "XY" && record.encoding = .utf16be)
  assertTrue "string scanner enforces minimum length"
    !((Analysis.Strings.strings (Raw.load utf16be 0x3000 .little) 4).any fun record => record.text = "XY")
  let signature ← match Analysis.Signatures.create "prologue"
    (ByteArray.mk #[0x55, 0x48, 0x89]) (ByteArray.mk #[0xff, 0xff, 0x00]) with
    | .ok signature => pure signature
    | .error error => throw <| IO.userError error
  let signatureImage := Raw.load (ByteArray.mk #[0, 0x55, 0x48, 0, 0x55, 0x48, 0x89]) 0x4000 .little
  assertEqual "masked signature finds all matches" [0x4001, 0x4004]
    (Analysis.Signatures.find signatureImage signature)
  Analysis.Signatures.save [signature] "native/build/signatures.sexp"
  let restoredSignatures ← Analysis.Signatures.load "native/build/signatures.sexp"
  assertTrue "signature database round trip" (restoredSignatures == [signature])
  match Analysis.Signatures.create "bad" (ByteArray.mk #[1]) (ByteArray.mk #[]) with
  | .error _ => IO.println "ok: signature length mismatch rejected"
  | .ok _ => throw <| IO.userError "signature length mismatch accepted"
  match Elf.decode small with
  | .error _ => IO.println "ok: malformed ELF rejected"
  | .ok _ => throw <| IO.userError "malformed ELF accepted"
  if ← System.FilePath.pathExists "/bin/echo" then
    let host ← Elf.load "/bin/echo"
    assertEqual "host ELF architecture" Arch.x86_64 host.arch
    assertEqual "host ELF address width" 64 host.addrWidth
    assertTrue "host ELF has sections" (!host.sections.isEmpty)
    assertTrue "host ELF has segments" (!host.segments.isEmpty)
    assertTrue "host ELF has symbols" (!host.symbols.isEmpty)
    assertTrue "host ELF has mapped regions" (!host.memory.entries.isEmpty)
    assertTrue "host ELF has executable segment" (host.segments.any Segment.executable)

end Bap.Tests.Image
