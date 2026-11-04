import Bap.Image.Elf
import Bap.Image.Macho
import Bap.Image.Pe

namespace Bap.Image

/-- Which decoder a file is for, by its magic number. -/
def dispatch (data : ByteArray) : Except String Image :=
  if data.size ≥ 4 && data.get! 0 = 0x7f && data.get! 1 = 0x45 && data.get! 2 = 0x4c && data.get! 3 = 0x46 then
    Elf.decode data
  else if data.size ≥ 2 && data.get! 0 = 0x4d && data.get! 1 = 0x5a then
    Pe.decode data
  else if data.size ≥ 4 &&
      (data.get! 0 = 0xcf && data.get! 1 = 0xfa && data.get! 2 = 0xed && data.get! 3 = 0xfe ||
       data.get! 0 = 0xfe && data.get! 1 = 0xed && data.get! 2 = 0xfa && data.get! 3 = 0xcf) then
    Macho.decode data
  else
    .error "unsupported executable format"

/-- Whether the bytes are ELF, PE or Mach-O, by their magic numbers. -/
private def isElf (data : ByteArray) : Bool :=
  data.size ≥ 4 && data.get! 0 = 0x7f && data.get! 1 = 0x45 && data.get! 2 = 0x4c && data.get! 3 = 0x46

/-- How many bytes of zeros past what a file has its regions would take, as its headers say, whatever its format. -/
def zeroFill (data : ByteArray) : Nat :=
  if isElf data then Elf.zeroFill data
  else if data.size ≥ 2 && data.get! 0 = 0x4d && data.get! 1 = 0x5a then Pe.zeroFill data
  else Macho.zeroFill data

/-- At most this many bytes of zeros past what a file has, of all its regions together: a header can say anything. -/
def zeroLimit : Nat := 2 ^ 32

/-- An image of the bytes of an executable, unless its headers ask for more zeros than `zeroLimit`. -/
def decode (data : ByteArray) : Except String Image :=
  if zeroFill data > zeroLimit then .error "the regions of the file are too large" else dispatch data

def load (path : String) : IO Image := do
  let data ← IO.FS.readBinFile path
  match decode data with
  | .ok image => pure image
  | .error error => throw <| IO.userError error

end Bap.Image
