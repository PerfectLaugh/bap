import Bap.Image.Elf
import Bap.Image.Macho
import Bap.Image.Pe

namespace Bap.Image

def decode (data : ByteArray) : Except String Image :=
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

def load (path : String) : IO Image := do
  let data ← IO.FS.readBinFile path
  match decode data with
  | .ok image => pure image
  | .error error => throw <| IO.userError error

end Bap.Image
