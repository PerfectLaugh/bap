import Bap.Image.Ogre

namespace Bap.Image.Raw

def load (data : ByteArray) (base : Nat) (endian : Endian) (addrWidth : Nat := 64) : Image :=
  let region : MemRegion := ⟨base, data, true, false, true⟩
  let segment : Segment := ⟨"raw", base, data.size, true, false, true⟩
  {
    arch := .unknown
    addrWidth := addrWidth
    endian := endian
    entryPoint := base
    data := data
    segments := [segment]
    memory := MemoryMap.empty.add region ()
  }

end Bap.Image.Raw
