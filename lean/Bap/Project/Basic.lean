import Bap.Image.Loader
import Bap.Disasm.Recursive
import Bap.Target.X86
import Bap.Target.AArch64
import Bap.Target.RISCV
import Bap.Target.PowerPC
import Bap.Target.MIPS
import Bap.Target.ARM32
import Bap.Target.X8632
import Bap.Knowledge.Core

namespace Bap.Project

structure Project where
  image : Option Image.Image := none
  disasm : Option Disasm.Disasm := none
  knowledge : Knowledge.State := {}
  storage : List (String × String) := []
  passed : List String := []

namespace Project

def empty : Project := {}

def disassembled (project : Project) : Bool := project.disasm.isSome

def set (project : Project) (name value : String) : Project :=
  { project with storage := Assoc.put name value project.storage }

def get (project : Project) (name : String) : Option String := Assoc.get name project.storage

def markPassed (project : Project) (name : String) : Project :=
  { project with passed := name :: project.passed }

def fromImage (image : Image.Image) : IO Project := do
  let disasm ← match image.memory.entries.find? fun entry => entry.1.contains image.entryPoint with
    | none => pure none
    | some (region, _) =>
      match image.arch with
      | .x86_64 => pure (some (← Disasm.Recursive.scan (← Target.X86.disassembler region.addr) region.data image.entryPoint))
      | .x86 => pure (some (← Disasm.Recursive.scan (← Target.X8632.disassembler region.addr) region.data image.entryPoint))
      | .aarch64 => pure (some (← Disasm.Recursive.scan (← Target.AArch64.disassembler region.addr) region.data image.entryPoint))
      | .riscv => pure (some (← Disasm.Recursive.scan (← Target.RISCV.disassembler region.addr) region.data image.entryPoint))
      | .powerpc => pure (some (← Disasm.Recursive.scan (← Target.PowerPC.disassembler region.addr) region.data image.entryPoint))
      | .mips => pure (some (← Disasm.Recursive.scan (← Target.MIPS.disassembler region.addr) region.data image.entryPoint))
      | .arm => pure (some (← Disasm.Recursive.scan (← Target.ARM32.disassembler region.addr) region.data image.entryPoint))
      | _ => pure none
  pure { image := some image, disasm := disasm }

def load (path : String) : IO Project := do
  fromImage (← Image.load path)

end Project
end Bap.Project
