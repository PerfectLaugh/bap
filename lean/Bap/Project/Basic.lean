import Bap.Image.Loader
import Bap.Disasm.Recursive
import Bap.Target.X86
import Bap.Target.AArch64
import Bap.Target.RISCV
import Bap.Target.PowerPC
import Bap.Target.MIPS
import Bap.Target.ARM32
import Bap.Target.X8632
import Bap.Target.RISCV32
import Bap.Target.PowerPC32
import Bap.Target.MIPS32
import Bap.Target.Thumb
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

/-- The disassembler of an image for the code of a section that starts at `base`. An ARM entry point with bit 0 set runs in
Thumb state, except for the stubs of the linker, which are in ARM state. -/
def codeDisassembler (image : Image.Image) (name : String) (base : Nat) : IO (Option Disasm.Disassembler) :=
  match image.arch, image.addrWidth with
  | .x86_64, _ => some <$> Target.X86.disassembler base
  | .x86, _ => some <$> Target.X8632.disassembler base
  | .aarch64, _ => some <$> Target.AArch64.disassembler base
  | .riscv, 32 => some <$> Target.RISCV32.disassembler base
  | .riscv, _ => some <$> Target.RISCV.disassembler base
  | .powerpc, 32 => some <$> Target.PowerPC32.disassembler base
  | .powerpc, _ => some <$> Target.PowerPC.disassembler base
  | .mips, 32 => some <$> Target.MIPS32.disassembler base
  | .mips, _ => some <$> Target.MIPS.disassembler base
  | .arm, _ =>
    if image.entryPoint % 2 = 1 && name != ".plt" then some <$> Target.Thumb.disassembler base
    else some <$> Target.ARM32.disassembler base
  | _, _ => pure none

/-- The sections with instructions, as their ELF kind and flag or their Mach-O flags tell, each with the name it goes by.
PE has a region for each section, with the flag of its code. -/
private def codeSections (image : Image.Image) : List (String × Image.MemRegion) :=
  (image.sections.filter fun part =>
    (part.kind == 1 && part.flags &&& 4 != 0) || (part.kind == 0 && part.flags &&& 0x80000400 != 0 && part.size != 0)).filterMap fun part =>
    (image.memory.entries.find? fun entry =>
      entry.1.executable && entry.1.addr ≤ part.addr && part.addr + part.size ≤ entry.1.maxAddr).map fun entry =>
        let offset := part.addr - entry.1.addr
        (part.name, { entry.1 with addr := part.addr, data := entry.1.data.extract offset (offset + part.size) })

/-- The code of an image, each part with its name: its sections with instructions, or else its executable regions, or
else the region of its entry point. -/
def codeRegions (image : Image.Image) : List (String × Image.MemRegion) :=
  match codeSections image with
  | [] =>
    match (image.memory.entries.map Prod.fst).filter (·.executable) with
    | [] => ((image.memory.entries.map Prod.fst).filter (·.contains image.entryPoint)).map ("", ·)
    | regions => regions.map ("", ·)
  | sections => sections

/-- The number of a little- or big-endian word at `address`, of the first region with all of it. -/
private def readWord (image : Image.Image) (address size : Nat) : Option Nat :=
  (image.memory.entries.find? fun entry => entry.1.contains address && entry.1.contains (address + size - 1)).map fun entry =>
    let offset := address - entry.1.addr
    let bytes := (List.range size).map fun index => (entry.1.data.get! (offset + index)).toNat
    let ordered := if image.endian = .little then bytes.reverse else bytes
    ordered.foldl (fun value byte => value * 256 + byte) 0

/-- The functions an ELF file has its loader run, in the `.preinit_array`, `.init_array` and `.fini_array` sections,
whose kinds are 16, 14 and 15. -/
def initFunctions (image : Image.Image) : List Nat :=
  let size := image.addrWidth / 8
  (image.sections.filter fun part => part.kind == 14 || part.kind == 15 || part.kind == 16).flatMap fun part =>
    (List.range (part.size / size)).filterMap fun index => readWord image (part.addr + index * size) size

/-- The entry point of an image. An ARM one has the Thumb state in bit 0. -/
def entryOf (image : Image.Image) : Nat :=
  if image.arch = .arm then image.entryPoint - image.entryPoint % 2 else image.entryPoint

/-- Where the scan of an image starts: at its entry point, the functions of its symbol tables and the functions it has
its loader run, as far as they are in code, each once. -/
def roots (image : Image.Image) : List Nat :=
  let regions := (codeRegions image).map Prod.snd
  let symbols := (image.symbols.filter (·.isFunction)).map (·.addr)
  let candidates := entryOf image :: (symbols ++ initFunctions image)
  (candidates.foldl (init := (({} : Std.HashSet Nat), ([] : List Nat))) fun state address =>
    if state.1.contains address || !regions.any (·.contains address) then state
    else (state.1.insert address, address :: state.2)).2.reverse

/-- The names of the sections of stubs, which nothing jumps to directly when they are lazily bound. -/
private def stubSections : List String := [".plt", ".plt.sec", ".plt.got", ".iplt", "__stubs", "__stub_helper", ".MIPS.stubs"]

/-- The code without instructions in the stream, so that a linear sweep doesn't go through data. ARM has its constant
pools among the instructions. -/
private def sweepable (image : Image.Image) : Bool := image.arch != .arm

/-- The end of a region without the zeros at its end, which pad it to the alignment of its segment. -/
private def endOfData (region : Image.MemRegion) : Nat :=
  let rec go : Nat → Nat
    | 0 => 0
    | size + 1 => if region.data.get! size != 0 then size + 1 else go size
  region.addr + go region.size

/-- What a linear sweep goes through after the recursive scan, as starts and ends: the stubs, and all the code of an image
without a symbol table with sizes, which only has its exports to go by, where upstream finds its functions with byte
patterns. An image with one says where its functions are, and the sweep finds the targets of their jump tables in them. An
image without sections can have anything in its segments. -/
def sweepRanges (image : Image.Image) : List (Nat × Nat) :=
  let regions := codeRegions image
  let stubs := regions.filter fun part => stubSections.contains part.1
  let code :=
    if !sweepable image || image.sections.isEmpty then []
    else if image.sections.any (·.name == ".symtab") then
      (image.symbols.filter fun symbol => symbol.isFunction && symbol.size != 0).filterMap fun symbol =>
        if regions.any (·.2.contains symbol.addr) then some (symbol.addr, symbol.addr + symbol.size) else none
    else
      regions.map fun part => (part.2.addr, endOfData part.2)
  (stubs.map fun part => (part.2.addr, part.2.maxAddr)) ++ code

/-- The distance of the addresses a linear sweep tries again from after it fails. x86 functions start at 16 bytes. -/
private def sweepAlignment (image : Image.Image) : Nat :=
  match image.arch with
  | .x86 | .x86_64 => 16
  | .riscv => 2
  | _ => 4

/-- The recursive scan of all the code of an image, from all its roots, and a linear sweep of what it didn't find, in
`sweepRanges`. -/
def scanImage (image : Image.Image) : IO (Option Disasm.Disasm) := do
  let regions := (codeRegions image).map Prod.snd
  match regions, ← codeDisassembler image "" 0 with
  | [], _ | _, none => pure none
  | _, some base =>
    let decoders ← (codeRegions image).filterMapM fun part => do
      pure ((← codeDisassembler image part.1 part.2.addr).map (part.2, ·))
    let bytes := (decoders.map (·.1.size)).sum
    pure (some (← Disasm.Recursive.scanRegions (Disasm.Disassembler.ofRegions base decoders) bytes (entryOf image) (roots image)
      (sweepAlignment image) (sweepRanges image)))

def fromImage (image : Image.Image) : IO Project := do
  pure { image := some image, disasm := ← scanImage image }

def load (path : String) : IO Project := do
  fromImage (← Image.load path)

end Project
end Bap.Project
