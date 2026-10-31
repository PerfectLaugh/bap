import Bap.Image.Loader
import Bap.Disasm.Recursive
import Bap.Disasm.Interwork
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

/-- The PowerPC of an image: its ELF class and encoding. -/
def powerpcVariant (image : Image.Image) : Target.LLVMLift.PowerPCVariant :=
  { bits := if image.addrWidth = 32 then 32 else 64, endian := image.endian }

/-- The MIPS of an image: its ELF class and encoding, and the architecture of its `e_flags`. -/
def mipsVariant (image : Image.Image) : Target.LLVMLift.MipsVariant :=
  { bits := if image.addrWidth = 32 then 32 else 64, endian := image.endian
    release6 := Image.Elf.mipsRelease6 (Image.Elf.machineFlags image) }

/-- The sections with instructions, as their ELF kind and flag, their Mach-O flags, also of `S_SYMBOL_STUBS`, whose kind is 8, or their PE flag
`IMAGE_SCN_MEM_EXECUTE` tell, each with the name it goes by. A PE section has its `VirtualSize`, past which its region has only the padding of the file. -/
private def codeSections (image : Image.Image) : List (String × Image.MemRegion) :=
  (image.sections.filter fun part =>
    (part.kind == 1 && part.flags &&& 4 != 0) || (part.kind == 0 && part.flags &&& 0xa0000400 != 0 && part.size != 0) ||
      (part.kind == 8 && part.flags &&& 0x80000000 != 0 && part.size != 0)).filterMap fun part =>
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

/-- The runs of mapping symbols in the order of their addresses, each up to the next one or the end of its part. -/
private def runsOf (regions : List Image.MemRegion) : List (Nat × Disasm.Interwork.Code) → List Disasm.Interwork.Run
  | [] => []
  | (start, kind) :: rest =>
    match (regions.find? (·.contains start)).map (·.maxAddr) with
    | none => runsOf regions rest
    | some limit =>
      let stop := match rest.head? with
        | some next => min next.1 limit
        | none => limit
      if start < stop then ⟨start, stop, kind⟩ :: runsOf regions rest else runsOf regions rest

/-- The runs of an ARM image, in the order of their addresses. -/
def armRuns (image : Image.Image) : Array Disasm.Interwork.Run :=
  if image.arch != .arm then #[] else
  let symbols := (image.symbols.filterMap fun symbol =>
    (Disasm.Interwork.mappingKind symbol.name).map (symbol.addr, ·)).mergeSort fun left right => left.1 ≤ right.1
  (runsOf ((codeRegions image).map Prod.snd) symbols).toArray

/-- The disassembler of an image for the code of a part that starts at `base`. That of an ARM image goes over keys of
addresses and states, of `Interwork`, with what the mapping symbols of the image say. -/
def codeDisassembler (image : Image.Image) (base : Nat) : IO (Option Disasm.Disassembler) :=
  match image.arch, image.addrWidth with
  | .x86_64, _ => some <$> Target.X86.disassembler base
  | .x86, _ => some <$> Target.X8632.disassembler base
  | .aarch64, _ => some <$> Target.AArch64.disassembler base
  | .riscv, 32 => some <$> Target.RISCV32.disassembler base
  | .riscv, _ => some <$> Target.RISCV.disassembler base
  | .powerpc, _ => some <$> Target.PowerPC.disassembler base (powerpcVariant image)
  | .mips, _ => some <$> Target.MIPS.disassembler base (mipsVariant image)
  | .arm, _ => do
    let arm ← Target.ARM32.disassembler base
    let thumb ← Target.Thumb.disassembler base
    pure (some (Disasm.Interwork.decoder (armRuns image) arm thumb))
  | _, _ => pure none

/-- The number of a little- or big-endian word at `address`, of the first region with all of it. -/
private def readWord (image : Image.Image) (address size : Nat) : Option Nat :=
  (image.memory.entries.find? fun entry => entry.1.contains address && entry.1.contains (address + size - 1)).map fun entry =>
    let offset := address - entry.1.addr
    let bytes := (List.range size).map fun index => (entry.1.data.get! (offset + index)).toNat
    let ordered := if image.endian = .little then bytes.reverse else bytes
    ordered.foldl (fun value byte => value * 256 + byte) 0

/-- The words of a table in memory. -/
private def tableWords (image : Image.Image) (address size : Nat) : List Nat :=
  let width := image.addrWidth / 8
  (List.range (size / width)).filterMap fun index => readWord image (address + index * width) width

/-- The functions an ELF file has its loader run, in the `.preinit_array`, `.init_array` and `.fini_array` sections,
whose kinds are 16, 14 and 15, and what its dynamic linking says: `DT_INIT`, `DT_FINI` and the same arrays, which is all
that a file without sections has. -/
def initFunctions (image : Image.Image) : List Nat :=
  let inSections := (image.sections.filter fun part => part.kind == 14 || part.kind == 15 || part.kind == 16).flatMap fun part =>
    tableWords image part.addr part.size
  let tag := Image.Elf.tagOf image
  let single := [tag 12, tag 13].filterMap id
  let arrays := [(25, 27), (26, 28), (32, 33)].flatMap fun tags =>
    match tag tags.1, tag tags.2 with
    | some address, some size => tableWords image address size
    | _, _ => []
  inSections ++ single ++ arrays

/-- What the slots of the jumps of a PLT hold before they are bound: an address in the PLT. `DT_JMPREL` has the relocations
of the slots, of the size of `DT_PLTREL`, and they start with the address of the slot. -/
def pltEntries (image : Image.Image) : List Nat :=
  let tag := Image.Elf.tagOf image
  match tag 23, tag 2 with
  | some table, some size =>
    let width := image.addrWidth / 8
    let entry := if tag 20 == some 7 then 3 * width else 2 * width
    (List.range (size / entry)).filterMap fun index =>
      (readWord image (table + index * entry) width).bind fun slot => readWord image slot width
  | _, _ => []

/-- A number of `size` bytes as a signed distance from `base`, in the addresses of an image. -/
private def fromBase (image : Image.Image) (base value : Nat) (bits : Nat) : Nat :=
  let modulus := 2 ^ image.addrWidth
  if value < 2 ^ (bits - 1) then (base + value) % modulus
  else (base + modulus - (2 ^ bits - value)) % modulus

/-- The functions of the unwind tables of a file, which it keeps of all it has, and also when it is stripped. `PT_GNU_EH_FRAME`
has the header of `.eh_frame`, with a sorted table of 4-byte offsets of function starts when its encoding is 0x3b. Each entry of
`PT_ARM_EXIDX` starts with an offset of 31 bits to a function, with no Thumb bit, so a function has the state of the entry
point. -/
def unwindFunctions (image : Image.Image) : List Nat :=
  let frames := match Image.Elf.programHeaderOf image 0x6474e550 with
    | some header =>
      match readWord image header.addr 4 with
      | some head =>
        -- the version, and the encodings of the pointer to `.eh_frame`, of the count and of the table, little- or big-endian
        let byte (index : Nat) : Nat :=
          if image.endian = .little then head / 256 ^ index % 256 else head / 256 ^ (3 - index) % 256
        if byte 0 == 1 && byte 1 == 0x1b && byte 2 == 0x03 && byte 3 == 0x3b then
          match readWord image (header.addr + 8) 4 with
          | some count =>
            (List.range count).filterMap fun index =>
              (readWord image (header.addr + 12 + index * 8) 4).map fun value => fromBase image header.addr value 32
          | none => []
        else []
      | none => []
    | none => []
  let indices := match Image.Elf.programHeaderOf image 0x70000001 with
    | some header =>
      if image.arch != .arm then []
      else (List.range (header.fileSize / 8)).filterMap fun index =>
        let entry := header.addr + index * 8
        (readWord image entry 4).bind fun word =>
          let start := fromBase image entry (word % 0x80000000) 31
          -- a linker ends the table with an entry for what is after the last function
          if readWord image start 4 == some 0 then none else some (start + image.entryPoint % 2)
    | none => []
  frames ++ indices

/-- The entry point of an image. An ARM one has the Thumb state in bit 0. -/
def entryOf (image : Image.Image) : Nat :=
  if image.arch = .arm then image.entryPoint - image.entryPoint % 2 else image.entryPoint

/-- Where the code of a function symbol starts, as the decoder of its image goes by it. -/
def symbolStart (symbol : Image.Symbol) : Nat :=
  if symbol.thumb then Disasm.Interwork.key symbol.addr true else symbol.addr

/-- Where the scan of an image starts: at its entry point, the functions of its symbol tables and the functions it has
its loader run, as far as they are in code, each once. An image without a symbol table with sizes also has what its unwind
tables say, and one without sections what its PLT says. An ARM image has the state in bit 0 of its entry point and of the
words of its loader. -/
def scanRoots (image : Image.Image) : List Nat :=
  let regions := (codeRegions image).map Prod.snd
  let symbols := (image.symbols.filter (·.isFunction)).map symbolStart
  let stubs := if image.sections.isEmpty then pltEntries image else []
  let unwound := if image.sections.any (·.name == ".symtab") then [] else unwindFunctions image
  let candidates := image.entryPoint :: (symbols ++ initFunctions image ++ stubs ++ unwound)
  (candidates.foldl (init := (({} : Std.HashSet Nat), ([] : List Nat))) fun state address =>
    if state.1.contains address || !regions.any (·.contains address) then state
    else (state.1.insert address, address :: state.2)).2.reverse

/-- The addresses that the scan of an image starts at. -/
def roots (image : Image.Image) : List Nat :=
  if image.arch = .arm then (scanRoots image).map Disasm.Interwork.addressOf else scanRoots image

/-- The names of the sections of stubs, which nothing jumps to directly when they are lazily bound. -/
private def stubSections : List String := [".plt", ".plt.sec", ".plt.got", ".iplt", ".glink", "__stubs", "__stub_helper", ".MIPS.stubs"]

/-- The end of a region without the zeros at its end, which pad it to the alignment of its segment. -/
private def endOfData (region : Image.MemRegion) : Nat :=
  let rec go : Nat → Nat
    | 0 => 0
    | size + 1 => if region.data.get! size != 0 then size + 1 else go size
  region.addr + go region.size

/-- What a linear sweep goes through after the recursive scan, as starts and ends: the stubs, and all the code of an image
without a symbol table with sizes, which only has its exports to go by, where upstream finds its functions with byte
patterns: its sections or its executable segments. An image with one says where its functions are, and the sweep finds the
targets of their jump tables in them, and not the padding between them. ARM has its constant pools among the instructions,
so what is not a stub is swept where its mapping symbols say that it is code. -/
def sweepRanges (image : Image.Image) : List (Nat × Nat) :=
  let regions := codeRegions image
  let stubs := regions.filter fun part => stubSections.contains part.1
  if image.arch = .arm then
    (stubs.map fun part => (part.2.addr, part.2.maxAddr)) ++ (armRuns image).toList.filterMap fun run =>
      match run.kind with
      | .arm => some (run.start, run.stop)
      | .thumb => some (Disasm.Interwork.key run.start true, run.stop)
      | .data => none
  else
    let code :=
      if image.sections.any (·.name == ".symtab") then
        (image.symbols.filter fun symbol => symbol.isFunction && symbol.size != 0).filterMap fun symbol =>
          if regions.any (·.2.contains symbol.addr) then some (symbol.addr, symbol.addr + symbol.size) else none
      else
        regions.map fun part => (part.2.addr, endOfData part.2)
    (stubs.map fun part => (part.2.addr, part.2.maxAddr)) ++ code

/-- A byte of the code of an image. -/
private def codeByte (regions : List Image.MemRegion) (address : Nat) : Option Nat :=
  (regions.find? (·.contains address)).map fun region => (region.data.get! (address - region.addr)).toNat

/-- Where a run of a byte that starts at an address ends, up to the end of its region. -/
private def endOfRun (regions : List Image.MemRegion) (byte address : Nat) : Nat :=
  match regions.find? (·.contains address) with
  | none => address
  | some region =>
    let rec go : Nat → Nat → Nat
      | 0, cursor => cursor
      | fuel + 1, cursor =>
        if cursor < region.maxAddr && (region.data.get! (cursor - region.addr)).toNat == byte then go fuel (cursor + 1)
        else cursor
    go (region.maxAddr - address) address

/-- Whether code can pad up to an address with bytes that aren't part of its next function. x86 functions start at 16
bytes, after `int3`, `nop`, or a long `nop`, which ends in a zero. -/
private def x86PaddingEnd (regions : List Image.MemRegion) (address : Nat) : Bool :=
  address % 16 == 0 &&
    match codeByte regions (address - 1), codeByte regions address with
    | some before, some here =>
      [0xcc, 0x90, 0].contains before && ![0xcc, 0x90, 0].contains here
    | _, _ => false

/-- Past the end of what is in a section or at the end of a segment, there are zeros, which are not instructions of any of
these targets, and the words that `ld.lld` pads ARM stubs with. -/
private def paddingOf (image : Image.Image) (regions : List Image.MemRegion) (address : Nat) : Option Nat :=
  let code := if image.arch = .arm then Disasm.Interwork.addressOf address else address
  let state := address - code
  let run (byte count : Nat) : Option Nat :=
    let stop := endOfRun regions byte code
    if stop ≥ code + count then some ((stop - code) / count * count + address) else none
  match image.arch, codeByte regions code, state with
  | .x86, some 0, _ | .x86_64, some 0, _ => run 0 2
  | .arm, some 0, _ => run 0 4
  | .arm, some 0xd4, _ => run 0xd4 4
  | .riscv, some 0, _ => run 0 2
  | .aarch64, some 0, _ | .powerpc, some 0, _ => run 0 4
  | _, _, _ => none

/-- How the linear sweep of an image goes: instructions of x86 have many sizes, so after what doesn't decode it goes on at
the end of padding, and the others are aligned, so it goes on at the next one. -/
private def sweepPlan (image : Image.Image) : Disasm.Recursive.SweepPlan :=
  let regions := (codeRegions image).map Prod.snd
  let stride := match image.arch with
    | .x86 | .x86_64 => 1
    | .arm | .riscv => 2
    | _ => 4
  { stride
    skip := paddingOf image regions
    resume := match image.arch with
      | .x86 | .x86_64 => x86PaddingEnd regions
      | _ => fun _ => true }

/-- The recursive scan of all the code of an image, from all its roots, and a linear sweep of what it didn't find, in
`sweepRanges`. -/
def scanImage (image : Image.Image) : IO (Option Disasm.Disasm) := do
  let regions := (codeRegions image).map Prod.snd
  match regions, ← codeDisassembler image 0 with
  | [], _ | _, none => pure none
  | _, some base =>
    let decoders ← (codeRegions image).filterMapM fun part => do
      pure ((← codeDisassembler image part.2.addr).map (part.2, ·))
    let bytes := (decoders.map (·.1.size)).sum
    let disasm ← Disasm.Recursive.scanRegions (Disasm.Disassembler.ofRegions base decoders) bytes (entryOf image) (scanRoots image)
      (sweepPlan image) (sweepRanges image)
    pure (some (if image.arch = .arm then Disasm.Interwork.unkey disasm else disasm))

def fromImage (image : Image.Image) : IO Project := do
  pure { image := some image, disasm := ← scanImage image }

def load (path : String) : IO Project := do
  fromImage (← Image.load path)

end Project
end Bap.Project
