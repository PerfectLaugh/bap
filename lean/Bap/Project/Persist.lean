import Bap.Project.Basic
import Bap.Bil.Binary
import Bap.Knowledge.Persist

/-! A saved project is binary. Numbers are in base 128 and so have no width limit, code and instruction texts and the variables are
stored once, and read back shared. `Bap.Proofs.Project` proves that what `serialize` writes, `deserialize` reads back. -/

namespace Bap.Project

open Binary

private def archCode : Image.Arch → Nat
  | .x86 => 0 | .x86_64 => 1 | .arm => 2 | .aarch64 => 3 | .mips => 4 | .powerpc => 5 | .riscv => 6 | .systemz => 7 | .unknown => 8

private def archOf? : Nat → Option Image.Arch
  | 0 => some .x86 | 1 => some .x86_64 | 2 => some .arm | 3 => some .aarch64 | 4 => some .mips | 5 => some .powerpc
  | 6 => some .riscv | 7 => some .systemz | 8 => some .unknown | _ => none

private def putSection (out : ByteArray) (sec : Image.Section) : ByteArray :=
  putNat (putNat (putNat (putNat (putNat (putText out sec.name) sec.addr) sec.offset) sec.size) sec.flags) sec.kind

private def getSection (data : ByteArray) (pos : Nat) : Option (Image.Section × Nat) := do
  let (name, pos) ← getText data pos
  let (addr, pos) ← getNat data pos
  let (offset, pos) ← getNat data pos
  let (size, pos) ← getNat data pos
  let (flags, pos) ← getNat data pos
  let (kind, pos) ← getNat data pos
  some (⟨name, addr, offset, size, flags, kind⟩, pos)

private def putSegment (out : ByteArray) (segment : Image.Segment) : ByteArray :=
  putBool (putBool (putBool (putNat (putNat (putText out segment.name) segment.addr) segment.size) segment.readable)
    segment.writable) segment.executable

private def getSegment (data : ByteArray) (pos : Nat) : Option (Image.Segment × Nat) := do
  let (name, pos) ← getText data pos
  let (addr, pos) ← getNat data pos
  let (size, pos) ← getNat data pos
  let (readable, pos) ← getBool data pos
  let (writable, pos) ← getBool data pos
  let (executable, pos) ← getBool data pos
  some (⟨name, addr, size, readable, writable, executable⟩, pos)

private def putSymbol (out : ByteArray) (symbol : Image.Symbol) : ByteArray :=
  putBool (putBool (putBool (putNat (putNat (putText out symbol.name) symbol.addr) symbol.size) symbol.isFunction) symbol.isDebug)
    symbol.thumb

private def getSymbol (data : ByteArray) (pos : Nat) : Option (Image.Symbol × Nat) := do
  let (name, pos) ← getText data pos
  let (addr, pos) ← getNat data pos
  let (size, pos) ← getNat data pos
  let (isFunction, pos) ← getBool data pos
  let (isDebug, pos) ← getBool data pos
  let (thumb, pos) ← getBool data pos
  some (⟨name, addr, size, isFunction, isDebug, thumb⟩, pos)

private def putRegion (out : ByteArray) (region : Image.MemRegion) : ByteArray :=
  putBool (putBool (putBool (putBytes (putNat out region.addr) region.data) region.readable) region.writable) region.executable

private def getRegion (data : ByteArray) (pos : Nat) : Option (Image.MemRegion × Nat) := do
  let (addr, pos) ← getNat data pos
  let (bytes, pos) ← getBytes data pos
  let (readable, pos) ← getBool data pos
  let (writable, pos) ← getBool data pos
  let (executable, pos) ← getBool data pos
  some (⟨addr, bytes, readable, writable, executable⟩, pos)

private def putImage (out : ByteArray) (image : Image.Image) : ByteArray :=
  let out := putNat out (archCode image.arch)
  let out := putNat out image.addrWidth
  let out := putEndian out image.endian
  let out := putNat out image.entryPoint
  let out := putBytes out image.data
  let out := putList putSection out image.sections
  let out := putList putSegment out image.segments
  let out := putList putSymbol out image.symbols
  putList putRegion out (image.memory.entries.map Prod.fst)

private def getImage (data : ByteArray) (pos : Nat) : Option (Image.Image × Nat) := do
  let (arch, pos) ← getNat data pos
  let arch ← archOf? arch
  let (addrWidth, pos) ← getNat data pos
  let (endian, pos) ← getEndian data pos
  let (entryPoint, pos) ← getNat data pos
  let (bytes, pos) ← getBytes data pos
  let (sections, pos) ← getList (getSection data) data pos
  let (segments, pos) ← getList (getSegment data) data pos
  let (symbols, pos) ← getList (getSymbol data) data pos
  let (regions, pos) ← getList (getRegion data) data pos
  some ({ arch, addrWidth, endian, entryPoint, data := bytes, sections, segments, symbols, memory := ⟨regions.map (·, ())⟩ }, pos)

private def flowCode : Disasm.Flow → Nat
  | .normal => 0 | .jump => 1 | .conditionalJump => 2 | .indirectJump => 3 | .call => 4 | .ret => 5 | .barrier => 6

private def flowOf? : Nat → Option Disasm.Flow
  | 0 => some .normal | 1 => some .jump | 2 => some .conditionalJump | 3 => some .indirectJump | 4 => some .call
  | 5 => some .ret | 6 => some .barrier | _ => none

/-- The tables of a disassembly, of what its instructions have in common, and where each instruction has its parts. -/
structure Tables where
  vars : Table Bap.Var := {}
  programs : Table Bil.Program := {}
  texts : Table String := {}
  programAt : Array Nat := #[]
  textAt : Array Nat := #[]

private def addInsn (tables : Tables) (insn : Disasm.Insn) : Tables :=
  match tables with
  | ⟨vars, programs, texts, programAt, textAt⟩ =>
    let (programs, programPosition) := programs.place insn.bil
    let (texts, textPosition) := texts.place insn.asm
    ⟨vars, programs, texts, programAt.push programPosition, textAt.push textPosition⟩

private def tablesOf (instructions : List Disasm.Insn) : Tables :=
  let tables := instructions.foldl addInsn {}
  { tables with vars := tables.programs.items.foldl (init := {}) Binary.addProgramVars }

private def putInsn (tables : Tables) (number : Nat) (out : ByteArray) (insn : Disasm.Insn) : ByteArray :=
  let out := putNat out insn.address
  let out := putNat out insn.size
  let out := putAt putText tables.texts.items (tables.textAt.getD number 0) out insn.asm
  let out := putNat out (flowCode insn.flow)
  let out := putOption putNat out insn.target
  putAt (putProgram tables.vars) tables.programs.items (tables.programAt.getD number 0) out insn.bil

/-- The instructions from the one of that number on. -/
private def putInsns (tables : Tables) (out : ByteArray) : List Disasm.Insn → Nat → ByteArray
  | [], _ => out
  | insn :: rest, number => putInsns tables (putInsn tables number out insn) rest (number + 1)

private def getInsn (vars : Array Bap.Var) (programs : Array Bil.Program) (texts : Array String) (data : ByteArray) (pos : Nat) :
    Option (Disasm.Insn × Nat) := do
  let (address, pos) ← getNat data pos
  let (size, pos) ← getNat data pos
  let (asm, pos) ← getRef (getText data) texts data pos
  let (flow, pos) ← getNat data pos
  let flow ← flowOf? flow
  let (target, pos) ← getOption (getNat data) data pos
  let (bil, pos) ← getRef (getProgram vars data) programs data pos
  some (⟨address, size, asm, flow, target, bil⟩, pos)

private def putEdge (out : ByteArray) (edge : Nat × Nat) : ByteArray :=
  putNat (putNat out edge.1) edge.2

private def getEdge (data : ByteArray) (pos : Nat) : Option ((Nat × Nat) × Nat) := do
  let (source, pos) ← getNat data pos
  let (target, pos) ← getNat data pos
  some ((source, target), pos)

private def putDisasm (tables : Tables) (out : ByteArray) (disasm : Disasm.Disasm) : ByteArray :=
  let out := putNat out disasm.entry
  let out := putList putVar out tables.vars.items.toList
  let out := putList (putProgram tables.vars) out tables.programs.items.toList
  let out := putList putText out tables.texts.items.toList
  let out := putInsns tables (putNat out disasm.instructions.length) disasm.instructions 0
  let out := putList putEdge out disasm.edges
  putList putText out disasm.errors

private def getDisasm (data : ByteArray) (pos : Nat) : Option (Disasm.Disasm × Nat) := do
  let (entry, pos) ← getNat data pos
  let (vars, pos) ← getArray (getVar data) data pos
  let (programs, pos) ← getArray (getProgram vars data) data pos
  let (texts, pos) ← getArray (getText data) data pos
  let (instructions, pos) ← getList (getInsn vars programs texts data) data pos
  let (edges, pos) ← getList (getEdge data) data pos
  let (errors, pos) ← getList (getText data) data pos
  some (⟨entry, instructions, edges, errors⟩, pos)

/-- The code is no deeper than what the reader goes. -/
private def disasmFits (tables : Tables) (disasm : Disasm.Disasm) : Bool :=
  tables.programs.items.all (stmtsDepth · ≤ maxDepth) && disasm.instructions.all (stmtsDepth ·.bil ≤ maxDepth)

private def putBinding (out : ByteArray) (binding : String × String) : ByteArray :=
  putText (putText out binding.1) binding.2

private def getBinding (data : ByteArray) (pos : Nat) : Option ((String × String) × Nat) := do
  let (name, pos) ← getText data pos
  let (value, pos) ← getText data pos
  some ((name, value), pos)

private def magic : ByteArray := "BAPPROJECT2\n".toUTF8

private def putProject (project : Project) (tables : Tables) (knowledge : String) : ByteArray :=
  let out := magic
  let out := putOption putImage out project.image
  let out := putOption (putDisasm tables) out project.disasm
  let out := putList putBinding out project.storage
  let out := putList putText out project.passed
  putText out knowledge

private def getProject (data : ByteArray) : Option (Project × String) := do
  if data.extract 0 magic.size ≠ magic then none
  let (image, pos) ← getOption (getImage data) data magic.size
  let (disasm, pos) ← getOption (getDisasm data) data pos
  let (storage, pos) ← getList (getBinding data) data pos
  let (passed, pos) ← getList (getText data) data pos
  let (knowledge, pos) ← getText data pos
  if pos != data.size then none
  some ({ image, disasm, storage, passed }, knowledge)

def serialize (project : Project) (persistent : List Knowledge.AnySlot := []) : Except String ByteArray := do
  let names := persistent.map fun slot => slot.2.name
  let facts := project.knowledge.facts ++ project.knowledge.opinions.map fun opinion => opinion.fact
  match facts.find? fun fact => !names.contains fact.slot.2.name with
  | some fact => .error s!"unregistered project Knowledge slot {fact.slot.2.name}"
  | none =>
    let knowledge ← Knowledge.encodeState persistent project.knowledge
    let tables := tablesOf ((project.disasm.map (·.instructions)).getD [])
    if (project.disasm.map (disasmFits tables)).getD true then .ok (putProject project tables (toString knowledge))
    else .error "project code is nested too deep"

def deserialize (data : ByteArray) (persistent : List Knowledge.AnySlot := []) : Except String Project := do
  match getProject data with
  | none => .error "not a well-formed project"
  | some (project, knowledge) =>
    let knowledge ← Knowledge.decodeState persistent (← Sexp.parse knowledge)
    .ok { project with knowledge }

def save (project : Project) (path : String) (persistent : List Knowledge.AnySlot := []) : IO Unit := do
  match serialize project persistent with
  | .error error => throw <| IO.userError error
  | .ok data => IO.FS.writeBinFile path data

def loadSaved (path : String) (persistent : List Knowledge.AnySlot := []) : IO Project := do
  match deserialize (← IO.FS.readBinFile path) persistent with
  | .error error => throw <| IO.userError error
  | .ok project => pure project

end Bap.Project
