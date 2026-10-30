import Bap.Project.Basic
import Bap.Bil.Wire
import Bap.Knowledge.Persist

namespace Bap.Project

private def nat (value : Nat) : Sexp := .atom (toString value)
private def bool (value : Bool) : Sexp := .atom (toString value)

private def boolValue (input : Sexp) : Except String Bool := do
  match ← Sexp.asAtom input with
  | "true" => .ok true
  | "false" => .ok false
  | _ => .error "invalid project boolean"

private def encodeBytes (data : ByteArray) : Sexp :=
  .list (data.toList.map fun byte => nat byte.toNat)

private def decodeBytes (input : Sexp) : Except String ByteArray := do
  let bytes ← (← Sexp.asList input).mapM fun byte => Sexp.nat byte
  if bytes.any fun byte => byte ≥ 256 then
    .error "project byte is out of range"
  else
    .ok (ByteArray.mk (bytes.map UInt8.ofNat).toArray)

private def encodeArch : Image.Arch → Sexp
  | .x86 => .atom "x86"
  | .x86_64 => .atom "x86_64"
  | .arm => .atom "arm"
  | .aarch64 => .atom "aarch64"
  | .mips => .atom "mips"
  | .powerpc => .atom "powerpc"
  | .riscv => .atom "riscv"
  | .systemz => .atom "systemz"
  | .unknown => .atom "unknown"

private def decodeArch (input : Sexp) : Except String Image.Arch := do
  match ← Sexp.asAtom input with
  | "x86" => .ok .x86
  | "x86_64" => .ok .x86_64
  | "arm" => .ok .arm
  | "aarch64" => .ok .aarch64
  | "mips" => .ok .mips
  | "powerpc" => .ok .powerpc
  | "riscv" => .ok .riscv
  | "systemz" => .ok .systemz
  | "unknown" => .ok .unknown
  | _ => .error "invalid project architecture"

private def encodeSection (sec : Image.Section) : Sexp :=
  .tagged "section" [.atom sec.name, nat sec.addr, nat sec.offset,
    nat sec.size, nat sec.flags, nat sec.kind]

private def decodeSection (input : Sexp) : Except String Image.Section := do
  let args ← Sexp.expectTagged "section" 6 input
  match args with
  | [name, addr, offset, size, flags, kind] =>
    .ok ⟨← Sexp.asAtom name, ← Sexp.nat addr, ← Sexp.nat offset,
      ← Sexp.nat size, ← Sexp.nat flags, ← Sexp.nat kind⟩
  | _ => .error "invalid project section"

private def encodeSegment (segment : Image.Segment) : Sexp :=
  .tagged "segment" [.atom segment.name, nat segment.addr, nat segment.size,
    bool segment.readable, bool segment.writable, bool segment.executable]

private def decodeSegment (input : Sexp) : Except String Image.Segment := do
  let args ← Sexp.expectTagged "segment" 6 input
  match args with
  | [name, addr, size, readable, writable, executable] =>
    .ok ⟨← Sexp.asAtom name, ← Sexp.nat addr, ← Sexp.nat size,
      ← boolValue readable, ← boolValue writable, ← boolValue executable⟩
  | _ => .error "invalid project segment"

private def encodeSymbol (symbol : Image.Symbol) : Sexp :=
  .tagged "symbol" [.atom symbol.name, nat symbol.addr, nat symbol.size,
    bool symbol.isFunction, bool symbol.isDebug]

private def decodeSymbol (input : Sexp) : Except String Image.Symbol := do
  let args ← Sexp.expectTagged "symbol" 5 input
  match args with
  | [name, addr, size, isFunction, isDebug] =>
    .ok ⟨← Sexp.asAtom name, ← Sexp.nat addr, ← Sexp.nat size,
      ← boolValue isFunction, ← boolValue isDebug⟩
  | _ => .error "invalid project symbol"

private def encodeRegion (region : Image.MemRegion) : Sexp :=
  .tagged "region" [nat region.addr, encodeBytes region.data,
    bool region.readable, bool region.writable, bool region.executable]

private def decodeRegion (input : Sexp) : Except String Image.MemRegion := do
  let args ← Sexp.expectTagged "region" 5 input
  match args with
  | [addr, data, readable, writable, executable] =>
    .ok ⟨← Sexp.nat addr, ← decodeBytes data,
      ← boolValue readable, ← boolValue writable, ← boolValue executable⟩
  | _ => .error "invalid project memory region"

private def encodeImage (image : Image.Image) : Sexp :=
  .tagged "image" [
    encodeArch image.arch,
    nat image.addrWidth,
    Bil.Wire.printEndian image.endian,
    nat image.entryPoint,
    encodeBytes image.data,
    .list (image.sections.map encodeSection),
    .list (image.segments.map encodeSegment),
    .list (image.symbols.map encodeSymbol),
    .list (image.memory.entries.map fun entry => encodeRegion entry.1)
  ]

private def decodeImage (input : Sexp) : Except String Image.Image := do
  let args ← Sexp.expectTagged "image" 9 input
  match args with
  | [arch, width, endian, entry, data, sections, segments, symbols, memory] =>
    let arch ← decodeArch arch
    let width ← Sexp.nat width
    let endian ← Bil.Wire.parseEndian endian
    let entry ← Sexp.nat entry
    let data ← decodeBytes data
    let sections ← (← Sexp.asList sections).mapM decodeSection
    let segments ← (← Sexp.asList segments).mapM decodeSegment
    let symbols ← (← Sexp.asList symbols).mapM decodeSymbol
    let regions ← (← Sexp.asList memory).mapM decodeRegion
    let memory : Image.MemoryMap Unit := ⟨regions.map (·, ())⟩
    .ok {
      arch
      addrWidth := width
      endian
      entryPoint := entry
      data
      sections
      segments
      symbols
      memory
    }
  | _ => .error "invalid project image"

private def encodeFlow : Disasm.Flow → Sexp
  | .normal => .atom "normal"
  | .jump => .atom "jump"
  | .conditionalJump => .atom "conditionalJump"
  | .indirectJump => .atom "indirectJump"
  | .call => .atom "call"
  | .ret => .atom "ret"
  | .barrier => .atom "barrier"

private def decodeFlow (input : Sexp) : Except String Disasm.Flow := do
  match ← Sexp.asAtom input with
  | "normal" => .ok .normal
  | "jump" => .ok .jump
  | "conditionalJump" => .ok .conditionalJump
  | "indirectJump" => .ok .indirectJump
  | "call" => .ok .call
  | "ret" => .ok .ret
  | "barrier" => .ok .barrier
  | _ => .error "invalid project control flow"

private def encodeTarget : Option Nat → Sexp
  | none => .atom "none"
  | some target => nat target

private def decodeTarget (input : Sexp) : Except String (Option Nat) := do
  match input with
  | .atom "none" => .ok none
  | _ => .ok (some (← Sexp.nat input))

private def encodeInsn (insn : Disasm.Insn) : Sexp :=
  .tagged "insn" [nat insn.address, nat insn.size, .atom insn.asm,
    encodeFlow insn.flow, encodeTarget insn.target, Bil.Wire.printProgram insn.bil]

private def decodeInsn (input : Sexp) : Except String Disasm.Insn := do
  let args ← Sexp.expectTagged "insn" 6 input
  match args with
  | [address, size, assembly, flow, target, bil] =>
    .ok ⟨← Sexp.nat address, ← Sexp.nat size, ← Sexp.asAtom assembly,
      ← decodeFlow flow, ← decodeTarget target, ← Bil.Wire.parseStmts 1000000 bil⟩
  | _ => .error "invalid project instruction"

private def encodeEdge (edge : Nat × Nat) : Sexp :=
  .tagged "edge" [nat edge.1, nat edge.2]

private def decodeEdge (input : Sexp) : Except String (Nat × Nat) := do
  let args ← Sexp.expectTagged "edge" 2 input
  match args with
  | [source, target] => .ok (← Sexp.nat source, ← Sexp.nat target)
  | _ => .error "invalid project edge"

private def encodeDisasm (disasm : Disasm.Disasm) : Sexp :=
  .tagged "disasm" [nat disasm.entry, .list (disasm.instructions.map encodeInsn),
    .list (disasm.edges.map encodeEdge), .list (disasm.errors.map Sexp.atom)]

private def decodeDisasm (input : Sexp) : Except String Disasm.Disasm := do
  let args ← Sexp.expectTagged "disasm" 4 input
  match args with
  | [entry, instructions, edges, errors] =>
    let entry ← Sexp.nat entry
    let instructions ← (← Sexp.asList instructions).mapM decodeInsn
    let edges ← (← Sexp.asList edges).mapM decodeEdge
    let errors ← (← Sexp.asList errors).mapM Sexp.asAtom
    .ok ⟨entry, instructions, edges, errors⟩
  | _ => .error "invalid project disassembly"

private def encodeBinding (binding : String × String) : Sexp :=
  .tagged "binding" [.atom binding.1, .atom binding.2]

private def decodeBinding (input : Sexp) : Except String (String × String) := do
  let args ← Sexp.expectTagged "binding" 2 input
  match args with
  | [name, value] => .ok (← Sexp.asAtom name, ← Sexp.asAtom value)
  | _ => .error "invalid project storage binding"

def encode (project : Project) (persistent : List Knowledge.AnySlot := []) : Except String Sexp := do
  let names := persistent.map fun slot => slot.2.name
  let facts := project.knowledge.facts ++ project.knowledge.opinions.map fun opinion => opinion.fact
  match facts.find? fun fact => !names.contains fact.slot.2.name with
  | some fact => .error s!"unregistered project Knowledge slot {fact.slot.2.name}"
  | none =>
    let knowledge ← Knowledge.encodeState persistent project.knowledge
    .ok (.tagged "project" [
        match project.image with
        | some image => .tagged "some" [encodeImage image]
        | none => .atom "none",
        match project.disasm with
        | some disasm => .tagged "some" [encodeDisasm disasm]
        | none => .atom "none",
        .list (project.storage.map encodeBinding),
        .list (project.passed.map Sexp.atom),
        knowledge
      ])

def decode (input : Sexp) (persistent : List Knowledge.AnySlot := []) : Except String Project := do
  let args ← Sexp.expectTagged "project" 5 input
  match args with
  | [image, disasm, storage, passed, knowledge] =>
    let image ← match image with
      | .atom "none" => .ok none
      | _ => do
        let args ← Sexp.expectTagged "some" 1 image
        match args with
        | [image] => .ok (some (← decodeImage image))
        | _ => .error "invalid optional project image"
    let disasm ← match disasm with
      | .atom "none" => .ok none
      | _ => do
        let args ← Sexp.expectTagged "some" 1 disasm
        match args with
        | [disasm] => .ok (some (← decodeDisasm disasm))
        | _ => .error "invalid optional project disassembly"
    let storage ← (← Sexp.asList storage).mapM decodeBinding
    let passed ← (← Sexp.asList passed).mapM Sexp.asAtom
    let knowledge ← Knowledge.decodeState persistent knowledge
    .ok { image, disasm, knowledge, storage, passed }
  | _ => .error "invalid project"

def save (project : Project) (path : String) (persistent : List Knowledge.AnySlot := []) : IO Unit := do
  match encode project persistent with
  | .error error => throw <| IO.userError error
  | .ok encoded => IO.FS.writeFile path (toString encoded)

def loadSaved (path : String) (persistent : List Knowledge.AnySlot := []) : IO Project := do
  let input ← IO.FS.readFile path
  match Sexp.parse input with
  | .error error => throw <| IO.userError error
  | .ok input =>
    match decode input persistent with
    | .error error => throw <| IO.userError error
    | .ok project => pure project

end Bap.Project
