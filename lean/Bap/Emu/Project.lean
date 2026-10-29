import Bap.Emu
import Bap.Project.Basic

namespace Bap.Emu

private def imageArch : SyscallAbi → Image.Arch
  | .riscv => .riscv
  | .x86_64 => .x86_64
  | .aarch64 => .aarch64
  | .mips => .mips

private def imageWidth (config : Config) : Except String Nat :=
  match config.memory.typ with
  | .mem width 8 => .ok width
  | _ => .error "Emu memory must have byte-wide cells"

private def mergeInstructions (left right : List Disasm.Insn) : List Disasm.Insn :=
  right.foldl (init := left) fun instructions insn =>
    if instructions.any fun current => current.address == insn.address then instructions
    else instructions ++ [insn]

private def mergeEdges (left right : List (Nat × Nat)) : List (Nat × Nat) :=
  right.foldl (init := left) fun edges edge =>
    if edges.contains edge then edges else edges ++ [edge]

private def mergeDisasm (left right : Disasm.Disasm) : Disasm.Disasm := {
  entry := left.entry
  instructions := mergeInstructions left.instructions right.instructions
  edges := mergeEdges left.edges right.edges
  errors := left.errors ++ right.errors
}

def project (emu : Emu) (roots : List Nat := []) (symbols : List (String × Nat) := []) :
    IO Project.Project := do
  Bap.Emu.refreshRegions emu
  let entry ← emu.pc.get
  let mapped ← emu.regions.get
  let width ← match imageWidth emu.config with
    | .ok width => pure width
    | .error error => throw <| IO.userError error
  let roots := (entry :: roots ++ symbols.map Prod.snd).foldl (init := []) fun roots root =>
    if roots.contains root then roots else roots ++ [root]
  let memory : Image.MemoryMap Unit := mapped.foldl (init := Image.MemoryMap.empty) fun memory region =>
    memory.add ⟨region.address, region.data, region.protection.readable,
      region.protection.writable, region.protection.executable⟩ ()
  let image : Image.Image := {
    arch := imageArch emu.config.syscallAbi
    addrWidth := width
    endian := emu.config.endian
    entryPoint := entry
    data := ByteArray.empty
    segments := mapped.map fun region => {
      name := "live"
      addr := region.address
      size := region.data.size
      readable := region.protection.readable
      writable := region.protection.writable
      executable := region.protection.executable
    }
    symbols := symbols.map fun symbol => {
      name := symbol.1
      addr := symbol.2
      size := 0
      isFunction := true
      isDebug := false
    }
    memory := memory
  }
  let disasm ← mapped.foldlM (init := ({ entry := entry } : Disasm.Disasm)) fun disasm region => do
    if !region.protection.executable then
      pure disasm
    else
      let regionRoots := roots.filter region.contains
      let disassembler ← match emu.config.disassemblerAt with
        | some create => create region.address
        | none => pure emu.config.disassembler
      regionRoots.foldlM (init := disasm) fun disasm root => do
        let scanned ← Disasm.Recursive.scan disassembler region.data root
        pure (mergeDisasm disasm scanned)
  pure { image := some image, disasm := some disasm }

end Bap.Emu
