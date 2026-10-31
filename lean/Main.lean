import Bap.Bil.Wire
import Bap.Bil.Typecheck
import Bap.Image.Loader
import Bap.Image.Raw
import Bap.Disasm.Linear
import Bap.Disasm.Recursive
import Bap.Target.X86
import Bap.Target.X8632
import Bap.Target.AArch64
import Bap.Target.RISCV
import Bap.Target.PowerPC
import Bap.Target.MIPS
import Bap.Target.ARM32
import Bap.Primus.Lisp
import Bap.Project.Basic
import Bap.Analysis.Xrefs
import Bap.Analysis.Callgraph
import Bap.Symbolic.Executor

open Bap
open Bap.Bil

private def usage : String :=
  "usage: bap check FILE | bap print FILE | bap eval FILE [FUEL] | bap image FILE | bap raw FILE BASE | bap mc HEX | bap disassemble FILE | bap lisp FILE | bap analyze FILE | bap symbolic FILE"

private def loadProgram (path : String) : IO Program := do
  let input ← IO.FS.readFile path
  match Wire.parseProgram input with
  | .ok program => pure program
  | .error error => throw <| IO.userError error

private def check (path : String) : IO Unit := do
  let program ← loadProgram path
  match checkProgram program with
  | .ok _ => IO.println "well-typed"
  | .error error => throw <| IO.userError error

private def print (path : String) : IO Unit := do
  IO.println (Wire.renderProgram (← loadProgram path))

private def evaluate (path : String) (fuel : Nat) : IO Unit := do
  let program ← loadProgram path
  match checkProgram program with
  | .error error => throw <| IO.userError error
  | .ok _ =>
    match run program {} fuel with
    | .error error => throw <| IO.userError error
    | .ok (final, effect) =>
      IO.println s!"effect: {repr effect}"
      IO.println s!"environment: {repr final.env}"

private def parseNat (input : String) : Except String Nat :=
  if input.startsWith "0x" then
    Bil.Wire.parseHex (input.drop 2).toString
  else
    match input.toNat? with
    | some value => .ok value
    | none => .error s!"invalid natural number {input}"

private def image (path : String) : IO Unit := do
  let image ← Image.load path
  IO.println (repr image.summary)

private def raw (path : String) (base : Nat) : IO Unit := do
  let data ← IO.FS.readBinFile path
  IO.println (repr (Image.Raw.load data base .little).summary)

private def parseBytes (input : String) : Except String ByteArray := do
  let atoms := (input.splitOn " ").filter fun atom => !atom.isEmpty
  let bytes ← atoms.mapM Bil.Wire.parseHex
  if bytes.any fun byte => byte ≥ 256 then
    .error "instruction byte is out of range"
  else
    .ok (ByteArray.mk (bytes.map UInt8.ofNat).toArray)

private def mc (input : String) : IO Unit := do
  match parseBytes input with
  | .error error => throw <| IO.userError error
  | .ok bytes =>
    let result ← Disasm.Linear.sweep (← Target.X86.disassembler 0) bytes
    if result.errors.isEmpty then
      IO.println result.render
    else
      throw <| IO.userError (String.intercalate "\n" result.errors)

private def disassemble (path : String) : IO Unit := do
  let image ← Image.load path
  match image.memory.entries.find? fun entry => entry.1.contains image.entryPoint with
  | none => throw <| IO.userError "entry point is not mapped"
  | some (region, _) =>
    let result ← match image.arch with
      | .x86_64 => Disasm.Recursive.scan (← Target.X86.disassembler region.addr) region.data image.entryPoint
      | .x86 => Disasm.Recursive.scan (← Target.X8632.disassembler region.addr) region.data image.entryPoint
      | .aarch64 => Disasm.Recursive.scan (← Target.AArch64.disassembler region.addr) region.data image.entryPoint
      | .riscv => Disasm.Recursive.scan (← Target.RISCV.disassembler region.addr) region.data image.entryPoint
      | .powerpc => Disasm.Recursive.scan (← Target.PowerPC.disassembler region.addr) region.data image.entryPoint
      | .mips => Disasm.Recursive.scan (← Target.MIPS.disassembler region.addr) region.data image.entryPoint
      | .arm => Disasm.Recursive.scan (← Target.ARM32.disassembler region.addr) region.data image.entryPoint
      | _ => throw <| IO.userError "unsupported disassembly architecture"
    IO.println result.render

private def lisp (path : String) : IO Unit := do
  let input ← IO.FS.readFile path
  match Primus.Lisp.evalString input with
  | .ok (value, _) => IO.println (Primus.Lisp.render value)
  | .error error => throw <| IO.userError error

private def analyze (path : String) : IO Unit := do
  let project ← Project.Project.load path
  let xrefs := Analysis.Xrefs.create project
  let callgraph := Analysis.Callgraph.create xrefs
  IO.println s!"instructions: {project.disasm.map (fun disasm => disasm.instructions.length) |>.getD 0}"
  IO.println s!"xrefs: {xrefs.xrefs.length}"
  IO.println s!"callgraph edges: {callgraph.graph.edges.length}"

private def symbolic (path : String) : IO Unit := do
  let program ← loadProgram path
  match Symbolic.run program with
  | .ok results => IO.println s!"paths: {results.length}"
  | .error error => throw <| IO.userError error

def main (args : List String) : IO Unit := do
  match args with
  | ["check", path] => check path
  | ["print", path] => print path
  | ["eval", path] => evaluate path 100000
  | ["eval", path, fuel] =>
    match fuel.toNat? with
    | some fuel => evaluate path fuel
    | none => throw <| IO.userError "fuel must be a natural number"
  | ["image", path] => image path
  | ["raw", path, base] =>
    match parseNat base with
    | .ok base => raw path base
    | .error error => throw <| IO.userError error
  | ["disassemble", path] => disassemble path
  | ["lisp", path] => lisp path
  | ["analyze", path] => analyze path
  | ["symbolic", path] => symbolic path
  | "mc" :: atoms => mc (String.intercalate " " atoms)
  | _ => IO.println usage
