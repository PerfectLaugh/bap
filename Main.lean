import Bap.Bil.Wire
import Bap.Bil.Typecheck
import Bap.Image.Loader
import Bap.Image.Raw
import Bap.Disasm.Linear
import Bap.Disasm.Recursive
import Bap.Target.X86
import Bap.Linux.Machine
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
  "usage: bap check FILE | bap run [--copy PATH].. [--root DIR] [--env NAME=VALUE].. [--strace] PROGRAM [ARGS] | bap print FILE | bap eval FILE [FUEL] | bap image FILE | bap raw FILE BASE | bap mc HEX | bap disassemble FILE | bap lisp FILE | bap analyze FILE | bap symbolic FILE"

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
  match (← Project.Project.load path).disasm with
  | none => throw <| IO.userError "no code to disassemble"
  | some result => IO.println result.render

private def lisp (path : String) : IO Unit := do
  let input ← IO.FS.readFile path
  match Primus.Lisp.evalString input with
  | .ok (value, _) => IO.println (Primus.Lisp.render value)
  | .error error => throw <| IO.userError error

private def analyze (path : String) : IO Unit := do
  let project ← Project.Project.load path
  let xrefs := Analysis.Xrefs.discover project
  let callgraph := Analysis.Callgraph.create xrefs
  let disasm := project.disasm.getD { entry := 0 }
  IO.println s!"instructions: {disasm.instructions.length}"
  IO.println s!"blocks: {disasm.blocks.length}"
  IO.println s!"errors: {disasm.errors.length}"
  IO.println s!"functions: {xrefs.functions.length}"
  IO.println s!"xrefs: {xrefs.xrefs.length}"
  IO.println s!"callgraph edges: {callgraph.graph.edges.length}"

/-- Runs a program in a virtual Linux, with the status of its first process as ours. It sees only what was copied in before it
started: itself, the libraries that it needs, from under `--root DIR` if they aren't of this machine, and each `--copy PATH`. -/
private def runProgram (args : List String) : IO Unit := do
  let rec split : List String → List String → List String → String → Bool → List String × List String × List String × String × Bool
    | "--copy" :: path :: rest, copies, environment, root, trace => split rest (path :: copies) environment root trace
    | "--env" :: entry :: rest, copies, environment, root, trace => split rest copies (entry :: environment) root trace
    | "--root" :: path :: rest, copies, environment, _, trace => split rest copies environment path trace
    | "--strace" :: rest, copies, environment, root, _ => split rest copies environment root true
    | rest, copies, environment, root, trace => (copies, rest, environment.reverse, root, trace)
  let (copies, command, environment, root, trace) := split args [] [] "" false
  let some path := command.head? | IO.println usage
  let mut kernel ← Linux.Kernel.empty.copyProgramFromHost path root
  for copy in copies do
    kernel ← kernel.copyFromHost copy
  let stderr ← IO.getStderr
  let watch : Option (Nat → List Nat → IO Unit) :=
    if trace then some fun number args => stderr.putStrLn s!"syscall {number} {args.take 4}" else none
  let machine ← Linux.start kernel path command environment (watch := watch)
  let stdout ← IO.getStdout
  match ← machine.run fun data => do
      stdout.write data
      stdout.flush with
  | .finished status =>
    IO.Process.exit (if status % 128 != 0 then 128 + (status % 128).toUInt8 else (status / 256).toUInt8)
  | outcome => throw <| IO.userError s!"the program didn't finish: {repr outcome} at {← Emu.pc machine.emu}"

private def symbolic (path : String) : IO Unit := do
  let program ← loadProgram path
  match Symbolic.run program with
  | .ok results => IO.println s!"paths: {results.length}"
  | .error error => throw <| IO.userError error

private def run (args : List String) : IO Unit := do
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
  | "run" :: args => runProgram args
  | ["symbolic", path] => symbolic path
  | "mc" :: atoms => mc (String.intercalate " " atoms)
  | _ => IO.println usage

/-- Runs the command. A process that is done doesn't need to free what it holds, such as all the instructions of a binary. -/
def main (args : List String) : IO Unit := do
  run args
  (← IO.getStdout).flush
  IO.Process.exit 0
