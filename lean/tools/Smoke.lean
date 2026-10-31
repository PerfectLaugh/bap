import Bap.Target.LLVMLift

/-! The smoke test of the lifters: which opcodes of LLVM an encoding reaches, and whether each lifts.

`bap-smoke TARGET FILE [SAMPLES]` reads the encodings of `FILE`, one in hex on a line, decodes each, and lifts up to `SAMPLES`
of each opcode. It prints a line `OPCODE lifted failed encoding error` for each opcode that it reached, with the first
encoding that failed and its error, and lines `# ...` of totals. `tools/smoke.py` makes the encodings and reads this. -/

open Bap

namespace Bap.Tools.Smoke

/-- A target: the triple of its decoder and what lifts an instruction at an address. -/
structure Target where
  triple : String
  lift : Nat → ByteArray → IO Disasm.Insn

/-- The targets by the names that `tools/smoke.py` has for them. -/
def targets : List (String × Target) := [
  ("x86_64", ⟨"x86_64", Bap.Target.LLVMLift.decodeX86 0x1000⟩),
  ("i386", ⟨"i386", Bap.Target.LLVMLift.decodeX8632 0x1000⟩),
  ("aarch64", ⟨"aarch64", Bap.Target.LLVMLift.decodeAArch64 0x1000⟩),
  ("riscv64", ⟨"riscv64", Bap.Target.LLVMLift.decodeRISCV 0x1000⟩),
  ("riscv32", ⟨"riscv32", Bap.Target.LLVMLift.decodeRISCV32 0x1000⟩),
  ("powerpc64le", ⟨"powerpc64le", Bap.Target.LLVMLift.decodePowerPC 0x1000⟩),
  ("powerpc", ⟨"powerpc", Bap.Target.LLVMLift.decodePowerPC32 0x1000⟩),
  ("mips64", ⟨"mips64", Bap.Target.LLVMLift.decodeMIPS 0x1000⟩),
  ("mips", ⟨"mips", Bap.Target.LLVMLift.decodeMIPS32 0x1000⟩),
  ("armv7", ⟨"armv7", Bap.Target.LLVMLift.decodeARM32 0x1000⟩),
  ("thumbv7", ⟨"thumbv7", Bap.Target.LLVMLift.decodeThumb 0x1000⟩)]

/-- What is known of an opcode. -/
structure Tally where
  lifted : Nat := 0
  failed : Nat := 0
  encoding : String := ""
  error : String := ""

def hexDigit? (char : Char) : Option UInt8 :=
  if '0' ≤ char ∧ char ≤ '9' then some (char.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ char ∧ char ≤ 'f' then some (char.toNat - 'a'.toNat + 10).toUInt8
  else none

/-- The bytes of a line of hex. -/
def parseHex (line : String) : Option ByteArray :=
  let rec go : List Char → ByteArray → Option ByteArray
    | [], out => some out
    | high :: low :: rest, out =>
      match hexDigit? high, hexDigit? low with
      | some high, some low => go rest (out.push (high * 16 + low))
      | _, _ => none
    | [_], _ => none
  go line.toList ByteArray.empty

/-- The first line of an error, which is all that goes on a line of the report. -/
def firstLine (text : String) : String :=
  (((text.splitOn "\n").headD "").replace "\t" " ").take 300 |>.toString

/-- What the decoder has for each of the encodings, and the first statements of what it lifts to or its error. -/
def showEncodings (target : Target) (encodings : List String) : IO Unit := do
  for encoding in encodings do
    let some data := parseHex encoding | throw <| IO.userError s!"{encoding} is not hex"
    let decoded ← match (← (LLVM.disassemble target.triple data 0x1000).toBaseIO) with
      | .ok decoded => pure decoded
      | .error _ =>
        IO.println s!"{encoding}\t0\tundecoded\t\t"
        continue
    let result ← (target.lift 0x1000 data).toBaseIO
    let lifted := match result with
      | .ok insn => s!"{insn.bil.length} statements"
      | .error error => firstLine (toString error)
    IO.println s!"{encoding}\t{decoded.size}\t{decoded.opcode}\t{(decoded.assembly.replace "\t" " ")}\t{lifted}"

def main (args : List String) : IO UInt32 := do
  if let name :: "--show" :: encodings := args then
    let some target := targets.lookup name
      | throw <| IO.userError s!"no target {name}"
    showEncodings target encodings
    return 0
  let (name, path, samples) ← match args with
    | [name, path] => pure (name, path, 4)
    | [name, path, samples] => pure (name, path, samples.toNat!)
    | _ => throw <| IO.userError "usage: bap-smoke TARGET FILE [SAMPLES]"
  let some target := targets.lookup name
    | throw <| IO.userError s!"no target {name}"
  let mut tallies : Std.HashMap String Tally := {}
  let mut undecoded := 0
  let mut lines := 0
  let handle ← IO.FS.Handle.mk path .read
  repeat
    let line ← handle.getLine
    if line.isEmpty then break
    let some data := parseHex line.trimAscii.toString | continue
    lines := lines + 1
    match (← (LLVM.disassemble target.triple data 0x1000).toBaseIO) with
    | .error _ => undecoded := undecoded + 1
    | .ok decoded =>
      let tally := tallies.getD decoded.opcode {}
      if tally.lifted + tally.failed < samples then
        let tally ← match (← (target.lift 0x1000 data).toBaseIO) with
          | .ok _ => pure { tally with lifted := tally.lifted + 1 }
          | .error error =>
            pure (if tally.failed = 0 then
              { tally with failed := 1, encoding := line.trimAscii.toString, error := firstLine (toString error) }
            else { tally with failed := tally.failed + 1 })
        tallies := tallies.insert decoded.opcode tally
      else if tally.lifted + tally.failed = 0 then
        tallies := tallies.insert decoded.opcode tally
  for (opcode, tally) in tallies.toList do
    IO.println s!"{opcode}\t{tally.lifted}\t{tally.failed}\t{tally.encoding}\t{tally.error}"
  IO.println s!"# lines {lines} undecoded {undecoded} opcodes {tallies.size}"
  return 0

end Bap.Tools.Smoke

def main (args : List String) : IO UInt32 := Bap.Tools.Smoke.main args
