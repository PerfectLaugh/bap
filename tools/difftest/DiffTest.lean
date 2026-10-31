import Bap.Float
import Bap.Target.LLVMLift

/-! # The lifter's side of the differential test

Reads requests on the standard input and answers each on the standard output, one line each, see `tools/difftest/difftest.py`.
All numbers are in hexadecimal, values as many digits as their width takes.

- `T target` picks the target: its semantics and its decoder.
- `V name:width ...` names the registers of the following runs, in order.
- `W address size bits`: where the window of memory is, its size, and the width of an address.
- `C id address bytes` decodes an instruction, which is also in the memory of its runs, and answers `D id opcode size intrinsic control assembly` or `E id message`.
- `S` prints the program of the last instruction, on stderr.
- `R index window value ...` runs it from these registers and answers
  `O index effect value ... window` or `X index message`. The effect is `n`, `j` and the target, `s` or `c` and the number. -/

namespace Bap.DiffTest

open Bap

private def hexDigit (value : Nat) : Char :=
  if value < 10 then Char.ofNat (48 + value) else Char.ofNat (87 + value)

/-- The `count` digits of a number, most significant first. -/
private def hexOf (value count : Nat) : String :=
  String.ofList ((List.range count).reverse.map fun index => hexDigit (value / 16 ^ index % 16))

private def digitOf (char : Char) : Nat :=
  if char.isDigit then char.toNat - 48 else if 'a' ≤ char ∧ char ≤ 'f' then char.toNat - 87 else char.toNat - 55

private def parseHex (input : String) : Nat :=
  input.foldl (fun value char => value * 16 + digitOf char) 0

/-- The bytes of pairs of digits. -/
private def bytesOf (input : String) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  let mut high : Option Nat := none
  for char in input.toList do
    match high with
    | none => high := some (digitOf char)
    | some value =>
      result := result.push (UInt8.ofNat (value * 16 + digitOf char))
      high := none
  return result

private def hexBytes (bytes : ByteArray) : String := Id.run do
  let mut result := ""
  for byte in bytes do
    result := (result.push (hexDigit (byte.toNat / 16))).push (hexDigit (byte.toNat % 16))
  return result

structure Target where
  triple : String
  decode : Nat → ByteArray → IO Disasm.Insn

private def targetOf : String → IO Target
  | "x86_64" => do
    let env ← Target.LLVMLift.x86Environment
    pure ⟨"x86_64", fun address data => Target.LLVMLift.decodeX86With env address address data⟩
  | "i686" => do
    let env ← Target.LLVMLift.x8632Environment
    pure ⟨"i386", fun address data => Target.LLVMLift.decodeX8632With env address address data⟩
  | "aarch64" => do
    let env ← Target.LLVMLift.aarch64Environment
    pure ⟨"aarch64", fun address data => Target.LLVMLift.decodeAArch64With env address address data⟩
  | "arm" => do
    let env ← Target.LLVMLift.arm32Environment
    pure ⟨"armv7", fun address data => Target.LLVMLift.decodeARM32With env address address data⟩
  | "thumb" => do
    let env ← Target.LLVMLift.thumbEnvironment
    pure ⟨"thumbv7", fun address data => Target.LLVMLift.decodeThumbWith env address address data⟩
  | "riscv64" => do
    let env ← Target.LLVMLift.riscvEnvironment
    pure ⟨"riscv64", fun address data => Target.LLVMLift.decodeRISCVWith env address address data⟩
  | "riscv32" => do
    let env ← Target.LLVMLift.riscv32Environment
    pure ⟨"riscv32", fun address data => Target.LLVMLift.decodeRISCV32With env address address data⟩
  | "ppc64le" => powerpc { bits := 64, endian := .little }
  | "ppc64" => powerpc { bits := 64, endian := .big }
  | "ppc" => powerpc { bits := 32, endian := .big }
  | "mips" => mips { bits := 32, endian := .big }
  | "mipsel" => mips { bits := 32, endian := .little }
  | "mips64" => mips { bits := 64, endian := .big }
  | "mips64el" => mips { bits := 64, endian := .little }
  | "mipsr6" => mips { bits := 32, endian := .big, release6 := true }
  | "mips64r6" => mips { bits := 64, endian := .big, release6 := true }
  | name => throw <| IO.userError s!"no target {name}"
where
  powerpc (variant : Target.LLVMLift.PowerPCVariant) : IO Target := do
    let env ← Target.LLVMLift.powerpcEnvironmentOf variant
    pure ⟨variant.triple, fun address data => Target.LLVMLift.decodePowerPCOf variant env address address data⟩
  mips (variant : Target.LLVMLift.MipsVariant) : IO Target := do
    let env ← Target.LLVMLift.mipsEnvironmentOf variant
    pure ⟨variant.triple, fun address data => Target.LLVMLift.decodeMIPSOf variant env address address data⟩

private def varOf (spec : String) : Bap.Var :=
  match spec.splitOn ":" with
  | [name, width] => ⟨name, .imm (parseHex width), 0, false⟩
  | _ => ⟨spec, .imm 64, 0, false⟩

private def widthOf (var : Bap.Var) : Nat :=
  match var.typ with
  | .imm width => width
  | _ => 0

/-- The window of memory with these bytes. -/
private def memoryOf (bits base : Nat) (bytes : ByteArray) (memory : Memory bits := Memory.empty bits) : Memory bits := Id.run do
  let mut memory := memory
  for offset in [0:bytes.size] do
    memory := Memory.writeByte memory (BitVec.ofNat bits (base + offset)) bytes[offset]!
  return memory

private def windowOf {bits : Nat} (memory : Memory bits) (base size : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for offset in [0:size] do
    result := result.push (Memory.readByte memory (BitVec.ofNat bits (base + offset)))
  return result

private def effectText : Bil.Effect → String
  | .normal => "n"
  | .jump target => s!"j{hexOf target.toNat ((target.toNat.log2 + 4) / 4)}"
  | .special _ => "s"
  | .cpuExn number => s!"c{number}"

structure Window where
  base : Nat := 0
  size : Nat := 0
  bits : Nat := 64

/-- Whether a program calls an intrinsic of floating point, to this depth of branches, or one of anything else. -/
private def specialsOf : Nat → Bil.Program → List String
  | 0, _ => []
  | fuel + 1, program => program.flatMap fun stmt =>
    match stmt with
    | .special name => [name]
    | .ifElse _ yes no => specialsOf fuel yes ++ specialsOf fuel no
    | .while _ body => specialsOf fuel body
    | _ => []

/-- A program with each intrinsic of floating point served where it is, by `Bap.Float`, as the Linux machine does. -/
private def runServed (rules : Bap.Float.NaNRules) (state : Bil.State) (program : Bil.Program) :
    Except String (Bil.State × Bil.Effect) :=
  let rec go : Nat → Bil.State → List Nat → Bil.Program → Except String (Bil.State × List Nat × Bil.Effect)
    | 0, _, _, _ => .error "out of fuel"
    | _ + 1, state, operands, [] => .ok (state, operands, .normal)
    | fuel + 1, state, operands, stmt :: rest => do
      match stmt with
      | .move var value =>
        let value ← Bil.evalExp state.env value
        let operands ← if var.name.startsWith "intrinsic:x" then do
            let bits ← Value.asBits value
            pure (operands ++ [bits.2.toNat])
          else pure operands
        go fuel { env := Bil.bind state.env var value } operands rest
      | .special name =>
        match Bap.Float.evaluateWith rules name operands with
        | some (width, bits) =>
          go fuel { env := Bil.bind state.env ⟨"intrinsic:y0", .imm width, 0, false⟩ (.bits (BitVec.ofNat width bits)) } [] rest
        | none => .ok (state, [], .special name)
      | .ifElse condition yes no =>
        let bits ← Value.asBits (← Bil.evalExp state.env condition)
        let (state, operands, effect) ← go fuel state operands (if bits.2.toNat != 0 then yes else no)
        match effect with
        | .normal => go fuel state operands rest
        | other => .ok (state, operands, other)
      | .while condition body =>
        let bits ← Value.asBits (← Bil.evalExp state.env condition)
        if bits.2.toNat == 0 then go fuel state operands rest
        else
          let (state, operands, effect) ← go fuel state operands body
          match effect with
          | .normal => go fuel state operands (stmt :: rest)
          | other => .ok (state, operands, other)
      | .jmp target =>
        let bits ← Value.asBits (← Bil.evalExp state.env target)
        .ok (state, operands, .jump (BitVec.ofNat bits.1 bits.2.toNat))
      | .cpuExn number => .ok (state, operands, .cpuExn number)
  (go 100000 state [] program).map fun result => (result.1, result.2.2)

private def runCase (rules : Bap.Float.NaNRules) (vars : List Bap.Var) (window : Window) (address : Nat) (code : ByteArray) (program : Bil.Program) (index : String)
    (memoryBytes : String) (values : List String) : String :=
  let memoryVar : Bap.Var := ⟨"mem", .mem window.bits 8, 0, false⟩
  let memory := memoryOf window.bits window.base (bytesOf memoryBytes) (memoryOf window.bits address code)
  let env : Bil.Env := (memoryVar, .memory memory) ::
    (vars.zip values).map fun (var, value) => (var, .bits (BitVec.ofNat (widthOf var) (parseHex value)))
  let floats := (specialsOf 64 program).any Bap.Float.serves
  match (if floats then runServed rules { env := env } program else Bil.run program { env := env }) with
  | .error message => s!"X {index} {message}"
  | .ok (state, effect) =>
    let shown := vars.map fun var =>
      match Bil.lookup state.env var with
      | .ok (@Value.bits width value) =>
        if width = widthOf var then hexOf value.toNat ((width + 3) / 4) else s!"width{width}"
      | .ok _ => "?"
      | .error _ => "?"
    let memory :=
      match Bil.lookup state.env memoryVar with
      | .ok (.memory memory) => hexBytes (windowOf memory window.base window.size)
      | _ => "?"
    s!"O {index} {effectText effect} {String.intercalate " " shown} {memory}"

private def serve (stdin stdout stderr : IO.FS.Stream) : IO Unit := do
  let mut target : Option Target := none
  let mut rulesNow := Bap.Float.NaNRules.x86
  let mut vars : List Bap.Var := []
  let mut window : Window := {}
  let mut current : Option Disasm.Insn := none
  let mut codeAddress := 0
  let mut code := ByteArray.empty
  repeat
    let line ← stdin.getLine
    if line.isEmpty then
      break
    match (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty) with
    | ["T", name] =>
      target := some (← targetOf name)
      rulesNow := match name.take 3 |>.toString with
        | "x86" | "i68" => .x86
        | "aar" | "arm" | "thu" => .arm
        | "ris" => .riscv
        | "mip" => if (name.splitOn "r6").length > 1 then .powerpc else .mips
        | _ => .powerpc
      current := none
    | "V" :: specs => vars := specs.map varOf
    | ["W", base, size, bits] => window := ⟨parseHex base, parseHex size, parseHex bits⟩
    | ["C", id, address, data] =>
      match target with
      | none => throw <| IO.userError "no target"
      | some chosen =>
        let bytes := bytesOf data
        let address := parseHex address
        try
          let insn ← chosen.decode address bytes
          let decoded ← LLVM.disassemble chosen.triple bytes address
          -- An intrinsic of floating point has a value, which `Bap.Float` computes, and any other has none.
          let specials := specialsOf 64 insn.bil
          let served := !specials.isEmpty && specials.all Bap.Float.serves
          let intrinsic := !served && ((reprStr insn.bil).splitOn "intrinsic:").length > 1
          stdout.putStrLn s!"D {id} {decoded.opcode} {hexOf insn.size 2} {if intrinsic then 1 else 0} {if insn.flow == .normal then 0 else 1} {insn.asm}"
          current := some insn
          codeAddress := address
          code := bytes
        catch error =>
          let text := (toString error).replace "\n" " "
          stdout.putStrLn s!"E {id} {text}"
          current := none
    | ["S"] =>
      if let some insn := current then
        stderr.putStrLn (reprStr insn.bil)
    | "R" :: index :: memoryBytes :: values =>
      match current with
      | none => stdout.putStrLn s!"X {index} not decoded"
      | some insn => stdout.putStrLn (runCase rulesNow vars window codeAddress code insn.bil index memoryBytes values)
    | [] => stdout.flush
    | _ => throw <| IO.userError s!"bad request: {line}"

end Bap.DiffTest

def main : IO Unit := do
  Bap.DiffTest.serve (← IO.getStdin) (← IO.getStdout) (← IO.getStderr)
  (← IO.getStdout).flush
  IO.Process.exit 0
