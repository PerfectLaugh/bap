import Bap.Emu.Checkpoint

namespace Bap.Emu

private def hex (value : Nat) : String := String.ofList (Nat.toDigits 16 value)

private def byteHex (value : UInt8) : String :=
  let digits := hex value.toNat
  if digits.length < 2 then "0" ++ digits else digits

private def print (output : IO.FS.Stream) (text : String) : IO Unit :=
  output.putStr (text ++ "\n")

/-- A number of the debugger: decimal, or hexadecimal after `0x`. -/
def parseNumber (input : String) : Except String Nat :=
  match input.toList with
  | '0' :: 'x' :: digits => Bil.Wire.parseHex (String.ofList digits)
  | _ =>
    match input.toNat? with
    | some value => .ok value
    | none => .error s!"invalid number: {input}"

/-- A byte of the debugger, always in hexadecimal. -/
def parseByte (input : String) : Except String UInt8 := do
  let value ← Bil.Wire.parseHex input
  if value ≥ 256 then .error s!"byte is out of range: {input}"
  else .ok (UInt8.ofNat value)

inductive Command where
  | nothing
  | quit
  | help
  | pc
  | regs
  | reg (name : String)
  | set (name : String) (value : Nat)
  | examine (address size : Nat)
  | write (address : Nat) (bytes : List UInt8)
  | step
  | proceed
  | proceedTo (address : Nat)
  | stop
  | breakAt (address : Nat)
  | breaks
  | delete (address : Nat)
  | snap
  | restore
  | save (path : String)
  deriving DecidableEq, Repr

/-- The words of a line of the debugger, which `parseCommand` reads. -/
def parseCommand : List String → Except String Command
  | [] | [""] => .ok .nothing
  | ["q"] | ["quit"] => .ok .quit
  | ["help"] | ["?"] => .ok .help
  | ["pc"] => .ok .pc
  | ["regs"] => .ok .regs
  | ["reg", name] => .ok (.reg name)
  | ["set", name, value] => do .ok (.set name (← parseNumber value))
  | ["x", address] => do .ok (.examine (← parseNumber address) 1)
  | ["x", address, size] => do .ok (.examine (← parseNumber address) (← parseNumber size))
  | "write" :: address :: bytes =>
    if bytes.isEmpty then .error "write needs at least one byte"
    else do .ok (.write (← parseNumber address) (← bytes.mapM parseByte))
  | ["step"] | ["s"] => .ok .step
  | ["continue"] | ["c"] => .ok .proceed
  | ["continue", address] | ["c", address] => do .ok (.proceedTo (← parseNumber address))
  | ["stop"] => .ok .stop
  | ["break", address] => do .ok (.breakAt (← parseNumber address))
  | ["breaks"] => .ok .breaks
  | ["delete", address] => do .ok (.delete (← parseNumber address))
  | ["snap"] => .ok .snap
  | ["restore"] => .ok .restore
  | ["save", path] => .ok (.save path)
  | command :: _ => .error s!"unknown debugger command: {command}"

def isMemoryType : Typ → Bool
  | .mem _ _ => true
  | _ => false

/-- The variable of a register of the debugger: the one in the environment, whatever its width, or else a
new one of the width of a word. -/
def registerVar (env : Bil.Env) (width : Nat) (name : String) : Bap.Var :=
  match env.find? fun binding => binding.1.name == name && !isMemoryType binding.1.typ with
  | some binding => binding.1
  | none => ⟨name, .imm width, 0, false⟩

/-- The value of a register, unless it does not fit. -/
def registerValue (var : Bap.Var) (value : Nat) : Except String Value :=
  match var.typ with
  | .imm width =>
    if value < 2 ^ width then .ok (.bits (BitVec.ofNat width value))
    else .error s!"value {value} does not fit register {var.name}"
  | _ => .error s!"{var.name} is not a register"

/-- The names of the registers, in order of their first appearance. -/
def registerNames (env : Bil.Env) : List String :=
  (env.foldl (init := []) fun names binding =>
    if isMemoryType binding.1.typ || names.contains binding.1.name then names
    else binding.1.name :: names).reverse

private def formatValue (value : Value) : String :=
  match Value.asBits value with
  | .ok ⟨width, value⟩ => s!"{width}:0x{hex value.toNat}"
  | .error _ => (repr value).pretty

private def printPc (emu : Emu) (output : IO.FS.Stream) : IO Unit := do
  let address ← pc emu
  print output s!"PC=0x{hex address}"

private def shellHelp : String :=
  "help pc regs reg NAME set NAME VALUE x ADDR [SIZE] write ADDR BYTES... " ++
  "step continue [ADDR] stop break ADDR breaks delete ADDR snap restore save PATH q"

private def execute (emu : Emu) (output : IO.FS.Stream) (saved : IO.Ref (Option Snapshot))
    (words : List String) : IO Bool := do
  let width ← match emu.config.memory.typ with
    | .mem width _ => pure width
    | _ => pure 64
  match ← IO.ofExcept (parseCommand words) with
  | .nothing => pure true
  | .quit => pure false
  | .help => print output shellHelp; pure true
  | .pc => printPc emu output; pure true
  | .regs =>
    let state ← emu.state.get
    print output (String.intercalate " " (registerNames state.env))
    pure true
  | .reg name =>
    let state ← emu.state.get
    let value ← Bap.Emu.reg emu (registerVar state.env width name)
    print output s!"{name}={formatValue value}"
    pure true
  | .set name value =>
    let state ← emu.state.get
    let var := registerVar state.env width name
    setReg emu var (← IO.ofExcept (registerValue var value))
    pure true
  | .examine address size =>
    let bytes ← read emu address size
    print output (String.intercalate " " (bytes.toList.map byteHex))
    pure true
  | .write address bytes =>
    Bap.Emu.write emu address (ByteArray.mk bytes.toArray)
    pure true
  | .step =>
    resume emu
    let _ ← Bap.Emu.step emu
    printPc emu output
    pure true
  | .proceed =>
    resume emu
    let steps ← run emu
    print output s!"steps={steps}"
    printPc emu output
    pure true
  | .proceedTo address =>
    resume emu
    let steps ← runUntil emu address
    print output s!"steps={steps}"
    printPc emu output
    pure true
  | .stop => Bap.Emu.stop emu; pure true
  | .breakAt address =>
    let _ ← addBreakpoint emu address
    pure true
  | .breaks =>
    let addresses ← breakpoints emu
    print output (String.intercalate " " (addresses.map hex))
    pure true
  | .delete address =>
    removeBreakpoint emu address
    pure true
  | .snap => saved.set (some (← snapshot emu)); pure true
  | .restore =>
    match ← saved.get with
    | some saved => Bap.Emu.restore emu saved; printPc emu output
    | none => throw <| IO.userError "no shell snapshot"
    pure true
  | .save path => Bap.Emu.save emu path; pure true

def shell (emu : Emu) (input output : IO.FS.Stream) (prompt : String := "(emu) ")
    (fuel : Nat := 100000) : IO Unit := do
  let saved ← IO.mkRef none
  let rec loop : Nat → IO Unit
    | 0 => throw <| IO.userError "Emu debugger command fuel exhausted"
    | fuel + 1 => do
      output.putStr prompt
      output.flush
      let line ← input.getLine
      if line.isEmpty then
        pure ()
      else
        let words := ((String.trimAscii line).copy.splitOn " ").filter fun word => !word.isEmpty
        let proceed ← try
          execute emu output saved words
        catch error =>
          print output s!"error: {error}"
          pure true
        if proceed then loop fuel else pure ()
  loop fuel

def shellStdio (emu : Emu) : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  shell emu input output

end Bap.Emu
