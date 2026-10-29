import Bap.Emu.Checkpoint

namespace Bap.Emu

private def hex (value : Nat) : String := String.ofList (Nat.toDigits 16 value)

private def byteHex (value : UInt8) : String :=
  let digits := hex value.toNat
  if digits.length < 2 then "0" ++ digits else digits

private def print (output : IO.FS.Stream) (text : String) : IO Unit :=
  output.putStr (text ++ "\n")

private def parseNat (input : String) : IO Nat := do
  if input.startsWith "0x" then
    match Bil.Wire.parseHex (input.drop 2).toString with
    | .ok value => pure value
    | .error error => throw <| IO.userError error
  else
    match input.toNat? with
    | some value => pure value
    | none => throw <| IO.userError s!"invalid number: {input}"

private def parseBytes (inputs : List String) : IO ByteArray := do
  let bytes ← inputs.mapM fun input => do
    let value ← match Bil.Wire.parseHex input with
      | .ok value => pure value
      | .error error => throw <| IO.userError error
    if value ≥ 256 then
      throw <| IO.userError s!"byte is out of range: {input}"
    else
      pure (UInt8.ofNat value)
  pure (ByteArray.mk bytes.toArray)

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
  match words with
  | [] | [""] => pure true
  | ["q"] | ["quit"] => pure false
  | ["help"] | ["?"] => print output shellHelp; pure true
  | ["pc"] => printPc emu output; pure true
  | ["regs"] =>
    let state ← emu.state.get
    let names := state.env.foldl (init := []) fun names binding =>
      if binding.1.typ matches Typ.mem _ _ || names.contains binding.1.name then names
      else binding.1.name :: names
    print output (String.intercalate " " names.reverse)
    pure true
  | ["reg", name] =>
    let value ← reg emu ⟨name, .imm 64, 0, false⟩
    print output s!"{name}={formatValue value}"
    pure true
  | ["set", name, value] =>
    let value ← parseNat value
    setReg emu ⟨name, .imm 64, 0, false⟩ (.bits (BitVec.ofNat 64 value))
    pure true
  | ["x", address] | ["x", address, "1"] =>
    let address ← parseNat address
    let bytes ← read emu address 1
    print output (String.intercalate " " (bytes.toList.map byteHex))
    pure true
  | ["x", address, size] =>
    let address ← parseNat address
    let size ← parseNat size
    let bytes ← read emu address size
    print output (String.intercalate " " (bytes.toList.map byteHex))
    pure true
  | "write" :: address :: bytes =>
    if bytes.isEmpty then
      throw <| IO.userError "write needs at least one byte"
    let address ← parseNat address
    write emu address (← parseBytes bytes)
    pure true
  | ["step"] | ["s"] =>
    resume emu
    let _ ← step emu
    printPc emu output
    pure true
  | ["continue"] | ["c"] =>
    resume emu
    let steps ← run emu
    print output s!"steps={steps}"
    printPc emu output
    pure true
  | ["continue", address] | ["c", address] =>
    let address ← parseNat address
    resume emu
    let steps ← runUntil emu address
    print output s!"steps={steps}"
    printPc emu output
    pure true
  | ["stop"] => stop emu; pure true
  | ["break", address] =>
    let address ← parseNat address
    let _ ← addBreakpoint emu address
    pure true
  | ["breaks"] =>
    let addresses ← breakpoints emu
    print output (String.intercalate " " (addresses.map hex))
    pure true
  | ["delete", address] =>
    removeBreakpoint emu (← parseNat address)
    pure true
  | ["snap"] => saved.set (some (← snapshot emu)); pure true
  | ["restore"] =>
    match ← saved.get with
    | some saved => restore emu saved; printPc emu output
    | none => throw <| IO.userError "no shell snapshot"
    pure true
  | ["save", path] => save emu path; pure true
  | command :: _ => throw <| IO.userError s!"unknown debugger command: {command}"

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
