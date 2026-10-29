import Bap.Emu
import Bap.Bil.Wire

namespace Bap.Emu

private def nat (value : Nat) : Sexp := .atom (toString value)
private def bool (value : Bool) : Sexp := .atom (toString value)
private def hex (value : Nat) : Sexp := .atom (String.ofList (Nat.toDigits 16 value))

private def boolValue (input : Sexp) : Except String Bool := do
  match ← Sexp.asAtom input with
  | "true" => .ok true
  | "false" => .ok false
  | _ => .error "invalid checkpoint boolean"

private def encodeTyp : Typ → Sexp
  | .unknown => .atom "unknown"
  | .unit => .atom "unit"
  | .mem addressWidth valueWidth => .tagged "mem" [nat addressWidth, nat valueWidth]
  | .imm width => .tagged "imm" [nat width]

private def decodeTyp (input : Sexp) : Except String Typ := do
  match input with
  | .atom "unknown" => .ok .unknown
  | .atom "unit" => .ok .unit
  | .list [.atom "imm", width] => .ok (.imm (← Sexp.nat width))
  | .list [.atom "mem", addressWidth, valueWidth] =>
    .ok (.mem (← Sexp.nat addressWidth) (← Sexp.nat valueWidth))
  | _ => .error "invalid checkpoint type"

private def encodeValue : Value → Sexp
  | @Value.bits width value => .tagged "bits" [nat width, hex value.toNat]
  | @Value.memory addressWidth memory => .tagged "memory" [nat addressWidth,
      .list (memory.cells.map fun cell => .tagged "cell" [hex cell.1.toNat, nat cell.2.toNat])]
  | .undefined => .atom "undefined"

private def decodeCells (width : Nat) (input : Sexp) : Except String (List (BitVec width × UInt8)) := do
  let inputs ← Sexp.asList input
  inputs.mapM fun input => do
    let args ← Sexp.expectTagged "cell" 2 input
    match args with
    | [address, value] =>
      let address ← Bil.Wire.parseHex (← Sexp.asAtom address)
      let value ← Sexp.nat value
      if value ≥ 256 then
        .error "checkpoint byte is out of range"
      else
        .ok (BitVec.ofNat width address, UInt8.ofNat value)
    | _ => .error "invalid checkpoint cell"

private def decodeValue (input : Sexp) : Except String Value := do
  match input with
  | .atom "undefined" => .ok .undefined
  | .list [.atom "bits", width, value] =>
    let width ← Sexp.nat width
    .ok (.bits (BitVec.ofNat width (← Bil.Wire.parseHex (← Sexp.asAtom value))))
  | .list [.atom "memory", width, cells] =>
    let width ← Sexp.nat width
    .ok (.memory (⟨← decodeCells width cells⟩))
  | _ => .error "invalid checkpoint value"

private def encodeBinding (binding : Bap.Var × Value) : Sexp :=
  let (var, value) := binding
  .tagged "binding" [.atom var.name, encodeTyp var.typ, nat var.index, bool var.isVirtual, encodeValue value]

private def decodeBinding (input : Sexp) : Except String (Bap.Var × Value) := do
  let args ← Sexp.expectTagged "binding" 5 input
  match args with
  | [name, typ, index, isVirtual, value] =>
    let name ← Sexp.asAtom name
    let typ ← decodeTyp typ
    let index ← Sexp.nat index
    let isVirtual ← boolValue isVirtual
    let value ← decodeValue value
    .ok (⟨name, typ, index, isVirtual⟩, value)
  | _ => .error "invalid checkpoint binding"

private def encodeRegion (region : Region) : Sexp :=
  .tagged "region" [
    nat region.address,
    bool region.protection.readable,
    bool region.protection.writable,
    bool region.protection.executable,
    .list (region.data.toList.map fun byte => nat byte.toNat)
  ]

private def decodeRegion (input : Sexp) : Except String Region := do
  let args ← Sexp.expectTagged "region" 5 input
  match args with
  | [address, readable, writable, executable, data] =>
    let address ← Sexp.nat address
    let readable ← boolValue readable
    let writable ← boolValue writable
    let executable ← boolValue executable
    let bytes ← (← Sexp.asList data).mapM fun byte => Sexp.nat byte
    if bytes.any fun byte => byte ≥ 256 then
      .error "checkpoint region byte is out of range"
    else
      .ok ⟨address, ByteArray.mk (bytes.map UInt8.ofNat).toArray, ⟨readable, writable, executable⟩⟩
  | _ => .error "invalid checkpoint region"

private def encodePending : Option PendingBranch → Sexp
  | none => .atom "none"
  | some pending => .tagged "pending" [nat pending.branch, nat pending.target]

private def decodePending (input : Sexp) : Except String (Option PendingBranch) := do
  match input with
  | .atom "none" => .ok none
  | _ =>
    let args ← Sexp.expectTagged "pending" 2 input
    match args with
    | [branch, target] => .ok (some ⟨← Sexp.nat branch, ← Sexp.nat target⟩)
    | _ => .error "invalid checkpoint pending branch"

private def encodeThread (context : ThreadContext) : Sexp :=
  .tagged "thread" [
    nat context.id,
    nat context.pc,
    bool context.stopped,
    .list (context.state.env.map encodeBinding),
    encodePending context.pending
  ]

private def decodeThread (input : Sexp) : Except String ThreadContext := do
  let args ← Sexp.expectTagged "thread" 5 input
  match args with
  | [id, pc, stopped, env, pending] =>
    let id ← Sexp.nat id
    let pc ← Sexp.nat pc
    let stopped ← boolValue stopped
    let env ← (← Sexp.asList env).mapM decodeBinding
    let pending ← decodePending pending
    .ok ⟨id, { env := env }, pc, stopped, pending⟩
  | _ => .error "invalid checkpoint thread"

def encodeSnapshot (snapshot : Snapshot) : Sexp :=
  .tagged "snapshot" [
    nat snapshot.pc,
    bool snapshot.stopped,
    .list (snapshot.regions.map encodeRegion),
    .list (snapshot.state.env.map encodeBinding),
    .list (snapshot.threads.map encodeThread),
    nat snapshot.currentThread,
    nat snapshot.nextThread,
    encodePending snapshot.pending
  ]

def decodeSnapshot (input : Sexp) : Except String Snapshot := do
  let args ← Sexp.expectTagged "snapshot" 8 input
  match args with
  | [pc, stopped, regions, env, threads, currentThread, nextThread, pending] =>
    let pc ← Sexp.nat pc
    let stopped ← boolValue stopped
    let regions ← (← Sexp.asList regions).mapM decodeRegion
    let env ← (← Sexp.asList env).mapM decodeBinding
    let threads ← (← Sexp.asList threads).mapM decodeThread
    let currentThread ← Sexp.nat currentThread
    let nextThread ← Sexp.nat nextThread
    let pending ← decodePending pending
    .ok ⟨{ env := env }, pc, regions, stopped, threads, currentThread, nextThread, pending⟩
  | _ => .error "invalid checkpoint snapshot"

def save (emu : Emu) (path : String) : IO Unit := do
  let snapshot ← snapshot emu
  IO.FS.writeFile path (toString (encodeSnapshot snapshot))

def load (emu : Emu) (path : String) : IO Unit := do
  let input ← IO.FS.readFile path
  match Sexp.parse input with
  | .error error => throw <| IO.userError error
  | .ok input =>
    match decodeSnapshot input with
    | .error error => throw <| IO.userError error
    | .ok snapshot => restore emu snapshot

end Bap.Emu
