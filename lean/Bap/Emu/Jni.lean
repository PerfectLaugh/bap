import Bap.Emu

namespace Bap.Emu.Jni

structure Call where
  index : Nat
  args : Array Nat
  deriving Repr

inductive Answer where
  | value (value : Nat)
  | object (identity : Nat)
  | string (contents : String)
  | handle (value : Nat)
  | fresh
  deriving Repr

inductive Identity where
  | external (value : Nat)
  | internal (value : Nat)
  deriving DecidableEq, Hashable, Repr

inductive RefKind where
  | local | global | weak
  deriving DecidableEq, Hashable

structure BindingKey where
  owner : Identity
  name : String
  signature : String
  static : Bool
  deriving DecidableEq, Hashable

structure MethodDecl where
  name : String
  signature : String
  answer : Call → IO Answer

structure FieldDecl where
  name : String
  signature : String
  value : Answer

structure ClassDecl where
  name : String
  methods : List MethodDecl := []
  staticMethods : List MethodDecl := []
  fields : List FieldDecl := []
  staticFields : List FieldDecl := []

structure ObjectDecl where
  identity : Nat
  className : String
  elements : List Answer := []

structure MethodInfo where
  decl : MethodDecl
  owner : Identity
  static : Bool

structure FieldInfo where
  decl : FieldDecl
  owner : Identity
  static : Bool

structure StringInfo where
  contents : String
  address : Option Nat := none

structure Layout where
  vm : Nat
  vmFunctions : Nat
  env : Nat
  envFunctions : Nat
  envStubs : Nat
  envDispatcher : Nat
  vmStubs : Nat
  vmDispatcher : Nat

structure Model where
  nextHandle : IO.Ref Nat
  nextIdentity : IO.Ref Nat
  handles : IO.Ref (Std.HashMap (RefKind × Identity) Nat)
  sources : IO.Ref (Std.HashMap Nat Identity)
  classes : IO.Ref (Std.HashMap String Identity)
  classNames : IO.Ref (Std.HashMap Identity String)
  objectClasses : IO.Ref (Std.HashMap Identity Identity)
  arrays : IO.Ref (Std.HashMap Identity (List Answer))
  methods : IO.Ref (Std.HashMap Identity MethodInfo)
  methodIds : IO.Ref (Std.HashMap BindingKey Identity)
  fields : IO.Ref (Std.HashMap Identity FieldInfo)
  fieldIds : IO.Ref (Std.HashMap BindingKey Identity)
  strings : IO.Ref (Std.HashMap Identity StringInfo)
  stringsByContent : IO.Ref (Std.HashMap String Identity)
  dynamicIds : IO.Ref (Std.HashMap (Nat × Identity × String × String) Nat)
  dynamicNames : IO.Ref (Std.HashMap Identity String)
  nextDynamic : IO.Ref Nat
  readString : Nat → IO String
  allocString : String → IO Nat
  classOf : Nat → Option String
  default : Call → (Nat → IO (Option String)) → IO Answer
  log : Call → String → Nat → IO Unit
  version : Nat := 0x10006
  env : IO.Ref Nat
  vm : IO.Ref Nat

def arg (call : Call) (index : Nat) : Nat := call.args.getD index 0

private def reg (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩

private def readReg (emu : Emu) (name : String) : IO Nat := do
  match Value.asBits (← Bap.Emu.reg emu (reg name)) with
  | .ok value => pure value.2.toNat
  | .error error => throw <| IO.userError error

private def writeReg (emu : Emu) (name : String) (value : Nat) : IO Unit :=
  Bap.Emu.setReg emu (reg name) (.bits (BitVec.ofNat 64 value))

private def word (value : Nat) : ByteArray :=
  ByteArray.mk ((List.range 8).map fun index => UInt8.ofNat (value / 256 ^ index % 256)).toArray

private def writeWord (emu : Emu) (address value : Nat) : IO Unit :=
  Bap.Emu.write emu address (word value)

def readCString (emu : Emu) (address : Nat) : IO String := do
  if address < 0x10000 then pure "" else
    let rec loop (offset : Nat) (bytes : ByteArray) : IO ByteArray := do
      if offset ≥ 4096 then pure bytes else
        let byte ← Bap.Emu.read emu (address + offset) 1
        if byte[0]! = 0 then pure bytes else loop (offset + 1) (bytes.push byte[0]!)
    pure (String.fromUTF8! (← loop 0 ByteArray.empty))

private def freshIdentity (model : Model) : IO Identity := do
  let id ← model.nextIdentity.get
  model.nextIdentity.set (id + 1)
  pure (.internal id)

def resolve (model : Model) (handle : Nat) : IO Identity := do
  pure ((← model.sources.get).get? handle |>.getD (.external handle))

def internIdentity (model : Model) (kind : RefKind) (identity : Identity) : IO Nat := do
  if identity = .external 0 then pure 0 else
    let handles ← model.handles.get
    match handles.get? (kind, identity) with
    | some handle => pure handle
    | none =>
      let handle ← model.nextHandle.get
      model.nextHandle.set (handle + 0x10)
      model.handles.set (handles.insert (kind, identity) handle)
      model.sources.modify (·.insert handle identity)
      pure handle

def intern (model : Model) (identity : Nat) : IO Nat :=
  internIdentity model .local (.external identity)

def identity (model : Model) (handle : Nat) : IO (Option Nat) := do
  match (← model.sources.get).get? handle with
  | some (.external id) => pure (some id)
  | _ => pure none

private def classIdentity (model : Model) (name : String) : IO Identity := do
  match (← model.classes.get).get? name with
  | some id => pure id
  | none =>
    let id ← freshIdentity model
    model.classes.modify (·.insert name id)
    model.classNames.modify (·.insert id name)
    pure id

private def stringIdentity (model : Model) (contents : String) (fresh : Bool := false) : IO Identity := do
  let existing ← if fresh then pure none else pure ((← model.stringsByContent.get).get? contents)
  match existing with
  | some id => pure id
  | none =>
    let id ← freshIdentity model
    model.strings.modify (·.insert id ⟨contents, none⟩)
    if !fresh then model.stringsByContent.modify (·.insert contents id)
    pure id

private def answer (model : Model) : Answer → IO Nat
  | .value value => pure value
  | .object id => intern model id
  | .string contents => stringIdentity model contents >>= internIdentity model .local
  | .handle handle => pure handle
  | .fresh => freshIdentity model >>= internIdentity model .local

private def registerClass (model : Model) (decl : ClassDecl) : IO Unit := do
  let owner ← classIdentity model decl.name
  for method in decl.methods do
    let id ← freshIdentity model
    model.methods.modify (·.insert id ⟨method, owner, false⟩)
    model.methodIds.modify (·.insert ⟨owner, method.name, method.signature, false⟩ id)
  for method in decl.staticMethods do
    let id ← freshIdentity model
    model.methods.modify (·.insert id ⟨method, owner, true⟩)
    model.methodIds.modify (·.insert ⟨owner, method.name, method.signature, true⟩ id)
  for field in decl.fields do
    let id ← freshIdentity model
    model.fields.modify (·.insert id ⟨field, owner, false⟩)
    model.fieldIds.modify (·.insert ⟨owner, field.name, field.signature, false⟩ id)
  for field in decl.staticFields do
    let id ← freshIdentity model
    model.fields.modify (·.insert id ⟨field, owner, true⟩)
    model.fieldIds.modify (·.insert ⟨owner, field.name, field.signature, true⟩ id)

def create (readString : Nat → IO String) (allocString : String → IO Nat)
    (default : Call → (Nat → IO (Option String)) → IO Answer)
    (log : Call → String → Nat → IO Unit := fun _ _ _ => pure ())
    (classes : List ClassDecl := []) (objects : List ObjectDecl := [])
    (classOf : Nat → Option String := fun _ => none)
    (firstHandle : Nat := 0x52030000) (version : Nat := 0x10006) : IO Model := do
  let model : Model := {
    nextHandle := ← IO.mkRef firstHandle
    nextIdentity := ← IO.mkRef 0
    handles := ← IO.mkRef {}
    sources := ← IO.mkRef {}
    classes := ← IO.mkRef {}
    classNames := ← IO.mkRef {}
    objectClasses := ← IO.mkRef {}
    arrays := ← IO.mkRef {}
    methods := ← IO.mkRef {}
    methodIds := ← IO.mkRef {}
    fields := ← IO.mkRef {}
    fieldIds := ← IO.mkRef {}
    strings := ← IO.mkRef {}
    stringsByContent := ← IO.mkRef {}
    dynamicIds := ← IO.mkRef {}
    dynamicNames := ← IO.mkRef {}
    nextDynamic := ← IO.mkRef 0x10000
    readString, allocString, classOf, default, log, version
    env := ← IO.mkRef 0
    vm := ← IO.mkRef 0
  }
  classes.forM (registerClass model)
  for object in objects do
    let classId ← classIdentity model object.className
    model.objectClasses.modify (·.insert (.external object.identity) classId)
    model.arrays.modify (·.insert (.external object.identity) object.elements)
  pure model

def dynamicName (model : Model) (handle : Nat) : IO (Option String) := do
  let id ← resolve model handle
  pure ((← model.dynamicNames.get).get? id)

private def dynamicBinding (model : Model) (call : Call) : IO Nat := do
  let owner ← resolve model (arg call 1)
  let name ← model.readString (arg call 2)
  let signature ← model.readString (arg call 3)
  let key := (call.index, owner, name, signature)
  let id ← match (← model.dynamicIds.get).get? key with
    | some id => pure id
    | none =>
      let id ← model.nextDynamic.get
      model.nextDynamic.set (id + 1)
      model.dynamicIds.modify (·.insert key id)
      model.dynamicNames.modify (·.insert (.external id) name)
      pure id
  intern model id

private def callMethod (model : Model) (call : Call) (static : Bool) (handle : Nat) : IO Nat := do
  let methodId ← resolve model handle
  match (← model.methods.get).get? methodId with
  | some info =>
    if info.static = static then answer model (← info.decl.answer call)
    else answer model (← model.default call (dynamicName model))
  | none => answer model (← model.default call (dynamicName model))

private def getField (model : Model) (call : Call) (static : Bool) (handle : Nat) : IO Nat := do
  let fieldId ← resolve model handle
  match (← model.fields.get).get? fieldId with
  | some info =>
    if info.static = static then answer model info.decl.value
    else answer model (← model.default call (dynamicName model))
  | none => answer model (← model.default call (dynamicName model))

private def getObjectClass (model : Model) (handle : Nat) : IO Nat := do
  let objectId ← resolve model handle
  let classId ← match (← model.objectClasses.get).get? objectId with
    | some id => pure id
    | none =>
      if (← model.strings.get).contains objectId then classIdentity model "java/lang/String"
      else
        let declared ← match objectId with
          | .external id => pure (model.classOf id)
          | .internal _ => pure ((← model.classNames.get).get? objectId)
        match declared with
        | some name => classIdentity model name
        | none =>
          let id ← freshIdentity model
          model.objectClasses.modify (·.insert objectId id)
          pure id
  internIdentity model .local classId

private def stringAddress (model : Model) (id : Identity) : IO Nat := do
  match (← model.strings.get).get? id with
  | none => pure 0
  | some info =>
    match info.address with
    | some address => pure address
    | none =>
      let address ← model.allocString info.contents
      model.strings.modify (·.insert id { info with address := some address })
      pure address

private def findBinding (model : Model) (call : Call) (static : Bool) (field : Bool) : IO Nat := do
  let owner ← resolve model (arg call 1)
  let name ← model.readString (arg call 2)
  let signature ← model.readString (arg call 3)
  let key : BindingKey := ⟨owner, name, signature, static⟩
  let id ← if field then pure ((← model.fieldIds.get).get? key) else pure ((← model.methodIds.get).get? key)
  match id with
  | some id => internIdentity model .local id
  | none => dynamicBinding model call

private def compute (model : Model) (call : Call) : IO (Nat × String) := do
  let fallback := fun () => do answer model (← model.default call (dynamicName model))
  match call.index with
  | 4 => pure (model.version, "")
  | 6 =>
    let name ← model.readString (arg call 1)
    pure (← classIdentity model name >>= internIdentity model .local, name)
  | 21 => pure (← resolve model (arg call 1) >>= internIdentity model .global, "")
  | 22 | 23 | 166 | 170 | 227 => pure (0, "")
  | 24 =>
    let left ← resolve model (arg call 1)
    let right ← resolve model (arg call 2)
    let same := if arg call 1 = 0 || arg call 2 = 0 then arg call 1 = arg call 2 else left = right
    pure (if same then 1 else 0, "")
  | 25 => pure (← resolve model (arg call 1) >>= internIdentity model .local, "")
  | 28 | 29 | 30 => pure (← callMethod model call false (arg call 2), "")
  | 31 => pure (← getObjectClass model (arg call 1), "")
  | 33 | 113 =>
    let name ← model.readString (arg call 2)
    let signature ← model.readString (arg call 3)
    pure (← findBinding model call (call.index = 113) false, s!"{name} {signature}")
  | 94 | 144 =>
    let name ← model.readString (arg call 2)
    let signature ← model.readString (arg call 3)
    pure (← findBinding model call (call.index = 144) true, s!"{name} {signature}")
  | 167 =>
    let contents ← model.readString (arg call 1)
    pure (← stringIdentity model contents true >>= internIdentity model .local, contents)
  | 164 | 168 =>
    let id ← resolve model (arg call 1)
    match (← model.strings.get).get? id with
    | some info => pure (info.contents.utf8ByteSize, "")
    | none => pure (← fallback (), "")
  | 165 | 169 => pure (← resolve model (arg call 1) >>= stringAddress model, "")
  | 171 =>
    let id ← resolve model (arg call 1)
    match (← model.arrays.get).get? id with
    | some elements => pure (elements.length, "")
    | none => pure (← fallback (), "")
  | 172 =>
    let length := arg call 1
    if length > 1000000 then throw <| IO.userError "unreasonable JNI object-array length"
    let id ← freshIdentity model
    let component ← resolve model (arg call 2)
    let className := (← model.classNames.get).get? component |>.map (fun name => s!"[L{name};") |>.getD "[Ljava/lang/Object;"
    model.objectClasses.modify (·.insert id (← classIdentity model className))
    model.arrays.modify (·.insert id (List.replicate length (.handle (arg call 3))))
    pure (← internIdentity model .local id, "")
  | 173 =>
    let id ← resolve model (arg call 1)
    match (← model.arrays.get).get? id with
    | some elements =>
      match elements[arg call 2]? with
      | some element => pure (← answer model element, "")
      | none => pure (← fallback (), "")
    | none => pure (← fallback (), "")
  | 219 => pure (0, s!"vm-out={arg call 1}")
  | 226 => pure (← resolve model (arg call 1) >>= internIdentity model .weak, "")
  | _ =>
    if call.index ≥ 34 && call.index ≤ 63 then pure (← callMethod model call false (arg call 2), "")
    else if call.index ≥ 64 && call.index ≤ 93 then pure (← callMethod model call false (arg call 3), "")
    else if call.index ≥ 95 && call.index ≤ 103 then pure (← getField model call false (arg call 2), "")
    else if call.index ≥ 114 && call.index ≤ 143 then pure (← callMethod model call true (arg call 2), "")
    else if call.index ≥ 145 && call.index ≤ 153 then pure (← getField model call true (arg call 2), "")
    else pure (← fallback (), "")

def dispatch (model : Model) (call : Call) : IO Nat := do
  let (result, detail) ← compute model call
  model.log call detail result
  pure result

def dispatchVm (model : Model) (call : Call) : IO Nat := do
  let result ← if call.index = 6 && arg call 2 != model.version then pure 0xFFFFFFFFFFFFFFFE else pure 0
  model.log call "JavaVM" result
  pure result

private def branch (source target : Nat) : Nat :=
  let delta := (Int.ofNat target - Int.ofNat source) / 4
  0x14000000 + (delta % 0x4000000).toNat

private def installStubs (emu : Emu) (stubs dispatcher count : Nat) : IO Unit :=
  (List.range count).forM fun index => do
    let address := stubs + index * 8
    let movz := 0x52800008 + index * 32
    Bap.Emu.write emu address (word (movz + branch (address + 4) dispatcher * 0x100000000))

def install (model : Model) (emu : Emu) (layout : Layout) : IO Unit := do
  model.env.set layout.env
  model.vm.set layout.vm
  writeWord emu layout.vm layout.vmFunctions
  writeWord emu layout.env layout.envFunctions
  installStubs emu layout.envStubs layout.envDispatcher 233
  installStubs emu layout.vmStubs layout.vmDispatcher 8
  (List.range 233).forM fun index =>
    writeWord emu (layout.envFunctions + index * 8) (layout.envStubs + index * 8)
  (List.range 8).forM fun index =>
    writeWord emu (layout.vmFunctions + index * 8) (layout.vmStubs + index * 8)

private def currentCall (emu : Emu) : IO Call := do
  let args ← (List.range 8).mapM fun index => readReg emu s!"X{index}"
  pure ⟨← readReg emu "X8", args.toArray⟩

def serve (model : Model) (emu : Emu) : IO Unit := do
  let call ← currentCall emu
  if call.index = 219 then writeWord emu (arg call 1) (← model.vm.get)
  let result ← dispatch model call
  writeReg emu "X0" result
  Bap.Emu.setPc emu (← readReg emu "X30")

def serveVm (model : Model) (emu : Emu) : IO Unit := do
  let call ← currentCall emu
  let result ← dispatchVm model call
  if call.index = 4 || call.index = 7 || (call.index = 6 && result = 0) then
    writeWord emu (← readReg emu "X1") (← model.env.get)
  writeReg emu "X0" result
  Bap.Emu.setPc emu (← readReg emu "X30")

end Bap.Emu.Jni
