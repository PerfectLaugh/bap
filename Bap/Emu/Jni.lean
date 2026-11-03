import Bap.Emu
import Bap.Linux.Wire
import Bap.Emu.Tasks

/-! # A model of JNI

What native code of an app gets from the Java runtime through `JNIEnv *` and `JavaVM *`, for running it without a runtime: the standard
table of 233 functions of the environment, in the numbering of `jni.h`, which Android has too, and the 8 of the VM. There is no Java
here. Classes, objects, strings and arrays are identities that the model keeps, behind handles that it gives out. What a method or a
field is comes from the declarations that the model is made with, and what it isn't told of, from `default`, which the host gives.

A guest calls the tables by the convention of its architecture (`attach`, `serveIndex`), or on AArch64 through the dispatcher of the
stubs that `install` writes (`serve`). What it holds goes into a checkpoint (`state`). -/

namespace Bap.Emu.Jni

/-- A call of a function of a table: its index in the table, and the words of its arguments, from the `JNIEnv *` or `JavaVM *` on. -/
structure Call where
  index : Nat
  args : Array Nat
  deriving Repr

/-- What a method, a field or `default` says a call gives: a number as it is, an object that the host knows by its number, a string with
these contents, a handle as it is, or a new object. The model makes a handle of each but the first and the fourth. -/
inductive Answer where
  | value (value : Nat)
  | object (identity : Nat)
  | string (contents : String)
  | handle (value : Nat)
  | fresh
  deriving Repr

/-- What a handle stands for: what the host knows by a number of its own, or what the model made. -/
inductive Identity where
  | external (value : Nat)
  | internal (value : Nat)
  deriving DecidableEq, Hashable, Repr

/-- The kinds of reference of JNI, each of which has handles of its own for the same identity. -/
inductive RefKind where
  | local | global | weak
  deriving DecidableEq, Hashable

/-- What `GetMethodID` and its kin look a method or a field up by: its class, name, signature, and whether it is static. -/
structure BindingKey where
  owner : Identity
  name : String
  signature : String
  static : Bool
  deriving DecidableEq, Hashable

/-- A method that the model has: what it gives for a call, which has the method's arguments after the object or class and the method ID. -/
structure MethodDecl where
  name : String
  signature : String
  answer : Call → IO Answer

/-- A field that the model has, and what it holds. -/
structure FieldDecl where
  name : String
  signature : String
  value : Answer

/-- A class that the model has, by its name as `FindClass` takes it, such as `java/lang/String`, with its methods and fields. -/
structure ClassDecl where
  name : String
  /-- What `GetSuperclass` gives for it, by its name: none for an interface, as for `java/lang/Object`. -/
  superclass : Option String := some "java/lang/Object"
  methods : List MethodDecl := []
  staticMethods : List MethodDecl := []
  fields : List FieldDecl := []
  staticFields : List FieldDecl := []

/-- An object that the host knows by a number, of a class, and the elements of it if it is an array. -/
structure ObjectDecl where
  identity : Nat
  className : String
  elements : List Answer := []

/-- A method that the model has, as it is known by its ID. -/
structure MethodInfo where
  decl : MethodDecl
  owner : Identity
  static : Bool

/-- A field that the model has, as it is known by its ID. -/
structure FieldInfo where
  decl : FieldDecl
  owner : Identity
  static : Bool

/-- A string, with where its bytes are once native code has asked for them, in UTF-8 and in UTF-16. -/
structure StringInfo where
  contents : String
  address : Option Nat := none
  wideAddress : Option Nat := none

/-- Where the model is in the memory of the guest. -/
structure Layout where
  /-- The `JavaVM`, a word that points at its table, which is what a `JavaVM *` is the address of. -/
  vm : Nat
  /-- The table of the VM, of 8 functions. -/
  vmFunctions : Nat
  /-- The `JNIEnv`, which is what native code is given the address of. -/
  env : Nat
  /-- The table of the environment, of 233 functions. -/
  envFunctions : Nat
  /-- Where the function of each index is, 8 bytes apart. -/
  envStubs : Nat
  /-- Where the stubs of AArch64 go to, with the index in `X8`: a hook there is to run `serve`. -/
  envDispatcher : Nat
  vmStubs : Nat
  vmDispatcher : Nat

/-- A model, with what it has given out and what it was given: how to read and place strings and bytes in the guest, the class of
what the host knows by a number, what to give for what it isn't told of, and what hears of each call. -/
structure Model where
  nextHandle : IO.Ref Nat
  nextIdentity : IO.Ref Nat
  handles : IO.Ref (Std.HashMap (RefKind × Identity) Nat)
  sources : IO.Ref (Std.HashMap Nat Identity)
  classes : IO.Ref (Std.HashMap String Identity)
  classNames : IO.Ref (Std.HashMap Identity String)
  objectClasses : IO.Ref (Std.HashMap Identity Identity)
  arrays : IO.Ref (Std.HashMap Identity (List Answer))
  arrayAddresses : IO.Ref (Std.HashMap Identity Nat)
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
  allocBytes : ByteArray → IO Nat
  classOf : Nat → Option String
  default : Call → (Nat → IO (Option String)) → IO Answer
  log : Call → String → Nat → IO Unit
  version : Nat := 0x10006
  /-- The superclass of each class that was declared, by name, which goes by names so that a checkpoint has nothing to say of it. -/
  superclasses : Std.HashMap String (Option String) := {}
  /-- Whether the guest has the most significant byte first, for the elements of arrays and the units of strings that it is given. -/
  big : Bool := false
  exception : IO.Ref (Option Identity)
  env : IO.Ref Nat
  vm : IO.Ref Nat

/-- The word of an argument of a call, from 0 for the `JNIEnv *`, or 0 if it has none there. -/
def arg (call : Call) (index : Nat) : Nat := call.args.getD index 0

/-- The UTF-16 code units of a string, as `GetStringChars` and `GetStringLength` see it. -/
def utf16Units (text : String) : List Nat :=
  text.toList.flatMap fun char =>
    if char.toNat < 0x10000 then [char.toNat]
    else
      let offset := char.toNat - 0x10000
      [0xD800 + offset / 0x400, 0xDC00 + offset % 0x400]

/-- The bytes of UTF-16 code units, the least significant first unless `big`. -/
def utf16Bytes (units : List Nat) (big : Bool := false) : ByteArray :=
  ByteArray.mk (units.flatMap fun unit =>
    if big then [UInt8.ofNat (unit / 256), UInt8.ofNat (unit % 256)] else [UInt8.ofNat (unit % 256), UInt8.ofNat (unit / 256)]).toArray

/-- The size of an element of a primitive array, by the `Get<Type>ArrayElements` of the JNI table:
boolean, byte, char, short, int, long, float, double. -/
def arrayElementWidth : Nat → Option Nat
  | 183 | 184 => some 1
  | 185 | 186 => some 2
  | 187 | 189 => some 4
  | 188 | 190 => some 8
  | _ => none

/-- The array class of `New<Type>Array` of the JNI table. -/
def primitiveArrayClass : Nat → Option String
  | 175 => some "[Z"
  | 176 => some "[B"
  | 177 => some "[C"
  | 178 => some "[S"
  | 179 => some "[I"
  | 180 => some "[J"
  | 181 => some "[F"
  | 182 => some "[D"
  | _ => none

/-- What the JNI table has at an index, for the families that `compute` serves alike. -/
inductive Family where
  | callMethod (static : Bool) (methodArgument : Nat)
  | getField (static : Bool)
  | other
  deriving DecidableEq, Repr

/-- Which family a function of the environment is of, with whether it is static and which argument has the method ID: `NewObject`,
`Call<Type>Method`, `CallNonvirtual<Type>Method` and `CallStatic<Type>Method`, each in its plain, `V` and `A` forms, and
`Get<Type>Field` and `GetStatic<Type>Field`. -/
def familyOf (index : Nat) : Family :=
  if index ≥ 28 && index ≤ 30 then .callMethod false 2
  else if index ≥ 34 && index ≤ 63 then .callMethod false 2
  else if index ≥ 64 && index ≤ 93 then .callMethod false 3
  else if index ≥ 95 && index ≤ 103 then .getField false
  else if index ≥ 114 && index ≤ 143 then .callMethod true 2
  else if index ≥ 145 && index ≤ 153 then .getField true
  else .other

/-- `JavaVM.GetEnv`: 0, or `JNI_EVERSION` (-3, as an unsigned word) for a version that the model does not
have, that is a newer one. -/
def getEnvResult (requested supported : Nat) : Nat :=
  if requested ≤ supported then 0 else 0xFFFFFFFFFFFFFFFD

private def reg (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩

private def readReg (emu : Emu) (name : String) : IO Nat := do
  match Value.asBits (← Bap.Emu.reg emu (reg name)) with
  | .ok value => pure value.2.toNat
  | .error error => throw <| IO.userError error

private def writeReg (emu : Emu) (name : String) (value : Nat) : IO Unit :=
  Bap.Emu.setReg emu (reg name) (.bits (BitVec.ofNat 64 value))

private def word (value : Nat) : ByteArray :=
  ByteArray.mk ((List.range 8).map fun index => UInt8.ofNat (value / 256 ^ index % 256)).toArray

/-- The string of C at an address, up to 4096 bytes: what a model is given to read the names that native code passes, which are text.
What is below 0x10000 isn't a string, and is empty. -/
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

/-- What a handle stands for. One that the model didn't give out is what the host knows by that number. -/
def resolve (model : Model) (handle : Nat) : IO Identity := do
  pure ((← model.sources.get).get? handle |>.getD (.external handle))

/-- What a handle of a string has in it, if it is one. -/
def stringContents (model : Model) (handle : Nat) : IO (Option String) := do
  let id ← resolve model handle
  pure ((← model.strings.get).get? id |>.map fun info => info.contents)

/-- The handle of an identity, of a kind of reference: the same one each time. The null object is 0. -/
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

/-- A local handle of what the host knows by a number, to give native code: an object, such as the `this` of a native method. -/
def intern (model : Model) (identity : Nat) : IO Nat :=
  internIdentity model .local (.external identity)

/-- The number that the host knows what a handle stands for by, if it is one of the host's. -/
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
    model.strings.modify (·.insert id { contents })
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

/-- A model. `readString` reads a name that native code passes, `allocString` and `allocBytes` put what it asks for in its memory,
`default` says what to give for what isn't declared, by the call and the name of a method or field if it was asked for by one, and
`log` hears of each call with what it gave. `classOf` says the class of an object of the host. `big` is that the guest has the most
significant byte first. -/
def create (readString : Nat → IO String) (allocString : String → IO Nat)
    (allocBytes : ByteArray → IO Nat)
    (default : Call → (Nat → IO (Option String)) → IO Answer)
    (log : Call → String → Nat → IO Unit := fun _ _ _ => pure ())
    (classes : List ClassDecl := []) (objects : List ObjectDecl := [])
    (classOf : Nat → Option String := fun _ => none)
    (firstHandle : Nat := 0x52030000) (version : Nat := 0x10006) (big : Bool := false) : IO Model := do
  let model : Model := {
    nextHandle := ← IO.mkRef firstHandle
    nextIdentity := ← IO.mkRef 0
    handles := ← IO.mkRef {}
    sources := ← IO.mkRef {}
    classes := ← IO.mkRef {}
    classNames := ← IO.mkRef {}
    objectClasses := ← IO.mkRef {}
    arrays := ← IO.mkRef {}
    arrayAddresses := ← IO.mkRef {}
    methods := ← IO.mkRef {}
    methodIds := ← IO.mkRef {}
    fields := ← IO.mkRef {}
    fieldIds := ← IO.mkRef {}
    strings := ← IO.mkRef {}
    stringsByContent := ← IO.mkRef {}
    dynamicIds := ← IO.mkRef {}
    dynamicNames := ← IO.mkRef {}
    nextDynamic := ← IO.mkRef 0x10000
    readString, allocString, allocBytes, classOf, default, log, version, big
    superclasses := classes.foldl (init := {}) fun table decl => table.insert decl.name decl.superclass
    exception := ← IO.mkRef none
    env := ← IO.mkRef 0
    vm := ← IO.mkRef 0
  }
  classes.forM (registerClass model)
  for object in objects do
    let classId ← classIdentity model object.className
    model.objectClasses.modify (·.insert (.external object.identity) classId)
    model.arrays.modify (·.insert (.external object.identity) object.elements)
  pure model

/-- The name of a method or field that wasn't declared, by the ID that `GetMethodID` or `GetFieldID` gave for it. -/
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

/-- The UTF-16 buffer of `GetStringChars`, which is not the UTF-8 one of `GetStringUTFChars`. -/
private def wideStringAddress (model : Model) (id : Identity) : IO Nat := do
  match (← model.strings.get).get? id with
  | none => pure 0
  | some info =>
    match info.wideAddress with
    | some address => pure address
    | none =>
      let address ← model.allocBytes (utf16Bytes (utf16Units info.contents) model.big)
      model.strings.modify (·.insert id { info with wideAddress := some address })
      pure address

private def newArray (model : Model) (className : String) (length : Nat) : IO Nat := do
  if length > 1000000 then throw <| IO.userError "unreasonable JNI array length"
  let id ← freshIdentity model
  model.objectClasses.modify (·.insert id (← classIdentity model className))
  model.arrays.modify (·.insert id (List.replicate length (.value 0)))
  internIdentity model .local id

private def arrayAddress (model : Model) (id : Identity) (width : Nat) : IO Nat := do
  match (← model.arrayAddresses.get).get? id with
  | some address => pure address
  | none =>
    match (← model.arrays.get).get? id with
    | none => pure 0
    | some elements =>
      let bytes := elements.flatMap fun element =>
        match element with
        | .value value =>
          let bytes := (List.range width).map fun index => UInt8.ofNat (value / 256 ^ index % 256)
          if model.big then bytes.reverse else bytes
        | _ => []
      let address ← model.allocBytes (ByteArray.mk bytes.toArray)
      model.arrayAddresses.modify (·.insert id address)
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
  | 10 =>
    -- GetSuperclass(env, class): as it was declared, or `java/lang/Object` for what wasn't, and null for that and for an interface.
    if arg call 1 = 0 then pure (0, "superclass-null") else
      let name := (← model.classNames.get).get? (← resolve model (arg call 1))
      let parent := match name with
        | some "java/lang/Object" => none
        | some name => (model.superclasses.get? name).getD (some "java/lang/Object")
        | none => some "java/lang/Object"
      match parent with
      | some parent => pure (← classIdentity model parent >>= internIdentity model .local, s!"superclass {parent}")
      | none => pure (0, "superclass-none")
  | 13 =>
    model.exception.set (some (← resolve model (arg call 1)))
    pure (0, "throw")
  | 14 =>
    -- ThrowNew(env, class, message) throws a new object of the class, and not the class.
    let exception ← freshIdentity model
    model.objectClasses.modify (·.insert exception (← resolve model (arg call 1)))
    model.exception.set (some exception)
    pure (0, "throw-new")
  | 15 =>
    match ← model.exception.get with
    | some id => pure (← internIdentity model .local id, "exception")
    | none => pure (0, "")
  | 16 => pure (0, "describe")
  | 17 =>
    model.exception.set none
    pure (0, "clear")
  | 21 => pure (← resolve model (arg call 1) >>= internIdentity model .global, "")
  | 22 | 23 | 166 | 170 | 227 => pure (0, "")
  | 24 =>
    let left ← resolve model (arg call 1)
    let right ← resolve model (arg call 2)
    let same := if arg call 1 = 0 || arg call 2 = 0 then arg call 1 = arg call 2 else left = right
    pure (if same then 1 else 0, "")
  | 25 => pure (← resolve model (arg call 1) >>= internIdentity model .local, "")
  | 27 =>
    -- AllocObject(env, class): an object of the class that no constructor has run on.
    let object ← freshIdentity model
    model.objectClasses.modify (·.insert object (← resolve model (arg call 1)))
    pure (← internIdentity model .local object, "alloc")
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
  | 164 =>
    let id ← resolve model (arg call 1)
    match (← model.strings.get).get? id with
    | some info => pure ((utf16Units info.contents).length, "")
    | none => pure (← fallback (), "")
  | 168 =>
    let id ← resolve model (arg call 1)
    match (← model.strings.get).get? id with
    | some info => pure (info.contents.utf8ByteSize, "")
    | none => pure (← fallback (), "")
  | 165 => pure (← resolve model (arg call 1) >>= wideStringAddress model, "")
  | 169 => pure (← resolve model (arg call 1) >>= stringAddress model, "")
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
  | 174 =>
    let id ← resolve model (arg call 1)
    match (← model.arrays.get).get? id with
    | some elements =>
      if arg call 2 < elements.length then
        model.arrays.modify (·.insert id (elements.set (arg call 2) (.handle (arg call 3))))
        pure (0, "")
      else pure (← fallback (), "")
    | none => pure (← fallback (), "")
  | 219 => pure (0, s!"vm-out={arg call 1}")
  | 226 => pure (← resolve model (arg call 1) >>= internIdentity model .weak, "")
  | 228 =>
    match ← model.exception.get with
    | some _ => pure (1, "exception-pending")
    | none => pure (0, "")
  | _ =>
    match primitiveArrayClass call.index, arrayElementWidth call.index with
    | some className, _ => pure (← newArray model className (arg call 1), "")
    | _, some width => pure (← arrayAddress model (← resolve model (arg call 1)) width, "")
    | none, none =>
      match familyOf call.index with
      | .callMethod static methodArgument =>
        pure (← callMethod model call static (arg call methodArgument), "")
      | .getField static => pure (← getField model call static (arg call 2), "")
      | .other => pure (← fallback (), "")

/-- What a function of the environment gives for a call, which it logs. -/
def dispatch (model : Model) (call : Call) : IO Nat := do
  let (result, detail) ← compute model call
  model.log call detail result
  pure result

/-- What a function of the VM gives: `GetEnv` says whether it has the version asked for, and the rest succeed. -/
def dispatchVm (model : Model) (call : Call) : IO Nat := do
  let result := if call.index = 6 then getEnvResult (arg call 2) model.version else 0
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

/-- A pointer of the guest at an address, as wide as its words and in its order. -/
private def writePointer (emu : Emu) (address value : Nat) : IO Unit := do
  let width ← wordWidth emu
  let bytes := (List.range (width / 8)).map fun index => UInt8.ofNat (value / 256 ^ index % 256)
  Bap.Emu.write emu address (ByteArray.mk (if emu.config.endian == .big then bytes.reverse else bytes).toArray)

/-- Puts the tables of the VM and of the environment where the layout says, each function at its stub, 8 bytes apart. On AArch64 a stub
is code that says which it is and goes to the dispatcher, for `serve` and `serveVm`; elsewhere what is there doesn't run, as `attach`
serves a stub before it would. -/
def install (model : Model) (emu : Emu) (layout : Layout) : IO Unit := do
  let word := (← wordWidth emu) / 8
  model.env.set layout.env
  model.vm.set layout.vm
  writePointer emu layout.vm layout.vmFunctions
  writePointer emu layout.env layout.envFunctions
  if emu.config.syscallAbi == .aarch64 then
    installStubs emu layout.envStubs layout.envDispatcher 233
    installStubs emu layout.vmStubs layout.vmDispatcher 8
  (List.range 233).forM fun index =>
    writePointer emu (layout.envFunctions + index * word) (layout.envStubs + index * 8)
  (List.range 8).forM fun index =>
    writePointer emu (layout.vmFunctions + index * word) (layout.vmStubs + index * 8)

/-! ### Calls by the convention of each architecture

Native code calls what a table has as a function of C, by the convention of its architecture: the arguments in registers and then on
the stack, and the result in a register, or in two for a `jlong` on 32 bits, or in a register of floating point for a `jfloat` or a
`jdouble`. A variadic call, `Call<Type>Method`, has its arguments where a call that isn't has them, on the systems that this serves. -/

private structure Convention where
  arguments : List String
  stack : String
  /-- Where on the stack the first argument that isn't in a register is, at the first instruction. -/
  stackOffset : Nat
  /-- What has where it returns to; on x86 the stack has it. -/
  link : Option String
  result : String
  /-- Of a result of 64 bits on 32: the register of the other half, and whether it has the high half or the low. -/
  pair : Option (String × Bool) := none
  /-- The registers of a floating-point result, if the host serves those here. -/
  float : List String := []

private def conventionOf (emu : Emu) (width : Nat) : Convention :=
  let big := emu.config.endian == .big
  match emu.config.syscallAbi with
  | .aarch64 => { arguments := (List.range 8).map (s!"X{·}"), stack := "SP", stackOffset := 0, link := some "X30", result := "X0"
                  float := ["Q0"] }
  | .x86_64 => { arguments := ["RDI", "RSI", "RDX", "RCX", "R8", "R9"], stack := "RSP", stackOffset := 8, link := none
                 result := "RAX", float := ["ZMM0"] }
  | .x86_32 => { arguments := [], stack := "ESP", stackOffset := 4, link := none, result := "EAX", pair := some ("EDX", true) }
  -- Android's ARM is soft-float, with what floats in core registers, and the rest of Linux has `D0`: both have it.
  | .arm => { arguments := ["R0", "R1", "R2", "R3"], stack := "SP", stackOffset := 0, link := some "LR", result := "R0"
              pair := some ("R1", true), float := ["D0"] }
  | .riscv => { arguments := (List.range 8).map (s!"X{10 + ·}"), stack := "X2", stackOffset := 0, link := some "X1", result := "X10"
                pair := if width == 32 then some ("X11", true) else none, float := ["F10"] }
  | .mips =>
    if width == 32 then
      { arguments := ["R4", "R5", "R6", "R7"], stack := "R29", stackOffset := 16, link := some "R31", result := "R2"
        pair := some ("R3", !big) }
    else { arguments := (List.range 8).map (s!"R{4 + ·}"), stack := "R29", stackOffset := 0, link := some "R31", result := "R2" }
  | .powerpc => { arguments := (List.range 8).map (s!"R{3 + ·}"), stack := "R1", stackOffset := 8, link := some "LR", result := "R3"
                  pair := some ("R4", false) }
  | .powerpc64 => { arguments := (List.range 8).map (s!"R{3 + ·}"), stack := "R1", stackOffset := 96, link := some "LR", result := "R3" }

/-- What a function of the table gives: of `Call<Type>Method` and `Get<Type>Field`, by their type, as `boolean`, `byte`, `char`, `short`,
`int`, `long`, `float`, `double` and `void` come after `Object` in each. -/
inductive ResultKind where
  | word | long | float | double
  deriving DecidableEq, Repr

/-- What the function of an index gives, of those that give a `jlong`, a `jfloat` or a `jdouble`, and otherwise a word. -/
def resultKindOf (index : Nat) : ResultKind :=
  let ofType (type : Nat) : ResultKind := match type with
    | 6 => .long
    | 7 => .float
    | 8 => .double
    | _ => .word
  if index ≥ 34 && index ≤ 63 then ofType ((index - 34) / 3)
  else if index ≥ 64 && index ≤ 93 then ofType ((index - 64) / 3)
  else if index ≥ 114 && index ≤ 143 then ofType ((index - 114) / 3)
  else if index ≥ 95 && index ≤ 103 then ofType (index - 95)
  else if index ≥ 145 && index ≤ 153 then ofType (index - 145)
  else .word

private def registerOf (emu : Emu) (name : String) (width : Nat) : IO Nat := do
  match Value.asBits (← Bap.Emu.reg emu ⟨name, .imm width, 0, false⟩) with
  | .ok value => pure value.2.toNat
  | .error error => throw <| IO.userError error

private def setRegister (emu : Emu) (name : String) (width value : Nat) : IO Unit :=
  Bap.Emu.setReg emu ⟨name, .imm width, 0, false⟩ (.bits (BitVec.ofNat width value))

/-- Reads a word of the guest. -/
private def readPointer (emu : Emu) (address width : Nat) : IO Nat := do
  let bytes ← Bap.Emu.read emu address (width / 8)
  let ordered := if emu.config.endian == .big then bytes.toList else bytes.toList.reverse
  pure (ordered.foldl (fun value byte => value * 256 + byte.toNat) 0)

/-- Serves the function `index` of the environment, or of the VM, for a call that is at its first instruction now, by the convention
of the architecture, and returns to where it was called from. -/
def serveIndex (model : Model) (emu : Emu) (index : Nat) (vm : Bool := false) : IO Unit := do
  let width ← wordWidth emu
  let convention := conventionOf emu width
  let registers ← convention.arguments.mapM fun name => registerOf emu name width
  let sp ← registerOf emu convention.stack width
  let stacked ← (List.range (8 - min 8 registers.length)).mapM fun index =>
    readPointer emu (sp + convention.stackOffset + index * (width / 8)) width
  let call : Call := ⟨index, (registers ++ stacked).take 8 |>.toArray⟩
  for starts in ← emu.hostStarts.get do starts s!"{if vm then "jni-vm" else "jni"}:{index}"
  let result ← if vm then do
      let result ← dispatchVm model call
      if index = 4 || index = 7 || (index = 6 && result = 0) then writePointer emu (arg call 1) (← model.env.get)
      pure result
    else do
      if index = 219 then writePointer emu (arg call 1) (← model.vm.get)
      dispatch model call
  let kind := if vm then .word else resultKindOf index
  -- A value that is of a register of floating point is there, and in the core registers as well, as soft-float ARM has it.
  if kind == .float || kind == .double then
    for name in convention.float do
      let floatWidth := if name == "Q0" then 128 else if name == "ZMM0" then 512 else 64
      -- RISC-V boxes a single in ones above it.
      let value := if name == "F10" && kind == .float then result % 2 ^ 32 + (2 ^ 64 - 2 ^ 32) else result
      setRegister emu name floatWidth value
  match convention.pair, kind with
  | some (other, high), .long | some (other, high), .double =>
    let low := result % 2 ^ 32
    let upper := result / 2 ^ 32 % 2 ^ 32
    setRegister emu convention.result width (if high then low else upper)
    setRegister emu other width (if high then upper else low)
  | _, _ => setRegister emu convention.result width (result % 2 ^ width)
  for ends in ← emu.hostEnds.get do ends (some convention.result)
  match convention.link with
  | some link =>
    let target ← registerOf emu link width
    if emu.config.syscallAbi == .arm then
      Bap.Emu.setReg emu ⟨"ISET", .imm 1, 0, false⟩ (.bits (BitVec.ofNat 1 (target % 2)))
      Bap.Emu.setPc emu (target - target % 2)
    else Bap.Emu.setPc emu target
  | none =>
    -- x86 has where it returns to on the stack, which a return takes off.
    let target ← readPointer emu sp width
    setRegister emu convention.stack width (sp + width / 8)
    Bap.Emu.setPc emu target

/-- `serveIndex` for the dispatcher of AArch64, whose stubs say which function it is in `X8`. -/
def serve (model : Model) (emu : Emu) : IO Unit := do
  serveIndex model emu (← readReg emu "X8")

/-- `serve` for the stubs of the VM. -/
def serveVm (model : Model) (emu : Emu) : IO Unit := do
  serveIndex model emu (← readReg emu "X8") (vm := true)

/-- Installs the tables and serves the stubs of each function, on any architecture: a call that comes to a stub is served there,
whatever is in it, by the convention of the architecture. The stubs have to be where something can be called, and the tables where
they can be read. -/
def attach (model : Model) (emu : Emu) (layout : Layout) : IO (List HookId) := do
  install model emu layout
  let env ← onCode emu (layout.envStubs, layout.envStubs + 233 * 8 - 1) fun current address => do
    if (← current.pc.get) == address && (address - layout.envStubs) % 8 == 0 then
      serveIndex model current ((address - layout.envStubs) / 8)
  let vm ← onCode emu (layout.vmStubs, layout.vmStubs + 8 * 8 - 1) fun current address => do
    if (← current.pc.get) == address && (address - layout.vmStubs) % 8 == 0 then
      serveIndex model current ((address - layout.vmStubs) / 8) (vm := true)
  pure [env, vm]

/-- The layout of `attachAt`: two pages from `base`, of which the first has the VM, the environment and their tables, and the second
their stubs. -/
def Layout.at (base : Nat) : Layout :=
  { vm := base, env := base + 0x10, vmFunctions := base + 0x40, envFunctions := base + 0x100
    envStubs := base + 0x1000, vmStubs := base + 0x1800, envDispatcher := base + 0x1c00, vmDispatcher := base + 0x1c00 }

/-- Maps two pages at a free address, for the tables and for the stubs, and `attach`es there. It says where they are: `env` is the
`JNIEnv *` to give native code, and `vm` the `JavaVM *`. -/
def attachAt (model : Model) (emu : Emu) : IO Layout := do
  let base ← Bap.Emu.freeAddress emu 0x2000
  Bap.Emu.map emu ⟨base, ByteArray.mk (Array.replicate 0x1000 0), ⟨true, true, false⟩⟩
  -- Written once, with the stubs of AArch64, and then only run.
  Bap.Emu.map emu ⟨base + 0x1000, ByteArray.mk (Array.replicate 0x1000 0), ⟨true, true, false⟩⟩
  let layout := Layout.at base
  let _ ← attach model emu layout
  Bap.Emu.protect emu (base + 0x1000) 0x1000 ⟨true, false, true⟩
  pure layout

/-! What a model holds, for a checkpoint. A method or a field is saved by what it is called, and takes its function or its value from
the declarations that the new model was made with, which have to be the same ones. -/

namespace State

open Bap.Linux.Wire

private def putIdentity (out : ByteArray) : Identity → ByteArray
  | .external value => putNat (putNat out 0) value
  | .internal value => putNat (putNat out 1) value

private def getIdentity : Decoder Identity := fun data at_ => do
  let (tag, at_) ← getNat data at_
  let (value, at_) ← getNat data at_
  match tag with
  | 0 => .ok (.external value, at_)
  | 1 => .ok (.internal value, at_)
  | _ => .error "a checkpoint with a JNI identity that isn't"

private def kindTag : RefKind → Nat
  | .local => 0
  | .global => 1
  | .weak => 2

private def kindOf : Nat → Except String RefKind
  | 0 => .ok .local
  | 1 => .ok .global
  | 2 => .ok .weak
  | _ => .error "a checkpoint with a JNI reference that isn't"

private def putAnswer (out : ByteArray) : Answer → ByteArray
  | .value value => putNat (putNat out 0) value
  | .object identity => putNat (putNat out 1) identity
  | .string contents => putText (putNat out 2) contents
  | .handle value => putNat (putNat out 3) value
  | .fresh => putNat out 4

private def getAnswer : Decoder Answer := fun data at_ => do
  let (tag, at_) ← getNat data at_
  match tag with
  | 0 => let (value, at_) ← getNat data at_; .ok (.value value, at_)
  | 1 => let (value, at_) ← getNat data at_; .ok (.object value, at_)
  | 2 => let (value, at_) ← getText data at_; .ok (.string value, at_)
  | 3 => let (value, at_) ← getNat data at_; .ok (.handle value, at_)
  | 4 => .ok (.fresh, at_)
  | _ => .error "a checkpoint with a JNI answer that isn't"

private def putKey (out : ByteArray) (key : BindingKey) : ByteArray :=
  putFlag (putText (putText (putIdentity out key.owner) key.name) key.signature) key.static

private def getKey : Decoder BindingKey := fun data at_ => do
  let (owner, at_) ← getIdentity data at_
  let (name, at_) ← getText data at_
  let (signature, at_) ← getText data at_
  let (static, at_) ← getFlag data at_
  .ok (⟨owner, name, signature, static⟩, at_)

private def putPair (putKey : ByteArray → κ → ByteArray) (putValue : ByteArray → ν → ByteArray) (out : ByteArray)
    (entry : κ × ν) : ByteArray :=
  putValue (putKey out entry.1) entry.2

private def getPair (getKey : Decoder κ) (getValue : Decoder ν) : Decoder (κ × ν) := fun data at_ => do
  let (key, at_) ← getKey data at_
  let (value, at_) ← getValue data at_
  .ok ((key, value), at_)

private def putTable [BEq κ] [Hashable κ] (putKey : ByteArray → κ → ByteArray) (putValue : ByteArray → ν → ByteArray) (out : ByteArray)
    (table : Std.HashMap κ ν) : ByteArray :=
  putSorted (putPair putKey putValue) out table.toList

private def getTable [BEq κ] [Hashable κ] (getKey : Decoder κ) (getValue : Decoder ν) : Decoder (Std.HashMap κ ν) := fun data at_ => do
  let (entries, at_) ← getList (getPair getKey getValue) data at_
  .ok (Std.HashMap.ofList entries, at_)

private def putRefKey (out : ByteArray) (key : RefKind × Identity) : ByteArray :=
  putIdentity (putNat out (kindTag key.1)) key.2

private def getRefKey : Decoder (RefKind × Identity) := fun data at_ => do
  let (tag, at_) ← getNat data at_
  let kind ← kindOf tag
  let (identity, at_) ← getIdentity data at_
  .ok ((kind, identity), at_)

private def putStringInfo (out : ByteArray) (info : StringInfo) : ByteArray :=
  putOption putNat (putOption putNat (putText out info.contents) info.address) info.wideAddress

private def getStringInfo : Decoder StringInfo := fun data at_ => do
  let (contents, at_) ← getText data at_
  let (address, at_) ← getOption getNat data at_
  let (wideAddress, at_) ← getOption getNat data at_
  .ok ({ contents, address, wideAddress }, at_)

private def putDynamicKey (out : ByteArray) (key : Nat × Identity × String × String) : ByteArray :=
  putText (putText (putIdentity (putNat out key.1) key.2.1) key.2.2.1) key.2.2.2

private def getDynamicKey : Decoder (Nat × Identity × String × String) := fun data at_ => do
  let (index, at_) ← getNat data at_
  let (owner, at_) ← getIdentity data at_
  let (name, at_) ← getText data at_
  let (signature, at_) ← getText data at_
  .ok ((index, owner, name, signature), at_)

/-- A method or a field without what it does: what it is called, and whose it is. -/
private def putBinding (out : ByteArray) (entry : Identity × String × String × Identity × Bool) : ByteArray :=
  putFlag (putIdentity (putText (putText (putIdentity out entry.1) entry.2.1) entry.2.2.1) entry.2.2.2.1) entry.2.2.2.2

private def getBinding : Decoder (Identity × String × String × Identity × Bool) := fun data at_ => do
  let (id, at_) ← getIdentity data at_
  let (name, at_) ← getText data at_
  let (signature, at_) ← getText data at_
  let (owner, at_) ← getIdentity data at_
  let (static, at_) ← getFlag data at_
  .ok ((id, name, signature, owner, static), at_)

private def putBytesOf (model : Model) : IO ByteArray := do
  let out := putNat (putNat (putNat ByteArray.empty (← model.nextHandle.get)) (← model.nextIdentity.get)) (← model.nextDynamic.get)
  let out := putTable putRefKey putNat out (← model.handles.get)
  let out := putTable putNat putIdentity out (← model.sources.get)
  let out := putTable putText putIdentity out (← model.classes.get)
  let out := putTable putIdentity putText out (← model.classNames.get)
  let out := putTable putIdentity putIdentity out (← model.objectClasses.get)
  let out := putTable putIdentity (putList putAnswer) out (← model.arrays.get)
  let out := putTable putIdentity putNat out (← model.arrayAddresses.get)
  let methods := (← model.methods.get).toList.map fun (id, info) => (id, info.decl.name, info.decl.signature, info.owner, info.static)
  let out := putSorted putBinding out methods
  let out := putTable putKey putIdentity out (← model.methodIds.get)
  let fields := (← model.fields.get).toList.map fun (id, info) => (id, info.decl.name, info.decl.signature, info.owner, info.static)
  let out := putSorted putBinding out fields
  let out := putTable putKey putIdentity out (← model.fieldIds.get)
  let out := putTable putIdentity putStringInfo out (← model.strings.get)
  let out := putTable putText putIdentity out (← model.stringsByContent.get)
  let out := putTable putDynamicKey putNat out (← model.dynamicIds.get)
  let out := putTable putIdentity putText out (← model.dynamicNames.get)
  let out := putOption putIdentity out (← model.exception.get)
  pure (putNat (putNat out (← model.env.get)) (← model.vm.get))

/-- The declarations of a saved table of methods or fields, from those that the model was made with. -/
private def rebind {δ : Type} (kind : String) (saved : Std.HashMap Identity String)
    (declarations : List (String × String × String × Bool × δ))
    (entries : List (Identity × String × String × Identity × Bool)) :
    Except String (List (Identity × δ × Identity × Bool)) := do
  if entries.length != declarations.length then
    throw s!"a checkpoint with {entries.length} JNI {kind}s, and this model declares {declarations.length}"
  entries.mapM fun (id, name, signature, owner, static) => do
    let className := saved.getD owner ""
    match declarations.find? fun (ownerName, otherName, otherSignature, otherStatic, _) =>
        ownerName == className && otherName == name && otherSignature == signature && otherStatic == static with
    | some (_, _, _, _, decl) => .ok (id, decl, owner, static)
    | none => .error s!"a checkpoint with the JNI {kind} {className}.{name} {signature}, which this model doesn't declare"

private def loadBytes (model : Model) (data : ByteArray) : IO Unit := do
  let decode : Except String (IO Unit) := do
    let (nextHandle, at_) ← getNat data 0
    let (nextIdentity, at_) ← getNat data at_
    let (nextDynamic, at_) ← getNat data at_
    let (handles, at_) ← getTable getRefKey getNat data at_
    let (sources, at_) ← getTable getNat getIdentity data at_
    let (classes, at_) ← getTable getText getIdentity data at_
    let (classNames, at_) ← getTable getIdentity getText data at_
    let (objectClasses, at_) ← getTable getIdentity getIdentity data at_
    let (arrays, at_) ← getTable getIdentity (getList getAnswer) data at_
    let (arrayAddresses, at_) ← getTable getIdentity getNat data at_
    let (methods, at_) ← getList getBinding data at_
    let (methodIds, at_) ← getTable getKey getIdentity data at_
    let (fields, at_) ← getList getBinding data at_
    let (fieldIds, at_) ← getTable getKey getIdentity data at_
    let (strings, at_) ← getTable getIdentity getStringInfo data at_
    let (stringsByContent, at_) ← getTable getText getIdentity data at_
    let (dynamicIds, at_) ← getTable getDynamicKey getNat data at_
    let (dynamicNames, at_) ← getTable getIdentity getText data at_
    let (exception, at_) ← getOption getIdentity data at_
    let (env, at_) ← getNat data at_
    let (vm, at_) ← getNat data at_
    expectEnd data at_
    .ok do
      let names ← model.classNames.get
      let methodDecls := (← model.methods.get).toList.map fun (_, info) =>
        (names.getD info.owner "", info.decl.name, info.decl.signature, info.static, info.decl)
      let fieldDecls := (← model.fields.get).toList.map fun (_, info) =>
        (names.getD info.owner "", info.decl.name, info.decl.signature, info.static, info.decl)
      let methods ← IO.ofExcept (rebind "method" classNames methodDecls methods)
      let fields ← IO.ofExcept (rebind "field" classNames fieldDecls fields)
      model.nextHandle.set nextHandle
      model.nextIdentity.set nextIdentity
      model.nextDynamic.set nextDynamic
      model.handles.set handles
      model.sources.set sources
      model.classes.set classes
      model.classNames.set classNames
      model.objectClasses.set objectClasses
      model.arrays.set arrays
      model.arrayAddresses.set arrayAddresses
      model.methods.set (Std.HashMap.ofList (methods.map fun (id, decl, owner, static) => (id, ⟨decl, owner, static⟩)))
      model.methodIds.set methodIds
      model.fields.set (Std.HashMap.ofList (fields.map fun (id, decl, owner, static) => (id, ⟨decl, owner, static⟩)))
      model.fieldIds.set fieldIds
      model.strings.set strings
      model.stringsByContent.set stringsByContent
      model.dynamicIds.set dynamicIds
      model.dynamicNames.set dynamicNames
      model.exception.set exception
      model.env.set env
      model.vm.set vm
  (← IO.ofExcept decode)

end State

/-- What holds the state of a model, for the `attach` of a `RuntimeModel`. -/
def state (model : Model) : Bap.Linux.ModelState where
  save := State.putBytesOf model
  load := State.loadBytes model

end Bap.Emu.Jni
