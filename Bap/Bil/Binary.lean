import Bap.Bil.Syntax
import Std.Data.HashMap

/-! The compact binary form of BIL: little-endian base-128 numbers, so that no width limits a value, and tables that
a value may refer to, so that what is the same is stored once and shared when it is read back. A table only decides
what is stored by reference. It need not be complete, and nothing has to hold of its index, since `putAt` looks at what
it finds. `Bap.Proofs.Binary` proves that what `put` writes, `get` reads back. -/

namespace Bap.Binary

open Bap Bil

/-! ### Numbers, bytes and text -/

/-- The bytes of `value`: seven bits at a time, the lowest first, the high bit of a byte saying that more follow. -/
def putNat (out : ByteArray) (value : Nat) : ByteArray :=
  if value < 128 then out.push value.toUInt8
  else putNat (out.push (value % 128 + 128).toUInt8) (value / 128)
termination_by value
decreasing_by omega

/-- The rest of a number, of which `value` was read, the next byte counting `scale`. -/
def getNatFrom (data : ByteArray) (pos value scale : Nat) : Option (Nat × Nat) :=
  if h : pos < data.size then
    let byte := data[pos].toNat
    if byte < 128 then some (value + byte * scale, pos + 1)
    else getNatFrom data (pos + 1) (value + (byte - 128) * scale) (scale * 128)
  else none
termination_by data.size - pos

@[inline] def getNat (data : ByteArray) (pos : Nat) : Option (Nat × Nat) :=
  if h : pos < data.size then
    let byte := data[pos].toNat
    if byte < 128 then some (byte, pos + 1)
    else getNatFrom data (pos + 1) (byte - 128) 128
  else none

@[inline] def getByte (data : ByteArray) (pos : Nat) : Option (UInt8 × Nat) :=
  if h : pos < data.size then some (data[pos], pos + 1) else none

@[inline] def putBool (out : ByteArray) (value : Bool) : ByteArray :=
  out.push (if value then 1 else 0)

@[inline] def getBool (data : ByteArray) (pos : Nat) : Option (Bool × Nat) :=
  match getByte data pos with
  | some (0, next) => some (false, next)
  | some (1, next) => some (true, next)
  | _ => none

def putBytes (out bytes : ByteArray) : ByteArray :=
  putNat out bytes.size ++ bytes

def getBytes (data : ByteArray) (pos : Nat) : Option (ByteArray × Nat) := do
  let (size, pos) ← getNat data pos
  if pos + size ≤ data.size then some (data.extract pos (pos + size), pos + size) else none

def putText (out : ByteArray) (text : String) : ByteArray :=
  putBytes out text.toUTF8

def getText (data : ByteArray) (pos : Nat) : Option (String × Nat) := do
  let (bytes, pos) ← getBytes data pos
  let text ← String.fromUTF8? bytes
  some (text, pos)

/-! ### Lists -/

def putItems {α : Type} (put : ByteArray → α → ByteArray) (out : ByteArray) : List α → ByteArray
  | [] => out
  | item :: rest => putItems put (put out item) rest

def putList {α : Type} (put : ByteArray → α → ByteArray) (out : ByteArray) (items : List α) : ByteArray :=
  putItems put (putNat out items.length) items

/-- `count` items, on top of those in `done`. A file can't say to read more items than it has bytes: each takes one. -/
def getItems {α : Type} (get : Nat → Option (α × Nat)) : Nat → Nat → Array α → Option (Array α × Nat)
  | 0, pos, done => some (done, pos)
  | count + 1, pos, done =>
    match get pos with
    | some (item, next) => getItems get count next (done.push item)
    | none => none

@[inline] def getArray {α : Type} (get : Nat → Option (α × Nat)) (data : ByteArray) (pos : Nat) : Option (Array α × Nat) := do
  let (count, pos) ← getNat data pos
  getItems get count pos #[]

@[inline] def getList {α : Type} (get : Nat → Option (α × Nat)) (data : ByteArray) (pos : Nat) : Option (List α × Nat) := do
  let (items, pos) ← getArray get data pos
  some (items.toList, pos)

def putOption {α : Type} (put : ByteArray → α → ByteArray) (out : ByteArray) : Option α → ByteArray
  | none => out.push 0
  | some value => put (out.push 1) value

@[inline] def getOption {α : Type} (get : Nat → Option (α × Nat)) (data : ByteArray) (pos : Nat) : Option (Option α × Nat) :=
  match getByte data pos with
  | some (0, next) => some (none, next)
  | some (1, next) =>
    match get next with
    | some (value, next) => some (some value, next)
    | none => none
  | _ => none

/-! ### Tables -/

/-- Values stored once, and an index that finds them by their hash. That compares no values, which are large, except where
a value is looked up. A value with the hash of another stays out of the table. -/
structure Table (α : Type) where
  items : Array α := #[]
  index : Std.HashMap UInt64 Nat := {}

/-- A new value goes at the end. -/
def Table.add {α : Type} [Hashable α] : Table α → α → Table α
  | ⟨items, index⟩, value =>
    let key := hash value
    if index.contains key then ⟨items, index⟩
    else
      let position := items.size
      ⟨items.push value, index.insert key position⟩

/-- `add`, which tells where the value may be. -/
def Table.place {α : Type} [Hashable α] : Table α → α → Table α × Nat
  | ⟨items, index⟩, value =>
    let key := hash value
    match index.get? key with
    | some position => (⟨items, index⟩, position)
    | none =>
      let position := items.size
      (⟨items.push value, index.insert key position⟩, position)

/-- A value by its position in the table and one more, or else 0 and the value. `position` is where it may be: this looks
at what it finds there, so that nothing has to hold of how it was found. -/
@[inline] def putAt {α : Type} [BEq α] (put : ByteArray → α → ByteArray) (items : Array α) (position : Nat)
    (out : ByteArray) (value : α) : ByteArray :=
  match items[position]? with
  | some found => if found == value then putNat out (position + 1) else put (putNat out 0) value
  | none => put (putNat out 0) value

@[inline] def getRef {α : Type} (get : Nat → Option (α × Nat)) (items : Array α) (data : ByteArray) (pos : Nat) : Option (α × Nat) :=
  match getNat data pos with
  | some (0, next) => get next
  | some (position + 1, next) =>
    match items[position]? with
    | some value => some (value, next)
    | none => none
  | none => none

/-! ### Types and variables -/

@[inline] def putEndian (out : ByteArray) : Endian → ByteArray
  | .little => out.push 0
  | .big => out.push 1

@[inline] def getEndian (data : ByteArray) (pos : Nat) : Option (Endian × Nat) :=
  match getByte data pos with
  | some (0, next) => some (.little, next)
  | some (1, next) => some (.big, next)
  | _ => none

def putTyp (out : ByteArray) : Typ → ByteArray
  | .unknown => out.push 0
  | .unit => out.push 1
  | .mem addressWidth valueWidth => putNat (putNat (out.push 2) addressWidth) valueWidth
  | .imm width => putNat (out.push 3) width

def getTyp (data : ByteArray) (pos : Nat) : Option (Typ × Nat) :=
  match getByte data pos with
  | some (0, next) => some (.unknown, next)
  | some (1, next) => some (.unit, next)
  | some (2, next) => do
    let (addressWidth, next) ← getNat data next
    let (valueWidth, next) ← getNat data next
    some (.mem addressWidth valueWidth, next)
  | some (3, next) => do
    let (width, next) ← getNat data next
    some (.imm width, next)
  | _ => none

def putVar (out : ByteArray) (var : Bap.Var) : ByteArray :=
  putBool (putNat (putTyp (putText out var.name) var.typ) var.index) var.isVirtual

def getVar (data : ByteArray) (pos : Nat) : Option (Bap.Var × Nat) := do
  let (name, pos) ← getText data pos
  let (typ, pos) ← getTyp data pos
  let (index, pos) ← getNat data pos
  let (isVirtual, pos) ← getBool data pos
  some (⟨name, typ, index, isVirtual⟩, pos)

/-- A variable, by where the table has one of its hash. -/
@[inline] def putVarRef (vars : Table Bap.Var) (out : ByteArray) (var : Bap.Var) : ByteArray :=
  putAt putVar vars.items ((vars.index.get? (hash var)).getD 0) out var

/-! ### Expressions -/

@[inline] def castCode : Cast → UInt8
  | .low => 0
  | .high => 1
  | .signed => 2
  | .unsigned => 3

@[inline] def castOf? : UInt8 → Option Cast
  | 0 => some .low
  | 1 => some .high
  | 2 => some .signed
  | 3 => some .unsigned
  | _ => none

@[inline] def unCode : UnOp → UInt8
  | .neg => 0
  | .not => 1

@[inline] def unOf? : UInt8 → Option UnOp
  | 0 => some .neg
  | 1 => some .not
  | _ => none

def binCode : BinOp → UInt8
  | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .sdiv => 4 | .rem => 5 | .srem => 6 | .smod => 7
  | .lshift => 8 | .rshift => 9 | .ashift => 10 | .and => 11 | .or => 12 | .xor => 13 | .eq => 14 | .neq => 15
  | .lt => 16 | .le => 17 | .gt => 18 | .ge => 19 | .slt => 20 | .sle => 21 | .sgt => 22 | .sge => 23

def binOf? : UInt8 → Option BinOp
  | 0 => some .add | 1 => some .sub | 2 => some .mul | 3 => some .div | 4 => some .sdiv | 5 => some .rem
  | 6 => some .srem | 7 => some .smod | 8 => some .lshift | 9 => some .rshift | 10 => some .ashift
  | 11 => some .and | 12 => some .or | 13 => some .xor | 14 => some .eq | 15 => some .neq | 16 => some .lt
  | 17 => some .le | 18 => some .gt | 19 => some .ge | 20 => some .slt | 21 => some .sle | 22 => some .sgt
  | 23 => some .sge | _ => none

def putExp (vars : Table Bap.Var) (out : ByteArray) : Exp → ByteArray
  | .int (width := width) value => putNat (putNat (out.push 0) width) value.toNat
  | .var var => putVarRef vars (out.push 1) var
  | .load memory address endian size =>
    putNat (putEndian (putExp vars (putExp vars (out.push 2) memory) address) endian) size
  | .store memory address value endian size =>
    putNat (putEndian (putExp vars (putExp vars (putExp vars (out.push 3) memory) address) value) endian) size
  | .bin op left right => putExp vars (putExp vars ((out.push 4).push (binCode op)) left) right
  | .un op value => putExp vars ((out.push 5).push (unCode op)) value
  | .cast kind width value => putExp vars (putNat ((out.push 6).push (castCode kind)) width) value
  | .letIn var value body => putExp vars (putExp vars (putVarRef vars (out.push 7) var) value) body
  | .ite condition yes no => putExp vars (putExp vars (putExp vars (out.push 8) condition) yes) no
  | .extract high low value => putExp vars (putNat (putNat (out.push 9) high) low) value
  | .concat left right => putExp vars (putExp vars (out.push 10) left) right
  | .unknown message typ => putTyp (putText (out.push 11) message) typ

/-- The reader goes as deep as this, which is how deep the writer lets BIL be, so that a file can't overflow the stack. -/
def maxDepth : Nat := 4096

def getExp (vars : Array Bap.Var) (data : ByteArray) : Nat → Nat → Option (Exp × Nat)
  | 0, _ => none
  | fuel + 1, pos => do
    let (tag, pos) ← getByte data pos
    match tag with
    | 0 =>
      let (width, pos) ← getNat data pos
      let (value, pos) ← getNat data pos
      if value >>> width = 0 then some (.int (BitVec.ofNat width value), pos) else none
    | 1 =>
      let (var, pos) ← getRef (getVar data) vars data pos
      some (.var var, pos)
    | 2 =>
      let (memory, pos) ← getExp vars data fuel pos
      let (address, pos) ← getExp vars data fuel pos
      let (endian, pos) ← getEndian data pos
      let (size, pos) ← getNat data pos
      some (.load memory address endian size, pos)
    | 3 =>
      let (memory, pos) ← getExp vars data fuel pos
      let (address, pos) ← getExp vars data fuel pos
      let (value, pos) ← getExp vars data fuel pos
      let (endian, pos) ← getEndian data pos
      let (size, pos) ← getNat data pos
      some (.store memory address value endian size, pos)
    | 4 =>
      let (code, pos) ← getByte data pos
      let op ← binOf? code
      let (left, pos) ← getExp vars data fuel pos
      let (right, pos) ← getExp vars data fuel pos
      some (.bin op left right, pos)
    | 5 =>
      let (code, pos) ← getByte data pos
      let op ← unOf? code
      let (value, pos) ← getExp vars data fuel pos
      some (.un op value, pos)
    | 6 =>
      let (code, pos) ← getByte data pos
      let kind ← castOf? code
      let (width, pos) ← getNat data pos
      let (value, pos) ← getExp vars data fuel pos
      some (.cast kind width value, pos)
    | 7 =>
      let (var, pos) ← getRef (getVar data) vars data pos
      let (value, pos) ← getExp vars data fuel pos
      let (body, pos) ← getExp vars data fuel pos
      some (.letIn var value body, pos)
    | 8 =>
      let (condition, pos) ← getExp vars data fuel pos
      let (yes, pos) ← getExp vars data fuel pos
      let (no, pos) ← getExp vars data fuel pos
      some (.ite condition yes no, pos)
    | 9 =>
      let (high, pos) ← getNat data pos
      let (low, pos) ← getNat data pos
      let (value, pos) ← getExp vars data fuel pos
      some (.extract high low value, pos)
    | 10 =>
      let (left, pos) ← getExp vars data fuel pos
      let (right, pos) ← getExp vars data fuel pos
      some (.concat left right, pos)
    | 11 =>
      let (message, pos) ← getText data pos
      let (typ, pos) ← getTyp data pos
      some (.unknown message typ, pos)
    | _ => none

/-- How deep the reader has to go for an expression. -/
def expDepth : Exp → Nat
  | .int _ | .var _ | .unknown .. => 1
  | .load memory address .. => 1 + max (expDepth memory) (expDepth address)
  | .store memory address value .. => 1 + max (expDepth memory) (max (expDepth address) (expDepth value))
  | .bin _ left right | .concat left right => 1 + max (expDepth left) (expDepth right)
  | .un _ value | .cast _ _ value | .extract _ _ value => 1 + expDepth value
  | .letIn _ value body => 1 + max (expDepth value) (expDepth body)
  | .ite condition yes no => 1 + max (expDepth condition) (max (expDepth yes) (expDepth no))

/-! ### Statements -/

mutual
  def putStmt (vars : Table Bap.Var) (out : ByteArray) : Stmt → ByteArray
    | .move var value => putExp vars (putVarRef vars (out.push 0) var) value
    | .jmp target => putExp vars (out.push 1) target
    | .special message => putText (out.push 2) message
    | .while condition body => putStmts vars (putNat (putExp vars (out.push 3) condition) body.length) body
    | .ifElse condition yes no =>
      putStmts vars (putNat (putStmts vars (putNat (putExp vars (out.push 4) condition) yes.length) yes) no.length) no
    | .cpuExn number => putNat (out.push 5) number

  /-- `putItems` of `putStmt`. -/
  def putStmts (vars : Table Bap.Var) (out : ByteArray) : List Stmt → ByteArray
    | [] => out
    | stmt :: rest => putStmts vars (putStmt vars out stmt) rest
end

def putProgram (vars : Table Bap.Var) (out : ByteArray) (program : Program) : ByteArray :=
  putStmts vars (putNat out program.length) program

def getStmt (vars : Array Bap.Var) (data : ByteArray) : Nat → Nat → Option (Stmt × Nat)
  | 0, _ => none
  | fuel + 1, pos => do
    let (tag, pos) ← getByte data pos
    match tag with
    | 0 =>
      let (var, pos) ← getRef (getVar data) vars data pos
      let (value, pos) ← getExp vars data fuel pos
      some (.move var value, pos)
    | 1 =>
      let (target, pos) ← getExp vars data fuel pos
      some (.jmp target, pos)
    | 2 =>
      let (message, pos) ← getText data pos
      some (.special message, pos)
    | 3 =>
      let (condition, pos) ← getExp vars data fuel pos
      let (body, pos) ← getList (getStmt vars data fuel) data pos
      some (.while condition body, pos)
    | 4 =>
      let (condition, pos) ← getExp vars data fuel pos
      let (yes, pos) ← getList (getStmt vars data fuel) data pos
      let (no, pos) ← getList (getStmt vars data fuel) data pos
      some (.ifElse condition yes no, pos)
    | 5 =>
      let (number, pos) ← getNat data pos
      some (.cpuExn number, pos)
    | _ => none

@[inline] def getProgram (vars : Array Bap.Var) (data : ByteArray) (pos : Nat) : Option (Program × Nat) :=
  getList (getStmt vars data maxDepth) data pos

mutual
  /-- How deep the reader has to go for a statement. -/
  def stmtDepth : Stmt → Nat
    | .move _ value | .jmp value => 1 + expDepth value
    | .special _ | .cpuExn _ => 1
    | .while condition body => 1 + max (expDepth condition) (stmtsDepth body)
    | .ifElse condition yes no => 1 + max (expDepth condition) (max (stmtsDepth yes) (stmtsDepth no))

  def stmtsDepth : List Stmt → Nat
    | [] => 0
    | stmt :: rest => max (stmtDepth stmt) (stmtsDepth rest)
end

/-! ### The variables of a program -/

/-- The variables of an expression, for a table. It can leave out some, which are then stored where they are used. -/
def addExpVars (vars : Table Bap.Var) : Exp → Table Bap.Var
  | .int _ | .unknown .. => vars
  | .var var => vars.add var
  | .load memory address .. => addExpVars (addExpVars vars memory) address
  | .store memory address value .. => addExpVars (addExpVars (addExpVars vars memory) address) value
  | .bin _ left right | .concat left right => addExpVars (addExpVars vars left) right
  | .un _ value | .cast _ _ value | .extract _ _ value => addExpVars vars value
  | .letIn var value body => addExpVars (addExpVars (vars.add var) value) body
  | .ite condition yes no => addExpVars (addExpVars (addExpVars vars condition) yes) no

mutual
  def addStmtVars (vars : Table Bap.Var) : Stmt → Table Bap.Var
    | .move var value => addExpVars (vars.add var) value
    | .jmp value => addExpVars vars value
    | .special _ | .cpuExn _ => vars
    | .while condition body => addProgramVars (addExpVars vars condition) body
    | .ifElse condition yes no => addProgramVars (addProgramVars (addExpVars vars condition) yes) no

  def addProgramVars (vars : Table Bap.Var) : List Stmt → Table Bap.Var
    | [] => vars
    | stmt :: rest => addProgramVars (addStmtVars vars stmt) rest
end

/-! ### What identifies a program, to find it in a table -/

private def hashExp : Exp → UInt64
  | .int (width := width) value => mixHash (hash width) (hash value.toNat)
  | .var var => hash var
  | .load memory address _ size => mixHash (mixHash (hashExp memory) (hashExp address)) (hash size)
  | .store memory address value _ size =>
    mixHash (mixHash (mixHash (hashExp memory) (hashExp address)) (hashExp value)) (hash size)
  | .bin op left right => mixHash (binCode op).toUInt64 (mixHash (hashExp left) (hashExp right))
  | .un op value => mixHash (unCode op + 32).toUInt64 (hashExp value)
  | .cast kind width value => mixHash (castCode kind + 64).toUInt64 (mixHash (hash width) (hashExp value))
  | .letIn var value body => mixHash (hash var) (mixHash (hashExp value) (hashExp body))
  | .ite condition yes no => mixHash (hashExp condition) (mixHash (hashExp yes) (hashExp no))
  | .extract high low value => mixHash (hash high) (mixHash (hash low) (hashExp value))
  | .concat left right => mixHash 96 (mixHash (hashExp left) (hashExp right))
  | .unknown message _ => hash message

mutual
  private def hashStmt : Stmt → UInt64
    | .move var value => mixHash (hash var) (hashExp value)
    | .jmp target => mixHash 1 (hashExp target)
    | .special message => hash message
    | .while condition body => mixHash (hashExp condition) (hashStmts body)
    | .ifElse condition yes no => mixHash (hashExp condition) (mixHash (hashStmts yes) (hashStmts no))
    | .cpuExn number => mixHash 2 (hash number)

  private def hashStmts : List Stmt → UInt64
    | [] => 7
    | stmt :: rest => mixHash (hashStmt stmt) (hashStmts rest)
end

instance : Hashable Program := ⟨hashStmts⟩

end Bap.Binary

namespace Bap.Bil

mutual
  /-- Whether two statements are the same. `same_eq` says that it is equality. -/
  def Stmt.same : Stmt → Stmt → Bool
    | .move var value, .move otherVar other => var = otherVar && value = other
    | .jmp target, .jmp other => decide (target = other)
    | .special message, .special other => message = other
    | .while condition body, .while otherCondition otherBody => condition = otherCondition && Stmt.sameAll body otherBody
    | .ifElse condition yes no, .ifElse otherCondition otherYes otherNo =>
      condition = otherCondition && Stmt.sameAll yes otherYes && Stmt.sameAll no otherNo
    | .cpuExn number, .cpuExn other => number = other
    | _, _ => false

  def Stmt.sameAll : List Stmt → List Stmt → Bool
    | [], [] => true
    | stmt :: rest, other :: others => Stmt.same stmt other && Stmt.sameAll rest others
    | _, _ => false
end

mutual
  theorem Stmt.same_eq : (first second : Stmt) → Stmt.same first second = true → first = second
    | .move _ _, .move _ _, h => by
      simp only [Stmt.same, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, h.2]
    | .move _ _, .jmp _, h | .move _ _, .special _, h | .move _ _, .while _ _, h | .move _ _, .ifElse _ _ _, h
    | .move _ _, .cpuExn _, h | .jmp _, .move _ _, h | .jmp _, .special _, h | .jmp _, .while _ _, h
    | .jmp _, .ifElse _ _ _, h | .jmp _, .cpuExn _, h | .special _, .move _ _, h | .special _, .jmp _, h
    | .special _, .while _ _, h | .special _, .ifElse _ _ _, h | .special _, .cpuExn _, h
    | .while _ _, .move _ _, h | .while _ _, .jmp _, h | .while _ _, .special _, h | .while _ _, .ifElse _ _ _, h
    | .while _ _, .cpuExn _, h | .ifElse _ _ _, .move _ _, h | .ifElse _ _ _, .jmp _, h | .ifElse _ _ _, .special _, h
    | .ifElse _ _ _, .while _ _, h | .ifElse _ _ _, .cpuExn _, h | .cpuExn _, .move _ _, h | .cpuExn _, .jmp _, h
    | .cpuExn _, .special _, h | .cpuExn _, .while _ _, h | .cpuExn _, .ifElse _ _ _, h => by simp [Stmt.same] at h
    | .jmp _, .jmp _, h => by
      simp only [Stmt.same, decide_eq_true_eq] at h
      rw [h]
    | .special _, .special _, h => by
      simp only [Stmt.same, decide_eq_true_eq] at h
      rw [h]
    | .while _ first, .while _ second, h => by
      simp only [Stmt.same, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, Stmt.sameAll_eq first second h.2]
    | .ifElse _ a b, .ifElse _ c d, h => by
      simp only [Stmt.same, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1.1, Stmt.sameAll_eq a c h.1.2, Stmt.sameAll_eq b d h.2]
    | .cpuExn _, .cpuExn _, h => by
      simp only [Stmt.same, decide_eq_true_eq] at h
      rw [h]

  theorem Stmt.sameAll_eq : (first second : List Stmt) → Stmt.sameAll first second = true → first = second
    | [], [], _ => rfl
    | _ :: _, [], h | [], _ :: _, h => by simp [Stmt.sameAll] at h
    | stmt :: rest, other :: others, h => by
      simp only [Stmt.sameAll, Bool.and_eq_true] at h
      rw [Stmt.same_eq stmt other h.1, Stmt.sameAll_eq rest others h.2]
end

instance : BEq Program := ⟨Stmt.sameAll⟩

end Bap.Bil

namespace Bap.Binary

/-- The value of the table that is the same as `value`, so that the same code is held once, or else `value`, which is put in the table. Which of
them it is, `share_eq` says doesn't matter. -/
def share (table : Table Bil.Program) (value : Bil.Program) : Table Bil.Program × Bil.Program :=
  let (table, position) := table.place value
  match table.items[position]? with
  | some found => if found == value then (table, found) else (table, value)
  | none => (table, value)

/-- It is `value` itself. -/
theorem share_eq (table : Table Bil.Program) (value : Bil.Program) : (share table value).2 = value := by
  simp only [share]
  split
  · split
    · next found _ hb => exact Bil.Stmt.sameAll_eq _ _ hb
    · rfl
  · rfl

end Bap.Binary
