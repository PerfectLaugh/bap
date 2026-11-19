import Bap.Analysis.Xrefs
import Bap.Image.Elf
import Bap.Symbolic.Executor
import Bap.Proofs.Symbolic

/-! # The partition of a program into functions

What ROSE's `Partitioner2` does of the code of an image, on the instructions and edges of BAP's scan: the targets of the indirect
jumps that go through a table, which the scan then goes on from; each function as the instructions its entry reaches without
going into another function; the functions that never return, so that what follows a call of one isn't of its caller; tail
calls; thunks, which only jump on to another function; and the stubs of the imports of an ELF file, by the slot of the global
offset table that each jumps through.

A jump table is found by running what leads to an indirect jump symbolically, back to where control could come from more than
one place: the target is then an expression of the inputs, whose read of memory, if it has one, is at `base + scale * index`.
The index is a register, or a part or an extension of one, with a constant added or taken away, which each value of it is had
of. The values of the index are tried from 0 as long as the conditions of the path, e.g., the comparison with the bound of a
`switch`, which are of that register alone, hold, each target read of the table in the image. Without such a condition the
table goes on as long as its targets are in the code. -/

namespace Bap.Analysis.Partition

open Bap.Symbolic

/-- The functions that don't return, of the C library, by their names, which the imports and the symbols of a program have. -/
def noReturnNames : List String :=
  ["exit", "_exit", "_Exit", "abort", "quick_exit", "__assert_fail", "__assert_perror_fail", "__assert", "__stack_chk_fail",
    "__stack_chk_fail_local", "__fortify_fail", "__chk_fail", "longjmp", "siglongjmp", "_longjmp", "__longjmp_chk",
    "pthread_exit", "__cxa_throw", "__cxa_rethrow", "__cxa_bad_cast", "__cxa_bad_typeid", "__cxa_call_unexpected",
    "_Unwind_Resume", "__libc_start_main", "err", "errx", "verr", "verrx", "__libc_fatal", "_ZSt9terminatev",
    "__cxa_pure_virtual", "__ubsan_handle_builtin_unreachable"]

/-- A jump through a table: the jump, the table, if it was read, whether a condition of the path bounded it, and its targets. -/
structure JumpTable where
  jump : Nat
  table : Option Nat
  bounded : Bool
  targets : List Nat
  deriving Repr, BEq

/-- A function of a partition. -/
structure Function where
  entry : Nat
  name : String
  /-- The addresses of its instructions, in order. -/
  instructions : List Nat
  /-- Whether it may return to its caller: by a return, or by a tail call of one that may. -/
  returns : Bool
  /-- The function a thunk jumps on to. -/
  thunkOf : Option Nat := none
  /-- The import a stub jumps to, by its name. -/
  importName : Option String := none
  /-- The jumps from it to the entries of other functions, with their targets. -/
  tailCalls : List (Nat × Nat) := []
  /-- The direct calls from it, with what they call. -/
  calls : List (Nat × Nat) := []
  deriving Repr

/-- What a partition found: the functions, the jump tables, the indirect jumps that no table was found of and that aren't of a
stub, and the edges of the flow of control within functions, the jumps of the tables among them, without what follows a call of
a function that doesn't return. -/
structure Partition where
  functions : List Function
  tables : List JumpTable
  /-- The indirect jumps through a slot of memory at a constant address, e.g., of the global offset table, with the slot and the
  import it is of, if it is one: tail calls through a pointer, which isn't of the code. -/
  slotJumps : List (Nat × Nat × Option String)
  unresolved : List Nat
  edges : List (Nat × Nat)
  disasm : Disasm.Disasm

/-- Each of a list once, in the order of its first, in the time of a pass, which `List.eraseDups` isn't. -/
def dedup {α : Type} [BEq α] [Hashable α] (items : List α) : List α :=
  (items.foldl (init := (({} : Std.HashSet α), ([] : List α))) fun (seen, kept) item =>
    if seen.contains item then (seen, kept) else (seen.insert item, item :: kept)).2.reverse

/-! ## The image -/

/-- The byte of the image at an address, of the first region that has it. -/
def imageByte (image : Image.Image) (address : Nat) : Option Nat :=
  (image.memory.entries.find? fun entry => entry.1.contains address).map fun entry =>
    (entry.1.data.get! (address - entry.1.addr)).toNat

/-- Whether an address can start an instruction of the image: in executable memory and aligned as its instructions are. -/
def inCode (image : Image.Image) (address : Nat) : Bool :=
  let alignment := match image.arch with
    | .x86 | .x86_64 => 1
    | .arm | .riscv => 2
    | _ => 4
  address % alignment == 0 && image.memory.entries.any fun entry => entry.1.executable && entry.1.contains address

/-! ## Evaluating the expressions of the symbolic executor -/

/-- The variables of an expression, by name. -/
def varsOf (expr : Expr) : List String := dedup (expr.vars.map Prod.fst)

/-- The addresses that an expression reads of the initial memory. -/
partial def selectsOf : Expr → List Expr
  | .select _ address => address :: selectsOf address
  | .app _ _ args => args.flatMap selectsOf
  | .extract _ _ value => selectsOf value
  | .concat left right => selectsOf left ++ selectsOf right
  | .ite condition yes no => selectsOf condition ++ selectsOf yes ++ selectsOf no
  | _ => []

/-- The assignment of a value to one variable, zero to the others, and the bytes of the image to the initial memory. -/
def assignment (image : Image.Image) (name : String) (value : Nat) : Proofs.Symbolic.Assignment where
  var other width := if other == name then BitVec.ofNat width value else 0
  memory _ _ address := BitVec.ofNat 8 ((imageByte image address.toNat).getD 0)

/-- The number an expression has under an assignment. -/
def valueOf (σ : Proofs.Symbolic.Assignment) (expr : Expr) : Nat := (Proofs.Symbolic.denote σ expr).2.toNat

/-- Whether all that an expression reads of memory is in the image, under an assignment. -/
def readsMapped (image : Image.Image) (σ : Proofs.Symbolic.Assignment) (expr : Expr) : Bool :=
  (selectsOf expr).all fun address => (imageByte image (valueOf σ address)).isSome

/-- Whether an expression has no input: no variable and no read of memory. -/
partial def closed : Expr → Bool
  | .var _ _ | .select _ _ => false
  | .const _ => true
  | .app _ _ args => args.all closed
  | .extract _ _ value => closed value
  | .concat left right => closed left && closed right
  | .ite condition yes no => closed condition && closed yes && closed no

/-- What the executor leaves of constants that are cast, which it folds only of its operations: each closed part folded to its
value, an `extract` of all the bits dropped, an `extract` of a `concat` of the part it is of and of an `extract` of what that is
of, as a bit of a condition register that a lifter makes of its fields, and a sum, `or` or shift with zero, and a product with
one, its other operand. -/
partial def simplify (expr : Expr) : Expr :=
  let zeros : Proofs.Symbolic.Assignment := { var := fun _ _ => 0, memory := fun _ _ _ => 0 }
  let fold (expr : Expr) : Expr :=
    if closed expr then
      let value := Proofs.Symbolic.denote zeros expr
      .const value.2
    else expr
  let isConst (expr : Expr) (value : Nat) : Bool :=
    match expr with
    | .const bits => bits.toNat == value
    | _ => false
  match expr with
  | .extract high low value =>
    let value := simplify value
    if low == 0 && value.width == high + 1 then value
    else match value with
      | .concat left right =>
        let width := right.width
        if low ≥ width then simplify (.extract (high - width) (low - width) left)
        else if high < width then simplify (.extract high low right)
        else fold (.extract high low value)
      | .extract _ low' inner => simplify (.extract (high + low') (low + low') inner)
      | _ => fold (.extract high low value)
  | .app name width args =>
    let args := args.map simplify
    match name, args with
    | "bvadd", [left, right] | "bvor", [left, right] | "bvxor", [left, right] =>
      if isConst left 0 && right.width == width then right
      else if isConst right 0 && left.width == width then left else fold (.app name width args)
    | "bvsub", [left, right] | "bvshl", [left, right] | "bvlshr", [left, right] | "bvashr", [left, right] =>
      if isConst right 0 && left.width == width then left else fold (.app name width args)
    | "bvmul", [left, right] =>
      if isConst left 1 && right.width == width then right
      else if isConst right 1 && left.width == width then left else fold (.app name width args)
    | _, _ => fold (.app name width args)
  | .concat left right => fold (.concat (simplify left) (simplify right))
  | .ite condition yes no => fold (.ite (simplify condition) (simplify yes) (simplify no))
  | .select memory address => .select memory (simplify address)
  | _ => expr

/-- Whether an expression has a part that is another. -/
partial def hasPart (part : Expr) (expr : Expr) : Bool :=
  Expr.structuralEq part expr || match expr with
    | .app _ _ args => args.any (hasPart part)
    | .extract _ _ value => hasPart part value
    | .concat left right => hasPart part left || hasPart part right
    | .ite condition yes no => hasPart part condition || hasPart part yes || hasPart part no
    | .select _ address => hasPart part address
    | _ => false

/-- An expression with each of a part replaced by another. -/
partial def replace (part value : Expr) (expr : Expr) : Expr :=
  if Expr.structuralEq part expr then value else
  match expr with
  | .app name width args => .app name width (args.map (replace part value))
  | .extract high low inner => .extract high low (replace part value inner)
  | .concat left right => .concat (replace part value left) (replace part value right)
  | .ite condition yes no => .ite (replace part value condition) (replace part value yes) (replace part value no)
  | .select memory address => .select memory (replace part value address)
  | _ => expr

/-! ## The index of a table -/

/-- An address as `offset + scale * index`, of a constant offset and scale: what isn't a sum, a product or a shift by a
constant is the index. What is scaled is the index whole, as what is added in it, e.g., the least case of a `switch` taken
away, is of the index that its bound is of, and not of the offset of the table. -/
partial def affine (expr : Expr) (scaled : Bool := false) : Nat × Nat × Expr :=
  match expr with
  | .extract high 0 value => if value.width == high + 1 then affine value scaled else (0, 1, expr)
  | .app "bvmul" _ [left, @Expr.const _ value] =>
    let (offset, scale, index) := affine left true
    (offset * value.toNat, scale * value.toNat, index)
  | .app "bvmul" _ [@Expr.const _ value, right] =>
    let (offset, scale, index) := affine right true
    (offset * value.toNat, scale * value.toNat, index)
  | .app "bvshl" _ [left, @Expr.const _ value] =>
    let (offset, scale, index) := affine left true
    (offset * 2 ^ value.toNat, scale * 2 ^ value.toNat, index)
  | .app "bvadd" _ [left, @Expr.const _ value] =>
    if scaled then (0, 1, expr) else
    let (offset, scale, index) := affine left
    (offset + value.toNat, scale, index)
  | .app "bvadd" _ [@Expr.const _ value, right] =>
    if scaled then (0, 1, expr) else
    let (offset, scale, index) := affine right
    (offset + value.toNat, scale, index)
  | .app "bvsub" width [left, @Expr.const _ value] =>
    if scaled then (0, 1, expr) else
    let (offset, scale, index) := affine left
    (offset + 2 ^ width - value.toNat, scale, index)
  | _ => (0, 1, expr)

/-- The input and its value that give an index the value `index`: the index is the input, a part of it from bit 0, an
extension of it, or it with a constant added, taken away or masked off, which isn't more than the mask. The input is what is
none of these: a register, or what was read of memory, e.g., an argument on the stack. -/
partial def invert (expr : Expr) (index : Nat) : Option (Expr × Nat) :=
  let modulus := 2 ^ expr.width
  if index ≥ modulus then none else
  match expr with
  | .const _ => none
  | .extract _ 0 value => invert value index
  | .app "bvshl" _ [value, @Expr.const _ amount] =>
    if index % 2 ^ amount.toNat == 0 then invert value (index / 2 ^ amount.toNat) else none
  | .app name _ [value] =>
    if name.startsWith "(_ zero_extend" || name.startsWith "(_ sign_extend" then
      if index < 2 ^ value.width then invert value index else none
    else none
  | .app "bvadd" _ [left, @Expr.const _ value] => invert left ((index + modulus - value.toNat % modulus) % modulus)
  | .app "bvadd" _ [@Expr.const _ value, right] => invert right ((index + modulus - value.toNat % modulus) % modulus)
  | .app "bvsub" _ [left, @Expr.const _ value] => invert left ((index + value.toNat) % modulus)
  | .app "bvand" _ [left, @Expr.const _ value] => if index &&& value.toNat == index then invert left index else none
  | _ => some (expr, index)

/-- The index of the targets of a jump, of its reads of memory, or of the target itself if it reads none, and where the
reads start, the least of their offsets. -/
def indexOf (target : Expr) : Option (Nat × Expr) :=
  let parts := match selectsOf target with
    | [] => [affine target]
    | addresses => addresses.map affine
  -- the reads of the table, of the index of the outermost: an index read of memory is read at an address of its own
  match parts.head? with
  | none => none
  | some (offset, _, index) =>
    match index with
    | .const _ => none
    | _ =>
      let ofTable := parts.filter fun part => Expr.structuralEq part.2.2 index
      some ((ofTable.map (·.1)).foldl min offset, index)

/-- The most entries a table is read for. -/
def maxEntries : Nat := 4096

/-- The most entries of a table that no condition bounds, which goes on as long as its targets are near its jump. -/
def maxUnbounded : Nat := 512

/-- The targets of a jump to `target` under the conditions of its path, as the index of it goes from 0: while the conditions
that are of the variable of the index alone hold, or else while the targets are in the code, each in the code, and of the
first read of the table. A table is of one variable, which the target has nothing else of. -/
def tableTargets (image : Image.Image) (target : Expr) (constraints : List Expr) (near : Nat × Nat := (0, 0)) :
    Option (Option Nat × Bool × List Nat) := do
  let target := simplify target
  let constraints := constraints.map simplify
  let (table, index) ← indexOf target
  let (input, _) ← invert index 0
  -- of a value of the input, the target and the conditions that are of nothing else
  let given (value : Nat) : Expr × List Expr :=
    let constant : Expr := .const (BitVec.ofNat input.width value)
    let target := simplify (replace input constant target)
    let conditions := (constraints.filter (hasPart input)).map fun condition => simplify (replace input constant condition)
    (target, conditions.filter fun condition => (varsOf condition).isEmpty)
  if !(varsOf (given 0).1).isEmpty then none
  let bounded := !(given 0).2.isEmpty
  let σ := assignment image "" 0
  -- what the conditions allow first, of a table of a least index above 0
  let holds (current : Nat) : Bool :=
    match invert index current with
    | some (_, value) => (given value).2.all fun condition => valueOf σ condition == 1
    | none => false
  let first := if bounded then ((List.range maxEntries).find? holds).getD maxEntries else 0
  let rec go : Nat → Nat → List Nat → Option (List Nat)
    | 0, _, found => if bounded then none else some found.reverse
    | fuel + 1, current, found =>
      match invert index current with
      | none => some found.reverse
      | some (_, value) =>
        let (target, conditions) := given value
        if !conditions.all (fun condition => valueOf σ condition == 1) then
          if bounded then some found.reverse else go fuel (current + 1) found
        else if !readsMapped image σ target then
          if bounded then none else some found.reverse
        else
          let address := valueOf σ target
          if inCode image address && (bounded || near.1 ≤ address && address < near.2) then
            go fuel (current + 1) (address :: found)
          else if bounded then none else some found.reverse
  let targets ← go (if bounded then maxEntries else maxUnbounded) first []
  if targets.isEmpty then none
  let table := if (selectsOf target).isEmpty then none else some (table % 2 ^ image.addrWidth)
  some (table, bounded, dedup targets)

/-! ## The flow of control -/

/-- The instructions of a scan by address, and the edges into each. -/
structure Graph where
  instructions : Std.HashMap Nat Disasm.Insn
  successors : Std.HashMap Nat (List Nat)
  predecessors : Std.HashMap Nat (List Nat)

def Graph.ofEdges (instructions : List Disasm.Insn) (edges : List (Nat × Nat)) : Graph :=
  let edges := dedup edges
  {
    instructions := instructions.foldl (init := {}) fun table insn => table.insert insn.address insn
    successors := edges.foldl (init := {}) fun table (source, target) =>
      table.insert source (target :: (table.getD source []))
    predecessors := edges.foldl (init := {}) fun table (source, target) =>
      table.insert target (source :: (table.getD target [])) }

/-- What leads to an instruction, in order, back to where control could come from elsewhere or a call, at most `limit` of
them, and the instruction. -/
def pathTo (graph : Graph) (address : Nat) (limit : Nat := 24) : List Disasm.Insn :=
  let rec go : Nat → Nat → List Disasm.Insn → List Disasm.Insn
    | 0, _, path => path
    | fuel + 1, current, path =>
      match graph.predecessors.getD current [] with
      | [before] =>
        match graph.instructions[before]? with
        | some insn =>
          if insn.flow == .call then path
          else go fuel before (insn :: path)
        | none => path
      | _ => path
  match graph.instructions[address]? with
  | some insn => go limit address [insn]
  | none => []

/-- Whether a path goes from an instruction to the next of a path. -/
def continuesTo (insn : Disasm.Insn) (next : Nat) : Symbolic.Outcome → Bool
  | .normal => insn.next == next
  | .jump (@Expr.const _ value) => value.toNat == next
  | _ => false

/-- The states and the targets of the indirect jump at the end of a path: what it does, run symbolically, of each way that goes
through all of it. -/
def pathTargets (path : List Disasm.Insn) (initial : Symbolic.State := {}) : List (Symbolic.State × Expr) :=
  let rec go : List Disasm.Insn → List Symbolic.State → List (Symbolic.State × Expr)
    | [], _ => []
    | [jump], states => states.flatMap fun state =>
      match Symbolic.run jump.bil state 4000 with
      | .ok results => results.filterMap fun result =>
        match result.outcome with
        | .jump target => some (result.state, target)
        | _ => none
      | .error _ => []
    | insn :: rest@(next :: _), states =>
      let states := states.flatMap fun state =>
        match Symbolic.run insn.bil state 4000 with
        | .ok results => results.filterMap fun result =>
          if continuesTo insn next.address result.outcome then some result.state else none
        | .error _ => []
      go rest (states.take 16)
  go path [initial]

/-- What is known of the registers where a path starts at the entry of a function: of the global entry of a function of 64-bit
PowerPC of ELFv2, that r12 has its address, which r2, the pointer to its TOC, is made of. -/
def entryState (image : Image.Image) (start : Nat) : Symbolic.State :=
  if image.arch == .powerpc && image.addrWidth == 64 && image.symbols.any (fun symbol => symbol.isFunction && symbol.addr == start)
  then { env := [(⟨"R12", .imm 64, 0, false⟩, .const (BitVec.ofNat 64 start))] }
  else {}

/-- The table of the indirect jump at an address, of what leads to it. The targets of a table that no condition of its path
bounds are in `near`, which is where the function of the jump is: what is read past its end isn't of it. What `known` says of an
address, the registers that hold a constant there, of their widths, holds where a path starts there. -/
def resolveJump (image : Image.Image) (graph : Graph) (jump : Nat) (near : Nat × Nat)
    (known : Nat → List (String × Nat × Nat) := fun _ => []) : Option JumpTable :=
  let ofPath (path : List Disasm.Insn) : List (Option Nat × Bool × List Nat) :=
    let initial := match path.head? with
      | some first =>
        let state := entryState image first.address
        { state with env := (known first.address).map (fun (name, width, value) =>
            ((⟨name, .imm width, 0, false⟩ : Bap.Var), Expr.const (BitVec.ofNat width value))) ++ state.env }
      | none => {}
    (pathTargets path initial).filterMap fun (state, target) =>
      match target with
      | .const _ => none
      | _ => tableTargets image target state.constraints near
  let found := ofPath (pathTo graph jump)
  -- a way that bounds the table is what is had of it, rather than one that only reads it as far as it is near
  let found := if found.any (·.2.1) then found.filter (·.2.1) else found
  match found with
  | [] => none
  | (table, bounded, targets) :: rest =>
    some { jump, table, bounded, targets := dedup (targets ++ rest.flatMap (·.2.2)) }

/-! ## The stubs of imports -/

/-- The names of the imports of an ELF image, by the slot of the global offset table they are bound in. -/
def importSlots (image : Image.Image) : Std.HashMap Nat String :=
  match Image.Elf.dynamicRelocations image with
  | .ok spec => spec.references.foldl (init := {}) fun table (slot, name) =>
    table.insert slot ((name.splitOn "@").headD name)
  | .error _ => {}

/-- The slot that a jump to `target` jumps through, if it is a read of memory at a constant address. -/
def slotOf (target : Expr) : Option Nat :=
  let addresses := (selectsOf target).filterMap fun address =>
    match address with
    | .const value => some value.toNat
    | _ => none
  if addresses.isEmpty || addresses.length != (selectsOf target).length || !(varsOf target).isEmpty then none
  else addresses.min?

/-- The import that the stub at an address jumps to: it reaches an indirect jump through a slot of an import. -/
def stubImport (slots : Std.HashMap Nat String) (graph : Graph) (entry : Nat) : Option String := do
  let rec straight : Nat → Nat → List Disasm.Insn → List Disasm.Insn
    | 0, _, path => path.reverse
    | fuel + 1, address, path =>
      match graph.instructions[address]? with
      | none => path.reverse
      | some insn =>
        if insn.flow == .indirectJump then (insn :: path).reverse
        else if insn.flow == .normal then straight fuel insn.next (insn :: path)
        else path.reverse
  let path := straight 6 entry []
  let jump ← path.getLast?
  if jump.flow != .indirectJump then none
  let targets := pathTargets path
  targets.findSome? fun (_, target) => (slotOf (simplify target)).bind slots.get?

/-- The register that a call leaves the return address in, by its name in the semantics. -/
def linkRegister : Image.Arch → Option String
  | .mips => some "R31"
  | .arm | .powerpc => some "LR"
  | .aarch64 => some "X30"
  | .riscv => some "X1"
  | _ => none

/-- Whether an indirect jump goes to where the link register says, which is a return, as MIPS `jr $ra` and Thumb `bx lr` are: its
target, run on its own, is of nothing but the link register as it was. -/
def returnsByLink (arch : Image.Arch) (insn : Disasm.Insn) : Bool :=
  insn.flow == .indirectJump && match linkRegister arch, Symbolic.run insn.bil {} 1000 with
    | some name, .ok results => !results.isEmpty && results.all fun result =>
      match result.outcome with
      | .jump target => match varsOf (simplify target) with
        | [var] => var.startsWith (name ++ "#")
        | _ => false
      | _ => false
    | _, _ => false

/-- The register that points to the stack. -/
def stackRegister : Image.Arch → Option String
  | .mips => some "R29"
  | .arm | .aarch64 => some "SP"
  | .powerpc => some "R1"
  | .riscv => some "X2"
  | .x86 => some "RSP"
  | _ => none

/-- Whether an indirect jump goes to a word that it reads of the stack, which is a return of what saved the link register there, as
ARM's `pop {..., pc}` is: its target, run on its own, is of nothing but the memory where the stack pointer points. -/
def returnsByStack (arch : Image.Arch) (insn : Disasm.Insn) : Bool :=
  insn.flow == .indirectJump && arch != .x86 && match stackRegister arch, Symbolic.run insn.bil {} 1000 with
    | some name, .ok results => !results.isEmpty && results.all fun result =>
      match result.outcome with
      | .jump target =>
        let target := simplify target
        !(selectsOf target).isEmpty && (varsOf target).all (·.startsWith (name ++ "#"))
      | _ => false
    | _, _ => false

/-- Whether an indirect jump returns, by the link register or of the stack. -/
def returnsBy (arch : Image.Arch) (insn : Disasm.Insn) : Bool :=
  returnsByLink arch insn || returnsByStack arch insn

/-- The scan of an image gone on from more roots: what is reachable from them that the scan didn't have, with the edges of it,
into what it had too. The decoder doesn't decode what was had, so that this stops there rather than scanning all that is
called again. -/
def rescan (image : Image.Image) (disasm : Disasm.Disasm) (roots : List Nat) : IO Disasm.Disasm := do
  let some base ← Project.Project.codeDisassembler image 0 | return disasm
  let decoders ← (Project.Project.codeRegions image).filterMapM fun part => do
    pure ((← Project.Project.codeDisassembler image part.2.addr).map (part.2, ·))
  let known : Std.HashSet Nat := disasm.instructions.foldl (init := {}) fun set insn => set.insert insn.address
  let whole := Disasm.Disassembler.ofRegions base decoders
  let fresh : Disasm.Disassembler := { whole with
    decode := fun address data => if known.contains address then pure (.error "known") else whole.decode address data }
  let bytes := (decoders.map (·.1.size)).sum
  let found ← Disasm.Recursive.scanRoots fresh ByteArray.empty bytes disasm.entry roots
  let added := found.instructions.filter fun insn => !known.contains insn.address
  return { disasm with instructions := disasm.instructions ++ added, edges := disasm.edges ++ found.edges }

/-! ## Functions -/

/-- Whether an instruction of MIPS has a delay slot, which all but the compact ones have, a call too, which the decoder doesn't
say of. -/
def mipsSlotted (arch : Image.Arch) (insn : Disasm.Insn) : Bool :=
  arch == .mips && !Target.LLVMLift.mipsCompactMnemonics.contains ((insn.asm.splitOn " ").headD "")

/-- The edges of the flow of control, with those of the tables, and without the fall-through of calls of what doesn't return. -/
def flowEdges (arch : Image.Arch) (disasm : Disasm.Disasm) (graph : Graph) (tables : List JumpTable)
    (hasDelaySlot : Disasm.Insn → Bool) (noReturn : Nat → Bool) : List (Nat × Nat) :=
  -- a call goes on after itself, or after its delay slot, which is of the size of the call: what the decoder says of a jump,
  -- and of a call of MIPS, but a compact one, which falls through to its slot
  let slotted (insn : Disasm.Insn) : Bool := hasDelaySlot insn || mipsSlotted arch insn
  let dead : Std.HashSet (Nat × Nat) := disasm.instructions.foldl (init := {}) fun set insn =>
    if insn.flow == .call && insn.target.any noReturn then
      set.insert (if slotted insn then (insn.next, insn.next + insn.size) else (insn.address, insn.next))
    else set
  let kept := disasm.edges.filter fun edge => !dead.contains edge
  let tableEdges := tables.flatMap fun table =>
    let source := match graph.instructions[table.jump]? with
      | some insn => if hasDelaySlot insn then insn.next else insn.address
      | none => table.jump
    table.targets.map (source, ·)
  kept ++ tableEdges

/-- The instructions that an entry reaches by the edges without going into the entry of another function, and the jumps into
those, which are tail calls. -/
def body (successors : Std.HashMap Nat (List Nat)) (entries : Std.HashSet Nat) (instructions : Std.HashSet Nat) (entry : Nat) :
    List Nat × List (Nat × Nat) :=
  let rec go : Nat → List Nat → Std.HashSet Nat → List (Nat × Nat) → Std.HashSet Nat × List (Nat × Nat)
    | 0, _, seen, tails => (seen, tails)
    | _, [], seen, tails => (seen, tails)
    | fuel + 1, address :: work, seen, tails =>
      if seen.contains address || !instructions.contains address then go fuel work seen tails
      else
        let seen := seen.insert address
        let (inner, tails) := (successors.getD address []).foldl (init := ([], tails)) fun (inner, tails) target =>
          if target != entry && entries.contains target then (inner, (address, target) :: tails) else (target :: inner, tails)
        go fuel (inner ++ work) seen tails
  let (seen, tails) := go (4 * instructions.size + 4) [entry] {} []
  ((seen.toList.mergeSort (· ≤ ·)), dedup tails.reverse)

/-- The partition of a project: its jump tables, with the scan gone on from their targets, and then its functions, with what
doesn't return found as long as more is. What `known` says holds where a path to a jump starts, and the targets that `observed` gives
a jump are its targets where its path doesn't say them, as those that a run saw. -/
def partition (project : Project.Project) (rounds : Nat := 8) (known : Nat → List (String × Nat × Nat) := fun _ => [])
    (observed : Nat → List Nat := fun _ => []) : IO (Option Partition) := do
  let some image := project.image | return none
  let some first := project.disasm | return none
  let some decoder ← Project.Project.codeDisassembler image 0 | return none
  let hasDelaySlot := decoder.hasDelaySlot
  -- the targets of a table of ARM run in the state of its jump, which the mapping symbols say, or as bit 0 of each says
  let runs := Project.Project.armRuns image
  let thumbAt (address : Nat) : Bool :=
    runs.any fun run => run.kind == .thumb && run.start ≤ address && address < run.stop
  let keyOf (jump target : Nat) : Nat :=
    if image.arch = .arm then Disasm.Interwork.key target (target % 2 == 1 || thumbAt jump) else target
  -- the tables, as long as their targets lead to more
  let mut disasm := first
  let mut tables : List JumpTable := []
  let mut extra : List Nat := []
  -- each jump is tried once: what new code adds rarely leads to one that was tried
  let mut tried : Std.HashSet Nat := {}
  for _ in List.range rounds do
    let graph := Graph.ofEdges disasm.instructions disasm.edges
    -- where functions start, as far as is known: their symbols, the roots of the scan, and what is called
    let starts := ((image.symbols.filter (·.isFunction)).map (·.addr) ++ Project.Project.roots image ++
      disasm.instructions.filterMap (fun insn => if insn.flow == .call then insn.target else none)) |> dedup |>.mergeSort (· ≤ ·)
    let codeEnd (address : Nat) : Nat :=
      ((image.memory.entries.find? fun entry => entry.1.executable && entry.1.contains address).map (·.1.maxAddr)).getD address
    let near (jump : Nat) : Nat × Nat :=
      let below := (starts.filter (· ≤ jump)).getLast?.getD jump
      let above := (starts.find? (· > jump)).getD (codeEnd jump)
      (below, above)
    let jumps := disasm.instructions.filter fun insn =>
      insn.flow == .indirectJump && !tried.contains insn.address && !returnsBy image.arch insn
    tried := jumps.foldl (init := tried) fun set insn => set.insert insn.address
    -- of a jump that the code doesn't say the targets of, those that a run saw, as of a dispatcher's table of encoded states
    let found := jumps.filterMap fun insn =>
      (resolveJump image graph insn.address (near insn.address) known).orElse fun _ =>
        match observed insn.address with
        | [] => none
        | targets => some { jump := insn.address, table := none, bounded := false, targets }
    if found.isEmpty then break
    tables := tables ++ found
    let instructions : Std.HashSet Nat := disasm.instructions.foldl (init := {}) fun set insn => set.insert insn.address
    let fresh := (found.flatMap fun table => table.targets.map (table.jump, ·)).filter fun (_, target) =>
      !instructions.contains target
    if fresh.isEmpty then break
    extra := extra ++ fresh.map fun (jump, target) => keyOf jump target
    -- ARM goes over keys of addresses and states, of which a scan is had whole
    if image.arch = .arm then
      match ← Project.Project.scanImageWith image extra with
      | some next => disasm := next
      | none => break
    else
      disasm ← rescan image disasm (fresh.map (·.2))
  -- the functions, of what the scan found, with its starts and what it calls
  let scanned := { project with disasm := some disasm }
  let index := Xrefs.discover scanned
  let graph := Graph.ofEdges disasm.instructions disasm.edges
  let slots := importSlots image
  let named : Std.HashMap Nat String := index.functions.foldl (init := {}) fun table symbol =>
    if symbol.name.isEmpty || symbol.name.startsWith "sub_" then table else table.insert symbol.addr symbol.name
  let calledTargets := disasm.instructions.filterMap fun insn => if insn.flow == .call then insn.target else none
  let candidates := (dedup ((index.functions.map (·.addr)) ++ calledTargets)).filter fun address =>
    graph.instructions.contains address
  let candidateSet : Std.HashSet Nat := candidates.foldl (init := {}) fun set address => set.insert address
  -- an entry without a name that a named one falls through to in a few instructions is another entry of it, as the local entry
  -- of PowerPC of ELFv2 is of its global entry, which sets its TOC pointer first
  let aliases : Std.HashMap Nat Nat := named.fold (init := {}) fun table entry _ =>
    let rec walk : Nat → Nat → Std.HashMap Nat Nat
      | 0, _ => table
      | fuel + 1, address =>
        match graph.instructions[address]? with
        | some insn =>
          if insn.flow != .normal then table
          else if candidateSet.contains insn.next && !named.contains insn.next then table.insert insn.next entry
          else walk fuel insn.next
        | none => table
    walk 3 entry
  let canonical (address : Nat) : Nat := aliases.getD address address
  let entryList := candidates.filter fun address => !aliases.contains address
  let entries : Std.HashSet Nat := entryList.foldl (init := {}) fun set address => set.insert address
  let imports : Std.HashMap Nat String := entryList.foldl (init := {}) fun table entry =>
    match stubImport slots graph entry with
    | some name => table.insert entry name
    | none => table
  let nameOf (entry : Nat) : String :=
    match named[entry]?, imports[entry]? with
    | some name, _ => name
    | none, some name => name ++ "@plt"
    | none, none => Xrefs.subroutineName entry
  let instructionSet : Std.HashSet Nat := disasm.instructions.foldl (init := {}) fun set insn => set.insert insn.address
  let unresolvedOf (instructions : List Nat) : Bool := instructions.any fun address =>
    match graph.instructions[address]? with
    | some insn => insn.flow == .indirectJump && !tables.any (·.jump == address) && !returnsBy image.arch insn
    | none => false
  -- what doesn't return, from the names of the library, grown as long as more is found
  let knownNoReturn : Std.HashSet Nat := entryList.foldl (init := {}) fun set entry =>
    let base := match imports[entry]? with
      | some name => name
      | none => (named.getD entry "").splitOn "@" |>.headD ""
    if noReturnNames.contains base then set.insert entry else set
  let mut noReturn := knownNoReturn
  let mut functions : List Function := []
  for _ in List.range (entryList.length + 1) do
    let edges := flowEdges image.arch disasm graph tables hasDelaySlot (noReturn.contains ∘ canonical)
    let successors : Std.HashMap Nat (List Nat) := edges.foldl (init := {}) fun table (source, target) =>
      table.insert source (target :: table.getD source [])
    functions := entryList.map fun entry =>
      let (instructions, tailCalls) := body successors entries instructionSet entry
      let calls := instructions.filterMap fun address =>
        match graph.instructions[address]? with
        | some insn => if insn.flow == .call then insn.target.map (address, canonical ·) else none
        | none => none
      let thunkOf := match instructions.filter (fun address => (graph.instructions[address]?.map (·.flow)) != some .normal) with
        | [last] =>
          if instructions.length ≤ 2 then
            match graph.instructions[last]? with
            | some insn => if insn.flow == .jump then (insn.target.filter entries.contains).map canonical else none
            | none => none
          else none
        | _ => none
      let hasReturn := instructions.any fun address =>
        match graph.instructions[address]? with
        | some insn => insn.flow == .ret || returnsBy image.arch insn
        | none => false
      { entry, name := nameOf entry, instructions, tailCalls, calls, thunkOf, importName := imports[entry]?
        returns := hasReturn || imports.contains entry || unresolvedOf instructions }
    let byEntry : Std.HashMap Nat Function := functions.foldl (init := {}) fun table function => table.insert function.entry function
    let grown := functions.foldl (init := noReturn) fun set function =>
      if set.contains function.entry || function.returns then set
      else if function.tailCalls.all (fun (_, target) => set.contains target || !(byEntry[target]?.map (·.returns)).getD true) then
        set.insert function.entry
      else set
    if grown.size == noReturn.size then break
    noReturn := grown
  let final := functions.map fun function =>
    { function with returns := !noReturn.contains function.entry && (function.returns ||
      function.tailCalls.any fun (_, target) => !noReturn.contains target) }
  let ofStubs : Std.HashSet Nat := final.foldl (init := {}) fun set function =>
    if function.importName.isSome then function.instructions.foldl (init := set) fun set address => set.insert address else set
  let tabled : Std.HashSet Nat := tables.foldl (init := {}) fun set table => set.insert table.jump
  let open_ := disasm.instructions.filter fun insn =>
    insn.flow == .indirectJump && !tabled.contains insn.address && !ofStubs.contains insn.address &&
      !returnsBy image.arch insn
  let slotJumps := open_.filterMap fun insn =>
    (pathTargets (pathTo graph insn.address 8)).findSome? fun (_, target) =>
      (slotOf (simplify target)).map fun slot => (insn.address, slot, slots[slot]?)
  let throughSlots : Std.HashSet Nat := slotJumps.foldl (init := {}) fun set jump => set.insert jump.1
  let unresolved := (open_.filter fun insn => !throughSlots.contains insn.address).map (·.address)
  let edges := flowEdges image.arch disasm graph tables hasDelaySlot (noReturn.contains ∘ canonical)
  return some { functions := final, tables, slotJumps, unresolved, edges, disasm }

/-- The function of a partition that starts at an address. -/
def Partition.functionAt (partition : Partition) (entry : Nat) : Option Function :=
  partition.functions.find? (·.entry == entry)

/-- The functions of a partition that an instruction is of. -/
def Partition.functionsOf (partition : Partition) (address : Nat) : List Function :=
  partition.functions.filter fun function => function.instructions.contains address

end Bap.Analysis.Partition
