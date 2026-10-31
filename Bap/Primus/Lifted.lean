import Bap.Jit
import Bap.Bil.Observe
import Bap.Primus.Machine
import Std.Data.HashMap
import Bap.Emu.Core

namespace Bap.Primus.Lifted

structure Block where
  address : Nat
  next : Nat
  program : Bil.Program
  deriving Repr, Inhabited

abbrev Fetch := Nat → IO ByteArray
abbrev Lift := Nat → ByteArray → IO Block

structure Statistics where
  cacheHits : Nat := 0
  lifts : Nat := 0
  nativeCompilations : Nat := 0
  nativeRuns : Nat := 0
  interpretedRuns : Nat := 0
  compileMs : Nat := 0
  versionSaves : Nat := 0
  versionHits : Nat := 0
  invalidations : Nat := 0
  evictions : Nat := 0
  graphBlocks : Nat := 0
  deriving Repr

private structure Lowering where
  ops : List Jit.Op := []
  layout : List (Bap.Var × Nat) := []
  inputs : List Bap.Var := []
  outputs : List (Bap.Var × Nat) := []
  checkpoints : List (Nat × List (Bap.Var × Nat)) := []
  written : List Bap.Var := []
  nextSlot : Nat := 0
  nextLabel : Nat := 0
  next : Nat := 0
  effectSlot : Option Nat := none
  memory : Option Bap.Var := none
  /-- Whether the observer of the runner rejects an access that passes the end of the address space, so that
  native code, which does not wrap, never gets to make one. Without that, such a memory is not lowered. -/
  wrapFaults : Bool := false
  /-- The slot that counts the blocks a compiled range may still enter. -/
  budget : Option Nat := none
  /-- The slot that tells the guarded code sites of a range whether anything observes them. -/
  observed : Option Nat := none
  /-- The outputs that a run of a range may not reach, each with a slot that is not 0 once it was written. -/
  flags : List (Nat × Nat) := []

private structure Operand where
  slot : Nat
  width : Nat

private inductive Plan where
  | native (lowering : Lowering) (program : Jit.Program) (fallback : Bil.Program)
  | interpreted (program : Bil.Program)

private structure CachedBlock where
  address : Nat
  code : ByteArray
  next : Nat
  firstNext : Nat
  last : Nat
  /-- Bumped on every hit, in place: a hit touches no table. -/
  executions : IO.Ref Nat
  plan : Plan
  coverage : List (Nat × Nat) := []
  sources : List (Nat × ByteArray) := []
  /-- Whether a range was tried for these bytes and did not form, which is not worth trying on every step. -/
  settled : Bool := false

structure Engine where
  cache : IO.Ref (Std.HashMap Nat CachedBlock)
  ranges : IO.Ref (Std.HashMap Nat CachedBlock)
  cacheVersions : IO.Ref (Std.HashMap Nat (List CachedBlock))
  rangeVersions : IO.Ref (Std.HashMap Nat (List CachedBlock))
  statistics : IO.Ref Statistics
  persistentMemory : IO.Ref (Option Jit.Memory)
  persistentVariable : IO.Ref (Option Bap.Var)
  hotThreshold : Nat
  cacheLimit : Nat
  rangeLimit : Nat
  rangeCacheLimit : Nat
  writeCooldown : Nat
  nativeCooldown : IO.Ref Nat
  deferMemorySync : Bool
  nativeLimit : Nat
  nativeLive : IO.Ref Nat
  dirtyCode : IO.Ref (Option (Nat × Nat))
  /-- The size from which a block's memory lives in a native memory instead of being copied for each run. -/
  persistentFrom : Nat
  /-- Whether the observer of the runner rejects accesses past the end of the address space. -/
  wrapFaults : Bool
  /-- Whether a block that runs off its end continues with the next one. It does in the emulator, and it ends
  `run`, for which falling off the end of a block is how a program ends. -/
  chainFallthrough : Bool
  /-- The blocks that the last run entered after its first. -/
  chained : IO.Ref Nat

structure Result where
  state : Bil.State
  pc : Nat
  next : Nat
  effect : Bil.Effect
  deriving Repr

def Engine.create (hotThreshold : Nat := 1) (cacheLimit : Nat := 128) (rangeLimit : Nat := 1)
    (rangeCacheLimit : Nat := 16) (writeCooldown : Nat := 0) (deferMemorySync : Bool := false)
    (nativeLimit : Nat := 512) (persistentFrom : Nat := 100000) (wrapFaults : Bool := false)
    (chainFallthrough : Bool := false) : IO Engine := do
  return {
    cache := ← IO.mkRef {}
    ranges := ← IO.mkRef {}
    cacheVersions := ← IO.mkRef {}
    rangeVersions := ← IO.mkRef {}
    statistics := ← IO.mkRef {}
    persistentMemory := ← IO.mkRef none
    persistentVariable := ← IO.mkRef none
    hotThreshold := max hotThreshold 1
    cacheLimit := max cacheLimit 1
    rangeLimit := max rangeLimit 1
    rangeCacheLimit := max rangeCacheLimit 1
    writeCooldown
    nativeCooldown := ← IO.mkRef 0
    deferMemorySync
    nativeLimit := max nativeLimit 1
    nativeLive := ← IO.mkRef 0
    dirtyCode := ← IO.mkRef none
    persistentFrom
    wrapFaults
    chainFallthrough
    chained := ← IO.mkRef 0
  }

def stats (engine : Engine) : IO Statistics := engine.statistics.get

private def rememberVersion (engine : Engine)
    (versions : IO.Ref (Std.HashMap Nat (List CachedBlock))) (entry : CachedBlock) : IO Unit := do
  match entry.plan with
  | .interpreted _ => pure ()
  | .native .. => do
    let all ← versions.get
    let existing := all.getD entry.address []
    let previous := existing.filter fun old => old.code != entry.code || old.sources != entry.sources
    if previous.length = existing.length then
      engine.statistics.modify fun stats => { stats with versionSaves := stats.versionSaves + 1 }
    entry.executions.set 1
    let candidates := entry :: previous
    let dropped := candidates.drop 4
    engine.nativeLive.modify fun count => count - min count dropped.length
    versions.set (all.insert entry.address (candidates.take 4))

private def forgetVersions (engine : Engine) (first last : Nat) : IO Unit := do
  let blocks ← engine.cache.get
  blocks.toList.forM fun (address, entry) =>
    if first ≤ address && address ≤ last then rememberVersion engine engine.cacheVersions entry else pure ()
  let ranges ← engine.ranges.get
  ranges.toList.forM fun (_, entry) =>
    let affected := if entry.coverage.isEmpty then first ≤ entry.address && entry.address ≤ last
      else entry.coverage.any fun (lo, hi) => lo ≤ last && first ≤ hi
    if affected then rememberVersion engine engine.rangeVersions entry else pure ()

def clearCache (engine : Engine) : IO Unit := do
  engine.cache.set {}
  engine.ranges.set {}
  engine.cacheVersions.set {}
  engine.rangeVersions.set {}
  engine.nativeLive.set 0

/-- Drops the compiled ranges, which go by the code they were compiled from only when it is written to. -/
def forgetRanges (engine : Engine) : IO Unit := do
  (← engine.ranges.get).toList.forM fun (_, entry) => rememberVersion engine engine.rangeVersions entry
  engine.ranges.set {}

def discardRange (engine : Engine) (first last : Nat) : IO Unit := do
  engine.statistics.modify fun stats => { stats with invalidations := stats.invalidations + 1 }
  forgetVersions engine first last
  engine.cache.modify fun entries => entries.filter fun address _ => address < first || last < address
  engine.ranges.modify fun entries => entries.filter fun _ entry =>
    if entry.coverage.isEmpty then entry.last < first || last < entry.address
    else entry.coverage.all fun (lo, hi) => hi < first || last < lo
  if engine.writeCooldown > 0 then engine.nativeCooldown.set (engine.writeCooldown + 1)

def markDirtyRange (engine : Engine) (first last : Nat) : IO Unit := do
  engine.dirtyCode.modify fun current =>
    match current with
    | some (first', last') => some (min first first', max last last')
    | none => some (first, last)

def flushDirtyRange (engine : Engine) : IO Unit := do
  match ← engine.dirtyCode.get with
  | some (first, last) =>
    engine.dirtyCode.set none
    discardRange engine first last
  | none => pure ()

def discardMemory (engine : Engine) : IO Unit := do
  engine.dirtyCode.set none
  engine.persistentMemory.set none
  engine.persistentVariable.set none

private def widthOf (var : Bap.Var) : Option Nat :=
  match var.typ with
  | .imm width => if 0 < width && width ≤ 64 then some width else none
  | _ => none

private def slot (lowering : Lowering) (var : Bap.Var) : Lowering × Nat :=
  match lowering.layout.find? fun binding => binding.1 == var with
  | some binding => (lowering, binding.2)
  | none =>
    let index := lowering.nextSlot
    ({ lowering with layout := lowering.layout ++ [(var, index)], nextSlot := index + 1 }, index)

private def temporary (lowering : Lowering) : Lowering × Nat :=
  ({ lowering with nextSlot := lowering.nextSlot + 1 }, lowering.nextSlot)

private def readVar (lowering : Lowering) (var : Bap.Var) : Option (Lowering × Nat) := do
  let _ ← widthOf var
  let (lowering, index) := slot lowering var
  let lowering :=
    if lowering.written.contains var || lowering.inputs.contains var then lowering
    else { lowering with inputs := lowering.inputs ++ [var] }
  some (lowering, index)

/-- Records a write of `var`, which is an output once however often it is written. -/
private def recordWrite (lowering : Lowering) (var : Bap.Var) (index : Nat) : Lowering :=
  { lowering with
    outputs := if lowering.outputs.contains (var, index) then lowering.outputs else lowering.outputs ++ [(var, index)]
    written := if lowering.written.contains var then lowering.written else lowering.written ++ [var] }

private def writeVar (lowering : Lowering) (var : Bap.Var) : Option (Lowering × Nat) := do
  let _ ← widthOf var
  let (lowering, index) := slot lowering var
  some (recordWrite lowering var index, index)

private def setEffect (lowering : Lowering) (value : UInt64) : Lowering × Nat :=
  match lowering.effectSlot with
  | some slot => ({ lowering with ops := lowering.ops ++ [.set slot value] }, slot)
  | none =>
    let (lowering, slot) := temporary lowering
    ({ lowering with ops := lowering.ops ++ [.set slot value], effectSlot := some slot }, slot)

private def jumpConstant (lowering : Lowering) (target : UInt64) : Lowering :=
  let (lowering, _) := setEffect lowering 1
  { lowering with ops := lowering.ops ++ [.jump target] }

private def jumpSlot (lowering : Lowering) (target : Nat) : Lowering :=
  let (lowering, _) := setEffect lowering 1
  { lowering with ops := lowering.ops ++ [.jumpSlot target] }

private def immediate {width : Nat} (value : BitVec width) : UInt64 := UInt64.ofNat value.toNat

private def mask (width : Nat) : UInt64 := UInt64.ofNat (2 ^ width - 1)

private def binaryOp : Bil.BinOp → Option Jit.BinOp
  | .add => some .add | .sub => some .sub | .mul => some .mul
  | .and => some .and | .or => some .or | .xor => some .xor
  | .lshift => some .lshift | .rshift => some .rshift
  | .eq => some .eq | .neq => some .neq
  | .lt => some .lt | .le => some .le | .gt => some .gt | .ge => some .ge
  | .div => some .udiv | .rem => some .urem | .sdiv => some .sdiv | .srem => some .srem
  | .slt => some .slt | .sle => some .sle | .sgt => some .sgt | .sge => some .sge
  | _ => none

private def isComparison (op : Jit.BinOp) : Bool :=
  match op with
  | .eq | .neq | .lt | .le | .gt | .ge | .slt | .sle | .sgt | .sge => true
  | _ => false

private def isSigned (op : Jit.BinOp) : Bool :=
  match op with
  | .sdiv | .srem | .slt | .sle | .sgt | .sge => true
  | _ => false

private def signExtend (lowering : Lowering) (width slot : Nat) : Lowering × Nat :=
  let (lowering, dst) := temporary lowering
  ({ lowering with ops := lowering.ops ++ [.signExtend width dst slot] }, dst)

private def narrow (lowering : Lowering) (width slot : Nat) : Lowering :=
  if width < 64 then { lowering with ops := lowering.ops ++ [.andImm slot slot (mask width)] }
  else lowering

/-- Whether native code gets an access of this size right. It does not wrap at the end of the address space, as
the interpreter does, so that an access of several bytes on a memory narrower than its 64 bits stays with the
interpreter, unless the observer of the runner rejects the accesses that would wrap. -/
private def wrapSafe (lowering : Lowering) (var : Bap.Var) (size : Nat) : Bool :=
  match var.typ with
  | .mem width _ => 64 ≤ width || size == 1 || lowering.wrapFaults
  | _ => false

private def useMemory (lowering : Lowering) (var : Bap.Var) : Option Lowering :=
  match var.typ, lowering.memory with
  | .mem _ 8, none => some { lowering with memory := some var }
  | .mem _ 8, some existing => if existing == var then some lowering else none
  | _, _ => none

/-- `useMemory` for an access of `size` bytes. -/
private def useMemoryAt (lowering : Lowering) (var : Bap.Var) (size : Nat) : Option Lowering :=
  if wrapSafe lowering var size then useMemory lowering var else none

/-- Whether an operand of this width addresses the memory, which is what the interpreter requires. -/
private def addressOf (var : Bap.Var) (width : Nat) : Bool :=
  match var.typ with
  | .mem addressWidth _ => addressWidth == width
  | _ => false

/-- Whether evaluating an expression reads memory. A native `select` evaluates both alternatives, so an
`ite` with a load in an alternative would report reads that the program does not make. -/
private def readsMemory : Bil.Exp → Bool
  | .load .. => true
  | .bin _ left right | .concat left right => readsMemory left || readsMemory right
  | .un _ value | .cast _ _ value | .extract _ _ value => readsMemory value
  | .ite condition yes no => readsMemory condition || readsMemory yes || readsMemory no
  | .store .. | .letIn .. => true
  | _ => false

private def lowerExp (lowering : Lowering) : Bil.Exp → Option (Lowering × Operand)
  | @Bil.Exp.int width value =>
    if 0 < width && width ≤ 64 then
      let (lowering, dst) := temporary lowering
      some ({ lowering with ops := lowering.ops ++ [.set dst (immediate value)] }, ⟨dst, width⟩)
    else none
  | .load memory address endian size => do
    let memory ← match memory with
      | .var var => some var
      | _ => none
    let lowering ← useMemoryAt lowering memory size
    let (lowering, address) ← lowerExp lowering address
    if size = 0 || size > 8 || !addressOf memory address.width then none
    let (lowering, dst) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++
      [.memLoad dst address.slot size (endian == .big)] }
    some (lowering, ⟨dst, size * 8⟩)
  | .var var => do
    let width ← widthOf var
    let (lowering, slot) ← readVar lowering var
    some (lowering, ⟨slot, width⟩)
  | .un op value => do
    let (lowering, value) ← lowerExp lowering value
    let (lowering, dst) := temporary lowering
    let lowering ← match op with
      | .neg => some { lowering with ops := lowering.ops ++ [.neg dst value.slot] }
      | .not => some { lowering with ops := lowering.ops ++ [.not dst value.slot] }
    some (narrow lowering value.width dst, ⟨dst, value.width⟩)
  | .bin .smod left right => do
    let (lowering, left) ← lowerExp lowering left
    let (lowering, right) ← lowerExp lowering right
    if left.width != right.width then none
    let (lowering, zeroSlot) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++ [.set zeroSlot 0] }
    let (lowering, signedLeft) := signExtend lowering left.width left.slot
    let (lowering, signedRight) := signExtend lowering right.width right.slot
    let (lowering, leftSign) := temporary lowering
    let (lowering, rightSign) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++
      [.bin .slt leftSign signedLeft zeroSlot, .bin .slt rightSign signedRight zeroSlot] }
    let (lowering, negatedLeft) := temporary lowering
    let (lowering, negatedRight) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++ [.neg negatedLeft left.slot, .neg negatedRight right.slot] }
    let lowering := narrow lowering left.width negatedLeft
    let lowering := narrow lowering left.width negatedRight
    let (lowering, absLeft) := temporary lowering
    let (lowering, absRight) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++
      [.select absLeft leftSign negatedLeft left.slot, .select absRight rightSign negatedRight right.slot] }
    let (lowering, remainder) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++ [.bin .urem remainder absLeft absRight] }
    let (lowering, negated) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++ [.neg negated remainder] }
    let (lowering, leftAdjusted) := temporary lowering
    let (lowering, rightAdjusted) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++
      [.bin .add leftAdjusted negated right.slot, .bin .add rightAdjusted remainder right.slot] }
    let (lowering, leftResult) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++
      [.select leftResult leftSign leftAdjusted remainder] }
    let (lowering, bothResult) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++
      [.select bothResult leftSign negated rightAdjusted] }
    let (lowering, rightResult) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++
      [.select rightResult rightSign bothResult leftResult] }
    let (lowering, nonzero) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++ [.bin .eq nonzero remainder zeroSlot] }
    let (lowering, dst) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++
      [.select dst nonzero remainder rightResult] }
    some (narrow lowering left.width dst, ⟨dst, left.width⟩)
  | .bin .ashift left right => do
    let (lowering, left) ← lowerExp lowering left
    let (lowering, right) ← lowerExp lowering right
    if left.width != right.width then none
    let (lowering, signed) := signExtend lowering left.width left.slot
    let (lowering, dst) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++ [.ashr left.width dst signed right.slot] }
    some (narrow lowering left.width dst, ⟨dst, left.width⟩)
  | .bin op left right => do
    let op ← binaryOp op
    let (lowering, left) ← lowerExp lowering left
    let (lowering, right) ← lowerExp lowering right
    if left.width != right.width then none
    let (lowering, leftSlot) := if isSigned op then signExtend lowering left.width left.slot else (lowering, left.slot)
    let (lowering, rightSlot) := if isSigned op then signExtend lowering right.width right.slot else (lowering, right.slot)
    let (lowering, dst) := temporary lowering
    let width := if isComparison op then 1 else left.width
    let lowering := { lowering with ops := lowering.ops ++ [.bin op dst leftSlot rightSlot] }
    some (narrow lowering width dst, ⟨dst, width⟩)
  | .ite condition yes no => do
    if readsMemory yes || readsMemory no then none
    let (lowering, condition) ← lowerExp lowering condition
    let (lowering, yes) ← lowerExp lowering yes
    let (lowering, no) ← lowerExp lowering no
    if condition.width != 1 || yes.width != no.width then none
    let (lowering, dst) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++ [.select dst condition.slot yes.slot no.slot] }
    some (lowering, ⟨dst, yes.width⟩)
  | .extract high low value => do
    let (lowering, value) ← lowerExp lowering value
    if high < low || high ≥ value.width then none
    let width := high - low + 1
    let (lowering, amount) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++ [.set amount (UInt64.ofNat low)] }
    let (lowering, shifted) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++ [.bin .rshift shifted value.slot amount] }
    let (lowering, dst) := temporary lowering
    some ({ lowering with ops := lowering.ops ++ [.andImm dst shifted (mask width)] }, ⟨dst, width⟩)
  | .cast .signed width value => do
    if width = 0 || width > 64 then none
    let (lowering, value) ← lowerExp lowering value
    if width ≥ value.width then
      let (lowering, dst) := signExtend lowering value.width value.slot
      some (narrow lowering width dst, ⟨dst, width⟩)
    else
      let (lowering, dst) := temporary lowering
      some ({ lowering with ops := lowering.ops ++ [.andImm dst value.slot (mask width)] }, ⟨dst, width⟩)
  | .cast .high width value => do
    let (lowering, value) ← lowerExp lowering value
    if width = 0 || width > value.width then none
    let (lowering, amount) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++ [.set amount (UInt64.ofNat (value.width - width))] }
    let (lowering, shifted) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++ [.bin .rshift shifted value.slot amount] }
    let (lowering, dst) := temporary lowering
    some ({ lowering with ops := lowering.ops ++ [.andImm dst shifted (mask width)] }, ⟨dst, width⟩)
  | .cast kind width value => do
    if (kind != .low && kind != .unsigned) || width = 0 || width > 64 then none
    let (lowering, value) ← lowerExp lowering value
    if width ≥ value.width then
      some (lowering, ⟨value.slot, width⟩)
    else
      let (lowering, dst) := temporary lowering
      some ({ lowering with ops := lowering.ops ++ [.andImm dst value.slot (mask width)] }, ⟨dst, width⟩)
  | _ => none

private def lowerMove (lowering : Lowering) (dst : Bap.Var) (value : Bil.Exp) :
    Option Lowering := do
  match dst.typ, value with
  | .mem _ _, .store memory address stored endian size => do
    let memory ← match memory with
      | .var var => if var == dst then some var else none
      | _ => none
    let lowering ← useMemoryAt lowering memory size
    let (lowering, address) ← lowerExp lowering address
    let (lowering, stored) ← lowerExp lowering stored
    if size = 0 || size > 8 || stored.width != size * 8 || !addressOf memory address.width then none
    some { lowering with ops := lowering.ops ++
      [.memStore address.slot stored.slot size (endian == .big)] }
  | _, _ => do
    let dstWidth ← widthOf dst
    let (lowering, value) ← lowerExp lowering value
    if value.width != dstWidth then none
    let (lowering, dst) ← writeVar lowering dst
    some { lowering with ops := lowering.ops ++ [.move dst value.slot] }

mutual
  private def lowerStmt (lowering : Lowering) : Bil.Stmt → Option (Lowering × Bool)
    | .move dst value => do
      let lowering ← lowerMove lowering dst value
      some (lowering, false)
    | .jmp (@Bil.Exp.int width target) =>
      if width ≤ 64 then some (jumpConstant lowering (immediate target), true) else none
    | .jmp target => do
      let (lowering, target) ← lowerExp lowering target
      some (jumpSlot lowering target.slot, true)
    | .ifElse condition yes no => do
      let (lowering, condition) ← lowerExp lowering condition
      if condition.width != 1 then none
      let yesLabel := lowering.nextLabel
      let noLabel := yesLabel + 1
      let doneLabel := noLabel + 1
      let lowering := { lowering with nextLabel := doneLabel + 1 }
      let lowering := { lowering with ops := lowering.ops ++
        [.branch condition.slot yesLabel noLabel, .label yesLabel] }
      let initialWritten := lowering.written
      let initialOutputs := lowering.outputs
      let (yesLowering, yesTerminated) ← lowerStatements lowering yes
      let noLowering ← lowerStatements { yesLowering with
        written := initialWritten,
        outputs := initialOutputs,
        ops := yesLowering.ops ++ (if yesTerminated then [] else [.goto doneLabel]) ++ [.label noLabel] } no
      if yesLowering.written.length != noLowering.1.written.length ||
        yesLowering.written.any fun var => !noLowering.1.written.contains var then none
      -- the else branch was lowered last, so it has every slot and label; its writes are the same
      let resultOps := noLowering.1.ops ++
        (if noLowering.2 then [] else [.goto doneLabel]) ++
        (if yesTerminated && noLowering.2 then [] else [.label doneLabel])
      some ({ noLowering.1 with ops := resultOps }, yesTerminated && noLowering.2)
    | .while condition body => do
      let conditionLabel := lowering.nextLabel
      let checkLabel := conditionLabel + 1
      let bodyLabel := checkLabel + 1
      let doneLabel := bodyLabel + 1
      let exhaustedLabel := doneLabel + 1
      let lowering := { lowering with nextLabel := exhaustedLabel + 1 }
      let (lowering, counter) := temporary lowering
      let lowering := { lowering with ops := lowering.ops ++
        [.set counter 0, .goto conditionLabel, .label conditionLabel, .add counter counter 1] }
      let (lowering, limit) := temporary lowering
      let (lowering, tooMuch) := temporary lowering
      let lowering := { lowering with ops := lowering.ops ++
        [.set limit 100000, .bin .ge tooMuch counter limit,
         .branch tooMuch exhaustedLabel checkLabel, .label checkLabel] }
      let (lowering, condition) ← lowerExp lowering condition
      if condition.width != 1 then none
      let lowering := { lowering with ops := lowering.ops ++
        [.branch condition.slot bodyLabel doneLabel, .label bodyLabel] }
      let initialWritten := lowering.written
      let (bodyLowering, bodyTerminated) ← lowerStatements lowering body
      if bodyLowering.written.any fun var => !initialWritten.contains var then none
      let bodyOps := bodyLowering.ops ++ (if bodyTerminated then [] else [.goto conditionLabel]) ++
        [.label exhaustedLabel]
      let (resultLowering, _) := setEffect { bodyLowering with ops := bodyOps } 2
      -- a finished loop continues with the next statement
      some ({ resultLowering with ops := resultLowering.ops ++
        [.jump (UInt64.ofNat lowering.next), .label doneLabel] }, false)
    | _ => none

  private def lowerStatements (lowering : Lowering) : Bil.Program → Option (Lowering × Bool)
    | [] => some (lowering, false)
    | stmt :: rest => do
      let (lowering, terminated) ← lowerStmt lowering stmt
      if terminated then some (lowering, true) else lowerStatements lowering rest
end

private def codeSite (lowering : Lowering) (pc : Nat) : Lowering :=
  let (lowering, slot) := setEffect lowering 0
  { lowering with
    ops := lowering.ops ++ [.code slot (UInt64.ofNat pc)]
    checkpoints := lowering.checkpoints ++ [(pc, lowering.outputs)]
  }

private def atCodeStop (lowering : Lowering) (pc : Nat) : Lowering :=
  match lowering.checkpoints.find? fun checkpoint => checkpoint.1 = pc with
  | some checkpoint => { lowering with outputs := checkpoint.2 }
  | none => lowering

/-- The value of a target that depends on no variable, like the pc-relative targets of lifted branches. -/
private def closedTarget (target : Bil.Exp) : Option Nat :=
  let rec closed : Bil.Exp → Bool
    | .int _ => true
    | .bin _ left right => closed left && closed right
    | .un _ value | .cast _ _ value => closed value
    | _ => false
  if closed target then
    match Bil.evalExp [] target with
    | .ok (@Value.bits width value) => if width ≤ 64 then some value.toNat else none
    | _ => none
  else none

/-- How a block ends, as far as a range can chain it. -/
private inductive BlockExit where
  /-- It runs off its end. -/
  | fall
  | direct (target : Nat)
  /-- A branch, whose `no` is the fall-through when it has no else, which `falls` says. -/
  | branch (condition : Bil.Exp) (yes no : Nat) (falls : Bool)
  /-- It ends in a way that a range leaves to the dispatcher. -/
  | other

private def blockExit (block : Block) : BlockExit :=
  match block.program.getLast? with
  | some (.jmp target) =>
    match closedTarget target with
    | some target => .direct target
    | none => .other
  | some (.ifElse condition [.jmp yes] []) =>
    match closedTarget yes with
    | some yes => .branch condition yes block.next true
    | none => .other
  | some (.ifElse condition [.jmp yes] [.jmp no]) =>
    match closedTarget yes, closedTarget no with
    | some yes, some no => .branch condition yes no false
    | _, _ => .other
  | some (.ifElse ..) | some (.while ..) | some (.special _) | some (.cpuExn _) => .other
  | _ => .fall

/-- The blocks that may follow `block` in a range. -/
private def directEdges (block : Block) (chainFallthrough : Bool := false) : List Nat :=
  match blockExit block with
  | .direct target => [target]
  | .branch _ yes no falls => if falls && !chainFallthrough then [yes] else [yes, no]
  | .fall => if chainFallthrough then [block.next] else []
  | .other => []

private def reachable (edges : List (Nat × Nat)) (source target : Nat) : Bool :=
  let rec loop (fuel : Nat) (visited : List Nat) (pending : List Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      match pending with
      | [] => false
      | current :: rest =>
        if current = target then true
        else if visited.contains current then loop fuel visited rest
        else
          let next := edges.filterMap fun (source, target) => if source = current then some target else none
          loop fuel (current :: visited) (next ++ rest)
  loop (edges.length + 1) [] [source]

private def gatherGraph (engine : Engine) (fetch : Fetch) (lift : Lift) (limit : Nat)
    (seed : Block) (seedCode : ByteArray) (lowerable : Block → Bool) :
    IO (List Block × List (Nat × Nat) × List (Nat × ByteArray)) := do
  let rec visit (queue : List Block) (blocks : List Block) (edges : List (Nat × Nat))
      (sources : List (Nat × ByteArray)) := do
    match queue with
    | [] => pure (blocks, edges, sources)
    | current :: rest =>
      if blocks.any fun block => block.address = current.address then visit rest blocks edges sources
      else if _h : blocks.length >= limit then pure (blocks, edges, sources)
      else
        let grown := blocks ++ [current]
        let (edges, additions, sources) ← (directEdges current engine.chainFallthrough).foldlM
            (init := (edges, [], sources)) fun state target => do
          let (edges, additions, sources) := state
          let known := (grown ++ queue ++ additions).any fun block => block.address = target
          if !known && grown.length + rest.length + additions.length >= limit then pure state
          else if known then pure (edges ++ [(current.address, target)], additions, sources)
          else
            try
              let code ← fetch target
              engine.statistics.modify fun stats => { stats with lifts := stats.lifts + 1 }
              let block ← lift target code
              if block.address != target then
                throw <| IO.userError s!"lifted graph block address {block.address} does not match {target}"
              -- A block that needs the interpreter stays out, and the range leaves for it.
              if lowerable block then
                pure (edges ++ [(current.address, target)], additions ++ [block], sources ++ [(target, code)])
              else
                pure (edges, additions, sources)
            catch _ =>
              pure (edges, additions, sources)
        visit (rest ++ additions) grown edges sources
  termination_by (limit - blocks.length, queue.length)
  decreasing_by
    · exact Prod.Lex.right _ (by simp)
    · apply Prod.Lex.left
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  visit [seed] [] [] [(seed.address, seedCode)]

private def graphEdgeOps (lowering : Lowering) (labels : List (Nat × Nat))
    (edges : List (Nat × Nat)) (source target : Nat) : Option (List Jit.Op) :=
  if edges.contains (source, target) then
    match labels.find? fun (address, _) => address = target with
    | some (_, label) => some [.goto label]
    | none => none
  else
    some (jumpConstant { lowering with ops := [] } (UInt64.ofNat target)).ops

/-- A fresh label. -/
private def freshLabel (lowering : Lowering) : Lowering × Nat :=
  ({ lowering with nextLabel := lowering.nextLabel + 1 }, lowering.nextLabel)

/-- Entering a block over an edge of a range: when the budget is used up, the range leaves for the dispatcher,
with the block not entered. Otherwise the code site of the block, which a stop leaves with the block not
entered either, and then the block counts. Lean code only runs in observers, so a block needs the guard around
its code site only if it and the blocks before it have none: `guarded` says whether that is the case. -/
private def enterBlock (lowering : Lowering) (budget observed address : Nat) (guarded : Bool) : Lowering :=
  let (lowering, go) := freshLabel lowering
  let (lowering, leave) := freshLabel lowering
  let lowering := { lowering with ops := lowering.ops ++ [.branch budget go leave, .label leave] }
  let lowering := jumpConstant lowering (UInt64.ofNat address)
  let lowering := { lowering with ops := lowering.ops ++ [.label go] }
  let lowering :=
    if guarded then
      let (lowering, site) := freshLabel lowering
      let (lowering, done) := freshLabel lowering
      let lowering := { lowering with ops := lowering.ops ++ [.branch observed site done, .label site] }
      let lowering := codeSite lowering address
      { lowering with ops := lowering.ops ++ [.goto done, .label done] }
    else codeSite lowering address
  { lowering with ops := lowering.ops ++ [.add budget budget (UInt64.ofNat (2 ^ 64 - 1))] }

mutual
  /-- Whether a statement can end in any other way than running off its end. -/
  private def stmtLeaves : Bil.Stmt → Bool
    | .move .. => false
    | .ifElse _ yes no => programLeaves yes || programLeaves no
    | .while _ body => programLeaves body
    | _ => true

  private def programLeaves : Bil.Program → Bool
    | [] => false
    | stmt :: rest => stmtLeaves stmt || programLeaves rest
end

mutual
  /-- The variables that a statement has written at every end of it. -/
  private def stmtWrites : Bil.Stmt → List Bap.Var
    | .move dst _ => if (widthOf dst).isSome then [dst] else []
    | .ifElse _ yes no => (programWrites yes).filter (programWrites no).contains
    | _ => []

  /-- The variables that a program has written at every end of it, however it ends: what follows a statement that can
  leave does not count. -/
  private def programWrites : Bil.Program → List Bap.Var
    | [] => []
    | stmt :: rest => stmtWrites stmt ++ if stmtLeaves stmt then [] else programWrites rest
end

/-- What a table of `definitelyWritten` says of a block. -/
private def writtenAt (table : List (Nat × List Bap.Var)) (address : Nat) : List Bap.Var :=
  (table.find? fun entry => entry.1 == address).elim [] Prod.snd

/-- What the block at an address writes at every end of it. -/
private def writesOf (blocks : List Block) (address : Nat) : List Bap.Var :=
  (blocks.find? fun block => block.address == address).elim [] fun block => programWrites block.program

/-- A round of `definitelyWritten`: what each block has written on all ways to it of one step more. -/
private def writtenRound (seed : Nat) (blocks : List Block) (edges : List (Nat × Nat)) (all : List Bap.Var)
    (current : List (Nat × List Bap.Var)) : List (Nat × List Bap.Var) :=
  blocks.map fun block =>
    (block.address,
      if block.address = seed then [] else
        (edges.filter fun edge => edge.2 == block.address).foldl (init := all) fun kept edge =>
          let reaching := writtenAt current edge.1 ++ writesOf blocks edge.1
          kept.filter reaching.contains)

/-- Whether a table says only what holds on every way to a block: nothing at the seed, and along each edge only what
its source has or writes. -/
private def writtenStable (seed : Nat) (blocks : List Block) (edges : List (Nat × Nat))
    (table : List (Nat × List Bap.Var)) : Bool :=
  (writtenAt table seed).isEmpty &&
    edges.all fun edge => (writtenAt table edge.2).all fun var =>
      (writtenAt table edge.1).contains var || (writesOf blocks edge.1).contains var

/-- What each block has written on all ways to it, starting from the seed, where nothing is written. A way around a
loop only ever removes what the first way wrote, so that this converges from above in as many rounds as the longest
way without a cycle, which is at most one for each block. A table that were not stable says nothing, which is always
right: `writtenStable` is what its soundness rests on, not the number of rounds. -/
private def definitelyWritten (seed : Nat) (blocks : List Block) (edges : List (Nat × Nat)) : List (Nat × List Bap.Var) :=
  let all := (blocks.flatMap fun block => programWrites block.program).eraseDups
  let table := (List.range blocks.length).foldl (init := blocks.map fun block => (block.address, all))
    fun current _ => writtenRound seed blocks edges all current
  if writtenStable seed blocks edges table then table else []

/-- A flag for each of `outputs`, each with a slot of its own from `start` on. -/
private def flagSlots (outputs : List (Bap.Var × Nat)) (start : Nat) : Nat × List (Nat × Nat) :=
  outputs.foldl (init := (start, [])) fun (next, flags) output => (next + 1, (output.2, next) :: flags)

/-- An operation, and if it is a move to a slot with a flag, the setting of the flag. -/
private def flagged (flags : List (Nat × Nat)) (op : Jit.Op) : List Jit.Op :=
  match op with
  | .move dst _ =>
    match flags.find? fun flag => flag.1 == dst with
    | some flag => [op, .set flag.2 1]
    | none => [op]
  | _ => [op]

/-- Outputs need not have been written where a run ended, other than those of `seedWritten`. Each gets a slot, set
next to the moves to it, which says whether it was. A move only ever goes to the slot of a variable. -/
private def flagOutputs (seedWritten : List Bap.Var) (lowering : Lowering) : Lowering :=
  let later := lowering.outputs.filter fun output => !seedWritten.contains output.1
  let (next, flags) := flagSlots later lowering.nextSlot
  { lowering with
    nextSlot := next
    flags
    ops := lowering.ops.flatMap (flagged flags)
    checkpoints := lowering.checkpoints.map fun checkpoint => (checkpoint.1, lowering.outputs) }

/-- The variables that a program writes before it can do anything else, and so at every end of it. The others of
a run may not have been written where it ended. -/
private def leadingMoves (program : Bil.Program) : List Bap.Var :=
  match program with
  | .move dst _ :: rest => dst :: leadingMoves rest
  | _ => []

/-- The slots an operation reads or writes. -/
private def opSlots : Jit.Op → List Nat
  | .set dst _ => [dst]
  | .move dst src | .add dst src _ | .andImm dst src _ | .signExtend _ dst src | .neg dst src | .not dst src => [dst, src]
  | .jump _ | .label _ | .goto _ => []
  | .jumpSlot src => [src]
  | .bin _ dst left right | .ashr _ dst left right => [dst, left, right]
  | .select dst condition yes no => [dst, condition, yes, no]
  | .branch condition _ _ => [condition]
  | .memLoad dst address _ _ => [dst, address]
  | .memStore address value _ _ => [address, value]
  | .code effectSlot _ => [effectSlot]

private def opLabels (ops : List Jit.Op) : List Nat :=
  ops.filterMap fun op =>
    match op with
    | .label id => some id
    | _ => none

/-- What the proof of a whole range checks of what it lowered, rather than follows through every statement: blocks
have an address each and it fits, a label is where it is once, operations stay in the slots allocated, which leaves
the slots after them to the flags, an input has a slot, what is moved to, if it is a variable's, is an output, and the control slots stay.
All hold of what lowering makes. A lowering that did not would stay out of native code. -/
private def lowerGraphChecked (blocks : List Block) (initial lowering : Lowering) : Bool :=
  lowering.budget == initial.budget && lowering.observed == initial.observed &&
    decide (blocks.map Block.address).Nodup &&
    blocks.all (fun block => decide (block.address < 2 ^ 64) && decide (block.next < 2 ^ 64)) &&
    decide (opLabels lowering.ops).Nodup &&
    lowering.ops.all (fun op => (opSlots op).all (· < lowering.nextSlot)) &&
    lowering.outputs.all lowering.layout.contains &&
    lowering.inputs.all (fun var => lowering.layout.any fun binding => binding.1 == var) &&
    lowering.ops.all fun op =>
      match op with
      | .move dst _ => lowering.layout.all fun binding => binding.2 != dst || lowering.outputs.contains binding
      | _ => true

/-- What stays the same while the blocks of a range are lowered. -/
private structure GraphPlan where
  seed : Nat
  labels : List (Nat × Nat)
  edges : List (Nat × Nat)
  budget : Nat
  observed : Nat
  chained : Bool
  definite : Nat → List Bap.Var
  guarded : Block → Bool

private def Lowering.push (lowering : Lowering) (ops : List Jit.Op) : Lowering :=
  { lowering with ops := lowering.ops ++ ops }

private def Lowering.withWritten (lowering : Lowering) (written : List Bap.Var) : Lowering :=
  { lowering with written }

/-- The way into a block: over an edge, there is one. A block with no edge to it can only be the seed. -/
private def lowerEntry (plan : GraphPlan) (lowering : Lowering) (block : Block) (hasEdge : Bool) : Option Lowering :=
  if !hasEdge then
    if block.address = plan.seed then some lowering else none
  else
    match plan.labels.find? fun (address, _) => address = block.address with
    | some (_, label) =>
      some (enterBlock (lowering.push [.label label]) plan.budget plan.observed block.address
        (plan.guarded block))
    | none => none

/-- What a block does, and where it goes. -/
private def lowerExit (plan : GraphPlan) (lowering : Lowering) (block : Block) : Option Lowering :=
  match blockExit block with
  | .direct target => do
    let (lowered, terminated) ← lowerStatements lowering block.program.dropLast
    if terminated then none
    else
      let ops ← graphEdgeOps lowered plan.labels plan.edges block.address target
      some (lowered.push ops)
  | .branch condition yes no falls => do
    let (lowered, terminated) ← lowerStatements lowering block.program.dropLast
    if terminated then none
    else
      let (lowered, condition) ← lowerExp lowered condition
      if condition.width != 1 then none
      else
        let (lowered, yesLabel) := freshLabel lowered
        let (lowered, noLabel) := freshLabel lowered
        let yesOps ← graphEdgeOps lowered plan.labels plan.edges block.address yes
        let lowered := lowered.push ([.branch condition.slot yesLabel noLabel, .label yesLabel] ++ yesOps ++ [.label noLabel])
        -- The else of a branch without one is no jump: its effect stays a normal one.
        let noOps ←
          if falls && !plan.edges.contains (block.address, no) then some [.jump (UInt64.ofNat no)]
          else graphEdgeOps lowered plan.labels plan.edges block.address no
        some (lowered.push noOps)
  | _ => do
    let (lowered, terminated) ← lowerStatements lowering block.program
    if terminated then some lowered
    else if plan.edges.contains (block.address, block.next) then
      let ops ← graphEdgeOps lowered plan.labels plan.edges block.address block.next
      some (lowered.push ops)
    else some (lowered.push [.jump (UInt64.ofNat block.next)])

private def lowerBlock (plan : GraphPlan) (lowering : Lowering) (block : Block) : Option Lowering := do
  -- A read of what the block does not have written on all ways to it is an input.
  let lowering := if plan.chained then lowering.withWritten (plan.definite block.address) else lowering
  let incoming := plan.edges.any fun edge => edge.2 == block.address
  if block.address = plan.seed && incoming then
    -- A seed that an edge leads back to has an entry and a body, which the first run goes to directly.
    let (lowering, body) := freshLabel lowering
    let lowering ← lowerEntry plan (lowering.push [.goto body]) block incoming
    lowerExit plan (lowering.push [.goto body, .label body]) block
  else
    let lowering ← lowerEntry plan lowering block incoming
    lowerExit plan lowering block

private def lowerBlocks (plan : GraphPlan) (lowering : Lowering) : List Block → Option Lowering
  | [] => some lowering
  | block :: rest => do
    let lowering ← lowerBlock plan lowering block
    lowerBlocks plan lowering rest

/-- The lowering that the blocks of a graph start from: the effect, and for a chained range what controls it. -/
private def graphInitial (seed : Block) (labelCount : Nat) (wrapFaults chained : Bool) : Lowering :=
  let initial := (setEffect { next := seed.next, nextLabel := labelCount, wrapFaults } 0).1
  if chained then
    let (initial, budget) := temporary initial
    let (initial, observed) := temporary initial
    { initial with budget := some budget, observed := some observed }
  else initial

private def graphPlan (blocks : List Block) (edges : List (Nat × Nat)) (wrapFaults : Bool) (seed : Block) (initial : Lowering) : GraphPlan :=
  -- The label of a block heads the entry over an edge; a run starts in the seed without one.
  let alone (block : Block) := lowerStatements { wrapFaults } block.program
  let touches (block : Block) : Bool := (alone block).elim true fun lowered => lowered.1.memory.isSome
  let definite := definitelyWritten seed.address blocks edges
  { seed := seed.address
    labels := (List.range blocks.length).map fun index => (blocks[index]!.address, index)
    edges
    budget := initial.budget.getD 0
    observed := initial.observed.getD 0
    chained := !edges.isEmpty
    definite := writtenAt definite
    guarded := fun block => !touches block && !(edges.any fun edge => edge.2 == block.address &&
      blocks.any fun other => other.address == edge.1 && touches other) }

private def lowerGraph (blocks : List Block) (edges : List (Nat × Nat)) (wrapFaults : Bool := false) :
    Option Lowering := do
  let seed ← blocks.head?
  let initial := graphInitial seed blocks.length wrapFaults !edges.isEmpty
  let lowering ← lowerBlocks (graphPlan blocks edges wrapFaults seed initial) initial blocks
  if lowerGraphChecked blocks initial lowering then some (flagOutputs (leadingMoves seed.program) lowering) else none

private def compilePlan (engine : Engine) (block : Block) : IO Plan := do
  if (← engine.nativeLive.get) ≥ engine.nativeLimit then pure (.interpreted block.program)
  else
    match lowerGraph [block] [] engine.wrapFaults with
    | none => pure (.interpreted block.program)
    | some lowering =>
      let started ← IO.monoMsNow
      let program ← Jit.compile lowering.ops
      let elapsed := (← IO.monoMsNow) - started
      engine.nativeLive.modify (· + 1)
      engine.statistics.modify fun stats =>
        { stats with nativeCompilations := stats.nativeCompilations + 1, compileMs := stats.compileMs + elapsed }
      pure (.native lowering program block.program)

/-- Drops the entry that ran least, and of those the one at the lowest address. Only a miss gets here, whose
lifting and compilation cost far more than a walk over the table. -/
private def evictColdest (engine : Engine)
    (versions : IO.Ref (Std.HashMap Nat (List CachedBlock)))
    (entries : Std.HashMap Nat CachedBlock) : IO (Std.HashMap Nat CachedBlock) := do
  let coldest ← entries.toList.foldlM (init := (none : Option (Nat × Nat × CachedBlock))) fun best (address, entry) => do
    let executions ← entry.executions.get
    match best with
    | some (bestRuns, bestAddress, _) =>
      if executions < bestRuns || (executions == bestRuns && address < bestAddress) then
        pure (some (executions, address, entry))
      else pure best
    | none => pure (some (executions, address, entry))
  match coldest with
  | some (_, address, entry) =>
    rememberVersion engine versions entry
    pure (entries.erase address)
  | none => pure entries

/-- Whether two byte strings are the same, without unpacking them. -/
private def sameBytes (left right : ByteArray) : Bool :=
  left.size == right.size &&
    Nat.all left.size fun index _ => left.get! index == right.get! index

private def restoreBlockVersion (engine : Engine) (address : Nat) (code : ByteArray) :
    IO (Option CachedBlock) := do
  let versions ← engine.cacheVersions.get
  pure ((versions.getD address []).find? fun entry => entry.code = code)

private def prepare (engine : Engine) (lift : Lift) (address : Nat) (code : ByteArray)
    (compileSingle : Bool := true) : IO CachedBlock := do
  let cooldown ← engine.nativeCooldown.get
  let miss := do
    let restored ← if cooldown = 0 then restoreBlockVersion engine address code else pure none
    match restored with
    | some entry =>
      engine.statistics.modify fun stats => { stats with versionHits := stats.versionHits + 1 }
      engine.cache.modify (·.insert address entry)
      return entry
    | none =>
      let entries ← engine.cache.get
      entries.get? address |>.forM fun previous => rememberVersion engine engine.cacheVersions previous
      let entries ← if entries.size ≥ engine.cacheLimit then do
        engine.statistics.modify fun stats => { stats with evictions := stats.evictions + 1 }
        evictColdest engine engine.cacheVersions entries
      else pure entries
      engine.statistics.modify fun stats => { stats with lifts := stats.lifts + 1 }
      let block ← lift address code
      if block.address != address then
        throw <| IO.userError s!"lifted block address {block.address} does not match {address}"
      let plan ← if compileSingle && engine.hotThreshold = 1 && cooldown = 0 then compilePlan engine block
        else pure (.interpreted block.program)
      let entry : CachedBlock := {
        address, code, next := block.next, firstNext := block.next, last := address
        executions := ← IO.mkRef 1, plan
      }
      engine.cache.set (entries.insert address entry)
      return entry
  match (← engine.cache.get).get? address with
  | some entry =>
    if sameBytes entry.code code then do
      engine.statistics.modify fun stats => { stats with cacheHits := stats.cacheHits + 1 }
      entry.executions.modify (· + 1)
      match entry.plan with
      | .native .. => return entry
      | .interpreted program =>
        let shouldCompile := compileSingle && cooldown = 0 && (← entry.executions.get) ≥ engine.hotThreshold
        if shouldCompile then
          let plan ← compilePlan engine ⟨entry.address, entry.next, program⟩
          let updated := { entry with plan }
          engine.cache.modify (·.insert address updated)
          return updated
        else return entry
    else
      miss
  | none => miss

private def restoreRangeVersion (engine : Engine) (fetch : Fetch) (address : Nat) (code : ByteArray) :
    IO (Option CachedBlock) := do
  let versions ← engine.rangeVersions.get
  let rec find (candidates : List CachedBlock) : IO (Option CachedBlock) := do
    match candidates with
    | [] => pure none
    | entry :: rest =>
      if entry.code != code || entry.sources.isEmpty then find rest
      else
        let valid ← entry.sources.allM fun (source, bytes) => do
          try
            let current ← fetch source
            pure (current = bytes)
          catch _ =>
            pure false
        if valid then do
          engine.statistics.modify fun stats => { stats with versionHits := stats.versionHits + 1 }
          pure (some entry)
        else find rest
  find (versions.getD address [])

private def prepareGraph (engine : Engine) (fetch : Fetch) (lift : Lift)
    (address : Nat) (code : ByteArray) (budget : Nat) : IO CachedBlock := do
  -- A run that may enter no other block has no use for a range: the block alone moves less in and out of native code.
  if budget = 0 then return ← prepare engine lift address code
  match (← engine.ranges.get).get? address with
  | some entry =>
    engine.statistics.modify fun stats => { stats with cacheHits := stats.cacheHits + 1 }
    entry.executions.modify (· + 1)
    return entry
  | none => do
    if engine.rangeLimit ≤ 1 then return ← prepare engine lift address code
    let cooldown ← engine.nativeCooldown.get
    let restored ← if cooldown = 0 then restoreRangeVersion engine fetch address code else pure none
    match restored with
    | some entry =>
      entry.executions.modify (· + 1)
      engine.ranges.modify (·.insert address entry)
      return entry
    | none => do
      let first ← prepare engine lift address code false
      if first.settled || (← first.executions.get) < engine.hotThreshold || cooldown != 0 then return first
      else
        let settle (entry : CachedBlock) : IO CachedBlock := do
          let updated := { entry with settled := true }
          engine.cache.modify (·.insert address updated)
          pure updated
        let firstProgram := match first.plan with
          | .native _ _ fallback => fallback
          | .interpreted program => program
        let seed : Block := ⟨first.address, first.next, firstProgram⟩
        let lowerable (block : Block) : Bool := (lowerGraph [block] [] engine.wrapFaults).isSome
        let (blocks, edges, sources) ←
          if lowerable seed then gatherGraph engine fetch lift engine.rangeLimit seed first.code lowerable
          else pure ([seed], [], [])
        if edges.isEmpty then
          match first.plan with
          | .native .. => settle first
          | .interpreted program => settle { first with plan := ← compilePlan engine ⟨first.address, first.next, program⟩ }
        else
          match lowerGraph blocks edges engine.wrapFaults with
          | none => settle first
          | some lowering =>
            if (← engine.nativeLive.get) ≥ engine.nativeLimit then return first
            else
              let started ← IO.monoMsNow
              let program ← Jit.compile lowering.ops
              let elapsed := (← IO.monoMsNow) - started
              engine.nativeLive.modify (· + 1)
              engine.statistics.modify fun stats =>
                { stats with
                  nativeCompilations := stats.nativeCompilations + 1
                  compileMs := stats.compileMs + elapsed
                  graphBlocks := stats.graphBlocks + blocks.length }
              let plan := Plan.native lowering program firstProgram
              let last := blocks.foldl (init := seed.address) fun current block => max current (block.next - 1)
              let entry := { first with
                next := lowering.next
                last
                plan
                coverage := blocks.map fun block => (block.address, block.next - 1)
                sources
              }
              let ranges ← engine.ranges.get
              let ranges ← if ranges.size ≥ engine.rangeCacheLimit then do
                engine.statistics.modify fun stats => { stats with evictions := stats.evictions + 1 }
                evictColdest engine engine.rangeVersions ranges
              else pure ranges
              engine.ranges.set (ranges.insert address entry)
              engine.cache.modify (·.erase address)
              return entry

private def encodeState (lowering : Lowering) (env : Bil.Env) : Except String (Array UInt64) := do
  lowering.layout.foldlM (init := Array.replicate lowering.nextSlot 0) fun slots binding => do
    let var := binding.1
    match Bil.lookup env var with
    | .ok value =>
      let ⟨width, value⟩ ← Value.asBits value
      match widthOf var with
      | some expected =>
        if width == expected then .ok (slots.set! binding.2 (immediate value))
        else .error s!"variable {var.name} has width {width}, expected {expected}"
      | none => .error s!"unsupported variable {var.name}"
    | .error error =>
      if lowering.inputs.contains var then .error error else .ok slots

/-- The value of a slot in a variable, without working out `2 ^ 64` for the common width. -/
private def slotBits (width : Nat) (slot : UInt64) : BitVec width :=
  if h : width = 64 then h ▸ slot.toBitVec else BitVec.ofNat width slot.toNat

/-- The environment without the bindings of `pending`, which are distinct. The bindings stop at the last of
them and the rest of the environment is shared, and those that a loop writes are near the front. -/
private def withoutBindings (pending : List Bap.Var) : Bil.Env → Bil.Env
  | [] => []
  | binding :: rest =>
    if pending.isEmpty then binding :: rest
    else if pending.contains binding.1 then withoutBindings (pending.erase binding.1) rest
    else binding :: withoutBindings pending rest

/-- The values of the outputs in the slots. -/
private def syncUpdates (outputs : List (Bap.Var × Nat)) (slots : Array UInt64) : List (Bap.Var × Value) :=
  outputs.foldr (init := []) fun output updates =>
    match widthOf output.1 with
    | some width => (output.1, Value.bits (slotBits width (slots.getD output.2 0))) :: updates
    | none => updates

/-- The outputs that were written: an output with a flag only if the flag says so. -/
private def reachedOutputs (lowering : Lowering) (slots : Array UInt64) : List (Bap.Var × Nat) :=
  if lowering.flags.isEmpty then lowering.outputs
  else lowering.outputs.filter fun output =>
    match lowering.flags.find? fun flag => flag.1 == output.2 with
    | some flag => slots.getD flag.2 0 != 0
    | none => true

private def syncState (lowering : Lowering) (state : Bil.State) (slots : Array UInt64) : Bil.State :=
  let updates := syncUpdates (reachedOutputs lowering slots) slots
  { env := updates ++ withoutBindings (updates.map Prod.fst) state.env }

private def memoryInput (lowering : Lowering) (state : Bil.State) :
    Except String (Array UInt64 × Array UInt8) := do
  match lowering.memory with
  | none => .ok (#[], #[])
  | some var =>
    match Bil.lookup state.env var with
    | .ok (.memory memory) =>
      let cells := Bap.Memory.cells memory
      let addresses := cells.map (fun cell => UInt64.ofNat cell.1.toNat) |>.toArray
      let values := cells.map (fun cell => cell.2) |>.toArray
      .ok (addresses, values)
    | .ok _ => .error s!"variable {var.name} is not memory"
    | .error error => .error error

private def syncMemory (lowering : Lowering) (state : Bil.State)
    (addresses : Array UInt64) (values : Array UInt8) : Bil.State :=
  match lowering.memory with
  | none => state
  | some var =>
    match var.typ with
    | .mem width 8 =>
      let memory := (addresses.zip values).foldl (init := Bap.Memory.empty width) fun memory cell =>
        Bap.Memory.writeByte memory (BitVec.ofNat width cell.1.toNat) cell.2
      { env := Bil.bind state.env var (.memory memory) }
    | _ => state

private def syncMemoryDelta (lowering : Lowering) (state : Bil.State)
    (addresses : Array UInt64) (values : Array UInt8) : Bil.State :=
  match lowering.memory with
  | none => state
  | some var =>
    if addresses.isEmpty then state else
      match var.typ, Bil.lookup state.env var with
      | .mem width 8, .ok (@Value.memory addressWidth memory) =>
        if h : width = addressWidth then
          let memory : Bap.Memory width := h ▸ memory
          let cells := (addresses.zip values).toList.map fun cell => (BitVec.ofNat width cell.1.toNat, cell.2)
          let updated := Bap.Memory.writeCells memory cells
          { env := Bil.bind state.env var (.memory updated) }
        else state
      | _, _ => state

/-- What a native run comes to, by its effect slot. -/
private def nativeOutcome (lowering : Lowering) (following : Nat) (next : Nat) (state : Bil.State) (slots : Array UInt64) :
    Except String Result :=
  let effect : UInt64 := match lowering.effectSlot with
    | some slot => slots.getD slot 0
    | none => 0
  if effect == 1 then
    .ok ⟨state, next, following, .jump (BitVec.ofNat 64 next)⟩
  else if effect == 2 then
    .error "Primus loop fuel exhausted"
  else
    -- A range runs off the end of whichever block it ended in, and a code stop has its pc.
    .ok ⟨state, next, next, .normal⟩

private def nativeResult (lowering : Lowering) (following : Nat) (next : Nat)
    (state : Bil.State) (slots : Array UInt64) : IO Result :=
  match nativeOutcome lowering following next state slots with
  | .ok result => pure result
  | .error error => throw <| IO.userError error

private def recordNative (engine : Engine) : IO Unit :=
  engine.statistics.modify fun stats => { stats with nativeRuns := stats.nativeRuns + 1 }

private def recordInterpreted (engine : Engine) : IO Unit :=
  engine.statistics.modify fun stats =>
    { stats with interpretedRuns := stats.interpretedRuns + 1 }

private def syncInterpretedWrites (engine : Engine) (writes : List (Nat × Nat))
    (state : Bil.State) : IO Unit := do
  let persistent ← engine.persistentMemory.get
  let memoryVar ← engine.persistentVariable.get
  match persistent, memoryVar with
  | some memory, some var =>
    match Bil.lookup state.env var with
    | .ok (@Value.memory width cells) =>
      writes.forM fun write => do
        let addresses := (List.range write.2).map fun offset => UInt64.ofNat (write.1 + offset)
        let values := (List.range write.2).map fun offset =>
          Bap.Memory.readByte cells (BitVec.ofNat width (write.1 + offset))
        Jit.writeMemory memory addresses.toArray values.toArray
    | _ => discardMemory engine
  | _, _ => pure ()

/-- The memory of `state` with the bytes of the native memory at everything `program` reads. A worker of a
parallel round writes to native memory only, so that the memory of its state is stale, and what an instruction
reads depends on what it reads, which `readThroughM` follows. -/
private def readThrough (memory : Jit.Memory) (var : Bap.Var) (program : Bil.Program) (state : Bil.State) :
    IO Bil.State := do
  match Bil.lookup state.env var with
  | .ok (@Value.memory width cells) =>
    let reads (cells : Bap.Memory width) : IO (List (Nat × Nat)) := do
      let collected ← IO.mkRef []
      let observer : Bil.MemoryObserver := fun write address size _ =>
        if write then pure () else collected.modify ((address, size) :: ·)
      let _ ← Bil.runObserved (some observer) program { env := Bil.bind state.env var (.memory cells) }
      collected.get
    let native (address : Nat) : IO UInt8 := Jit.readMemory memory (UInt64.ofNat address)
    match ← Bap.Emu.readThroughM reads native 16 cells with
    | some cells => pure { env := Bil.bind state.env var (.memory cells) }
    | none =>
      -- It keeps reading elsewhere: all of the memory, then.
      let (addresses, values) ← Jit.dumpMemory memory
      let cells := Bap.Memory.writeSortedCells (Bap.Memory.empty width)
        ((addresses.zip values).toList.map fun cell => (BitVec.ofNat width cell.1.toNat, cell.2))
      pure { env := Bil.bind state.env var (.memory cells) }
  | _ => pure state

private def runInterpreted (engine : Engine) (next pc : Nat) (program : Bil.Program)
    (state : Bil.State) (observer : Option Jit.MemoryObserver) : IO Result := do
  let writes ← IO.mkRef []
  let observed : Option Jit.MemoryObserver := some fun write address size value => do
    observer.forM fun notify => notify write address size value
    if write then writes.modify fun current => (address, size) :: current
  recordInterpreted engine
  let state ← if engine.deferMemorySync then
      match ← engine.persistentMemory.get, ← engine.persistentVariable.get with
      | some memory, some var => readThrough memory var program state
      | _, _ => pure state
    else pure state
  match ← Bil.runObserved observed program state with
  | .error error =>
    discardMemory engine
    throw <| IO.userError error
  | .ok (state, effect) => do
    syncInterpretedWrites engine (← writes.get) state
    match effect with
    | .normal => return ⟨state, next, next, .normal⟩
    | .jump target => return ⟨state, target.toNat, next, .jump target⟩
    | _ => return ⟨state, pc, next, effect⟩

/-- The control slots of a compiled range, and what the run may do. -/
private def withControl (lowering : Lowering) (slots : Array UInt64) (budget : Nat) (observed : Bool) : Array UInt64 :=
  let slots := match lowering.budget with
    | some slot => slots.set! slot (UInt64.ofNat budget)
    | none => slots
  match lowering.observed with
  | some slot => slots.set! slot (if observed then 1 else 0)
  | none => slots

/-- The blocks that a run entered after its first, out of its budget. -/
private def chainedCount (lowering : Lowering) (budget : Nat) (slots : Array UInt64) : Option Nat :=
  lowering.budget.map fun slot => budget - (slots.getD slot 0).toNat

private def recordChained (engine : Engine) (lowering : Lowering) (budget : Nat) (slots : Array UInt64) : IO Unit :=
  (chainedCount lowering budget slots).forM engine.chained.set

private def runPersistent (engine : Engine) (lowering : Lowering) (following : Nat)
    (program : Jit.Program) (state : Bil.State) (slots : Array UInt64)
    (memory : Jit.Memory) (observer : Option Jit.MemoryObserver)
    (codeObserver : Option Jit.CodeObserver) (budget : Nat) : IO Result := do
  recordNative engine
  let (next, slots, addresses, values) ←
    Jit.runWithPersistentMemoryObservedCode program slots memory observer codeObserver
  recordChained engine lowering budget slots
  let completed := atCodeStop lowering next
  let state := if engine.deferMemorySync then syncState completed state slots
    else syncMemoryDelta completed (syncState completed state slots) addresses values
  nativeResult lowering following next state slots

def runBlockObserved (engine : Engine) (fetch : Fetch) (lift : Lift) (state : Bil.State) (pc : Nat)
    (observer : Option Jit.MemoryObserver) (codeObserver : Option Jit.CodeObserver := none)
    (observed : Bool := true) (budget : Nat := engine.rangeLimit) : IO Result := do
  -- A run cannot chain more than the slot that counts them holds.
  let budget := min budget (2 ^ 64 - 1)
  engine.nativeCooldown.modify fun cooldown => if cooldown = 0 then 0 else cooldown - 1
  engine.chained.set 0
  let code ← fetch pc
  let entry ← prepareGraph engine fetch lift pc code budget
  match entry.plan with
  | .interpreted program => runInterpreted engine entry.next pc program state observer
  | .native lowering program fallback =>
    match encodeState lowering state.env with
    | .error _ => runInterpreted engine entry.firstNext pc fallback state observer
    | .ok slots => do
      let slots := withControl lowering slots budget observed
      let persistent ← engine.persistentMemory.get
      match persistent, lowering.memory with
      | some memory, some _ =>
        runPersistent engine lowering entry.next program state slots memory observer codeObserver budget
      | _, _ =>
        match memoryInput lowering state with
        | .error _ => runInterpreted engine entry.firstNext pc fallback state observer
        | .ok (addresses, values) =>
          if lowering.memory.isSome && addresses.size ≥ engine.persistentFrom then do
            let memory ← Jit.createMemory addresses values
            engine.persistentMemory.set (some memory)
            engine.persistentVariable.set lowering.memory
            runPersistent engine lowering entry.next program state slots memory observer codeObserver budget
          else do
            recordNative engine
            let (next, slots, addresses, values) ←
              Jit.runWithMemoryObservedCode program slots addresses values observer codeObserver
            recordChained engine lowering budget slots
            let completed := atCodeStop lowering next
            let state := syncMemory completed (syncState completed state slots) addresses values
            nativeResult lowering entry.next next state slots

/-- A run of a block, or of the range that starts there, up to `rangeLimit` blocks after the first. -/
def runBlock (engine : Engine) (fetch : Fetch) (lift : Lift) (state : Bil.State) (pc : Nat) :
    IO Result :=
  runBlockObserved engine fetch lift state pc none

/-- Runs until a block does not end in a jump, out of `fuel` blocks. A range counts for all that it entered. -/
def run (engine : Engine) (fetch : Fetch) (lift : Lift) (initial : Bil.State) (entry : Nat)
    (fuel : Nat := 100000) : IO Result := do
  let rec loop (state : Bil.State) (pc : Nat) (remaining : Nat) : Nat → IO Result
    | 0 => throw <| IO.userError "lifted execution fuel exhausted"
    | rounds + 1 => do
      if remaining = 0 then throw <| IO.userError "lifted execution fuel exhausted"
      let result ← runBlockObserved engine fetch lift state pc none (budget := remaining - 1)
      match result.effect with
      | .jump _ =>
        let chained ← engine.chained.get
        loop result.state result.pc (remaining - 1 - min chained (remaining - 1)) rounds
      | _ => return result
  loop initial entry fuel fuel

end Bap.Primus.Lifted
