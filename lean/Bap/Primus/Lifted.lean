import Bap.Jit
import Bap.Bil.Observe
import Bap.Primus.Machine
import Std.Data.HashMap

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
  executions : Nat
  plan : Plan

structure Engine where
  cache : IO.Ref (Std.HashMap Nat CachedBlock)
  ranges : IO.Ref (Std.HashMap Nat CachedBlock)
  statistics : IO.Ref Statistics
  persistentMemory : IO.Ref (Option Jit.Memory)
  persistentVariable : IO.Ref (Option Bap.Var)
  hotThreshold : Nat
  cacheLimit : Nat
  rangeLimit : Nat
  rangeCacheLimit : Nat
  writeCooldown : Nat
  nativeCooldown : IO.Ref Nat

structure Result where
  state : Bil.State
  pc : Nat
  next : Nat
  effect : Bil.Effect
  deriving Repr

def Engine.create (hotThreshold : Nat := 1) (cacheLimit : Nat := 128) (rangeLimit : Nat := 1)
    (rangeCacheLimit : Nat := 16) (writeCooldown : Nat := 0) : IO Engine := do
  return {
    cache := ← IO.mkRef {}
    ranges := ← IO.mkRef {}
    statistics := ← IO.mkRef {}
    persistentMemory := ← IO.mkRef none
    persistentVariable := ← IO.mkRef none
    hotThreshold := max hotThreshold 1
    cacheLimit := max cacheLimit 1
    rangeLimit := max rangeLimit 1
    rangeCacheLimit := max rangeCacheLimit 1
    writeCooldown
    nativeCooldown := ← IO.mkRef 0
  }

def stats (engine : Engine) : IO Statistics := engine.statistics.get

def clearCache (engine : Engine) : IO Unit := do
  engine.cache.set {}
  engine.ranges.set {}

def discardRange (engine : Engine) (first last : Nat) : IO Unit := do
  engine.cache.modify fun entries => entries.filter fun address _ => address < first || last < address
  engine.ranges.modify fun entries => entries.filter fun _ entry => entry.last < first || last < entry.address
  if engine.writeCooldown > 0 then engine.nativeCooldown.set (engine.writeCooldown + 1)

def discardMemory (engine : Engine) : IO Unit := do
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

private def writeVar (lowering : Lowering) (var : Bap.Var) : Option (Lowering × Nat) := do
  let _ ← widthOf var
  let (lowering, index) := slot lowering var
  let lowering := { lowering with outputs := lowering.outputs ++ [(var, index)] }
  let lowering :=
    if lowering.written.contains var then lowering
    else { lowering with written := lowering.written ++ [var] }
  some (lowering, index)

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

private def useMemory (lowering : Lowering) (var : Bap.Var) : Option Lowering :=
  match var.typ, lowering.memory with
  | .mem _ _, none => some { lowering with memory := some var }
  | .mem _ _, some existing => if existing == var then some lowering else none
  | _, _ => none

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
    let lowering ← useMemory lowering memory
    let (lowering, address) ← lowerExp lowering address
    if size = 0 || size > 8 then none
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
    let (lowering, remainder) := temporary lowering
    let lowering := { lowering with ops := lowering.ops ++ [.bin .urem remainder left.slot right.slot] }
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
    let lowering ← useMemory lowering memory
    let (lowering, address) ← lowerExp lowering address
    let (lowering, stored) ← lowerExp lowering stored
    if size = 0 || size > 8 || stored.width != size * 8 then none
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
    | .jmp (.int target) => some (jumpConstant lowering (immediate target), true)
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
      let resultLowering := if yesTerminated then noLowering.1
        else if noLowering.2 then yesLowering else noLowering.1
      let resultOps := noLowering.1.ops ++
        (if noLowering.2 then [] else [.goto doneLabel]) ++
        (if yesTerminated && noLowering.2 then [] else [.label doneLabel])
      some ({ resultLowering with ops := resultOps }, yesTerminated && noLowering.2)
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
        [.label doneLabel, .jump (UInt64.ofNat lowering.next), .label exhaustedLabel]
      let (resultLowering, _) := setEffect { bodyLowering with ops := bodyOps } 2
      some (resultLowering, false)
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

private def lowerRange (blocks : List Block) : Option Lowering := do
  let final ← blocks.getLast?
  let (initial, _) := setEffect { next := final.next } 0
  let rec go (lowering : Lowering) (remaining : List Block) : Option Lowering :=
    match remaining with
    | [] => some { lowering with ops := lowering.ops ++ [.jump (UInt64.ofNat final.next)] }
    | [block] => do
      let (lowering, terminated) ← lowerStatements lowering block.program
      if terminated then some lowering
      else some { lowering with ops := lowering.ops ++ [.jump (UInt64.ofNat block.next)] }
    | block :: rest => do
      let (lowering, terminated) ← lowerStatements lowering block.program.dropLast
      if terminated then none
      else go (codeSite lowering rest.head!.address) rest
  go initial blocks

private def compileRangePlan (engine : Engine) (blocks : List Block) : IO (Option Plan) := do
  match lowerRange blocks with
  | none => pure none
  | some lowering =>
    let program ← Jit.compile lowering.ops
    engine.statistics.modify fun stats =>
      { stats with nativeCompilations := stats.nativeCompilations + 1 }
    pure (some (.native lowering program blocks.head!.program))

private def compilePlan (engine : Engine) (block : Block) : IO Plan := do
  match ← compileRangePlan engine [block] with
  | some plan => pure plan
  | none => pure (.interpreted block.program)

private def prepare (engine : Engine) (lift : Lift) (address : Nat) (code : ByteArray) :
    IO CachedBlock := do
  let entries ← engine.cache.get
  let cooldown ← engine.nativeCooldown.get
  let miss := do
    let entries ← if entries.size ≥ engine.cacheLimit then do
      clearCache engine
      pure {}
    else
      pure entries
    engine.statistics.modify fun stats => { stats with lifts := stats.lifts + 1 }
    let block ← lift address code
    if block.address != address then
      throw <| IO.userError s!"lifted block address {block.address} does not match {address}"
    let plan ← if engine.hotThreshold = 1 && cooldown = 0 then compilePlan engine block
      else pure (.interpreted block.program)
    let entry : CachedBlock := {
      address, code, next := block.next, firstNext := block.next, last := address, executions := 1, plan
    }
    engine.cache.set (entries.insert address entry)
    return entry
  match entries.get? address with
  | some entry =>
    if entry.code == code then do
      engine.statistics.modify fun stats => { stats with cacheHits := stats.cacheHits + 1 }
      let executions := entry.executions + 1
      let shouldCompile := cooldown = 0 && executions ≥ engine.hotThreshold &&
        match entry.plan with
        | .interpreted _ => true
        | .native _ _ _ => false
      let plan ← if shouldCompile then
        match entry.plan with
        | .interpreted program => compilePlan engine ⟨entry.address, entry.next, program⟩
        | .native .. => pure entry.plan
      else
        pure entry.plan
      let updated := { entry with executions, plan }
      engine.cache.set (entries.insert address updated)
      return updated
    else
      miss
  | none => miss

private def directFallthrough (block : Block) : Bool :=
  match block.program.getLast? with
  | some (.jmp (.int target)) => target.toNat = block.next
  | _ => false

private def prepareRange (engine : Engine) (fetch : Fetch) (lift : Lift)
    (address : Nat) (code : ByteArray) : IO CachedBlock := do
  if engine.rangeLimit = 1 then prepare engine lift address code
  else
    let ranges ← engine.ranges.get
    match ranges.get? address with
    | some entry =>
      engine.statistics.modify fun stats => { stats with cacheHits := stats.cacheHits + 1 }
      return entry
    | none => do
      let first ← prepare engine lift address code
      match first.plan with
      | .interpreted _ => return first
      | .native .. => do
        let firstProgram := match first.plan with
          | .native _ _ fallback => fallback
          | .interpreted program => program
        let rec gather (remaining : Nat) (previous : Block) (blocks : List Block) : IO (List Block) := do
          match remaining with
          | 0 | 1 => pure blocks
          | remaining + 2 =>
            if !directFallthrough previous then pure blocks
            else
              let next := previous.next
              let nextCode ← fetch next
              engine.statistics.modify fun stats => { stats with lifts := stats.lifts + 1 }
              let block ← lift next nextCode
              if block.address != next then
                throw <| IO.userError s!"lifted range block address {block.address} does not match {next}"
              gather (remaining + 1) block (blocks ++ [block])
        let blocks ← gather engine.rangeLimit ⟨first.address, first.next, firstProgram⟩ []
        if blocks.length = 0 then return first
        else
          match ← compileRangePlan engine (⟨first.address, first.next, firstProgram⟩ :: blocks) with
          | none => return first
          | some plan =>
            let all := ⟨first.address, first.next, firstProgram⟩ :: blocks
            let final := all.getLast!
            let entry := { first with next := final.next, last := final.address, plan }
            if ranges.size ≥ engine.rangeCacheLimit then engine.ranges.set {}
            engine.ranges.modify (·.insert address entry)
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

private def syncState (lowering : Lowering) (state : Bil.State) (slots : Array UInt64) : Bil.State :=
  lowering.outputs.foldl (init := state) fun state output =>
    match widthOf output.1 with
    | some width =>
      let value := (slots.getD output.2 0).toNat
      { env := Bil.bind state.env output.1 (.bits (BitVec.ofNat width value)) }
    | none => state

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
          let updated := (addresses.zip values).foldl (init := memory) fun memory cell =>
            Bap.Memory.writeByte memory (BitVec.ofNat width cell.1.toNat) cell.2
          { env := Bil.bind state.env var (.memory updated) }
        else state
      | _, _ => state

private def nativeResult (lowering : Lowering) (following : Nat) (next : Nat)
    (state : Bil.State) (slots : Array UInt64) : IO Result := do
  let effect : UInt64 := match lowering.effectSlot with
    | some slot => slots.getD slot 0
    | none => 0
  if effect == 1 then
    return ⟨state, next, following, .jump (BitVec.ofNat 64 next)⟩
  else if effect == 2 then
    throw <| IO.userError "Primus loop fuel exhausted"
  else if effect == 3 then
    return ⟨state, next, next, .normal⟩
  else
    return ⟨state, next, following, .normal⟩

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

private def runInterpreted (engine : Engine) (next pc : Nat) (program : Bil.Program)
    (state : Bil.State) (observer : Option Jit.MemoryObserver) : IO Result := do
  let writes ← IO.mkRef []
  let observed := some fun write address size value => do
    observer.forM fun notify => notify write address size value
    if write then writes.modify fun current => (address, size) :: current
  recordInterpreted engine
  match ← Bil.runObserved observed program state with
  | .error error =>
    discardMemory engine
    throw <| IO.userError error
  | .ok (state, effect) => do
    syncInterpretedWrites engine (← writes.get) state
    match effect with
    | .normal => return ⟨state, next, next, .normal⟩
    | .jump target => return ⟨state, target.toNat, target.toNat, .jump target⟩
    | _ => return ⟨state, pc, next, effect⟩

private def runPersistent (engine : Engine) (lowering : Lowering) (following : Nat)
    (program : Jit.Program) (state : Bil.State) (slots : Array UInt64)
    (memory : Jit.Memory) (observer : Option Jit.MemoryObserver)
    (codeObserver : Option Jit.CodeObserver) : IO Result := do
  recordNative engine
  let (next, slots, addresses, values) ←
    Jit.runWithPersistentMemoryObservedCode program slots memory observer codeObserver
  let completed := atCodeStop lowering next
  let state := syncMemoryDelta completed (syncState completed state slots) addresses values
  nativeResult lowering following next state slots

def runBlockObserved (engine : Engine) (fetch : Fetch) (lift : Lift) (state : Bil.State) (pc : Nat)
    (observer : Option Jit.MemoryObserver) (codeObserver : Option Jit.CodeObserver := none) : IO Result := do
  engine.nativeCooldown.modify fun cooldown => if cooldown = 0 then 0 else cooldown - 1
  let code ← fetch pc
  let entry ← prepareRange engine fetch lift pc code
  match entry.plan with
  | .interpreted program => runInterpreted engine entry.next pc program state observer
  | .native lowering program fallback =>
    match encodeState lowering state.env with
    | .error _ => runInterpreted engine entry.firstNext pc fallback state observer
    | .ok slots => do
      let persistent ← engine.persistentMemory.get
      match persistent, lowering.memory with
      | some memory, some _ =>
        runPersistent engine lowering entry.next program state slots memory observer codeObserver
      | _, _ =>
        match memoryInput lowering state with
        | .error _ => runInterpreted engine entry.firstNext pc fallback state observer
        | .ok (addresses, values) =>
          if addresses.size ≥ 100000 then do
            let memory ← Jit.createMemory addresses values
            engine.persistentMemory.set (some memory)
            engine.persistentVariable.set lowering.memory
            runPersistent engine lowering entry.next program state slots memory observer codeObserver
          else do
            recordNative engine
            let (next, slots, addresses, values) ←
              Jit.runWithMemoryObservedCode program slots addresses values observer codeObserver
            let completed := atCodeStop lowering next
            let state := syncMemory completed (syncState completed state slots) addresses values
            nativeResult lowering entry.next next state slots

def runBlock (engine : Engine) (fetch : Fetch) (lift : Lift) (state : Bil.State) (pc : Nat) :
    IO Result :=
  runBlockObserved engine fetch lift state pc none

def run (engine : Engine) (fetch : Fetch) (lift : Lift) (initial : Bil.State) (entry : Nat)
    (fuel : Nat := 100000) : IO Result := do
  let rec loop (state : Bil.State) (pc : Nat) : Nat → IO Result
    | 0 => throw <| IO.userError "lifted execution fuel exhausted"
    | fuel + 1 => do
      let result ← runBlock engine fetch lift state pc
      match result.effect with
      | .jump _ => loop result.state result.pc fuel
      | _ => return result
  loop initial entry fuel

end Bap.Primus.Lifted
