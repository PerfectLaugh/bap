import Bap.Bil.Syntax

namespace Bap.Bil

private def expectImm : Typ → Except String Nat
  | .imm width => .ok width
  | typ => .error s!"expected an immediate type, got {repr typ}"

private def expectSameType (left right : Typ) : Except String Unit :=
  if left = right then .ok () else .error s!"type mismatch: {repr left} and {repr right}"

/-- Only types with bits have values: BIL has no size and SMT-LIB no sort for anything else. -/
private def expectBits : Typ → Except String Typ
  | .imm 0 => .error "a value must have at least one bit"
  | .mem 0 _ | .mem _ 0 => .error "a memory must have addresses and cells of at least one bit"
  | typ => .ok typ

def inferExp : Exp → Except String Typ
  | @Exp.int width _ => expectBits (.imm width)
  | .var var => expectBits var.typ
  | .load memory address _ size => do
    match ← inferExp memory with
    | .mem addressWidth valueWidth =>
      if valueWidth = 8 then
        let actual ← expectImm (← inferExp address)
        if actual = addressWidth then
          if size = 0 then .error "a load must have at least one byte" else .ok (.imm (size * 8))
        else
          .error "address width does not match memory"
      else
        .error "BIL memory cells must be bytes"
    | typ => .error s!"expected memory, got {repr typ}"
  | .store memory address value _ size => do
    let memoryType ← inferExp memory
    match memoryType with
    | .mem addressWidth cellWidth =>
      if cellWidth ≠ 8 then
        .error "BIL memory cells must be bytes"
      else
        let actual ← expectImm (← inferExp address)
        if actual ≠ addressWidth then
          .error "address width does not match memory"
        else
          let valueWidth ← expectImm (← inferExp value)
          if valueWidth ≠ size * 8 then
            .error "stored value has the wrong width"
          else if size = 0 then
            .error "a store must have at least one byte"
          else if size > 2 ^ addressWidth then
            .error "a store must not overlap itself"
          else
            .ok memoryType
    | typ => .error s!"expected memory, got {repr typ}"
  | .bin op left right => do
    let leftType ← inferExp left
    let rightType ← inferExp right
    let leftWidth ← expectImm leftType
    let rightWidth ← expectImm rightType
    if leftWidth ≠ rightWidth then
      .error "binary operands have different widths"
    else
      match op with
      | .eq | .neq | .lt | .le | .gt | .ge | .slt | .sle | .sgt | .sge => .ok (.imm 1)
      | _ => .ok (.imm leftWidth)
  | .un _ value => do
    .ok (.imm (← expectImm (← inferExp value)))
  | .cast kind width value => do
    let source ← expectImm (← inferExp value)
    if width = 0 then
      .error "cast width must be positive"
    else
      match kind with
      | .low | .high =>
        if width ≤ source then .ok (.imm width) else .error "cast is wider than its operand"
      | .signed | .unsigned => .ok (.imm width)
  | .letIn var value body => do
    let valueType ← inferExp value
    if var.typ ≠ valueType then
      .error s!"let binding for {var.name} has the wrong type"
    else
      inferExp body
  | .ite condition yes no => do
    let conditionWidth ← expectImm (← inferExp condition)
    if conditionWidth ≠ 1 then
      .error "condition must be one bit"
    else
      let yesType ← inferExp yes
      let noType ← inferExp no
      expectSameType yesType noType
      .ok yesType
  | .extract high low value => do
    let width ← expectImm (← inferExp value)
    if high < low then
      .error "extract high bound is below low bound"
    else if high ≥ width then
      .error "extract high bound exceeds source width"
    else
      .ok (.imm (high - low + 1))
  | .concat left right => do
    let leftWidth ← expectImm (← inferExp left)
    let rightWidth ← expectImm (← inferExp right)
    .ok (.imm (leftWidth + rightWidth))
  | .unknown _ typ => expectBits typ

private def checkCondition (condition : Exp) : Except String Unit := do
  let width ← expectImm (← inferExp condition)
  if width = 1 then .ok () else .error "condition must be one bit"

mutual
  def checkStmt : Stmt → Except String Unit
    | .move var value => do
      let typ ← inferExp value
      if var.typ = typ then .ok () else .error s!"assignment to {var.name} has the wrong type"
    | .jmp target => do
      let _ ← expectImm (← inferExp target)
      .ok ()
    | .special _ | .cpuExn _ => .ok ()
    | .while condition body => do
      checkCondition condition
      checkProgram body
    | .ifElse condition yes no => do
      checkCondition condition
      checkProgram yes
      checkProgram no

  def checkProgram : Program → Except String Unit
    | [] => .ok ()
    | stmt :: rest => do
      checkStmt stmt
      checkProgram rest
end

end Bap.Bil
