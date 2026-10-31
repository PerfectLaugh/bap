import BapTests.Support

namespace Bap.Tests.Optimize

open Bap
open Bap.Bil
open Bap.IR

private def reg (name : String) : Var := ⟨name, .imm 32, 0, false⟩
private def mem : Var := ⟨"mem", .mem 32 8, 0, false⟩
private def x := reg "x"
private def y := reg "y"
private def z := reg "z"
private def int (value : Nat) : Exp := .int (BitVec.ofNat 32 value)
private def defn (tid : Tid) (var : Var) (rhs : Exp) : Def := ⟨tid, var, rhs⟩
private def goto (tid destination : Tid) : Jmp := ⟨tid, none, .goto (.direct destination)⟩
private def expString (exp : Exp) : String := toString (Wire.printExp exp)

private def sample : Sub :=
  let store := Exp.store (.var mem) (int 0) (.var z) .little 4
  {
    tid := 1
    name := "optimize"
    blks := [
      ⟨1, [], [defn 1 x (int 40)], [goto 1 2]⟩,
      ⟨2, [], [defn 2 y (.bin .add (.var x) (int 2))], [goto 2 3]⟩,
      ⟨3, [], [defn 3 z (.var y), defn 4 mem store], [⟨5, none, .goto (.indirect (.var z))⟩]⟩,
      ⟨99, [], [defn 99 (reg "unused") (int 9)], []⟩
    ]
  }

/-- `x := z; y := x` followed by a jump that reads `y`. -/
private def usedInBlock : Sub :=
  ⟨1, "used-in-block", [], [
    ⟨1, [], [defn 1 x (.var z), defn 2 y (.var x)], [goto 3 2]⟩,
    ⟨2, [], [], [⟨4, some (.var y), .ret (.indirect (.var y))⟩]⟩]⟩

/-- `x := z; x := y` followed by a jump that reads `x`: the first write is dead. -/
private def overwritten : Sub :=
  ⟨1, "overwritten", [], [
    ⟨1, [], [defn 1 x (.var z), defn 2 x (.var y)], [⟨3, none, .ret (.indirect (.var x))⟩]⟩]⟩

/-- `x := 1; L: y := x; x := 2; if z goto L else M; M: ret y`. -/
private def loop : Sub :=
  ⟨1, "loop", [], [
    ⟨1, [], [defn 1 x (int 1)], [goto 2 2]⟩,
    ⟨2, [], [defn 3 y (.var x), defn 4 x (int 2)], [⟨5, some (.var z), .goto (.direct 2)⟩, goto 6 3]⟩,
    ⟨3, [], [], [⟨7, none, .ret (.indirect (.var y))⟩]⟩]⟩

/-- `L: y := x; x := 1; goto L`: the entry state of `x` is unknown on the first iteration. -/
private def entryLoop : Sub :=
  ⟨1, "entry-loop", [], [
    ⟨1, [], [defn 1 y (.var x), defn 2 x (int 1)], [goto 3 1]⟩]⟩

/-- `x := 1; L: y := x; if z goto L else M`: `x` is 1 on every path into `L`. -/
private def stableLoop : Sub :=
  ⟨1, "stable-loop", [], [
    ⟨1, [], [defn 1 x (int 1)], [goto 2 2]⟩,
    ⟨2, [], [defn 3 y (.var x)], [⟨4, some (.var z), .goto (.direct 2)⟩, goto 5 3]⟩,
    ⟨3, [], [], []⟩]⟩

/-- `x := z; y := 7; ret z`: nothing in the subroutine reads `x` or `y`. -/
private def deadOutputs : Sub :=
  ⟨1, "dead-outputs", [], [
    ⟨1, [], [defn 1 x (.var z), defn 2 y (int 7)], [⟨3, none, .ret (.indirect (.var z))⟩]⟩]⟩

/-- `x := z; goto L; L: y := 1; ret z`: `x` is written in the block before the exit. -/
private def outputAcrossBlocks : Sub :=
  ⟨1, "output-across-blocks", [], [
    ⟨1, [], [defn 1 x (.var z)], [goto 2 2]⟩,
    ⟨2, [], [defn 3 y (int 1)], [⟨4, none, .ret (.indirect (.var z))⟩]⟩]⟩

/-- `x := y; x := z; ret z`: only the last write to `x` reaches the end of the block. -/
private def overwrittenOutput : Sub :=
  ⟨1, "overwritten-output", [], [
    ⟨1, [], [defn 1 x (.var y), defn 2 x (.var z)], [⟨3, none, .ret (.indirect (.var z))⟩]⟩]⟩

/-- `y := z; x := y; ret z`: the protected `x` keeps the write to `y` that feeds it alive. -/
private def outputChain : Sub :=
  ⟨1, "output-chain", [], [
    ⟨1, [], [defn 1 y (.var z), defn 2 x (.var y)], [⟨3, none, .ret (.indirect (.var z))⟩]⟩]⟩

/-- `x := z; ret x`: the jump alone reads `x`. -/
private def readByJump : Sub :=
  ⟨1, "read-by-jump", [], [⟨1, [], [defn 1 x (.var z)], [⟨2, none, .ret (.indirect (.var x))⟩]⟩]⟩

/-- `goto L; L: ret z`: only the jump of `L` reads `z`, and nothing writes it. -/
private def readOnJump : Sub :=
  ⟨1, "read-on-jump", [], [⟨1, [], [], [goto 1 2]⟩, ⟨2, [], [], [⟨2, none, .ret (.indirect (.var z))⟩]⟩]⟩

/-- `if z goto A else B; A: x := 1; goto J; B: x := 2; goto J; J: ret y`: `x` is an output with a version per arm. -/
private def branchOutput : Sub :=
  ⟨1, "branch-output", [], [
    ⟨1, [], [], [⟨1, some (.var z), .goto (.direct 2)⟩, goto 2 3]⟩,
    ⟨2, [], [defn 3 x (int 1)], [goto 4 4]⟩,
    ⟨3, [], [defn 5 x (int 2)], [goto 6 4]⟩,
    ⟨4, [], [], [⟨7, none, .ret (.indirect (.var y))⟩]⟩]⟩

private def definedVars (sub : Sub) (tid : Tid) : List String :=
  (sub.block tid).map (fun blk => blk.defs.map (·.var.name)) |>.getD []

/-- The protected names of an SSA form: an unversioned output covers all its versions. -/
private def ssaRegressions : IO Unit := do
  let ssa := toSsa branchOutput
  let deadSsa := optimize ssa
  assertEqual "without protection the SSA output dies" [] (definedVars deadSsa 2)
  assertEqual "without protection its phi dies too" 0 ((deadSsa.block 4).map (·.phis.length) |>.getD 999)
  let kept := optimize ssa [x]
  assertEqual "an unversioned output protects its versions" ["x"] (definedVars kept 2)
  assertEqual "in every arm" ["x"] (definedVars kept 3)
  assertEqual "and its phi at the join" 1 ((kept.block 4).map (·.phis.length) |>.getD 0)
  let exact := optimize ssa [x.version 1]
  assertEqual "a versioned output protects just that version" [(1 : Nat)]
    (((exact.block 2).map (fun blk => blk.defs.map (·.var.index)) |>.getD []))
  assertEqual "not the other arm" [] (definedVars exact 3)

private def protectedRegressions : IO Unit := do
  assertEqual "protected write survives" ["x"] (definedVars (optimize deadOutputs [x]) 1)
  assertEqual "unprotected dead writes removed" [] (definedVars (optimize deadOutputs) 1)
  assertEqual "protected constant write survives, unprotected removed" ["y"] (definedVars (optimize deadOutputs [y]) 1)
  let across := optimize outputAcrossBlocks [x]
  assertEqual "protected write survives before a successor" ["x"] (definedVars across 1)
  assertEqual "dead write in the successor removed" [] (definedVars across 2)
  assertEqual "without protection the write across blocks is removed" []
    (definedVars (optimize outputAcrossBlocks) 1)
  match (optimize overwrittenOutput [x]).block 1 with
  | some blk =>
    assertEqual "only the last protected write survives" [expString (.var z)] (blk.defs.map (expString ·.rhs))
  | none => throw <| IO.userError "missing overwritten block"
  assertEqual "a protected write keeps what it reads" ["y", "x"] (definedVars (optimize outputChain [x]) 1)
  assertEqual "the chain dies without protection" [] (definedVars (optimize outputChain) 1)
  assertEqual "a read through a jump keeps the write" ["x"] (definedVars (optimize readByJump) 1)
  assertEqual "a read through a jump keeps the write when protected too" ["x"]
    (definedVars (optimize readByJump [x]) 1)
  let versioned : Var := x.version 1
  assertEqual "protection matches the exact variable" [] (definedVars (optimize deadOutputs [versioned]) 1)
  let cfg := Cfg.fromSub deadOutputs
  assertEqual "eliminateDeadCode takes the protected list" 1
    ((eliminateDeadCode cfg [x]).block 1 |>.map (·.defs.length) |>.getD 0)
  assertEqual "eliminateDeadCode defaults to none" 0
    ((eliminateDeadCode cfg).block 1 |>.map (·.defs.length) |>.getD 999)

private def regressions : IO Unit := do
  protectedRegressions
  ssaRegressions
  match (propagateConstants (Cfg.fromSub stableLoop)).block 2 with
  | some block =>
    match block.defs with
    | [read] => assertEqual "constant stable around a loop is folded" (expString (int 1)) (expString read.rhs)
    | _ => throw <| IO.userError "missing stable loop definition"
  | none => throw <| IO.userError "missing stable loop block"
  let kept := (optimize usedInBlock).block 1 |>.map (·.defs.length) |>.getD 0
  assertEqual "definition read later in its block survives" 2 kept
  let single := (optimize overwritten).block 1 |>.map (fun blk => blk.defs.map (expString ·.rhs)) |>.getD []
  assertEqual "overwritten definition removed" [expString (.var y)] single
  match (propagateConstants (Cfg.fromSub loop)).block 2 with
  | some block =>
    match block.defs with
    | [read, _] => assertEqual "loop read not folded to first iteration" (expString (.var x)) (expString read.rhs)
    | _ => throw <| IO.userError "missing loop definitions"
  | none => throw <| IO.userError "missing loop block"
  match (propagateConstants (Cfg.fromSub entryLoop)).block 1 with
  | some block =>
    match block.defs with
    | [read, _] => assertEqual "entry state stays unknown" (expString (.var x)) (expString read.rhs)
    | _ => throw <| IO.userError "missing entry definitions"
  | none => throw <| IO.userError "missing entry block"
  let straight : Sub := ⟨1, "straight", [], [⟨1, [], [], [goto 1 2]⟩, ⟨2, [], [], []⟩]⟩
  let (ins, outs) := (Cfg.fromSub straight).livenessFrom 2 [x]
  assertTrue "seed live out of the exit" ((Assoc.get 2 outs).getD [] |>.contains x)
  assertTrue "seed live into the exit" ((Assoc.get 2 ins).getD [] |>.contains x)
  assertTrue "seed reaches the predecessor" ((Assoc.get 1 ins).getD [] |>.contains x)

local macro "dcePass" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.dcePass)

/-- `eliminateDeadCode` as it reads: a pass over everything until a pass changes nothing. -/
private def deadCodeBySpec (protectedVars : List Var) (cfg : Cfg) : Nat → Cfg
  | 0 => cfg
  | fuel + 1 =>
    let next := dcePass protectedVars cfg
    let sizes (cfg : Cfg) : List (Nat × Nat) := cfg.blocks.map fun blk => (blk.defs.length, blk.phis.length)
    if sizes cfg = sizes next then cfg else deadCodeBySpec protectedVars next fuel

private def sameDeadCode (name : String) (sub : Sub) (protectedVars : List Var := []) : IO Unit := do
  let cfg := Cfg.fromSub sub
  let count := cfg.blocks.foldl (fun count blk => count + blk.defs.length + blk.phis.length) 0
  let expected := Wire.printSub ((deadCodeBySpec protectedVars cfg (count + 1)).intoSub sub)
  assertEqual name (toString expected) (toString (Wire.printSub ((eliminateDeadCode cfg protectedVars).intoSub sub)))

local macro "propagateAux" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.propagateAux)
local macro "propagateFuel" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.propagateFuel)
local macro "entryEnv" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.entryEnv)
local macro "isSolved" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.isSolved)
local macro "propagateBlock" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.propagateBlock)

/-- `propagateConstants` as it reads: its lists, and a block rewritten for what it says of its constants. -/
private def constantsBySpec (cfg : Cfg) : Cfg :=
  let cfg := cfg.prune
  let exits := propagateAux cfg (propagateFuel cfg) [] [cfg.start]
  let solved := isSolved cfg exits
  { cfg with blocks := cfg.blocks.map fun blk =>
    (propagateBlock blk (if solved then entryEnv cfg exits blk.tid else [])).1
  }

private def sameConstants (name : String) (sub : Sub) : IO Unit :=
  let cfg := Cfg.fromSub sub
  assertEqual s!"constants of {name}" (toString (Wire.printSub ((constantsBySpec cfg).intoSub sub)))
    (toString (Wire.printSub ((propagateConstants cfg).intoSub sub)))

/-- From a real instruction sequence: a block per basic block and its moves, jumps by flow. -/
private def stmtDefs : Nat → Bil.Program → List Def
  | _, [] => []
  | t, .move v e :: rest => ⟨t, v, e⟩ :: stmtDefs (t + 1) rest
  | t, _ :: rest => stmtDefs (t + 1) rest

private def subOfDisasm (disasm : Disasm.Disasm) : Sub :=
  let blocks := disasm.blocks
  let flag := reg "ZF"
  let blks : List Blk := blocks.map fun block =>
    let defs := block.instructions.flatMap fun insn => stmtDefs (insn.address * 100) insn.bil
    let successors := (block.instructions.getLast?.map (·.successors)).getD []
    let jmps : List Jmp := match successors with
      | [] => [⟨block.start * 100 + 90, none, .ret (.indirect (.var (reg "RAX")))⟩]
      | [next] => [goto (block.start * 100 + 90) next]
      | next :: other :: _ => [⟨block.start * 100 + 90, some (.var flag), .goto (.direct other)⟩, goto (block.start * 100 + 91) next]
    { tid := block.start, defs := defs, jmps := jmps }
  let entry : Blk := { tid := 7, jmps := blks.map fun blk => ⟨blk.tid * 100 + 99, some (.var flag), .goto (.direct blk.tid)⟩ }
  ⟨1, "real", [], entry :: blks⟩

/-- A dead chain over the blocks of a loop and a phi of each kind, for many passes that each remove little. -/
private def chainSub (length : Nat) : Sub :=
  let temp (i : Nat) : Var := reg s!"t{i}"
  ⟨1, "chain", [], (List.range length).map fun i =>
    let phi : List Phi := if i % 3 = 2 then [⟨i, temp (i + 1000), [(i, .var (temp i)), (i + 1, .var (temp (i + 1000 - 3)))]⟩] else []
    { tid := i + 1, phis := phi, defs := [defn (i * 10) (temp i) (if i = 0 then int 1 else .bin .add (.var (temp (i - 1))) (int 1))],
      jmps := if i + 1 = length then [⟨i * 10 + 1, none, .ret (.indirect (.var x))⟩]
        else if i % 5 = 4 then [⟨i * 10 + 1, some (.var y), .goto (.direct (i - 2))⟩, goto (i * 10 + 2) (i + 2)]
        else [goto (i * 10 + 1) (i + 2)] }⟩

/-- `x := x + 1` over a line of blocks: one assignment dies per pass, and all of them mention the one variable. -/
private def selfChain (length : Nat) : Sub :=
  ⟨1, "self-chain", [], (List.range length).map fun i =>
    { tid := i + 1, defs := [defn (i * 2 + 100) x (.bin .add (.var x) (int 1))],
      jmps := if i + 1 = length then [] else [goto (i * 2 + 101) (i + 2)] }⟩

/-- Each block reads the last one's variable and one that all of them read, assigned in the first block or nowhere. -/
private def hubChain (assignHub : Bool) (length : Nat) : Sub :=
  ⟨1, "hub-chain", [], (List.range length).map fun i =>
    let hub : List Def := if assignHub && i = 0 then [defn 99 z (.var y)] else []
    { tid := i + 1, defs := hub ++ [defn (i * 2 + 100) (reg s!"v{i}") (if i = 0 then .var z else .bin .add (.var (reg s!"v{i - 1}")) (.var z))],
      jmps := if i + 1 = length then [] else [goto (i * 2 + 101) (i + 2)] }⟩

/-- A small pseudorandom generator: a linear congruence. -/
private def nextRandom (seed : Nat) : Nat := (seed * 1103515245 + 12345) % 2147483648

/-- A pseudorandom CFG over a few variables, with loops, phis and memory, that has dead code of every kind: its
blocks reuse their variables, so that passes remove assignments of what other blocks read. -/
private def randomSub (seed : Nat) : Sub := Id.run do
  let mut seed := seed
  let mut blks : Array Blk := #[]
  let var (r : Nat) : Var := reg s!"r{r % 5}"
  let count := 3 + seed % 10
  for i in [0:count] do
    let mut phis : List Phi := []
    let mut defs : List Def := []
    seed := nextRandom seed
    if seed / 16 % 4 == 0 then
      seed := nextRandom seed
      phis := [⟨i * 100 + 90, var (seed / 16), [(1 + seed / 32 % count, .var (var (seed / 64))), (1 + seed / 128 % count, .var (var (seed / 512)))]⟩]
    seed := nextRandom seed
    for j in [0:seed / 16 % 4] do
      seed := nextRandom seed
      let rhs : Exp := match seed / 16 % 5 with
        | 0 => int (seed / 64 % 7)
        | 1 => .var (var (seed / 64))
        | 2 => .bin .add (.var (var (seed / 64))) (.var (var (seed / 512)))
        | 3 => .store (.var mem) (int 0) (.var (var (seed / 64))) .little 4
        | _ => .bin .add (.var (var (seed / 64))) (int 1)
      let target := if seed / 16 % 5 == 3 then mem else var (seed / 4096)
      defs := defs ++ [defn (i * 100 + j) target rhs]
    seed := nextRandom seed
    let next := 1 + seed / 16 % count
    let other := 1 + seed / 256 % count
    let jmps : List Jmp := match seed / 4096 % 4 with
      | 0 => [⟨i * 100 + 80, some (.var (var (seed / 65536))), .goto (.direct next)⟩, goto (i * 100 + 81) other]
      | 1 => [goto (i * 100 + 80) next]
      | 2 => [⟨i * 100 + 80, none, .ret (.indirect (.var (var (seed / 65536))))⟩]
      | _ => if i + 1 = count then [] else [goto (i * 100 + 80) (i + 2)]
    blks := blks.push { tid := i + 1, phis := phis, defs := defs, jmps := jmps }
  return ⟨1, s!"random", [], blks.toList⟩

private def deadCodeFastPath : IO Unit := do
  sameConstants "a sample" sample
  sameConstants "a loop" loop
  sameConstants "a chain" (chainSub 30)
  sameConstants "the SSA of a chain" (toSsa (chainSub 30))
  sameDeadCode "dead code: a line of one variable" (selfChain 40)
  sameDeadCode "dead code: a line of one variable, protected" (selfChain 40) [x]
  sameDeadCode "dead code: what all read, not assigned" (hubChain false 40)
  sameDeadCode "dead code: what all read, assigned" (hubChain true 40)
  sameDeadCode "dead code: what all read, protected" (hubChain true 40) [reg "v20"]
  let agrees (protectedVars : List Var) (sub : Sub) : Bool :=
    let cfg := Cfg.fromSub sub
    let count := cfg.blocks.foldl (fun count blk => count + blk.defs.length + blk.phis.length) 0
    toString (Wire.printSub ((deadCodeBySpec protectedVars cfg (count + 1)).intoSub sub)) ==
      toString (Wire.printSub ((eliminateDeadCode cfg protectedVars).intoSub sub))
  assertEqual "dead code: 1000 random CFGs" ([] : List Nat)
    ((List.range 1000).filter fun seed => !agrees [] (randomSub seed) || !agrees [reg "r1"] (randomSub seed) || !agrees [] (toSsa (randomSub seed)))
  -- a pass costs what it removes: these take a pass a block, and many blocks mention the one variable
  let started ← IO.monoMsNow
  for sub in [selfChain 7000, hubChain false 7000, hubChain true 7000] do
    assertEqual "a line of 7000 blocks dies" 0 ((optimize sub).blks.foldl (fun count blk => count + blk.defs.length) 0)
  let elapsed := (← IO.monoMsNow) - started
  assertTrue s!"a line of 7000 blocks takes a pass a block in under a second, not {elapsed} ms" (elapsed < 1000)
  sameDeadCode "dead code: a sample" sample
  sameDeadCode "dead code: a loop" loop
  sameDeadCode "dead code: an entry loop" entryLoop
  sameDeadCode "dead code: a stable loop" stableLoop
  sameDeadCode "dead code: protected variables" sample [x, reg "unused"]
  sameDeadCode "dead code: a chain" (chainSub 60)
  sameDeadCode "dead code: a protected chain" (chainSub 60) [reg "t20", reg "t1020"]
  sameDeadCode "dead code: the SSA of a chain" (toSsa (chainSub 60))
  sameDeadCode "dead code: the SSA of a chain, protected" (toSsa (chainSub 60)) [reg "t3.1"]
  -- a variable kept alive only by itself around a loop, and blocks of the same tid
  let selfLoop : Sub := ⟨1, "self", [], [
    ⟨1, [], [defn 1 x (.bin .add (.var x) (int 1)), defn 2 y (.var z)], [⟨3, some (.var y), .goto (.direct 1)⟩, goto 4 2]⟩,
    ⟨2, [], [defn 5 z (.var y)], []⟩]⟩
  sameDeadCode "dead code: a variable that only reads itself" selfLoop
  let sameTids : Sub := ⟨1, "same", [], [
    ⟨1, [], [defn 1 x (int 1), defn 2 y (.var x)], [goto 3 2]⟩,
    ⟨2, [], [defn 4 z (.var y)], [⟨5, none, .ret (.indirect (.var z))⟩]⟩,
    ⟨2, [], [defn 6 y (int 2), defn 7 x (.var y)], []⟩,
    ⟨99, [], [defn 8 z (int 3)], [goto 9 2]⟩]⟩
  sameDeadCode "dead code: blocks with the same tid, and one out of reach" sameTids
  sameDeadCode "dead code: blocks with the same tid, protected" sameTids [z]
  -- real code, if there is any to read
  let path := "/bin/ls"
  if ← System.FilePath.pathExists path then
    let image ← Image.load path
    match image.sections.find? (·.name == ".text") with
    | none => pure ()
    | some text =>
      let data := image.data.extract text.offset (text.offset + min text.size 6000)
      let disasm ← Disasm.Linear.sweep (← Target.X86.disassembler text.addr) data text.addr
      let sub := subOfDisasm disasm
      sameConstants "real code" sub
      sameDeadCode "dead code: real code" sub
      sameDeadCode "dead code: real code, protected" sub [reg "RAX"]
      sameDeadCode "dead code: real code in SSA" (toSsa sub)
      sameDeadCode "dead code: real code in SSA, protected" (toSsa sub) [reg "RAX"]
      sameDeadCode "dead code: real code, folded" (Cfg.intoSub (propagateConstants (Cfg.fromSub (toSsa sub))) sub)

def run : IO Unit := do
  deadCodeFastPath
  regressions
  -- a definition that would fail is gone from the output, which is why `optimize` only refines runs
  let failing : Sub := ⟨1, "failing", [], [⟨1, [], [defn 10 x (.var y)], []⟩]⟩
  match Bap.IR.optimize failing with
  | { blks := [block], .. } =>
    assertEqual "a dead definition that would fail is removed" 0 block.defs.length
    assertTrue "the definition does fail" (match Bil.evalExp [] (.var y) with | .error _ => true | .ok _ => false)
  | _ => throw <| IO.userError "missing optimized block"
  let cfg := Cfg.fromSub sample
  let (ins, outs) := cfg.liveness
  assertTrue "liveness propagates across blocks" ((Assoc.get 2 outs).getD [] |>.contains y)
  -- Block 3 writes `z` before its jump reads it, so the jump sees the block's own write.
  assertTrue "a jump read after a write in the block is not live in" (!((Assoc.get 3 ins).getD [] |>.contains z))
  assertTrue "what the block reads first is live in" ((Assoc.get 3 ins).getD [] |>.contains y)
  assertTrue "a jump read nothing in the block writes is live in" ((Assoc.get 2 ((Cfg.fromSub readOnJump).liveness.1)).getD [] |>.contains z)
  let propagated := propagateConstants cfg
  match propagated.block 2 with
  | some block =>
    match block.defs with
    | [defn] => assertEqual "cross-block constant propagation" (expString (int 42)) (expString defn.rhs)
    | _ => throw <| IO.userError "missing propagated definition"
  | none => throw <| IO.userError "missing propagated block"
  match propagated.block 3 with
  | some block =>
    match block.defs with
    | [result, _] => assertEqual "live result folded before DCE" (expString (int 42)) (expString result.rhs)
    | _ => throw <| IO.userError "missing propagated result"
  | none => throw <| IO.userError "missing propagated result block"
  let optimized := optimize sample
  assertEqual "optimization prunes unreachable blocks" [1, 2, 3] (optimized.blks.map Blk.tid)
  assertEqual "dead entry definition removed" 0 ((optimized.block 1).map (fun blk => blk.defs.length) |>.getD 999)
  assertEqual "dead intermediate definition removed" 0 ((optimized.block 2).map (fun blk => blk.defs.length) |>.getD 999)
  match optimized.block 3 with
  | none => throw <| IO.userError "missing optimized block"
  | some block =>
    assertEqual "only side-effecting store retained" 1 block.defs.length
    match block.defs with
    | [store] =>
      assertTrue "store remains side effecting" (match store.rhs with | .store _ _ _ _ _ => true | _ => false)
      match store.rhs with
      | .store _ _ value _ _ =>
        assertEqual "stored value folded" (expString (int 42)) (expString value)
      | _ => pure ()
    | _ => pure ()

end Bap.Tests.Optimize
