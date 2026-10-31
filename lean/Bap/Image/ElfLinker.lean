import Std.Data.HashMap
import Bap.Image.Basic

/-!
A static linker for relocatable ELF files, after upstream's `Bap_llvm_elf_linker`.

A relocatable file has no memory layout and its code and data are incomplete until the relocations are
applied. The linker assigns addresses to the allocatable sections, allocates the storage for the common and
external symbols and the global offset table, and applies the relocations to a copy of the input.
-/

namespace Bap.Image.ElfLinker

structure Section where
  name : String
  typ : Nat
  flags : Nat
  off : Nat
  size : Nat
  align : Nat
  deriving Inhabited

structure Sym where
  name : String
  shndx : Nat
  /-- `shndx` is an extended section index, which is never one of the special ones. -/
  extended : Bool
  value : Nat
  size : Nat
  typ : Nat
  bind : Nat
  deriving Inhabited

structure Rel where
  target : Nat
  offset : Nat
  typ : Nat
  symbol : Nat
  addend : Int
  isExplicit : Bool

structure Input where
  machine : Nat
  width : Nat
  little : Bool
  base : Nat
  data : ByteArray
  /-- By section index. -/
  sections : Array Section
  /-- By symbol index. -/
  symbols : Array Sym
  relocations : List Rel

structure Region where
  name : String
  addr : Nat
  size : Nat
  /-- The file offset of the contents, and of the GOT's past the end of the file; `none` reads as zero. -/
  off : Option Nat
  r : Bool
  w : Bool
  x : Bool
  isSection : Bool

structure Output where
  regions : List Region
  symbols : List Symbol
  references : List (Nat × String)
  /-- The addresses of the sections, by section index. -/
  sectionAddrs : Array (Option Nat)
  /-- The input with the relocations applied, followed by the GOT. -/
  memory : ByteArray
  warnings : List String

/-! ### Constants of the ELF gABI -/

def shfWrite : Nat := 1
def shfAlloc : Nat := 2
def shfExecinstr : Nat := 4
def shtNobits : Nat := 8
def shnUndef : Nat := 0
def shnLoreserve : Nat := 0xff00
def shnAbs : Nat := 0xfff1
def shnCommon : Nat := 0xfff2
def sttFunc : Nat := 2
def sttGnuIfunc : Nat := 10
def stbLocal : Nat := 0
def emMips : Nat := 8
def emArm : Nat := 40
def emPpc64 : Nat := 21

def hasFlag (flags flag : Nat) : Bool := flags &&& flag != 0

/-! ### Bit fields -/

/-- The `n` bits of `value` from bit `lo`. Values are unbounded, so nothing wraps before it is cut to a field. -/
def field (value : Int) (lo n : Nat) : Nat :=
  ((value >>> lo) % ((2 ^ n : Nat) : Int)).toNat

/-- `value`, as an `n`-bit two's complement number. -/
def sext (value : Int) (n : Nat) : Int :=
  let low := field value 0 n
  if 2 * low ≥ 2 ^ n then (low : Int) - ((2 ^ n : Nat) : Int) else low

/-- Replaces the `n` bits of `word` at `lo` with the low bits of `value`. -/
def setBits (word lo n : Nat) (value : Int) : Nat :=
  word - field word lo n * 2 ^ lo + field value 0 n * 2 ^ lo

def readNat (memory : ByteArray) (little : Bool) (off n : Nat) : Nat :=
  (List.range n).foldl (init := 0) fun value index =>
    value + (memory.get! (off + index)).toNat * 256 ^ (if little then index else n - index - 1)

def writeNat (memory : ByteArray) (little : Bool) (off n : Nat) (value : Int) : ByteArray :=
  (List.range n).foldl (init := memory) fun result index =>
    result.set! (off + index) (UInt8.ofNat (field value (8 * if little then index else n - index - 1) 8))

/-! ### Layout -/

/-- Where the allocatable sections go: `addrs` by section index, `regions` in reverse. -/
structure Layout where
  cursor : Nat
  addrs : Array (Option Nat) := #[]
  regions : List Region := []

def placeSection (layout : Layout) (sec : Section) : Layout :=
  if hasFlag sec.flags shfAlloc then
    let addr := alignUp layout.cursor sec.align
    let region : Region :=
      ⟨sec.name, addr, sec.size, if sec.typ != shtNobits then some sec.off else none, true,
        hasFlag sec.flags shfWrite, hasFlag sec.flags shfExecinstr, true⟩
    { cursor := addr + sec.size
      addrs := layout.addrs.push (some addr)
      regions := if sec.size > 0 then region :: layout.regions else layout.regions }
  else
    { layout with addrs := layout.addrs.push none }

def layoutSections (sections : List Section) (base : Nat) : Layout :=
  sections.foldl placeSection { cursor := base }

/-- A synthetic region for what was placed since `start`, if anything. -/
def synthetic (name : String) (start cursor : Nat) (off : Option Nat) (w : Bool) : List Region :=
  if cursor > start then [⟨name, start, cursor - start, off, true, w, false, false⟩] else []

def special (sym : Sym) (shn : Nat) : Bool := !sym.extended && sym.shndx == shn

/-- The offset from the GOT of a symbol defined by the linker. -/
def linkerSymbol (machine : Nat) (sym : Sym) : Option Nat :=
  if sym.name == "_GLOBAL_OFFSET_TABLE_" then some 0
  else if machine == emMips && (sym.name == "_gp" || sym.name == "_gp_disp" || sym.name == "__gnu_local_gp") then
    some 0x7ff0
  else none

def isExternal (machine : Nat) (sym : Sym) : Bool :=
  special sym shnUndef && !sym.name.isEmpty && (linkerSymbol machine sym).isNone

def isFunctionSym (sym : Sym) : Bool := sym.typ == sttFunc || sym.typ == sttGnuIfunc

/-! ### Relocation sites -/

/-- A relocated place: `off` is its file offset, in a section whose bytes in the file end at `limit`. -/
structure Site where
  rel : Rel
  sym : Sym
  sectionName : String
  /-- The address of the place. -/
  p : Int
  /-- The address of the symbol. -/
  s : Int
  /-- The explicit addend or zero. -/
  a : Int
  off : Nat
  limit : Nat

/-- A store of `n` bytes at file offset `off`. -/
structure Write where
  off : Nat
  n : Nat
  value : Int
  little : Bool

structure Env where
  machine : Nat
  width : Nat
  little : Bool
  /-- AArch64 instructions are little-endian whatever the data is. -/
  codeLittle : Bool
  gotBase : Nat
  gotOff : Nat

structure LinkState where
  memory : ByteArray
  /-- The address of the GOT entry of a value. -/
  got : Std.HashMap Nat Nat := {}
  gotCount : Nat := 0
  /-- The HI16 and local GOT16 sites awaiting their LO16, the latest first, with their stored halves. -/
  mipsPending : List (Site × Nat) := []
  /-- The pc-relative values of the AUIPC instructions, by their addresses. -/
  riscvHi : Std.HashMap Int Int := {}
  references : List (Nat × String) := []
  warnings : List String := []

abbrev LinkM := EStateM String LinkState

def inSection (site : Site) (at' n : Nat) (memorySize : Nat) : Bool :=
  site.off + at' + n ≤ site.limit && site.off + at' + n ≤ memorySize

def outside (site : Site) : String :=
  s!"relocation at {site.p} accesses data outside of the section {site.sectionName}"

/-- Loads `n` bytes at `at'` past the place, which must be inside of its section. -/
def load (site : Site) (at' n : Nat) (little : Bool) : LinkM Nat := do
  let state ← get
  if inSection site at' n state.memory.size then
    pure (readNat state.memory little (site.off + at') n)
  else
    throw (outside site)

/-- Performs the stores of a site, all of them or none. -/
def commit (site : Site) (writes : List Write) : LinkM Unit := do
  let state ← get
  if writes.all fun write => site.off ≤ write.off && write.off + write.n ≤ site.limit &&
      write.off + write.n ≤ state.memory.size then
    let memory := writes.foldl (init := state.memory) fun memory write =>
      writeNat memory write.little write.off write.n write.value
    set { state with memory }
  else
    throw (outside site)

/-- The address of the GOT entry that holds `value`. -/
def gotEntry (env : Env) (value : Int) : LinkM Int := do
  let key := field value 0 64
  let state ← get
  match state.got[key]? with
  | some slot => pure slot
  | none =>
    let word := env.width / 8
    let slot := env.gotBase + state.gotCount * word
    let off := env.gotOff + state.gotCount * word
    let padded := (List.range (off + word - state.memory.size)).foldl (init := state.memory)
      fun memory _ => memory.push 0
    set { state with
      memory := writeNat padded env.little off word value
      got := state.got.insert key slot
      gotCount := state.gotCount + 1 }
    pure slot

/-! ### Relocation handlers

The relocation types are the numbers of the `R_<ARCH>_*` constants of each psABI; S is the symbol's address,
A the addend, P the place's address and GOT the GOT's. There are no PLT entries, so PLT relocations go directly
to the symbol. A handler returns the stores of a relocation, or `none` when the type is not supported. -/

abbrev Outcome := LinkM (Option (List Write))

def stAt (env : Env) (site : Site) (at' n : Nat) (value : Int) : Write := ⟨site.off + at', n, value, env.little⟩
def stiAt (env : Env) (site : Site) (at' n : Nat) (value : Int) : Write := ⟨site.off + at', n, value, env.codeLittle⟩
def done (writes : List Write) : Outcome := pure (some writes)
def ld (env : Env) (site : Site) (at' n : Nat) : LinkM Nat := load site at' n env.little
def ldInt (env : Env) (site : Site) (at' n : Nat) : LinkM Int := do
  pure ((← ld env site at' n : Nat) : Int)
def ldi (env : Env) (site : Site) (at' : Nat) (n : Nat := 4) : LinkM Nat := load site at' n env.codeLittle

def x86_64 (env : Env) (site : Site) : Outcome := do
  let s := site.s
  let a := site.a
  let p := site.p
  let got : Int := env.gotBase
  let store n value := done [stAt env site 0 n value]
  match site.rel.typ with
  | 0 => done []
  | 1 => store 8 (s + a)
  | 2 | 4 => store 4 (s + a - p)
  | 3 => store 4 ((← gotEntry env s) - got + a)
  | 9 | 41 | 42 | 43 => store 4 ((← gotEntry env s) + a - p)
  | 10 | 11 => store 4 (s + a)
  | 12 => store 2 (s + a)
  | 13 => store 2 (s + a - p)
  | 14 => store 1 (s + a)
  | 15 => store 1 (s + a - p)
  | 24 => store 8 (s + a - p)
  | 25 => store 8 (s + a - got)
  | 26 => store 4 (got + a - p)
  | 27 => store 8 ((← gotEntry env s) - got + a)
  | 28 => store 8 ((← gotEntry env s) + a - p)
  | 29 => store 8 (got + a - p)
  | 32 => store 4 (site.sym.size + a)
  | 33 => store 8 (site.sym.size + a)
  | _ => pure none

def i386 (env : Env) (site : Site) : Outcome := do
  let s := site.s
  let p := site.p
  let got : Int := env.gotBase
  let store n value := done [stAt env site 0 n value]
  let addend (n : Nat) : LinkM Int := do
    if site.rel.isExplicit then pure site.a else pure (sext (← ld env site 0 n) (8 * n))
  match site.rel.typ with
  | 0 => done []
  | 1 => store 4 (s + (← addend 4))
  | 2 | 4 => store 4 (s + (← addend 4) - p)
  | 3 | 43 => store 4 ((← gotEntry env s) + (← addend 4) - got)
  | 9 => store 4 (s + (← addend 4) - got)
  | 10 => store 4 (got + (← addend 4) - p)
  | 20 => store 2 (s + (← addend 2))
  | 21 => store 2 (s + (← addend 2) - p)
  | 22 => store 1 (s + (← addend 1))
  | 23 => store 1 (s + (← addend 1) - p)
  | _ => pure none

def aarch64 (env : Env) (site : Site) : Outcome := do
  let s := site.s
  let a := site.a
  let p := site.p
  let x := s + a
  let store n value := done [stAt env site 0 n value]
  let update (f : Nat → Nat) : Outcome := do
    done [stiAt env site 0 4 (f (← ldi env site 0))]
  let page (value : Int) : Int := value - value % 4096
  let adr (value : Int) (insn : Nat) : Nat := setBits (setBits insn 29 2 value) 5 19 (value >>> 2)
  let lo12 (shift : Nat) (value : Int) : Outcome :=
    update fun insn => setBits insn 10 12 (field value 0 12 >>> shift : Nat)
  match site.rel.typ with
  | 0 => done []
  | 0x101 => store 8 x
  | 0x102 => store 4 x
  | 0x103 => store 2 x
  | 0x104 => store 8 (x - p)
  | 0x105 | 0x13a => store 4 (x - p)
  | 0x106 => store 2 (x - p)
  | 0x107 | 0x108 | 0x109 | 0x10a | 0x10b | 0x10c | 0x10d =>
    let shift := (site.rel.typ - 0x107) / 2 * 16
    update fun insn => setBits insn 5 16 (x >>> shift)
  | 0x111 | 0x118 => update fun insn => setBits insn 5 19 ((x - p) >>> 2)
  | 0x112 => update (adr (x - p))
  | 0x113 | 0x114 => update (adr ((page x - page p) >>> 12))
  | 0x115 | 0x116 => lo12 0 x
  | 0x117 => update fun insn => setBits insn 5 14 ((x - p) >>> 2)
  | 0x11a | 0x11b => update fun insn => setBits insn 0 26 ((x - p) >>> 2)
  | 0x11c => lo12 1 x
  | 0x11d => lo12 2 x
  | 0x11e => lo12 3 x
  | 0x12b => lo12 4 x
  | 0x135 =>
    let entry ← gotEntry env x
    update fun insn => setBits insn 5 19 ((entry - p) >>> 2)
  | 0x137 =>
    let entry ← gotEntry env x
    update (adr ((page entry - page p) >>> 12))
  | 0x138 =>
    let entry ← gotEntry env x
    lo12 3 entry
  | 0x13b => store 4 ((← gotEntry env s) + a - p)
  | _ => pure none

def isThumb (sym : Sym) : Bool := isFunctionSym sym && sym.value % 2 == 1

def arm (env : Env) (site : Site) : Outcome := do
  let sym := site.sym
  let typ := site.rel.typ
  let p := site.p
  let got : Int := env.gotBase
  let thumb := isThumb sym
  let s : Int := if thumb then site.s - site.s % 2 else site.s
  let withT (value : Int) : Int := if thumb && value % 2 == 0 then value + 1 else value
  let addend (decoded : Int) : Int := if site.rel.isExplicit then site.a else decoded
  let a32 : LinkM Int := do pure (addend (sext (← ld env site 0 4) 32))
  let store n value := done [stAt env site 0 n value]
  let movw (kind : Nat) (imm : Nat) : Nat :=
    let a := addend (sext imm 16)
    match kind with
    | 0 => field (withT (s + a)) 0 16
    | 1 => field (s + a) 16 16
    | 2 => field (withT (s + a) - p) 0 16
    | _ => field (s + a - p) 16 16
  let armMovw (kind : Nat) : Outcome := do
    let insn ← ld env site 0 4
    let imm := ((insn >>> 4) &&& 0xf000) ||| (insn &&& 0xfff)
    let v := movw kind imm
    store 4 (((insn &&& 0xfff0f000) ||| ((v &&& 0xf000) <<< 4) ||| (v &&& 0xfff) : Nat) : Int)
  let thumbMovw (kind : Nat) : Outcome := do
    let hw1 ← ld env site 0 2
    let hw2 ← ld env site 2 2
    let imm := (field hw1 0 4 <<< 12) ||| (field hw1 10 1 <<< 11) ||| (field hw2 12 3 <<< 8) ||| field hw2 0 8
    let v := movw kind imm
    done [stAt env site 0 2 (((hw1 &&& 0xfbf0) ||| field v 12 4 ||| (field v 11 1 <<< 10) : Nat) : Int),
      stAt env site 2 2 (((hw2 &&& 0x8f00) ||| (field v 8 3 <<< 12) ||| field v 0 8 : Nat) : Int)]
  let armBranch : Outcome := do
    let insn ← ld env site 0 4
    let a := addend (sext ((insn &&& 0xffffff) <<< 2 : Nat) 26)
    let v := s + a - p
    let imm24 := field v 2 24
    if typ == 0x1c && thumb then
      store 4 ((0xfa000000 ||| (field v 1 1 <<< 24) ||| imm24 : Nat) : Int)
    else if typ == 0x1c && isFunctionSym sym && field insn 28 4 == 0xf then
      store 4 ((0xeb000000 ||| imm24 : Nat) : Int)
    else
      store 4 (((insn &&& 0xff000000) ||| imm24 : Nat) : Int)
  let thumbBranch : Outcome := do
    let hw1 ← ld env site 0 2
    let hw2 ← ld env site 2 2
    let sign := field hw1 10 1
    let i1 := 1 - (field hw2 13 1 ^^^ sign)
    let i2 := 1 - (field hw2 11 1 ^^^ sign)
    let a := addend (sext ((sign <<< 24) ||| (i1 <<< 23) ||| (i2 <<< 22) ||| (field hw1 0 10 <<< 12) |||
      (field hw2 0 11 <<< 1) : Nat) 25)
    let call := typ == 0xa
    let blx := call && (if isFunctionSym sym then !thumb else field hw2 12 1 == 0)
    let v := if blx then s + a - (p - p % 4) else s + a - p
    let sign := field v 24 1
    let j1 := 1 - (field v 23 1 ^^^ sign)
    let j2 := 1 - (field v 22 1 ^^^ sign)
    let hw2 := if !call then hw2 else if blx then hw2 &&& 0xefff else hw2 ||| 0x1000
    done [stAt env site 0 2 (((hw1 &&& 0xf800) ||| (sign <<< 10) ||| field v 12 10 : Nat) : Int),
      stAt env site 2 2 (((hw2 &&& 0xd000) ||| (j1 <<< 13) ||| (j2 <<< 11) ||| field v 1 11 : Nat) : Int)]
  let thumbJump19 : Outcome := do
    let hw1 ← ld env site 0 2
    let hw2 ← ld env site 2 2
    let a := addend (sext ((field hw1 10 1 <<< 20) ||| (field hw2 11 1 <<< 19) ||| (field hw2 13 1 <<< 18) |||
      (field hw1 0 6 <<< 12) ||| (field hw2 0 11 <<< 1) : Nat) 21)
    let v := s + a - p
    done [stAt env site 0 2 (((hw1 &&& 0xfbc0) ||| (field v 20 1 <<< 10) ||| field v 12 6 : Nat) : Int),
      stAt env site 2 2 (((hw2 &&& 0xd000) ||| (field v 18 1 <<< 13) ||| (field v 19 1 <<< 11) ||| field v 1 11 : Nat) : Int)]
  let thumbShortBranch (n : Nat) : Outcome := do
    let hw ← ld env site 0 2
    let a := addend (sext (field hw 0 n <<< 1 : Nat) (n + 1))
    store 2 ((hw - field hw 0 n + field (s + a - p) 1 n : Nat) : Int)
  match typ with
  | 0 | 0x28 => done []
  | 1 | 0x1c | 0x1d => armBranch
  | 2 | 0x26 => store 4 (withT (s + (← a32)))
  | 3 | 0x29 => store 4 (withT (s + (← a32)) - p)
  | 5 => store 2 (s + addend (sext (← ld env site 0 2) 16))
  | 8 => store 1 (s + addend (sext (← ld env site 0 1) 8))
  | 0xa | 0x1e => thumbBranch
  | 0x18 => store 4 (s + (← a32) - got)
  | 0x19 => store 4 (got + (← a32) - p)
  | 0x1a => store 4 ((← gotEntry env (withT s)) + (← a32) - got)
  | 0x2a =>
    let old ← ld env site 0 4
    let a := addend (sext (old &&& 0x7fffffff : Nat) 31)
    store 4 (((old &&& 0x80000000) ||| field (withT (s + a) - p) 0 31 : Nat) : Int)
  | 0x2b => armMovw 0
  | 0x2c => armMovw 1
  | 0x2d => armMovw 2
  | 0x2e => armMovw 3
  | 0x2f => thumbMovw 0
  | 0x30 => thumbMovw 1
  | 0x31 => thumbMovw 2
  | 0x32 => thumbMovw 3
  | 0x33 => thumbJump19
  | 0x60 => store 4 ((← gotEntry env (withT s)) + (← a32) - p)
  | 0x66 => thumbShortBranch 11
  | 0x67 => thumbShortBranch 8
  | _ => pure none

def mipsGp (env : Env) : Int := env.gotBase + 0x7ff0

def setLo16 (insn : Nat) (value : Int) : Int := setBits insn 0 16 value

/-- Resolves a deferred HI16 or local GOT16 now that its addend `AHL = (AHI << 16) + ALO` is known. -/
def mipsApplyHi (env : Env) (site : Site) (ahl : Int) : LinkM Unit := do
  let insn ← ld env site 0 4
  let gp := mipsGp env
  if site.rel.typ == 5 then
    let s := if site.sym.name == "_gp_disp" then gp - site.p else site.s
    commit site [stAt env site 0 4 (setLo16 insn ((ahl + s + 0x8000) >>> 16))]
  else
    let page := site.s + ahl + 0x8000
    let entry ← gotEntry env (page - page % 65536)
    commit site [stAt env site 0 4 (setLo16 insn (entry - gp))]

def mipsFlush (env : Env) (lo : Int) (symbol : Nat) : LinkM Unit := do
  let state ← get
  let (matched, rest) := state.mipsPending.partition fun entry => entry.1.rel.symbol == symbol
  set { state with mipsPending := rest }
  for entry in matched.reverse do
    mipsApplyHi env entry.1 (((entry.2 : Int) * 65536) + lo)

def mips (env : Env) (site : Site) : Outcome := do
  let rel := site.rel
  let sym := site.sym
  let p := site.p
  let s := site.s
  let gp := mipsGp env
  let isLocal := sym.bind == stbLocal
  let store n value := done [stAt env site 0 n value]
  let a16 : LinkM Int := do
    if rel.isExplicit then pure site.a else pure (sext ((← ld env site 0 4) &&& 0xffff : Nat) 16)
  let a32 : LinkM Int := do
    if rel.isExplicit then pure site.a else pure (← ldInt env site 0 4)
  let defer : Outcome := do
    if rel.isExplicit then
      mipsApplyHi env site site.a
    else
      let stored := (← ld env site 0 4) &&& 0xffff
      modify fun state => { state with mipsPending := (site, stored) :: state.mipsPending }
    done []
  match rel.typ with
  | 0 | 37 => done []
  | 2 => store 4 (s + (← a32))
  | 4 =>
    let insn ← ld env site 0 4
    let a : Int := if rel.isExplicit then site.a else ((insn &&& 0x3ffffff) <<< 2 : Nat)
    let target := if isLocal then
        (field a 0 28 + (field (p + 4) 28 36) * 2 ^ 28 : Nat) + s
      else sext a 28 + s
    store 4 (setBits insn 0 26 (target >>> 2) : Nat)
  | 5 => defer
  | 9 =>
    if isLocal then defer
    else store 4 (setLo16 (← ld env site 0 4) ((← gotEntry env s) - gp))
  | 11 => store 4 (setLo16 (← ld env site 0 4) ((← gotEntry env s) - gp))
  | 6 =>
    let lo ← a16
    mipsFlush env lo rel.symbol
    let s := if sym.name == "_gp_disp" then gp - p + 4 else s
    store 4 (setLo16 (← ld env site 0 4) (s + lo))
  | 7 => store 4 (setLo16 (← ld env site 0 4) (s + (← a16) - gp))
  | 10 =>
    let insn ← ld env site 0 4
    let a := sext ((insn &&& 0xffff) <<< 2 : Nat) 18
    store 4 (setLo16 insn ((s + a - p) >>> 2))
  | 12 => store 4 (s + (← a32) - gp)
  | 18 => if env.width == 64 then store 8 (s + (← a32)) else pure none
  | 20 =>
    if env.width == 64 then
      let x := s + (← a16)
      let insn ← ld env site 0 4
      if isLocal && sext x 32 == x then
        let rt := field insn 16 5
        store 4 ((0x3c000000 ||| (rt <<< 16) ||| field (x + 0x8000) 16 16 : Nat) : Int)
      else
        let page := x + 0x8000
        store 4 (setLo16 insn ((← gotEntry env (page - page % 65536)) - gp))
    else pure none
  | 21 =>
    if env.width == 64 then
      let x := s + (← a16)
      let page := (x + 0x8000) - (x + 0x8000) % 65536
      store 4 (setLo16 (← ld env site 0 4) (if isLocal && sext x 32 == x then x else x - page))
    else pure none
  | 248 => store 4 (s + (← a32) - p)
  | _ => pure none

def mipsFinish (env : Env) : LinkM Unit := do
  let symbols := (← get).mipsPending.map (·.1.rel.symbol)
  let unique := symbols.foldl (init := []) fun result symbol =>
    if result.contains symbol then result else symbol :: result
  for symbol in unique.mergeSort do
    mipsFlush env 0 symbol

def bit (value : Int) (n : Nat) : Nat := field value n 1

def riscvU (value : Int) (insn : Nat) : Int := setBits insn 12 20 ((value + 0x800) >>> 12)
def riscvI (value : Int) (insn : Nat) : Int := setBits insn 20 12 value
def riscvS (value : Int) (insn : Nat) : Int := setBits (setBits insn 25 7 (value >>> 5)) 7 5 value
def riscvB (value : Int) (insn : Nat) : Int :=
  ((insn &&& 0x1fff07f) ||| (bit value 12 <<< 31) ||| (field value 5 6 <<< 25) ||| (field value 1 4 <<< 8) |||
    (bit value 11 <<< 7) : Nat)
def riscvJ (value : Int) (insn : Nat) : Int :=
  ((insn &&& 0xfff) ||| (bit value 20 <<< 31) ||| (field value 1 10 <<< 21) ||| (bit value 11 <<< 20) |||
    (field value 12 8 <<< 12) : Nat)
def riscvCB (value : Int) (insn : Nat) : Int :=
  ((insn &&& 0xe383) ||| (bit value 8 <<< 12) ||| (field value 3 2 <<< 10) ||| (field value 6 2 <<< 5) |||
    (field value 1 2 <<< 3) ||| (bit value 5 <<< 2) : Nat)
def riscvCJ (value : Int) (insn : Nat) : Int :=
  ((insn &&& 0xe003) ||| (bit value 11 <<< 12) ||| (bit value 4 <<< 11) ||| (field value 8 2 <<< 9) |||
    (bit value 10 <<< 8) ||| (bit value 6 <<< 7) ||| (bit value 7 <<< 6) ||| (field value 1 3 <<< 3) |||
    (bit value 5 <<< 2) : Nat)

/-- The pc-relative values of the AUIPC instructions, collected before the relocations are applied, because
a `PCREL_LO12` relocation refers to the label of its AUIPC rather than to the target. -/
def riscvPrescan (env : Env) (site : Site) : LinkM Unit := do
  match site.rel.typ with
  | 20 =>
    let entry ← gotEntry env site.s
    modify fun state => { state with riscvHi := state.riscvHi.insert site.p (entry + site.a - site.p) }
  | 23 =>
    modify fun state => { state with riscvHi := state.riscvHi.insert site.p (site.s + site.a - site.p) }
  | _ => pure ()

/-- The length of the ULEB128 number at the place, in at most 10 bytes. -/
def ulebLength (env : Env) (site : Site) : Nat → Nat → LinkM Nat
  | 0, n => pure (n + 1)
  | fuel + 1, n => do
    if (← ld env site n 1) &&& 0x80 == 0 then pure (n + 1) else ulebLength env site fuel (n + 1)

/-- Rewrites the ULEB128 number at the place in its existing length. -/
def rewriteUleb (env : Env) (site : Site) (f : Nat → Int) : Outcome := do
  let n ← ulebLength env site 9 0
  let mut old := 0
  for i in List.range n do
    old := old + ((← ld env site i 1) &&& 0x7f) * 2 ^ (7 * i)
  let value := f old
  done ((List.range n).map fun i =>
    stAt env site i 1 ((field value (7 * i) 7 + (if i + 1 < n then 0x80 else 0) : Nat) : Int))

def riscv (env : Env) (site : Site) : Outcome := do
  let p := site.p
  let s := site.s
  let a := site.a
  let x := s + a
  let store n value := done [stAt env site 0 n value]
  let update (f : Nat → Int) : Outcome := do done [stiAt env site 0 4 (f (← ldi env site 0))]
  let update16 (f : Nat → Int) : Outcome := do done [stiAt env site 0 2 (f (← ldi env site 0 2))]
  let pcrelLo (f : Int → Nat → Int) : Outcome := do
    match (← get).riscvHi[s]? with
    | some value => update (f value)
    | none => pure none
  match site.rel.typ with
  | 0 | 43 | 51 => done []
  | 1 => store 4 x
  | 2 => store 8 x
  | 16 => update (riscvB (x - p))
  | 17 => update (riscvJ (x - p))
  | 18 | 19 =>
    let v := x - p
    let first ← ldi env site 0
    let second ← ldi env site 4
    done [stiAt env site 0 4 (riscvU v first), stiAt env site 4 4 (riscvI v second)]
  | 20 | 23 =>
    match (← get).riscvHi[p]? with
    | some value => update (riscvU value)
    | none => pure none
  | 24 => pcrelLo riscvI
  | 25 => pcrelLo riscvS
  | 26 => update (riscvU x)
  | 27 => update (riscvI x)
  | 28 => update (riscvS x)
  | 33 => store 1 ((← ldInt env site 0 1) + x)
  | 34 => store 2 ((← ldInt env site 0 2) + x)
  | 35 => store 4 ((← ldInt env site 0 4) + x)
  | 36 => store 8 ((← ldInt env site 0 8) + x)
  | 37 => store 1 ((← ldInt env site 0 1) - x)
  | 38 => store 2 ((← ldInt env site 0 2) - x)
  | 39 => store 4 ((← ldInt env site 0 4) - x)
  | 40 => store 8 ((← ldInt env site 0 8) - x)
  | 41 => store 4 ((← gotEntry env s) + a - p)
  | 44 => update16 (riscvCB (x - p))
  | 45 => update16 (riscvCJ (x - p))
  | 52 =>
    let old ← ld env site 0 1
    store 1 (setBits old 0 6 ((old : Int) - x) : Nat)
  | 53 =>
    let old ← ld env site 0 1
    store 1 (setBits old 0 6 x : Nat)
  | 54 => store 1 x
  | 55 => store 2 x
  | 56 => store 4 x
  | 57 | 59 => store 4 (x - p)
  | 60 => rewriteUleb env site fun _ => x
  | 61 => rewriteUleb env site fun old => (old : Int) - x
  | _ => pure none

def powerpc (env : Env) (site : Site) : Outcome := do
  let p := site.p
  let x := site.s + site.a
  let store n value := done [stAt env site 0 n value]
  let update (f : Nat → Nat) : Outcome := do done [stiAt env site 0 4 (f (← ldi env site 0))]
  match site.rel.typ with
  | 0 => done []
  | 1 => store 4 x
  | 2 => update fun i => (i &&& 0xfc000003) ||| (field x 0 26 &&& 0x3fffffc)
  | 3 | 4 => store 2 (field x 0 16 : Nat)
  | 5 => store 2 (field x 16 16 : Nat)
  | 6 => store 2 (field (x + 0x8000) 16 16 : Nat)
  | 7 => update fun i => (i &&& 0xffff0003) ||| (field x 0 16 &&& 0xfffc)
  | 10 | 18 => update fun i => (i &&& 0xfc000003) ||| (field (x - p) 0 26 &&& 0x3fffffc)
  | 11 => update fun i => (i &&& 0xffff0003) ||| (field (x - p) 0 16 &&& 0xfffc)
  | 26 => store 4 (x - p)
  | 38 => store 8 x
  | 44 => store 8 (x - p)
  | _ => pure none

def systemz (env : Env) (site : Site) : Outcome := do
  match site.rel.typ with
  | 0 => done []
  | 20 => done [stiAt env site 0 4 ((site.s + site.a - site.p) >>> 1)]
  | _ => pure none

/-- The handler of a machine, if the machine has one. -/
def handler (env : Env) : Option (Site → Outcome) :=
  match env.machine with
  | 62 => some (x86_64 env)
  | 3 => some (i386 env)
  | 183 => some (aarch64 env)
  | 40 => some (arm env)
  | 8 => some (mips env)
  | 243 => some (riscv env)
  | 20 | 21 => some (powerpc env)
  | 22 => some (systemz env)
  | _ => none

/-! ### The linker -/

/-- The tables that are fixed once the layout is done. -/
structure Tables where
  input : Input
  env : Env
  addrs : Array (Option Nat)
  commons : Array (Option Nat)
  externals : Std.HashMap String Nat

def nullSym : Sym := ⟨"", shnUndef, false, 0, 0, 0, 0⟩

/-- The address of a symbol, if it has one. -/
def resolve (tables : Tables) (index : Nat) (sym : Sym) : Option Nat :=
  if special sym shnUndef then
    if sym.name.isEmpty then some 0
    else match linkerSymbol tables.input.machine sym with
      | some off => some (tables.env.gotBase + off)
      | none => tables.externals[sym.name]?
  else if special sym shnAbs then some sym.value
  else if special sym shnCommon then (tables.commons[index]?).join
  else if !sym.extended && sym.shndx ≥ shnLoreserve then none
  else ((tables.addrs[sym.shndx]?).join).map (· + sym.value)

/-- The section of a symbol or relocation, if it is allocated and has contents. -/
def relocatedSection (tables : Tables) (index : Nat) : Option (Section × Nat) := do
  let sec ← tables.input.sections[index]?
  let addr ← (tables.addrs[index]?).join
  if sec.typ != shtNobits then some (sec, addr) else none

/-- The symbol of a PowerPC64 branch through a function descriptor in `.opd` is the code it points to. -/
def resolveBranchTarget (tables : Tables) (rel : Rel) (sym : Sym) : Option Nat :=
  let plain := resolve tables rel.symbol sym
  if tables.input.machine == emPpc64 && (rel.typ == 10 || rel.typ == 18) then
    let descriptor := match relocatedSection tables sym.shndx with
      | some (sec, _) =>
        if sec.name == ".opd" then
          tables.input.relocations.findSome? fun entry =>
            if entry.target == sym.shndx && entry.typ == 38 &&
                (entry.offset : Int) == (sym.value : Int) + rel.addend then
              (resolve tables entry.symbol ((tables.input.symbols[entry.symbol]?).getD nullSym)).map
                fun code => field ((code : Int) + entry.addend - rel.addend) 0 64
            else none
        else none
      | none => none
    match descriptor with
    | some code => some code
    | none => plain
  else plain

def warn (message : String) : LinkM Unit :=
  modify fun state => { state with warnings := message :: state.warnings }

/-- The site of a relocation that is applied; the first pass, `report`, tells about the ones that are not. -/
def siteOf (tables : Tables) (report : Bool) (rel : Rel) : LinkM (Option Site) := do
  match relocatedSection tables rel.target with
  | none => pure none
  | some (sec, base) =>
    let sym := (tables.input.symbols[rel.symbol]?).getD nullSym
    let p := base + rel.offset
    if rel.offset ≥ sec.size then
      if report then warn s!"relocation at {p} is outside of the section {sec.name}"
      pure none
    else
      match resolveBranchTarget tables rel sym with
      | none =>
        if report then warn s!"unable to resolve the symbol {sym.name} referenced at {p}"
        pure none
      | some s =>
        if report && isExternal tables.input.machine sym then
          modify fun state => { state with references := (p, sym.name) :: state.references }
        pure (some ⟨rel, sym, sec.name, p, s, if rel.isExplicit then rel.addend else 0,
          sec.off + rel.offset, min (sec.off + sec.size) tables.env.gotOff⟩)

/-- Runs a pass, a failed relocation becoming a warning. -/
def guard (action : LinkM Unit) : LinkM Unit :=
  EStateM.tryCatch action warn

def applySite (env : Env) (apply : Site → Outcome) (site : Site) : LinkM Unit := do
  match ← apply site with
  | some writes => commit site writes
  | none => warn s!"relocation of type {site.rel.typ} (machine {env.machine}) at {site.p} was not applied"

def relocate (tables : Tables) : LinkM Unit := do
  let env := tables.env
  match handler env with
  | none =>
    let mut relocated := false
    for rel in tables.input.relocations do
      if (← siteOf tables true rel).isSome then relocated := true
    if relocated then
      warn s!"relocations of the machine {env.machine} are not supported, the code is left unrelocated"
  | some apply =>
    for rel in tables.input.relocations do
      guard do
        if let some site ← siteOf tables true rel then
          if env.machine == 243 then riscvPrescan env site
    for rel in tables.input.relocations do
      guard do
        if let some site ← siteOf tables false rel then
          applySite env apply site
    if env.machine == emMips then guard (mipsFinish env)

/-- The commons and externals, placed after the sections, and the word-aligned cursor following them. -/
def placeCommons (symbols : List Sym) (cursor : Nat) : Array (Option Nat) × Nat :=
  symbols.foldl (init := (#[], cursor)) fun (commons, cursor) sym =>
    if special sym shnCommon then
      let addr := alignUp cursor sym.value
      (commons.push (some addr), addr + sym.size)
    else
      (commons.push none, cursor)

def placeExternals (machine word : Nat) (symbols : List Sym) (cursor : Nat) : Std.HashMap String Nat × Nat :=
  symbols.foldl (init := ({}, cursor)) fun (externals, cursor) sym =>
    if isExternal machine sym && !externals.contains sym.name then
      let addr := alignUp cursor word
      (externals.insert sym.name addr, addr + word)
    else
      (externals, cursor)

/-- The symbols of the image: functions in allocated sections drop the Thumb bit or go through their descriptor. -/
def outputSymbols (tables : Tables) (memory : ByteArray) : List Symbol :=
  let input := tables.input
  let withIndex := input.symbols.toList.zipIdx
  withIndex.filterMap fun (sym, index) =>
    if sym.name.isEmpty then none
    else
      let allocated := (sym.extended || sym.shndx < shnLoreserve) && ((tables.addrs[sym.shndx]?).join).isSome
      let isFunction := isFunctionSym sym && allocated
      let value := (resolve tables index sym).getD sym.value
      let descriptor := match relocatedSection tables sym.shndx with
        | some (sec, _) =>
          if input.machine == emPpc64 && sec.name == ".opd" && sym.value + 8 ≤ sec.size then
            some (readNat memory input.little (sec.off + sym.value) 8)
          else none
        | none => none
      if isFunction then
        match descriptor with
        | some code => some ⟨sym.name, code, 0, true, false⟩
        | none =>
          let addr := if input.machine == emArm then value - value % 2 else value
          some ⟨sym.name, addr, sym.size, true, false⟩
      else
        some ⟨sym.name, value, sym.size, false, false⟩

/-- Assigns the addresses and applies the relocations. -/
def link (input : Input) : Output :=
  let word := input.width / 8
  let layout := layoutSections input.sections.toList input.base
  let symbols := input.symbols.toList
  let commonsStart := alignUp layout.cursor word
  let (commons, commonsEnd) := placeCommons symbols commonsStart
  let externalsStart := alignUp commonsEnd word
  let (externals, externalsEnd) := placeExternals input.machine word symbols externalsStart
  let gotBase := alignUp externalsEnd word
  let env : Env := ⟨input.machine, input.width, input.little, input.little || input.machine == 183, gotBase, input.data.size⟩
  let tables : Tables := ⟨input, env, layout.addrs, commons, externals⟩
  let start : LinkState := { memory := input.data }
  let state := match (relocate tables).run start with
    | .ok _ state => state
    | .error _ state => state
  let gotEnd := gotBase + state.gotCount * word
  { regions := layout.regions.reverse ++
      synthetic "%common" commonsStart commonsEnd none true ++
      synthetic "EXTERNAL" externalsStart externalsEnd none false ++
      synthetic "%got" gotBase gotEnd (some input.data.size) true
    symbols := outputSymbols tables state.memory
    references := state.references.reverse
    sectionAddrs := layout.addrs
    memory := state.memory
    warnings := state.warnings.reverse }

/-- The contents of a region: its bytes in `memory`, padded with zeros to its size. A section never reads past
the file's `fileSize` bytes into the GOT that follows them. -/
def regionBytes (memory : ByteArray) (fileSize : Nat) (region : Region) : ByteArray :=
  match region.off with
  | none => ByteArray.mk (Array.replicate region.size 0)
  | some off =>
    let limit := if region.isSection then min fileSize memory.size else memory.size
    let available := min region.size (limit - off)
    (memory.extract off (off + available)).append (ByteArray.mk (Array.replicate (region.size - available) 0))

def toMemRegion (memory : ByteArray) (fileSize : Nat) (region : Region) : MemRegion :=
  ⟨region.addr, regionBytes memory fileSize region, region.r, region.w, region.x⟩

def toSegment (region : Region) : Segment :=
  ⟨region.name, region.addr, region.size, region.r, region.w, region.x⟩

end Bap.Image.ElfLinker
