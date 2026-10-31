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
  /-- `st_other`, whose top bits give the local entry of a PowerPC64 ELFv2 function. -/
  other : Nat := 0
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
  /-- The global pointer the object was assembled for, of its `.reginfo` or `.MIPS.options`. -/
  gp0 : Int := 0
  /-- The index of the section of thunks, which the sections from there on moved one up for. -/
  thunksAt : Option Nat := none

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

/-! ### Constants of the ELF gABI -/

def shfWrite : Nat := 1
def shfAlloc : Nat := 2
def shfExecinstr : Nat := 4
def shfTls : Nat := 0x400
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
  else if machine == emPpc64 && sym.name == ".TOC." then some 0x8000
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

structure Output where
  regions : List Region
  symbols : List Symbol
  references : List (Nat × String)
  /-- The addresses of the sections, by section index. -/
  sectionAddrs : Array (Option Nat)
  /-- The input with the relocations applied, followed by the GOT. -/
  memory : ByteArray
  warnings : List String
  /-- The stores of the relocations in the order they were done, a site at a time. -/
  applied : List (Site × List Write) := []

/-- The thread-local storage of the image, as a `PT_TLS` segment says it. -/
structure TlsBlock where
  start : Nat := 0
  size : Nat := 0
  align : Nat := 1

structure Env where
  machine : Nat
  width : Nat
  little : Bool
  /-- AArch64 instructions are little-endian whatever the data is. -/
  codeLittle : Bool
  gotBase : Nat
  gotOff : Nat
  tls : TlsBlock := {}
  /-- What a MIPS object's local `GPREL` addends are relative to. -/
  gp0 : Int := 0

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
  /-- The stores done so far, the latest first, a site at a time. -/
  applied : List (Site × List Write) := []

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
    set { state with memory, applied := (site, writes) :: state.applied }
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

/-- A symbol's address as an offset from the thread pointer. The thread pointer is where each psABI puts it relative to
the thread-local block: past it in variant II, before it in variant I, and with a bias on MIPS and PowerPC. -/
def tpOff (env : Env) (s : Int) : Int :=
  let start : Int := env.tls.start
  let align : Int := max 1 env.tls.align
  let offset := s - start
  match env.machine with
  | 40 | 183 =>
    let tcb : Int := env.width / 4
    offset + tcb + (start - tcb) % align
  | 8 | 20 | 21 => offset + start % align - 0x7000
  | 243 => offset + start % align
  | _ =>
    let size := (alignUp env.tls.size (max 1 env.tls.align) : Nat)
    offset - size - (-start - size) % align

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
  | 18 => store 8 (tpOff env s + a)
  | 22 | 44 | 50 => store 4 ((← gotEntry env (tpOff env s)) + a - p)
  | 23 => store 4 (tpOff env s + a)
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
  | 27 | 30 => store 8 ((← gotEntry env s) - got + a)
  | 28 => store 8 ((← gotEntry env s) + a - p)
  | 29 => store 8 (got + a - p)
  | 31 => store 8 (s + a - got)
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
  | 15 => store 4 ((← gotEntry env (tpOff env s)) + (← addend 4))
  | 16 => store 4 ((← gotEntry env (tpOff env s)) + (← addend 4) - got)
  | 17 => store 4 (tpOff env s + (← addend 4))
  | 33 => store 4 ((← gotEntry env (-tpOff env s)) + (← addend 4) - got)
  | 34 => store 4 (-(tpOff env s) + (← addend 4))
  | 10 => store 4 (got + (← addend 4) - p)
  | 20 => store 2 (s + (← addend 2))
  | 21 => store 2 (s + (← addend 2) - p)
  | 22 => store 1 (s + (← addend 1))
  | 23 => store 1 (s + (← addend 1) - p)
  | _ => pure none

/-- An AArch64 page: the value with its low 12 bits cleared. -/
def aarch64Page (value : Int) : Int := value - value % 4096

/-- `immlo` and `immhi` of ADR and ADRP. -/
def aarch64Adr (value : Int) (insn : Nat) : Nat := setBits (setBits insn 29 2 value) 5 19 (value >>> 2)

/-- The scaled 12-bit offset of an ADD or a load, from the low bits of a value. -/
def aarch64Lo12 (shift : Nat) (value : Int) (insn : Nat) : Nat :=
  setBits insn 10 12 (field value 0 12 >>> shift : Nat)

/-- A signed MOVW: the sign bit above the 16 bits of the value says whether the instruction is a MOVZ of the value or a
MOVN, which takes it inverted. -/
def aarch64SMov (value : Int) (insn : Nat) : Nat :=
  if field value 16 1 == 1 then setBits (setBits insn 30 1 0) 5 16 ((field value 0 16 ^^^ 0xffff : Nat) : Int)
  else setBits (setBits insn 30 1 1) 5 16 value

def aarch64 (env : Env) (site : Site) : Outcome := do
  let s := site.s
  let a := site.a
  let p := site.p
  let x := s + a
  let store n value := done [stAt env site 0 n value]
  let update (f : Nat → Nat) : Outcome := do
    done [stiAt env site 0 4 (f (← ldi env site 0))]
  let page := aarch64Page
  let adr := aarch64Adr
  let lo12 (shift : Nat) (value : Int) : Outcome := update (aarch64Lo12 shift value)
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
  | 0x10e => update (aarch64SMov x)
  | 0x10f => update (aarch64SMov (x >>> 16))
  | 0x110 => update (aarch64SMov (x >>> 32))
  | 0x11c => lo12 1 x
  | 0x11d => lo12 2 x
  | 0x11e => lo12 3 x
  | 0x11f | 0x120 => update (aarch64SMov (x - p))
  | 0x121 | 0x122 => update (aarch64SMov ((x - p) >>> 16))
  | 0x123 | 0x124 => update (aarch64SMov ((x - p) >>> 32))
  | 0x125 => update (aarch64SMov ((x - p) >>> 48))
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
  | 0x21d =>
    let entry ← gotEntry env (tpOff env s + a)
    update (adr ((page entry - page p) >>> 12))
  | 0x21e =>
    let entry ← gotEntry env (tpOff env s + a)
    lo12 3 entry
  | 0x21f =>
    let entry ← gotEntry env (tpOff env s + a)
    update fun insn => setBits insn 5 19 ((entry - p) >>> 2)
  | 0x220 => update (aarch64SMov ((tpOff env s + a) >>> 32))
  | 0x221 => update (aarch64SMov ((tpOff env s + a) >>> 16))
  | 0x222 => update fun insn => setBits insn 5 16 ((tpOff env s + a) >>> 16)
  | 0x223 => update (aarch64SMov (tpOff env s + a))
  | 0x224 => update fun insn => setBits insn 5 16 (tpOff env s + a)
  | 0x225 => update (aarch64Lo12 0 ((tpOff env s + a) >>> 12))
  | 0x226 | 0x227 => lo12 0 (tpOff env s + a)
  | 0x228 | 0x229 => lo12 0 (tpOff env s + a)
  | 0x22a | 0x22b => lo12 1 (tpOff env s + a)
  | 0x22c | 0x22d => lo12 2 (tpOff env s + a)
  | 0x22e | 0x22f => lo12 3 (tpOff env s + a)
  | 0x23a | 0x23b => lo12 4 (tpOff env s + a)
  | _ => pure none

def isThumb (sym : Sym) : Bool := isFunctionSym sym && sym.value % 2 == 1

/-! `R_ARM_TARGET2` means what its platform says. On Linux it is `R_ARM_GOT_PREL`, which is what unwinders there read
back through the GOT and what lld and GNU ld do by default; bare-metal systems use `R_ARM_REL32` instead. -/

/-! Instruction fields of ARM and Thumb. A word holds what its bits say whatever else the word holds, which is what
the theorems about these say. -/

/-- The 16-bit immediate of an A32 MOVW or MOVT. -/
def armMovImm (insn : Nat) : Nat := field insn 16 4 * 2 ^ 12 + field insn 0 12

def armMovSet (insn : Nat) (value : Int) : Nat := setBits (setBits insn 16 4 (value >>> 12)) 0 12 value

/-- The 16-bit immediate of a T32 MOVW or MOVT, `imm4:i:imm3:imm8`. -/
def thumbMovImm (hw1 hw2 : Nat) : Nat :=
  field hw1 0 4 * 2 ^ 12 + field hw1 10 1 * 2 ^ 11 + field hw2 12 3 * 2 ^ 8 + field hw2 0 8

def thumbMovSet1 (hw1 : Nat) (value : Int) : Nat := setBits (setBits hw1 0 4 (value >>> 12)) 10 1 (value >>> 11)
def thumbMovSet2 (hw2 : Nat) (value : Int) : Nat := setBits (setBits hw2 12 3 (value >>> 8)) 0 8 value

/-- The offset of an A32 branch: the 24-bit immediate, in words. -/
def armBranchImm (insn : Nat) : Int := sext (field insn 0 24 * 4 : Nat) 26

def armBranchSet (insn : Nat) (value : Int) : Nat := setBits insn 0 24 (value >>> 2)

/-- The offset of a T32 BL, BLX or B.W, `S:I1:I2:imm10:imm11:0` with `I = NOT(J XOR S)`. -/
def thumbBranchImm (hw1 hw2 : Nat) : Int :=
  let sign := field hw1 10 1
  let i1 := 1 - (field hw2 13 1 ^^^ sign)
  let i2 := 1 - (field hw2 11 1 ^^^ sign)
  sext (sign * 2 ^ 24 + i1 * 2 ^ 23 + i2 * 2 ^ 22 + field hw1 0 10 * 2 ^ 12 + field hw2 0 11 * 2 : Nat) 25

def thumbBranchSet1 (hw1 : Nat) (value : Int) : Nat := setBits (setBits hw1 10 1 (value >>> 24)) 0 10 (value >>> 12)

def thumbBranchSet2 (hw2 : Nat) (value : Int) : Nat :=
  let sign := field value 24 1
  setBits (setBits (setBits hw2 13 1 ((1 - (field value 23 1 ^^^ sign) : Nat) : Int))
    11 1 ((1 - (field value 22 1 ^^^ sign) : Nat) : Int)) 0 11 (value >>> 1)

/-- The offset of a T32 conditional B.W, `S:J2:J1:imm6:imm11:0`. -/
def thumbJump19Imm (hw1 hw2 : Nat) : Int :=
  sext (field hw1 10 1 * 2 ^ 20 + field hw2 11 1 * 2 ^ 19 + field hw2 13 1 * 2 ^ 18 + field hw1 0 6 * 2 ^ 12 +
    field hw2 0 11 * 2 : Nat) 21

def thumbJump19Set1 (hw1 : Nat) (value : Int) : Nat := setBits (setBits hw1 10 1 (value >>> 20)) 0 6 (value >>> 12)

def thumbJump19Set2 (hw2 : Nat) (value : Int) : Nat :=
  setBits (setBits (setBits hw2 13 1 (value >>> 18)) 11 1 (value >>> 19)) 0 11 (value >>> 1)

/-- The offset of a narrow Thumb branch with an `n`-bit immediate, in halfwords. -/
def thumbShortImm (n hw : Nat) : Int := sext (field hw 0 n * 2 : Nat) (n + 1)

def thumbShortSet (n hw : Nat) (value : Int) : Nat := setBits hw 0 n (value >>> 1)

/-- The address of a symbol without its Thumb bit. -/
def armS (site : Site) : Int := if isThumb site.sym then site.s - site.s % 2 else site.s

/-- `(S + A) | T`: a value with the Thumb bit of the symbol. -/
def armWithT (site : Site) (value : Int) : Int := if isThumb site.sym && value % 2 == 0 then value + 1 else value

/-- The addend: the one of the record, or the one in the place. -/
def addendOf (site : Site) (decoded : Int) : Int := if site.rel.isExplicit then site.a else decoded

def arm (env : Env) (site : Site) : Outcome := do
  let sym := site.sym
  let typ := site.rel.typ
  let p := site.p
  let got : Int := env.gotBase
  let thumb := isThumb sym
  let s : Int := armS site
  let withT := armWithT site
  let addend := addendOf site
  let a32 : LinkM Int := do pure (addend (sext (← ld env site 0 4) 32))
  let store n value := done [stAt env site 0 n value]
  let movw (kind : Nat) (imm : Nat) : Int :=
    let a := addend (sext imm 16)
    match kind with
    | 0 => withT (s + a)
    | 1 => (s + a) >>> 16
    | 2 => withT (s + a) - p
    | _ => (s + a - p) >>> 16
  let armMovw (kind : Nat) : Outcome := do
    let insn ← ld env site 0 4
    store 4 (armMovSet insn (movw kind (armMovImm insn)) : Nat)
  let thumbMovw (kind : Nat) : Outcome := do
    let hw1 ← ld env site 0 2
    let hw2 ← ld env site 2 2
    let v := movw kind (thumbMovImm hw1 hw2)
    done [stAt env site 0 2 (thumbMovSet1 hw1 v : Nat), stAt env site 2 2 (thumbMovSet2 hw2 v : Nat)]
  let armBranch : Outcome := do
    let insn ← ld env site 0 4
    let v := s + addend (armBranchImm insn) - p
    if typ == 0x1c && thumb then
      store 4 (setBits (armBranchSet 0xfa000000 v) 24 1 (v >>> 1) : Nat)
    else if typ == 0x1c && isFunctionSym sym && field insn 28 4 == 0xf then
      store 4 (armBranchSet 0xeb000000 v : Nat)
    else
      store 4 (armBranchSet insn v : Nat)
  let thumbBranch : Outcome := do
    let hw1 ← ld env site 0 2
    let hw2 ← ld env site 2 2
    let a := addend (thumbBranchImm hw1 hw2)
    let call := typ == 0xa
    let blx := call && (if isFunctionSym sym then !thumb else field hw2 12 1 == 0)
    let v := if blx then s + a - (p - p % 4) else s + a - p
    let hw2 := if !call then hw2 else setBits hw2 12 1 (if blx then 0 else 1)
    done [stAt env site 0 2 (thumbBranchSet1 hw1 v : Nat), stAt env site 2 2 (thumbBranchSet2 hw2 v : Nat)]
  let thumbJump19 : Outcome := do
    let hw1 ← ld env site 0 2
    let hw2 ← ld env site 2 2
    let v := s + addend (thumbJump19Imm hw1 hw2) - p
    done [stAt env site 0 2 (thumbJump19Set1 hw1 v : Nat), stAt env site 2 2 (thumbJump19Set2 hw2 v : Nat)]
  let thumbShortBranch (n : Nat) : Outcome := do
    let hw ← ld env site 0 2
    store 2 (thumbShortSet n hw (s + addend (thumbShortImm n hw) - p) : Nat)
  match typ with
  | 0 | 0x28 => done []
  | 1 | 0x1c | 0x1d => armBranch
  | 2 | 0x26 => store 4 (withT (s + (← a32)))
  | 3 => store 4 (withT (s + (← a32)) - p)
  | 5 => store 2 (s + addend (sext (← ld env site 0 2) 16))
  | 8 => store 1 (s + addend (sext (← ld env site 0 1) 8))
  | 0xa | 0x1e => thumbBranch
  | 0x18 => store 4 (s + (← a32) - got)
  | 0x19 => store 4 (got + (← a32) - p)
  | 0x1a => store 4 ((← gotEntry env (withT s)) + (← a32) - got)
  | 0x2a =>
    let old ← ld env site 0 4
    let a := addend (sext (field old 0 31) 31)
    store 4 (setBits old 0 31 (withT (s + a) - p) : Nat)
  | 0x2b => armMovw 0
  | 0x2c => armMovw 1
  | 0x2d => armMovw 2
  | 0x2e => armMovw 3
  | 0x2f => thumbMovw 0
  | 0x30 => thumbMovw 1
  | 0x31 => thumbMovw 2
  | 0x32 => thumbMovw 3
  | 0x33 => thumbJump19
  | 0x29 | 0x60 => store 4 ((← gotEntry env (withT s)) + (← a32) - p)
  | 0x66 => thumbShortBranch 11
  | 0x67 => thumbShortBranch 8
  | 0x6b => store 4 ((← gotEntry env (tpOff env s)) + (← a32) - p)
  | 0x6c => store 4 (tpOff env s + (← a32))
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

/-- The high half of a 16-bit pair: `HI16 << 16` and the sign-extended `LO16` add up to the value. -/
def mipsHi (value : Int) : Int := (value + 0x8000) >>> 16

/-- The two highest halves of a four-instruction 64-bit constant, each carrying the halves below it. -/
def mipsHigher (value : Int) : Int := (value + 0x80008000) >>> 32
def mipsHighest (value : Int) : Int := (value + 0x800080008000) >>> 48

/-- A middle relocation of a compound record of the N64 ABI, on `S`, the special symbol of the record, and whose addend
is the result so far: `R_MIPS_SUB` is `S - A`, `R_MIPS_64` is `S + A`, and `R_MIPS_NONE` leaves it. -/
def mipsCompoundStep (s value : Int) : Nat → Option Int
  | 0 => some value
  | 18 => some (s + value)
  | 24 => some (s - value)
  | _ => none

/-- The address the special symbol of a compound record stands for: `RSS_UNDEF`, `RSS_GP`, `RSS_GP0` or `RSS_LOC`. -/
def mipsSpecial (env : Env) (site : Site) : Nat → Option Int
  | 0 => some 0
  | 1 => some (mipsGp env)
  | 2 => some env.gp0
  | 3 => some site.p
  | _ => none

/-- The last relocation of a compound record, on the result so far: the size of its store and what it stores. -/
def mipsCompoundField (insn : Nat) (s value : Int) : Nat → Option (Nat × Int)
  | 2 => some (4, s + value)
  | 18 => some (8, s + value)
  | 24 => some (8, s - value)
  | 5 => some (4, setLo16 insn (mipsHi (s + value)))
  | 6 => some (4, setLo16 insn (s + value))
  | 28 => some (4, setLo16 insn (mipsHigher (s + value)))
  | 29 => some (4, setLo16 insn (mipsHighest (s + value)))
  | _ => none

/-- What a local symbol's `GPREL` addend is relative to, in the object it came from. -/
def mipsGp0 (env : Env) (sym : Sym) : Int := if sym.bind == stbLocal then env.gp0 else 0

/-- The value of the first relocation of a compound record, which is the only one with a symbol. -/
def mipsCompoundBase (env : Env) (site : Site) (typ : Nat) : LinkM (Option Int) := do
  let x := site.s + site.a
  let gp := mipsGp env
  match typ with
  | 2 | 3 | 18 => pure (some x)
  | 7 | 12 => pure (some (x + mipsGp0 env site.sym - gp))
  | 248 => pure (some (x - site.p))
  | 19 => pure (some ((← gotEntry env x) - gp))
  | 9 | 11 => pure (some ((← gotEntry env site.s) - gp))
  | _ => pure none

/-- A record of the N64 ABI that packs up to three relocations, its type holding the bytes `ssym:type3:type2:type`, or the
same relocations of N32 in successive records, which the reader of the file packs. Each relocation's result is the addend of
the next, the second one's symbol is the special one and the third one has none, and the last one stores it. Unlike lld's two
fixed combinations, and its `RSS_UNDEF` only, this is the ABI's general rule. -/
def mipsCompound (env : Env) (site : Site) : Outcome := do
  let typ := site.rel.typ
  let second := (typ >>> 8) % 256
  let third := (typ >>> 16) % 256
  match mipsSpecial env site (typ >>> 24) with
  | none => pure none
  | some special =>
    match ← mipsCompoundBase env site (typ % 256) with
    | none => pure none
    | some base =>
      match if third != 0 then mipsCompoundStep special base second else some base with
      | none => pure none
      | some value =>
        match mipsCompoundField (← ld env site 0 4) (if third != 0 then 0 else special) value
            (if third != 0 then third else second) with
        | some (n, stored) => done [stAt env site 0 n stored]
        | none => pure none

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
  let gotOffset (value : LinkM Int) : LinkM Int := do pure ((← value) - gp)
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
    let insn ← ld env site 0 4
    mipsFlush env lo rel.symbol
    let s := if sym.name == "_gp_disp" then gp - p + 4 else s
    store 4 (setLo16 insn (s + lo))
  | 7 | 8 => store 4 (setLo16 (← ld env site 0 4) (s + (← a16) + mipsGp0 env sym - gp))
  | 10 =>
    let insn ← ld env site 0 4
    let a := addendOf site (sext ((insn &&& 0xffff) <<< 2 : Nat) 18)
    store 4 (setLo16 insn ((s + a - p) >>> 2))
  | 12 => store 4 (s + (← a32) + mipsGp0 env sym - gp)
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
  | 19 => store 4 (setLo16 (← ld env site 0 4) (← gotOffset (gotEntry env (s + (← a16)))))
  | 22 | 30 => store 4 (setLo16 (← ld env site 0 4) (mipsHi (← gotOffset (gotEntry env (s + (← a16))))))
  | 23 | 31 => store 4 (setLo16 (← ld env site 0 4) (← gotOffset (gotEntry env (s + (← a16)))))
  | 28 => store 4 (setLo16 (← ld env site 0 4) (mipsHigher (s + (← a16))))
  | 29 => store 4 (setLo16 (← ld env site 0 4) (mipsHighest (s + (← a16))))
  | 46 => store 4 (setLo16 (← ld env site 0 4) ((← gotEntry env (tpOff env s)) + (← a16) - gp))
  | 47 => store 4 (tpOff env s + (← a32))
  | 48 => if env.width == 64 then store 8 (tpOff env s + (← a32)) else pure none
  | 49 => store 4 (setLo16 (← ld env site 0 4) (mipsHi (tpOff env s + (← a16))))
  | 50 => store 4 (setLo16 (← ld env site 0 4) (tpOff env s + (← a16)))
  | 248 => store 4 (s + (← a32) - p)
  | typ => if typ < 256 then pure none else mipsCompound env site

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
  setBits (setBits (setBits (setBits insn 31 1 (value >>> 12)) 25 6 (value >>> 5)) 8 4 (value >>> 1)) 7 1 (value >>> 11)
def riscvJ (value : Int) (insn : Nat) : Int :=
  setBits (setBits (setBits (setBits insn 31 1 (value >>> 20)) 21 10 (value >>> 1)) 20 1 (value >>> 11)) 12 8 (value >>> 12)
def riscvCB (value : Int) (insn : Nat) : Int :=
  setBits (setBits (setBits (setBits (setBits insn 12 1 (value >>> 8)) 10 2 (value >>> 3)) 5 2 (value >>> 6))
    3 2 (value >>> 1)) 2 1 (value >>> 5)
def riscvCJ (value : Int) (insn : Nat) : Int :=
  setBits (setBits (setBits (setBits (setBits (setBits (setBits (setBits insn 12 1 (value >>> 11)) 11 1 (value >>> 4))
    9 2 (value >>> 8)) 8 1 (value >>> 10)) 7 1 (value >>> 6)) 6 1 (value >>> 7)) 3 3 (value >>> 1)) 2 1 (value >>> 5)

/-- The pc-relative values of the AUIPC instructions, collected before the relocations are applied, because
a `PCREL_LO12` relocation refers to the label of its AUIPC rather than to the target. -/
def riscvPrescan (env : Env) (site : Site) : LinkM Unit := do
  match site.rel.typ with
  | 20 =>
    let entry ← gotEntry env site.s
    modify fun state => { state with riscvHi := state.riscvHi.insert site.p (entry + site.a - site.p) }
  | 21 =>
    let entry ← gotEntry env (tpOff env site.s + site.a)
    modify fun state => { state with riscvHi := state.riscvHi.insert site.p (entry - site.p) }
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
  | 0 | 32 | 43 | 51 => done []
  | 1 => store 4 x
  | 2 => store 8 x
  | 16 => update (riscvB (x - p))
  | 17 => update (riscvJ (x - p))
  | 18 | 19 =>
    let v := x - p
    let first ← ldi env site 0
    let second ← ldi env site 4
    done [stiAt env site 0 4 (riscvU v first), stiAt env site 4 4 (riscvI v second)]
  | 29 => update (riscvU (tpOff env s + a))
  | 30 => update (riscvI (tpOff env s + a))
  | 31 => update (riscvS (tpOff env s + a))
  | 20 | 21 | 23 =>
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

/-- The TOC pointer of PowerPC64: 32 KiB into the TOC, which starts with the GOT, as with `.TOC.`. -/
def ppcToc (env : Env) : Int := env.gotBase + 0x8000

/-- The halves of a value: `@h` is plain, and `@ha` carries the sign of what is below it. -/
def ppcHi (value : Int) : Int := value >>> 16
def ppcHa (value : Int) : Int := (value + 0x8000) >>> 16
def ppcHigher (value : Int) : Int := value >>> 32
def ppcHighera (value : Int) : Int := (value + 0x8000) >>> 32
def ppcHighest (value : Int) : Int := value >>> 48
def ppcHighesta (value : Int) : Int := (value + 0x8000) >>> 48

/-- Whether an instruction's offset is DQ-form, with four low bits that are not the offset: `lq`, `lxvp` and `stxvp`,
and `lxv` and `stxv` among opcode 61. -/
def ppcIsDq (insn : Nat) : Bool :=
  let opcode := field insn 26 6
  opcode == 6 || opcode == 56 || (opcode == 61 && field insn 0 2 == 1)

/-- A DS-form or DQ-form offset, the low bits of whose halfword belong to the instruction. -/
def ppcDsHalf (dq : Bool) (old : Nat) (value : Int) : Nat :=
  if dq then setBits old 4 12 (value >>> 4) else setBits old 2 14 (value >>> 2)

/-- The word of the instruction whose low halfword is at the place: the place is in its second half on big-endian. -/
def ppcInsnOfHalf (env : Env) (site : Site) : LinkM Nat := do
  if env.little then ldi env site 0
  else if site.off < 2 then throw (outside site)
  else load { site with off := site.off - 2 } 0 4 false

def powerpc (env : Env) (site : Site) : Outcome := do
  let p := site.p
  let x := site.s + site.a
  let store n value := done [stAt env site 0 n value]
  let update (f : Nat → Nat) : Outcome := do done [stiAt env site 0 4 (f (← ldi env site 0))]
  let ds (value : Int) : Outcome := do
    let old ← ld env site 0 2
    store 2 (ppcDsHalf (ppcIsDq (← ppcInsnOfHalf env site)) old value : Nat)
  match site.rel.typ with
  | 0 => done []
  | 1 => store 4 x
  | 2 => update fun i => setBits i 2 24 (x >>> 2)
  | 3 | 4 => store 2 x
  | 5 => store 2 (ppcHi x)
  | 6 => store 2 (ppcHa x)
  | 7 => update fun i => setBits i 2 14 (x >>> 2)
  | 10 | 18 => update fun i => setBits i 2 24 ((x - p) >>> 2)
  | 11 => update fun i => setBits i 2 14 ((x - p) >>> 2)
  | 26 => store 4 (x - p)
  | 38 => store 8 x
  | 44 => store 8 (x - p)
  | 67 => done []
  | 69 | 70 => store 2 (tpOff env site.s + site.a)
  | 71 => store 2 (ppcHi (tpOff env site.s + site.a))
  | 72 => store 2 (ppcHa (tpOff env site.s + site.a))
  | typ =>
    if env.machine != emPpc64 then
      let got : LinkM Int := do pure ((← gotEntry env (tpOff env site.s + site.a)) - (env.gotBase + 0x8000))
      match typ with
      | 73 => store 4 (tpOff env site.s + site.a)
      | 87 | 88 => store 2 (← got)
      | 89 => store 2 (ppcHi (← got))
      | 90 => store 2 (ppcHa (← got))
      | _ => pure none
    else
      let toc := ppcToc env
      let got : LinkM Int := do pure ((← gotEntry env x) - toc)
      let tp := tpOff env site.s + site.a
      let gotTp : LinkM Int := do pure ((← gotEntry env tp) - toc)
      match typ with
      | 73 => store 8 tp
      | 87 | 88 => ds (← gotTp)
      | 89 => store 2 (ppcHi (← gotTp))
      | 90 => store 2 (ppcHa (← gotTp))
      | 95 | 96 => ds tp
      | 97 => store 2 (ppcHigher tp)
      | 98 => store 2 (ppcHighera tp)
      | 99 => store 2 (ppcHighest tp)
      | 100 => store 2 (ppcHighesta tp)
      | 112 => store 2 (ppcHi tp)
      | 113 => store 2 (ppcHa tp)
      | 14 | 15 => store 2 (← got)
      | 16 => store 2 (ppcHi (← got))
      | 17 => store 2 (ppcHa (← got))
      | 39 => store 2 (ppcHigher x)
      | 40 => store 2 (ppcHighera x)
      | 41 => store 2 (ppcHighest x)
      | 42 => store 2 (ppcHighesta x)
      | 47 | 48 => store 2 (x - toc)
      | 49 => store 2 (ppcHi (x - toc))
      | 50 => store 2 (ppcHa (x - toc))
      | 51 => store 8 (toc + site.a)
      | 56 | 57 => ds x
      | 58 | 59 => ds (← got)
      | 63 | 64 => ds (x - toc)
      | 249 | 250 => store 2 (x - p)
      | 251 => store 2 (ppcHi (x - p))
      | 252 => store 2 (ppcHa (x - p))
      | _ => pure none

def systemz (env : Env) (site : Site) : Outcome := do
  let x := site.s + site.a
  let pc := x - site.p
  let store n value := done [stAt env site 0 n value]
  match site.rel.typ with
  | 0 => done []
  | 1 => store 1 x
  | 2 =>
    let old ← ld env site 0 2
    store 2 (setBits old 0 12 x : Nat)
  | 3 => store 2 x
  | 4 => store 4 x
  | 5 | 8 => store 4 pc
  | 16 => store 2 pc
  | 17 | 18 => store 2 (pc >>> 1)
  | 19 | 20 => store 4 (pc >>> 1)
  | 22 => store 8 x
  | 23 | 25 => store 8 pc
  | 37 => done []
  | 43 => store 4 ((← gotEntry env (tpOff env site.s)) - env.gotBase + site.a)
  | 44 => store 8 ((← gotEntry env (tpOff env site.s)) - env.gotBase + site.a)
  | 47 => store 4 ((← gotEntry env (tpOff env site.s)) + site.a)
  | 48 => store 8 ((← gotEntry env (tpOff env site.s)) + site.a)
  | 49 => store 4 (((← gotEntry env (tpOff env site.s)) + site.a - site.p) >>> 1)
  | 50 => store 4 (tpOff env site.s + site.a)
  | 51 => store 8 (tpOff env site.s + site.a)
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

def nullSym : Sym := ⟨"", shnUndef, false, 0, 0, 0, 0, 0⟩

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

/-- From the global to the local entry of an ELFv2 function, as the top bits of `st_other` say. All the code shares
one TOC here, so a call takes the local entry. Values 0 and 1 mean none, and 7 is reserved. -/
def ppcLocalEntry (other : Nat) : Nat :=
  match (other >>> 5) % 8 with
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 32
  | 6 => 64
  | _ => 0

/-- The symbol of a PowerPC64 branch through a function descriptor in `.opd` is the code it points to, and an ELFv2
function is entered past what sets up its TOC pointer. -/
def resolveBranchTarget (tables : Tables) (rel : Rel) (sym : Sym) : Option Nat :=
  let plain := (resolve tables rel.symbol sym).map (· + if tables.input.machine == emPpc64 && (rel.typ == 10 || rel.typ == 18)
    then ppcLocalEntry sym.other else 0)
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

/-! ### Field overflow

What a relocation stores is cut to the bits of its field, and most psABIs make it an error if that loses anything, for the
fields that are not explicitly a part of a bigger value (the `_NC`, `LO` and `HA` ones). These are `ld.lld`'s `checkInt`,
`checkUInt` and `checkIntUInt` (`lld/ELF/Arch/*.cpp` of LLVM 23.1.4, each entry read against `relocate`), on values as wide as the
machine's word. Where a relocation has a check here and none there, the psABI has one or the value does not reach what it says:
what lld does not link at all (`R_ARM_ABS8`, `R_ARM_ABS16`, `R_MIPS_LITERAL`, `R_PPC64_ADDR24`, `R_PPC64_REL16` and the checked
`TLSLE_*_TPREL_LO12` of AArch64), `R_PPC64_ADDR14` and `R_MIPS_26`, which lld cuts in silence. -/

/-- How a field holds its value. -/
inductive FieldKind where
  | signed
  | unsigned
  /-- Whichever the user meant, as a data field of the size of a C `int` can be either. -/
  | either
  deriving DecidableEq, Repr

/-- A value that must fit in the `bits` bits of a field. -/
structure FieldCheck where
  kind : FieldKind
  bits : Nat
  value : Int

/-- Whether a value fits in a field, as the range of the kind says. -/
def fits (kind : FieldKind) (bits : Nat) (value : Int) : Bool :=
  match kind with
  | .signed => -((2 ^ (bits - 1) : Nat) : Int) ≤ value && value < ((2 ^ (bits - 1) : Nat) : Int)
  | .unsigned => 0 ≤ value && value < ((2 ^ bits : Nat) : Int)
  | .either => -((2 ^ (bits - 1) : Nat) : Int) ≤ value && value < ((2 ^ bits : Nat) : Int)

/-- A value as the machine computes it: in a word, sign-extended. -/
def wordValue (env : Env) (value : Int) : Int := sext value (if env.width == 32 then 32 else 64)

/-- The GOT slot of a value that has one by now. -/
def slotOf (state : LinkState) (value : Int) : Int := ((state.got[field value 0 64]?).getD 0 : Nat)

/-- The field a relocation of x86-64 is cut to. -/
def x86_64Field (env : Env) (state : LinkState) (site : Site) : Option FieldCheck :=
  let x := site.s + site.a
  let got : Int := env.gotBase
  let tp := tpOff env site.s + site.a
  match site.rel.typ with
  | 2 | 4 => some ⟨.signed, 32, x - site.p⟩
  | 3 => some ⟨.signed, 32, slotOf state site.s - got + site.a⟩
  | 9 | 41 | 42 | 43 => some ⟨.signed, 32, slotOf state site.s + site.a - site.p⟩
  | 10 => some ⟨.unsigned, 32, x⟩
  | 11 => some ⟨.signed, 32, x⟩
  | 12 => some ⟨.either, 16, x⟩
  | 13 => some ⟨.signed, 16, x - site.p⟩
  | 14 => some ⟨.either, 8, x⟩
  | 15 => some ⟨.signed, 8, x - site.p⟩
  | 22 | 44 | 50 => some ⟨.signed, 32, slotOf state (tpOff env site.s) + site.a - site.p⟩
  | 23 => some ⟨.signed, 32, tp⟩
  | 26 => some ⟨.signed, 32, got + site.a - site.p⟩
  | 32 => some ⟨.signed, 32, site.sym.size + site.a⟩
  | _ => none

/-- The field a relocation of i386 is cut to. -/
def i386Field (env : Env) (state : LinkState) (site : Site) : Option FieldCheck :=
  let addend (n : Nat) : Int :=
    addendOf site (sext (readNat state.memory env.little site.off n) (8 * n))
  let got : Int := env.gotBase
  let tp := tpOff env site.s
  match site.rel.typ with
  | 2 | 4 => some ⟨.signed, 32, site.s + addend 4 - site.p⟩
  | 20 => some ⟨.either, 16, site.s + addend 2⟩
  | 21 => some ⟨.signed, 17, site.s + addend 2 - site.p⟩
  | 22 => some ⟨.either, 8, site.s + addend 1⟩
  | 23 => some ⟨.signed, 8, site.s + addend 1 - site.p⟩
  | 16 => some ⟨.signed, 32, slotOf state tp + addend 4 - got⟩
  | 17 => some ⟨.signed, 32, tp + addend 4⟩
  | 34 => some ⟨.signed, 32, -tp + addend 4⟩
  | _ => none

/-- The field a relocation of AArch64 is cut to. -/
def aarch64Field (env : Env) (state : LinkState) (site : Site) : Option FieldCheck :=
  let x := site.s + site.a
  let p := site.p
  let tp := tpOff env site.s + site.a
  let page := aarch64Page
  match site.rel.typ with
  | 0x102 => some ⟨.either, 32, x⟩
  | 0x103 => some ⟨.either, 16, x⟩
  | 0x105 | 0x13a => some ⟨.signed, 32, x - p⟩
  | 0x106 => some ⟨.signed, 16, x - p⟩
  | 0x107 => some ⟨.unsigned, 16, x⟩
  | 0x109 => some ⟨.unsigned, 32, x⟩
  | 0x10b => some ⟨.unsigned, 48, x⟩
  | 0x10e => some ⟨.signed, 17, x⟩
  | 0x10f => some ⟨.signed, 33, x⟩
  | 0x110 => some ⟨.signed, 49, x⟩
  | 0x111 | 0x118 => some ⟨.signed, 21, x - p⟩
  | 0x112 => some ⟨.signed, 21, x - p⟩
  | 0x113 => some ⟨.signed, 33, page x - page p⟩
  | 0x117 => some ⟨.signed, 16, x - p⟩
  | 0x11a | 0x11b => some ⟨.signed, 28, x - p⟩
  | 0x11f => some ⟨.signed, 17, x - p⟩
  | 0x121 => some ⟨.signed, 33, x - p⟩
  | 0x123 => some ⟨.signed, 49, x - p⟩
  | 0x135 => some ⟨.signed, 21, slotOf state x - p⟩
  | 0x137 => some ⟨.signed, 33, page (slotOf state x) - page p⟩
  | 0x13b => some ⟨.signed, 32, slotOf state site.s + site.a - p⟩
  | 0x21d => some ⟨.signed, 33, page (slotOf state tp) - page p⟩
  | 0x21f => some ⟨.signed, 21, slotOf state tp - p⟩
  | 0x220 => some ⟨.signed, 49, tp⟩
  | 0x221 => some ⟨.signed, 33, tp⟩
  | 0x223 => some ⟨.signed, 17, tp⟩
  | 0x225 => some ⟨.unsigned, 24, tp⟩
  | 0x226 | 0x228 | 0x22a | 0x22c | 0x22e | 0x23a => some ⟨.unsigned, 12, tp⟩
  | _ => none

/-- The field a relocation of ARM is cut to. -/
def armField (env : Env) (state : LinkState) (site : Site) : Option FieldCheck :=
  let sym := site.sym
  let s := armS site
  let p := site.p
  let addend := addendOf site
  let hw1 := readNat state.memory env.little site.off 2
  let hw2 := readNat state.memory env.little (site.off + 2) 2
  let word := readNat state.memory env.little site.off 4
  match site.rel.typ with
  | 1 | 0x1c | 0x1d => some ⟨.signed, 26, s + addend (armBranchImm word) - p⟩
  | 5 => some ⟨.either, 16, s + addend (sext hw1 16)⟩
  | 8 => some ⟨.either, 8, s + addend (sext (readNat state.memory env.little site.off 1) 8)⟩
  | 0xa | 0x1e =>
    let a := addend (thumbBranchImm hw1 hw2)
    let blx := site.rel.typ == 0xa && (if isFunctionSym sym then !isThumb sym else field hw2 12 1 == 0)
    some ⟨.signed, 25, if blx then s + a - (p - p % 4) else s + a - p⟩
  | 0x2a => some ⟨.signed, 31, armWithT site (s + addend (sext (field word 0 31) 31)) - p⟩
  | 0x33 => some ⟨.signed, 21, s + addend (thumbJump19Imm hw1 hw2) - p⟩
  | 0x66 => some ⟨.signed, 12, s + addend (thumbShortImm 11 hw1) - p⟩
  | 0x67 => some ⟨.signed, 9, s + addend (thumbShortImm 8 hw1) - p⟩
  | _ => none

/-- Where an `R_MIPS_26` means to go. Its field has the low 28 bits, and the top ones are those of the place. -/
def mips26Target (site : Site) (insn : Nat) : Int :=
  let a : Int := addendOf site ((insn &&& 0x3ffffff) <<< 2 : Nat)
  if site.sym.bind == stbLocal then (field a 0 28 : Nat) + site.s else sext a 28 + site.s

/-- The field a relocation of MIPS is cut to. -/
def mipsField (env : Env) (state : LinkState) (site : Site) : Option FieldCheck :=
  let gp := mipsGp env
  let insn := readNat state.memory env.little site.off 4
  let a16 : Int := addendOf site (sext (insn &&& 0xffff : Nat) 16)
  let x16 := site.s + a16
  let page := x16 + 0x8000
  match site.rel.typ with
  | 4 => some ⟨.unsigned, 28, mips26Target site insn - ((site.p + 4) >>> 28) * 2 ^ 28⟩
  | 9 => if site.sym.bind == stbLocal then none else some ⟨.signed, 16, slotOf state site.s - gp⟩
  | 20 =>
    if env.width == 64 && !(site.sym.bind == stbLocal && sext x16 32 == x16) then
      some ⟨.signed, 16, slotOf state (page - page % 65536) - gp⟩
    else none
  | 7 | 8 => some ⟨.signed, 16, site.s + a16 + mipsGp0 env site.sym - gp⟩
  | 10 => some ⟨.signed, 18, site.s + addendOf site (sext ((insn &&& 0xffff) <<< 2 : Nat) 18) - site.p⟩
  | 11 => some ⟨.signed, 16, slotOf state site.s - gp⟩
  | 19 => some ⟨.signed, 16, slotOf state (site.s + a16) - gp⟩
  | 46 => some ⟨.signed, 16, slotOf state (tpOff env site.s) + a16 - gp⟩
  | _ => none

/-- The length of the ULEB128 number at an offset, in at most ten bytes. -/
def ulebSize (memory : ByteArray) (off : Nat) : Nat → Nat
  | 0 => 1
  | fuel + 1 => if (memory.get! off).toNat &&& 0x80 == 0 then 1 else ulebSize memory (off + 1) fuel + 1

/-- The ULEB128 number of `n` bytes at an offset. -/
def ulebValue (memory : ByteArray) (off n : Nat) : Int :=
  ((List.range n).foldl (init := 0) fun old i => old + ((memory.get! (off + i)).toNat &&& 0x7f) * 2 ^ (7 * i) : Nat)

/-- The field a relocation of RISC-V is cut to. -/
def riscvField (env : Env) (state : LinkState) (site : Site) : Option FieldCheck :=
  let x := site.s + site.a
  let p := site.p
  let hi (value : Int) : Int := wordValue env (value + 0x800) >>> 12
  match site.rel.typ with
  | 16 => some ⟨.signed, 13, x - p⟩
  | 17 => some ⟨.signed, 21, x - p⟩
  | 18 | 19 => some ⟨.signed, 20, hi (x - p)⟩
  | 20 | 21 | 23 => (state.riscvHi[p]?).map fun value => ⟨.signed, 20, hi value⟩
  | 26 => some ⟨.signed, 20, hi x⟩
  | 29 => some ⟨.signed, 20, hi (tpOff env site.s + site.a)⟩
  | 41 => some ⟨.signed, 32, slotOf state site.s + site.a - p⟩
  | 44 => some ⟨.signed, 9, x - p⟩
  | 45 => some ⟨.signed, 12, x - p⟩
  | 56 => some ⟨.signed, 32, x⟩
  | 57 | 59 => some ⟨.signed, 32, x - p⟩
  | 60 => some ⟨.unsigned, 7 * ulebSize state.memory site.off 9, x⟩
  | 61 => some ⟨.unsigned, 7 * ulebSize state.memory site.off 9, ulebValue state.memory site.off (ulebSize state.memory site.off 9) - x⟩
  | _ => none

/-- The field a relocation of PowerPC is cut to. -/
def powerpcField (env : Env) (state : LinkState) (site : Site) : Option FieldCheck :=
  let x := site.s + site.a
  let p := site.p
  let toc := ppcToc env
  let tp := tpOff env site.s + site.a
  match site.rel.typ with
  | 2 => some ⟨.signed, 26, x⟩
  | 3 => some ⟨.either, 16, x⟩
  | 7 => some ⟨.signed, 16, x⟩
  | 10 | 18 => some ⟨.signed, 26, x - p⟩
  | 11 => some ⟨.signed, 16, x - p⟩
  | 69 => some ⟨.signed, 16, tp⟩
  | typ =>
    if env.machine != emPpc64 then
      if typ == 87 then some ⟨.signed, 16, slotOf state tp - toc⟩ else none
    else
      let got := slotOf state x - toc
      let gotTp := slotOf state tp - toc
      match typ with
      | 1 => some ⟨.either, 32, x⟩
      | 5 => some ⟨.signed, 32, x⟩
      | 6 => some ⟨.signed, 32, x + 0x8000⟩
      | 14 | 58 => some ⟨.signed, 16, got⟩
      | 16 => some ⟨.signed, 32, got⟩
      | 17 => some ⟨.signed, 32, got + 0x8000⟩
      | 26 => some ⟨.signed, 32, x - p⟩
      | 47 | 63 => some ⟨.signed, 16, x - toc⟩
      | 49 => some ⟨.signed, 32, x - toc⟩
      | 50 => some ⟨.signed, 32, x - toc + 0x8000⟩
      | 56 => some ⟨.signed, 16, x⟩
      | 71 => some ⟨.signed, 32, tp⟩
      | 72 => some ⟨.signed, 32, tp + 0x8000⟩
      | 87 => some ⟨.signed, 16, gotTp⟩
      | 89 => some ⟨.signed, 32, gotTp⟩
      | 90 => some ⟨.signed, 32, gotTp + 0x8000⟩
      | 95 => some ⟨.signed, 16, tp⟩
      | 249 => some ⟨.signed, 16, x - p⟩
      | 251 => some ⟨.signed, 32, x - p⟩
      | 252 => some ⟨.signed, 32, x - p + 0x8000⟩
      | _ => none

/-- The field a relocation of SystemZ is cut to. -/
def systemzField (env : Env) (state : LinkState) (site : Site) : Option FieldCheck :=
  let x := site.s + site.a
  let pc := x - site.p
  let slot := slotOf state (tpOff env site.s)
  match site.rel.typ with
  | 1 => some ⟨.either, 8, x⟩
  | 2 => some ⟨.unsigned, 12, x⟩
  | 3 => some ⟨.either, 16, x⟩
  | 4 => some ⟨.either, 32, x⟩
  | 5 | 8 => some ⟨.signed, 32, pc⟩
  | 16 => some ⟨.signed, 16, pc⟩
  | 17 | 18 => some ⟨.signed, 17, pc⟩
  | 19 | 20 => some ⟨.signed, 33, pc⟩
  | 43 => some ⟨.either, 32, slot - env.gotBase + site.a⟩
  | 47 => some ⟨.either, 32, slot + site.a⟩
  | 49 => some ⟨.signed, 33, slot + site.a - site.p⟩
  | 50 => some ⟨.either, 32, tpOff env site.s + site.a⟩
  | _ => none

/-- The field a relocation is cut to, if its psABI says that it must fit. -/
def fieldOf (env : Env) (state : LinkState) (site : Site) : Option FieldCheck :=
  match env.machine with
  | 62 => x86_64Field env state site
  | 3 => i386Field env state site
  | 183 => aarch64Field env state site
  | 40 => armField env state site
  | 8 => mipsField env state site
  | 243 => riscvField env state site
  | 20 | 21 => powerpcField env state site
  | 22 => systemzField env state site
  | _ => none

/-- Whether what a relocation stores fits in its field. -/
def fieldFits (env : Env) (state : LinkState) (site : Site) : Bool :=
  match fieldOf env state site with
  | some check => fits check.kind check.bits (wordValue env check.value)
  | none => true

/-- The word of the instruction whose low halfword is at the place, as `ppcInsnOfHalf` reads it. -/
def ppcInsnAt (env : Env) (state : LinkState) (site : Site) : Nat :=
  if env.little then readNat state.memory env.codeLittle site.off 4
  else if site.off < 2 then 0
  else readNat state.memory false (site.off - 2) 4

/-- What a relocation that drops the low bits of its value needs of them: their number as an alignment, and the value. An
instruction has no place for them, so that the link would go to, or load from, somewhere else. Entries with `lld` are `checkAlignment`
in `lld/ELF/Arch/*.cpp` of LLVM 23.1.4, read against it. Those with `stored` are the ones where lld stores what it can and says nothing,
or that it does not link, and the bits are lost all the same. -/
def alignCheck (env : Env) (state : LinkState) (site : Site) : Option (Nat × Int) :=
  let x := site.s + site.a
  let p := site.p
  let tp := tpOff env site.s + site.a
  let toc := env.gotBase + 0x8000
  let ds (value : Int) : Option (Nat × Int) :=
    some (if ppcIsDq (ppcInsnAt env state site) then 16 else 4, value)
  match env.machine, site.rel.typ with
  -- lld: `LD_PREL_LO19`, `CONDBR19`, `GOT_LD_PREL19`; stored: `TSTBR14`, `JUMP26`, `CALL26`, `TLSIE_LD_GOTTPREL_PREL19`
  | 183, 0x111 | 183, 0x117 | 183, 0x118 | 183, 0x11a | 183, 0x11b => some (4, x - p)
  | 183, 0x135 => some (4, slotOf state x - p)
  | 183, 0x21f => some (4, slotOf state tp - p)
  -- lld: `LDST16`, `LDST32`, `LDST64`, `LDST128` of an offset that is the low bits of an address, `LD64_GOT_LO12_NC`,
  -- `TLSIE_LD64_GOTTPREL_LO12_NC`, and the `_NC` of `TLSLE_LDST*_TPREL_LO12`; stored: the checked ones of those
  | 183, 0x11c => some (2, x)
  | 183, 0x11d => some (4, x)
  | 183, 0x11e => some (8, x)
  | 183, 0x12b => some (16, x)
  | 183, 0x138 => some (8, slotOf state x)
  | 183, 0x21e => some (8, slotOf state tp)
  | 183, 0x22a | 183, 0x22b => some (2, tp)
  | 183, 0x22c | 183, 0x22d => some (4, tp)
  | 183, 0x22e | 183, 0x22f => some (8, tp)
  | 183, 0x23a | 183, 0x23b => some (16, tp)
  -- stored: the branches of ARM drop two bits, or one for a Thumb target. lld has no check of these, and none of the ones
  -- it has (`THM_PC8`) is linked here
  | 40, 1 | 40, 0x1c | 40, 0x1d =>
    let value := armS site + addendOf site (armBranchImm (readNat state.memory env.little site.off 4)) - p
    some (if site.rel.typ == 0x1c && isThumb site.sym then 2 else 4, value)
  | 40, 0xa | 40, 0x1e =>
    match armField env state site with
    | some check =>
      let hw2 := readNat state.memory env.little (site.off + 2) 2
      let blx := site.rel.typ == 0xa && (if isFunctionSym site.sym then !isThumb site.sym else field hw2 12 1 == 0)
      some (if blx then 4 else 2, check.value)
    | none => none
  | 40, 0x33 | 40, 0x66 | 40, 0x67 =>
    (armField env state site).map fun check => (2, check.value)
  -- lld: `BRANCH`, `JAL`, `RVC_BRANCH`, `RVC_JUMP`
  | 243, 16 | 243, 17 | 243, 44 | 243, 45 => some (2, x - p)
  -- lld: `R_MIPS_PC16`, whose value is in words; stored: `R_MIPS_26`
  | 8, 4 => some (4, mips26Target site (readNat state.memory env.little site.off 4))
  | 8, 10 =>
    let insn := readNat state.memory env.little site.off 4
    some (4, site.s + addendOf site (sext ((insn &&& 0xffff) <<< 2 : Nat) 18) - p)
  -- lld: `REL24`, `PLTREL24`, `REL14`, `R_PPC_ADDR24`, `R_PPC64_ADDR14`; stored: `R_PPC64_ADDR24`, `R_PPC_ADDR14`
  | 20, 10 | 21, 10 | 20, 18 | 21, 18 | 20, 11 | 21, 11 => some (4, x - p)
  | 20, 2 | 21, 2 | 20, 7 | 21, 7 => some (4, x)
  -- lld: the `DS` forms, 16 when the instruction at the place is `DQ`, which has four low bits
  | 21, 56 | 21, 57 => ds x
  | 21, 58 | 21, 59 => ds (slotOf state x - toc)
  | 21, 63 | 21, 64 => ds (x - toc)
  | 21, 87 | 21, 88 => ds (slotOf state tp - toc)
  | 21, 95 | 21, 96 => ds tp
  -- lld: the `DBL` ones of SystemZ, whose value is in halfwords, and `R_390_TLS_IEENT`
  | 22, 17 | 22, 18 | 22, 19 | 22, 20 => some (2, x - p)
  | 22, 49 => some (2, slotOf state (tpOff env site.s) + site.a - p)
  | _, _ => none

/-- Whether what a relocation stores keeps its low bits. -/
def aligned (env : Env) (state : LinkState) (site : Site) : Bool :=
  match alignCheck env state site with
  | some (alignment, value) => value % (alignment : Int) == 0
  | none => true

/-- Whether a relocation stores what it says. -/
def fieldOk (env : Env) (state : LinkState) (site : Site) : Bool :=
  fieldFits env state site && aligned env state site

/-- What a relocation that doesn't store what it says has against it. -/
def fieldProblem (env : Env) (state : LinkState) (site : Site) : String :=
  if fieldFits env state site then
    s!"relocation of type {site.rel.typ} at {site.p} needs a value aligned to {((alignCheck env state site).map (·.1)).getD 1}"
  else s!"relocation of type {site.rel.typ} at {site.p} is out of range of its field"

/-- Warns if a relocation has to cut its value to its field, or lose its low bits. -/
def checkField (env : Env) (site : Site) : LinkM Unit := do
  let state ← get
  if !fieldOk env state site then
    warn (fieldProblem env state site)

/-- Runs a pass, a failed relocation becoming a warning. -/
def guard (action : LinkM Unit) : LinkM Unit :=
  EStateM.tryCatch action warn

def applySite (env : Env) (apply : Site → Outcome) (site : Site) : LinkM Unit := do
  match ← apply site with
  | some writes =>
    checkField env site
    commit site writes
  | none => warn s!"relocation of type {site.rel.typ} (machine {env.machine}) at {site.p} was not applied"

/-- A relocation in the first pass: tells about the ones that won't be applied, and what the second pass will need. -/
def prescanOne (tables : Tables) (rel : Rel) : LinkM Unit :=
  guard do
    if let some site ← siteOf tables true rel then
      if tables.env.machine == 243 then riscvPrescan tables.env site

/-- A relocation in the second pass. -/
def applyOne (tables : Tables) (apply : Site → Outcome) (rel : Rel) : LinkM Unit :=
  guard do
    if let some site ← siteOf tables false rel then
      applySite tables.env apply site

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
      prescanOne tables rel
    for rel in tables.input.relocations do
      applyOne tables apply rel
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

/-- The segment of the thread-local sections: from the first one to the end of the last one, as aligned as the most
aligned one. -/
def tlsBlock (sections : List Section) (addrs : Array (Option Nat)) : TlsBlock :=
  let tls := sections.zipIdx.filterMap fun (sec, index) =>
    if hasFlag sec.flags shfTls then (addrs[index]?).join.map (sec, ·) else none
  match tls with
  | [] => {}
  | (_, start) :: _ =>
    let stop := tls.foldl (fun stop (sec, addr) => max stop (addr + sec.size)) start
    { start, size := stop - start, align := tls.foldl (fun align (sec, _) => max align sec.align) 1 }

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
  let env : Env := { machine := input.machine, width := input.width, little := input.little
                     codeLittle := input.little || input.machine == 183, gotBase, gotOff := input.data.size
                     tls := tlsBlock input.sections.toList layout.addrs, gp0 := input.gp0 }
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
    warnings := state.warnings.reverse
    applied := state.applied.reverse }

/-! ### Relaxing thread-local accesses

An image has one module, whose thread-local block the local-exec model reaches without a loader, so what the general-dynamic,
local-dynamic and TLSDESC models ask a loader for is known at link time. These rewrite the instructions the way `ld.lld` does for
an executable and go through the relocations of local-exec. On machines where `ld.lld` doesn't relax, ARM among them, what needs
a loader stays and warns. -/

/-- Stores bytes at an offset. -/
def writeBytes (memory : ByteArray) (off : Nat) (bytes : List Nat) : ByteArray :=
  bytes.zipIdx.foldl (init := memory) fun memory (byte, index) => memory.set! (off + index) (UInt8.ofNat byte)

/-- The byte at an offset, or zero past the end of a malformed file. -/
def peek (memory : ByteArray) (off : Nat) : Nat := if off < memory.size then (memory.get! off).toNat else 0

/-- Whether bytes are at an offset. -/
def hasBytes (memory : ByteArray) (off : Nat) (bytes : List Nat) : Bool :=
  bytes.zipIdx.all fun (byte, index) => peek memory (off + index) == byte

/-- What relaxing a relocation does: the bytes it rewrites, what it becomes, and if it takes the relocation that follows with it. -/
structure Relaxed where
  patches : List (Nat × List Nat) := []
  rels : List Rel := []
  skip : Bool := false

/-- `mov %fs:0,%rax; lea x@tpoff(%rax),%rax`, for `.byte 0x66; leaq x@tlsgd(%rip),%rdi; .word 0x6666; rex64; call __tls_get_addr`. -/
def x86_64GdInsns : List Nat := [0x64, 0x48, 0x8b, 0x04, 0x25, 0, 0, 0, 0, 0x48, 0x8d, 0x80, 0, 0, 0, 0]

/-- `.word 0x6666; .byte 0x66; mov %fs:0,%rax`, for `leaq x@tlsld(%rip),%rdi; call __tls_get_addr`. -/
def x86_64LdInsns : List Nat := [0x66, 0x66, 0x66, 0x64, 0x48, 0x8b, 0x04, 0x25, 0, 0, 0, 0]

/-- The same for `call *__tls_get_addr@GOTPCREL(%rip)`. -/
def x86_64LdIndirectInsns : List Nat := [0x66, 0x66, 0x66, 0x66, 0x64, 0x48, 0x8b, 0x04, 0x25, 0, 0, 0, 0]

/-- `movl %gs:0,%eax; subl $x@ntpoff,%eax`, for `leal x@tlsgd(%ebx),%eax; call ___tls_get_addr`. -/
def i386GdInsns : List Nat := [0x65, 0xa1, 0, 0, 0, 0, 0x81, 0xe8, 0, 0, 0, 0]

/-- `movl %gs:0,%eax; nop; leal 0(%esi,1),%esi`, for `leal x@tlsldm(%ebx),%eax; call ___tls_get_addr`. -/
def i386LdInsns : List Nat := [0x65, 0xa1, 0, 0, 0, 0, 0x90, 0x8d, 0x74, 0x26, 0x00]

/-- The two-byte `nop` that replaces a call through a TLS descriptor. -/
def x86Nop : List Nat := [0x66, 0x90]

def wordBytes (word : Nat) : List Nat := (List.range 4).map fun i => (word >>> (8 * i)) % 256

/-- `movz x0, #:tprel_g1:x`, `movk x0, #:tprel_g0_nc:x`, and the `nop` that replaces the rest of a TLSDESC sequence of AArch64. -/
def aarch64Movz : Nat := 0xd2a00000
def aarch64Movk : Nat := 0xf2800000
def aarch64Nop : Nat := 0xd503201f

/-- A relocation that goes through local-exec at another offset, with another type. -/
def relocated (rel : Rel) (offset typ : Nat) (addend : Int) : Rel := { rel with offset, typ, addend, isExplicit := true }

def relaxX86_64 (data : ByteArray) (sec : Section) (rel : Rel) (next : Option Rel) : Option Relaxed :=
  let loc := sec.off + rel.offset
  let inSec (off n : Nat) : Bool := sec.off ≤ off && off + n ≤ sec.off + sec.size
  let follows (at' : Nat) (typs : List Nat) : Bool := match next with
    | some call => call.target == rel.target && call.offset == rel.offset + at' && typs.contains call.typ
    | none => false
  match rel.typ with
  | 19 =>
    if 4 ≤ loc && inSec (loc - 4) 16 && hasBytes data (loc - 4) [0x66, 0x48, 0x8d, 0x3d] &&
        follows 8 [2, 4, 9, 41, 42] then
      some { patches := [(loc - 4, x86_64GdInsns)], rels := [relocated rel (rel.offset + 8) 23 (rel.addend + 4)], skip := true }
    else none
  | 20 =>
    if 3 ≤ loc && hasBytes data (loc - 3) [0x48, 0x8d, 0x3d] then
      if follows 5 [2, 4] && inSec (loc - 3) 12 then
        some { patches := [(loc - 3, x86_64LdInsns)], skip := true }
      else if follows 6 [9, 41, 42] && inSec (loc - 3) 13 then
        some { patches := [(loc - 3, x86_64LdIndirectInsns)], skip := true }
      else none
    else none
  | 17 => some { rels := [{ rel with typ := 18 }] }
  | 21 => some { rels := [{ rel with typ := 23 }] }
  | 34 =>
    let rex := peek data (loc - 3)
    let modrm := peek data (loc - 1)
    if 3 ≤ loc && inSec (loc - 3) 7 && (rex == 0x48 || rex == 0x4c) && peek data (loc - 2) == 0x8d && modrm % 8 == 5 &&
        modrm >>> 6 == 0 then
      some { patches := [(loc - 3, [0x48 + (rex >>> 2) % 2, 0xc7, 0xc0 + (modrm >>> 3) % 8])],
             rels := [relocated rel rel.offset 23 (rel.addend + 4)] }
    else none
  | 35 => if inSec loc 2 then some { patches := [(loc, x86Nop)] } else none
  | _ => none

def relaxI386 (data : ByteArray) (sec : Section) (rel : Rel) (next : Option Rel) : Option Relaxed :=
  let loc := sec.off + rel.offset
  let inSec (off n : Nat) : Bool := sec.off ≤ off && off + n ≤ sec.off + sec.size
  let calls := match next with
    | some call => call.target == rel.target && [2, 4, 43].contains call.typ
    | none => false
  match rel.typ with
  | 18 =>
    let start := if peek data (loc - 2) == 0x04 then loc - 3 else loc - 2
    if 3 ≤ loc && calls && inSec start 12 && start ≥ sec.off && loc + 4 ≤ data.size then
      let inPlace : Int := if rel.isExplicit then rel.addend else sext (readNat data true loc 4) 32
      some { patches := [(start, i386GdInsns)], rels := [relocated rel (start + 8 - sec.off) 34 (-inPlace)], skip := true }
    else none
  | 19 =>
    if 2 ≤ loc && calls && inSec (loc - 2) 11 then some { patches := [(loc - 2, i386LdInsns)], skip := true } else none
  | 32 => some { rels := [{ rel with typ := 17 }] }
  | 39 =>
    if 2 ≤ loc && inSec (loc - 2) 6 && peek data (loc - 2) == 0x8d then
      some { patches := [(loc - 1, [0x05 + (peek data (loc - 1) &&& 0x38)])], rels := [{ rel with typ := 17 }] }
    else none
  | 40 => if inSec loc 2 then some { patches := [(loc, x86Nop)] } else none
  | _ => none

def relaxAArch64 (sec : Section) (rel : Rel) : Option Relaxed :=
  let loc := sec.off + rel.offset
  if loc + 4 ≤ sec.off + sec.size then
    match rel.typ with
    | 0x232 => some { patches := [(loc, wordBytes aarch64Movz)], rels := [{ rel with typ := 0x222 }] }
    | 0x233 => some { patches := [(loc, wordBytes aarch64Movk)], rels := [{ rel with typ := 0x224 }] }
    | 0x234 | 0x239 => some { patches := [(loc, wordBytes aarch64Nop)] }
    | _ => none
  else none

/-- What relaxing a relocation does on a machine, if anything. -/
def relaxOne (input : Input) (data : ByteArray) (rel : Rel) (next : Option Rel) : Option Relaxed :=
  match input.sections[rel.target]? with
  | none => none
  | some sec =>
    match input.machine with
    | 62 => relaxX86_64 data sec rel next
    | 3 => relaxI386 data sec rel next
    | 183 => relaxAArch64 sec rel
    | _ => none

/-- The state of the pass: the bytes, the relocations in reverse, and whether a call has to go. -/
structure RelaxState where
  data : ByteArray
  rels : List Rel := []
  skip : Bool := false

def relaxStep (input : Input) (state : RelaxState) (entry : Rel × Option Rel) : RelaxState :=
  if state.skip then { state with skip := false }
  else match relaxOne input state.data entry.1 entry.2 with
    | some relaxed =>
      { data := relaxed.patches.foldl (fun data patch => writeBytes data patch.1 patch.2) state.data
        rels := relaxed.rels.reverse ++ state.rels
        skip := relaxed.skip }
    | none => { state with rels := entry.1 :: state.rels }

/-- A file with its thread-local accesses relaxed to local-exec. -/
def relaxTls (input : Input) : Input :=
  let nexts := input.relocations.tail.map some ++ [none]
  let done := (input.relocations.zip nexts).foldl (relaxStep input) { data := input.data }
  { input with data := done.data, relocations := done.rels.reverse }

/-! ### Range-extension thunks

A branch whose target is out of its range goes to a thunk in a section of its own at the end of the sections, which goes to the
target whatever its address. The thunk of a branch that changes the instruction set is the veneer that `ld.lld` adds, since its
`BX` also changes the state, as a jump can't by itself. The thunks are ordinary code with ordinary relocations against the symbol
of the branch, and each branch only gets a new symbol, so all there is to know of a link holds of a link with thunks. -/

/-- A word as bytes, in a byte order. -/
def bytesOf (little : Bool) (n value : Nat) : List Nat :=
  (List.range n).map fun i => (value >>> (8 * if little then i else n - i - 1)) % 256

/-- `ldr x16, #8; br x16; .quad target`, always little-endian for its instructions. -/
def aarch64Thunk : List Nat := bytesOf true 4 0x58000050 ++ bytesOf true 4 0xd61f0200 ++ List.replicate 8 0

/-- `ldr pc, [pc, #-4]; .word target`. The word has the Thumb bit of the target, which makes it interwork. -/
def armThunk (little : Bool) : List Nat := bytesOf little 4 0xe51ff004 ++ List.replicate 4 0

/-- `movw ip, #lo; movt ip, #hi; bx ip; nop`. The address has the Thumb bit of the target, which makes it interwork. -/
def thumbThunk (little : Bool) : List Nat :=
  [0xf240, 0x0c00, 0xf2c0, 0x0c00, 0x4760, 0xbf00].flatMap (bytesOf little 2)

/-- What a branch needs of a thunk. -/
structure ThunkKind where
  /-- The instruction set of the thunk, that of the branch. -/
  thumb : Bool
  /-- What the branch has in its addend for the pipeline. -/
  bias : Int
  /-- The bits of the offset of the branch. -/
  bits : Nat

/-- The branches with a thunk: `R_AARCH64_JUMP26` and `CALL26`, and `R_ARM_PC24`, `CALL`, `JUMP24`, `THM_CALL`, `THM_JUMP24` and
`THM_JUMP19`. -/
def thunkKind (machine typ : Nat) : Option ThunkKind :=
  match machine, typ with
  | 183, 0x11a | 183, 0x11b => some ⟨false, 0, 28⟩
  | 40, 1 | 40, 0x1c | 40, 0x1d => some ⟨false, -8, 26⟩
  | 40, 0xa | 40, 0x1e => some ⟨true, -4, 25⟩
  | 40, 0x33 => some ⟨true, -4, 21⟩
  | _, _ => none

/-- Whether the target of a branch is Thumb code, as far as its symbol or its instruction tell, which an ARM branch reads from
its `BLX` and a Thumb one from its `BL`. -/
def targetIsThumb (memory : ByteArray) (little : Bool) (site : Site) (kind : ThunkKind) : Bool :=
  if isFunctionSym site.sym then isThumb site.sym
  else if kind.thumb then
    site.rel.typ != 0xa || field (readNat memory little (site.off + 2) 2) 12 1 == 1
  else site.rel.typ == 0x1c && field (readNat memory little site.off 4) 28 4 == 0xf

/-- The branch can't do it by itself: a jump that changes the instruction set, or a target out of its range. -/
def needsThunk (env : Env) (state : LinkState) (site : Site) (kind : ThunkKind) : Bool :=
  let interworks := env.machine == emArm && site.rel.typ != 0x1c && site.rel.typ != 0xa &&
    targetIsThumb state.memory env.little site kind != kind.thumb
  interworks || !fieldFits env state site

/-- The thunks so far, by the symbol, the target's addend and the instruction set of the branch. -/
structure ThunkState where
  /-- Where the thunks start. -/
  base : Nat
  /-- The first of the new symbols. -/
  symbols : Nat
  known : List ((Nat × Int × Bool) × Nat) := []
  bytes : List Nat := []
  newSyms : List Sym := []
  newRels : List Rel := []
  rels : List Rel := []

def thunkSize (kind : ThunkKind) (machine : Nat) : Nat :=
  if machine == emArm then (if kind.thumb then 12 else 8) else 16

/-- A thunk's code, and its relocations against the target. -/
def thunkCode (machine : Nat) (little : Bool) (kind : ThunkKind) (secIndex offset symbol : Nat) (addend : Int) : List Nat × List Rel :=
  let rel (at' typ : Nat) : Rel := ⟨secIndex, offset + at', typ, symbol, addend, true⟩
  if machine == emArm then
    if kind.thumb then (thumbThunk little, [rel 0 0x2f, rel 4 0x30])
    else (armThunk little, [rel 4 2])
  else (aarch64Thunk, [rel 8 0x101])

/-- What a thunk goes to from its symbol: the branch's target, without its pipeline, and with the bit of its instruction set. -/
def thunkTargetAddend (tables : Tables) (data : ByteArray) (site : Site) (kind : ThunkKind) : Int :=
  let decoded : Int :=
    if tables.input.machine == emArm then
      if kind.thumb then
        let hw1 := readNat data tables.env.little site.off 2
        let hw2 := readNat data tables.env.little (site.off + 2) 2
        addendOf site (if site.rel.typ == 0x33 then thumbJump19Imm hw1 hw2 else thumbBranchImm hw1 hw2)
      else addendOf site (armBranchImm (readNat data tables.env.little site.off 4))
    else site.a
  let wantThumb := tables.input.machine == emArm && targetIsThumb data tables.env.little site kind
  decoded - kind.bias + (if wantThumb && !isThumb site.sym then 1 else 0)

/-- Where the thunk of a key is, or will be. -/
def thunkOffset (state : ThunkState) (key : Nat × Int × Bool) : Nat :=
  ((state.known.find? (·.1 == key)).map (·.2)).getD state.bytes.length

def thunkIsNew (state : ThunkState) (key : Nat × Int × Bool) : Bool := (state.known.find? (·.1 == key)).isNone

/-- Sends a branch to its thunk, if it has to and the thunk is in its range. -/
def thunkStep (tables : Tables) (data : ByteArray) (secIndex : Nat) (state : ThunkState) (rel : Rel) : ThunkState :=
  let keep := { state with rels := rel :: state.rels }
  match thunkKind tables.input.machine rel.typ with
  | none => keep
  | some kind =>
    let linkState : LinkState := { memory := data }
    match siteOf tables false rel linkState with
    | .ok (some site) _ =>
      if needsThunk tables.env linkState site kind && site.off + 4 ≤ data.size then
        let targetAddend := thunkTargetAddend tables data site kind
        let key := (rel.symbol, targetAddend, kind.thumb)
        let offset := thunkOffset state key
        let reached := (state.base + offset : Int) + kind.bias - site.p
        if fits .signed kind.bits reached then
          let symbolIndex := state.symbols + offset / 4
          let branch : Rel := { rel with symbol := symbolIndex, addend := kind.bias, isExplicit := true }
          if thunkIsNew state key then
            let (code, thunkRels) := thunkCode tables.input.machine tables.env.little kind secIndex offset rel.symbol targetAddend
            let padded := code
            let value := offset + if kind.thumb then 1 else 0
            let sym : Sym := ⟨s!"__thunk_{site.sym.name}_{offset}", secIndex, false, value, padded.length, sttFunc, stbLocal, 0⟩
            -- a symbol for every word of the secIndex, so that the index of one is known from its offset
            let fillers := (List.range (padded.length / 4 - 1)).map fun _ => nullSym
            { state with
              known := (key, offset) :: state.known
              bytes := state.bytes ++ padded
              newSyms := state.newSyms ++ sym :: fillers
              newRels := state.newRels ++ thunkRels
              rels := branch :: state.rels }
          else { state with rels := branch :: state.rels }
        else keep
      else keep
    | _ => keep

/-- The tables of a layout, as `link` makes them. -/
def layoutTables (input : Input) : Tables :=
  let word := input.width / 8
  let layout := layoutSections input.sections.toList input.base
  let symbols := input.symbols.toList
  let (commons, commonsEnd) := placeCommons symbols (alignUp layout.cursor word)
  let (externals, externalsEnd) := placeExternals input.machine word symbols (alignUp commonsEnd word)
  let env : Env := { machine := input.machine, width := input.width, little := input.little
                     codeLittle := input.little || input.machine == 183, gotBase := alignUp externalsEnd word
                     gotOff := input.data.size, tls := tlsBlock input.sections.toList layout.addrs, gp0 := input.gp0 }
  ⟨input, env, layout.addrs, commons, externals⟩

/-- A file with `size` bytes more of executable section after the section `at'`, whose number the sections after it move up for. -/
def withThunkSection (input : Input) (at' size : Nat) : Input :=
  let up (index : Nat) : Nat := if index > at' then index + 1 else index
  let thunks : Section := ⟨".thunks", 1, shfAlloc + shfExecinstr, input.data.size, size, 16⟩
  let sections := input.sections.toList
  { input with
    sections := (sections.take (at' + 1) ++ thunks :: sections.drop (at' + 1)).toArray
    symbols := input.symbols.map fun sym =>
      if sym.extended || sym.shndx < shnLoreserve then { sym with shndx := up sym.shndx } else sym
    relocations := input.relocations.map fun rel => { rel with target := up rel.target }
    thunksAt := some (at' + 1) }

/-- What the thunks of a file with a section of `reserved` bytes for them come to. -/
def thunkPass (input : Input) (at' reserved : Nat) : ThunkState :=
  let laid := withThunkSection input at' reserved
  let tables := layoutTables laid
  let base := ((tables.addrs[at' + 1]?).join).getD 0
  laid.relocations.foldl (thunkStep tables laid.data (at' + 1)) { base, symbols := laid.symbols.size }

/-- The first branch that needs a thunk, which the thunks go after the section of. -/
def firstThunked (input : Input) : Option Nat :=
  let tables := layoutTables input
  let linkState : LinkState := { memory := input.data }
  (input.relocations.find? fun rel =>
    match thunkKind input.machine rel.typ, siteOf tables false rel linkState with
    | some kind, .ok (some site) _ => needsThunk tables.env linkState site kind
    | _, _ => false).map (·.target)

/-- Adds a section of thunks to a file for the branches that need them, right after the section of the first of them. The section
is as big as it takes for what the layout says, and the layout is the one with it, so a second round settles what the first one
left out of the space it reserved. A file without any stays as it is. -/
def addThunks (input : Input) : Input :=
  match firstThunked input with
  | none => input
  | some at' =>
    let first := thunkPass input at' (input.relocations.length * 16)
    let second := thunkPass input at' first.bytes.length
    let (reserved, done) := if second.bytes.length ≤ first.bytes.length then (first.bytes.length, second)
      else (input.relocations.length * 16, first)
    if done.bytes.isEmpty then input
    else
      let laid := withThunkSection input at' reserved
      let padded := done.bytes ++ List.replicate (reserved - done.bytes.length) 0
      { laid with
        data := input.data ++ ByteArray.mk (padded.map UInt8.ofNat).toArray
        symbols := laid.symbols ++ done.newSyms.toArray
        relocations := done.rels.reverse ++ done.newRels }

/-- What a file goes through before it is linked. -/
def prepare (input : Input) : Input := addThunks (relaxTls input)

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
