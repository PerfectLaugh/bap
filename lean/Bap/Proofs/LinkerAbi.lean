import Bap.Proofs.Linker

/-!
The calculation columns of the psABIs, as functions: what each relocation of each machine stores, given the bytes of its place,
the address of the GOT entry of a value, and the values of the AUIPC instructions. A handler stores what these say.
-/

namespace Bap.Proofs.Linker

open Bap.Image Bap.Image.ElfLinker Bap.Proofs.Image Bap.Proofs.Image.LinkerLaws

/-! ### A weakest precondition of the linker's monad -/

/-- What holds of an action's result, if it has one. -/
def wp (m : LinkM α) (Q : α → LinkState → Prop) (st : LinkState) : Prop :=
  match m st with
  | .ok a after => Q a after
  | .error _ _ => True

theorem wp_bind (m : LinkM α) (f : α → LinkM β) (Q : β → LinkState → Prop) (st : LinkState) :
    wp (m >>= f) Q st = wp m (fun a s => wp (f a) Q s) st := by
  simp only [wp, bind, EStateM.bind]
  cases m st <;> rfl

theorem wp_pure (a : α) (Q : α → LinkState → Prop) (st : LinkState) : wp (pure a : LinkM α) Q st = Q a st := rfl

theorem wp_ite {c : Prop} [Decidable c] (a b : LinkM α) (Q : α → LinkState → Prop) (st : LinkState) :
    wp (if c then a else b) Q st = if c then wp a Q st else wp b Q st := by
  split <;> rfl

theorem wp_throw (e : String) (Q : α → LinkState → Prop) (st : LinkState) : wp (throw e : LinkM α) Q st = True := rfl

theorem wp_get (Q : LinkState → LinkState → Prop) (st : LinkState) : wp (get : LinkM LinkState) Q st = Q st st := rfl

theorem wp_getS (Q : LinkState → LinkState → Prop) (st : LinkState) : wp (MonadState.get : LinkM LinkState) Q st = Q st st := rfl

theorem wp_load (site : Site) (at' n : Nat) (little : Bool) (Q : Nat → LinkState → Prop) (st : LinkState) :
    wp (load site at' n little) Q st =
      (inSection site at' n st.memory.size = true → Q (readNat st.memory little (site.off + at') n) st) := by
  by_cases h : inSection site at' n st.memory.size = true
  · simp only [h, true_implies]
    simp only [wp, ElfLinker.load, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, h, ite_true]
    rfl
  · have h' : inSection site at' n st.memory.size = false := by simpa using h
    simp only [h', Bool.false_eq_true, false_implies, eq_iff_iff, iff_true]
    simp only [wp, ElfLinker.load, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, h', Bool.false_eq_true,
      ite_false]
    trivial

theorem wp_ld (env : Env) (site : Site) (at' n : Nat) (Q : Nat → LinkState → Prop) (st : LinkState) :
    wp (ld env site at' n) Q st =
      (inSection site at' n st.memory.size = true → Q (readNat st.memory env.little (site.off + at') n) st) := wp_load ..

theorem wp_ldi (env : Env) (site : Site) (at' n : Nat) (Q : Nat → LinkState → Prop) (st : LinkState) :
    wp (ldi env site at' n) Q st =
      (inSection site at' n st.memory.size = true → Q (readNat st.memory env.codeLittle (site.off + at') n) st) := wp_load ..

theorem wp_ldInt (env : Env) (site : Site) (at' n : Nat) (Q : Int → LinkState → Prop) (st : LinkState) :
    wp (ldInt env site at' n) Q st =
      (inSection site at' n st.memory.size = true → Q (readNat st.memory env.little (site.off + at') n) st) := by
  unfold ldInt
  rw [wp_bind, wp_ld]
  rfl

theorem wp_done (writes : List Write) (Q : Option (List Write) → LinkState → Prop) (st : LinkState) :
    wp (done writes) Q st = Q (some writes) st := rfl

/-- Whatever an action does, what holds of everything holds of its result. -/
theorem wp_any {m : LinkM α} {Q : α → LinkState → Prop} {st : LinkState} (h : ∀ a s, Q a s) : wp m Q st := by
  unfold wp
  split
  · exact h _ _
  · trivial

theorem wp_insn (env : Env) (site : Site) (Q : Nat → LinkState → Prop) (st : LinkState) :
    wp (ppcInsnOfHalf env site) Q st =
      if env.little then
        (inSection site 0 4 st.memory.size = true → Q (readNat st.memory env.codeLittle (site.off + 0) 4) st)
      else if site.off < 2 then True
      else (inSection { site with off := site.off - 2 } 0 4 st.memory.size = true →
        Q (readNat st.memory false (site.off - 2 + 0) 4) st) := by
  simp only [ppcInsnOfHalf, wp_ite, wp_ldi, wp_throw, wp_load]

/-! ### The GOT -/

/-- The address of the entry of a value. -/
def gotVal (env : Env) (value : Int) (st : LinkState) : Int :=
  match gotEntry env value st with
  | .ok a _ => a
  | .error _ _ => 0

/-- The state after asking for an entry. -/
def gotAfter (env : Env) (value : Int) (st : LinkState) : LinkState := stateOf (gotEntry env value st)

theorem gotEntry_run (env : Env) (value : Int) (st : LinkState) :
    gotEntry env value st = .ok (gotVal env value st) (gotAfter env value st) := by
  obtain ⟨_, _, h, _, _⟩ := gotEntry_ok env value st
  simp [gotVal, gotAfter, stateOf, h]

theorem wp_got (env : Env) (value : Int) (Q : Int → LinkState → Prop) (st : LinkState) :
    wp (gotEntry env value) Q st = Q (gotVal env value st) (gotAfter env value st) := by
  simp only [wp, gotEntry_run]

/-- A value has its entry after asking for it. -/
theorem slotOf_gotAfter (env : Env) (value : Int) (st : LinkState) :
    slotOf (gotAfter env value st) value = gotVal env value st := by
  simp only [gotVal, gotAfter, stateOf, gotEntry, slotOf, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
  cases hc : st.got[field value 0 64]? with
  | some slot => simp only [pure, EStateM.pure]; simp [hc]
  | none => simp [set, MonadStateOf.set, EStateM.set, EStateM.bind, pure, EStateM.pure]

theorem got_frame (env : Env) (value : Int) (st : LinkState) :
    st.memory.size ≤ (gotAfter env value st).memory.size ∧ ∀ o, o < st.memory.size → o < env.gotOff →
      (gotAfter env value st).memory.get! o = st.memory.get! o := by
  have hf := frame_gotEntry (P := fun o => env.gotOff ≤ o) (S := fun _ => True) (env := env) (fun _ h => h) value st
    (fun _ _ => trivial)
  exact ⟨hf.2.1, fun o ho hg => hf.2.2 o ho (by omega)⟩

theorem get!_outside {memory : ByteArray} {o : Nat} (h : memory.size ≤ o) : memory.get! o = default := by
  show memory.data[o]! = default
  rw [getElem!_neg memory.data o (by show ¬ o < memory.data.size; exact Nat.not_lt.mpr h)]

/-- The file's bytes don't change for the GOT. -/
theorem readNat_gotAfter {env : Env} (little : Bool) (value : Int) (st : LinkState) {off n : Nat}
    (hsize : env.gotOff ≤ st.memory.size) (h : off + n ≤ env.gotOff) :
    readNat (gotAfter env value st).memory little off n = readNat st.memory little off n := by
  obtain ⟨_, hk⟩ := got_frame env value st
  exact readNat_congr fun i hi => hk _ (by omega) (by omega)

/-! ### Reading a place -/

/-- What a relocation can read of the memory: the bytes of its place, in its section. Anything else reads as zero, so that two
memories with the same bytes there read the same. -/
def cut (lo hi limit : Nat) (rd : Bool → Nat → Nat → Nat) : Bool → Nat → Nat → Nat := fun little o n =>
  if lo ≤ o ∧ o + n ≤ hi ∧ o + n ≤ limit then rd little o n else 0

theorem cut_read {lo hi limit : Nat} {rd : Bool → Nat → Nat → Nat} (little : Bool) (o n : Nat) (h1 : lo ≤ o) (h2 : o + n ≤ hi)
    (h3 : o + n ≤ limit) : cut lo hi limit rd little o n = rd little o n := by
  rw [cut, ite_eq_left ⟨h1, h2, h3⟩]

/-! ### The tables -/

/-- x86-64. `Z` is the size of the symbol, and the TLS relocations go through the thread pointer. -/
def x86_64Spec (env : Env) (site : Site) (slot : Int → Int) : Option (List Write) :=
  let s := site.s
  let a := site.a
  let p := site.p
  let got : Int := env.gotBase
  let st n value := some [stAt env site 0 n value]
  match site.rel.typ with
  | 0 => some []
  | 1 => st 8 (s + a)
  | 2 | 4 => st 4 (s + a - p)
  | 18 => st 8 (tpOff env s + a)
  | 22 | 44 | 50 => st 4 (slot (tpOff env s) + a - p)
  | 23 => st 4 (tpOff env s + a)
  | 3 => st 4 (slot s - got + a)
  | 9 | 41 | 42 | 43 => st 4 (slot s + a - p)
  | 10 | 11 => st 4 (s + a)
  | 12 => st 2 (s + a)
  | 13 => st 2 (s + a - p)
  | 14 => st 1 (s + a)
  | 15 => st 1 (s + a - p)
  | 24 => st 8 (s + a - p)
  | 25 | 31 => st 8 (s + a - got)
  | 26 => st 4 (got + a - p)
  | 27 | 30 => st 8 (slot s - got + a)
  | 28 => st 8 (slot s + a - p)
  | 29 => st 8 (got + a - p)
  | 32 => st 4 (site.sym.size + a)
  | 33 => st 8 (site.sym.size + a)
  | _ => none

def x86_64Place : Nat → Nat
  | 0 => 0
  | 1 | 18 | 24 | 25 | 27 | 28 | 29 | 30 | 31 | 33 => 8
  | 12 | 13 => 2
  | 14 | 15 => 1
  | _ => 4

def i386Spec (env : Env) (site : Site) (rd : Bool → Nat → Nat → Nat) (slot : Int → Int) : Option (List Write) :=
  let s := site.s
  let p := site.p
  let got : Int := env.gotBase
  let a (n : Nat) : Int := addendOf site (sext (rd env.little (site.off + 0) n) (8 * n))
  let st n value := some [stAt env site 0 n value]
  match site.rel.typ with
  | 0 => some []
  | 1 => st 4 (s + a 4)
  | 2 | 4 => st 4 (s + a 4 - p)
  | 3 | 43 => st 4 (slot s + a 4 - got)
  | 9 => st 4 (s + a 4 - got)
  | 15 => st 4 (slot (tpOff env s) + a 4)
  | 16 => st 4 (slot (tpOff env s) + a 4 - got)
  | 17 => st 4 (tpOff env s + a 4)
  | 33 => st 4 (slot (-tpOff env s) + a 4 - got)
  | 34 => st 4 (-(tpOff env s) + a 4)
  | 10 => st 4 (got + a 4 - p)
  | 20 => st 2 (s + a 2)
  | 21 => st 2 (s + a 2 - p)
  | 22 => st 1 (s + a 1)
  | 23 => st 1 (s + a 1 - p)
  | _ => none

def i386Place : Nat → Nat
  | 0 => 0
  | 20 | 21 => 2
  | 22 | 23 => 1
  | _ => 4

def aarch64Spec (env : Env) (site : Site) (rd : Bool → Nat → Nat → Nat) (slot : Int → Int) : Option (List Write) :=
  let s := site.s
  let a := site.a
  let p := site.p
  let x := s + a
  let tp := tpOff env s + a
  let st n value := some [stAt env site 0 n value]
  let up (f : Nat → Nat) := some [stiAt env site 0 4 (f (rd env.codeLittle (site.off + 0) 4))]
  let adr := aarch64Adr
  let page := aarch64Page
  let typ := site.rel.typ
  match typ with
  | 0 => some []
  | 0x101 => st 8 x
  | 0x102 => st 4 x
  | 0x103 => st 2 x
  | 0x104 => st 8 (x - p)
  | 0x105 | 0x13a => st 4 (x - p)
  | 0x106 => st 2 (x - p)
  | 0x107 | 0x108 | 0x109 | 0x10a | 0x10b | 0x10c | 0x10d => up fun insn => setBits insn 5 16 (x >>> ((typ - 0x107) / 2 * 16))
  | 0x111 | 0x118 => up fun insn => setBits insn 5 19 ((x - p) >>> 2)
  | 0x112 => up (adr (x - p))
  | 0x113 | 0x114 => up (adr ((page x - page p) >>> 12))
  | 0x115 | 0x116 => up (aarch64Lo12 0 x)
  | 0x117 => up fun insn => setBits insn 5 14 ((x - p) >>> 2)
  | 0x11a | 0x11b => up fun insn => setBits insn 0 26 ((x - p) >>> 2)
  | 0x10e => up (aarch64SMov x)
  | 0x10f => up (aarch64SMov (x >>> 16))
  | 0x110 => up (aarch64SMov (x >>> 32))
  | 0x11c => up (aarch64Lo12 1 x)
  | 0x11d => up (aarch64Lo12 2 x)
  | 0x11e => up (aarch64Lo12 3 x)
  | 0x11f | 0x120 => up (aarch64SMov (x - p))
  | 0x121 | 0x122 => up (aarch64SMov ((x - p) >>> 16))
  | 0x123 | 0x124 => up (aarch64SMov ((x - p) >>> 32))
  | 0x125 => up (aarch64SMov ((x - p) >>> 48))
  | 0x12b => up (aarch64Lo12 4 x)
  | 0x135 => up fun insn => setBits insn 5 19 ((slot x - p) >>> 2)
  | 0x137 => up (adr ((page (slot x) - page p) >>> 12))
  | 0x138 => up (aarch64Lo12 3 (slot x))
  | 0x13b => st 4 (slot s + a - p)
  | 0x21d => up (adr ((page (slot tp) - page p) >>> 12))
  | 0x21e => up (aarch64Lo12 3 (slot tp))
  | 0x21f => up fun insn => setBits insn 5 19 ((slot tp - p) >>> 2)
  | 0x220 => up (aarch64SMov (tp >>> 32))
  | 0x221 => up (aarch64SMov (tp >>> 16))
  | 0x222 => up fun insn => setBits insn 5 16 (tp >>> 16)
  | 0x223 => up (aarch64SMov tp)
  | 0x224 => up fun insn => setBits insn 5 16 tp
  | 0x225 => up (aarch64Lo12 0 (tp >>> 12))
  | 0x226 | 0x227 | 0x228 | 0x229 => up (aarch64Lo12 0 tp)
  | 0x22a | 0x22b => up (aarch64Lo12 1 tp)
  | 0x22c | 0x22d => up (aarch64Lo12 2 tp)
  | 0x22e | 0x22f => up (aarch64Lo12 3 tp)
  | 0x23a | 0x23b => up (aarch64Lo12 4 tp)
  | _ => none

def aarch64Place : Nat → Nat
  | 0 => 0
  | 0x101 | 0x104 => 8
  | 0x103 | 0x106 => 2
  | _ => 4

def armSpec (env : Env) (site : Site) (rd : Bool → Nat → Nat → Nat) (slot : Int → Int) : Option (List Write) :=
  let sym := site.sym
  let typ := site.rel.typ
  let p := site.p
  let got : Int := env.gotBase
  let thumb := isThumb sym
  let s : Int := armS site
  let withT := armWithT site
  let addend := addendOf site
  let r (at' n : Nat) : Nat := rd env.little (site.off + at') n
  let a32 : Int := addend (sext (r 0 4) 32)
  let st n value := some [stAt env site 0 n value]
  let movw (kind : Nat) (imm : Nat) : Int :=
    let a := addend (sext imm 16)
    match kind with
    | 0 => withT (s + a)
    | 1 => (s + a) >>> 16
    | 2 => withT (s + a) - p
    | _ => (s + a - p) >>> 16
  let armMovw (kind : Nat) := st 4 (armMovSet (r 0 4) (movw kind (armMovImm (r 0 4))) : Nat)
  let thumbMovw (kind : Nat) :=
    let v := movw kind (thumbMovImm (r 0 2) (r 2 2))
    some [stAt env site 0 2 (thumbMovSet1 (r 0 2) v : Nat), stAt env site 2 2 (thumbMovSet2 (r 2 2) v : Nat)]
  let armBranch :=
    let insn := r 0 4
    let v := s + addend (armBranchImm insn) - p
    if typ == 0x1c && thumb then st 4 (setBits (armBranchSet 0xfa000000 v) 24 1 (v >>> 1) : Nat)
    else if typ == 0x1c && isFunctionSym sym && field insn 28 4 == 0xf then st 4 (armBranchSet 0xeb000000 v : Nat)
    else st 4 (armBranchSet insn v : Nat)
  let thumbBranch :=
    let hw1 := r 0 2
    let hw2 := r 2 2
    let a := addend (thumbBranchImm hw1 hw2)
    let call := typ == 0xa
    let blx := call && (if isFunctionSym sym then !thumb else field hw2 12 1 == 0)
    let v := if blx then s + a - (p - p % 4) else s + a - p
    let hw2 := if !call then hw2 else setBits hw2 12 1 (if blx then 0 else 1)
    some [stAt env site 0 2 (thumbBranchSet1 hw1 v : Nat), stAt env site 2 2 (thumbBranchSet2 hw2 v : Nat)]
  match typ with
  | 0 | 0x28 => some []
  | 1 | 0x1c | 0x1d => armBranch
  | 2 | 0x26 => st 4 (withT (s + a32))
  | 3 => st 4 (withT (s + a32) - p)
  | 5 => st 2 (s + addend (sext (r 0 2) 16))
  | 8 => st 1 (s + addend (sext (r 0 1) 8))
  | 0xa | 0x1e => thumbBranch
  | 0x18 => st 4 (s + a32 - got)
  | 0x19 => st 4 (got + a32 - p)
  | 0x1a => st 4 (slot (withT s) + a32 - got)
  | 0x2a =>
    let old := r 0 4
    st 4 (setBits old 0 31 (withT (s + addend (sext (field old 0 31) 31)) - p) : Nat)
  | 0x2b => armMovw 0
  | 0x2c => armMovw 1
  | 0x2d => armMovw 2
  | 0x2e => armMovw 3
  | 0x2f => thumbMovw 0
  | 0x30 => thumbMovw 1
  | 0x31 => thumbMovw 2
  | 0x32 => thumbMovw 3
  | 0x33 =>
    let hw1 := r 0 2
    let hw2 := r 2 2
    let v := s + addend (thumbJump19Imm hw1 hw2) - p
    some [stAt env site 0 2 (thumbJump19Set1 hw1 v : Nat), stAt env site 2 2 (thumbJump19Set2 hw2 v : Nat)]
  | 0x29 | 0x60 => st 4 (slot (withT s) + a32 - p)
  | 0x66 => st 2 (thumbShortSet 11 (r 0 2) (s + addend (thumbShortImm 11 (r 0 2)) - p) : Nat)
  | 0x67 => st 2 (thumbShortSet 8 (r 0 2) (s + addend (thumbShortImm 8 (r 0 2)) - p) : Nat)
  | 0x6b => st 4 (slot (tpOff env s) + a32 - p)
  | 0x6c => st 4 (tpOff env s + a32)
  | _ => none

def armPlace : Nat → Nat
  | 0 | 0x28 => 0
  | 5 | 0x66 | 0x67 => 2
  | 8 => 1
  | _ => 4

def mipsCompoundBaseSpec (env : Env) (site : Site) (slot : Int → Int) (typ : Nat) : Option Int :=
  let x := site.s + site.a
  let gp := mipsGp env
  match typ with
  | 2 | 3 | 18 => some x
  | 7 | 12 => some (x + mipsGp0 env site.sym - gp)
  | 248 => some (x - site.p)
  | 19 => some (slot x - gp)
  | 9 | 11 => some (slot site.s - gp)
  | _ => none

def mipsCompoundSpec (env : Env) (site : Site) (rd : Bool → Nat → Nat → Nat) (slot : Int → Int) : Option (List Write) :=
  let typ := site.rel.typ
  let second := (typ >>> 8) % 256
  let third := (typ >>> 16) % 256
  match mipsSpecial env site (typ >>> 24) with
  | none => none
  | some special =>
    match mipsCompoundBaseSpec env site slot (typ % 256) with
    | none => none
    | some base =>
      match if third != 0 then mipsCompoundStep special base second else some base with
      | none => none
      | some value =>
        match mipsCompoundField (rd env.little (site.off + 0) 4) (if third != 0 then 0 else special) value
            (if third != 0 then third else second) with
        | some (n, stored) => some [stAt env site 0 n stored]
        | none => none

/-- MIPS, what each relocation stores when its handler is done with it: a deferred `HI16`, and a local `GOT16`, store later. -/
def mipsSpec (env : Env) (site : Site) (rd : Bool → Nat → Nat → Nat) (slot : Int → Int) : Option (List Write) :=
  let sym := site.sym
  let p := site.p
  let s := site.s
  let gp := mipsGp env
  let isLocal := sym.bind == stbLocal
  let r : Nat := rd env.little (site.off + 0) 4
  let st n value := some [stAt env site 0 n value]
  let a16 : Int := addendOf site (sext (r &&& 0xffff : Nat) 16)
  let a32 : Int := addendOf site (r : Int)
  match site.rel.typ with
  | 0 | 37 => some []
  | 2 => st 4 (s + a32)
  | 4 =>
    let a : Int := if site.rel.isExplicit then site.a else ((r &&& 0x3ffffff) <<< 2 : Nat)
    let target := if isLocal then (field a 0 28 + (field (p + 4) 28 36) * 2 ^ 28 : Nat) + s else sext a 28 + s
    st 4 (setBits r 0 26 (target >>> 2) : Nat)
  | 5 => some []
  | 9 => if isLocal then some [] else st 4 (setLo16 r (slot s - gp))
  | 11 => st 4 (setLo16 r (slot s - gp))
  | 6 => st 4 (setLo16 r ((if sym.name == "_gp_disp" then gp - p + 4 else s) + a16))
  | 7 | 8 => st 4 (setLo16 r (s + a16 + mipsGp0 env sym - gp))
  | 10 => st 4 (setLo16 r ((s + sext ((r &&& 0xffff) <<< 2 : Nat) 18 - p) >>> 2))
  | 12 => st 4 (s + a32 + mipsGp0 env sym - gp)
  | 18 => if env.width == 64 then st 8 (s + a32) else none
  | 20 =>
    if env.width == 64 then
      let x := s + a16
      if isLocal && sext x 32 == x then
        st 4 ((0x3c000000 ||| (field r 16 5 <<< 16) ||| field (x + 0x8000) 16 16 : Nat) : Int)
      else st 4 (setLo16 r (slot ((x + 0x8000) - (x + 0x8000) % 65536) - gp))
    else none
  | 21 =>
    if env.width == 64 then
      let x := s + a16
      st 4 (setLo16 r (if isLocal && sext x 32 == x then x else x - ((x + 0x8000) - (x + 0x8000) % 65536)))
    else none
  | 19 => st 4 (setLo16 r (slot (s + a16) - gp))
  | 22 | 30 => st 4 (setLo16 r (mipsHi (slot (s + a16) - gp)))
  | 23 | 31 => st 4 (setLo16 r (slot (s + a16) - gp))
  | 28 => st 4 (setLo16 r (mipsHigher (s + a16)))
  | 29 => st 4 (setLo16 r (mipsHighest (s + a16)))
  | 46 => st 4 (setLo16 r (slot (tpOff env s) + a16 - gp))
  | 47 => st 4 (tpOff env s + a32)
  | 48 => if env.width == 64 then st 8 (tpOff env s + a32) else none
  | 49 => st 4 (setLo16 r (mipsHi (tpOff env s + a16)))
  | 50 => st 4 (setLo16 r (tpOff env s + a16))
  | 248 => st 4 (s + a32 - p)
  | typ => if typ < 256 then none else mipsCompoundSpec env site rd slot

/-- A compound record stores eight bytes if its last relocation is a 64-bit one. -/
def mipsPlace (typ : Nat) : Nat :=
  match typ with
  | 0 | 37 => 0
  | 18 | 48 => 8
  | _ =>
    if typ < 256 then 4
    else
      let last := if (typ >>> 16) % 256 != 0 then (typ >>> 16) % 256 else (typ >>> 8) % 256
      if last == 18 || last == 24 then 8 else 4

/-- The length of a ULEB128 number, as `ulebLength` reads it. -/
def ulebLengthSpec (r : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n + 1
  | fuel + 1, n => if r n &&& 0x80 == 0 then n + 1 else ulebLengthSpec r fuel (n + 1)

def ulebSpec (env : Env) (site : Site) (rd : Bool → Nat → Nat → Nat) (f : Nat → Int) : Option (List Write) :=
  let r (i : Nat) : Nat := rd env.little (site.off + i) 1
  let n := ulebLengthSpec r 9 0
  let old := (List.range n).foldl (init := 0) fun acc i => acc + (r i &&& 0x7f) * 2 ^ (7 * i)
  some ((List.range n).map fun i =>
    stAt env site i 1 ((field (f old) (7 * i) 7 + (if i + 1 < n then 0x80 else 0) : Nat) : Int))

def riscvSpec (env : Env) (site : Site) (rd : Bool → Nat → Nat → Nat) (slot : Int → Int) (hi : Int → Option Int) :
    Option (List Write) :=
  let p := site.p
  let s := site.s
  let a := site.a
  let x := s + a
  let st n value := some [stAt env site 0 n value]
  let r (n : Nat) : Int := (rd env.little (site.off + 0) n : Nat)
  let c (at' n : Nat) : Nat := rd env.codeLittle (site.off + at') n
  let up (f : Nat → Int) := some [stiAt env site 0 4 (f (c 0 4))]
  let up16 (f : Nat → Int) := some [stiAt env site 0 2 (f (c 0 2))]
  let pcrelLo (f : Int → Nat → Int) :=
    match hi s with
    | some value => up (f value)
    | none => none
  match site.rel.typ with
  | 0 | 32 | 43 | 51 => some []
  | 1 => st 4 x
  | 2 => st 8 x
  | 16 => up (riscvB (x - p))
  | 17 => up (riscvJ (x - p))
  | 18 | 19 => some [stiAt env site 0 4 (riscvU (x - p) (c 0 4)), stiAt env site 4 4 (riscvI (x - p) (c 4 4))]
  | 29 => up (riscvU (tpOff env s + a))
  | 30 => up (riscvI (tpOff env s + a))
  | 31 => up (riscvS (tpOff env s + a))
  | 20 | 21 | 23 =>
    match hi p with
    | some value => up (riscvU value)
    | none => none
  | 24 => pcrelLo riscvI
  | 25 => pcrelLo riscvS
  | 26 => up (riscvU x)
  | 27 => up (riscvI x)
  | 28 => up (riscvS x)
  | 33 => st 1 (r 1 + x)
  | 34 => st 2 (r 2 + x)
  | 35 => st 4 (r 4 + x)
  | 36 => st 8 (r 8 + x)
  | 37 => st 1 (r 1 - x)
  | 38 => st 2 (r 2 - x)
  | 39 => st 4 (r 4 - x)
  | 40 => st 8 (r 8 - x)
  | 41 => st 4 (slot s + a - p)
  | 44 => up16 (riscvCB (x - p))
  | 45 => up16 (riscvCJ (x - p))
  | 52 => st 1 (setBits (rd env.little (site.off + 0) 1) 0 6 (r 1 - x) : Nat)
  | 53 => st 1 (setBits (rd env.little (site.off + 0) 1) 0 6 x : Nat)
  | 54 => st 1 x
  | 55 => st 2 x
  | 56 => st 4 x
  | 57 | 59 => st 4 (x - p)
  | 60 => ulebSpec env site rd fun _ => x
  | 61 => ulebSpec env site rd fun old => (old : Int) - x
  | _ => none

def riscvPlace : Nat → Nat
  | 0 | 32 | 43 | 51 => 0
  | 2 | 18 | 19 | 36 | 40 => 8
  | 33 | 37 | 52 | 53 | 54 => 1
  | 34 | 38 | 44 | 45 | 55 => 2
  | 60 | 61 => 10
  | _ => 4

def powerpcSpec (env : Env) (site : Site) (rd : Bool → Nat → Nat → Nat) (slot : Int → Int) : Option (List Write) :=
  let p := site.p
  let x := site.s + site.a
  let st n value := some [stAt env site 0 n value]
  let up (f : Nat → Nat) := some [stiAt env site 0 4 (f (rd env.codeLittle (site.off + 0) 4))]
  let ds (value : Int) :=
    let insn := if env.little then rd env.codeLittle (site.off + 0) 4 else rd false (site.off - 2 + 0) 4
    st 2 (ppcDsHalf (ppcIsDq insn) (rd env.little (site.off + 0) 2) value : Nat)
  let tp := tpOff env site.s + site.a
  match site.rel.typ with
  | 0 => some []
  | 1 => st 4 x
  | 2 => up fun i => setBits i 2 24 (x >>> 2)
  | 3 | 4 => st 2 x
  | 5 => st 2 (ppcHi x)
  | 6 => st 2 (ppcHa x)
  | 7 => up fun i => setBits i 2 14 (x >>> 2)
  | 10 | 18 => up fun i => setBits i 2 24 ((x - p) >>> 2)
  | 11 => up fun i => setBits i 2 14 ((x - p) >>> 2)
  | 26 => st 4 (x - p)
  | 38 => st 8 x
  | 44 => st 8 (x - p)
  | 67 => some []
  | 69 | 70 => st 2 tp
  | 71 => st 2 (ppcHi tp)
  | 72 => st 2 (ppcHa tp)
  | typ =>
    if env.machine != emPpc64 then
      let got := slot tp - (env.gotBase + 0x8000)
      match typ with
      | 73 => st 4 tp
      | 87 | 88 => st 2 got
      | 89 => st 2 (ppcHi got)
      | 90 => st 2 (ppcHa got)
      | _ => none
    else
      let toc := ppcToc env
      let got := slot x - toc
      let gotTp := slot tp - toc
      match typ with
      | 73 => st 8 tp
      | 87 | 88 => ds gotTp
      | 89 => st 2 (ppcHi gotTp)
      | 90 => st 2 (ppcHa gotTp)
      | 95 | 96 => ds tp
      | 97 => st 2 (ppcHigher tp)
      | 98 => st 2 (ppcHighera tp)
      | 99 => st 2 (ppcHighest tp)
      | 100 => st 2 (ppcHighesta tp)
      | 112 => st 2 (ppcHi tp)
      | 113 => st 2 (ppcHa tp)
      | 14 | 15 => st 2 got
      | 16 => st 2 (ppcHi got)
      | 17 => st 2 (ppcHa got)
      | 39 => st 2 (ppcHigher x)
      | 40 => st 2 (ppcHighera x)
      | 41 => st 2 (ppcHighest x)
      | 42 => st 2 (ppcHighesta x)
      | 47 | 48 => st 2 (x - toc)
      | 49 => st 2 (ppcHi (x - toc))
      | 50 => st 2 (ppcHa (x - toc))
      | 51 => st 8 (toc + site.a)
      | 56 | 57 => ds x
      | 58 | 59 => ds got
      | 63 | 64 => ds (x - toc)
      | 249 | 250 => st 2 (x - p)
      | 251 => st 2 (ppcHi (x - p))
      | 252 => st 2 (ppcHa (x - p))
      | _ => none

def ppcIsDs (typ : Nat) : Bool := typ == 87 || typ == 88 || typ == 95 || typ == 96 || typ == 56 || typ == 57 || typ == 58 ||
  typ == 59 || typ == 63 || typ == 64

/-- A DS-form offset is in the low half of a word, whose other half tells the form of the instruction, and which comes first on
big-endian. -/
def powerpcLo (little : Bool) (typ off : Nat) : Nat := if ppcIsDs typ && !little then off - 2 else off

def powerpcPlace (little : Bool) (typ : Nat) : Nat :=
  if ppcIsDs typ then (if little then 4 else 2)
  else match typ with
    | 0 | 67 => 0
    | 1 | 2 | 7 | 10 | 11 | 18 | 26 => 4
    | 38 | 44 | 51 | 73 => 8
    | _ => 2

def systemzSpec (env : Env) (site : Site) (rd : Bool → Nat → Nat → Nat) (slot : Int → Int) : Option (List Write) :=
  let x := site.s + site.a
  let pc := x - site.p
  let st n value := some [stAt env site 0 n value]
  let g := slot (tpOff env site.s)
  match site.rel.typ with
  | 0 | 37 => some []
  | 1 => st 1 x
  | 2 => st 2 (setBits (rd env.little (site.off + 0) 2) 0 12 x : Nat)
  | 3 => st 2 x
  | 4 => st 4 x
  | 5 | 8 => st 4 pc
  | 16 => st 2 pc
  | 17 | 18 => st 2 (pc >>> 1)
  | 19 | 20 => st 4 (pc >>> 1)
  | 22 => st 8 x
  | 23 | 25 => st 8 pc
  | 43 => st 4 (g - env.gotBase + site.a)
  | 44 => st 8 (g - env.gotBase + site.a)
  | 47 => st 4 (g + site.a)
  | 48 => st 8 (g + site.a)
  | 49 => st 4 ((g + site.a - site.p) >>> 1)
  | 50 => st 4 (tpOff env site.s + site.a)
  | 51 => st 8 (tpOff env site.s + site.a)
  | _ => none

def systemzPlace : Nat → Nat
  | 0 | 37 => 0
  | 1 => 1
  | 2 | 3 | 16 | 17 | 18 => 2
  | 22 | 23 | 25 | 44 | 48 | 51 => 8
  | _ => 4

/-! ### A handler does what its table says -/

/-- What a handler's result is, given what it read: the stores of its table. -/
def Says (spec : LinkState → Option (List Write)) : Option (List Write) → LinkState → Prop :=
  fun result after => ∀ writes, result = some writes → some writes = spec after

/-- Reduces a handler's arm to what its table says. -/
local macro "abi_arm" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
    repeat' first
      | simp only [wp_bind, wp_pure, wp_ite, wp_ld, wp_ldi, wp_ldInt, wp_got, wp_done, wp_getS, wp_throw, wp_insn]
      | trivial
      | split
      | intro _
      | with_reducible apply wp_any
    all_goals (rename_i hw; cases hw)
    all_goals try simp only [inSection, Bool.and_eq_true, decide_eq_true_eq] at *
    all_goals simp (disch := omega) only [$ts,*, addendOf, cut_read, readNat_gotAfter, slotOf_gotAfter, ite_true, ite_false,
      Bool.false_eq_true, *, Nat.add_zero, reduceIte]))

theorem x86_64_says {env : Env} {site : Site} {st : LinkState} :
    wp (x86_64 env site) (Says fun after => x86_64Spec env site (slotOf after)) st := by
  unfold x86_64
  dsimp only
  split <;> abi_arm [x86_64Spec, Says]

theorem i386_says {env : Env} {site : Site} {st : LinkState} (hl : site.limit ≤ env.gotOff) (hs : env.gotOff ≤ st.memory.size) :
    wp (i386 env site) (Says fun after => i386Spec env site
      (cut site.off (site.off + i386Place site.rel.typ) site.limit (fun l o n => readNat st.memory l o n)) (slotOf after)) st := by
  unfold i386
  dsimp only
  split <;> abi_arm [i386Spec, i386Place, Says]

set_option maxHeartbeats 2000000 in
theorem aarch64_says {env : Env} {site : Site} {st : LinkState} (hl : site.limit ≤ env.gotOff) (hs : env.gotOff ≤ st.memory.size) :
    wp (aarch64 env site) (Says fun after => aarch64Spec env site
      (cut site.off (site.off + aarch64Place site.rel.typ) site.limit (fun l o n => readNat st.memory l o n)) (slotOf after)) st := by
  unfold aarch64
  dsimp only
  split <;> abi_arm [aarch64Spec, aarch64Place, Says]

set_option maxHeartbeats 2000000 in
theorem arm_says {env : Env} {site : Site} {st : LinkState} (hl : site.limit ≤ env.gotOff) (hs : env.gotOff ≤ st.memory.size) :
    wp (arm env site) (Says fun after => armSpec env site
      (cut site.off (site.off + armPlace site.rel.typ) site.limit (fun l o n => readNat st.memory l o n)) (slotOf after)) st := by
  unfold arm
  dsimp only
  split <;> abi_arm [armSpec, armPlace, Says]
  all_goals simp_all

set_option maxHeartbeats 2000000 in
theorem systemz_says {env : Env} {site : Site} {st : LinkState} (_hl : site.limit ≤ env.gotOff) (_hs : env.gotOff ≤ st.memory.size) :
    wp (systemz env site) (Says fun after => systemzSpec env site
      (cut site.off (site.off + systemzPlace site.rel.typ) site.limit (fun l o n => readNat st.memory l o n)) (slotOf after)) st := by
  unfold systemz
  dsimp only
  split <;> abi_arm [systemzSpec, systemzPlace, Says]

set_option maxHeartbeats 2000000 in
theorem mipsCompound_says {env : Env} {site : Site} {st : LinkState} (hl : site.limit ≤ env.gotOff) (hs : env.gotOff ≤ st.memory.size)
    (hw : 4 ≤ mipsPlace site.rel.typ) :
    wp (mipsCompound env site) (Says fun after => mipsCompoundSpec env site
      (cut site.off (site.off + mipsPlace site.rel.typ) site.limit (fun l o n => readNat st.memory l o n)) (slotOf after)) st := by
  unfold mipsCompound mipsCompoundBase
  dsimp only
  abi_arm [mipsCompoundSpec, mipsCompoundBaseSpec, Says]
  all_goals (try simp (disch := omega) only [readNat_gotAfter] at *)
  all_goals (try simp only [Nat.add_zero] at *)
  all_goals simp only [*]

theorem mipsSpec_compound (env : Env) (site : Site) (rd : Bool → Nat → Nat → Nat) (slot : Int → Int) (h : 256 ≤ site.rel.typ) :
    mipsSpec env site rd slot = mipsCompoundSpec env site rd slot := by
  simp only [mipsSpec]
  split <;> first | omega | (rw [ite_eq_right (by omega)])

theorem mipsPlace_compound {typ : Nat} (h : 256 ≤ typ) : 4 ≤ mipsPlace typ := by
  have h0 : typ ≠ 0 ∧ typ ≠ 37 ∧ typ ≠ 18 ∧ typ ≠ 48 := by omega
  unfold mipsPlace
  split
  · omega
  · omega
  · omega
  · omega
  · dsimp only
    rw [ite_eq_right (by omega)]
    split <;> (try split) <;> omega

set_option maxHeartbeats 4000000 in
theorem mips_says {env : Env} {site : Site} {st : LinkState} (hl : site.limit ≤ env.gotOff) (hs : env.gotOff ≤ st.memory.size) :
    wp (mips env site) (Says fun after => mipsSpec env site
      (cut site.off (site.off + mipsPlace site.rel.typ) site.limit (fun l o n => readNat st.memory l o n)) (slotOf after)) st := by
  unfold mips
  dsimp only
  split
  rotate_right
  · simp only [wp_ite, wp_pure]
    split
    · intro _ hw
      cases hw
    · have hbig : 256 ≤ site.rel.typ := by omega
      have := mipsCompound_says (env := env) (st := st) hl hs (mipsPlace_compound hbig)
      simp only [mipsSpec_compound _ _ _ _ hbig] at *
      exact this
  all_goals abi_arm [mipsSpec, mipsPlace, Says]
  all_goals try simp_all
  all_goals try simp (disch := omega) only [cut_read]
  all_goals try (split <;> simp_all [slotOf_gotAfter])
  all_goals simp only [slotOf_gotAfter]

/-- What is read of a ULEB128 number stays in the ten bytes of its place. -/
theorem ulebLength_spec {env : Env} {site : Site} {st : LinkState} {lo limit : Nat} (hlo : lo = site.off) (hhi : limit = site.limit) :
    ∀ (fuel n : Nat) {result : Nat} {after : LinkState}, n + fuel ≤ 9 → ulebLength env site fuel n st = .ok result after →
      after = st ∧ n < result ∧ result ≤ 10 ∧
      result = ulebLengthSpec (fun i => cut lo (lo + 10) limit (fun l o k => readNat st.memory l o k) env.little (site.off + i) 1) fuel n := by
  subst hlo hhi
  intro fuel
  induction fuel with
  | zero =>
    intro n result after hn h
    simp only [ulebLength, pure, EStateM.pure] at h
    cases h
    exact ⟨rfl, by omega, by omega, rfl⟩
  | succ fuel ih =>
    intro n result after hn h
    unfold ulebLength at h
    simp only [ld, ElfLinker.load, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get] at h
    by_cases hb : inSection site n 1 st.memory.size = true
    · simp only [hb, ite_true, pure, EStateM.pure] at h
      have hb' := hb
      simp only [inSection, Bool.and_eq_true, decide_eq_true_eq] at hb'
      have hcut : cut site.off (site.off + 10) site.limit (fun l o k => readNat st.memory l o k) env.little (site.off + n) 1 =
          readNat st.memory env.little (site.off + n) 1 := cut_read _ _ _ (by omega) (by omega) (by omega)
      simp only [ulebLengthSpec, hcut]
      split at h
      · next hz =>
        cases h
        rw [ite_eq_left hz]
        exact ⟨rfl, by omega, by omega, rfl⟩
      · next hz =>
        obtain ⟨h1, h2, h3, h6⟩ := ih (n + 1) (by omega) h
        rw [ite_eq_right hz]
        exact ⟨h1, by omega, h3, h6⟩
    · have hb' : inSection site n 1 st.memory.size = false := by simpa using hb
      simp [hb', throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h

theorem uleb_loop_in {env : Env} {site : Site} {state : LinkState} :
    ∀ (l : List Nat) (init r : Nat) (after : LinkState),
      (forIn l init (fun i (r : Nat) =>
        (do
          let r' := r + ((← ld env site i 1) &&& 0x7f) * 2 ^ (7 * i)
          pure PUnit.unit
          pure (ForInStep.yield r') : LinkM (ForInStep Nat)))) state = .ok r after →
      ∀ i ∈ l, inSection site i 1 state.memory.size = true
  | [], _, _, _, _, _, hi => by cases hi
  | i :: rest, init, r, after, h, j, hj => by
    simp only [List.forIn_cons] at h
    by_cases hb : inSection site i 1 state.memory.size = true
    · have hi := ld_ok (env := env) hb
      simp only [bind, EStateM.bind, hi, pure, EStateM.pure] at h
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hb
      · exact uleb_loop_in rest _ r after h j hj
    · have hb' : inSection site i 1 state.memory.size = false := by simpa using hb
      simp [bind, EStateM.bind, ld, ElfLinker.load, get, getThe, MonadStateOf.get, EStateM.get, hb', throw, throwThe,
        MonadExceptOf.throw, EStateM.throw] at h

theorem foldl_congr_mem {f g : β → α → β} : ∀ (l : List α) (init : β), (∀ b, ∀ a ∈ l, f b a = g b a) →
    l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | a :: rest, init, h => by
    simp only [List.foldl_cons]
    rw [h init a (by simp)]
    exact foldl_congr_mem rest _ fun b x hx => h b x (by simp [hx])

/-- `R_RISCV_SET_ULEB128` and `R_RISCV_SUB_ULEB128` do what their table says. -/
theorem rewriteUleb_says {env : Env} {site : Site} {st : LinkState} (f : Nat → Int) :
    wp (rewriteUleb env site f) (fun result _ => ∀ writes, result = some writes → some writes = ulebSpec env site
      (cut site.off (site.off + 10) site.limit (fun l o n => readNat st.memory l o n)) f) st := by
  unfold wp
  split
  · next result after h =>
    intro writes hres
    subst hres
    have hbind : rewriteUleb env site f st = _ := h
    simp only [rewriteUleb, bind, EStateM.bind] at hbind
    cases hlen : ulebLength env site 9 0 st with
    | error e s => simp [hlen] at hbind
    | ok n mid =>
      obtain ⟨rfl, _, hle, hspec⟩ := ulebLength_spec (env := env) (site := site) (st := st) rfl rfl 9 0 (by omega) hlen
      simp only [hlen] at hbind
      have hb : ∀ i, i < n → inSection site i 1 mid.memory.size = true := by
        split at hbind
        · next a s heq => exact fun i hi => uleb_loop_in _ _ _ _ heq i (List.mem_range.2 hi)
        · cases hbind
      have hrun := rewriteUleb_spec (f := f) hlen hb
      have heq : EStateM.Result.ok (some writes) after = _ := h.symm.trans hrun
      simp only [EStateM.Result.ok.injEq] at heq
      obtain ⟨hw, rfl⟩ := heq
      have hold : (List.range n).foldl (init := 0) (fun acc i => acc + (cut site.off (site.off + 10) site.limit
            (fun l o k => readNat after.memory l o k) env.little (site.off + i) 1 &&& 0x7f) * 2 ^ (7 * i)) =
          (List.range n).foldl (init := 0) (fun r i => r + (readNat after.memory env.little (site.off + i) 1 &&& 0x7f) * 2 ^ (7 * i)) := by
        refine foldl_congr_mem _ _ fun b i hi => ?_
        have hi' := List.mem_range.1 hi
        have hb' := hb i hi'
        simp only [inSection, Bool.and_eq_true, decide_eq_true_eq] at hb'
        rw [cut_read _ _ _ (by omega) (by omega) (by omega)]
      simp only [ulebSpec, ← hspec, hold]
      rw [hw]
  · trivial

theorem wp_mono {m : LinkM α} {Q Q' : α → LinkState → Prop} {st : LinkState} (h : wp m Q st) (hq : ∀ a s, Q a s → Q' a s) :
    wp m Q' st := by
  unfold wp at h ⊢
  cases hr : m st with
  | ok a s => rw [hr] at h; exact hq _ _ h
  | error e s => trivial

set_option maxHeartbeats 2000000 in
theorem riscv_says {env : Env} {site : Site} {st : LinkState} (_hl : site.limit ≤ env.gotOff) (_hs : env.gotOff ≤ st.memory.size) :
    wp (riscv env site) (Says fun after => riscvSpec env site
      (cut site.off (site.off + riscvPlace site.rel.typ) site.limit (fun l o n => readNat st.memory l o n)) (slotOf after)
        (fun key => st.riscvHi[key]?)) st := by
  unfold riscv
  dsimp only
  split <;> first
    | (with_reducible refine @id (wp (rewriteUleb _ _ _) _ _) ?_
       refine wp_mono (rewriteUleb_says _) ?_
       intro r after h writes hw
       rw [h writes hw]
       simp only [riscvSpec, riscvPlace, *])
    | abi_arm [riscvSpec, riscvPlace, Says]

set_option maxHeartbeats 4000000 in
theorem powerpc_says {env : Env} {site : Site} {st : LinkState} (hl : site.limit ≤ env.gotOff) (hs : env.gotOff ≤ st.memory.size) :
    wp (powerpc env site) (Says fun after => powerpcSpec env site
      (cut (powerpcLo env.little site.rel.typ site.off) (site.off + powerpcPlace env.little site.rel.typ) site.limit
        (fun l o n => readNat st.memory l o n)) (slotOf after)) st := by
  unfold powerpc
  dsimp only
  split <;> abi_arm [powerpcSpec, powerpcPlace, powerpcLo, ppcIsDs, Says]
  all_goals try simp_all
  all_goals try simp (disch := omega) only [cut_read]

end Bap.Proofs.Linker
