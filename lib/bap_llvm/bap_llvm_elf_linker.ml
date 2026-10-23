open Core

type section = {
  index : int;
  name : string;
  typ : int;
  flags : int64;
  off : int64;
  size : int64;
  align : int64;
}

type symbol = {
  name : string;
  shndx : int;
  extended : bool;
  value : int64;
  size : int64;
  typ : int;
  bind : int;
}

type relocation = {
  section : int;
  offset : int64;
  typ : int;
  symbol : int;
  addend : int64;
  explicit : bool;
}

type input = {
  machine : int;
  width : int;
  little : bool;
  base : int64;
  data : Bigstring.t;
  sections : section list;
  symbols : symbol Int.Map.t;
  relocations : relocation list;
}

type region = {
  name : string;
  addr : int64;
  size : int64;
  off : int64 option;
  r : bool;
  w : bool;
  x : bool;
  is_section : bool;
}

type output = {
  regions : region list;
  functions : (string * int64 * int64 * int64) list;
  references : (int64 * string) list;
  patches : (int64 * string) list;
  warnings : string list;
}

(* The constants of the ELF generic ABI (gABI) that the linker uses,
   named as in <elf.h> without the prefix. *)
module Elf = struct
  (* section flags (sh_flags) *)
  let shf_write = 0x1L (* writable at run time *)
  let shf_alloc = 0x2L (* occupies memory at run time *)
  let shf_execinstr = 0x4L (* contains executable code *)

  (* section type (sh_type) of a section with no file contents (.bss) *)
  let sht_nobits = 8

  (* special section indices (st_shndx) *)
  let shn_undef = 0 (* the symbol is undefined *)
  let shn_loreserve = 0xff00 (* the start of the reserved indices *)
  let shn_abs = 0xfff1 (* the value is an absolute address *)

  (* a common block, the value is its alignment *)
  let shn_common = 0xfff2

  (* symbol types (st_info & 0xf) *)
  let stt_func = 2
  let stt_gnu_ifunc = 10 (* a function resolved at load time *)

  (* symbol binding (st_info >> 4) *)
  let stb_local = 0

  (* machines (e_machine) *)
  let em_386 = 3
  let em_mips = 8
  let em_ppc = 20
  let em_ppc64 = 21
  let em_arm = 40
  let em_x86_64 = 62
  let em_aarch64 = 183
  let em_riscv = 243
end

let has flags flag = Int64.(flags land flag <> 0L)

let align_up x align =
  if Int64.(align <= 1L) then x else Int64.((x + align - 1L) / align * align)

(* [sext x n] sign-extends the [n]-bit value [x] *)
let sext x n = Int64.((x lsl Int.(64 - n)) asr Int.(64 - n))
let mask n = Int64.((1L lsl n) - 1L)

(* [bits x lo n] the [n] bits of [x] starting from the bit [lo] *)
let bits x lo n = Int64.((x lsr lo) land mask n)

(* [set_bits x lo n v] replaces the [n] bits of [x] at [lo] with [v] *)
let set_bits x lo n v =
  Int64.(x land lnot (mask n lsl lo) lor ((v land mask n) lsl lo))

(* The contents of the file with the relocations applied. It is a copy
   of the file, extended with zeros when the bytes past its end are
   written, and a bitmap of the modified bytes. *)
module Memory = struct
  type t = {
    length : int;  (** the length of the file *)
    mutable data : Bytes.t;
    mutable modified : Bytes.t;  (** a bit per byte of [data] *)
  }

  let create data =
    let length = Bigstring.length data in
    {
      length;
      data = Bigstring.to_bytes data;
      modified = Bytes.make ((length + 7) / 8) '\000';
    }

  let length t = Int64.of_int t.length

  (* the bytes past the end of the file are only written when the GOT
     is filled, so the buffer grows geometrically *)
  let reserve t off =
    let size = Bytes.length t.data in
    if off >= size then begin
      let size = Int.max (off + 1) (2 * size) in
      let data = Bytes.make size '\000' in
      Bytes.blito ~src:t.data ~dst:data ();
      let modified = Bytes.make ((size + 7) / 8) '\000' in
      Bytes.blito ~src:t.modified ~dst:modified ();
      t.data <- data;
      t.modified <- modified
    end

  let is_modified t off =
    Char.to_int (Bytes.unsafe_get t.modified (off lsr 3))
    land (1 lsl (off land 7))
    <> 0

  let get t off =
    let off = Int64.to_int_exn off in
    if off < 0 || off >= Bytes.length t.data then 0
    else Char.to_int (Bytes.get t.data off)

  let set t off b =
    let off = Int64.to_int_exn off in
    reserve t off;
    Bytes.set t.data off (Char.unsafe_of_int (b land 0xff));
    let bits = Char.to_int (Bytes.get t.modified (off lsr 3)) in
    Bytes.set t.modified (off lsr 3)
      (Char.unsafe_of_int (bits lor (1 lsl (off land 7))))

  let shift ~little n i = 8 * if little then i else n - i - 1

  let read t ~little off n =
    let x = ref 0L in
    for i = 0 to n - 1 do
      let b = Int64.of_int (get t Int64.(off + of_int i)) in
      x := Int64.(!x lor (b lsl shift ~little n i))
    done;
    !x

  let write t ~little off n v =
    for i = 0 to n - 1 do
      let b = Int64.((v lsr shift ~little n i) land 0xffL) in
      set t Int64.(off + of_int i) (Int64.to_int_exn b)
    done

  (* Two runs of modified bytes that are at most this far apart are
     emitted as one patch, together with the unmodified bytes between
     them. A patch costs more than a few dozen bytes of data, and the
     relocations of code are usually a few bytes apart. *)
  let max_gap = 32

  (* the runs of the modified bytes, as [(off, bytes)] *)
  let patches t =
    let size = Bytes.length t.data in
    let emit acc start stop =
      ( Int64.of_int start,
        Bytes.To_string.sub t.data ~pos:start ~len:(stop - start) )
      :: acc
    in
    (* [run] is the current run [start, stop), if any *)
    let rec scan acc run off =
      if off >= size then
        match run with None -> acc | Some (start, stop) -> emit acc start stop
      else if
        off land 7 = 0 && Char.equal (Bytes.get t.modified (off lsr 3)) '\000'
      then scan acc run (off + 8)
      else if not (is_modified t off) then scan acc run (off + 1)
      else
        match run with
        | Some (start, stop) when off - stop <= max_gap ->
            scan acc (Some (start, off + 1)) (off + 1)
        | Some (start, stop) ->
            scan (emit acc start stop) (Some (off, off + 1)) (off + 1)
        | None -> scan acc (Some (off, off + 1)) (off + 1)
    in
    List.rev (scan [] None 0)
end

(* a relocated place *)
type site = {
  rel : relocation;
  sym : symbol;
  p : int64;  (** the address of the place *)
  s : int64;  (** the address of the symbol *)
  a : int64;  (** the explicit addend or zero *)
  ld : int -> int -> int64;  (** [ld at n] loads [n] bytes of data at [p+at] *)
  st : int -> int -> int64 -> unit;  (** [st at n x] stores [x] at [p+at] *)
  ldi : int -> int -> int64;  (** loads using the code endianness *)
  sti : int -> int -> int64 -> unit;  (** stores using the code endianness *)
}

type env = {
  got : int64 -> int64;
      (** [got x] is the address of the GOT entry that holds [x] *)
  got_base : int64;
}

type result = Done | Unsupported

(* [Outside_of_section (p, name)] the relocation at [p] accesses bytes
   outside of the section [name] *)
exception Outside_of_section of int64 * string

type handler = {
  prescan : site -> unit;
  apply : site -> result;
  finish : unit -> unit;
}

let simple apply = { prescan = ignore; apply; finish = Fn.id }

let store site n x =
  site.st 0 n x;
  Done

let update_insn site f =
  site.sti 0 4 (f (site.ldi 0 4));
  Done

(* The relocation types below are the numbers of the R_<ARCH>_* constants
   of each processor's psABI. Their names are given next to each case, and
   in the formulas S is the symbol address ([s]), A the addend ([a]), P the
   address of the place ([p]), GOT the address of the GOT ([env.got_base]),
   and G(x) the address of the GOT entry of x ([env.got x]). There are no
   PLT entries, so the PLT relocations are resolved directly to the symbol. *)

(* x86-64 psABI, all relocations are RELA *)
let x86_64 env =
  simple @@ fun ({ rel; sym; p; s; a; _ } as site) ->
  let open Int64 in
  let store = store site in
  match rel.typ with
  | 0 -> Done (* NONE *)
  | 1 -> store 8 (s + a) (* 64 *)
  | 2 | 4 -> store 4 (s + a - p) (* PC32, PLT32 *)
  | 3 -> store 4 (env.got s - env.got_base + a) (* GOT32 *)
  (* GOTPCREL, GOTPCRELX, REX_GOTPCRELX, CODE_4_GOTPCRELX. The GOTPCRELX
     variants let the linker relax the load into a lea, we don't. *)
  | 9 | 41 | 42 | 43 -> store 4 (env.got s + a - p)
  | 10 | 11 -> store 4 (s + a) (* 32, 32S *)
  | 12 -> store 2 (s + a) (* 16 *)
  | 13 -> store 2 (s + a - p) (* PC16 *)
  | 14 -> store 1 (s + a) (* 8 *)
  | 15 -> store 1 (s + a - p) (* PC8 *)
  | 24 -> store 8 (s + a - p) (* PC64 *)
  | 25 -> store 8 (s + a - env.got_base) (* GOTOFF64 *)
  | 26 -> store 4 (env.got_base + a - p) (* GOTPC32 *)
  | 27 -> store 8 (env.got s - env.got_base + a) (* GOT64 *)
  | 28 -> store 8 (env.got s + a - p) (* GOTPCREL64 *)
  | 29 -> store 8 (env.got_base + a - p) (* GOTPC64 *)
  | 32 -> store 4 (sym.size + a) (* SIZE32 *)
  | 33 -> store 8 (sym.size + a) (* SIZE64 *)
  | _ -> Unsupported

(* i386 psABI, the relocations are REL, so the addend is the
   sign-extended contents of the place *)
let i386 env =
  simple @@ fun ({ rel; p; s; _ } as site) ->
  let open Int64 in
  let store = store site in
  let a n = if rel.explicit then site.a else sext (site.ld 0 n) Int.(8 * n) in
  match rel.typ with
  | 0 -> Done (* NONE *)
  | 1 -> store 4 (s + a 4) (* 32 *)
  | 2 | 4 -> store 4 (s + a 4 - p) (* PC32, PLT32 *)
  | 3 | 43 -> store 4 (env.got s + a 4 - env.got_base) (* GOT32, GOT32X *)
  | 9 -> store 4 (s + a 4 - env.got_base) (* GOTOFF *)
  | 10 -> store 4 (env.got_base + a 4 - p) (* GOTPC *)
  | 20 -> store 2 (s + a 2) (* 16 *)
  | 21 -> store 2 (s + a 2 - p) (* PC16 *)
  | 22 -> store 1 (s + a 1) (* 8 *)
  | 23 -> store 1 (s + a 1 - p) (* PC8 *)
  | _ -> Unsupported

(* AArch64 ELF ABI (AAELF64), all relocations are RELA *)
let aarch64 env =
  simple @@ fun ({ rel; p; s; a; _ } as site) ->
  let open Int64 in
  let store = store site and update = update_insn site in
  (* the 4KiB page of an address, as computed by ADRP *)
  let page x = x land lnot 0xfffL in
  (* the 21-bit immediate of ADR/ADRP: immlo at 29-30, immhi at 5-23 *)
  let adr v insn = set_bits (set_bits insn 29 2 v) 5 19 (v asr 2) in
  (* the 12-bit immediate (at 10-21) of ADD and of the loads and stores,
     which is scaled by the access size, 2^shift bytes *)
  let lo12 shift v =
    update (fun insn -> set_bits insn 10 12 ((v land 0xfffL) asr shift))
  in
  let x = s + a in
  match rel.typ with
  | 0 -> Done (* NONE *)
  | 0x101 -> store 8 x (* ABS64 *)
  | 0x102 -> store 4 x (* ABS32 *)
  | 0x103 -> store 2 x (* ABS16 *)
  | 0x104 -> store 8 (x - p) (* PREL64 *)
  | 0x105 | 0x13a -> store 4 (x - p) (* PREL32, PLT32 *)
  | 0x106 -> store 2 (x - p) (* PREL16 *)
  (* MOVW_UABS_G0 (0x107), G0_NC, G1, G1_NC, G2, G2_NC, and G3 (0x10d):
     the 16-bit immediate (at 5-20) of MOVZ/MOVK is the n-th halfword of
     the value, where n = (type - 0x107) / 2 *)
  | t when Int.(t >= 0x107 && t <= 0x10d) ->
      let shift = Int.((t - 0x107) / 2 * 16) in
      update (fun insn -> set_bits insn 5 16 (x asr shift))
  (* LD_PREL_LO19, CONDBR19: the 19-bit word offset at 5-23 *)
  | 0x111 | 0x118 -> update (fun insn -> set_bits insn 5 19 ((x - p) asr 2))
  | 0x112 -> update (adr (x - p)) (* ADR_PREL_LO21 *)
  (* ADR_PREL_PG_HI21, ADR_PREL_PG_HI21_NC *)
  | 0x113 | 0x114 -> update (adr ((page x - page p) asr 12))
  | 0x115 | 0x116 -> lo12 0 x (* ADD_ABS_LO12_NC, LDST8_ABS_LO12_NC *)
  (* TSTBR14: the 14-bit word offset of TBZ/TBNZ at 5-18 *)
  | 0x117 -> update (fun insn -> set_bits insn 5 14 ((x - p) asr 2))
  (* JUMP26, CALL26: the 26-bit word offset of B/BL at 0-25 *)
  | 0x11a | 0x11b -> update (fun insn -> set_bits insn 0 26 ((x - p) asr 2))
  | 0x11c -> lo12 1 x (* LDST16_ABS_LO12_NC *)
  | 0x11d -> lo12 2 x (* LDST32_ABS_LO12_NC *)
  | 0x11e -> lo12 3 x (* LDST64_ABS_LO12_NC *)
  | 0x12b -> lo12 4 x (* LDST128_ABS_LO12_NC *)
  (* GOT_LD_PREL19 *)
  | 0x135 -> update (fun insn -> set_bits insn 5 19 ((env.got x - p) asr 2))
  (* ADR_GOT_PAGE *)
  | 0x137 -> update (adr ((page (env.got x) - page p) asr 12))
  | 0x138 -> lo12 3 (env.got x) (* LD64_GOT_LO12_NC *)
  | 0x13b -> store 4 (env.got s + a - p) (* GOTPCREL32 *)
  | _ -> Unsupported

let is_function (sym : symbol) =
  sym.typ = Elf.stt_func || sym.typ = Elf.stt_gnu_ifunc

let is_thumb (sym : symbol) = is_function sym && Int64.(sym.value land 1L = 1L)

(* ARM ELF ABI (AAELF32). The relocations are usually REL, so the addend
   is decoded from the place. T is 1 when the target is a Thumb function
   (bit 0 of its value is set), and it is ORed into the addresses that
   are used for interworking. *)
let arm env =
  simple @@ fun ({ rel; sym; p; ld; _ } as site) ->
  let open Int64 in
  let store = store site in
  let thumb = is_thumb sym in
  let t = if thumb then 1L else 0L in
  let s = site.s land lnot t in
  let addend decoded = if rel.explicit then site.a else decoded in
  let a32 () = addend (sext (ld 0 4) 32) in
  (* the 16-bit immediate of MOVW/MOVT, the lo variants store the low
     halfword of the value and the hi variants the high one *)
  let movw typ imm =
    let a = addend (sext imm 16) in
    let v =
      match typ with
      | `abs_lo -> (s + a) lor t
      | `abs_hi -> (s + a) asr 16
      | `rel_lo -> ((s + a) lor t) - p
      | `rel_hi -> (s + a - p) asr 16
    in
    v land 0xffffL
  in
  (* A32 MOVW/MOVT: imm16 is split into imm4 at 16-19 and imm12 at 0-11,
     the mask 0xfff0f000 keeps the condition, the opcode, and Rd *)
  let arm_movw typ =
    let insn = ld 0 4 in
    let imm = (insn lsr 4) land 0xf000L lor (insn land 0xfffL) in
    let v = movw typ imm in
    store 4
      (insn land 0xfff0f000L lor ((v land 0xf000L) lsl 4) lor (v land 0xfffL))
  in
  (* T32 MOVW/MOVT: imm16 is split into imm4 (hw1 0-3), i (hw1 10),
     imm3 (hw2 12-14), and imm8 (hw2 0-7). The masks 0xfbf0 and 0x8f00
     clear these fields and keep the opcode and Rd. *)
  let thumb_movw typ =
    let hw1 = ld 0 2 and hw2 = ld 2 2 in
    let imm =
      (bits hw1 0 4 lsl 12)
      lor (bits hw1 10 1 lsl 11)
      lor (bits hw2 12 3 lsl 8)
      lor bits hw2 0 8
    in
    let v = movw typ imm in
    site.st 0 2 (hw1 land 0xfbf0L lor bits v 12 4 lor (bits v 11 1 lsl 10));
    site.st 2 2 (hw2 land 0x8f00L lor (bits v 8 3 lsl 12) lor bits v 0 8);
    Done
  in
  (* A32 B, BL, and BLX: the 24-bit word offset at 0-23. A call (CALL,
     0x1c) is rewritten for interworking: a BL to Thumb code becomes BLX
     (immediate) 0xfa000000, whose H bit (24) holds bit 1 of the offset,
     and a BLX to ARM code becomes BL with the AL condition 0xeb000000. *)
  let arm_branch () =
    let insn = ld 0 4 in
    let a = addend (sext ((insn land 0xffffffL) lsl 2) 26) in
    let v = s + a - p in
    let imm24 = bits v 2 24 in
    if Int.(rel.typ = 0x1c) && thumb then
      store 4 (0xfa000000L lor (bits v 1 1 lsl 24) lor imm24)
    else if Int.(rel.typ = 0x1c) && is_function sym && bits insn 28 4 = 0xfL
    then store 4 (0xeb000000L lor imm24)
    else store 4 (insn land 0xff000000L lor imm24)
  in
  (* T32 BL, BLX, and B.W: the 25-bit offset is S:I1:I2:imm10:imm11:0,
     where S is at hw1 10, imm10 at hw1 0-9, imm11 at hw2 0-10, and
     I1 = not (J1 xor S), I2 = not (J2 xor S) with J1 at hw2 13 and J2
     at hw2 11. Bit 12 of hw2 is set for BL and clear for BLX. The masks
     0xf800 and 0xd000 keep the opcode bits. A call (THM_CALL, 0xa) is
     rewritten into BL or BLX depending on the mode of the target, and
     BLX is relative to the word-aligned P. *)
  let thumb_branch () =
    let hw1 = ld 0 2 and hw2 = ld 2 2 in
    let sign = bits hw1 10 1 in
    let i1 = lnot (bits hw2 13 1 lxor sign) land 1L
    and i2 = lnot (bits hw2 11 1 lxor sign) land 1L in
    let a =
      addend
        (sext
           ((sign lsl 24) lor (i1 lsl 23) lor (i2 lsl 22)
           lor (bits hw1 0 10 lsl 12)
           lor (bits hw2 0 11 lsl 1))
           25)
    in
    let call = Int.(rel.typ = 0xa) in
    let blx =
      call && if is_function sym then not thumb else bits hw2 12 1 = 0L
    in
    let v = if blx then s + a - (p land lnot 3L) else s + a - p in
    let sign = bits v 24 1 in
    let j1 = lnot (bits v 23 1 lxor sign) land 1L
    and j2 = lnot (bits v 22 1 lxor sign) land 1L in
    let hw2 =
      if not call then hw2
      else if blx then hw2 land lnot 0x1000L
      else hw2 lor 0x1000L
    in
    site.st 0 2 (hw1 land 0xf800L lor (sign lsl 10) lor bits v 12 10);
    site.st 2 2
      (hw2 land 0xd000L lor (j1 lsl 13) lor (j2 lsl 11) lor bits v 1 11);
    Done
  in
  (* the conditional T32 B.W: the 21-bit offset is S:J2:J1:imm6:imm11:0,
     where S is at hw1 10, imm6 at hw1 0-5, J1 at hw2 13, J2 at hw2 11,
     and imm11 at hw2 0-10. The mask 0xfbc0 keeps the opcode and the
     condition (hw1 6-9). *)
  let thumb_jump19 () =
    let hw1 = ld 0 2 and hw2 = ld 2 2 in
    let a =
      addend
        (sext
           ((bits hw1 10 1 lsl 20)
           lor (bits hw2 11 1 lsl 19)
           lor (bits hw2 13 1 lsl 18)
           lor (bits hw1 0 6 lsl 12)
           lor (bits hw2 0 11 lsl 1))
           21)
    in
    let v = s + a - p in
    site.st 0 2 (hw1 land 0xfbc0L lor (bits v 20 1 lsl 10) lor bits v 12 6);
    site.st 2 2
      (hw2 land 0xd000L
      lor (bits v 18 1 lsl 13)
      lor (bits v 19 1 lsl 11)
      lor bits v 1 11);
    Done
  in
  (* T16 B and B<cond>: the n-bit halfword offset in the low bits *)
  let thumb_short_branch n =
    let hw = ld 0 2 in
    let a = addend (sext ((hw land mask n) lsl 1) Int.(n + 1)) in
    store 2 (hw land lnot (mask n) lor bits (s + a - p) 1 n)
  in
  match rel.typ with
  (* NONE, V4BX (marks a BX for ARMv4 patching, which isn't needed) *)
  | 0 | 0x28 -> Done
  | 1 | 0x1c | 0x1d -> arm_branch () (* PC24, CALL, JUMP24 *)
  | 2 | 0x26 -> store 4 ((s + a32 ()) lor t) (* ABS32, TARGET1 *)
  | 3 | 0x29 -> store 4 (((s + a32 ()) lor t) - p) (* REL32, TARGET2 *)
  | 5 -> store 2 (s + addend (sext (ld 0 2) 16)) (* ABS16 *)
  | 8 -> store 1 (s + addend (sext (ld 0 1) 8)) (* ABS8 *)
  | 0xa | 0x1e -> thumb_branch () (* THM_CALL, THM_JUMP24 *)
  | 0x18 -> store 4 (s + a32 () - env.got_base) (* GOTOFF32 *)
  | 0x19 -> store 4 (env.got_base + a32 () - p) (* BASE_PREL *)
  | 0x1a -> store 4 (env.got (s lor t) + a32 () - env.got_base) (* GOT_BREL *)
  (* PREL31: the low 31 bits hold the offset, bit 31 is kept, as used in
     the exception index tables (.ARM.exidx) *)
  | 0x2a ->
      let old = ld 0 4 in
      let a = addend (sext (old land 0x7fffffffL) 31) in
      store 4 (old land 0x80000000L lor ((((s + a) lor t) - p) land 0x7fffffffL))
  | 0x2b -> arm_movw `abs_lo (* MOVW_ABS_NC *)
  | 0x2c -> arm_movw `abs_hi (* MOVT_ABS *)
  | 0x2d -> arm_movw `rel_lo (* MOVW_PREL_NC *)
  | 0x2e -> arm_movw `rel_hi (* MOVT_PREL *)
  | 0x2f -> thumb_movw `abs_lo (* THM_MOVW_ABS_NC *)
  | 0x30 -> thumb_movw `abs_hi (* THM_MOVT_ABS *)
  | 0x31 -> thumb_movw `rel_lo (* THM_MOVW_PREL_NC *)
  | 0x32 -> thumb_movw `rel_hi (* THM_MOVT_PREL *)
  | 0x33 -> thumb_jump19 () (* THM_JUMP19 *)
  | 0x60 -> store 4 (env.got (s lor t) + a32 () - p) (* GOT_PREL *)
  | 0x66 -> thumb_short_branch 11 (* THM_JUMP11 *)
  | 0x67 -> thumb_short_branch 8 (* THM_JUMP8 *)
  | _ -> Unsupported

(* The offset of the global pointer ($gp, _gp) from the start of the
   GOT. The GOT is accessed through signed 16-bit offsets from $gp, so
   pointing $gp 0x7ff0 bytes into the GOT makes 64KiB of it reachable. *)
let mips_gp_offset = 0x7ff0L

(* MIPS o32 (SYSV ABI MIPS supplement), the relocations are REL. The
   HI16 (and local GOT16) relocations are applied when the matching LO16
   relocation is found, since they share the addend AHL = (AHI << 16) +
   ALO. The HI16 values are rounded by 0x8000 to compensate for the sign
   extension of the low 16 bits by the paired instruction. GP is the
   value of $gp. *)
let mips env =
  let open Int64 in
  let gp = env.got_base + mips_gp_offset in
  let pending = ref [] in
  let is_gp_disp (sym : symbol) = String.equal sym.name "_gp_disp" in
  let is_local (sym : symbol) = Int.(sym.bind = Elf.stb_local) in
  let set_lo16 insn v = set_bits insn 0 16 v in
  let apply_hi site ahl =
    let insn = site.ld 0 4 in
    match site.rel.typ with
    | 5 ->
        let s = if is_gp_disp site.sym then gp - site.p else site.s in
        site.st 0 4 (set_lo16 insn ((ahl + s + 0x8000L) asr 16))
    | _ ->
        let page = (site.s + ahl + 0x8000L) land lnot 0xffffL in
        site.st 0 4 (set_lo16 insn (env.got page - gp))
  in
  let flush ~lo symbol =
    let matched, rest =
      List.partition_tf !pending ~f:(fun (site, _) ->
          Int.(site.rel.symbol = symbol))
    in
    pending := rest;
    List.iter (List.rev matched) ~f:(fun (site, hi) ->
        apply_hi site ((hi lsl 16) + lo))
  in
  let apply ({ rel; sym; p; s; ld; _ } as site) =
    let store = store site in
    let a16 () =
      if rel.explicit then site.a else sext (ld 0 4 land 0xffffL) 16
    in
    let a32 () = if rel.explicit then site.a else ld 0 4 in
    let defer () =
      if rel.explicit then apply_hi site site.a
      else pending := (site, ld 0 4 land 0xffffL) :: !pending;
      Done
    in
    match rel.typ with
    (* NONE, JALR (a hint that allows turning JALR into BAL) *)
    | 0 | 37 -> Done
    | 2 -> store 4 (s + a32 ()) (* 32 *)
    (* 26: the 26-bit word index of J/JAL at 0-25. The jump stays in the
       256MiB region of P + 4, so for a local symbol the addend is an
       index in that region (hence 0xf0000000), and for an external one
       it is a sign-extended offset. *)
    | 4 ->
        let insn = ld 0 4 in
        let a = if rel.explicit then site.a else (insn land 0x3ffffffL) lsl 2 in
        let target =
          if is_local sym then (a lor ((p + 4L) land 0xf0000000L)) + s
          else sext a 28 + s
        in
        store 4 (set_bits insn 0 26 (target lsr 2))
    | 5 -> defer () (* HI16 *)
    (* GOT16 of a local symbol: the GOT entry holds the 64KiB page of the
       address, and the paired LO16 adds the rest *)
    | 9 when is_local sym -> defer ()
    (* GOT16 of a global symbol, CALL16: G(S) - GP *)
    | 9 | 11 -> store 4 (set_lo16 (ld 0 4) (env.got s - gp))
    (* LO16. For _gp_disp the HI16/LO16 pair loads GP - P relative to the
       HI16 (lui) instruction, which is 4 bytes before the LO16 one. *)
    | 6 ->
        let lo = a16 () in
        flush ~lo rel.symbol;
        let s = if is_gp_disp sym then gp - p + 4L else s in
        store 4 (set_lo16 (ld 0 4) (s + lo))
    | 7 -> store 4 (set_lo16 (ld 0 4) (s + a16 () - gp)) (* GPREL16 *)
    (* PC16: the 16-bit word offset of the branches *)
    | 10 ->
        let insn = ld 0 4 in
        let a = sext ((insn land 0xffffL) lsl 2) 18 in
        store 4 (set_lo16 insn ((s + a - p) asr 2))
    | 12 -> store 4 (s + a32 () - gp) (* GPREL32 *)
    | 248 -> store 4 (s + a32 () - p) (* PC32 *)
    | _ -> Unsupported
  in
  (* the HI16 relocations without a matching LO16 use ALO = 0 *)
  let finish () =
    List.map !pending ~f:(fun (site, _) -> site.rel.symbol)
    |> List.dedup_and_sort ~compare:Int.compare
    |> List.iter ~f:(flush ~lo:0L)
  in
  { prescan = ignore; apply; finish }

(* RISC-V ELF psABI, all relocations are RELA. Linker relaxation is not
   done, so the code keeps its size and R_RISCV_RELAX and R_RISCV_ALIGN
   are ignored. *)
let riscv env =
  let open Int64 in
  (* The pc-relative values of the AUIPC instructions by their addresses.
     A PCREL_LO12 relocation refers to the label of its AUIPC rather than
     to the target, so they are collected before the relocations are
     applied. *)
  let hi = Hashtbl.create (module Int64) in
  let prescan { rel; p; s; a; _ } =
    match rel.typ with
    | 20 -> Hashtbl.set hi ~key:p ~data:(env.got s + a - p) (* GOT_HI20 *)
    | 23 -> Hashtbl.set hi ~key:p ~data:(s + a - p) (* PCREL_HI20 *)
    | _ -> ()
  in
  let bit x n = bits x n 1 in
  (* The immediates of the instruction formats, see the "Base Instruction
     Formats" of the unprivileged ISA. The masks keep the opcode and the
     register fields. *)
  (* U (LUI, AUIPC): imm[31:12] at 12-31. 0x800 rounds the upper part
     to compensate for the sign extension of the paired 12-bit low part. *)
  let utype v insn = set_bits insn 12 20 ((v + 0x800L) asr 12) in
  (* I (ADDI, loads, JALR): imm[11:0] at 20-31 *)
  let itype v insn = set_bits insn 20 12 v in
  (* S (stores): imm[11:5] at 25-31, imm[4:0] at 7-11 *)
  let stype v insn = set_bits (set_bits insn 25 7 (v lsr 5)) 7 5 v in
  (* B (branches): imm[12|10:5] at 25-31, imm[4:1|11] at 7-11, the mask
     0x1fff07f keeps rs2, rs1, funct3, and the opcode *)
  let btype v insn =
    insn land 0x1fff07fL
    lor (bit v 12 lsl 31)
    lor (bits v 5 6 lsl 25)
    lor (bits v 1 4 lsl 8)
    lor (bit v 11 lsl 7)
  in
  (* J (JAL): imm[20|10:1|11|19:12] at 12-31, the mask 0xfff keeps rd and
     the opcode *)
  let jtype v insn =
    insn land 0xfffL
    lor (bit v 20 lsl 31)
    lor (bits v 1 10 lsl 21)
    lor (bit v 11 lsl 20)
    lor (bits v 12 8 lsl 12)
  in
  (* CB (C.BEQZ, C.BNEZ): offset[8|4:3] at 10-12, offset[7:6|2:1|5] at
     2-6, the mask 0xe383 keeps funct3, rs1', and the opcode *)
  let cbtype v insn =
    insn land 0xe383L
    lor (bit v 8 lsl 12)
    lor (bits v 3 2 lsl 10)
    lor (bits v 6 2 lsl 5)
    lor (bits v 1 2 lsl 3)
    lor (bit v 5 lsl 2)
  in
  (* CJ (C.J, C.JAL): offset[11|4|9:8|10|6|7|3:1|5] at 2-12, the mask
     0xe003 keeps funct3 and the opcode *)
  let cjtype v insn =
    insn land 0xe003L
    lor (bit v 11 lsl 12)
    lor (bit v 4 lsl 11)
    lor (bits v 8 2 lsl 9)
    lor (bit v 10 lsl 8)
    lor (bit v 6 lsl 7)
    lor (bit v 7 lsl 6)
    lor (bits v 1 3 lsl 3)
    lor (bit v 5 lsl 2)
  in
  (* rewrites the ULEB128 number at the place in its existing length, a
     64-bit number takes at most 10 bytes *)
  let uleb site f =
    let rec length n =
      if Int.(n >= 9) || site.ld n 1 land 0x80L = 0L then Int.(n + 1)
      else length Int.(n + 1)
    in
    let n = length 0 in
    let old =
      List.init n ~f:Fn.id
      |> List.fold ~init:0L ~f:(fun x i ->
          x lor ((site.ld i 1 land 0x7fL) lsl Int.(7 * i)))
    in
    let v = f old in
    for i = 0 to Int.(n - 1) do
      let more = if Int.(i < n - 1) then 0x80L else 0L in
      site.st i 1 (bits v Int.(7 * i) 7 lor more)
    done;
    Done
  in
  let apply ({ rel; p; s; a; ld; _ } as site) =
    let store = store site and update f = update_insn site f in
    let update16 f =
      site.sti 0 2 (f (site.ldi 0 2));
      Done
    in
    (* here S is the address of the AUIPC that computes the high part *)
    let pcrel_lo f =
      match Hashtbl.find hi s with
      | Some v -> update (f v)
      | None -> Unsupported
    in
    let x = s + a in
    match rel.typ with
    | 0 | 43 | 51 -> Done (* NONE, ALIGN, RELAX *)
    | 1 -> store 4 x (* 32 *)
    | 2 -> store 8 x (* 64 *)
    | 16 -> update (btype (x - p)) (* BRANCH *)
    | 17 -> update (jtype (x - p)) (* JAL *)
    (* CALL, CALL_PLT: an AUIPC and JALR pair *)
    | 18 | 19 ->
        let v = x - p in
        site.sti 0 4 (utype v (site.ldi 0 4));
        site.sti 4 4 (itype v (site.ldi 4 4));
        Done
    | 20 | 23 ->
        update (utype (Hashtbl.find_exn hi p)) (* GOT_HI20, PCREL_HI20 *)
    | 24 -> pcrel_lo itype (* PCREL_LO12_I *)
    | 25 -> pcrel_lo stype (* PCREL_LO12_S *)
    | 26 -> update (utype x) (* HI20 *)
    | 27 -> update (itype x) (* LO12_I *)
    | 28 -> update (stype x) (* LO12_S *)
    (* ADD8, ADD16, ADD32, ADD64, SUB8, SUB16, SUB32, SUB64: they come in
       pairs that compute the difference of two symbols in place *)
    | 33 -> store 1 (ld 0 1 + x)
    | 34 -> store 2 (ld 0 2 + x)
    | 35 -> store 4 (ld 0 4 + x)
    | 36 -> store 8 (ld 0 8 + x)
    | 37 -> store 1 (ld 0 1 - x)
    | 38 -> store 2 (ld 0 2 - x)
    | 39 -> store 4 (ld 0 4 - x)
    | 40 -> store 8 (ld 0 8 - x)
    | 41 -> store 4 (env.got s + a - p) (* GOT32_PCREL *)
    | 44 -> update16 (cbtype (x - p)) (* RVC_BRANCH *)
    | 45 -> update16 (cjtype (x - p)) (* RVC_JUMP *)
    (* SUB6, SET6: the low 6 bits of a byte, as used in DWARF call frame
       instructions *)
    | 52 -> store 1 (set_bits (ld 0 1) 0 6 (ld 0 1 - x))
    | 53 -> store 1 (set_bits (ld 0 1) 0 6 x)
    | 54 -> store 1 x (* SET8 *)
    | 55 -> store 2 x (* SET16 *)
    | 56 -> store 4 x (* SET32 *)
    | 57 | 59 -> store 4 (x - p) (* 32_PCREL, PLT32 *)
    | 60 -> uleb site (fun _ -> x) (* SET_ULEB128 *)
    | 61 -> uleb site (fun old -> old - x) (* SUB_ULEB128 *)
    | _ -> Unsupported
  in
  { prescan; apply; finish = Fn.id }

(* PowerPC and PowerPC64 psABI, the relocations are RELA, the ones of
   the TOC are not applied, as there is no TOC, e.g., the second words of
   the function descriptors of the ELFv1 ABI *)
let powerpc _env =
  simple @@ fun ({ rel; p; s; a; _ } as site) ->
  let open Int64 in
  let store = store site and update f = update_insn site f in
  let x = s + a in
  let lo x = x land 0xffffL
  and hi x = (x asr 16) land 0xffffL
  and ha x = ((x + 0x8000L) asr 16) land 0xffffL in
  match rel.typ with
  | 0 -> Done (* NONE *)
  | 1 -> store 4 x (* ADDR32 *)
  | 2 ->
      update (fun i -> i land 0xfc000003L lor (x land 0x3fffffcL)) (* ADDR24 *)
  | 3 | 4 -> store 2 (lo x) (* ADDR16, ADDR16_LO *)
  | 5 -> store 2 (hi x) (* ADDR16_HI *)
  | 6 -> store 2 (ha x) (* ADDR16_HA *)
  | 7 -> update (fun i -> i land 0xffff0003L lor (x land 0xfffcL)) (* ADDR14 *)
  (* REL24, PLTREL24 of PowerPC, the branches and the calls *)
  | 10 | 18 ->
      update (fun i -> i land 0xfc000003L lor ((x - p) land 0x3fffffcL))
  | 11 ->
      update (fun i -> i land 0xffff0003L lor ((x - p) land 0xfffcL))
      (* REL14 *)
  | 26 -> store 4 (x - p) (* REL32 *)
  | 38 -> store 8 x (* ADDR64 *)
  | 44 -> store 8 (x - p) (* REL64 *)
  | _ -> Unsupported

let handler { machine; width; _ } =
  match machine with
  | m when m = Elf.em_x86_64 -> Some x86_64
  | m when m = Elf.em_386 -> Some i386
  | m when m = Elf.em_aarch64 -> Some aarch64
  | m when m = Elf.em_arm -> Some arm
  | m when m = Elf.em_mips && width = 32 -> Some mips
  | m when m = Elf.em_riscv -> Some riscv
  | m when m = Elf.em_ppc || m = Elf.em_ppc64 -> Some powerpc
  | _ -> None

let null_symbol =
  {
    name = "";
    shndx = Elf.shn_undef;
    extended = false;
    value = 0L;
    size = 0L;
    typ = 0;
    bind = 0;
  }

(* [special sym shn] the symbol has the special section index [shn],
   an extended index is never special *)
let special (sym : symbol) shn = (not sym.extended) && sym.shndx = shn

(* the offsets from the GOT of the symbols defined by the linker *)
let linker_symbol machine (sym : symbol) =
  match sym.name with
  | "_GLOBAL_OFFSET_TABLE_" -> Some 0L
  | ("_gp" | "_gp_disp" | "__gnu_local_gp") when machine = Elf.em_mips ->
      Some mips_gp_offset
  | _ -> None

let is_external machine (sym : symbol) =
  special sym Elf.shn_undef
  && (not (String.is_empty sym.name))
  && Option.is_none (linker_symbol machine sym)

let link input =
  let open Int64 in
  let module Map = Core.Map in
  let warnings = ref [] in
  let warn fmt = ksprintf (fun s -> warnings := s :: !warnings) fmt in
  let word = Int.(input.width / 8) in
  let wordsize = of_int word in
  let mem = Memory.create input.data in
  (* AArch64 instructions are always little endian *)
  let code_little = input.little || Int.(input.machine = Elf.em_aarch64) in
  let cursor = ref input.base in
  let place size align =
    let addr = align_up !cursor align in
    cursor := addr + size;
    addr
  in
  let synthetic ?off ?(w = false) name start =
    if !cursor > start then
      Some
        {
          name;
          addr = start;
          size = !cursor - start;
          off;
          r = true;
          w;
          x = false;
          is_section = false;
        }
    else None
  in
  let sections =
    List.sort input.sections ~compare:(fun (x : section) y ->
        Int.compare x.index y.index)
  in
  let section_addrs = Hashtbl.create (module Int) in
  let section_regions =
    List.filter_map sections ~f:(fun sec ->
        if not (has sec.flags Elf.shf_alloc) then None
        else
          let addr = place sec.size sec.align in
          Hashtbl.set section_addrs ~key:sec.index ~data:addr;
          Option.some_if (sec.size > 0L)
            {
              name = sec.name;
              addr;
              size = sec.size;
              off = Option.some_if Int.(sec.typ <> Elf.sht_nobits) sec.off;
              r = true;
              w = has sec.flags Elf.shf_write;
              x = has sec.flags Elf.shf_execinstr;
              is_section = true;
            })
  in
  cursor := align_up !cursor wordsize;
  let commons_start = !cursor in
  let commons = Hashtbl.create (module Int) in
  Map.iteri input.symbols ~f:(fun ~key ~data:sym ->
      if special sym Elf.shn_common then
        Hashtbl.set commons ~key ~data:(place sym.size sym.value));
  let commons_region = synthetic ~w:true "%common" commons_start in
  cursor := align_up !cursor wordsize;
  let externals_start = !cursor in
  let externals = Hashtbl.create (module String) in
  Map.iter input.symbols ~f:(fun sym ->
      if is_external input.machine sym && not (Hashtbl.mem externals sym.name)
      then Hashtbl.set externals ~key:sym.name ~data:(place wordsize wordsize));
  let externals_region = synthetic "EXTERNAL" externals_start in
  cursor := align_up !cursor wordsize;
  let got_base = !cursor in
  let got_off = Memory.length mem in
  let got_entries = Hashtbl.create (module Int64) in
  let got value =
    Hashtbl.find_or_add got_entries value ~default:(fun () ->
        let slot = place wordsize wordsize in
        Memory.write mem ~little:input.little
          (got_off + slot - got_base)
          word value;
        slot)
  in
  let resolve index (sym : symbol) =
    if special sym Elf.shn_undef then
      if String.is_empty sym.name then Some 0L
      else
        match linker_symbol input.machine sym with
        | Some off -> Some (got_base + off)
        | None -> Hashtbl.find externals sym.name
    else if special sym Elf.shn_abs then Some sym.value
    else if special sym Elf.shn_common then Hashtbl.find commons index
    else if (not sym.extended) && Int.(sym.shndx >= Elf.shn_loreserve) then None
    else
      Hashtbl.find section_addrs sym.shndx
      |> Option.map ~f:(fun addr -> addr + sym.value)
  in
  (* the relocated sections, i.e., the allocated sections with contents *)
  let section_table =
    let table = Hashtbl.create (module Int) in
    List.iter sections ~f:(fun sec ->
        if
          Hashtbl.mem section_addrs sec.index && Int.(sec.typ <> Elf.sht_nobits)
        then Hashtbl.set table ~key:sec.index ~data:sec);
    table
  in
  let references = ref [] in
  (* the site of the relocation, which is made anew for each pass over
     the relocations, so that only one is live, as a file may have
     millions of them, e.g., a kernel module; the first pass [report]s
     the relocations, that are not applied, and the external references *)
  let site_of ~report rel =
    match
      ( Hashtbl.find section_table rel.section,
        Hashtbl.find section_addrs rel.section )
    with
    | Some sec, Some base -> (
        let sym =
          Map.find input.symbols rel.symbol |> Option.value ~default:null_symbol
        in
        let p = base + rel.offset in
        let off = sec.off + rel.offset in
        match resolve rel.symbol sym with
        | _ when rel.offset < 0L || rel.offset >= sec.size ->
            if report then
              warn "relocation at %Lx is outside of the section %s" p sec.name;
            None
        | None ->
            if report then
              warn "unable to resolve the symbol %S referenced at %Lx" sym.name
                p;
            None
        | Some s ->
            if report && is_external input.machine sym then
              references := (p, sym.name) :: !references;
            (* the accessed bytes must lie inside of the section and
               of the file, otherwise they would clobber the
               neighboring section or the GOT, which is stored past
               the end of the file *)
            let check at n =
              let at = rel.offset + of_int at in
              if
                at < 0L
                || at + of_int n > sec.size
                || sec.off + at + of_int n > Memory.length mem
              then raise (Outside_of_section (p, sec.name))
            in
            let ld little at n =
              check at n;
              Memory.read mem ~little (off + of_int at) n
            and st little at n x =
              check at n;
              Memory.write mem ~little (off + of_int at) n x
            in
            Some
              {
                rel;
                sym;
                p;
                s;
                a = (if rel.explicit then rel.addend else 0L);
                ld = ld input.little;
                st = st input.little;
                ldi = ld code_little;
                sti = st code_little;
              })
    | _ -> None
  in
  let each_site ~report f =
    List.iter input.relocations ~f:(fun rel ->
        Option.iter (site_of ~report rel) ~f)
  in
  (match handler input with
  | None ->
      let relocated = ref false in
      each_site ~report:true (fun _ -> relocated := true);
      if !relocated then
        warn
          "relocations of the machine %d are not supported, the code is left \
           unrelocated"
          input.machine
  | Some create ->
      let h = create { got; got_base } in
      let guard f x =
        try f x
        with Outside_of_section (p, name) ->
          warn "relocation at %Lx accesses data outside of the section %s" p
            name
      in
      each_site ~report:true (guard h.prescan);
      let unsupported = Hashtbl.create (module Int) in
      each_site ~report:false
        (guard (fun site ->
             match h.apply site with
             | Done -> ()
             | Unsupported -> Hashtbl.incr unsupported site.rel.typ));
      guard h.finish ();
      Hashtbl.iteri unsupported ~f:(fun ~key ~data ->
          warn "%d relocations of type %d (machine %d) were not applied" data
            key input.machine));
  let got_region = synthetic ~off:got_off ~w:true "%got" got_base in
  (* the functions of the ELFv1 ABI of PowerPC64 are their descriptors in
     .opd, whose first words, that are relocated, are their code *)
  let descriptor (sym : symbol) =
    match Hashtbl.find section_table sym.shndx with
    | Some sec
      when Int.(input.machine = Elf.em_ppc64)
           && String.equal sec.name ".opd"
           && sym.value + 8L <= sec.size ->
        Some (Memory.read mem ~little:input.little (sec.off + sym.value) 8)
    | _ -> None
  in
  let functions =
    Map.fold_right input.symbols ~init:[] ~f:(fun ~key ~data:sym acc ->
        let is_code = is_function sym && not (String.is_empty sym.name) in
        match resolve key sym with
        | Some value
          when is_code
               && (sym.extended || Int.(sym.shndx < Elf.shn_loreserve))
               && Hashtbl.mem section_addrs sym.shndx -> (
            match descriptor sym with
            | Some code -> (sym.name, code, 0L, code) :: acc
            | None ->
                let addr =
                  if Int.(input.machine = Elf.em_arm) then value land lnot 1L
                  else value
                in
                (sym.name, addr, sym.size, value) :: acc)
        | _ -> acc)
  in
  {
    regions =
      section_regions
      @ List.filter_opt [ commons_region; externals_region; got_region ];
    functions;
    references = List.rev !references;
    patches = Memory.patches mem;
    warnings = List.rev !warnings;
  }
