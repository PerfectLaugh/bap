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
  patches : (int64 * int * int64) list;
  warnings : string list;
}

module Elf = struct
  let shf_write = 0x1L
  let shf_alloc = 0x2L
  let shf_execinstr = 0x4L
  let sht_nobits = 8
  let shn_undef = 0
  let shn_loreserve = 0xff00
  let shn_abs = 0xfff1
  let shn_common = 0xfff2
  let stt_func = 2
  let stt_gnu_ifunc = 10
  let stb_local = 0
  let em_386 = 3
  let em_mips = 8
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

(* The contents of the file with the relocations applied, only
   the modified bytes are stored. The bytes past the end of the
   file are zeros. *)
module Memory = struct
  type t = { data : Bigstring.t; bytes : (int64, int) Hashtbl.t }

  let create data = { data; bytes = Hashtbl.create (module Int64) }
  let length t = Int64.of_int (Bigstring.length t.data)

  let get t off =
    match Hashtbl.find t.bytes off with
    | Some b -> b
    | None when Int64.(off >= 0L && off < length t) ->
        Char.to_int (Bigstring.get t.data (Int64.to_int_exn off))
    | None -> 0

  let set t off b = Hashtbl.set t.bytes ~key:off ~data:(b land 0xff)
  let shift ~little n i = 8 * if little then i else n - i - 1

  let read t ~little off n =
    List.init n ~f:Fn.id
    |> List.fold ~init:0L ~f:(fun acc i ->
        let b = Int64.of_int (get t Int64.(off + of_int i)) in
        Int64.(acc lor (b lsl shift ~little n i)))

  let write t ~little off n v =
    for i = 0 to n - 1 do
      let b = Int64.((v lsr shift ~little n i) land 0xffL) in
      set t Int64.(off + of_int i) (Int64.to_int_exn b)
    done

  (* groups the modified bytes into runs of at most eight bytes *)
  let patches t ~little =
    let emit (start, len) = (start, len, read t ~little start len) in
    Hashtbl.keys t.bytes
    |> List.sort ~compare:Int64.compare
    |> List.fold ~init:([], None) ~f:(fun (acc, run) off ->
        match run with
        | Some (start, len) when len < 8 && Int64.(start + of_int len = off) ->
            (acc, Some (start, len + 1))
        | Some run -> (emit run :: acc, Some (off, 1))
        | None -> (acc, Some (off, 1)))
    |> function
    | acc, None -> List.rev acc
    | acc, Some run -> List.rev (emit run :: acc)
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

let x86_64 env =
  simple @@ fun ({ rel; sym; p; s; a; _ } as site) ->
  let open Int64 in
  let store = store site in
  match rel.typ with
  | 0 -> Done
  | 1 -> store 8 (s + a)
  | 2 | 4 -> store 4 (s + a - p)
  | 3 -> store 4 (env.got s - env.got_base + a)
  | 9 | 41 | 42 | 43 -> store 4 (env.got s + a - p)
  | 10 | 11 -> store 4 (s + a)
  | 12 -> store 2 (s + a)
  | 13 -> store 2 (s + a - p)
  | 14 -> store 1 (s + a)
  | 15 -> store 1 (s + a - p)
  | 24 -> store 8 (s + a - p)
  | 25 -> store 8 (s + a - env.got_base)
  | 26 -> store 4 (env.got_base + a - p)
  | 27 -> store 8 (env.got s - env.got_base + a)
  | 28 -> store 8 (env.got s + a - p)
  | 29 -> store 8 (env.got_base + a - p)
  | 32 -> store 4 (sym.size + a)
  | 33 -> store 8 (sym.size + a)
  | _ -> Unsupported

let i386 env =
  simple @@ fun ({ rel; p; s; _ } as site) ->
  let open Int64 in
  let store = store site in
  let a n = if rel.explicit then site.a else sext (site.ld 0 n) Int.(8 * n) in
  match rel.typ with
  | 0 -> Done
  | 1 -> store 4 (s + a 4)
  | 2 | 4 -> store 4 (s + a 4 - p)
  | 3 | 43 -> store 4 (env.got s + a 4 - env.got_base)
  | 9 -> store 4 (s + a 4 - env.got_base)
  | 10 -> store 4 (env.got_base + a 4 - p)
  | 20 -> store 2 (s + a 2)
  | 21 -> store 2 (s + a 2 - p)
  | 22 -> store 1 (s + a 1)
  | 23 -> store 1 (s + a 1 - p)
  | _ -> Unsupported

let aarch64 env =
  simple @@ fun ({ rel; p; s; a; _ } as site) ->
  let open Int64 in
  let store = store site and update = update_insn site in
  let page x = x land lnot 0xfffL in
  let adr v insn = set_bits (set_bits insn 29 2 v) 5 19 (v asr 2) in
  let lo12 shift v =
    update (fun insn -> set_bits insn 10 12 ((v land 0xfffL) asr shift))
  in
  let x = s + a in
  match rel.typ with
  | 0 -> Done
  | 0x101 -> store 8 x
  | 0x102 -> store 4 x
  | 0x103 -> store 2 x
  | 0x104 -> store 8 (x - p)
  | 0x105 | 0x13a -> store 4 (x - p)
  | 0x106 -> store 2 (x - p)
  | t when Int.(t >= 0x107 && t <= 0x10d) ->
      let shift = Int.((t - 0x107) / 2 * 16) in
      update (fun insn -> set_bits insn 5 16 (x asr shift))
  | 0x111 | 0x118 -> update (fun insn -> set_bits insn 5 19 ((x - p) asr 2))
  | 0x112 -> update (adr (x - p))
  | 0x113 | 0x114 -> update (adr ((page x - page p) asr 12))
  | 0x115 | 0x116 -> lo12 0 x
  | 0x117 -> update (fun insn -> set_bits insn 5 14 ((x - p) asr 2))
  | 0x11a | 0x11b -> update (fun insn -> set_bits insn 0 26 ((x - p) asr 2))
  | 0x11c -> lo12 1 x
  | 0x11d -> lo12 2 x
  | 0x11e -> lo12 3 x
  | 0x12b -> lo12 4 x
  | 0x135 -> update (fun insn -> set_bits insn 5 19 ((env.got x - p) asr 2))
  | 0x137 -> update (adr ((page (env.got x) - page p) asr 12))
  | 0x138 -> lo12 3 (env.got x)
  | 0x13b -> store 4 (env.got s + a - p)
  | _ -> Unsupported

let is_function (sym : symbol) =
  sym.typ = Elf.stt_func || sym.typ = Elf.stt_gnu_ifunc

let is_thumb (sym : symbol) = is_function sym && Int64.(sym.value land 1L = 1L)

let arm env =
  simple @@ fun ({ rel; sym; p; ld; _ } as site) ->
  let open Int64 in
  let store = store site in
  let thumb = is_thumb sym in
  let t = if thumb then 1L else 0L in
  let s = site.s land lnot t in
  let addend decoded = if rel.explicit then site.a else decoded in
  let a32 () = addend (sext (ld 0 4) 32) in
  (* the 16-bit immediate of MOVW/MOVT *)
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
  let arm_movw typ =
    let insn = ld 0 4 in
    let imm = (insn lsr 4) land 0xf000L lor (insn land 0xfffL) in
    let v = movw typ imm in
    store 4
      (insn land 0xfff0f000L lor ((v land 0xf000L) lsl 4) lor (v land 0xfffL))
  in
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
  (* BL, BLX, and B.W *)
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
  (* the conditional B.W *)
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
  let thumb_short_branch n =
    let hw = ld 0 2 in
    let a = addend (sext ((hw land mask n) lsl 1) Int.(n + 1)) in
    store 2 (hw land lnot (mask n) lor bits (s + a - p) 1 n)
  in
  match rel.typ with
  | 0 | 0x28 -> Done
  | 1 | 0x1c | 0x1d -> arm_branch ()
  | 2 | 0x26 -> store 4 ((s + a32 ()) lor t)
  | 3 | 0x29 -> store 4 (((s + a32 ()) lor t) - p)
  | 5 -> store 2 (s + addend (sext (ld 0 2) 16))
  | 8 -> store 1 (s + addend (sext (ld 0 1) 8))
  | 0xa | 0x1e -> thumb_branch ()
  | 0x18 -> store 4 (s + a32 () - env.got_base)
  | 0x19 -> store 4 (env.got_base + a32 () - p)
  | 0x1a -> store 4 (env.got (s lor t) + a32 () - env.got_base)
  | 0x2a ->
      let old = ld 0 4 in
      let a = addend (sext (old land 0x7fffffffL) 31) in
      store 4 (old land 0x80000000L lor ((((s + a) lor t) - p) land 0x7fffffffL))
  | 0x2b -> arm_movw `abs_lo
  | 0x2c -> arm_movw `abs_hi
  | 0x2d -> arm_movw `rel_lo
  | 0x2e -> arm_movw `rel_hi
  | 0x2f -> thumb_movw `abs_lo
  | 0x30 -> thumb_movw `abs_hi
  | 0x31 -> thumb_movw `rel_lo
  | 0x32 -> thumb_movw `rel_hi
  | 0x33 -> thumb_jump19 ()
  | 0x60 -> store 4 (env.got (s lor t) + a32 () - p)
  | 0x66 -> thumb_short_branch 11
  | 0x67 -> thumb_short_branch 8
  | _ -> Unsupported

let mips_gp_offset = 0x7ff0L

(* MIPS o32: the HI16 (and local GOT16) relocations are applied when
   the matching LO16 relocation is found, since they share the addend. *)
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
    | 0 | 37 -> Done
    | 2 -> store 4 (s + a32 ())
    | 4 ->
        let insn = ld 0 4 in
        let a = if rel.explicit then site.a else (insn land 0x3ffffffL) lsl 2 in
        let target =
          if is_local sym then (a lor ((p + 4L) land 0xf0000000L)) + s
          else sext a 28 + s
        in
        store 4 (set_bits insn 0 26 (target lsr 2))
    | 5 -> defer ()
    | 9 when is_local sym -> defer ()
    | 9 | 11 -> store 4 (set_lo16 (ld 0 4) (env.got s - gp))
    | 6 ->
        let lo = a16 () in
        flush ~lo rel.symbol;
        let s = if is_gp_disp sym then gp - p + 4L else s in
        store 4 (set_lo16 (ld 0 4) (s + lo))
    | 7 -> store 4 (set_lo16 (ld 0 4) (s + a16 () - gp))
    | 10 ->
        let insn = ld 0 4 in
        let a = sext ((insn land 0xffffL) lsl 2) 18 in
        store 4 (set_lo16 insn ((s + a - p) asr 2))
    | 12 -> store 4 (s + a32 () - gp)
    | 248 -> store 4 (s + a32 () - p)
    | _ -> Unsupported
  in
  let finish () =
    List.map !pending ~f:(fun (site, _) -> site.rel.symbol)
    |> List.dedup_and_sort ~compare:Int.compare
    |> List.iter ~f:(flush ~lo:0L)
  in
  { prescan = ignore; apply; finish }

let riscv env =
  let open Int64 in
  (* the pc-relative values of the AUIPC instructions by their addresses *)
  let hi = Hashtbl.create (module Int64) in
  let prescan { rel; p; s; a; _ } =
    match rel.typ with
    | 20 -> Hashtbl.set hi ~key:p ~data:(env.got s + a - p)
    | 23 -> Hashtbl.set hi ~key:p ~data:(s + a - p)
    | _ -> ()
  in
  let bit x n = bits x n 1 in
  let utype v insn = set_bits insn 12 20 ((v + 0x800L) asr 12) in
  let itype v insn = set_bits insn 20 12 v in
  let stype v insn = set_bits (set_bits insn 25 7 (v lsr 5)) 7 5 v in
  let btype v insn =
    insn land 0x1fff07fL
    lor (bit v 12 lsl 31)
    lor (bits v 5 6 lsl 25)
    lor (bits v 1 4 lsl 8)
    lor (bit v 11 lsl 7)
  in
  let jtype v insn =
    insn land 0xfffL
    lor (bit v 20 lsl 31)
    lor (bits v 1 10 lsl 21)
    lor (bit v 11 lsl 20)
    lor (bits v 12 8 lsl 12)
  in
  let cbtype v insn =
    insn land 0xe383L
    lor (bit v 8 lsl 12)
    lor (bits v 3 2 lsl 10)
    lor (bits v 6 2 lsl 5)
    lor (bits v 1 2 lsl 3)
    lor (bit v 5 lsl 2)
  in
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
  let uleb site f =
    let rec length n =
      if Int.(n >= 10) || site.ld n 1 land 0x80L = 0L then Int.(n + 1)
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
    let pcrel_lo f =
      match Hashtbl.find hi s with
      | Some v -> update (f v)
      | None -> Unsupported
    in
    let x = s + a in
    match rel.typ with
    | 0 | 43 | 51 -> Done
    | 1 -> store 4 x
    | 2 -> store 8 x
    | 16 -> update (btype (x - p))
    | 17 -> update (jtype (x - p))
    | 18 | 19 ->
        let v = x - p in
        site.sti 0 4 (utype v (site.ldi 0 4));
        site.sti 4 4 (itype v (site.ldi 4 4));
        Done
    | 20 | 23 -> update (utype (Hashtbl.find_exn hi p))
    | 24 -> pcrel_lo itype
    | 25 -> pcrel_lo stype
    | 26 -> update (utype x)
    | 27 -> update (itype x)
    | 28 -> update (stype x)
    | 33 -> store 1 (ld 0 1 + x)
    | 34 -> store 2 (ld 0 2 + x)
    | 35 -> store 4 (ld 0 4 + x)
    | 36 -> store 8 (ld 0 8 + x)
    | 37 -> store 1 (ld 0 1 - x)
    | 38 -> store 2 (ld 0 2 - x)
    | 39 -> store 4 (ld 0 4 - x)
    | 40 -> store 8 (ld 0 8 - x)
    | 41 -> store 4 (env.got s + a - p)
    | 44 -> update16 (cbtype (x - p))
    | 45 -> update16 (cjtype (x - p))
    | 52 -> store 1 (set_bits (ld 0 1) 0 6 (ld 0 1 - x))
    | 53 -> store 1 (set_bits (ld 0 1) 0 6 x)
    | 54 -> store 1 x
    | 55 -> store 2 x
    | 56 -> store 4 x
    | 57 | 59 -> store 4 (x - p)
    | 60 -> uleb site (fun _ -> x)
    | 61 -> uleb site (fun old -> old - x)
    | _ -> Unsupported
  in
  { prescan; apply; finish = Fn.id }

let handler { machine; width; _ } =
  match machine with
  | m when m = Elf.em_x86_64 -> Some x86_64
  | m when m = Elf.em_386 -> Some i386
  | m when m = Elf.em_aarch64 -> Some aarch64
  | m when m = Elf.em_arm -> Some arm
  | m when m = Elf.em_mips && width = 32 -> Some mips
  | m when m = Elf.em_riscv -> Some riscv
  | _ -> None

let null_symbol =
  { name = ""; shndx = Elf.shn_undef; value = 0L; size = 0L; typ = 0; bind = 0 }

(* the offsets from the GOT of the symbols defined by the linker *)
let linker_symbol machine (sym : symbol) =
  match sym.name with
  | "_GLOBAL_OFFSET_TABLE_" -> Some 0L
  | ("_gp" | "_gp_disp" | "__gnu_local_gp") when machine = Elf.em_mips ->
      Some mips_gp_offset
  | _ -> None

let is_external machine (sym : symbol) =
  sym.shndx = Elf.shn_undef
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
      if Int.(sym.shndx = Elf.shn_common) then
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
    if Int.(sym.shndx = Elf.shn_undef) then
      if String.is_empty sym.name then Some 0L
      else
        match linker_symbol input.machine sym with
        | Some off -> Some (got_base + off)
        | None -> Hashtbl.find externals sym.name
    else if Int.(sym.shndx = Elf.shn_abs) then Some sym.value
    else if Int.(sym.shndx = Elf.shn_common) then Hashtbl.find commons index
    else if Int.(sym.shndx >= Elf.shn_loreserve) then None
    else
      Hashtbl.find section_addrs sym.shndx
      |> Option.map ~f:(fun addr -> addr + sym.value)
  in
  let section_table =
    let table = Hashtbl.create (module Int) in
    List.iter sections ~f:(fun sec ->
        Hashtbl.set table ~key:sec.index ~data:sec);
    table
  in
  let references = ref [] in
  let sites =
    List.filter_map input.relocations ~f:(fun rel ->
        match
          ( Hashtbl.find section_table rel.section,
            Hashtbl.find section_addrs rel.section )
        with
        | Some sec, Some base when Int.(sec.typ <> Elf.sht_nobits) -> (
            let sym =
              Map.find input.symbols rel.symbol
              |> Option.value ~default:null_symbol
            in
            let p = base + rel.offset in
            let off = sec.off + rel.offset in
            match resolve rel.symbol sym with
            | _ when rel.offset < 0L || rel.offset >= sec.size ->
                warn "relocation at %Lx is outside of the section %s" p sec.name;
                None
            | None ->
                warn "unable to resolve the symbol %S referenced at %Lx"
                  sym.name p;
                None
            | Some s ->
                if is_external input.machine sym then
                  references := (p, sym.name) :: !references;
                let ld little at n = Memory.read mem ~little (off + of_int at) n
                and st little at n x =
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
        | _ -> None)
  in
  (match handler input with
  | None when not (List.is_empty sites) ->
      warn
        "relocations of the machine %d are not supported, the code is left \
         unrelocated"
        input.machine
  | None -> ()
  | Some create ->
      let h = create { got; got_base } in
      List.iter sites ~f:h.prescan;
      let unsupported = Hashtbl.create (module Int) in
      List.iter sites ~f:(fun site ->
          match h.apply site with
          | Done -> ()
          | Unsupported -> Hashtbl.incr unsupported site.rel.typ);
      h.finish ();
      Hashtbl.iteri unsupported ~f:(fun ~key ~data ->
          warn "%d relocations of type %d (machine %d) were not applied" data
            key input.machine));
  let got_region = synthetic ~off:got_off ~w:true "%got" got_base in
  let functions =
    Map.fold_right input.symbols ~init:[] ~f:(fun ~key ~data:sym acc ->
        let is_code = is_function sym && not (String.is_empty sym.name) in
        match resolve key sym with
        | Some value when is_code && Hashtbl.mem section_addrs sym.shndx ->
            let addr =
              if Int.(input.machine = Elf.em_arm) then value land lnot 1L
              else value
            in
            (sym.name, addr, sym.size, value) :: acc
        | _ -> acc)
  in
  {
    regions =
      section_regions
      @ List.filter_opt [ commons_region; externals_region; got_region ];
    functions;
    references = List.rev !references;
    patches = Memory.patches mem ~little:input.little;
    warnings = List.rev !warnings;
  }
