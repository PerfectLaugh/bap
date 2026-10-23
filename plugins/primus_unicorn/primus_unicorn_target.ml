open Core
open Bap_core_theory
open Bap.Std
module Uc = Bap_engine

let is_in root target =
  List.exists (target :: Theory.Target.parents target) ~f:(fun t ->
      String.equal (Theory.Target.to_string t) root)

let engine target : (Uc.arch * Uc.Mode.t) option =
  let open Uc.Mode in
  let bits = Theory.Target.bits target in
  let order =
    if Theory.Endianness.(equal eb) (Theory.Target.endianness target) then
      big_endian
    else little_endian
  in
  let is_in root = is_in root target in
  if is_in "bap:x86" then
    match bits with
    | 16 -> Some (X86, mode16)
    | 32 -> Some (X86, mode32)
    | 64 -> Some (X86, mode64)
    | _ -> None
  else if is_in "bap:arm-family" then
    if bits = 64 then Some (Arm64, arm + order)
    else if is_in "bap:armv7-m+le" || is_in "bap:armv7-m+eb" then
      Some (Arm, mclass + order)
    else Some (Arm, arm + order)
  else if is_in "bap:mips-family" then
    Some (Mips, (if bits = 64 then mips64 else mips32) + order)
  else if is_in "bap:powerpc-family" then
    (* Unicorn runs only the big-endian PowerPC *)
    if (order :> int) = (little_endian :> int) then None
    else Some (Ppc, (if bits = 64 then ppc64 else ppc32) + order)
  else if is_in "bap:riscv" then
    Some (Riscv, if bits = 64 then riscv64 else riscv32)
  else None

let reg_exn arch name =
  match Uc.reg arch name with
  | Some reg -> reg
  | None -> failwithf "Unicorn has no register %s" name ()

let pc arch (mode : Uc.Mode.t) =
  match (arch : Uc.arch) with
  | X86 ->
      if (mode :> int) = (Uc.Mode.mode64 :> int) then reg_exn arch "RIP"
      else if (mode :> int) = (Uc.Mode.mode32 :> int) then reg_exn arch "EIP"
      else reg_exn arch "IP"
  | Arm | Arm64 | Mips | Ppc | Riscv -> reg_exn arch "PC"

(* The registers of BAP, whose names differ from the names of their
   counterparts in Unicorn, or which are parts of them. A name without a
   counterpart is not synchronized, e.g., the zero registers, the
   segment selectors, and the system flags of x86, which Unicorn
   handles. The program counter is set by the executor. *)

type part =
  | Same  (** the register of Unicorn with the same name *)
  | Reg of string  (** the whole register *)
  | Bit of string * int  (** a bit of the register *)
  | Bits of string * int * int  (** the bits from [lo] of the width *)
  | Skip

let numbered prefix ?(first = 0) last f =
  List.init
    (last - first + 1)
    ~f:(fun i ->
      let n = first + i in
      (sprintf "%s%d" prefix n, f n))

let parts ~bits : Uc.arch -> (string * part) list = function
  | Arm64 ->
      numbered "R" 30 (fun n -> Reg (sprintf "X%d" n))
      @ [
          ("R31", Reg "SP");
          ("ZR", Skip);
          ("XZR", Skip);
          ("WZR", Skip);
          ("NF", Bit ("NZCV", 31));
          ("ZF", Bit ("NZCV", 30));
          ("CF", Bit ("NZCV", 29));
          ("VF", Bit ("NZCV", 28));
          ("QF", Bit ("FPSR", 27));
        ]
  | Arm ->
      (* APSR holds only the flags, so writing it keeps the mode *)
      [
        ("TPIDRURO", Reg "C13_C0_3");
        ("NF", Bit ("APSR", 31));
        ("ZF", Bit ("APSR", 30));
        ("CF", Bit ("APSR", 29));
        ("VF", Bit ("APSR", 28));
        ("QF", Bit ("APSR", 27));
      ]
  | X86 ->
      [
        ("CF", Bit ("EFLAGS", 0));
        ("PF", Bit ("EFLAGS", 2));
        ("AF", Bit ("EFLAGS", 4));
        ("ZF", Bit ("EFLAGS", 6));
        ("SF", Bit ("EFLAGS", 7));
        ("DF", Bit ("EFLAGS", 10));
        ("OF", Bit ("EFLAGS", 11));
        ("AC", Bit ("EFLAGS", 18));
        ("ID", Bit ("EFLAGS", 21));
        ("FPU_CONTROL", Reg "FPCW");
      ]
      (* MMX uses the mantissas of the physical x87 registers *)
      @ numbered "MM" 7 (fun n -> Bits (sprintf "FP%d" n, 0, 64))
      (* the bases of the segments are the MSRs of the 64-bit mode *)
      @ (if bits = 64 then [] else [ ("FS_BASE", Skip); ("GS_BASE", Skip) ])
      @ List.map
          ~f:(fun r -> (r, Skip))
          [
            "CS";
            "DS";
            "ES";
            "FS";
            "GS";
            "SS";
            "TF";
            "IF";
            "IOPLL";
            "IOPLH";
            "IOPL";
            "NT";
            "MD";
            "RF";
            "VM";
            "VIF";
            "VIP";
            "AES";
            "AI";
          ]
  | Mips ->
      ("R0", Skip)
      :: ("USERLOCAL", Reg "CP0_USERLOCAL")
         (* the condition codes of the FPU are the bits 23, and 25 to 31, of
         FCSR *)
      :: ("FCC0", Bit ("FCSR", 23))
      :: numbered "FCC" ~first:1 7 (fun n -> Bit ("FCSR", 24 + n))
      @ numbered "R" ~first:1 31 (fun n -> Reg (Int.to_string n))
      @ [ ("ZERO", Skip); ("ZERO_64", Skip) ]
  | Ppc ->
      let cr =
        List.concat
        @@ List.init 8 ~f:(fun n ->
            List.mapi [ "LT"; "GT"; "EQ"; "UN" ] ~f:(fun k bit ->
                (sprintf "CR%d%s" n bit, Bit ("CR", 31 - (4 * n) - k))))
      in
      numbered "R" 31 (fun n -> Reg (Int.to_string n))
      @ numbered "F" 31 (fun n -> Reg (sprintf "FPR%d" n))
      @ cr
      @ [
          ("SO", Bit ("XER", 31));
          ("OV", Bit ("XER", 30));
          ("CA", Bit ("XER", 29));
          ("OV32", Bit ("XER", 19));
          ("CA32", Bit ("XER", 18));
          ("C", Bit ("FPSCR", 16));
          ("FL", Bit ("FPSCR", 15));
          ("FG", Bit ("FPSCR", 14));
          ("FE", Bit ("FPSCR", 13));
          ("FU", Bit ("FPSCR", 12));
          ("ZERO", Skip);
          ("ZERO8", Skip);
        ]
  | Riscv -> [ ("X0", Skip); ("PC", Skip) ]

(* the bits [lo, lo + width) of the register of Unicorn of the size *)
type loc = { id : int; size : int; lo : int; width : int }

let bytes_of_word size x =
  let s =
    Word.enum_chars (Word.extract_exn ~hi:((size * 8) - 1) x) LittleEndian
    |> Sequence.to_list |> String.of_char_list
  in
  if Sys.big_endian then String.rev s else s

let word_of_bytes s =
  let s = if Sys.big_endian then String.rev s else s in
  Word.of_binary ~width:(String.length s * 8) LittleEndian s

let read_loc uc { id; lo; width; _ } =
  let x = word_of_bytes (Uc.reg_read_bytes uc id) in
  Word.extract_exn ~hi:(lo + width - 1) ~lo x

let write_loc uc { id; size; lo; width } x =
  let x = Word.extract_exn ~hi:(width - 1) x in
  let bits = size * 8 in
  let x =
    if lo = 0 && width = bits then x
    else
      let old = word_of_bytes (Uc.reg_read_bytes uc id) in
      let x =
        if lo = 0 then x else Word.concat x (Word.extract_exn ~hi:(lo - 1) old)
      in
      if lo + width = bits then x
      else Word.concat (Word.extract_exn ~hi:(bits - 1) ~lo:(lo + width) old) x
  in
  Uc.reg_write_bytes uc id (bytes_of_word size x)

let width_of_var v =
  match Theory.Bitv.refine (Theory.Var.sort v) with
  | Some s -> Some (Theory.Bitv.size s)
  | None ->
      (* the flags are booleans *)
      Option.map (Theory.Bool.refine (Theory.Var.sort v)) ~f:(fun _ -> 1)

module Regs = struct
  type t = {
    uc : Uc.t;
    locs : loc String.Map.t;
    vars : var list;
    basis : var list;
    owners : string String.Map.t;
    unmapped : string list;
  }

  let size uc id = try Some (Uc.reg_size uc id) with Uc.Error _ -> None

  (* the register of Unicorn, provided it has enough bits *)
  let whole uc arch name ~lo ~width =
    match Uc.reg arch name with
    | None -> None
    | Some id -> (
        match size uc id with
        | Some size when lo + width <= size * 8 -> Some { id; size; lo; width }
        | _ -> None)

  let create target arch uc =
    let parts =
      String.Map.of_alist_reduce
        (parts ~bits:(Theory.Target.bits target) arch)
        ~f:(fun x _ -> x)
    in
    let regs = Theory.Target.regs target in
    let basis name width =
      match Map.find parts name with
      | Some Skip -> None
      | Some (Reg r) -> whole uc arch r ~lo:0 ~width
      | Some (Bit (r, lo)) -> whole uc arch r ~lo ~width:1
      | Some (Bits (r, lo, width)) -> whole uc arch r ~lo ~width
      | Some Same | None -> whole uc arch name ~lo:0 ~width
    in
    (* an alias is a part of its origin, e.g., D0 of V0 of AArch64, which
       Unicorn has as the registers of their own, that share the bits, so
       that the engines, that have the registers by their identifiers,
       e.g., the lifted one, see the same bits *)
    let origin v width =
      match Theory.Target.unalias target v with
      | None -> None
      | Some origin -> (
          match Theory.Origin.cast_sub origin with
          | None -> None
          | Some sub ->
              let base = Theory.Origin.reg sub in
              let lo = Theory.Origin.lo sub in
              let bits = Theory.Bitv.size (Theory.Var.sort base) in
              Option.bind
                (basis (Theory.Var.name base) bits)
                ~f:(fun loc ->
                  if loc.lo = 0 && lo + width <= loc.width then
                    Some { loc with lo; width }
                  else None))
    in
    let locate v =
      let name = Theory.Var.name v in
      match width_of_var v with
      | None -> None
      | Some width -> (
          match origin v width with
          | Some loc when not (Map.mem parts name) -> Some loc
          | _ -> (
              match basis name width with
              | Some loc -> Some loc
              | None when Map.mem parts name -> None
              | None -> origin v width))
    in
    let locs, unmapped =
      Set.fold regs ~init:(String.Map.empty, []) ~f:(fun (locs, unmapped) v ->
          let name = Theory.Var.name v in
          match locate v with
          | Some loc -> (Map.set locs ~key:name ~data:loc, unmapped)
          | None ->
              let unmapped =
                match Map.find parts name with
                | Some Skip -> unmapped
                | _ -> name :: unmapped
              in
              (locs, unmapped))
    in
    (* the registers of the table, that the target may not declare, e.g.,
       the registers of MIPS that are the origins of the ABI names *)
    let bits = Theory.Target.bits target in
    let extra =
      Map.fold parts ~init:[] ~f:(fun ~key ~data acc ->
          if Map.mem locs key then acc
          else
            match data with
            | Reg _ -> (key, bits) :: acc
            | Bit _ -> (key, 1) :: acc
            | Same | Bits _ | Skip -> acc)
    in
    let locs =
      List.fold extra ~init:locs ~f:(fun locs (name, width) ->
          match basis name width with
          | Some loc -> Map.set locs ~key:name ~data:loc
          | None -> locs)
    in
    let is_alias name =
      match Theory.Target.var target name with
      | Some v ->
          Theory.Target.has_roles target [ Theory.Role.Register.alias ] v
      | None -> false
    in
    let basis =
      Map.fold locs ~init:[] ~f:(fun ~key ~data acc ->
          if is_alias key then acc
          else Var.create key (Type.imm data.width) :: acc)
    in
    (* the register of the basis, which holds the register *)
    let owners =
      Map.filter_map locs ~f:(fun loc ->
          List.find_map basis ~f:(fun b ->
              let name = Var.name b in
              match Map.find locs name with
              | Some b
                when b.id = loc.id && b.lo <= loc.lo
                     && loc.lo + loc.width <= b.lo + b.width ->
                  Some name
              | _ -> None))
    in
    let vars =
      Map.fold locs ~init:[] ~f:(fun ~key ~data acc ->
          Var.create key (Type.imm data.width) :: acc)
    in
    { uc; locs; vars; basis; owners; unmapped = List.rev unmapped }

  let basis t = t.basis
  let vars t = t.vars
  let owner t name = Map.find t.owners name

  let find { locs; _ } v =
    match Map.find locs (Var.name v) with
    | Some loc
      when match Var.typ v with
           | Type.Imm width -> width = loc.width
           | _ -> false ->
        Some loc
    | _ -> None

  let mem t v = Option.is_some (find t v)
  let read t v = Option.map (find t v) ~f:(read_loc t.uc)

  let write t v x =
    match find t v with
    | None -> false
    | Some loc ->
        write_loc t.uc loc x;
        true

  let unmapped t = t.unmapped
  let read_name t name = Option.map (Map.find t.locs name) ~f:(read_loc t.uc)

  let write_name t name x =
    match Map.find t.locs name with
    | None -> false
    | Some loc ->
        write_loc t.uc loc (Word.extract_exn ~hi:(loc.width - 1) x);
        true

  let names t = Map.keys t.locs

  let locate t name =
    Option.map (Map.find t.locs name) ~f:(fun { id; lo; width; _ } ->
        (id, lo, width))
end

(* The bases of the segments of x86 in the protected mode, e.g., of FS,
   which the programs of Windows read their thread environment block
   through, are in the descriptors of the global descriptor table, which
   Unicorn loads, when the selectors are written, unlike the bases of
   the 64-bit mode, which are its registers. The table is mapped at
   [gdt_base], with the FS and the GS segments in its entries 1 and 2, and
   the flat stack segment in the entry 3, as loading a selector makes
   Unicorn take the size of the stack from the descriptor of SS. *)
module Segments = struct
  let gdt_base = 0xFFFE_0000L
  let gdt_size = 0x1000L

  let entry = function
    | "FS_BASE" -> Some (1, "FS")
    | "GS_BASE" -> Some (2, "GS")
    | _ -> None

  let is_base = Fn.compose Option.is_some entry

  (* the descriptor of the writable data segment of the 32-bit mode, of
     the ring 3, or 0, which covers all memory, from the base, with the
     page granularity *)
  let descriptor ?(access = 0xF2L) base =
    let limit = 0xFFFFFL and flags = 0xCL in
    let open Int64 in
    let low = limit land 0xFFFFL lor ((base land 0xFFFFL) lsl 16) in
    let high =
      (base lsr 16) land 0xFFL lor (access lsl 8)
      lor (((limit lsr 16) land 0xFL) lsl 16)
      lor (flags lsl 20)
      lor (((base lsr 24) land 0xFFL) lsl 24)
    in
    let byte x i =
      Char.of_int_exn (to_int_exn ((x lsr Int.(8 * i)) land 0xFFL))
    in
    String.init 8 ~f:(fun i ->
        if Int.(i < 4) then byte low i else byte high Int.(i - 4))

  (* the GDTR, which is uc_x86_mmr: the selector, the base, the limit,
     and the flags, as the C compiler lays them out *)
  let gdtr =
    let le x n =
      String.init n ~f:(fun i ->
          Char.of_int_exn Int64.(to_int_exn ((x lsr Int.(8 * i)) land 0xFFL)))
    in
    String.concat
      [
        le 0L 2;
        String.make 6 '\000';
        le gdt_base 8;
        le Int64.(gdt_size - 1L) 4;
        le 0L 4;
      ]

  let mapped uc =
    List.exists (Uc.mem_regions uc) ~f:(fun (lower, _, _) ->
        Int64.equal lower gdt_base)

  (* [get uc name] the base of the segment of the base register [name],
     in the little-endian bytes of 32 bits, which is 0, if the table is
     not mapped *)
  let get uc name =
    match entry name with
    | Some (index, _) when mapped uc ->
        let d = Uc.mem_read uc Int64.(gdt_base + of_int Int.(index * 8)) 8 in
        String.of_char_list [ d.[2]; d.[3]; d.[4]; d.[7] ]
    | _ -> String.make 4 '\000'

  (* [set uc name base] the segment of the base register [name], e.g.,
     FS_BASE, has the [base], returns [false], if it is not a base *)
  let set uc name base =
    match (entry name, Uc.reg X86 "GDTR") with
    | Some (index, selector), Some id -> (
        (* the lifted engine reads the base, as the semantics of BAP do *)
        Uc.set_unmapped uc name (Word.of_int64 ~width:32 base);
        if not (mapped uc) then begin
          Uc.mem_map uc gdt_base gdt_size Uc.Perm.(read + write);
          Uc.reg_write_bytes uc id gdtr;
          Uc.mem_write uc Int64.(gdt_base + 24L) (descriptor ~access:0x92L 0L);
          Option.iter (Uc.reg X86 "SS") ~f:(fun ss -> Uc.reg_write uc ss 0x18L)
        end;
        Uc.mem_write uc
          Int64.(gdt_base + of_int Int.(index * 8))
          (descriptor base);
        match Uc.reg X86 selector with
        | Some sel ->
            (* the selector of the entry, with the privilege level 3 *)
            Uc.reg_write uc sel (Int64.of_int ((index lsl 3) lor 3));
            true
        | None -> false)
    | _ -> false
end
