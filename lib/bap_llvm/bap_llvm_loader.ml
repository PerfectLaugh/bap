open Core
open Bap_knowledge
open Bap_core_theory
open Bap.Std
open Monads.Std
open Or_error
include Self ()
module Sys = Stdlib.Sys
module Unix = Caml_unix

module Ogre = struct
  include Ogre
  include Ogre.Make (KB)
end

module Primitive = struct
  external llvm_load : Bigstring.t -> string -> Bigstring.t
    = "bap_llvm_load_stub"
  (** [bap_llvm_load data pdb_path] analyzes [data] and describes the discovered
      meta-data with tables, see {!Bap_llvm_tables}.

      - [pdb_path] is a path to PE debugging database, could be empty. *)

  exception Llvm_loader_fail of int

  let () = Callback.register_exception "Llvm_loader_fail" (Llvm_loader_fail 0)
end

module Tables = Bap_llvm_tables

(* The facts that the native loader discovered, decoded from its tables.
   Each list holds the distinct rows of a table in the order of
   [Tables.facts], i.e., the last added first. *)
module LLVM = struct
  type flags = bool * bool * bool

  type t = {
    header : Tables.t;  (** all tables *)
    entry_point : int64 list;
    base_address : int64 list;
    code_entry : (string * int64 * int64) list;  (** name, off, size *)
    symbol_entry : (string * int64 * int64 * int64 * int64) list;
        (** name, addr, size, off, value *)
    section_entry : (string * int64 * int64 * int64) list;
        (** name, addr, size, off *)
    section_flags : (string * flags) list;
    segment_cmd : (string * int64 * int64) list;  (** name, off, size *)
    segment_cmd_flags : (string * flags) list;
    virtual_segment_cmd : (string * int64 * int64) list;
        (** name, addr, size *)
    elf_program_header : (string * int64 * int64) list;  (** name, off, size *)
    elf_virtual_program_header : (string * int64 * int64) list;
        (** name, addr, size *)
    elf_program_header_flags : (string * bool * flags) list;
        (** name, loadable, flags *)
    coff_virtual_section_header : (string * int64 * int64) list;
        (** name, addr, size *)
    relocation : (int64 * int64) list;  (** at, addr *)
    relative_relocation : int64 list;
    name_reference : (int64 * string) list;
    elf_header : (int64 * int64 * int64) list;  (** type, machine, flags *)
  }

  let ( let* ) = Or_error.( >>= )

  let rows doc name types f =
    let* table = Tables.table doc name types in
    Ok (List.map (Tables.facts table) ~f:(f table))

  let decode doc =
    let open Tables in
    let str = Tables.str and int = Tables.int and bool = Tables.bool in
    let flags t r = (bool t r 1, bool t r 2, bool t r 3) in
    let* entry_point =
      rows doc "llvm:entry-point" [ Int ] (fun t r -> int t r 0)
    in
    let* base_address =
      rows doc "llvm:base-address" [ Int ] (fun t r -> int t r 0)
    in
    let* code_entry =
      rows doc "llvm:code-entry" [ Str; Int; Int ] (fun t r ->
          (str t r 0, int t r 1, int t r 2))
    in
    let* symbol_entry =
      rows doc "llvm:symbol-entry" [ Str; Int; Int; Int; Int ] (fun t r ->
          (str t r 0, int t r 1, int t r 2, int t r 3, int t r 4))
    in
    let* section_entry =
      rows doc "llvm:section-entry" [ Str; Int; Int; Int ] (fun t r ->
          (str t r 0, int t r 1, int t r 2, int t r 3))
    in
    let* section_flags =
      rows doc "llvm:section-flags" [ Str; Bool; Bool; Bool ] (fun t r ->
          (str t r 0, flags t r))
    in
    let* segment_cmd =
      rows doc "llvm:segment-command" [ Str; Int; Int ] (fun t r ->
          (str t r 0, int t r 1, int t r 2))
    in
    let* segment_cmd_flags =
      rows doc "llvm:segment-command-flags" [ Str; Bool; Bool; Bool ]
        (fun t r -> (str t r 0, flags t r))
    in
    let* virtual_segment_cmd =
      rows doc "llvm:virtual-segment-command" [ Str; Int; Int ] (fun t r ->
          (str t r 0, int t r 1, int t r 2))
    in
    let* elf_program_header =
      rows doc "llvm:elf-program-header" [ Str; Int; Int ] (fun t r ->
          (str t r 0, int t r 1, int t r 2))
    in
    let* elf_virtual_program_header =
      rows doc "llvm:elf-virtual-program-header" [ Str; Int; Int ] (fun t r ->
          (str t r 0, int t r 1, int t r 2))
    in
    let* elf_program_header_flags =
      rows doc "llvm:elf-program-header-flags" [ Str; Bool; Bool; Bool; Bool ]
        (fun t r ->
          (str t r 0, bool t r 1, (bool t r 2, bool t r 3, bool t r 4)))
    in
    let* coff_virtual_section_header =
      rows doc "llvm:coff-virtual-section-header" [ Str; Int; Int ] (fun t r ->
          (str t r 0, int t r 1, int t r 2))
    in
    let* relocation =
      rows doc "llvm:relocation" [ Int; Int ] (fun t r ->
          (int t r 0, int t r 1))
    in
    let* relative_relocation =
      rows doc "llvm:relative-relocation" [ Int ] (fun t r -> int t r 0)
    in
    let* name_reference =
      rows doc "llvm:name-reference" [ Int; Str ] (fun t r ->
          (int t r 0, str t r 1))
    in
    let* elf_header =
      rows doc "llvm:elf-header" [ Int; Int; Int ] (fun t r ->
          (int t r 0, int t r 1, int t r 2))
    in
    Ok
      {
        header = doc;
        entry_point;
        base_address;
        code_entry;
        symbol_entry;
        section_entry;
        section_flags;
        segment_cmd;
        segment_cmd_flags;
        virtual_segment_cmd;
        elf_program_header;
        elf_virtual_program_header;
        elf_program_header_flags;
        coff_virtual_section_header;
        relocation;
        relative_relocation;
        name_reference;
        elf_header;
      }
end

module Filename = Stdlib.Filename
open Image.Scheme
open Ogre.Syntax

let provide_if cond code = if cond then code else []
let iter xs f = Ogre.List.iter xs ~f:(fun x -> Ogre.sequence (f x))

(* [one name facts] the only fact, as [Ogre.require] *)
let one name = function
  | [ x ] -> Ogre.return x
  | [] -> Ogre.failf "%s is not provided" name ()
  | _ -> Ogre.failf "%s values are ambiguous" name ()

(* [maybe name facts] the only fact if any, as [Ogre.request] *)
let maybe name = function
  | [] -> Ogre.return None
  | [ x ] -> Ogre.return (Some x)
  | _ -> Ogre.failf "%s values are ambiguous" name ()

(* [index facts ~key] the facts by their keys, each key maps to the facts
   in their order *)
let index (keys : 'k Base.Hashtbl.Key.t) facts ~key =
  let tab = Hashtbl.create keys in
  List.iter (List.rev facts) ~f:(fun x ->
      Hashtbl.add_multi tab ~key:(key x) ~data:x);
  Hashtbl.find_multi tab

(* [join_by_name xs ys] the pairs of [xs] and [ys] with the same names, in
   the order of the join of the corresponding Ogre attributes *)
let join_by_name xs ~name:x_name ys ~name:y_name =
  let ys = index (module String) ys ~key:y_name in
  List.concat_map xs ~f:(fun x -> List.map (ys (x_name x)) ~f:(fun y -> (x, y)))

let fst3 (x, _, _) = x
let fst4 (x, _, _, _) = x

(* provides the facts about the file that the native loader discovered
   itself, e.g., the architecture, in the order of their discovery *)
let provide_header doc =
  let open Tables in
  let each name types f =
    match Tables.table doc name types with
    | Error err -> Ogre.fail err
    | Ok t -> Ogre.List.iter (List.init (Tables.length t) ~f:Fn.id) ~f:(f t)
  in
  let str attr t r = Ogre.provide attr (Tables.str t r 0) in
  let int attr t r = Ogre.provide attr (Tables.int t r 0) in
  let bool attr t r = Ogre.provide attr (Tables.bool t r 0) in
  let attrs =
    [
      ("arch", Str, str arch);
      ("subarch", Str, str subarch);
      ("vendor", Str, str vendor);
      ("system", Str, str system);
      ("abi", Str, str abi);
      ("bits", Int, int bits);
      ("is-little-endian", Bool, bool is_little_endian);
      ("is-executable", Bool, bool is_executable);
      ("format", Str, str format);
      ("require", Str, str require);
    ]
  in
  List.filter (Tables.names doc) ~f:(fun name ->
      not (String.is_prefix name ~prefix:"llvm:"))
  |> Ogre.List.iter ~f:(fun name ->
      match List.find attrs ~f:(fun (n, _, _) -> String.equal n name) with
      | Some (_, typ, provide) -> each name [ typ ] provide
      | None ->
          warning "ignoring an unknown table %s of the llvm loader" name;
          Ogre.return ())

let unit_bias file =
  let open KB.Syntax in
  match file with
  | None | Some "" -> !!None
  | Some file ->
      Theory.Unit.for_file file
      >>= KB.collect Theory.Unit.bias
      >>| Option.map ~f:Bitvec.to_int64

let provide_base_and_bias (llvm : LLVM.t) ?file new_base =
  one "llvm:base-address" llvm.base_address >>= fun real ->
  Ogre.lift (unit_bias file) >>= function
  | Some b ->
      info "using provided bias 0x%Lx for file %s" b @@ Option.value_exn file;
      Ogre.sequence
        [ Ogre.provide bias b; Ogre.provide base_address Int64.(real + b) ]
  | None -> (
      Ogre.sequence
      @@
      match new_base with
      | None -> [ Ogre.provide bias 0L; Ogre.provide base_address real ]
      | Some base ->
          [
            Ogre.provide bias Int64.(base - real);
            Ogre.provide base_address base;
          ])

let provide_entry (llvm : LLVM.t) =
  Ogre.require bias >>= fun bias ->
  one "llvm:entry-point" llvm.entry_point >>= fun addr ->
  Ogre.provide entry_point Int64.(addr + bias)

let provide_symbols (llvm : LLVM.t) =
  let is_code =
    let entries = Hash_set.create (module String) in
    List.iter llvm.code_entry ~f:(fun (name, off, size) ->
        Hash_set.add entries (sprintf "%Ld:%Ld:%s" off size name));
    fun name off size ->
      Hash_set.mem entries (sprintf "%Ld:%Ld:%s" off size name)
  in
  Ogre.require bias >>= fun bias ->
  iter llvm.symbol_entry @@ fun (name, addr, size, off, value) ->
  let addr = Int64.(addr + bias) in
  provide_if
    Int64.(size > 0L)
    ([ Ogre.provide symbol_chunk addr size addr ]
    @ provide_if (is_code name off size) [ Ogre.provide code_start addr ])
  @ [
      Ogre.provide symbol_value addr value; Ogre.provide named_symbol addr name;
    ]

let provide_generic_sections (llvm : LLVM.t) =
  Ogre.require bias >>= fun bias ->
  iter llvm.section_entry @@ fun (name, addr, size, _) ->
  let addr = Int64.(addr + bias) in
  [ Ogre.provide section addr size; Ogre.provide named_region addr size name ]

let provide_relocations (llvm : LLVM.t) =
  Ogre.require bias >>= fun bias ->
  iter llvm.relocation @@ fun (addr, dest) ->
  [ Ogre.provide relocation Int64.(addr + bias) Int64.(dest + bias) ]

let provide_relative_relocations (llvm : LLVM.t) =
  Ogre.require bias >>= fun bias ->
  iter llvm.relative_relocation @@ fun addr ->
  [ Ogre.provide relative_relocation Int64.(addr + bias) ]

let provide_name_references (llvm : LLVM.t) =
  Ogre.require bias >>= fun bias ->
  iter llvm.name_reference @@ fun (addr, name) ->
  [ Ogre.provide external_reference Int64.(addr + bias) name ]

(* the named regions with code, which are joined with the code entries
   by their names and sizes *)
let provide_generic_code_regions (llvm : LLVM.t) =
  Ogre.collect Ogre.Query.(select (from named_region)) >>= fun regions ->
  let entries =
    index
      (module struct
        type t = string * int64 [@@deriving compare, hash, sexp_of]
      end)
      llvm.code_entry
      ~key:(fun (name, _, size) -> (name, size))
  in
  iter (Seq.to_list regions) @@ fun { addr; size; info = name } ->
  List.map
    (entries (name, size))
    ~f:(fun (_, off, _) -> Ogre.provide code_region addr size off)

let provide_macho_segments (llvm : LLVM.t) =
  Ogre.require bias >>= fun bias ->
  let flags = index (module String) llvm.segment_cmd_flags ~key:fst in
  let vcmds = index (module String) llvm.virtual_segment_cmd ~key:fst3 in
  iter llvm.segment_cmd @@ fun (name, off, size) ->
  List.concat_map (flags name) ~f:(fun (_, (r, w, x)) ->
      List.concat_map (vcmds name) ~f:(fun (_, addr, vsize) ->
          let addr = Int64.(bias + addr) in
          provide_if
            Int64.(size <> 0L)
            [
              Ogre.provide segment addr vsize r w x;
              Ogre.provide named_region addr vsize name;
              Ogre.provide mapped addr size off;
            ]))

let provide_macho_segmentation llvm =
  [
    provide_macho_segments llvm;
    provide_generic_sections llvm;
    provide_generic_code_regions llvm;
  ]

(* the program headers joined with their virtual headers and flags *)
let elf_program_headers (llvm : LLVM.t) =
  let vheaders =
    index (module String) llvm.elf_virtual_program_header ~key:fst3
  in
  let flags = index (module String) llvm.elf_program_header_flags ~key:fst3 in
  List.concat_map llvm.elf_program_header ~f:(fun ((name, _, _) as hdr) ->
      List.concat_map (vheaders name) ~f:(fun vhdr ->
          List.map (flags name) ~f:(fun flags -> (hdr, vhdr, flags))))

let derive_code_regions_of_segments llvm =
  Ogre.require bias >>= fun bias ->
  iter (elf_program_headers llvm)
  @@ fun ((_, off, size), (_, addr, _), (_, _, (_, _, x))) ->
  provide_if
    (x && Int64.(size <> 0L))
    [ Ogre.provide code_region Int64.(addr + bias) size off ]

let map_segments_to_sections (llvm : LLVM.t) =
  Ogre.require bias >>= fun bias ->
  iter llvm.elf_virtual_program_header @@ fun (_, addr, size) ->
  [ Ogre.provide section Int64.(addr + bias) size ]

let map_sections_to_segments (llvm : LLVM.t) =
  Ogre.require bias >>= fun bias ->
  iter (join_by_name llvm.section_entry ~name:fst4 llvm.section_flags ~name:fst)
  @@ fun ((name, addr, size, off), (_, (r, w, x))) ->
  let addr = Int64.(addr + bias) in
  provide_if
    Int64.(size <> 0L)
    [
      Ogre.provide segment addr size r w x;
      Ogre.provide mapped addr size off;
      Ogre.provide named_region addr size name;
    ]

let derive_missing (llvm : LLVM.t) =
  Ogre.sequence
    [
      (if List.is_empty llvm.section_entry then
         Ogre.sequence
           [
             derive_code_regions_of_segments llvm; map_segments_to_sections llvm;
           ]
       else Ogre.return ());
      ( Ogre.collect Ogre.Query.(select (from segment)) >>= fun segments ->
        if Seq.is_empty segments then map_sections_to_segments llvm
        else Ogre.return () );
    ]

let provide_elf_segments llvm =
  Ogre.require bias >>= fun bias ->
  iter (elf_program_headers llvm)
  @@ fun ((name, off, size), (_, addr, vsize), (_, ld, (r, w, x))) ->
  let addr = Int64.(addr + bias) in
  (* a segment without file contents, e.g., the one that holds .bss,
     is zero-filled, so it is not mapped to the file *)
  provide_if
    (ld && Int64.(vsize <> 0L))
    [
      Ogre.provide segment addr vsize r w x;
      Ogre.provide named_region addr vsize name;
    ]
  @ provide_if (ld && Int64.(size <> 0L)) [ Ogre.provide mapped addr size off ]

let provide_elf_segmentation llvm =
  [
    provide_generic_sections llvm;
    provide_elf_segments llvm;
    provide_generic_code_regions llvm;
    derive_missing llvm;
  ]

let provide_coff_segmentation (llvm : LLVM.t) =
  let vheaders =
    index (module String) llvm.coff_virtual_section_header ~key:fst3
  in
  let flags = index (module String) llvm.section_flags ~key:fst in
  [
    ( Ogre.require bias >>= fun bias ->
      iter llvm.section_entry @@ fun (name, _, size, start) ->
      List.concat_map (vheaders name) ~f:(fun (_, addr, vsize) ->
          List.concat_map (flags name) ~f:(fun (_, (r, w, x)) ->
              let addr = Int64.(addr + bias) in
              provide_if
                Int64.(size <> 0L)
                [
                  Ogre.provide segment addr vsize r w x;
                  Ogre.provide mapped addr size start;
                  Ogre.provide section addr vsize;
                  Ogre.provide named_region addr vsize name;
                ]
              @ provide_if x [ Ogre.provide code_region addr vsize start ])) );
  ]

let overload file_type info =
  Ogre.require format >>= fun file ->
  Ogre.sequence @@ provide_if (String.equal file file_type) info

module ElfDyn = struct
  type dyn = { tag : word; off : word }
  type img = { data : Bigstring.t; endian : Word.endian; width : int }

  let required attr k =
    Ogre.request attr >>= function None -> Ogre.return () | Some x -> k x

  let section_by_name (llvm : LLVM.t) { data; endian; width } sec_name =
    List.find llvm.section_entry ~f:(fun (name, _, _, _) ->
        String.equal name sec_name)
    |> function
    | None -> None
    | Some (_, addr, len, pos) -> (
        let len = Int64.to_int_trunc len and pos = Int64.to_int_trunc pos in
        let addr = Addr.of_int64 ~width addr in
        match Memory.create ~pos ~len endian addr data with
        | Ok mem -> Some mem
        | _ -> None)

  let word_size img = Size.of_int_exn img.width

  let dynamic_contents llvm img =
    match section_by_name llvm img ".dynamic" with
    | None -> []
    | Some mem -> (
        Memory.fold ~word_size:(word_size img) mem
          ~f:(fun data (acc, dyn) ->
            match dyn with
            | None -> (acc, Some data)
            | Some tag -> ({ tag; off = data } :: acc, None))
          ~init:([], None)
        |> function
        | acc, _ -> List.rev acc)

  let read ~strtab pos =
    let strtab = Memory.to_buffer strtab in
    let rec loop off =
      if Char.equal (Bigsubstring.get strtab off) '\x00' then
        Bigsubstring.sub strtab ~pos ~len:(off - pos)
      else loop (off + 1)
    in
    Bigsubstring.to_string @@ loop pos

  let libraries llvm data =
    required is_little_endian @@ fun is_little ->
    required bits @@ fun bits ->
    let endian = if is_little then LittleEndian else BigEndian in
    let img = { endian; data; width = Int64.to_int_exn bits } in
    match section_by_name llvm img ".dynstr" with
    | None -> Ogre.return ()
    | Some strtab ->
        Ogre.List.iter (dynamic_contents llvm img) ~f:(fun { tag; off } ->
            match (Word.to_int tag, Word.to_int off) with
            | Ok 1, Ok off -> Ogre.provide require (read ~strtab off)
            | _ -> Ogre.return ())
end

(** links a relocatable file, see {!Bap_llvm_elf_linker}. *)
module Relocatable = struct
  module Linker = Bap_llvm_elf_linker

  let et_rel = 1L

  let table doc name types =
    match Tables.table doc name types with
    | Ok t -> Ogre.return t
    | Error err -> Ogre.fail err

  let input (llvm : LLVM.t) data machine =
    let int t r f = Tables.int t r f and to_int = Int64.to_int_trunc in
    Ogre.require base_address >>= fun base ->
    Ogre.require bits >>= fun width ->
    Ogre.require is_little_endian >>= fun little ->
    table llvm.header "llvm:elf-section"
      Tables.[ Int; Str; Int; Int; Int; Int; Int ]
    >>= fun sections ->
    table llvm.header "llvm:elf-symbol"
      Tables.[ Int; Str; Int; Bool; Int; Int; Int; Int ]
    >>= fun symbols ->
    table llvm.header "llvm:elf-relocation"
      Tables.[ Int; Int; Int; Int; Int; Int; Bool ]
    >>| fun relocations ->
    {
      Linker.machine = to_int machine;
      width = to_int width;
      little;
      base;
      data;
      sections =
        List.map (Tables.facts sections) ~f:(fun r ->
            {
              Linker.index = to_int (int sections r 0);
              name = Tables.str sections r 1;
              typ = to_int (int sections r 2);
              flags = int sections r 3;
              off = int sections r 4;
              size = int sections r 5;
              align = int sections r 6;
            });
      symbols =
        List.fold (Tables.facts symbols) ~init:Int.Map.empty ~f:(fun syms r ->
            Map.set syms
              ~key:(to_int (int symbols r 0))
              ~data:
                {
                  Linker.name = Tables.str symbols r 1;
                  shndx = to_int (int symbols r 2);
                  extended = Tables.bool symbols r 3;
                  value = int symbols r 4;
                  size = int symbols r 5;
                  typ = to_int (int symbols r 6);
                  bind = to_int (int symbols r 7);
                });
      (* the relocations are numbered in the order of appearance *)
      relocations =
        List.init (Tables.length relocations) ~f:(fun r ->
            {
              Linker.section = to_int (int relocations r 1);
              offset = int relocations r 2;
              typ = to_int (int relocations r 3);
              symbol = to_int (int relocations r 4);
              addend = int relocations r 5;
              explicit = Tables.bool relocations r 6;
            });
    }

  let provide_region { Linker.name; addr; size; off; r; w; x; is_section } =
    [
      Ogre.provide segment addr size r w x;
      Ogre.provide named_region addr size name;
    ]
    @
    match off with
    | None -> []
    | Some off ->
        Ogre.provide mapped addr size off
        :: provide_if is_section [ Ogre.provide section addr size ]
        @ provide_if x [ Ogre.provide code_region addr size off ]

  let provide_function (name, addr, size, value) =
    [
      Ogre.provide named_symbol addr name;
      Ogre.provide symbol_value addr value;
      Ogre.provide code_start addr;
    ]
    @ provide_if Int64.(size > 0L) [ Ogre.provide symbol_chunk addr size addr ]

  let to_hex bytes =
    let digits = "0123456789abcdef" in
    String.init
      (2 * String.length bytes)
      ~f:(fun i ->
        let b = Char.to_int bytes.[i / 2] in
        digits.[if i % 2 = 0 then b lsr 4 else b land 0xf])

  let provide { Linker.regions; functions; references; patches; warnings } =
    List.iter warnings ~f:(fun msg -> warning "%s" msg);
    Ogre.sequence
    @@ List.concat_map regions ~f:provide_region
    @ List.concat_map functions ~f:provide_function
    @ List.map references ~f:(fun (addr, name) ->
        Ogre.provide external_reference addr name)
    @ List.map patches ~f:(fun (off, bytes) ->
        Ogre.provide patch off (to_hex bytes))

  let link (llvm : LLVM.t) data =
    maybe "llvm:elf-header" llvm.elf_header >>= function
    | Some (typ, machine, _) when Int64.equal typ et_rel ->
        input llvm data machine >>| Linker.link >>= provide
    | _ -> Ogre.return ()
end

let provide_elf_segmentation_and_libraries llvm data =
  (Relocatable.link llvm data :: provide_elf_segmentation llvm)
  @ [ ElfDyn.libraries llvm data ]

(** translates the facts of the native loader into the image specification *)
let translate ?file data user_base (llvm : LLVM.t) =
  Ogre.sequence
    [
      provide_header llvm.header;
      provide_base_and_bias llvm user_base ?file;
      provide_entry llvm;
      Ogre.sequence
        [
          overload "elf" @@ provide_elf_segmentation_and_libraries llvm data;
          overload "coff" @@ provide_coff_segmentation llvm;
          overload "macho" @@ provide_macho_segmentation llvm;
        ];
      provide_symbols llvm;
      provide_relocations llvm;
      provide_relative_relocations llvm;
      provide_name_references llvm;
    ]

let pdb_path ~pdb filename =
  if Sys.file_exists pdb then
    if Sys.is_directory pdb then
      let pdb_file =
        sprintf "%s.pdb" Filename.(remove_extension @@ basename filename)
      in
      Filename.concat pdb pdb_file
    else pdb
  else ""

type KB.conflict += Loader_error of Error.t

let () =
  KB.Conflict.register_printer @@ function
  | Loader_error err ->
      Some (Format.asprintf "llvm loader error: %a" Error.pp err)
  | _ -> None

let liftr = function
  | Ok x -> KB.return x
  | Error x -> KB.fail @@ Loader_error x

let translate_to_image_spec data base llvm file =
  let open KB.Syntax in
  Ogre.exec (translate data base ~file llvm) Ogre.Doc.empty >>= liftr

let load_doc ~pdb filename data =
  try Ok (Primitive.llvm_load data (pdb_path ~pdb filename))
  with Primitive.Llvm_loader_fail n -> (
    match n with
    | 1 -> Or_error.error_string "File corrupted"
    | 2 -> Or_error.error_string "File format is not supported"
    | n -> Or_error.errorf "fail with unexpected error code %d" n)

let from_data ~base ~pdb filename data =
  let open KB.Syntax in
  liftr (load_doc ~pdb filename data) >>= fun doc ->
  liftr Or_error.(Tables.of_bigstring doc >>= LLVM.decode) >>= fun llvm ->
  translate_to_image_spec data base llvm filename >>| Option.some

let map_file path =
  let fd = Unix.(openfile path [ O_RDONLY ] 0o400) in
  try
    let data =
      Unix.map_file fd Bigarray.char Bigarray.c_layout false [| -1 |]
    in
    Unix.close fd;
    Ok (Bigarray.array1_of_genarray data)
  with exn ->
    Unix.close fd;
    Or_error.errorf "unable to process file %s: %s" path (Exn.to_string exn)

let from_file ~base ~pdb path =
  let open KB.Syntax in
  liftr (map_file path) >>= from_data ~base ~pdb path

let init ?base ?(pdb_path = Sys.getcwd ()) () =
  Image.KB.register_loader ~name:"llvm"
    (module struct
      let from_file = from_file ~base ~pdb:pdb_path
      let from_data = from_data ~base ~pdb:pdb_path ""
    end);
  Ok ()
