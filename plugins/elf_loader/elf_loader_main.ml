open Core
open Bap.Std
open Bap_elf.Std
open Bap_dwarf.Std
open Elf
include Self ()

let () =
  Config.manpage
    [
      `S "DESCRIPTION";
      `P "An ELF image loader written in pure OCaml.";
      `S "SEE ALSO";
      `P "$(b,bap-elf)(3), $(b,bap-plugin-llvm)(1)";
    ]

let loader_name = "bap-elf"

open Image.Scheme
open Ogre.Syntax

let int_of_int64 n =
  match Int64.to_int n with
  | Some v -> Ok v
  | None -> Or_error.errorf "number %LdL doesn't fit into int" n

let section_data data s : string Or_error.t =
  let open Or_error.Monad_infix in
  int_of_int64 s.sh_size >>= fun size ->
  int_of_int64 s.sh_offset >>= fun offset ->
  Or_error.try_with (fun () ->
      Bigstring.To_string.sub data ~pos:offset ~len:size)

let endian_of_elf elf =
  match elf.e_data with ELFDATA2LSB -> LittleEndian | ELFDATA2MSB -> BigEndian

let arch_of_elf elf : arch Or_error.t =
  match (elf.e_machine, endian_of_elf elf, elf.e_class) with
  | EM_386, _, _ -> Ok `x86
  | EM_X86_64, _, _ -> Ok `x86_64
  | EM_ARM, LittleEndian, _ -> Ok `armv7
  | EM_ARM, BigEndian, _ -> Ok `armv7eb
  | EM_AARCH64, LittleEndian, _ -> Ok `aarch64
  | EM_AARCH64, BigEndian, _ -> Ok `aarch64_be
  | EM_SPARC, _, _ -> Ok `sparc
  | EM_SPARCV9, _, _ -> Ok `sparcv9
  | EM_PPC, _, _ -> Ok `ppc
  | EM_PPC64, BigEndian, _ -> Ok `ppc64
  | EM_PPC64, LittleEndian, _ -> Ok `ppc64le
  | EM_S390, _, _ -> Ok `systemz
  | EM_MIPS, BigEndian, ELFCLASS32 -> Ok `mips
  | EM_MIPS, LittleEndian, ELFCLASS32 -> Ok `mipsel
  | EM_MIPS, BigEndian, ELFCLASS64 -> Ok `mips64
  | EM_MIPS, LittleEndian, ELFCLASS64 -> Ok `mips64el
  | _ -> Or_error.errorf "can't load file, unsupported platform"

(** Function symbols recovered from the DWARF debug information, as
    [(name, start, size)] triples. *)
let dwarf_functions data elf =
  let open Or_error.Monad_infix in
  let module Buffer = Dwarf.Buffer in
  let create name s =
    match section_data data s with
    | Error _ -> None
    | Ok data -> Some (name, Buffer.create data)
  in
  let sections =
    Seq.filter_map elf.e_sections ~f:(fun s ->
        match Elf.section_name data elf s with
        | Ok ".debug_info" -> create Dwarf.Section.Info s
        | Ok ".debug_abbrev" -> create Dwarf.Section.Abbrev s
        | Ok ".debug_str" -> create Dwarf.Section.Str s
        | Ok _ | Error _ -> None)
    |> Seq.to_list_rev
  in
  Dwarf.Data.create (endian_of_elf elf) sections >>= Dwarf.Fbi.create
  >>= fun dff ->
  Dwarf.Fbi.functions dff
  |> Sequence.map ~f:(fun (name, fn) ->
      let pc_lo = Dwarf.Fn.pc_lo fn in
      Addr.to_int64 pc_lo >>= fun start ->
      (match Dwarf.Fn.pc_hi fn with
        | None -> Ok 1L
        | Some pc_hi -> Addr.Int_err.(!$pc_hi - !$pc_lo) >>= Addr.to_int64)
      >>| fun size -> (name, start, size))
  |> Sequence.to_list |> Or_error.all

let provide_arch arch =
  Ogre.sequence
    [
      Ogre.provide Image.Scheme.arch (Arch.to_string arch);
      Ogre.provide bits (Int64.of_int (Size.in_bits (Arch.addr_size arch)));
      Ogre.provide is_little_endian
        (match Arch.endian arch with
        | LittleEndian -> true
        | BigEndian -> false);
    ]

(* the ELF parser sign-extends 32-bit fields *)
let norm elf x =
  match elf.e_class with
  | ELFCLASS32 -> Int64.(x land 0xFFFF_FFFFL)
  | ELFCLASS64 -> x

let has_flag flag es = List.mem es.p_flags flag ~equal:[%compare.equal: p_flag]

(* only loadable segments with a valid set of permissions are mapped *)
let provide_segment elf i es =
  let r = has_flag PF_R es and w = has_flag PF_W es and x = has_flag PF_X es in
  if (not ([%compare.equal: p_type] es.p_type PT_LOAD)) || not (r || w || x)
  then Ogre.return ()
  else
    let addr = norm elf es.p_vaddr
    and vsize = norm elf es.p_memsz
    and fsize = norm elf es.p_filesz
    and off = norm elf es.p_offset in
    Ogre.sequence
      [
        Ogre.provide segment addr vsize r w x;
        Ogre.provide mapped addr fsize off;
        Ogre.provide named_region addr vsize (sprintf "%02d" i);
      ]

let provide_section data elf s =
  match Elf.section_name data elf s with
  | Error _ -> Ogre.return ()
  | Ok name ->
      let addr = norm elf s.sh_addr and size = norm elf s.sh_size in
      Ogre.sequence
        [
          Ogre.provide section addr size;
          Ogre.provide named_region addr size name;
        ]

let provide_function (name, start, size) =
  Ogre.sequence
    [
      Ogre.provide named_symbol start name;
      Ogre.provide code_start start;
      Ogre.provide symbol_chunk start size start;
    ]

let provide_elf data elf =
  let functions =
    match dwarf_functions data elf with
    | Ok fns -> fns
    | Error err ->
        info "failed to read symbols: %a" Error.pp err;
        []
  in
  if
    not
      (Seq.exists elf.e_segments ~f:(fun es ->
           [%compare.equal: p_type] es.p_type PT_LOAD))
  then Ogre.failf "failed to read segments" ()
  else
    match arch_of_elf elf with
    | Error err -> Ogre.fail err
    | Ok arch ->
        Ogre.sequence
          [
            provide_arch arch;
            Ogre.provide entry_point (norm elf elf.e_entry);
            Ogre.sequence
              (Seq.to_list (Seq.mapi elf.e_segments ~f:(provide_segment elf)));
            Ogre.sequence
              (Seq.to_list
                 (Seq.map elf.e_sections ~f:(provide_section data elf)));
            Ogre.sequence (List.map functions ~f:provide_function);
          ]

module Loader = struct
  let from_data data =
    let open Or_error.Monad_infix in
    Elf.from_bigstring data >>= fun elf ->
    Ogre.exec (provide_elf data elf) Ogre.Doc.empty >>| Option.some

  let from_file filename =
    let open Or_error.Monad_infix in
    Or_error.try_with (fun () -> In_channel.read_all filename)
    >>| Bigstring.of_string >>= from_data
end

let () =
  Config.declare_extension ~doc:"provides an alternative ELF image loader"
    ~provides:[ "elf"; "dwarf"; "loader" ]
  @@ fun _ -> Image.register_loader ~name:loader_name (module Loader)
