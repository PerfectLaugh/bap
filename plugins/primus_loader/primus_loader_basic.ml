open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
open Format
include Self ()
module Generator = Primus.Generator

module type Param = sig
  val stack_size : int
  val stack_base : int64
end

module Make (Param : Param) (Machine : Primus.Machine.S) = struct
  open Param
  open Machine.Syntax
  module Env = Primus.Env.Make (Machine)
  module Mem = Primus.Memory.Make (Machine)
  module Val = Primus.Value.Make (Machine)
  module Linker = Primus.Linker.Make (Machine)

  let make_word addr =
    Machine.gets Project.target >>| Theory.Target.code_addr_size
    >>| fun width -> Addr.of_int64 ~width addr

  let set_word name x =
    let t = Type.imm (Word.bitwidth x) in
    let var = Var.create name t in
    Val.of_word x >>= Env.set var

  let stack_pointer =
    Machine.gets Project.target >>| fun t ->
    match Theory.Target.reg t Theory.Role.Register.stack_pointer with
    | None -> None
    | Some sp -> Some (Var.reify sp)

  (* bottom points to the end of the stack, ala STL end pointer.
     Note: bottom is usually depicted at the top of the stack
     structure, and it is the highest address.
     Note: memory beyond top is readable, as it is the place,
     where kernel should put argc, argv, and other info to a
     user process *)
  let setup_stack () =
    make_word stack_base >>= fun bottom ->
    let top = Addr.(bottom -- stack_size) in
    Val.of_word bottom >>= fun bottom ->
    stack_pointer >>= function
    | None ->
        warning "unable to initialize stack - no stack pointer@\n";
        Machine.return ()
    | Some sp ->
        Env.set sp bottom >>= fun () ->
        Machine.get () >>= fun proj ->
        (* the stack of Windows is zeroed, which the programs of PE read,
           e.g., __chkstk_ms probes its pages *)
        let init =
          match
            Ogre.eval
              (Ogre.request Image.Scheme.format)
              (Project.specification proj)
          with
          | Ok (Some "coff") -> Some (fun _ -> Machine.return (Word.zero 8))
          | _ -> None
        in
        Mem.allocate ~readonly:false ~executable:false ?init top stack_size

  let setup_registers () =
    let zero = Generator.static 0 in
    Machine.gets Project.target >>= fun t ->
    Set.to_sequence (Theory.Target.vars t)
    |> Machine.Seq.iter ~f:(fun reg -> Env.add (Var.reify reg) zero)

  let thread_pointer =
    Machine.gets Project.target >>| fun t ->
    match Theory.Target.reg t Theory.Role.Register.thread with
    | None -> None
    | Some tp -> Some (Var.reify tp)

  let main_spec () =
    Machine.get () >>| fun proj -> Project.get proj Image.specification

  (* the only value of the attribute in the specification of the main
     image, if any *)
  let request attr =
    main_spec () >>| function
    | None -> None
    | Some spec -> (
        match Ogre.eval (Ogre.request attr) spec with
        | Ok x -> x
        | Error _ -> None)

  let align_up x align =
    if align <= 1 then x else (x + align - 1) / align * align

  (* the bytes below the thread pointer that are reserved for the slots
     of the thread control block that a libc keeps at negative offsets,
     e.g., bionic keeps one there *)
  let tcb_reserve = 0x100

  (* The TLS layout is the variant I, where the thread pointer points to
     the thread control block (TCB), which is followed by the TLS block
     of the executable. The TCB takes two words, e.g., on AArch64, but
     RISC-V has none. On x86, the layout is the variant II, where the
     TLS block of the executable precedes the TCB, to which the thread
     pointer points, and whose first word points to itself. *)
  let tcb_size target =
    if
      String.is_substring
        (asprintf "%a" Theory.Target.pp target)
        ~substring:"riscv"
    then 0
    else 2 * Theory.Target.code_addr_size target / 8

  (* the thread pointer of MIPS is 0x7000 bytes after the TLS block of
     the executable, as the local-exec model of its ABI tells *)
  let is_mips target =
    List.exists (target :: Theory.Target.parents target) ~f:(fun t ->
        String.is_prefix (Theory.Target.to_string t) ~prefix:"bap:mips")

  let mips_tp_offset = 0x7000

  let is_x86 target =
    List.exists (target :: Theory.Target.parents target) ~f:(fun t ->
        String.equal (Theory.Target.to_string t) "bap:x86")

  (* allocates the TLS area after [endp] and points the thread register
     to its TCB. The TLS block of the executable is initialized from its
     template (the first [init] bytes are copied from it and the rest are
     zeros), as in the main thread of the program, so that the code that
     accesses the thread-local variables of the executable (the
     local-exec model) finds their initial values. The area is zeroed,
     not generated, as the generated values are the inputs, e.g., of the
     symbolic executor. *)
  let setup_tls endp =
    thread_pointer >>= function
    | None -> Machine.return endp
    | Some tp ->
        Machine.gets Project.target >>= fun target ->
        request Image.Scheme.tls_template >>= fun template ->
        let image, size, init, align =
          match template with
          | None -> (0L, 0, 0, 1)
          | Some (addr, size, init, align) ->
              Int64.(addr, to_int_exn size, to_int_exn init, to_int_exn align)
        in
        (* the TLS block follows the TCB at the alignment of the TLS
           segment, e.g., 8 bytes after the thread pointer on ARM, which
           is aligned to 16 bytes *)
        let align = Int.max align 1 in
        let tp_align = Int.max align 16 in
        let start = Word.to_int64_exn endp in
        let tp_addr, block =
          if is_mips target then
            let block = align_up (Int64.to_int_exn start) align in
            (Int64.of_int (block + mips_tp_offset), Int64.of_int block)
          else if is_x86 target then
            let tp =
              align_up (Int64.to_int_exn start + align_up size align) tp_align
            in
            (Int64.of_int tp, Int64.of_int (tp - align_up size align))
          else
            let tp =
              Int64.of_int
                (align_up (Int64.to_int_exn start + tcb_reserve) tp_align)
            in
            (tp, Int64.(tp + of_int (align_up (tcb_size target) align)))
        in
        let total =
          let last =
            Int64.(max (block + of_int size) (tp_addr + of_int tcb_reserve))
          in
          align_up (Int.max (Int64.to_int_exn Int64.(last - start)) 1) 0x1000
        in
        Mem.allocate ~readonly:false ~executable:false
          ~init:(fun _ -> Machine.return (Word.zero 8))
          endp total
        >>= fun () ->
        make_word tp_addr >>= fun tp_word ->
        Val.of_word tp_word >>= Env.set tp >>= fun () ->
        (* the self pointer of the TCB of x86, which is little-endian *)
        (if is_x86 target then
           Word.enum_bytes tp_word LittleEndian
           |> Machine.Seq.fold ~init:tp_word ~f:(fun ptr byte ->
               Mem.store ptr byte >>| fun () -> Word.succ ptr)
           |> Machine.ignore_m
         else Machine.return ())
        >>= fun () ->
        make_word image >>= fun image ->
        make_word block >>= fun block ->
        Machine.Seq.iter (Seq.range 0 init) ~f:(fun i ->
            Mem.load (Addr.nsucc image i) >>= Mem.store (Addr.nsucc block i))
        >>| fun () -> Addr.nsucc endp total

  let segmentations =
    let open Image.Scheme in
    Ogre.foreach Ogre.Query.(select (from segment)) ~f:Fn.id

  let get_segmentations proj =
    match Project.get proj Image.specification with
    | None -> Ok Seq.empty
    | Some spec ->
        let libs = Project.libraries proj in
        let specs = spec :: List.map libs ~f:Project.Library.specification in
        List.map specs ~f:(Ogre.eval segmentations)
        |> Result.all
        |> Result.map ~f:(Fn.compose Seq.concat Seq.of_list)

  let load_segments () =
    Machine.project >>= fun proj ->
    make_word 0L >>= fun null ->
    match get_segmentations proj with
    | Error _ -> assert false
    | Ok segs ->
        Machine.Seq.fold ~init:null segs
          ~f:(fun endp { Image.Scheme.addr; size; info = _, w, x } ->
            assert (Int64.(size <> 0L));
            make_word addr >>= fun lower ->
            make_word Int64.(size - 1L) >>= fun diff ->
            let upper = Word.(lower + diff) in
            info "loading segment [%a, %a]" Addr.pp lower Addr.pp upper;
            Mem.add_region () ~lower ~upper ~readonly:(not w) ~executable:x
              ~generator:(Generator.static 0)
            >>| fun () -> Addr.max endp Addr.(succ upper))

  let one_memmap m ~init =
    Memmap.to_sequence m
    |> Machine.Seq.fold ~init ~f:(fun endp (mem, tag) ->
        match Value.get Image.segment tag with
        | None -> Machine.return endp
        | Some seg ->
            (* the segment keeps its permissions, e.g., the code, that is
               writable, which add_text would make read-only *)
            let alloc =
              Mem.map
                ~readonly:(not (Image.Segment.is_writable seg))
                ~executable:(Image.Segment.is_executable seg)
            in
            let lower = Memory.min_addr mem in
            let upper = Memory.max_addr mem in
            info "mapping segment [%a, %a]" Addr.pp lower Addr.pp upper;
            let update_ends =
              match Image.Segment.name seg with
              | ".text" -> set_word "etext" upper
              | ".data" -> set_word "edata" upper
              | _ -> Machine.return ()
            in
            alloc mem >>= fun () ->
            update_ends >>| fun () -> Addr.max endp upper)

  let map_segments () =
    Machine.project >>= fun proj ->
    make_word 0L >>= fun null ->
    one_memmap ~init:null (Project.memory proj) >>= fun init ->
    Project.libraries proj
    |> List.map ~f:Project.Library.memory
    |> Machine.List.fold ~init ~f:(fun init m -> one_memmap m ~init)

  let save_word ?(force = false) endian word ptr =
    let store = if force then Mem.store_never_fail else Mem.store in
    Word.enum_bytes word endian
    |> Machine.Seq.fold ~init:ptr ~f:(fun ptr byte ->
        store ptr byte >>| fun () -> Word.succ ptr)

  let read_word endian ptr =
    let rec aux a s =
      Mem.load a >>= fun v ->
      if s <= 8 then Machine.return v
      else
        aux (Word.succ a) (s - 8) >>| fun u ->
        match endian with
        | LittleEndian -> Word.concat u v
        | BigEndian -> Word.concat v u
    in
    aux ptr @@ Word.bitwidth ptr

  let or_empty doc x =
    Ogre.eval x doc |> Result.ok |> Option.value ~default:Seq.empty

  let relocations doc =
    Ogre.(collect Query.(select @@ from Image.Scheme.relocation))
    |> or_empty doc

  (* the difference between the addresses of the image and the
     addresses that it was linked at, i.e., the B of B + A *)
  let bias doc =
    match Ogre.eval (Ogre.request Image.Scheme.bias) doc with
    | Ok (Some bias) -> bias
    | Ok None | Error _ -> 0L

  let relative_relocations doc endian width =
    let bias = bias doc in
    let rels =
      Ogre.(collect Query.(select @@ from Image.Scheme.relative_relocation))
      |> or_empty doc
    in
    Machine.Seq.map rels ~f:(fun addr ->
        read_word endian (Word.of_int64 ~width addr) >>| fun v ->
        (addr, Int64.(bias + Word.to_int64_exn v)))

  let endian_of_target target =
    let endianness = Theory.Target.endianness target in
    if Theory.Endianness.(endianness = eb) then BigEndian else LittleEndian

  let fixup_one_reloc endian width (fixup, addr) =
    let fixup = Addr.of_int64 ~width fixup in
    let addr = Word.of_int64 ~width addr in
    debug "writing %a for relocation %a" Word.pp addr Addr.pp fixup;
    Machine.ignore_m @@ save_word ~force:true endian addr fixup

  let fixup_relocs_of_doc target doc =
    let endian = endian_of_target target in
    let width = Theory.Target.code_addr_size target in
    let rels = relocations doc in
    relative_relocations doc endian width >>= fun rrels ->
    let f = fixup_one_reloc endian width in
    Machine.Seq.iter rels ~f >>= fun () -> Machine.Seq.iter rrels ~f

  let fixup_relocs () =
    Machine.get () >>= fun project ->
    let target = Project.target project in
    let libs = Project.libraries project in
    let spec = Project.specification project in
    let specs = spec :: List.map libs ~f:Project.Library.specification in
    Machine.List.iter specs ~f:(fixup_relocs_of_doc target)

  (* the data objects of libc, which the programs of ELF import, e.g., stdin,
     whose slots, e.g., of the GOT, which the GLOB_DAT relocations fill,
     are not relocated, as they are not linked, while the weak imports,
     e.g., __gmon_start__, stay null, as the programs test them *)
  let imported_data_objects =
    String.Set.of_list
      [
        "stdin";
        "stdout";
        "stderr";
        "environ";
        "__environ";
        "optarg";
        "optind";
        "opterr";
        "optopt";
        "__stack_chk_guard";
        "__progname";
        "program_invocation_name";
        "program_invocation_short_name";
      ]

  let unversioned name =
    match String.lsplit2 name ~on:'@' with
    | Some (name, _) -> name
    | None -> name

  (* the slots, e.g., of the GOT, have contents in the file, while the
     reference of a copy relocation, e.g., of stdin on x86-64, is the
     object itself, e.g., in .bss, which the file doesn't contain, so the
     slots are found also, when the file has no sections *)
  let imported_data doc =
    let contents =
      Ogre.(collect Query.(select @@ from Image.Scheme.mapped))
      |> or_empty doc |> Seq.to_list
    in
    let in_file addr =
      List.exists contents ~f:(fun { Image.Scheme.addr = lower; size; _ } ->
          Int64.(lower <= addr && addr < lower + size))
    in
    Ogre.(collect Query.(select @@ from Image.Scheme.external_reference))
    |> or_empty doc
    |> Seq.filter ~f:(fun (addr, name) ->
        Set.mem imported_data_objects (unversioned name) && in_file addr)

  (* The slots of the functions, that the ELF file imports, e.g., the
     JUMP_SLOT relocations of the PLT, which hold the addresses of the
     lazy binding in the file, are resolved, as the dynamic linker does,
     to the code, that calls the functions by their names, e.g., their
     stubs, also when the PLT entries have no names, e.g., the PLT of
     MIPS, that lld makes, or the global entries of the GOT of MIPS. The
     weak functions, that nothing defines, have no references, see the
     ELF loader, so their slots stay null. *)
  let imported_functions doc =
    let contents =
      Ogre.(collect Query.(select @@ from Image.Scheme.mapped))
      |> or_empty doc |> Seq.to_list
    in
    let in_file addr =
      List.exists contents ~f:(fun { Image.Scheme.addr = lower; size; _ } ->
          Int64.(lower <= addr && addr < lower + size))
    in
    let code =
      Ogre.(collect Query.(select @@ from Image.Scheme.code_region))
      |> or_empty doc |> Seq.to_list
    in
    let in_code addr =
      List.exists code ~f:(fun (lower, size, _) ->
          Int64.(lower <= addr && addr < lower + size))
    in
    Ogre.(collect Query.(select @@ from Image.Scheme.external_reference))
    |> or_empty doc |> Seq.to_list
    |> List.map ~f:(fun (slot, name) -> (slot, unversioned name))
    |> List.dedup_and_sort ~compare:[%compare: int64 * string]
    |> List.filter ~f:(fun (slot, name) ->
        (not (Set.mem imported_data_objects name))
        && in_file slot
        && not (in_code slot))
    |> List.dedup_and_sort ~compare:(fun (x, _) (y, _) -> Int64.compare x y)

  let is_coff doc =
    match Ogre.eval (Ogre.request Image.Scheme.format) doc with
    | Ok (Some "coff") -> true
    | _ -> false

  (* the memory, that the loader zeroes, e.g., the storage of the imports,
     is initialized, not generated, as the generated values are the
     inputs, e.g., of the symbolic executor *)
  let zero _ = Machine.return (Word.zero 8)

  (* the slots of the imports, which the loader of the system fills, the
     data objects, with the addresses of their storage, and the functions
     with the addresses, at which the code, that calls them by their
     names, is linked, e.g., the stubs of Lisp, as the import address
     table of PE is the only way, by which the programs call them *)
  type import = Object of addr * string | Function of addr * string

  let imports doc =
    if is_coff doc then
      (* the api pass makes the imported functions subroutines, see
         api_main.ml, the other imports are the data objects *)
      Machine.gets Project.program >>= fun prog ->
      let functions =
        Term.enum sub_t prog |> Seq.map ~f:Sub.name |> Seq.to_list
        |> String.Set.of_list
      in
      Ogre.(collect Query.(select @@ from Image.Scheme.external_reference))
      |> or_empty doc |> Seq.to_list
      |> Machine.List.map ~f:(fun (slot, name) ->
          make_word slot >>| fun slot ->
          if Set.mem functions name then Function (slot, name)
          else Object (slot, name))
    else
      Machine.gets Project.target >>= fun target ->
      let endian = endian_of_target target in
      let objects =
        imported_data doc |> Seq.to_list
        |> Machine.List.filter_map ~f:(fun (slot, _) ->
            make_word slot >>= fun slot ->
            read_word endian slot >>| fun value ->
            Option.some_if (Word.is_zero value) (Object (slot, "")))
      in
      objects >>= fun objects ->
      imported_functions doc
      |> Machine.List.map ~f:(fun (slot, name) ->
          make_word slot >>| fun slot -> Function (slot, name))
      >>| fun functions -> objects @ functions

  (* the code, that calls the function by its name *)
  let call name : Primus.Linker.code =
    let module Code (Machine : Primus.Machine.S) = struct
      module Linker = Primus.Linker.Make (Machine)

      let exec = Linker.exec (`symbol name)
    end in
    (module Code)

  (* the imports get a word each, past the loaded memory, as a copy
     relocation gives a data object in the program, which is zeroed *)
  let setup_imports endp =
    Machine.get () >>= fun proj ->
    let target = Project.target proj in
    let endian = endian_of_target target in
    let size = Theory.Target.code_addr_size target / 8 in
    imports (Project.specification proj) >>= function
    | [] -> Machine.return endp
    | imports ->
        let total = align_up (List.length imports * size) 0x1000 in
        Mem.allocate ~readonly:false ~executable:false ~init:zero endp total
        >>= fun () ->
        List.mapi imports ~f:(fun i import ->
            (Addr.nsucc endp (i * size), import))
        |> Machine.List.iter ~f:(fun (addr, import) ->
            match import with
            | Object (slot, "_iob") ->
                (* the streams of msvcrt, e.g., stdin, which is &_iob[0],
                   are the file descriptors of Lisp, as __iob_func of
                   msvcrt.lisp tells *)
                make_word 0L >>= fun null ->
                Machine.ignore_m @@ save_word ~force:true endian null slot
            | Object (slot, _) ->
                Machine.ignore_m @@ save_word ~force:true endian addr slot
            | Function (slot, name) ->
                Linker.link ~addr (call name) >>= fun () ->
                Machine.ignore_m @@ save_word ~force:true endian addr slot)
        >>| fun () -> Addr.nsucc endp total

  (* The thread environment block (TEB) of Windows, which the programs of
     PE read through GS on x86-64, and FS on x86, e.g., its address at
     NtTib.Self, and the bounds of the stack, and its process environment
     block (PEB), which is zeroed, follows it, and the stack of Windows. *)
  let setup_teb endp =
    Machine.get () >>= fun proj ->
    if not (is_coff (Project.specification proj)) then Machine.return endp
    else
      let target = Project.target proj in
      let endian = endian_of_target target in
      let width = Theory.Target.code_addr_size target in
      let base, self, top, limit, peb =
        if width = 64 then ("GS_BASE", 0x30, 0x8, 0x10, 0x60)
        else ("FS_BASE", 0x18, 0x4, 0x8, 0x30)
      in
      let size = 0x2000 in
      let field off x =
        make_word x >>= fun x ->
        Machine.ignore_m @@ save_word ~force:true endian x (Addr.nsucc endp off)
      in
      Mem.allocate ~readonly:false ~executable:false ~init:zero endp size
      >>= fun () ->
      let teb = Word.to_int64_exn endp in
      field self teb >>= fun () ->
      field top stack_base >>= fun () ->
      field limit Int64.(stack_base - of_int stack_size) >>= fun () ->
      field peb Int64.(teb + 0x1000L) >>= fun () ->
      Val.of_word endp >>= Env.set (Var.create base (Type.imm width))
      >>= fun () ->
      (* the entry is called, as on Windows, with the stack aligned, so
         that the stack, whose callers own the shadow space above it, is
         below the arguments and the environment, see [setup_main_frame] *)
      ( stack_pointer >>= function
        | None -> Machine.return ()
        | Some sp ->
            make_word Int64.(stack_base - 0x88L) >>= Val.of_word >>= Env.set sp
      )
      >>| fun () -> Addr.nsucc endp size

  (* the dynamic linker of MIPS enters the program with the address of
     the entry in $t9 (R25), from which the position-independent code
     computes $gp *)
  let setup_entry_register () =
    Machine.gets Project.target >>= fun target ->
    let is_mips =
      List.exists (target :: Theory.Target.parents target) ~f:(fun t ->
          String.is_prefix (Theory.Target.to_string t) ~prefix:"bap:mips")
    in
    request Image.Scheme.entry_point >>= function
    | Some entry when is_mips ->
        let width = Theory.Target.code_addr_size target in
        Val.of_word (Word.of_int64 ~width entry)
        >>= Env.set (Var.create "R25" (Type.imm width))
    | _ -> Machine.return ()

  let irelative_relocations doc =
    Ogre.(collect Query.(select @@ from Image.Scheme.irelative_relocation))
    |> or_empty doc

  let link_register =
    Machine.gets Project.target >>| fun t ->
    Option.map ~f:Var.reify (Theory.Target.reg t Theory.Role.Register.link)

  (* the register that holds the address that a resolver returns, the
     first integer return register, as the targets that don't describe
     their return registers are x86 *)
  let return_register target =
    let name v = Theory.Var.name v in
    let by_order x y =
      Tuple2.compare ~cmp1:Int.compare ~cmp2:String.compare
        (String.length (name x), name x)
        (String.length (name y), name y)
    in
    let regs =
      Theory.Target.regs target
        ~roles:Theory.Role.Register.[ function_return; integer ]
      |> Set.to_list
      |> List.sort ~compare:by_order
    in
    match regs with
    | reg :: _ -> Some (Var.reify reg)
    | [] ->
        List.find_map [ "RAX"; "EAX" ] ~f:(Theory.Target.var target)
        |> Option.map ~f:Var.reify

  (* the code at the return address of a resolver, it does nothing, so
     the resolver returns to the loader *)
  module Return (Machine : Primus.Machine.S) = struct
    let exec = Machine.return ()
  end

  let save_registers =
    Env.all >>= fun vars ->
    Machine.Seq.filter_map vars ~f:(fun var ->
        Env.is_set var >>= function
        | false -> Machine.return None
        | true -> Env.get var >>| fun x -> Some (var, x))
    >>| Seq.to_list

  let restore_registers saved =
    Env.all >>= fun vars ->
    Machine.Seq.iter vars ~f:(fun var ->
        if List.Assoc.mem saved var ~equal:Var.equal then Machine.return ()
        else Env.del var)
    >>= fun () -> Machine.List.iter saved ~f:(fun (var, x) -> Env.set var x)

  (* passes control to the resolver with the return address [ret], in
     the link register, or on the stack, if there is none *)
  let call_resolver endian ret resolver =
    ( link_register >>= function
      | Some lr -> Val.of_word ret >>= Env.set lr
      | None -> (
          stack_pointer >>= function
          | None -> Machine.return ()
          | Some sp ->
              Env.get sp >>= fun top ->
              let width = Word.bitwidth ret in
              let size = Word.of_int ~width (width / 8) in
              let top = Word.(Primus.Value.to_word top - size) in
              save_word endian ret top >>= fun _ ->
              Val.of_word top >>= Env.set sp) )
    >>= fun () -> Linker.exec (`addr resolver)

  (* The IRELATIVE relocations store the address that the resolver of an
     indirect function returns, as the dynamic linker does at load time.
     A resolver is called with the arguments zeroed (no hardware
     capabilities), and the registers are restored after it returns, so
     a failed resolver leaves the place as it is. *)
  let resolve_indirect_functions ret () =
    Machine.get () >>= fun project ->
    let target = Project.target project in
    let endian = endian_of_target target in
    let width = Theory.Target.code_addr_size target in
    let specs =
      Project.specification project
      :: List.map (Project.libraries project) ~f:Project.Library.specification
    in
    match return_register target with
    | None -> Machine.return ()
    | Some result ->
        let rels =
          Seq.concat_map (Seq.of_list specs) ~f:irelative_relocations
        in
        if Seq.is_empty rels then Machine.return ()
        else
          Linker.link ~addr:ret (module Return) >>= fun () ->
          Machine.Seq.iter rels ~f:(fun (fixup, resolver) ->
              let fixup = Addr.of_int64 ~width fixup in
              let resolver = Addr.of_int64 ~width resolver in
              save_registers >>= fun saved ->
              Machine.catch
                ( call_resolver endian ret resolver >>= fun () ->
                  Env.get result >>| fun x -> Some (Primus.Value.to_word x) )
                (fun exn ->
                  warning "the resolver at %a for %a failed: %s" Addr.pp
                    resolver Addr.pp fixup (Primus.Exn.to_string exn);
                  Machine.return None)
              >>= fun value ->
              restore_registers saved >>= fun () ->
              match value with
              | None -> Machine.return ()
              | Some value ->
                  let value = Word.extract_exn ~hi:(width - 1) value in
                  debug "writing %a for the indirect function at %a" Word.pp
                    value Addr.pp fixup;
                  Machine.ignore_m @@ save_word ~force:true endian value fixup)
          >>= fun () -> Linker.unlink (`addr ret)

  let bytes_in_array =
    Array.fold ~init:0 ~f:(fun sum str -> sum + String.length str + 1)

  let word_of_char ch = Word.of_int ~width:8 (Char.to_int ch)

  let save_string str ptr =
    String.to_list str
    |> Machine.List.fold ~init:ptr ~f:(fun ptr char ->
        Mem.store ptr (word_of_char char) >>| fun () -> Word.succ ptr)

  let save_args array ptr =
    Seq.of_array array
    |> Machine.Seq.fold ~init:(ptr, []) ~f:(fun (ptr', ptrs) str ->
        save_string str ptr' >>= save_string "\x00" >>| fun ptr ->
        (ptr, ptr' :: ptrs))
    >>| fun (ptr, ptrs) -> (ptr, List.rev ptrs)

  let save_table endian addrs ptr =
    Machine.List.fold addrs ~init:ptr ~f:(fun ptr addr ->
        save_word endian addr ptr)

  (* the types of the auxiliary vector entries, see <elf.h> *)
  let at_null = 0
  let at_phdr = 3
  let at_phent = 4
  let at_phnum = 5
  let at_pagesz = 6
  let at_base = 7
  let at_flags = 8
  let at_entry = 9
  let at_uid = 11
  let at_euid = 12
  let at_gid = 13
  let at_egid = 14
  let at_hwcap = 16
  let at_clktck = 17
  let at_secure = 23
  let at_random = 25
  let at_hwcap2 = 26

  (* the bytes that AT_RANDOM points to *)
  let random_size = 16

  (* The auxiliary vector, which the kernel passes to a program after
     its environment, as [(type, value)] pairs. There is no dynamic
     linker (AT_BASE is 0), the hardware capabilities are empty, and
     [random] is the address of the AT_RANDOM bytes. *)
  let auxiliary_vector random =
    request Image.Scheme.program_headers >>= fun phdrs ->
    request Image.Scheme.entry_point >>| fun entry ->
    List.concat
      [
        (match phdrs with
        | None -> []
        | Some (addr, size, count) ->
            [ (at_phdr, addr); (at_phent, size); (at_phnum, count) ]);
        [ (at_pagesz, 4096L); (at_base, 0L); (at_flags, 0L) ];
        Option.value_map entry ~default:[] ~f:(fun e -> [ (at_entry, e) ]);
        [
          (at_uid, 0L);
          (at_euid, 0L);
          (at_gid, 0L);
          (at_egid, 0L);
          (at_hwcap, 0L);
          (at_hwcap2, 0L);
          (at_clktck, 100L);
          (at_secure, 0L);
          (at_random, random);
          (at_null, 0L);
        ];
      ]

  let setup_main_frame () =
    Machine.gets Project.target >>= fun target ->
    Machine.args >>= fun argv ->
    Machine.envp >>= fun envp ->
    make_word stack_base >>= fun sp ->
    let endian = endian_of_target target in
    let width = Theory.Target.code_addr_size target in
    let argc = Array.length argv |> Word.of_int ~width in
    let bytes_in_addr = width / 8 in
    let null = String.make bytes_in_addr '\x00' in
    let frame_size args = bytes_in_array args in
    let table_size args = bytes_in_addr * (Array.length args + 1) in
    let auxv_ptr =
      bytes_in_addr + table_size argv + table_size envp |> Addr.nsucc sp
    in
    (* the size of the auxiliary vector doesn't depend on the address of
       the random bytes *)
    auxiliary_vector 0L >>= fun auxv ->
    let auxv_size = 2 * bytes_in_addr * List.length auxv in
    let random_ptr = Addr.nsucc auxv_ptr auxv_size in
    auxiliary_vector (Word.to_int64_exn random_ptr) >>= fun auxv ->
    let argv_frame_ptr = Addr.nsucc random_ptr random_size in
    let total_size =
      Word.(to_int_exn (argv_frame_ptr - sp))
      + frame_size argv + frame_size envp
    in
    let argv_table_ptr = Addr.nsucc sp bytes_in_addr in
    Mem.allocate ~readonly:false ~executable:false sp total_size >>= fun () ->
    save_args argv argv_frame_ptr >>= fun (envp_frame_ptr, argv_table) ->
    save_args envp envp_frame_ptr >>= fun (_end_of_stack, envp_table) ->
    save_table endian argv_table argv_table_ptr >>= fun end_of_argv_table ->
    save_string null end_of_argv_table >>= fun envp_table_ptr ->
    save_table endian envp_table envp_table_ptr >>= fun end_of_envp_table ->
    save_string null end_of_envp_table >>= fun _auxv_ptr ->
    assert (Word.(auxv_ptr = _auxv_ptr));
    Machine.List.fold auxv ~init:auxv_ptr ~f:(fun ptr (typ, value) ->
        save_word endian (Word.of_int ~width typ) ptr
        >>= save_word endian (Word.of_int64 ~width value))
    >>= fun _random_ptr ->
    assert (Word.(random_ptr = _random_ptr));
    save_string (String.make random_size '\x00') random_ptr
    >>= fun _argv_frame_ptr ->
    assert (Word.(argv_frame_ptr = _argv_frame_ptr));
    save_word endian argc sp >>= fun _ ->
    set_word "posix:environ" envp_table_ptr

  let names prog =
    let add t env =
      match Term.get_attr t address with
      | Some addr -> Map.set env ~key:(Term.name t) ~data:addr
      | None -> env
    in
    let visitor =
      object
        inherit [addr String.Map.t] Term.visitor
        method! enter_blk = add
        method! enter_sub = add
      end
    in
    visitor#run prog String.Map.empty

  let init_names () =
    Machine.get () >>= fun proj ->
    Map.to_sequence (names (Project.program proj))
    |> Machine.Seq.iter ~f:(fun (name, addr) -> set_word name addr)

  let init () =
    debug "setting up stack";
    setup_stack () >>= fun () ->
    debug "setting up main frame";
    setup_main_frame () >>= fun () ->
    debug "loading segments";
    load_segments () >>= fun e1 ->
    debug "mapping segments";
    map_segments () >>= fun e2 ->
    debug "fixing up relocations";
    fixup_relocs () >>= fun () ->
    debug "setting up registers";
    let endp = Addr.max e1 e2 in
    setup_registers () >>= fun () ->
    setup_entry_register () >>= fun () ->
    debug "setting up thread-local storage";
    setup_tls endp >>= fun endp ->
    debug "setting up the imports";
    setup_imports endp >>= fun endp ->
    debug "setting up the thread environment block";
    setup_teb endp >>= fun endp ->
    set_word "posix:endp" endp >>= fun () ->
    set_word "posix:brk" endp >>= fun () ->
    (* the arguments and the environment, e.g., for __getmainargs of
       msvcrt, which the programs of PE call *)
    make_word stack_base >>= set_word "posix:main-frame" >>= fun () ->
    debug "initializing names";
    init_names () >>= fun () ->
    (* the resolvers are run when the code is linked, and they return
       to the first address past the loaded memory *)
    Primus.System.init >>> resolve_indirect_functions endp
end
