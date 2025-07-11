open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
open Format

include Self()

module Generator = Primus.Generator

module type Param = sig
  val stack_size : int
  val stack_base : int64
end

module Make(Param : Param)(Machine : Primus.Machine.S)  = struct
  open Param
  open Machine.Syntax

  module Env = Primus.Env.Make(Machine)
  module Mem = Primus.Memory.Make(Machine)
  module Val = Primus.Value.Make(Machine)

  let make_word addr =
    Machine.gets Project.target >>|
    Theory.Target.code_addr_size >>| fun width ->
    Addr.of_int64 ~width addr

  let set_word name x =
    let t = Type.imm (Word.bitwidth x) in
    let var = Var.create name t in
    Val.of_word x >>=
    Env.set var

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
      Mem.allocate
        ~readonly:false
        ~executable:false
        top stack_size

  let setup_registers () =
    let zero = Generator.static 0 in
    Machine.gets Project.target >>= fun t ->
    Set.to_sequence (Theory.Target.vars t) |>
    Machine.Seq.iter ~f:(fun reg -> Env.add (Var.reify reg) zero)

  let rec is set = function
    | Backend.Or (p1,p2) -> is set p1 || is set p2
    | bit -> [%compare.equal : Backend.perm] bit set

  let segmentations =
    let open Image.Scheme in
    Ogre.foreach Ogre.Query.(begin
        select (from segment)
      end)
      ~f:Fn.id

  let get_segmentations proj =
    match Project.get proj Image.specification with
    | None -> Ok Seq.empty
    | Some spec ->
      let libs = Project.libraries proj in
      let specs = spec :: List.map libs ~f:Project.Library.specification in
      List.map specs ~f:(Ogre.eval segmentations) |> Result.all |>
      Result.map ~f:(Fn.compose Seq.concat Seq.of_list)

  let load_segments () =
    Machine.project >>= fun proj ->
    make_word 0L >>= fun null ->
    match get_segmentations proj with
    | Error _ -> assert false
    | Ok segs ->
      Machine.Seq.fold ~init:null segs
        ~f:(fun endp {Image.Scheme.addr; size; info=(_,w,x)} ->
            assert Int64.(size <> 0L);
            make_word addr >>= fun lower ->
            make_word Int64.(size-1L) >>= fun diff ->
            let upper = Word.(lower + diff) in
            info "loading segment [%a, %a]" Addr.pp lower Addr.pp upper;
            Mem.add_region () ~lower ~upper
              ~readonly:(not w)
              ~executable:x
              ~generator:(Generator.static 0) >>| fun () ->
            Addr.max endp Addr.(succ upper))

  let one_memmap m ~init =
    Memmap.to_sequence m |>
    Machine.Seq.fold ~init ~f:(fun endp (mem,tag) ->
        match Value.get Image.segment tag with
        | None -> Machine.return endp
        | Some seg ->
          let alloc =
            if Image.Segment.is_executable seg
            then Mem.add_text else Mem.add_data in
          let lower = Memory.min_addr mem in
          let upper = Memory.max_addr mem in
          info "mapping segment [%a, %a]" Addr.pp lower Addr.pp upper;
          let update_ends = match Image.Segment.name seg with
            | ".text" -> set_word "etext" upper
            | ".data" -> set_word "edata" upper
            | _ -> Machine.return () in
          alloc mem >>= fun () ->
          update_ends >>| fun ()  ->
          Addr.max endp upper)

  let map_segments () =
    Machine.project >>= fun proj ->
    make_word 0L >>= fun null ->
    one_memmap ~init:null (Project.memory proj) >>= fun init ->
    Project.libraries proj |> List.map ~f:Project.Library.memory |>
    Machine.List.fold ~init ~f:(fun init m -> one_memmap m ~init)

  let save_word ?(force=false) endian word ptr =
    let store = if force then Mem.store_never_fail else Mem.store in
    Word.enum_bytes word endian |>
    Machine.Seq.fold ~init:ptr ~f:(fun ptr byte ->
        store ptr byte >>| fun () ->
        Word.succ ptr)

  let read_word endian ptr =
    let rec aux a s =
      Mem.load a >>= fun v ->
      if s <= 8 then Machine.return v
      else aux (Word.succ a) (s - 8) >>| fun u -> match endian with
        | LittleEndian -> Word.concat u v
        | BigEndian -> Word.concat v u in
    aux ptr @@ Word.bitwidth ptr

  let or_empty doc x =
    Ogre.eval x doc |> Result.ok |> Option.value ~default:Seq.empty

  let relocations doc = Ogre.(collect Query.(begin
      select @@ from Image.Scheme.relocation
    end)) |> or_empty doc

  let base_address = Ogre.require Image.Scheme.base_address

  let relative_relocations doc endian width =
    match Ogre.eval base_address doc with
    | Error _ -> !!Seq.empty
    | Ok base ->
      let rels = Ogre.(collect Query.(begin
          select @@ from Image.Scheme.relative_relocation
        end)) |> or_empty doc in
      Machine.Seq.map rels ~f:(fun addr ->
          read_word endian (Word.of_int64 ~width addr) >>| fun v ->
          addr, Int64.(base + Word.to_int64_exn v))

  let endian_of_target target =
    let endianness = Theory.Target.endianness target in
    if Theory.Endianness.(endianness = eb)
    then BigEndian else LittleEndian

  let fixup_one_reloc endian width (fixup, addr) =
    let fixup = Addr.of_int64 ~width fixup in
    let addr = Word.of_int64 ~width addr in
    debug "writing %a for relocation %a" Word.pp addr Addr.pp fixup;
    Machine.ignore_m @@
    save_word ~force:true endian addr fixup

  let fixup_relocs_of_doc target doc =
    let endian = endian_of_target target in
    let width = Theory.Target.code_addr_size target in
    let rels = relocations doc in
    relative_relocations doc endian width >>= fun rrels ->
    let f = fixup_one_reloc endian width in
    Machine.Seq.iter rels ~f >>= fun () ->
    Machine.Seq.iter rrels ~f

  let fixup_relocs () =
    Machine.get () >>= fun project ->
    let target = Project.target project in
    let libs = Project.libraries project in
    let spec = Project.specification project in
    let specs = spec :: List.map libs ~f:Project.Library.specification in
    Machine.List.iter specs ~f:(fixup_relocs_of_doc target)

  let bytes_in_array =
    Array.fold ~init:0 ~f:(fun sum str ->
        sum + String.length str + 1)

  let word_of_char ch = Word.of_int ~width:8 (Char.to_int ch)

  let save_string str ptr =
    String.to_list str |>
    Machine.List.fold ~init:ptr ~f:(fun ptr char ->
        Mem.store ptr (word_of_char char) >>| fun () ->
        Word.succ ptr)

  let save_args array ptr =
    Seq.of_array array |>
    Machine.Seq.fold ~init:(ptr,[]) ~f:(fun (ptr',ptrs) str ->
        save_string str ptr' >>=
        save_string "\x00"  >>| fun ptr ->
        (ptr,ptr'::ptrs)) >>| fun (ptr,ptrs) ->
    ptr, List.rev ptrs

  let save_table endian addrs ptr =
    Machine.List.fold addrs ~init:ptr ~f:(fun ptr addr ->
        save_word endian addr ptr)

  let setup_main_frame () =
    Machine.gets Project.target >>= fun target ->
    Machine.args >>= fun argv ->
    Machine.envp >>= fun envp ->
    make_word stack_base >>= fun sp ->
    let endian = endian_of_target target in
    let width = Theory.Target.code_addr_size target in
    let argc = Array.length argv |>
               Word.of_int ~width in
    let bytes_in_addr = width / 8 in
    let null = String.make bytes_in_addr '\x00' in
    let frame_size args = bytes_in_array args in
    let table_size args = bytes_in_addr * (Array.length args + 1) in
    let total_size =
      bytes_in_addr +    (* argc *)
      table_size argv + table_size envp +
      frame_size argv + frame_size envp in
    let argv_frame_ptr =
      bytes_in_addr +
      table_size  argv + table_size envp |>
      Addr.nsucc sp in
    let argv_table_ptr = Addr.nsucc sp bytes_in_addr in
    Mem.allocate
      ~readonly:false
      ~executable:false
      sp total_size >>= fun () ->
    save_args argv argv_frame_ptr >>=
    fun (envp_frame_ptr, argv_table) ->
    save_args envp envp_frame_ptr >>=
    fun (_end_of_stack, envp_table) ->
    save_table endian argv_table argv_table_ptr >>=
    fun end_of_argv_table ->
    save_string null end_of_argv_table >>=
    fun envp_table_ptr ->
    save_table endian envp_table envp_table_ptr >>=
    fun end_of_envp_table ->
    save_string null end_of_envp_table >>=
    fun _argv_frame_ptr ->
    assert Word.(argv_frame_ptr = _argv_frame_ptr);
    save_word endian argc sp >>= fun _ ->
    set_word "posix:environ" envp_table_ptr

  let names prog =
    let add t env = match Term.get_attr t address with
      | Some addr -> Map.set env ~key:(Term.name t) ~data:addr
      | None -> env in
    let visitor = object
      inherit [addr String.Map.t] Term.visitor
      method! enter_blk = add
      method! enter_sub = add
    end in
    visitor#run prog String.Map.empty

  let init_names () =
    Machine.get () >>= fun proj ->
    Map.to_sequence (names (Project.program proj)) |>
    Machine.Seq.iter ~f:(fun (name,addr) -> set_word name addr)

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
    set_word "posix:endp" endp >>= fun () ->
    set_word "posix:brk"  endp >>= fun () ->
    setup_registers () >>= fun () ->
    debug "initializing names";
    init_names ()
end
