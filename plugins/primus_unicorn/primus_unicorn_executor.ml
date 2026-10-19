(* Runs the subroutines of the binary program in Unicorn.

   The machine state stays in Primus, Unicorn borrows it while it runs:

   - the registers are written to Unicorn before it starts and are read
     back when it stops;

   - the memory pages are copied from Primus when Unicorn faults on
     them, and the writable pages are copied back, if they were changed,
     and dropped when Unicorn stops, since Primus may change them;

   - the code that Primus links instead of the program, e.g., the Lisp
     stubs, stops Unicorn at its address and is called by the Primus
     linker, after which Unicorn continues from the return address.

   A run ends when the subroutine returns, i.e., when the code reaches
   its return address with the stack pointer of the caller. *)

open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
module Uc = Bap_unicorn
module Target = Primus_unicorn_target

type Primus.exn += Unicorn_failure of string

let () =
  Primus.Exn.add_printer (function
    | Unicorn_failure msg -> Some ("Unicorn: " ^ msg)
    | _ -> None)

exception Unsupported of string

let page_size = 0x1000L
let page_of addr = Int64.(addr land lnot (page_size - 1L))

type reason =
  | Returned
  | Foreign of int64
  | Fault of Uc.access * int64
  | Interrupt of int
  | Invalid

(* a pending return of a run *)
type frame = { ret : int64; sp : int64 }
type page = { mutable snapshot : string option }

type engine = {
  uc : Uc.t;
  arch : Uc.arch;
  regs : Target.Regs.t;
  pc : int;
  sp : var;
  link : var option;
  bytes : int;  (** the size of an address *)
  basis : var list;  (** the mapped registers that are not aliases *)
  pages : page Int64.Table.t;
  trampolines : string Int64.Table.t;
      (** the addresses that stand for the external functions *)
  slots : (int * int64) list Int64.Table.t;
      (** the offsets in the pages of the slots, e.g., of GOT, which refer to
          the external functions, and their trampolines *)
  big_endian : bool;
  mutable owner : Primus.Machine.id option;
  mutable reason : reason option;
  mutable frames : frame list;
  mutable broken : bool;
      (** Unicorn 2.1.4 crashes on MIPS after a fetch fault, so the engine is
          created anew *)
}

let engine : engine option ref = ref None

(* the arguments of [create] *)
let recipe : (Theory.Target.t * int64 list * (int64 * string) list) option ref =
  ref None

(* the code that runs the subroutines in Unicorn, see [Loader] *)
let own_code : Primus.Linker.code Addr.Table.t = Addr.Table.create ()
let int64_of_word w = Bitvec.to_int64 (Word.to_bitvec w)

let var_of_reg v =
  Var.create (Theory.Var.name v)
    (Type.imm (Theory.Bitv.size (Theory.Var.sort v)))

let is_alias target v =
  Theory.Target.has_roles target [ Theory.Role.Register.alias ] v

let reg_of_role target role =
  Option.bind (Theory.Target.reg target role) ~f:(fun v ->
      Option.map
        (Theory.Bitv.refine (Theory.Var.sort v))
        ~f:(fun s ->
          Var.create (Theory.Var.name v) (Type.imm (Theory.Bitv.size s))))

(* the register that holds the return address *)
let link_register target (arch : Uc.arch) =
  let bits = Theory.Target.bits target in
  let reg name = Some (Var.create name (Type.imm bits)) in
  match arch with
  | X86 -> None
  | Arm | Ppc -> reg "LR"
  | Arm64 -> reg "R30"
  | Mips -> reg "R31"
  | Riscv -> reg "X1"

let failf fmt = ksprintf (fun msg -> raise (Unsupported msg)) fmt

(* The external functions, which the code calls through the slots that
   the dynamic linker fills, get the addresses in a reserved region,
   which is never mapped in Primus, and the slots of the pages copied
   to Unicorn refer to them. *)
let trampolines_base target =
  if Theory.Target.bits target = 64 then 0x7FFF_FFF0_0000L else 0xFFFF_0000L

let trampoline_size = 16L

let create target ~foreign ~externals =
  let arch, mode =
    match Target.engine target with
    | Some e -> e
    | None ->
        failf "the target %s is not supported" (Theory.Target.to_string target)
  in
  let uc = Uc.create arch mode in
  (* the addresses of the program are the addresses of Unicorn *)
  Uc.set_tlb_virtual uc;
  (* the 64-bit addresses of MIPS are enabled by the KX, SX, and UX bits *)
  (match arch with
  | Mips when Theory.Target.bits target = 64 ->
      let status = Option.value_exn (Uc.reg Mips "CP0_STATUS") in
      Uc.reg_write uc status Int64.(Uc.reg_read uc status lor 0xE0L)
  | _ -> ());
  let regs = Target.Regs.create target arch uc in
  let sp =
    match reg_of_role target Theory.Role.Register.stack_pointer with
    | Some sp -> sp
    | None -> failf "the target has no stack pointer"
  in
  let basis = Target.Regs.basis regs in
  let e =
    {
      uc;
      arch;
      regs;
      pc = Target.pc arch mode;
      sp;
      link = link_register target arch;
      bytes = Theory.Target.bits target / 8;
      basis;
      pages = Int64.Table.create ();
      owner = None;
      reason = None;
      frames = [];
      broken = false;
      trampolines = Int64.Table.create ();
      slots = Int64.Table.create ();
      big_endian =
        Theory.Endianness.(equal eb) (Theory.Target.endianness target);
    }
  in
  let base = trampolines_base target in
  let addrs = String.Table.create () in
  List.iter externals ~f:(fun (slot, name) ->
      let addr =
        Hashtbl.find_or_add addrs name ~default:(fun () ->
            let addr =
              Int64.(base + (of_int (Hashtbl.length addrs) * trampoline_size))
            in
            Hashtbl.set e.trampolines ~key:addr ~data:name;
            addr)
      in
      Hashtbl.add_multi e.slots ~key:(page_of slot)
        ~data:(Int64.(to_int_exn (slot - page_of slot)), addr));
  if not (Hashtbl.is_empty addrs) then begin
    let size =
      Int64.(
        page_of
          ((of_int (Hashtbl.length addrs) * trampoline_size) + page_size - 1L))
    in
    Uc.mem_map uc base size Uc.Perm.(read + exec);
    ignore
    @@ Uc.on_code uc ~first:base
         ~last:Int64.(base + size - 1L)
         (fun addr _ ->
           e.reason <- Some (Foreign addr);
           Uc.stop uc)
  end;
  let stop reason =
    e.reason <- Some reason;
    Uc.stop uc
  in
  List.iter foreign ~f:(fun addr ->
      ignore
      @@ Uc.on_code uc ~first:addr ~last:addr (fun _ _ -> stop (Foreign addr)));
  let returns addr =
    match e.frames with
    | { ret; sp } :: _ ->
        Int64.(ret = addr)
        && Int64.(
             int64_of_word (Option.value_exn (Target.Regs.read regs e.sp)) = sp)
    | [] -> false
  in
  ignore
  @@ Uc.on_mem_invalid uc [ `read; `write; `fetch ] [ `unmapped; `prot ]
       (fun access addr _ _ ->
         (match access with
         | Fetch_unmapped when returns addr -> e.reason <- Some Returned
         | _ -> e.reason <- Some (Fault (access, addr)));
         (match (access, arch) with
         | Fetch_unmapped, Mips -> e.broken <- true
         | _ -> ());
         false);
  ignore @@ Uc.on_interrupt uc (fun n -> stop (Interrupt n));
  ignore
  @@ Uc.on_invalid_insn uc (fun () ->
      e.reason <- Some Invalid;
      false);
  e

module Make (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  open Machine.Let
  module Env = Primus.Env.Make (Machine)
  module Memory = Primus.Memory.Make (Machine)
  module Value = Primus.Value.Make (Machine)
  module Linker = Primus.Linker.Make (Machine)

  let fail fmt = ksprintf (fun msg -> Machine.raise (Unicorn_failure msg)) fmt
  let word e x = Word.of_int64 ~width:(e.bytes * 8) x

  let engine () =
    match (!engine, !recipe) with
    | Some e, Some (target, foreign, externals)
      when e.broken && List.is_empty e.frames ->
        Uc.close e.uc;
        let e = create target ~foreign ~externals in
        engine := Some e;
        Machine.return e
    | Some e, _ -> Machine.return e
    | None, _ -> fail "the engine is not initialized"

  (* the pages of the memory of another machine are not valid *)
  let claim e =
    let+ id = Machine.current () in
    match e.owner with
    | Some owner when Monads.Std.Monad.State.Multi.Id.equal owner id -> false
    | _ ->
        Hashtbl.iter_keys e.pages ~f:(fun page ->
            Uc.mem_unmap e.uc page page_size);
        Hashtbl.clear e.pages;
        e.owner <- Some id;
        true

  let load_byte addr =
    let* mapped = Memory.is_mapped addr in
    if mapped then
      let+ x = Memory.load addr in
      Char.of_int_exn (Word.to_int_exn x)
    else Machine.return '\000'

  let map_page e page =
    let base = word e page in
    let* writable = Memory.is_writable base in
    let bytes = Bytes.create (Int64.to_int_exn page_size) in
    let* () =
      Machine.List.iter
        (List.init (Bytes.length bytes) ~f:Fn.id)
        ~f:(fun i ->
          let+ c = load_byte Word.(base ++ i) in
          Bytes.set bytes i c)
    in
    List.iter (Hashtbl.find_multi e.slots page) ~f:(fun (off, addr) ->
        if off + e.bytes <= Bytes.length bytes then
          List.iteri (List.init e.bytes ~f:Fn.id) ~f:(fun i _ ->
              let shift = if e.big_endian then e.bytes - 1 - i else i in
              let byte =
                Int64.(shift_right_logical addr Int.(8 * shift) land 0xFFL)
              in
              Bytes.set bytes (off + i)
                (Char.of_int_exn (Int64.to_int_exn byte))));
    let data = Bytes.to_string bytes in
    let perm = Uc.Perm.(read + exec + if writable then write else none) in
    Uc.mem_map e.uc page page_size perm;
    Uc.mem_write e.uc page data;
    Hashtbl.set e.pages ~key:page
      ~data:{ snapshot = (if writable then Some data else None) };
    Machine.return ()

  let ensure_page e addr =
    let page = page_of addr in
    if Hashtbl.mem e.pages page then Machine.return ()
    else
      let* mapped = Memory.is_mapped (word e addr) in
      if mapped then map_page e page else Machine.return ()

  (* maps the code, so that it is never fetched from unmapped pages,
     see [broken] *)
  let map_code e =
    match e.arch with
    | Mips ->
        let* memory = Machine.gets Project.memory in
        Memmap.to_sequence memory
        |> Seq.filter_map ~f:(fun (mem, tag) ->
            match Bap.Std.Value.get Image.segment tag with
            | Some seg when Image.Segment.is_executable seg -> Some mem
            | _ -> None)
        |> Seq.to_list
        |> Machine.List.iter ~f:(fun mem ->
            let first = page_of (int64_of_word (Bap.Std.Memory.min_addr mem)) in
            let last = int64_of_word (Bap.Std.Memory.max_addr mem) in
            let pages =
              List.init
                (Int64.to_int_exn Int64.((last - first) / page_size) + 1)
                ~f:(fun i -> Int64.(first + (of_int i * page_size)))
            in
            Machine.List.iter pages ~f:(ensure_page e))
    | _ -> Machine.return ()

  (* copies the registers from Primus, the aliases go first, so that
     the registers of the program win *)
  let push e =
    let* vars = Env.all in
    let vars = Seq.to_list vars |> List.filter ~f:(Target.Regs.mem e.regs) in
    let is_basis v = List.mem e.basis v ~equal:Var.equal in
    let aliases, basis = List.partition_tf vars ~f:(Fn.non is_basis) in
    Machine.List.iter (aliases @ basis) ~f:(fun v ->
        let+ x = Env.get v in
        ignore (Target.Regs.write e.regs v (Primus.Value.to_word x)))

  let store_page e page snapshot =
    let data = Uc.mem_read e.uc page (Int64.to_int_exn page_size) in
    if String.equal data snapshot then Machine.return ()
    else
      let base = word e page in
      Machine.List.iter
        (List.init (String.length data) ~f:Fn.id)
        ~f:(fun i ->
          if Char.equal data.[i] snapshot.[i] then Machine.return ()
          else
            Memory.store_never_fail
              Word.(base ++ i)
              (Word.of_int ~width:8 (Char.to_int data.[i])))

  (* copies the registers and the changed memory to Primus and drops
     the writable pages *)
  let pull e =
    let* () =
      Machine.List.iter e.basis ~f:(fun v ->
          match Target.Regs.read e.regs v with
          | None -> Machine.return ()
          | Some x -> Value.of_word x >>= Env.set v)
    in
    let writable =
      Hashtbl.fold e.pages ~init:[] ~f:(fun ~key ~data acc ->
          match data.snapshot with
          | Some snapshot -> (key, snapshot) :: acc
          | None -> acc)
    in
    let+ () =
      Machine.List.iter writable ~f:(fun (page, snapshot) ->
          store_page e page snapshot)
    in
    List.iter writable ~f:(fun (page, _) ->
        Uc.mem_unmap e.uc page page_size;
        Hashtbl.remove e.pages page)

  let load_word e addr =
    let+ bytes =
      Machine.List.map (List.init e.bytes ~f:Fn.id) ~f:(fun i ->
          Memory.load Word.(addr ++ i))
    in
    (* the order of the bytes of the return address on x86 *)
    List.fold (List.rev bytes) ~init:0L ~f:(fun acc b ->
        Int64.((acc lsl 8) lor int64_of_word b))

  (* the return address of the call that just started and the stack
     pointer after the return *)
  let frame e =
    let* sp = Env.get e.sp in
    let sp = Primus.Value.to_word sp in
    match e.link with
    | Some lr ->
        let+ ret = Env.get lr in
        {
          ret = int64_of_word (Primus.Value.to_word ret);
          sp = int64_of_word sp;
        }
    | None ->
        let+ ret = load_word e sp in
        { ret; sp = Int64.(int64_of_word sp + of_int e.bytes) }

  (* the address of the code at which Unicorn starts, which on ARM marks
     the Thumb code with the lower bit *)
  let address e { ret; _ } =
    match e.arch with Arm -> Int64.(ret land lnot 1L) | _ -> ret

  let fault e access addr =
    match (access : Uc.access) with
    | Read_unmapped | Write_unmapped | Fetch_unmapped ->
        let* mapped = Memory.is_mapped (word e addr) in
        if mapped then map_page e (page_of addr) >>| fun () -> `Continue
        else
          (* raises the Primus page fault *)
          pull e >>= fun () ->
          Memory.get (word e addr) >>= fun _ -> fail "page fault at %Lx" addr
    | Write_prot ->
        pull e >>= fun () ->
        let* x = Memory.get (word e addr) in
        Memory.set (word e addr) x >>= fun () ->
        fail "write to the read-only memory at %Lx" addr
    | _ -> pull e >>= fun () -> fail "access to %Lx is denied" addr

  let call_foreign e addr =
    let* () = pull e in
    let* frame = frame e in
    let name =
      match Hashtbl.find e.trampolines addr with
      | Some name -> `symbol name
      | None -> `addr (word e addr)
    in
    let* () = Linker.exec name in
    let* () = push e in
    (* the return address is popped on x86, if the stub did not *)
    if Option.is_none e.link then
      ignore (Target.Regs.write e.regs e.sp (word e frame.sp));
    Machine.return frame.ret

  let rec loop e pc =
    ensure_page e pc >>= fun () ->
    e.reason <- None;
    let error =
      try
        Uc.start e.uc pc;
        None
      with Uc.Error (_, msg) -> Some msg
    in
    let pc = Uc.reg_read e.uc e.pc in
    match (e.reason, error) with
    | Some Returned, _ | None, None -> pull e
    | Some (Foreign addr), _ -> call_foreign e addr >>= loop e
    | Some (Fault (access, addr)), _ -> (
        fault e access addr >>= function `Continue -> loop e pc)
    | Some (Interrupt n), _ ->
        pull e >>= fun () -> fail "an unhandled interrupt %d at %Lx" n pc
    | Some Invalid, _ ->
        pull e >>= fun () -> fail "an invalid instruction at %Lx" pc
    | None, Some msg -> pull e >>= fun () -> fail "%s at %Lx" msg pc

  let run addr =
    let* e = engine () in
    let* claimed = claim e in
    let* () = if claimed then map_code e else Machine.return () in
    let* () = push e in
    let* frame = frame e in
    let ret = address e frame in
    let hook =
      Uc.on_code e.uc ~first:ret ~last:ret (fun _ _ ->
          match e.frames with
          | top :: _ when Int64.(top.ret = ret) -> (
              match Target.Regs.read e.regs e.sp with
              | Some sp when Int64.(int64_of_word sp = top.sp) ->
                  e.reason <- Some Returned;
                  Uc.stop e.uc
              | _ -> ())
          | _ -> ())
    in
    e.frames <- { frame with ret } :: e.frames;
    let finish () =
      e.frames <- List.tl_exn e.frames;
      Uc.delete e.uc hook
    in
    Machine.catch
      (loop e (int64_of_word addr) >>| finish)
      (fun exn ->
        finish ();
        Machine.raise exn)
end

(* links the program, as load-binary does, except that its subroutines
   run in Unicorn, and keeps the linked code to tell the addresses of the
   subroutines that other components replace *)
module Loader (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  open Machine.Let
  module Linker = Primus.Linker.Make (Machine)

  let is_linked name t =
    let* linked =
      Machine.List.exists
        [ `tid (Term.tid t); `symbol (name t) ]
        ~f:Linker.is_linked
    in
    if linked then Machine.return true
    else
      match Term.get_attr t address with
      | None -> Machine.return false
      | Some addr -> Linker.is_linked (`addr addr)

  let link_blk blk =
    let* linked = is_linked Term.name blk in
    if linked then Machine.return ()
    else
      let module Code (Machine : Primus.Machine.S) = struct
        module Interp = Primus.Interpreter.Make (Machine)

        let exec = Interp.blk blk
      end in
      Linker.link ~name:(Term.name blk) ~tid:(Term.tid blk)
        ?addr:(Term.get_attr blk address)
        (module Code)

  let link_sub sub =
    let* linked = is_linked Sub.name sub in
    if linked then Machine.return ()
    else
      match Term.get_attr sub address with
      | None ->
          let module Code (Machine : Primus.Machine.S) = struct
            module Interp = Primus.Interpreter.Make (Machine)

            let exec = Interp.sub sub
          end in
          Linker.link ~name:(Sub.name sub) ~tid:(Term.tid sub) (module Code)
      | Some addr ->
          let module Code (Machine : Primus.Machine.S) = struct
            module Exec = Make (Machine)

            let exec = Exec.run addr
          end in
          let code : Primus.Linker.code = (module Code) in
          Hashtbl.set own_code ~key:addr ~data:code;
          Linker.link ~addr ~name:(Sub.name sub) ~tid:(Term.tid sub) code

  let link_program =
    let* prog = Machine.gets Project.program in
    Term.enum sub_t prog |> Seq.to_list
    |> Machine.List.iter ~f:(fun sub ->
        let* () = link_sub sub in
        Term.enum blk_t sub |> Seq.to_list |> Machine.List.iter ~f:link_blk)

  (* the references to the external functions of the program *)
  let externals () =
    let* proj = Machine.get () in
    let prog = Project.program proj in
    let functions =
      Term.enum sub_t prog |> Seq.map ~f:Sub.name |> Seq.to_list
      |> String.Set.of_list
    in
    match
      Ogre.eval
        (Ogre.collect
           Ogre.Query.(select (from Image.Scheme.external_reference)))
        (Project.specification proj)
    with
    | Error _ -> Machine.return []
    | Ok refs ->
        Machine.return @@ Seq.to_list
        @@ Seq.filter refs ~f:(fun (_, name) -> Set.mem functions name)

  (* the subroutines, whose code the other components replaced, stop
     Unicorn *)
  let create_engine () =
    let* target = Machine.gets Project.target in
    let* foreign =
      Hashtbl.keys own_code
      |> Machine.List.filter_map ~f:(fun addr ->
          Linker.lookup (`addr addr) >>| function
          | Some code when phys_equal code (Hashtbl.find_exn own_code addr) ->
              None
          | _ -> Some (int64_of_word addr))
    in
    (match !engine with Some e -> Uc.close e.uc | None -> ());
    engine := None;
    let* externals = externals () in
    recipe := Some (target, foreign, externals);
    match create target ~foreign ~externals with
    | exception Unsupported msg -> Machine.raise (Unicorn_failure msg)
    | e ->
        engine := Some e;
        Machine.return ()

  let init () =
    Hashtbl.clear own_code;
    Machine.sequence [ link_program; Primus.System.init >>> create_engine ]
end
