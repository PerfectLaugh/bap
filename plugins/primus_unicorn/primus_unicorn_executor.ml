(* Runs the subroutines of the binary program in Unicorn.

   The machine state stays in Primus, Unicorn borrows it while it runs:

   - the registers are written to Unicorn before it starts, the changed
     ones are read back when it stops, and the ones that Primus writes
     meanwhile are written to Unicorn before it continues;

   - the memory pages are copied from Primus when Unicorn faults on
     them, the changed bytes of the writable pages are copied back when
     Unicorn stops, and the bytes that Primus stores meanwhile are
     copied to Unicorn;

   - the code that Primus links instead of the program, e.g., the Lisp
     stubs, stops Unicorn at its address and is called by the Primus
     linker, after which Unicorn continues from the return address.

   A run ends when the subroutine returns, i.e., when the code reaches
   its return address with the stack pointer of the caller.

   A checkpoint of the machine is saved when Unicorn reaches its address
   for the first time, and a machine that restores it continues from
   there, instead of the first subroutine that it runs, e.g., the entry
   point, see [Primus_unicorn_checkpoint]. *)

open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
module Uc = Bap_unicorn
module Target = Primus_unicorn_target
module Checkpoint = Primus_unicorn_checkpoint
include Bap_main.Loggers ()

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
  | Interrupt of int  (** an interrupt or a system call *)
  | Invalid
  | Checkpoint

(* a pending return of a run *)
type frame = { ret : int64; sp : int64 }

(* the copied page, with the contents of a writable page that Primus
   has, and the ranges of the bytes that Primus did not have, which it
   may allocate later, so the page is dropped, if it does *)
type page = { snapshot : Bytes.t option; holes : (int * int) list }

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
      (** the pending returns of the machine that runs, see [frames] *)
  returns : unit Int64.Table.t;
      (** the addresses of the hooks of the returns, which stay, as the
          addresses are few *)
  synced : word String.Table.t;
      (** the values of the registers that Primus and Unicorn agree on *)
  mutable unchecked : (int64 * (int * int) list) list;
      (** the pages with holes, which Primus may have allocated *)
  mutable written : var list;
      (** the registers that Primus has written since Unicorn stopped *)
  mutable broken : bool;
      (** Unicorn 2.1.4 crashes on MIPS after a fetch fault, so the engine is
          created anew *)
}

(* the seconds of the emulation that a machine may run, as the limit
   component counts only the code that Primus interprets *)
let timeout : float option ref = ref None

let elapsed =
  Primus.Machine.State.declare ~uuid:"ccde44e4-b82f-4627-80ff-8f5ea918e960"
    ~name:"unicorn-elapsed" (fun _ -> 0.)

(* the pending returns of the runs of a machine, the innermost first,
   which are of the machine, as the machines may switch, while a stub
   runs, and stay when a machine raises an exception, which it doesn't
   survive, as the Primus exceptions are not handled *)
let frames =
  Primus.Machine.State.declare ~uuid:"d47083aa-ead6-439d-8a0c-6bc2bbcc9d6e"
    ~name:"unicorn-frames" (fun _ -> [])

(* the file of the checkpoint and the address or the name of the
   subroutine, at which it is saved *)
let checkpoint : (string * string) option ref = ref None

(* the address of the checkpoint, and whether it was saved, as it is
   saved once *)
let checkpoint_addr : int64 option ref = ref None
let checkpointed = ref false

(* the checkpoint is not saved at the address, from which the machine
   continues, as it was saved there, until its instruction runs, which
   it does, unless it faults, after Unicorn has skipped the checkpoint *)
let resumed_at : int64 option ref = ref None
let skipped = ref false

(* the file of the checkpoint, from which the machines continue *)
let restore : string option ref = ref None
let restored_from : Checkpoint.t option ref = ref None

(* a machine restores the checkpoint once, and its forks don't *)
let restored =
  Primus.Machine.State.declare ~uuid:"8c3f7a52-1d4e-4b9a-9f0e-6a2d5c7b8e41"
    ~name:"unicorn-restored" (fun _ -> false)

(* the engine of the machines *)
let active : engine option ref = ref None

(* the arguments of [create] *)
let recipe : (Theory.Target.t * int64 list * (int64 * string) list) option ref =
  ref None

(* the code that runs the subroutines in Unicorn, see [Loader] *)
let own_code : Primus.Linker.code Addr.Table.t = Addr.Table.create ()

(* the stubs of the external functions, e.g., in PLT, which jump through
   their slots to the trampolines, interpreted, see [call_foreign] *)
let stubs : Primus.Linker.code Addr.Table.t = Addr.Table.create ()

(* The instructions, e.g., the system calls, which the lifters represent
   as the calls to the intrinsic functions, e.g., intrinsic:syscall, with
   the inputs in the variables intrinsic:x0, intrinsic:x1, etc., are run
   by the Primus linker, as the interpreter does, when they stop Unicorn
   with an interrupt, at the address of their next instruction. *)
type intrinsic = { name : string; inputs : (var * exp) list }

let intrinsics : intrinsic Int64.Map.t ref = ref Int64.Map.empty

let index_intrinsics prog =
  let callee jmp =
    match Jmp.kind jmp with
    | Call call -> (
        match Call.target call with
        | Direct tid ->
            let name =
              match Term.find sub_t prog tid with
              | Some sub -> Sub.name sub
              | None -> String.chop_prefix_if_exists (Tid.name tid) ~prefix:"@"
            in
            Option.some_if (String.is_prefix name ~prefix:"intrinsic:") name
        | Indirect _ -> None)
    | Goto _ | Ret _ | Int _ -> None
  in
  intrinsics :=
    Term.enum sub_t prog
    |> Seq.concat_map ~f:(Term.enum blk_t)
    |> Seq.fold ~init:Int64.Map.empty ~f:(fun sites blk ->
        Term.enum jmp_t blk
        |> Seq.fold ~init:sites ~f:(fun sites jmp ->
            match (callee jmp, Term.get_attr jmp address) with
            | Some name, Some addr ->
                let inputs =
                  Term.enum def_t blk
                  |> Seq.filter ~f:(fun def ->
                      String.is_prefix
                        (Var.name (Def.lhs def))
                        ~prefix:"intrinsic:"
                      && Option.equal Addr.equal
                           (Term.get_attr def address)
                           (Some addr))
                  |> Seq.map ~f:(fun def -> (Def.lhs def, Def.rhs def))
                  |> Seq.to_list
                in
                Map.set sites
                  ~key:(Bitvec.to_int64 (Word.to_bitvec addr))
                  ~data:{ name; inputs }
            | _ -> sites))

(* the intrinsic, whose instruction precedes [pc] *)
let intrinsic_before pc =
  match Map.closest_key !intrinsics `Less_than pc with
  | Some (addr, site) when Int64.(pc - addr <= 16L) -> Some site
  | _ -> None

(* the subroutines in the Thumb encoding, which Unicorn runs from their
   addresses with the lower bit set *)
let thumb : Addr.Hash_set.t = Addr.Hash_set.create ()

(* the names of the Thumb instructions of LLVM start with t, e.g., tMOVi8
   or t2STRDi8, unlike the names of the ARM instructions *)
let is_thumb sub =
  match Term.first blk_t sub with
  | None -> false
  | Some blk -> (
      let insn =
        match Term.first def_t blk with
        | Some def -> Term.get_attr def Disasm.insn
        | None ->
            Option.bind (Term.first jmp_t blk) ~f:(fun jmp ->
                Term.get_attr jmp Disasm.insn)
      in
      match insn with
      | Some insn -> String.is_prefix (Insn.name insn) ~prefix:"t"
      | None -> false)

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

(* the instruction that does nothing, which fills the trampolines, since
   Unicorn raises an interrupt, before it calls the hooks of the address,
   if the instruction is invalid, as the zeros are on RISC-V *)
let nop (arch : Uc.arch) ~big_endian =
  let word ~big x =
    String.init 4 ~f:(fun i ->
        let i = if big then 3 - i else i in
        Char.of_int_exn ((x lsr (8 * i)) land 0xFF))
  in
  match arch with
  | X86 -> "\x90"
  (* andeq r0, r0, r0 and sll $0, $0, 0 *)
  | Arm | Mips -> "\000\000\000\000"
  | Arm64 -> word ~big:false 0xD503201F
  | Ppc -> word ~big:big_endian 0x60000000
  | Riscv -> word ~big:false 0x13

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
      returns = Int64.Table.create ();
      synced = String.Table.create ();
      written = [];
      unchecked = [];
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
    let nop = nop arch ~big_endian:e.big_endian in
    Uc.mem_write uc base
      (String.concat
         (List.init
            (Int64.to_int_exn size / String.length nop)
            ~f:(fun _ -> nop)));
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
  (* the first hook of an address that stops Unicorn is the last one
     called, so the checkpoint goes before the foreign code, which runs
     after it is saved *)
  Option.iter !checkpoint_addr ~f:(fun addr ->
      ignore
      @@ Uc.on_code uc ~first:addr ~last:addr (fun _ _ ->
          match !resumed_at with
          | Some at when Int64.(at = addr) ->
              resumed_at := None;
              skipped := true
          | _ -> if not !checkpointed then stop Checkpoint));
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
  (match arch with
  | X86 -> ignore @@ Uc.on_x86_syscall uc (fun () -> stop (Interrupt (-1)))
  | _ -> ());
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
  module Interpreter = Primus.Interpreter.Make (Machine)

  let fail fmt = ksprintf (fun msg -> Machine.raise (Unicorn_failure msg)) fmt
  let word e x = Word.of_int64 ~width:(e.bytes * 8) x

  let owns e =
    let+ id = Machine.current () in
    match e.owner with
    | Some owner -> Monads.Std.Monad.State.Multi.Id.equal owner id
    | None -> false

  (* drops the pages, which are copied anew *)
  let forget e =
    Hashtbl.iter_keys e.pages ~f:(fun page -> Uc.mem_unmap e.uc page page_size);
    Hashtbl.clear e.pages;
    e.unchecked <- [];
    e.written <- []

  (* the pages and the registers of another machine are not valid *)
  let claim e =
    let* owned = owns e in
    if owned then Machine.return false
    else
      let+ id = Machine.current () in
      forget e;
      e.owner <- Some id;
      true

  (* the byte and its protection, if it is mapped, a byte that is not
     readable is zero *)
  let load_byte addr =
    Memory.protection addr >>= function
    | None -> Machine.return None
    | Some (p : Primus.Memory.protection) when not p.readable ->
        Machine.return (Some ('\000', p))
    | Some p ->
        let+ x = Memory.load addr in
        Some (Char.of_int_exn (Word.to_int_exn x), p)

  let union (p : Primus.Memory.protection) (q : Primus.Memory.protection) :
      Primus.Memory.protection =
    {
      readable = p.readable || q.readable;
      writable = p.writable || q.writable;
      executable = p.executable || q.executable;
    }

  (* the page has the access of all its bytes, as Unicorn protects the
     whole pages *)
  let map_page e page =
    let base = word e page in
    let bytes = Bytes.make (Int64.to_int_exn page_size) '\000' in
    let none : Primus.Memory.protection =
      { readable = false; writable = false; executable = false }
    in
    let* holes, access =
      Machine.List.fold
        (List.init (Bytes.length bytes) ~f:Fn.id)
        ~init:([], none)
        ~f:(fun (holes, access) i ->
          load_byte Word.(base ++ i) >>| function
          | Some (c, p) ->
              Bytes.set bytes i c;
              (holes, union access p)
          | None -> (
              match holes with
              | (first, last) :: holes when last + 1 = i ->
                  ((first, i) :: holes, access)
              | holes -> ((i, i) :: holes, access)))
    in
    let writable = access.writable in
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
    let perm =
      Uc.Perm.(
        (if access.readable then read else none)
        + (if writable then write else none)
        + if access.executable then exec else none)
    in
    Uc.mem_map e.uc page page_size perm;
    Uc.mem_write e.uc page data;
    Hashtbl.set e.pages ~key:page
      ~data:
        {
          snapshot = (if writable then Some (Bytes.of_string data) else None);
          holes;
        };
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

  (* copies the registers that changed in Unicorn to Primus *)
  let pull_regs e =
    Machine.List.iter e.basis ~f:(fun v ->
        match Target.Regs.read e.regs v with
        | Some x
          when not
                 (Option.equal Word.equal
                    (Hashtbl.find e.synced (Var.name v))
                    (Some x)) ->
            Hashtbl.set e.synced ~key:(Var.name v) ~data:x;
            Value.of_word x >>= Env.set v
        | _ -> Machine.return ())

  (* copies the registers from Primus, the aliases go first, so that
     the registers of the program win, and then the registers, which the
     aliases changed, go back to Primus *)
  let push_vars e vars =
    let vars = List.filter vars ~f:(Target.Regs.mem e.regs) in
    let is_basis v = List.mem e.basis v ~equal:Var.equal in
    let aliases, basis = List.partition_tf vars ~f:(Fn.non is_basis) in
    let* () =
      Machine.List.iter (aliases @ basis) ~f:(fun v ->
          let+ x = Env.get v in
          ignore (Target.Regs.write e.regs v (Primus.Value.to_word x)))
    in
    e.written <- [];
    pull_regs e

  (* copies all registers from Primus *)
  let push e =
    Hashtbl.clear e.synced;
    let* vars = Env.all in
    push_vars e (Seq.to_list vars)

  (* copies the registers that Primus has written *)
  let push_written e = push_vars e (List.rev e.written)

  (* the registers that Primus has written go to Unicorn, unless another
     machine has run in it, as then all registers go there, see [loop] *)
  let push_owned e =
    let* owned = owns e in
    if owned then push_written e else Machine.return ()

  let written (v, _) =
    (match !active with
    | Some e when Target.Regs.mem e.regs v -> e.written <- v :: e.written
    | _ -> ());
    Machine.return ()

  let store_page e page snapshot =
    let data = Uc.mem_read e.uc page (Int64.to_int_exn page_size) in
    if String.equal data (Bytes.unsafe_to_string snapshot) then
      Machine.return ()
    else
      let base = word e page in
      let changed =
        List.filter
          (List.init (String.length data) ~f:Fn.id)
          ~f:(fun i -> not (Char.equal data.[i] (Bytes.get snapshot i)))
      in
      Machine.List.iter changed ~f:(fun i ->
          Bytes.set snapshot i data.[i];
          Memory.store_never_fail
            Word.(base ++ i)
            (Word.of_int ~width:8 (Char.to_int data.[i])))

  (* copies the registers and the changed memory to Primus and drops
     the writable pages, that Primus may extend, see [page] *)
  let pull e =
    let* () = pull_regs e in
    let writable =
      Hashtbl.fold e.pages ~init:[] ~f:(fun ~key ~data acc ->
          match data.snapshot with
          | Some snapshot -> (key, snapshot, data.holes) :: acc
          | None -> acc)
    in
    let* () =
      Machine.List.iter writable ~f:(fun (page, snapshot, _) ->
          store_page e page snapshot)
    in
    (* a page, which Primus may change, is checked before Unicorn runs *)
    e.unchecked <-
      List.filter_map writable ~f:(fun (page, _, holes) ->
          if List.is_empty holes then None else Some (page, holes))
      @ e.unchecked;
    Machine.return ()

  (* drops the pages, in which Primus has allocated memory, see [page] *)
  let check_pages e =
    let pages = e.unchecked in
    e.unchecked <- [];
    Machine.List.iter pages ~f:(fun (page, holes) ->
        let* allocated =
          Machine.List.exists holes ~f:(fun (first, last) ->
              let* first =
                Memory.is_mapped (word e Int64.(page + of_int first))
              in
              let+ last =
                Memory.is_mapped (word e Int64.(page + of_int last))
              in
              first || last)
        in
        if allocated && Hashtbl.mem e.pages page then (
          Uc.mem_unmap e.uc page page_size;
          Hashtbl.remove e.pages page);
        Machine.return ())

  (* the pages, whose protection changes, are copied anew *)
  let protected (lower, upper, _) =
    match !active with
    | None -> Machine.return ()
    | Some e ->
        let+ id = Machine.current () in
        let owned =
          match e.owner with
          | Some owner -> Monads.Std.Monad.State.Multi.Id.equal owner id
          | None -> false
        in
        if owned then
          let first = page_of (int64_of_word lower)
          and last = page_of (int64_of_word upper) in
          Hashtbl.filter_keys_inplace e.pages ~f:(fun page ->
              let inside =
                Int64.(page >= first && page <= last)
                || Int64.(first > last && (page >= first || page <= last))
              in
              if inside then Uc.mem_unmap e.uc page page_size;
              not inside)

  (* the bytes that Primus stores go to the copied pages *)
  let stored (addr, x) =
    match !active with
    | None -> Machine.return ()
    | Some e -> (
        let+ id = Machine.current () in
        let owned =
          match e.owner with
          | Some owner -> Monads.Std.Monad.State.Multi.Id.equal owner id
          | None -> false
        in
        let addr = int64_of_word (Primus.Value.to_word addr) in
        match Hashtbl.find e.pages (page_of addr) with
        | Some { snapshot = Some snapshot; _ } when owned ->
            let c =
              Char.of_int_exn (Word.to_int_exn (Primus.Value.to_word x))
            in
            Bytes.set snapshot Int64.(to_int_exn (addr - page_of addr)) c;
            Uc.mem_write e.uc addr (String.of_char c)
        | _ -> ())

  (* the engine, which is created anew, if it is broken, after its state
     goes to Primus *)
  let engine () =
    match (!active, !recipe) with
    | Some e, Some (target, foreign, externals) when e.broken ->
        let* owned = owns e in
        let* () = if owned then pull e else Machine.return () in
        Uc.close e.uc;
        let e = create target ~foreign ~externals in
        active := Some e;
        Machine.return e
    | Some e, _ -> Machine.return e
    | None, _ -> fail "the engine is not initialized"

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

  let drop_page e page =
    if Hashtbl.mem e.pages page then (
      Uc.mem_unmap e.uc page page_size;
      Hashtbl.remove e.pages page)

  (* repeats the access, that Unicorn denied, in Primus, which signals
     the pagefault trap, as the interpreter does, and raises the
     segmentation fault, unless the pagefault handler fixes the access,
     after which the page is copied anew *)
  let repeat e access addr =
    let a = word e addr in
    let* () = pull e in
    let* v = Value.of_word a in
    let* () =
      match (access : Uc.access) with
      | Write_unmapped | Write_prot ->
          let* x =
            Memory.protection a >>= function
            | Some p when p.readable -> Memory.get a
            | _ -> Value.zero 8
          in
          Interpreter.store v x LittleEndian `r8
      | Fetch_unmapped | Fetch_prot ->
          (* Primus doesn't fetch the code, so it checks only the access *)
          let* _ = Interpreter.load v LittleEndian `r8 in
          let* executable = Memory.is_executable a in
          if executable then Machine.return ()
          else Machine.raise (Primus.Interpreter.Segmentation_fault a)
      | _ -> Interpreter.load v LittleEndian `r8 >>| ignore
    in
    drop_page e (page_of addr);
    Machine.return `Continue

  let fault e access addr =
    match (access : Uc.access) with
    | Read_unmapped | Write_unmapped | Fetch_unmapped ->
        let* mapped = Memory.is_mapped (word e addr) in
        if mapped then map_page e (page_of addr) >>| fun () -> `Continue
        else repeat e access addr
    | Read_prot | Write_prot | Fetch_prot -> repeat e access addr
    | Read | Write | Fetch | Read_after ->
        pull e >>= fun () -> fail "access to %Lx is denied" addr

  (* the interpreted stub, if the function is linked to the stub of the
     program, which nothing replaced *)
  let unreplaced_stub name =
    let* code = Linker.lookup name in
    let+ addr = Linker.resolve_addr name in
    match (code, addr) with
    | Some code, Some addr -> (
        match (Hashtbl.find own_code addr, Hashtbl.find stubs addr) with
        | Some own, Some stub when phys_equal own code -> Some stub
        | _ -> None)
    | _ -> None

  (* the stub of the program, which runs in Unicorn, would jump back to
     the trampoline, so it is interpreted, as load-binary does, which
     calls the function, that nothing defines, by its address *)
  let call_foreign e addr =
    let* () = pull e in
    let* frame = frame e in
    let name =
      match Hashtbl.find e.trampolines addr with
      | Some name -> `symbol name
      | None -> `addr (word e addr)
    in
    let* () =
      unreplaced_stub name >>= function
      | Some (module Stub : Primus.Linker.Code) ->
          let module Stub = Stub (Machine) in
          Stub.exec
      | None -> Linker.exec name
    in
    let* () = push_owned e in
    (* the return address is popped on x86, if the stub did not *)
    if Option.is_none e.link then
      ignore (Target.Regs.write e.regs e.sp (word e frame.sp));
    Machine.return frame.ret

  (* the address, from which Unicorn continues, with the lower bit set in
     the Thumb state of ARM *)
  let current_pc e =
    let pc = Uc.reg_read e.uc e.pc in
    match e.arch with
    | Arm ->
        let cpsr = Option.value_exn (Uc.reg Arm "CPSR") in
        if Int64.(Uc.reg_read e.uc cpsr land 0x20L <> 0L) then Int64.(pc lor 1L)
        else pc
    | _ -> pc

  (* the address of the instruction at [pc] *)
  let code_addr e pc =
    match e.arch with Arm -> Int64.(pc land lnot 1L) | _ -> pc

  let call_intrinsic e { name; inputs } =
    let* () = pull e in
    let* () =
      Machine.List.iter inputs ~f:(fun (var, exp) ->
          Interpreter.exp exp >>= Interpreter.set var)
    in
    let* () = Linker.exec (`symbol name) in
    push_owned e

  (* saves the state of the machine, which is in Primus, after it is
     copied from Unicorn, and the innermost run, from which Unicorn
     continues *)
  let save e pc =
    let* () = pull e in
    let* target = Machine.gets Project.target in
    let* vars = Env.all in
    let* vars =
      Seq.to_list vars
      |> List.dedup_and_sort ~compare:Var.compare
      |> Machine.List.filter ~f:Env.is_set
    in
    let* vars =
      Machine.List.map vars ~f:(fun v ->
          let+ x = Env.get v in
          (v, Primus.Value.to_word x))
    in
    let* memory = Memory.snapshot in
    checkpointed := true;
    let file, _ = Option.value_exn !checkpoint in
    let { ret; sp } = List.hd_exn e.frames in
    match
      Checkpoint.save file
        { target = Theory.Target.to_string target; pc; ret; sp; vars; memory }
    with
    | Ok () ->
        info "saved the checkpoint at %Lx to %s" pc file;
        Machine.return ()
    | Error msg -> fail "can't save the checkpoint: %s" msg

  let terminate e =
    let* () = pull e in
    let* id = Machine.current () in
    info "terminating machine %a, which has run in Unicorn for %g seconds"
      Monads.Std.Monad.State.Multi.Id.pp id
      (Option.value_exn !timeout);
    Interpreter.halt >>= never_returns

  (* stops Unicorn at the return address of the innermost run *)
  let ensure_return e ret =
    if not (Hashtbl.mem e.returns ret) then (
      Hashtbl.set e.returns ~key:ret ~data:();
      ignore
      @@ Uc.on_code e.uc ~first:ret ~last:ret (fun _ _ ->
          match e.frames with
          | top :: _ when Int64.(top.ret = ret) -> (
              match Target.Regs.read e.regs e.sp with
              | Some sp when Int64.(int64_of_word sp = top.sp) ->
                  e.reason <- Some Returned;
                  Uc.stop e.uc
              | _ -> ())
          | _ -> ()))

  (* the engine may be created anew, see [broken], and another machine
     may have run in it, see [claim] *)
  let prepare () =
    let* e = engine () in
    let* claimed = claim e in
    let* () =
      if claimed then map_code e >>= fun () -> push e else Machine.return ()
    in
    let+ pending = Machine.Local.get frames in
    e.frames <- pending;
    (match pending with top :: _ -> ensure_return e top.ret | [] -> ());
    e

  let rec loop pc =
    let* e = prepare () in
    check_pages e >>= fun () ->
    ensure_page e pc >>= fun () ->
    let* used = Machine.Local.get elapsed in
    let remaining = Option.map !timeout ~f:(fun t -> t -. used) in
    match remaining with
    | Some t when Float.(t <= 0.) -> terminate e
    | _ -> (
        e.reason <- None;
        skipped := false;
        let started = Stdlib.Sys.time () in
        let error =
          try
            Uc.start e.uc pc
              ?timeout:
                (Option.map remaining ~f:(fun t ->
                     Int.max 1 (Float.iround_up_exn (t *. 1e6))));
            None
          with Uc.Error (_, msg) -> Some msg
        in
        let* () =
          Machine.Local.put elapsed (used +. Stdlib.Sys.time () -. started)
        in
        let pc = current_pc e in
        (match e.reason with
        | Some (Fault _)
          when !skipped
               && Option.equal Int64.equal !checkpoint_addr
                    (Some (code_addr e pc)) ->
            resumed_at := !checkpoint_addr
        | _ -> ());
        match (e.reason, error) with
        | None, None when Option.is_some remaining -> loop pc
        | Some Returned, _ | None, None -> pull e
        | Some (Foreign addr), _ -> call_foreign e addr >>= loop
        | Some (Fault (access, addr)), _ -> (
            fault e access addr >>= function `Continue -> loop pc)
        | Some (Interrupt n), _ -> (
            match intrinsic_before (code_addr e pc) with
            | Some site -> call_intrinsic e site >>= fun () -> loop pc
            | None ->
                pull e >>= fun () ->
                fail "an unhandled interrupt %d at %Lx" n pc)
        | Some Checkpoint, _ -> save e pc >>= fun () -> loop pc
        | Some Invalid, _ ->
            pull e >>= fun () -> fail "an invalid instruction at %Lx" pc
        | None, Some msg -> pull e >>= fun () -> fail "%s at %Lx" msg pc)

  let start e addr =
    let pc = int64_of_word addr in
    match e.arch with
    | Arm when Hash_set.mem thumb addr -> Int64.(pc lor 1L)
    | _ -> pc

  (* the run continues from the checkpoint, and ends when it returns,
     see [Checkpoint] *)
  let resume (cp : Checkpoint.t) =
    let* () = Machine.Local.put restored true in
    let* () = Memory.restore cp.memory in
    let* () =
      Machine.List.iter cp.vars ~f:(fun (v, x) -> Value.of_word x >>= Env.set v)
    in
    let* e = engine () in
    let* id = Machine.current () in
    forget e;
    e.owner <- Some id;
    let* () = map_code e in
    let* () = push e in
    if Option.equal Int64.equal !checkpoint_addr (Some (code_addr e cp.pc)) then
      resumed_at := !checkpoint_addr;
    info "continues from the checkpoint at %Lx" cp.pc;
    let* pending = Machine.Local.get frames in
    let* () =
      Machine.Local.put frames ({ ret = cp.ret; sp = cp.sp } :: pending)
    in
    let* () = loop cp.pc in
    Machine.Local.put frames pending

  let run addr =
    let* restored = Machine.Local.get restored in
    match !restored_from with
    | Some cp when not restored -> resume cp
    | _ ->
        let* e = engine () in
        let* claimed = claim e in
        let* () = if claimed then map_code e else Machine.return () in
        let* () = push e in
        let* frame = frame e in
        let* pending = Machine.Local.get frames in
        let* () =
          Machine.Local.put frames
            ({ frame with ret = address e frame } :: pending)
        in
        let* () = loop (start e addr) in
        Machine.Local.put frames pending
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
          if Term.has_attr sub Sub.stub then begin
            let module Stub (Machine : Primus.Machine.S) = struct
              module Interp = Primus.Interpreter.Make (Machine)

              let exec = Interp.sub sub
            end in
            Hashtbl.set stubs ~key:addr ~data:(module Stub)
          end;
          if is_thumb sub then Hash_set.add thumb addr;
          Linker.link ~addr ~name:(Sub.name sub) ~tid:(Term.tid sub) code

  let link_program =
    let* prog = Machine.gets Project.program in
    index_intrinsics prog;
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
        (* some loaders refer to the code, e.g., to the PLT entries, which
           are not the slots *)
        let width = Theory.Target.code_addr_size (Project.target proj) in
        let is_code addr =
          Memmap.lookup (Project.memory proj) (Word.of_int64 ~width addr)
          |> Seq.exists ~f:(fun (_, tag) ->
              match Bap.Std.Value.get Image.segment tag with
              | Some seg -> Image.Segment.is_executable seg
              | None -> false)
        in
        Machine.return @@ Seq.to_list
        @@ Seq.filter refs ~f:(fun (addr, name) ->
            Set.mem functions name && not (is_code addr))

  (* the address, or the name of the subroutine, as its address *)
  let resolve point =
    match Int64.of_string point with
    | addr -> Machine.return addr
    | exception _ -> (
        let* prog = Machine.gets Project.program in
        let sub =
          Term.enum sub_t prog
          |> Seq.find ~f:(fun sub -> String.equal (Sub.name sub) point)
        in
        match Option.bind sub ~f:(fun sub -> Term.get_attr sub address) with
        | Some addr -> Machine.return (int64_of_word addr)
        | None ->
            Machine.raise
              (Unicorn_failure
                 (sprintf "the checkpoint is at %s, which is not found" point)))

  let load_checkpoint target =
    match !restore with
    | None -> Machine.return None
    | Some file -> (
        match Checkpoint.load file with
        | Error msg -> Machine.raise (Unicorn_failure msg)
        | Ok cp when String.equal cp.target (Theory.Target.to_string target) ->
            Machine.return (Some cp)
        | Ok cp ->
            Machine.raise
              (Unicorn_failure
                 (sprintf "the checkpoint %s is of the target %s" file cp.target))
        )

  (* the subroutines, whose code the other components replaced, stop
     Unicorn *)
  let create_engine () =
    let* target = Machine.gets Project.target in
    let* () =
      match !checkpoint with
      | None -> Machine.return ()
      | Some (_, point) ->
          let+ addr = resolve point in
          checkpoint_addr := Some addr
    in
    let* cp = load_checkpoint target in
    restored_from := cp;
    let* foreign =
      Hashtbl.keys own_code
      |> Machine.List.filter_map ~f:(fun addr ->
          Linker.lookup (`addr addr) >>| function
          | Some code when phys_equal code (Hashtbl.find_exn own_code addr) ->
              None
          | _ -> Some (int64_of_word addr))
    in
    (match !active with Some e -> Uc.close e.uc | None -> ());
    active := None;
    let* externals = externals () in
    recipe := Some (target, foreign, externals);
    match create target ~foreign ~externals with
    | exception Unsupported msg -> Machine.raise (Unicorn_failure msg)
    | e ->
        active := Some e;
        Machine.return ()

  let init () =
    Hashtbl.clear own_code;
    Hashtbl.clear stubs;
    Hash_set.clear thumb;
    checkpoint_addr := None;
    checkpointed := false;
    resumed_at := None;
    let module Exec = Make (Machine) in
    Machine.sequence
      [
        link_program;
        Primus.System.init >>> create_engine;
        Primus.Interpreter.stored >>> Exec.stored;
        Primus.Interpreter.written >>> Exec.written;
        Primus.Memory.protected >>> Exec.protected;
      ]
end
