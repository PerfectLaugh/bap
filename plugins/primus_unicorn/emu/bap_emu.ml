open Core
open Bap_knowledge
open Bap.Std
open Bap_primus.Std
module X = Bap_primus_unicorn_plugin.Primus_unicorn_executor
module Native = Bap_primus_unicorn_plugin.Primus_unicorn_native
module Target = Bap_primus_unicorn_plugin.Primus_unicorn_target
module Uc = Bap_unicorn
module Io = Primus_lisp_library_plugin.Primus_lisp_io

type status = Paused | Running | Exited of int option | Failed of string
type action = Default | Return of int64

(* the system, which runs in the fiber of the script, either paused,
   with the address, from which it continues, or finished *)
type state =
  | Suspended of
      int64 * Primus.Machine.id * (X.request, state) Effect.Deep.continuation
  | Finished of
      ( Primus.exit_status * project * Knowledge.state,
        Knowledge.conflict )
      result
  | Crashed of exn
  | Ended of Primus.exit_status * (X.request, state) Effect.Deep.continuation
  | Running  (** the program runs, e.g., in a hook *)

(* the emulator, whose system has its own session, i.e., its own engine
   and the state of the executor, so that the emulators run side by side *)
type t = {
  session : X.session;
  mutable state : state;
  mutable call : string option;
  target : Bap_core_theory.Theory.Target.t;
  project : project;
  mutable hooked : Knowledge.state option;
      (** the knowledge, in which [bir] lifts the instructions in the hooks,
          outside of the machine, which runs *)
  lifted : (int64 * string * bool, (int * blk term list) option) Hashtbl.t;
      (** the instructions, that [bir] lifted in the hooks *)
  hooked_calls : Int64.Hash_set.t;
      (** the addresses, whose calls the script hooks, see [on_call] *)
}

let engine t =
  match t.session.active with
  | Some e -> e
  | None -> invalid_arg "Bap_emu: the engine is not running"

let fiber f =
  Effect.Deep.match_with f ()
    {
      retc = (fun result -> Finished result);
      exnc = (fun exn -> Crashed exn);
      effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | X.Paused (pc, id) ->
              Some
                (fun (k : (a, state) Effect.Deep.continuation) ->
                  Suspended (pc, id, k))
          | X.Ended status ->
              Some
                (fun (k : (a, state) Effect.Deep.continuation) ->
                  Ended (status, k))
          | _ -> None);
    }

(* the knowledge of the finished system is of the emulator, see
   [knowledge], e.g., of the instructions, that it lifted, see
   [Primus.Lift], and doesn't replace the toplevel one, as each emulator
   has its own *)
let finish t state =
  t.state <- state;
  match state with
  | Suspended _ | Ended _ | Running -> ()
  | Finished _ | Crashed _ -> t.session.driven <- false

(* continues the paused system with the request *)
let resume t request =
  match t.state with
  | Suspended (_, _, k) | Ended (_, k) ->
      (* the hooks see, that the program runs, and its continuation is
         not resumed again *)
      t.state <- Running;
      finish t (Effect.Deep.continue k request)
  | _ -> invalid_arg "Bap_emu: the program is not paused"

let status t =
  match t.state with
  | Suspended _ -> Paused
  | Running -> Running
  | Ended ((Primus.Normal | Exn Primus.Interpreter.Halt), _) ->
      Exited t.session.exit_code
  | Ended (Exn exn, _) -> Failed (Primus.Exn.to_string exn)
  | Finished (Ok ((Primus.Normal | Exn Primus.Interpreter.Halt), _, _)) ->
      Exited t.session.exit_code
  | Finished (Ok (Exn exn, _, _)) -> Failed (Primus.Exn.to_string exn)
  | Finished (Error conflict) ->
      Failed (Format.asprintf "%a" Knowledge.Conflict.pp conflict)
  | Crashed exn -> Failed (Exn.to_string exn)

let paused t = match t.state with Suspended _ -> true | _ -> false

(* the program runs from the entry, and, when it ends, the script may
   restore a snapshot, after which the machine, that ended, is killed,
   and the snapshot continues, which ends here too *)
let start init (entry : Primus.Linker.name) =
  let module Machine = Primus.Analysis in
  let module Linker = Primus.Linker.Make (Machine) in
  let open Machine.Syntax in
  Machine.List.iter init ~f:(fun component ->
      let module Component = (val component : Primus.Machine.Component) in
      let module Component = Component (Machine) in
      Component.init ())
  >>= fun () ->
  Machine.catch
    (Linker.exec entry >>| fun () -> Primus.Normal)
    (fun exn -> Machine.return (Primus.Exn exn))
  >>= fun status ->
  let rec ended () =
    match Effect.perform (X.Ended status) with
    | X.Restore snapshot ->
        Machine.current () >>= fun id ->
        Machine.kill id >>= fun () -> Machine.switch snapshot
    | X.Run component ->
        let module Component = (val component : Primus.Machine.Component) in
        let module Component = Component (Machine) in
        Component.init () >>= ended
    | X.Continue _ | X.Map _ | X.Snapshot | X.Store _ | X.Save _ ->
        Machine.return ()
  in
  ended ()

(* the components of [init], and the redirections run
   in the machine, after the components of the system, before the
   program starts, and the program continues from the checkpoint
   [restore], with its names, which the executor loads, when it starts.
   The system gets the session of the emulator with its project, see
   [X.with_session] *)
let create ?(system = "bap:unicorn-executor") ?(components = []) ?(init = [])
    ?(redirects = []) ?(args = []) ?(envp = []) ?entry ?restore proj =
  let init =
    init @ if List.is_empty redirects then [] else [ Io.redirect redirects ]
  in
  (* the entry point of the program, as the run pass finds it *)
  let entry =
    match entry with
    | Some name -> `symbol name
    | None -> (
        match
          Term.enum sub_t (Project.program proj)
          |> Seq.find ~f:(fun sub -> Term.has_attr sub Sub.entry_point)
        with
        | Some sub -> `tid (Term.tid sub)
        | None -> `symbol "_start")
  in
  let system =
    match Primus.System.Repository.find (Knowledge.Name.read system) with
    | Some sys -> sys
    | None -> invalid_argf "Bap_emu: unknown system %s" system ()
  in
  let system =
    List.fold components ~init:system ~f:(fun sys comp ->
        let name = Knowledge.Name.read comp in
        Primus.System.add_component sys
          ~package:(Knowledge.Name.package name)
          (Knowledge.Name.unqualified name))
  in
  let program = Option.value (Project.get proj filename) ~default:"a.out" in
  let session =
    X.create_session ?restore:(Option.map restore ~f:Option.return) ()
  in
  session.driven <- true;
  session.pause <- true;
  let t =
    {
      session;
      state = Crashed (Failure "not started");
      call = None;
      target = Project.target proj;
      project = proj;
      hooked = None;
      lifted = Hashtbl.Poly.create ();
      hooked_calls = Int64.Hash_set.create ();
    }
  in
  finish t
    (fiber (fun () ->
         Primus.System.run system
           (X.with_session proj session)
           (Toplevel.current ())
           ~args:(Array.of_list (program :: args))
           ~envp:(Array.of_list envp) ~start:(start init entry)));
  t

let pc t =
  match t.state with
  | Suspended (pc, _, _) -> pc
  | _ -> invalid_arg "Bap_emu: the program is not paused"

let set_pc t addr =
  match t.state with
  | Suspended (_, id, k) -> t.state <- Suspended (addr, id, k)
  | _ -> invalid_arg "Bap_emu: the program is not paused"

(* the machine, which is of the system of the emulator, as the systems
   number their machines alike *)
type snapshot = { owner : X.session; id : Primus.Machine.id }

let machine t =
  match t.state with
  | Suspended (_, id, _) -> id
  | _ -> invalid_arg "Bap_emu: the program is not paused"

(* the machine, that takes the snapshot, forks, and stays paused, as the
   snapshot, and its fork continues *)
let snapshot t =
  let id = machine t in
  resume t X.Snapshot;
  { owner = t.session; id }

let restore t { owner; id } =
  if not (phys_equal owner t.session) then
    invalid_arg "Bap_emu.restore: the snapshot is of another emulator";
  t.session.exit_code <- None;
  resume t (X.Restore id)

module type Completion = X.Completion

let complete = X.complete

let save t file =
  if not (paused t) then
    invalid_arg "Bap_emu.save: the program is not paused, e.g., in a hook";
  resume t (X.Save (file, pc t));
  match t.session.saved with Ok () -> () | Error msg -> failwith msg

(* pauses the program before the next instruction, from a hook *)
let stop t =
  let e = engine t in
  t.session.pause <- true;
  e.reason <- Some X.Pause;
  Uc.stop e.uc

(* [fresh addr] unless the hook saw the instruction at [addr] last in
   the previous start of Unicorn, which stopped there, and starts there
   again, e.g., after its fault, or as the hook paused the program, so
   that the hook, that stops it, doesn't stop it again, when it
   continues *)
let instructions t =
  let last = ref None in
  fun addr ->
    let s = t.session in
    let again =
      Option.equal Int64.equal s.restarted_at (Some addr)
      &&
      match !last with
      | Some (addr', start) -> Int64.equal addr addr' && start = s.starts - 1
      | None -> false
    in
    last := Some (addr, s.starts);
    not again

(* the hook goes to the engine of the emulator, and to its new engines,
   see [X.session] *)
let installed t f =
  t.session.engine_hooks <- f :: t.session.engine_hooks;
  Option.iter t.session.active ~f

let run ?until t =
  if paused t then begin
    let e = engine t in
    let hook =
      Option.map until ~f:(fun addr ->
          (* the program, which is paused at the address, runs its
             instruction first *)
          let code =
            match e.arch with Arm -> Int64.(pc t land lnot 1L) | _ -> pc t
          in
          let skip = ref (Int64.equal addr code) in
          let fresh = instructions t in
          ( e,
            Uc.on_code e.uc ~first:addr ~last:addr (fun addr _ ->
                if fresh addr then if !skip then skip := false else stop t) ))
    in
    resume t (X.Continue (pc t));
    Option.iter hook ~f:(fun (e', hook) ->
        match t.session.active with
        | Some e when phys_equal e e' -> Uc.delete e.uc hook
        | _ -> ())
  end;
  status t

let step t =
  if paused t then begin
    let e = engine t in
    let first = ref true in
    let fresh = instructions t in
    let hook =
      Uc.on_code e.uc (fun addr _ ->
          if fresh addr then if !first then first := false else stop t)
    in
    resume t (X.Continue (pc t));
    match t.session.active with
    | Some e' when phys_equal e e' -> Uc.delete e.uc hook
    | _ -> ()
  end;
  status t

let registers t = Target.Regs.names (engine t).regs

let reg t name =
  match Target.Regs.read_name (engine t).regs name with
  | Some x -> Bitvec.to_int64 (Word.to_bitvec x)
  | None -> invalid_argf "Bap_emu: unknown register %s" name ()

let set_reg t name x =
  if not (Target.Regs.write_name (engine t).regs name (Word.of_int64 x)) then
    invalid_argf "Bap_emu: unknown register %s" name ()

(* the pages, which a paused program copies to Unicorn, as Primus has
   them *)
let rec accessible t addr n f =
  match f () with
  | x -> x
  | exception Native.Missing missing when paused t ->
      let page = X.page_of missing in
      resume t (X.Map missing);
      if Hashtbl.mem (engine t).pages page then accessible t addr n f
      else invalid_argf "Bap_emu: %Lx is not mapped" missing ()
  | exception Native.Missing missing ->
      invalid_argf "Bap_emu: the page of %Lx is not in Unicorn yet" missing ()
  | exception Native.Denied ->
      invalid_argf "Bap_emu: the access to %d bytes at %Lx is denied" n addr ()

let read t addr n = accessible t addr n (fun () -> X.uc_read (engine t) addr n)

(* the bytes go only to Unicorn, which translates the code anew, see
   [X.uc_write] *)
let write_direct t addr data =
  let n = String.length data in
  accessible t addr n (fun () ->
      let e = engine t in
      if X.uc_readable e addr n < n then raise Native.Denied;
      X.uc_write e addr data)

(* the bytes go to Primus, from which they go to Unicorn, see
   [X.backing], and the code, that it translated, is translated anew *)
let write t addr data =
  if not (paused t) then
    invalid_arg "Bap_emu.write: the program is not paused, e.g., in a hook";
  (* the bytes are mapped and readable *)
  ignore (read t addr (String.length data) : string);
  resume t (X.Store (addr, data))

(* the component runs in the machine, which is paused, or ended *)
let primus t component =
  match t.state with
  | Suspended _ | Ended _ -> resume t (X.Run component)
  | _ ->
      invalid_arg "Bap_emu.primus: the program is not paused, e.g., in a hook"

(* the instruction in a hook, while the machine runs the program, is
   lifted outside of it, as the script does, in the knowledge, that
   starts from the toplevel one, and keeps the semantics, e.g., the Lisp
   program of x86, which it loads once, and the instructions, which are
   cached by their addresses and bytes *)
let hooked t ?encoding ~thumb addr bytes =
  let key = (addr, bytes, thumb) in
  match Hashtbl.find t.lifted key with
  | Some insn -> insn
  | None ->
      let toplevel = Toplevel.current () in
      let result = ref None in
      Toplevel.set (Option.value t.hooked ~default:toplevel);
      Exn.protect
        ~finally:(fun () ->
          t.hooked <- Some (Toplevel.current ());
          Toplevel.set toplevel)
        ~f:(fun () ->
          Toplevel.exec
            Knowledge.Syntax.(
              Primus.Lift.instruction ?encoding t.project addr bytes
              >>| fun insn -> result := insn));
      Hashtbl.set t.lifted ~key ~data:!result;
      !result

(* the bytes are read before the instruction is lifted in the machine,
   as the reading may copy the pages to Unicorn, and the instruction may
   end on an unmapped page *)
let bir ?thumb t addr =
  let e = engine t in
  let thumb =
    match (e.arch, thumb) with
    | Arm, Some thumb -> thumb
    | Arm, None -> Int64.(addr land 1L = 1L)
    | _ -> false
  in
  let addr = match e.arch with Arm -> Int64.(addr land lnot 1L) | _ -> addr in
  let bytes =
    List.range ~stride:(-1) Primus.Lift.max_size 0
    |> List.find_map ~f:(fun n ->
        try Some (read t addr n) with Invalid_argument _ -> None)
    |> Option.value_exn ~message:(sprintf "Bap_emu.bir: %Lx is not mapped" addr)
  in
  let read a n =
    let off = Int64.(to_int_exn (a - addr)) in
    if off < 0 || off >= String.length bytes then ""
    else String.sub bytes ~pos:off ~len:(min n (String.length bytes - off))
  in
  let encoding =
    match e.arch with Arm -> Primus.Interworking.encoding ~thumb | _ -> None
  in
  match t.state with
  | Running -> hooked t ?encoding ~thumb addr bytes
  | _ ->
      let result = ref None in
      primus t
        (module functor
                  (Machine : Primus.Machine.S)
                  ->
                  struct
                    module Lift = Primus.Lift.Make (Machine)
                    open Machine.Syntax

                    let init () =
                      Lift.insn ?encoding ~read addr >>| fun insn ->
                      result := insn
                  end);
      !result

(* the bytes of the code at [addr], at most the size of an instruction,
   fewer, if the rest is not mapped *)
let code_bytes t addr =
  List.range ~stride:(-1) Primus.Lift.max_size 0
  |> List.find_map ~f:(fun n ->
      try Some (read t addr n) with Invalid_argument _ -> None)
  |> Option.value ~default:""

(* the instruction at [pc], lifted outside of the machine, as in the
   hooks, from [bytes], by default, that it has now, in the mode, e.g.,
   Thumb or A32 of ARM, as the target doesn't know it *)
let lift ?(thumb = false) ?bytes t pc =
  let bytes = match bytes with Some b -> b | None -> code_bytes t pc in
  let encoding =
    match (engine t).arch with
    | Arm -> Primus.Interworking.encoding ~thumb
    | _ -> None
  in
  hooked t ?encoding ~thumb pc bytes

module Trace = struct
  type emu = t

  type t = {
    emu : emu;
    trace : Uc.Trace.t;
    memory : bool;
    mutable active : bool;
    mutable hooks : (Uc.t * Uc.hook list) option;  (** on the engine *)
    blocks : (int * int64 array) list Int64.Table.t;
        (** the instructions of the blocks, by their addresses, with the lower
            bit of Thumb, and sizes, see [insns] *)
  }

  (* the hooks are native, see [Uc.trace], and go to the new engines too,
     until the trace stops *)
  let start ?(size = 1 lsl 20) ?every ?(blocks = false) ?(accesses = 0) ?first
      ?last emu =
    let memory = accesses > 0 in
    if
      memory
      && (Option.value every ~default:1 > 1
         || Option.is_some first || Option.is_some last)
    then
      invalid_arg
        "Bap_emu.Trace.start: the accesses are recorded only with all \
         instructions, or blocks";
    let trace = Uc.Trace.create ?every ~blocks ~accesses size in
    let t =
      {
        emu;
        trace;
        memory;
        active = true;
        hooks = None;
        blocks = Int64.Table.create ();
      }
    in
    installed emu (fun e ->
        if t.active then
          t.hooks <- Some (e.uc, Uc.trace ?first ?last ~memory e.uc trace));
    t

  (* the hooks of a closed engine are gone with it *)
  let stop t =
    if t.active then begin
      t.active <- false;
      Option.iter t.hooks ~f:(fun (uc, hooks) ->
          List.iter hooks ~f:(fun hook ->
              try Uc.delete uc hook with Invalid_argument _ -> ()));
      t.hooks <- None
    end

  let count t = Uc.Trace.count t.trace
  let clear t = Uc.Trace.clear t.trace
  let blocks t = Uc.Trace.blocks t.trace
  let pcs ?last t = Uc.Trace.pcs ?last t.trace
  let sizes ?last t = Uc.Trace.sizes ?last t.trace
  let save ?last t file = Uc.Trace.save ?last t.trace file

  type access = {
    insn : int64;
    pc : int64;
    addr : int64;
    size : int;
    write : bool;
    value : int64;
    old : int64;
  }

  let access rows i =
    let open Bigarray.Array2 in
    let info = get rows i 3 in
    {
      insn = get rows i 0;
      addr = get rows i 1;
      value = get rows i 2;
      size = Int64.(to_int_exn (info land 0xFFFF_FFFFL));
      write = Int64.(shift_right_logical info 32 land 1L = 1L);
      pc = get rows i 4;
      old = get rows i 5;
    }

  let accesses ?last t =
    let rows = Uc.Trace.accesses ?last t.trace in
    List.init (Bigarray.Array2.dim1 rows) ~f:(access rows)

  (* the instructions of the block of [size] bytes at [addr], in the
     mode, which are decoded once, as the sizes of the instructions, that
     are lifted *)
  let block t ~thumb addr size =
    let key = if thumb then Int64.(addr lor 1L) else addr in
    let known = Option.value (Hashtbl.find t.blocks key) ~default:[] in
    match List.Assoc.find known size ~equal:Int.equal with
    | Some insns -> insns
    | None ->
        let last = Int64.(addr + of_int size) in
        let rec loop pc acc =
          if Int64.(pc >= last) then Array.of_list_rev acc
          else
            match lift ~thumb t.emu pc with
            | Some (n, _) when n > 0 -> loop Int64.(pc + of_int n) (pc :: acc)
            | _ -> Array.of_list_rev (pc :: acc)
        in
        let insns = loop addr [] in
        Hashtbl.set t.blocks ~key ~data:((size, insns) :: known);
        insns

  type words = (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array1.t

  let words n : words =
    Bigarray.Array1.create Bigarray.int64 Bigarray.c_layout n

  (* the program counters of the instructions of the last [last] records,
     and the indices of their records, which are unboxed, and their modes,
     see [Uc.Trace.modes] *)
  let window ?(records = true) ?last t : words * words * Uc.Trace.modes =
    let pcs = pcs ?last t in
    let n = Bigarray.Array1.dim pcs in
    let first = Int64.(count t - of_int n) in
    let modes = Uc.Trace.modes ?last t.trace in
    if not (blocks t) then begin
      let indices = words (if records then n else 0) in
      if records then
        for i = 0 to n - 1 do
          Bigarray.Array1.unsafe_set indices i Int64.(first + of_int i)
        done;
      (pcs, indices, modes)
    end
    else
      let sizes = sizes ?last t in
      (* the blocks of the loops repeat, so they are cached by the lower
         bits of their addresses first *)
      let slots = 4096 in
      let cache = Array.create ~len:slots (-1L, -1, [||]) in
      let insns =
        Array.init n ~f:(fun i ->
            let thumb = Bigarray.Array1.unsafe_get modes i = 1 in
            let addr = Bigarray.Array1.unsafe_get pcs i in
            let key = if thumb then Int64.(addr lor 1L) else addr in
            let size =
              Int32.to_int_trunc (Bigarray.Array1.unsafe_get sizes i)
            in
            let slot = Int64.to_int_trunc key land (slots - 1) in
            let a, sz, b = Array.unsafe_get cache slot in
            if Int64.(a = key) && sz = size then b
            else
              let b = block t ~thumb addr size in
              Array.unsafe_set cache slot (key, size, b);
              b)
      in
      let total = Array.sum (module Int) insns ~f:Array.length in
      let out = words total
      and indices = words (if records then total else 0)
      and expanded =
        Bigarray.Array1.create Bigarray.int8_unsigned Bigarray.c_layout
          (if records then total else 0)
      in
      let pos = ref 0 in
      Array.iteri insns ~f:(fun i b ->
          let record = Int64.(first + of_int i) in
          let mode = Bigarray.Array1.unsafe_get modes i in
          for j = 0 to Array.length b - 1 do
            Bigarray.Array1.unsafe_set out (!pos + j) (Array.unsafe_get b j);
            if records then begin
              Bigarray.Array1.unsafe_set indices (!pos + j) record;
              Bigarray.Array1.unsafe_set expanded (!pos + j) mode
            end
          done;
          pos := !pos + Array.length b);
      (out, indices, expanded)

  let insns ?last t =
    if blocks t then
      let pcs, _, _ = window ~records:false ?last t in
      pcs
    else pcs ?last t
end

type location = Reg of string | Mem of int64 * int
type step = { index : int64; pc : int64 }

type slice = {
  steps : step list;
  live : location list;
  gaps : int64 list;
  complete : bool;
}

(* The registers, that an instruction writes, and, for the ones, that are
   needed, the registers, that it reads to compute them, and the loads,
   that they make, through its temporaries, as the defs of all its
   blocks run in order. The defs of the blocks, that the instruction may
   skip, e.g., of a compare and exchange, may keep the registers, so they
   stay live, and their values depend on the conditions of the jumps, as
   of a conditional move. The stores, that are recorded, did happen, so
   the conditions of the jumps, e.g., of a repeated move, are not in the
   slice of the data.

   The loads and the stores are numbered in the order, that they run in,
   so that they are the accesses of the record, e.g., of the registers,
   that a load or a store of multiple registers of ARM moves, if their
   sizes are the same. *)
module Insn = struct
  (* the variables of the values, and of the addresses, and the loads of
     the values, and of the addresses *)
  type use = {
    vars : Var.t list;
    addrs : Var.t list;
    loads : int list;
    aloads : int list;
  }

  type def = {
    lhs : Var.t;
    must : bool;  (** the def must happen *)
    use : use;
    stores : (int * use) list;  (** the stores of the memory, and their values *)
  }

  type t = {
    size : int;
    defs : def list;
    conds : use list;
    load_sizes : int list;  (** of the loads, in their order *)
    store_sizes : int list;
    written : String.Set.t;
  }

  let register v =
    (not (Var.is_virtual v))
    && match Var.typ v with Imm _ -> true | Mem _ | Unk -> false

  let name v = String.uppercase (Var.name v)

  (* the blocks, that are on each of the paths from the first block to the
     ones, that leave the instruction *)
  let must blks =
    let blks = Array.of_list blks in
    let index = Tid.Table.create () in
    Array.iteri blks ~f:(fun i b -> Hashtbl.set index ~key:(Term.tid b) ~data:i);
    let succs i =
      let jmps = Term.enum jmp_t blks.(i) |> Seq.to_list in
      let targets =
        List.filter_map jmps ~f:(fun j ->
            match Jmp.kind j with
            | Goto (Direct tid) -> Some (Hashtbl.find index tid)
            | _ -> Some None)
      in
      let falls =
        List.for_all jmps ~f:(fun j ->
            match Jmp.cond j with Int w -> Word.is_zero w | _ -> true)
      in
      (* the block, whose jumps are conditional, falls through *)
      if falls then None :: targets else targets
    in
    let leaves i ~avoid =
      let seen = Array.create ~len:(Array.length blks) false in
      let rec go i =
        (not (i = avoid || seen.(i)))
        && begin
          seen.(i) <- true;
          List.exists (succs i) ~f:(function None -> true | Some j -> go j)
        end
      in
      go i
    in
    Array.mapi blks ~f:(fun i _ ->
        i = 0 || Array.length blks = 1 || not (leaves 0 ~avoid:i))

  type acc = {
    mutable vars : Var.t list;
    mutable addrs : Var.t list;
    mutable loads : int list;
    mutable aloads : int list;
  }

  let fresh () = { vars = []; addrs = []; loads = []; aloads = [] }

  let use (a : acc) : use =
    { vars = a.vars; addrs = a.addrs; loads = a.loads; aloads = a.aloads }

  let of_blks size blks =
    let must = must blks in
    let load_sizes = ref [] and store_sizes = ref [] in
    let next sizes n =
      let id = List.length !sizes in
      sizes := n :: !sizes;
      id
    in
    (* the subexpressions run first, the address before the load or the
       store *)
    let rec go (acc : acc) ~addr stores e =
      let go' = go acc ~addr stores in
      match (e : exp) with
      | Var v -> (
          match Var.typ v with
          | Mem _ -> ()
          | _ ->
              if addr then acc.addrs <- v :: acc.addrs
              else acc.vars <- v :: acc.vars)
      | Load (m, a, _, sz) ->
          go' m;
          go acc ~addr:true stores a;
          let id = next load_sizes (Size.in_bytes sz) in
          if addr then acc.aloads <- id :: acc.aloads
          else acc.loads <- id :: acc.loads
      | Store (m, a, x, _, sz) ->
          go' m;
          let value = fresh () in
          go value ~addr:true stores a;
          go value ~addr:false stores x;
          let id = next store_sizes (Size.in_bytes sz) in
          stores := (id, use value) :: !stores;
          acc.vars <- value.vars @ acc.vars;
          acc.addrs <- value.addrs @ acc.addrs;
          acc.loads <- value.loads @ acc.loads;
          acc.aloads <- value.aloads @ acc.aloads
      | BinOp (_, x, y) | Concat (x, y) | Let (_, x, y) ->
          go' x;
          go' y
      | UnOp (_, x) | Cast (_, _, x) | Extract (_, _, x) -> go' x
      | Ite (c, x, y) ->
          go' c;
          go' x;
          go' y
      | Int _ | Unknown _ -> ()
    in
    let analyze e =
      let a = fresh () and stores = ref [] in
      go a ~addr:false stores e;
      (use a, List.rev !stores)
    in
    let defs = ref [] and conds = ref [] in
    List.iteri blks ~f:(fun i b ->
        Term.enum def_t b
        |> Seq.iter ~f:(fun d ->
            let use, stores = analyze (Def.rhs d) in
            defs := { lhs = Def.lhs d; must = must.(i); use; stores } :: !defs);
        Term.enum jmp_t b
        |> Seq.iter ~f:(fun j ->
            match Jmp.cond j with
            | Int _ -> ()
            | c -> conds := fst (analyze c) :: !conds));
    let defs = List.rev !defs in
    let written =
      List.filter_map defs ~f:(fun d ->
          Option.some_if (register d.lhs) (name d.lhs))
      |> String.Set.of_list
    in
    {
      size;
      defs;
      conds = List.rev !conds;
      load_sizes = List.rev !load_sizes;
      store_sizes = List.rev !store_sizes;
      written;
    }

  (* The registers, that compute the [needed] registers, and the stores,
     that [stored] tells, or all, if [stores] and it doesn't, and the
     loads, that they make, and whether they load, and whether the stores
     may not happen, as the instruction, which [rewrites] the bytes, that
     it reads, may write them back, e.g., a compare and exchange, that
     fails, which the semantics doesn't have. *)
  let inputs ~addresses insn ~needed ~stores ~stored ~rewrites =
    let live = Var.Hash_set.create () in
    let loads = Int.Hash_set.create () in
    let take (u : use) =
      List.iter u.vars ~f:(Hash_set.add live);
      List.iter u.loads ~f:(Hash_set.add loads);
      if addresses then begin
        List.iter u.addrs ~f:(Hash_set.add live);
        List.iter u.aloads ~f:(Hash_set.add loads)
      end
    in
    (* the conditions are taken at the end, before the temporaries,
       that compute them, if a def, that is needed, may not happen *)
    let walk ~conds =
      Hash_set.clear live;
      Hash_set.clear loads;
      List.iter insn.defs ~f:(fun d ->
          if register d.lhs && Set.mem needed (name d.lhs) then
            Hash_set.add live d.lhs);
      if conds then List.iter insn.conds ~f:take;
      List.fold (List.rev insn.defs) ~init:false ~f:(fun skipped d ->
          match Var.typ d.lhs with
          | Mem _ ->
              let taken =
                match stored with
                | Some stored ->
                    List.fold d.stores ~init:false ~f:(fun taken (id, u) ->
                        if stored id then (
                          take u;
                          true)
                        else taken)
                | None ->
                    if stores then take d.use;
                    stores
              in
              skipped || (taken && rewrites && not d.must)
          | _ ->
              if Hash_set.mem live d.lhs then begin
                if d.must then Hash_set.remove live d.lhs;
                take d.use;
                skipped || not d.must
              end
              else skipped)
    in
    let skipped = walk ~conds:false in
    if skipped then ignore (walk ~conds:true : bool);
    let regs =
      Hash_set.to_list live
      |> List.filter_map ~f:(fun v -> Option.some_if (register v) (name v))
    in
    (regs, Hash_set.to_list loads, skipped && stores && rewrites)
end

(* the bytes of the locations, coalesced *)
let ranges bytes =
  List.sort (Hash_set.to_list bytes) ~compare:Int64.compare
  |> List.fold ~init:[] ~f:(fun acc a ->
      match acc with
      | Mem (b, n) :: rest when Int64.(b + of_int n = a) ->
          Mem (b, n + 1) :: rest
      | _ -> Mem (a, 1) :: acc)
  |> List.rev

(* The slice goes backward from the last recorded instruction, whose
   defs of the live locations make it a step, which kills them, and
   makes its inputs live, the registers, that compute them, and the
   bytes, that it read, if they load, as the trace has their addresses.
   The instructions of a trace of blocks are of their blocks, and their
   accesses are found by their program counters. The instructions are
   lifted once, from the bytes, that they have now, outside of the
   machine, as in the hooks. *)
let slice ?(addresses = false) ?window (tr : Trace.t) criterion =
  let t = tr.emu in
  let pcs, records, modes = Trace.window ?last:window tr in
  let n = Bigarray.Array1.dim pcs in
  let blocks = Trace.blocks tr in
  let rows = Uc.Trace.accesses tr.trace in
  let rows_n = Bigarray.Array2.dim1 rows in
  let first_record =
    if n = 0 then Trace.count tr else Bigarray.Array1.get records 0
  in
  (* the records before the oldest kept access, whose accesses the ring
     has lost, aren't in the window, as the record of the oldest one, that
     may have lost its first accesses *)
  let covered =
    if
      (not tr.memory)
      || Int64.(Uc.Trace.accesses_count tr.trace = of_int rows_n)
    then first_record
    else if rows_n = 0 then Trace.count tr
    else Int64.(max first_record ((Trace.access rows 0).insn + 1L))
  in
  let live_regs = String.Hash_set.create () in
  let live_mem = Int64.Hash_set.create () in
  List.iter criterion ~f:(function
    | Reg r -> Hash_set.add live_regs (String.uppercase r)
    | Mem (a, size) ->
        for i = 0 to size - 1 do
          Hash_set.add live_mem Int64.(a + of_int i)
        done);
  (* the loads, whose bytes the trace doesn't have *)
  let untracked = ref false in
  (* the records, before which the registers, the bit 62, or the memory,
     the bit 63, were written outside of the trace, with the written
     bytes, if they are known, and the ones, whose instructions, by the
     records and the program counters, a hook wrote them before, the bit
     61, see [Uc.Trace.bounds] *)
  let bounds = Int64.Table.create () and inside = Hashtbl.Poly.create () in
  let marks = Uc.Trace.bounds tr.trace and written = Uc.Trace.ranges tr.trace in
  let pos = ref 0 in
  for i = 0 to (Bigarray.Array1.dim marks / 3) - 1 do
    let b = Bigarray.Array1.get marks (3 * i) in
    let record = Int64.(b land 0x1FFF_FFFF_FFFF_FFFFL) in
    let regs = Int64.(b land 0x4000_0000_0000_0000L <> 0L) in
    let mem = Int64.(b < 0L) in
    let n = Int64.to_int_exn (Bigarray.Array1.get marks ((3 * i) + 2)) in
    let ranges =
      if n < 0 then None
      else
        Some
          (List.init n ~f:(fun j ->
               let k = 2 * (!pos + j) in
               Bigarray.Array1.(get written k, get written (k + 1))))
    in
    pos := !pos + Int.max n 0;
    let merge = function
      | None -> (regs, mem, ranges)
      | Some (r, m, w) ->
          (r || regs, m || mem, Option.map2 w ranges ~f:List.append)
    in
    if Int64.(b land 0x2000_0000_0000_0000L = 0L) then
      Hashtbl.update bounds record ~f:merge
    else
      let pc = Bigarray.Array1.get marks ((3 * i) + 1) in
      Hashtbl.update inside (record, pc) ~f:merge
  done;
  let gaps = ref [] in
  (* the live bytes, that were written outside, come from there, and
     aren't live before, unless the written ones are unknown *)
  let gap record = function
    | Some (regs, mem, ranges) ->
        let outside =
          match ranges with
          | Some ranges when mem ->
              Hash_set.filter live_mem ~f:(fun a ->
                  List.exists ranges ~f:(fun (b, n) ->
                      Int64.(a >= b && a - b < n)))
          | _ -> Int64.Hash_set.create ()
        in
        if
          (regs && not (Hash_set.is_empty live_regs))
          || mem
             &&
             if Option.is_some ranges then not (Hash_set.is_empty outside)
             else not (Hash_set.is_empty live_mem)
        then gaps := record :: !gaps;
        Hash_set.iter outside ~f:(Hash_set.remove live_mem)
    | None -> ()
  in
  (* the values of the live locations may come from outside of the trace,
     before the instruction, that a hook wrote them before, or before the
     first instruction of a record, that follows a boundary *)
  let crossed k =
    let record = Bigarray.Array1.get records k in
    if not (Hashtbl.is_empty inside) then
      gap record (Hashtbl.find inside (record, Bigarray.Array1.get pcs k));
    if k = 0 || not (Int64.equal (Bigarray.Array1.get records (k - 1)) record)
    then gap record (Hashtbl.find bounds record)
  in
  (* the bytes of the code, that the later writes changed, as they were
     at the instruction, which the walk is at, i.e., the bytes, that the
     earliest of the writes, that it saw, overwrote, or [None], if they
     are unknown, e.g., of a wide write *)
  let earlier = Int64.Table.create () in
  let executable = Int64.Table.create () in
  let is_code addr =
    let page = X.page_of addr in
    Hashtbl.find_or_add executable page ~default:(fun () ->
        match Hashtbl.find (engine t).pages page with
        | Some { perm; _ } -> Uc.Perm.(mem perm exec)
        | None -> false)
  in
  let overwrote (a : Trace.access) =
    if a.write then
      for i = 0 to a.size - 1 do
        let addr = Int64.(a.addr + of_int i) in
        if is_code addr then
          Hashtbl.set earlier ~key:addr
            ~data:
              (Option.some_if (a.size <= 8)
                 (Char.of_int_exn
                    Int64.(
                      to_int_exn
                        (shift_right_logical a.old Int.(8 * i) land 0xFFL))))
      done
  in
  let lifted = Int64.Table.create () in
  (* the instruction, in its mode, as it was, if the program patched it
     later, and its bytes are known, or else as it is now *)
  let insn ~thumb pc =
    let now () =
      let key = if thumb then Int64.(pc lor 1L) else pc in
      Hashtbl.find_or_add lifted key ~default:(fun () ->
          Option.map (lift ~thumb t pc) ~f:(fun (size, blks) ->
              Insn.of_blks size blks))
    in
    if Hashtbl.is_empty earlier then now ()
    else
      let bytes = code_bytes t pc in
      let changed = ref false and known = ref true in
      let old =
        String.mapi bytes ~f:(fun i c ->
            match Hashtbl.find earlier Int64.(pc + of_int i) with
            | Some (Some c') ->
                if Char.(c <> c') then changed := true;
                c'
            | Some None ->
                known := false;
                c
            | None -> c)
      in
      if !changed && !known then
        Option.map (lift ~thumb ~bytes:old t pc) ~f:(fun (size, blks) ->
            Insn.of_blks size blks)
      else now ()
  in
  (* The instructions of an IT block of Thumb have the conditions, that
     the decoder of LLVM keeps, as it decodes the IT instruction, and the
     next ones, and their lifts are kept, so the block is lifted in its
     order, from the IT instruction, that is in the 4 records before the
     instruction, before the walk, which goes backward, lifts one of
     them. The IT block before the window isn't known. *)
  let it_length = Int64.Table.create () in
  let it_block pc =
    Hashtbl.find_or_add it_length pc ~default:(fun () ->
        match code_bytes t pc with
        | b when String.length b >= 2 ->
            let h = Char.to_int b.[0] lor (Char.to_int b.[1] lsl 8) in
            let mask = h land 0xF in
            if h land 0xFF00 = 0xBF00 && mask <> 0 then 4 - Int.ctz mask else 0
        | _ -> 0)
  in
  let grouped = Int64.Hash_set.create () in
  let is_thumb k =
    k >= 0 && k < Bigarray.Array1.dim modes && Bigarray.Array1.get modes k = 1
  in
  let in_order k =
    Sequence.range ~stop:`inclusive (Int.max 0 (k - 4)) k
    |> Sequence.find ~f:(fun j ->
        is_thumb j && j < k && k - j <= it_block (Bigarray.Array1.get pcs j))
    |> Option.iter ~f:(fun j ->
        let it = Bigarray.Array1.get pcs j in
        if not (Hash_set.mem grouped it) then begin
          Hash_set.add grouped it;
          (* by the addresses, as the instructions, whose conditions
             fail, have no records *)
          let rec lift pc i =
            if i >= 0 then
              match insn ~thumb:true pc with
              | Some { size; _ } when size > 0 ->
                  lift Int64.(pc + of_int size) (i - 1)
              | _ -> ()
          in
          lift it (it_block it)
        end)
  in
  (* the access is of the instruction at [k], of a later one, whose
     access is skipped, or of an earlier one, as the instructions of a
     block of a trace of blocks have increasing addresses *)
  let order k (a : Trace.access) =
    let record = Bigarray.Array1.get records k in
    if Int64.(a.insn > record) then `Later
    else if Int64.(a.insn < record) then `Earlier
    else if not blocks then `Ours
    else
      let pc = Bigarray.Array1.get pcs k in
      if Int64.(a.pc > pc) then `Later
      else if Int64.(a.pc < pc) then `Earlier
      else `Ours
  in
  let rec loop k row steps =
    if
      k < 0
      || Int64.(Bigarray.Array1.get records k < covered)
      || (Hash_set.is_empty live_regs && Hash_set.is_empty live_mem)
    then steps
    else
      let record = Bigarray.Array1.get records k in
      (* the accesses of the instruction, which are before [row] *)
      let rec accesses row reads writes =
        if row < 0 then row
        else
          let a = Trace.access rows row in
          match order k a with
          | `Later ->
              overwrote a;
              accesses (row - 1) reads writes
          | `Ours ->
              overwrote a;
              (if a.write then writes else reads)
              := a :: !(if a.write then writes else reads);
              accesses (row - 1) reads writes
          | `Earlier -> row
      in
      let reads = ref [] and writes = ref [] in
      let row = accesses row reads writes in
      (* the accesses, in their order *)
      let bytes_of (a : Trace.access) =
        List.init a.size ~f:(fun i -> Int64.(a.addr + of_int i))
      in
      let read_bytes = List.concat_map !reads ~f:bytes_of
      and write_bytes = List.concat_map !writes ~f:bytes_of in
      let pc = Bigarray.Array1.get pcs k in
      let stores = List.exists write_bytes ~f:(Hash_set.mem live_mem) in
      let thumb = is_thumb k in
      if thumb then in_order k;
      match insn ~thumb pc with
      | None ->
          crossed k;
          loop (k - 1) row steps
      | Some i ->
          let needed = Set.filter i.written ~f:(Hash_set.mem live_regs) in
          if Set.is_empty needed && not stores then begin
            crossed k;
            loop (k - 1) row steps
          end
          else begin
            let rewrites =
              List.exists write_bytes
                ~f:(List.mem read_bytes ~equal:Int64.equal)
            in
            (* the accesses of the loads and the stores, by their numbers,
               if they are the same *)
            let matched accesses sizes =
              let accesses = Array.of_list accesses in
              Option.some_if
                (List.equal Int.equal sizes
                   (Array.to_list accesses
                   |> List.map ~f:(fun (a : Trace.access) -> a.size)))
                (fun id -> bytes_of accesses.(id))
            in
            let loaded = matched !reads i.load_sizes in
            let stored =
              Option.map (matched !writes i.store_sizes) ~f:(fun bytes id ->
                  List.exists (bytes id) ~f:(Hash_set.mem live_mem))
            in
            let regs, loads, kept =
              Insn.inputs ~addresses i ~needed ~stores ~stored ~rewrites
            in
            Set.iter needed ~f:(Hash_set.remove live_regs);
            if not kept then List.iter write_bytes ~f:(Hash_set.remove live_mem);
            List.iter regs ~f:(Hash_set.add live_regs);
            if not (List.is_empty loads) then
              if tr.memory then
                match loaded with
                | Some bytes ->
                    List.iter loads ~f:(fun id ->
                        List.iter (bytes id) ~f:(Hash_set.add live_mem))
                | None -> List.iter read_bytes ~f:(Hash_set.add live_mem)
              else untracked := true;
            crossed k;
            loop (k - 1) row ({ index = record; pc } :: steps)
          end
  in
  let steps = loop (n - 1) (rows_n - 1) [] in
  let live =
    (Hash_set.to_list live_regs
    |> List.sort ~compare:String.compare
    |> List.map ~f:(fun r -> Reg r))
    @ ranges live_mem
  in
  let gaps = List.rev !gaps in
  {
    steps;
    live;
    gaps;
    complete = List.is_empty live && List.is_empty gaps && not !untracked;
  }

let on_code ?first ?last t f =
  installed t (fun e ->
      let fresh = instructions t in
      ignore
        (Uc.on_code ?first ?last e.uc (fun addr _ ->
             if fresh addr then f t addr)))

let on_read ?first ?last t f =
  installed t (fun e ->
      ignore
        (Uc.on_mem ?first ?last e.uc [ `read ] (fun _ addr size _ ->
             f t addr size)))

let on_write ?first ?last t f =
  installed t (fun e ->
      ignore
        (Uc.on_mem ?first ?last e.uc [ `write ] (fun _ addr size value ->
             f t addr size value)))

(* the functions of the program, which no stub replaces, are hooked at
   their addresses, once, by the name, that the address has, when it is
   called, see [add_symbol], and the others stop Unicorn, see
   [X.call_returns] *)
let hook_calls t addr =
  if not (Hash_set.mem t.hooked_calls addr) then begin
    Hash_set.add t.hooked_calls addr;
    installed t (fun e ->
        (* the call is seen once, as the first instruction of the
           function runs again, when Unicorn starts at it again, after
           the hook saw it, and Unicorn stopped there, e.g., as the hook
           stops it *)
        let fresh = instructions t in
        ignore
          (Uc.on_code e.uc ~first:addr ~last:addr (fun addr _ ->
               let s = t.session in
               if fresh addr && not (Hash_set.mem e.foreign addr) then
                 match
                   Option.bind (Hashtbl.find s.names addr) ~f:(X.call_returns e)
                 with
                 | Some ret ->
                     e.reason <- Some (X.Jump ret);
                     Uc.stop e.uc
                 | None -> ())))
  end

let on_call t name f =
  let hook () =
    t.call <- Some name;
    Exn.protect
      ~f:(fun () ->
        match f t with Default -> X.Default | Return x -> X.Return x)
      ~finally:(fun () -> t.call <- None)
  in
  Hashtbl.add_multi t.session.call_hooks ~key:name ~data:hook;
  Hashtbl.iteri t.session.names ~f:(fun ~key:addr ~data ->
      if String.equal data name then hook_calls t addr)

(* the name goes to the checkpoints, and replaces the name, that the
   address had, e.g., of the program *)
let add_symbol t name addr =
  Hashtbl.set t.session.symbols ~key:addr ~data:name;
  Hashtbl.set t.session.names ~key:addr ~data:name;
  if Hashtbl.mem t.session.call_hooks name then hook_calls t addr

let symbols t =
  Hashtbl.to_alist t.session.names
  |> List.sort ~compare:(fun (a, _) (b, _) -> Int64.compare a b)
  |> List.map ~f:(fun (addr, name) -> (name, addr))

(* the functions of the program, whose code runs again in Unicorn,
   instead of the stubs, that replaced them *)
let unstub t name =
  let own addr =
    Hashtbl.existsi t.session.own_code ~f:(fun ~key ~data:_ ->
        Int64.equal (X.int64_of_word key) addr)
  in
  let addrs =
    Hashtbl.to_alist t.session.names
    |> List.filter_map ~f:(fun (addr, data) ->
        Option.some_if (String.equal data name && own addr) addr)
  in
  if List.is_empty addrs then
    invalid_argf "Bap_emu.unstub: %s is not a function of the program" name ();
  let module Unstub (Machine : Primus.Machine.S) = struct
    module Exec = X.Make (Machine)

    let init () = Machine.List.iter addrs ~f:Exec.unstub
  end in
  primus t (module Unstub)

let arg t n =
  let name =
    match t.call with
    | Some name -> name
    | None -> invalid_arg "Bap_emu.arg: no function is called"
  in
  match Hashtbl.find t.session.signatures name with
  | Some { inputs; _ } -> (
      match List.nth inputs n with
      | Some exp ->
          accessible t 0L 0 (fun () ->
              Bitvec.to_int64 (Word.to_bitvec (X.eval_uc (engine t) exp)))
      | None -> invalid_argf "Bap_emu.arg: %s has no argument %d" name n ())
  | None -> invalid_argf "Bap_emu.arg: the prototype of %s is unknown" name ()

let exit_code t = t.session.exit_code

(* the system, whose program ended, finishes, as its knowledge is the
   result of the system *)
let knowledge t =
  (match t.state with Ended _ -> resume t (X.Continue 0L) | _ -> ());
  match t.state with Finished (Ok (_, _, kb)) -> Some kb | _ -> None

(* The taint of the values, that the program computes, which Primus
   tracks, see [Bap_taint], as the program runs in Unicorn, which leaves
   the code, that uses the tainted values, to Primus. *)
module Taint = struct
  open Bap_core_theory
  module T = Bap_taint.Std.Taint

  type place = Reg of string | Mem of int64 * int

  let components =
    [ "bap:propagate-taint-by-computation"; "bap:select-default-taint-policy" ]

  (* the variable of the register of the target, or of its base
     register, e.g., R0 for X0 or W0 of AArch64, as the code reads it *)
  let var target name =
    match Theory.Target.var target name with
    | None -> invalid_argf "Bap_emu: unknown register %s" name ()
    | Some v -> (
        match
          Option.bind (Theory.Target.unalias target v) ~f:Theory.Origin.cast_sub
        with
        | Some origin -> Var.reify (Theory.Origin.reg origin)
        | None -> Var.reify v)

  (* the place is checked, before the component runs, as its exceptions
     end the program *)
  let checked t place =
    match place with
    | Reg name -> ignore (var t.target name : Var.t)
    | Mem (_, len) when len < 0 ->
        invalid_argf "Bap_emu: the negative length %d" len ()
    | Mem _ -> ()

  let introduce t ~kind place =
    checked t place;
    let module Introduce (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Env = Primus.Env.Make (Machine)
      module Value = Primus.Value.Make (Machine)
      module Kind = T.Kind.Make (Machine)
      module Tracker = T.Tracker.Make (Machine)

      let init () =
        Kind.create kind >>= fun kind ->
        match place with
        | Reg name ->
            Machine.gets Project.target >>= fun target ->
            Env.get (var target name) >>= fun v ->
            Tracker.new_direct v kind >>| ignore
        | Mem (addr, len) ->
            Machine.gets Project.target >>= fun target ->
            let width = Theory.Target.code_addr_size target in
            Value.of_word (Word.of_int64 ~width addr) >>= fun addr ->
            Value.of_int ~width len >>= fun len ->
            Tracker.new_indirect ~addr ~len kind >>| ignore
    end in
    primus t (module Introduce)

  (* the kinds of the taints of the place *)
  let kinds t place =
    checked t place;
    let result = ref [] in
    let module Kinds (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Env = Primus.Env.Make (Machine)
      module Value = Primus.Value.Make (Machine)
      module Kind = T.Kind.Make (Machine)
      module Object = T.Object.Make (Machine)
      module Tracker = T.Tracker.Make (Machine)

      let names objects =
        Machine.List.map (Set.to_list objects) ~f:(fun obj ->
            Object.kind obj >>= Kind.name)

      let init () =
        Machine.gets Project.target >>= fun target ->
        (match place with
          | Reg name ->
              Env.get (var target name) >>= fun v ->
              Tracker.lookup v T.Rel.direct >>= names
          | Mem (addr, len) ->
              let width = Theory.Target.code_addr_size target in
              Machine.List.map (List.init len ~f:Fn.id) ~f:(fun i ->
                  Value.of_word (Word.of_int64 ~width Int64.(addr + of_int i))
                  >>= fun addr -> Tracker.lookup addr T.Rel.indirect >>= names)
              >>| List.concat)
        >>| fun kinds ->
        result := List.dedup_and_sort kinds ~compare:String.compare
    end in
    primus t (module Kinds);
    !result

  let is_tainted t ~kind place =
    List.mem (kinds t place) kind ~equal:String.equal

  let sanitize t ~kind place =
    checked t place;
    let module Sanitize (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Env = Primus.Env.Make (Machine)
      module Value = Primus.Value.Make (Machine)
      module Kind = T.Kind.Make (Machine)
      module Tracker = T.Tracker.Make (Machine)

      let init () =
        Kind.create kind >>= fun kind ->
        Machine.gets Project.target >>= fun target ->
        match place with
        | Reg name ->
            Env.get (var target name) >>= fun v ->
            Tracker.sanitize v T.Rel.direct kind
        | Mem (addr, len) ->
            let width = Theory.Target.code_addr_size target in
            Machine.List.iter (List.init len ~f:Fn.id) ~f:(fun i ->
                Value.of_word (Word.of_int64 ~width Int64.(addr + of_int i))
                >>= fun addr -> Tracker.sanitize addr T.Rel.indirect kind)
    end in
    primus t (module Sanitize)

  let on_jump t f =
    let module Observe (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Kind = T.Kind.Make (Machine)
      module Object = T.Object.Make (Machine)
      module Tracker = T.Tracker.Make (Machine)

      let jumped (cond, dst) =
        Tracker.lookup cond T.Rel.direct >>= fun objects ->
        if Set.is_empty objects then Machine.return ()
        else
          Machine.List.map (Set.to_list objects) ~f:(fun obj ->
              Object.kind obj >>= Kind.name)
          >>| fun kinds ->
          f t
            ~kinds:(List.dedup_and_sort kinds ~compare:String.compare)
            (Bitvec.to_int64 (Word.to_bitvec (Primus.Value.to_word dst)))

      let init () =
        Machine.Observation.observe Primus.Interpreter.jumping jumped
    end in
    primus t (module Observe)
end

(* The symbolic execution of the values, that the program computes from
   its inputs, which Primus tracks, see [Bap_primus_symbolic], as the
   program runs in Unicorn, which leaves the code, that uses the symbolic
   values, to Primus. *)
module Symbolic = struct
  open Bap_core_theory
  module S = Bap_primus_symbolic

  type place = Taint.place = Reg of string | Mem of int64 * int
  type model = (string * int64) list

  type branch = {
    addr : int64;
    taken : bool;
    condition : string;
    formula : S.SMT.formula;
    path : S.SMT.formula list;
    inputs : S.Input.t list;
  }

  let components = [ "bap:symbolic-computer"; "bap:symbolic-path-constraints" ]
  let to_int64 x = Bitvec.to_int64 (Word.to_bitvec x)

  let model inputs model =
    List.filter_map inputs ~f:(fun input ->
        S.SMT.Model.get model input
        |> Option.map ~f:(fun x ->
            (S.Input.to_symbol input, to_int64 (S.SMT.Value.to_word x))))

  (* the addresses of the bytes of the place in the memory *)
  let addresses target addr len =
    let width = Theory.Target.code_addr_size target in
    List.init len ~f:(fun i -> Word.of_int64 ~width Int64.(addr + of_int i))

  let symbolize t place =
    Taint.checked t place;
    let module Symbolize (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Env = Primus.Env.Make (Machine)
      module Mems = Primus.Memory.Make (Machine)
      module Value = Primus.Value.Make (Machine)
      module Executor = S.Executor (Machine)

      (* the fresh value, whose formula is the input *)
      let input origin x =
        Value.of_word (Primus.Value.to_word x) >>= fun x ->
        Executor.set_input origin x >>| fun () -> x

      let init () =
        Machine.gets Project.target >>= fun target ->
        match place with
        | Reg name ->
            let v = Taint.var target name in
            Env.get v >>= input (S.Input.var v) >>= Env.set v
        | Mem (addr, len) ->
            Mems.memory >>= fun bank ->
            Machine.List.iter (addresses target addr len) ~f:(fun addr ->
                Mems.get addr
                >>= input (S.Input.ptr bank addr)
                >>= Mems.set addr)
    end in
    primus t (module Symbolize)

  let formula t place =
    Taint.checked t place;
    let result = ref [] in
    let module Formula (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Env = Primus.Env.Make (Machine)
      module Mems = Primus.Memory.Make (Machine)
      module Executor = S.Executor (Machine)

      let formula x =
        Executor.value x >>| Option.map ~f:(Format.asprintf "%a" S.SMT.pp_expr)

      let init () =
        Machine.gets Project.target >>= fun target ->
        (match place with
          | Reg name ->
              Env.get (Taint.var target name) >>= formula >>| List.return
          | Mem (addr, len) ->
              Machine.List.map (addresses target addr len) ~f:(fun addr ->
                  Mems.get addr >>= formula))
        >>| fun xs -> result := xs
    end in
    primus t (module Formula);
    !result

  let solve ?timeout t =
    let result = ref None in
    let module Solve (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Executor = S.Executor (Machine)
      module Constraints = S.Context.Make (Machine)

      let init () =
        Constraints.get S.Context.Scope.user >>= fun user ->
        Constraints.get S.Context.Scope.path >>= fun path ->
        Executor.inputs >>| fun inputs ->
        result :=
          S.SMT.check ?timeout (Set.to_list (Set.union user path))
          |> Option.map ~f:(model (Seq.to_list inputs))
    end in
    primus t (module Solve);
    !result

  let on_branch t f =
    let module Observe (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Eval = Primus.Interpreter.Make (Machine)
      module Value = Primus.Value.Make (Machine)
      module Executor = S.Executor (Machine)
      module Constraints = S.Context.Make (Machine)

      (* the observers, that come later, run first, so the constraints of
         the path don't have the condition yet *)
      let decided cond =
        Executor.value cond >>= function
        | None -> Machine.return ()
        | Some x ->
            let taken = not (Value.is_zero cond) in
            Eval.pc >>= fun pc ->
            Constraints.get S.Context.Scope.user >>= fun user ->
            Constraints.get S.Context.Scope.path >>= fun path ->
            Executor.inputs >>| fun inputs ->
            f t
              {
                addr = to_int64 pc;
                taken;
                condition = Format.asprintf "%a" S.SMT.pp_expr x;
                formula = S.SMT.formula ~refute:(not taken) x;
                path = Set.to_list (Set.union user path);
                inputs = Seq.to_list inputs;
              }

      let init () = Primus.Interpreter.eval_cond >>> decided
    end in
    primus t (module Observe)

  let addr b = b.addr
  let taken b = b.taken
  let condition b = b.condition

  let flip ?timeout b =
    S.SMT.check ?timeout (S.SMT.inverse b.formula :: b.path)
    |> Option.map ~f:(model b.inputs)
end
