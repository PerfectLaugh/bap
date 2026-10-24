open Core
open Bap_core_theory
open Bap.Std
open Bap_c.Std
open Format
open Bap_primus_types
include Self ()

module Primus = struct
  module Env = Bap_primus_env
  module Linker = Bap_primus_linker
  module Machine = Bap_primus_machine
  module Memory = Bap_primus_memory
  module Observation = Bap_primus_observation
  module State = Bap_primus_state
  module Value = Bap_primus_value
end

open Primus

module Time = struct
  include Int

  let clocks = Fn.id
  let of_clocks = of_int
end

open Bap_primus_sexp

let clock, tick =
  Observation.provide ~inspect:Time.sexp_of_t "clock"
    ~desc:"Occurs on each clock (operation) of the interpreter."

let memory_switch, switching_memory =
  let inspect = Primus.Memory.Descriptor.sexp_of_t in
  Observation.provide ~inspect "memory-switch"
    ~desc:"Occurs when the memory bank is switched."

let enter_term, term_entered =
  Observation.provide ~inspect:sexp_of_tid "enter-term"
    ~desc:"Occurs before the given term."

let leave_term, term_left =
  Observation.provide ~inspect:sexp_of_tid "leave-term"
    ~desc:"Occurs after the given term is evaluated."

let enter_pos, pos_entered =
  Observation.provide ~inspect:Pos.sexp_of_t "enter-pos"
    ~desc:"Occurs before the given position is evaluated."

let leave_pos, pos_left =
  Observation.provide ~inspect:Pos.sexp_of_t "leave-pos"
    ~desc:"Occurs after the given position is evaluated."

let sexp_of_term term = sexp_of_tid (Term.tid term)

let enter_sub, sub_entered =
  Observation.provide ~inspect:sexp_of_term "enter-sub"
    ~desc:"Occurs before the given term is evaluated."

let enter_arg, arg_entered =
  Observation.provide ~inspect:sexp_of_term "enter-arg"
    ~desc:"Occurs before the given term is evaluated."

let enter_blk, blk_entered =
  Observation.provide ~inspect:sexp_of_term "enter-blk"
    ~desc:"Occurs before the given term is evaluated."

let enter_phi, phi_entered =
  Observation.provide ~inspect:sexp_of_term "enter-phi"
    ~desc:"Occurs before the given term is evaluated."

let enter_def, def_entered =
  Observation.provide ~inspect:sexp_of_term "enter-def"
    ~desc:"Occurs before the given term is evaluated."

let enter_jmp, jmp_entered =
  Observation.provide ~inspect:sexp_of_term "enter-jmp"
    ~desc:"Occurs before the given term is evaluated."

let enter_top, top_entered =
  Observation.provide ~inspect:sexp_of_term "enter-top"
    ~desc:"Occurs before the given term is evaluated."

let leave_sub, sub_left =
  Observation.provide ~inspect:sexp_of_term "leave-sub"
    ~desc:"Occurs after the given term is evaluated."

let leave_arg, arg_left =
  Observation.provide ~inspect:sexp_of_term "leave-arg"
    ~desc:"Occurs after the given term is evaluated."

let leave_blk, blk_left =
  Observation.provide ~inspect:sexp_of_term "leave-blk"
    ~desc:"Occurs after the given term is evaluated."

let leave_phi, phi_left =
  Observation.provide ~inspect:sexp_of_term "leave-phi"
    ~desc:"Occurs after the given term is evaluated."

let leave_def, def_left =
  Observation.provide ~inspect:sexp_of_term "leave-def"
    ~desc:"Occurs after the given term is evaluated."

let leave_jmp, jmp_left =
  Observation.provide ~inspect:sexp_of_term "leave-jmp"
    ~desc:"Occurs after the given term is evaluated."

let leave_top, top_left =
  Observation.provide ~inspect:sexp_of_term "leave-top"
    ~desc:"Occurs after the given term is evaluated."

let enter_exp, exp_entered =
  Observation.provide ~inspect:sexp_of_exp "enter-exp"
    ~desc:"Occurs before the given exp is evaluated."

let leave_exp, exp_left =
  Observation.provide ~inspect:sexp_of_exp "leave-exp"
    ~desc:"Occurs after the given exp is evaluated."

let pc_change, pc_changed =
  Observation.provide ~inspect:sexp_of_word "pc-changed"
    ~desc:"Occurs after the program counter is changed."

(* the addresses, at which the executors, that run the code outside of
   the interpreter, stop and tell the address with [Make.set_pc], which
   are of the system, i.e., of all its machines, but not of the other
   systems, that run in the same process, e.g., the emulators of a
   script *)
module Stops = struct
  type t = { addrs : Set.M(Addr).t; stepping : bool; version : int }

  let state =
    Primus.Machine.State.declare ~uuid:"5e0d1a3c-9b47-4f6e-8d21-c7a4f3b9e016"
      ~name:"interpreter-stops" (fun _ ->
        { addrs = Set.empty (module Addr); stepping = false; version = 0 })

  module Make (Machine : Machine) = struct
    open Machine.Syntax

    let get = Machine.Global.get state

    let update f =
      Machine.Global.update state ~f:(fun s ->
          { (f s) with version = s.version + 1 })

    let add addr = update (fun s -> { s with addrs = Set.add s.addrs addr })

    let remove addr =
      update (fun s -> { s with addrs = Set.remove s.addrs addr })

    let mem addr = get >>| fun s -> Set.mem s.addrs addr
    let to_list = get >>| fun s -> Set.to_list s.addrs
    let set_stepping x = update (fun s -> { s with stepping = x })
    let stepping = get >>| fun s -> s.stepping
    let version = get >>| fun s -> s.version
  end
end

let stop_reached, reached_stop =
  Observation.provide ~inspect:sexp_of_word "stop-reached"
    ~desc:
      "Occurs after the program counter is changed to an address, at which the \
       machines stop, or to every address, while they are stepping, see \
       [Stops]."

let halting, will_halt =
  Observation.provide ~inspect:sexp_of_unit "halting"
    ~desc:"Occurs before the halt operation is posted."

let exited, will_exit =
  Observation.provide ~inspect:sexp_of_value "exited"
    ~desc:"Occurs when the program exits with the code."

let division_by_zero, will_divide_by_zero =
  Observation.provide ~inspect:sexp_of_unit "division-by-zero"
    ~desc:"Occurs before the division by zero happens."

let cfi_violation, cfi_will_diverge =
  Observation.provide ~inspect:sexp_of_word "cfi-violation"
    ~desc:"Occurs before the control flow violation is commited."

let segfault, will_segfault =
  Observation.provide ~inspect:sexp_of_word "segfault"
    ~desc:"Occurs just before the segmentation fault."

let pagefault, page_fail =
  Observation.provide ~inspect:sexp_of_word "pagefault"
    ~desc:"Occurs on pagefault."

let interrupt, will_interrupt =
  Observation.provide ~inspect:sexp_of_int "interrupt"
    ~desc:"Occurs before an interrupt."

let sexp_of_insn insn = Sexp.Atom (Insn.to_string insn)

let loading, on_loading =
  Observation.provide ~inspect:sexp_of_value "loading"
    ~desc:"Occurs just before the given address is dereferenced."

let loaded, on_loaded =
  Observation.provide ~inspect:sexp_of_values "loaded"
    ~desc:"Occurs after the given address is read."

let storing, on_storing =
  Observation.provide ~inspect:sexp_of_value "storing"
    ~desc:"Occurs before the value is stored at the address."

let stored, on_stored =
  Observation.provide ~inspect:sexp_of_values "stored"
    ~desc:"Occurs after the value is stored at the address."

let reading, on_reading =
  Observation.provide ~inspect:sexp_of_var "reading"
    ~desc:"Occurs before the given variable is read."

let read, on_read =
  Observation.provide ~inspect:sexp_of_binding "read"
    ~desc:"Occurs after the given variable is evaluated to the value."

let writing, on_writing =
  Observation.provide ~inspect:sexp_of_var "writing"
    ~desc:"Occurs before the value is assigned to the variable."

let written, on_written =
  Observation.provide ~inspect:sexp_of_binding "written"
    ~desc:"Occurs after the value is assigned to the variable."

let undefined, on_undefined =
  Observation.provide ~inspect:sexp_of_value "undefined"
    ~desc:"Occurs when an undefined value is created."

let jumping, will_jump =
  Observation.provide ~inspect:sexp_of_values "jumping"
    ~desc:"Occurs before the jump to the given destination."

let eval_cond, on_cond =
  Observation.provide ~inspect:sexp_of_value "eval-cond"
    ~desc:"Occurs when the jump condition is evaluated."

let results r op = Sexp.List [ op; sexp_of_value r ]

let sexp_of_binop ((op, x, y), r) =
  results r
  @@ sexps [ Bil.string_of_binop op; string_of_value x; string_of_value y ]

let sexp_of_unop ((op, x), r) =
  results r @@ sexps [ Bil.string_of_unop op; string_of_value x ]

let sexp_of_cast ((t, s, v), r) =
  results r
  @@ sexps [ Bil.string_of_cast t; string_of_int s; string_of_value v ]

let sexp_of_extract ((hi, lo, x), r) =
  results r @@ sexps [ string_of_int hi; string_of_int lo; string_of_value x ]

let sexp_of_concat ((x, y), r) =
  results r @@ sexps [ string_of_value x; string_of_value y ]

let sexp_of_ite ((cond, yes, no), r) =
  results r
  @@ sexps [ string_of_value cond; string_of_value yes; string_of_value no ]

let binop, on_binop =
  Observation.provide ~inspect:sexp_of_binop "binop"
    ~desc:"Occurs on each binary operation."

let unop, on_unop =
  Observation.provide ~inspect:sexp_of_unop "unop"
    ~desc:"Occurs on each unary operation."

let cast, on_cast =
  Observation.provide ~inspect:sexp_of_cast "cast" ~desc:"Occurs on each cast."

let extract, on_extract =
  Observation.provide ~inspect:sexp_of_extract "extract"
    ~desc:"Occurs on each extract operation."

let concat, on_concat =
  Observation.provide ~inspect:sexp_of_concat "concat"
    ~desc:"Occurs on each concat operation."

let const, on_const =
  Observation.provide ~inspect:sexp_of_value "const"
    ~desc:"Occurs on each constant."

let ite, on_ite =
  Observation.provide ~inspect:sexp_of_ite "ite"
    ~desc:"Occurs on each ite expression."

let sexp_of_name = function
  | `symbol name -> Sexp.Atom name
  | `tid tid -> Sexp.Atom (Tid.name tid)
  | `addr addr -> Sexp.Atom (Addr.string_of_value addr)

type scope = { stack : (var * value) list; bound : int Var.Map.t }

type state = {
  time : Time.t;
  addr : addr;
  curr : pos;
  lets : scope; (* lexical context *)
  prompts : tid list;
  patched : (addr * addr) option;
      (* the least and the greatest addresses of the code, that the
         program stored to, while the block runs, see [blk_body] *)
}

let sexp_of_state { curr } = Pos.sexp_of_t curr
let null proj = Addr.code_addr (Project.target proj) Bitvec.zero
let empty_scope = { stack = []; bound = Var.Map.empty }

let state =
  Primus.Machine.State.declare ~uuid:"14a17161-173b-46da-9e95-7819104cc220"
    ~name:"interpreter" ~inspect:sexp_of_state (fun proj ->
      let prog = Project.program proj in
      Pos.
        {
          time = Time.zero;
          addr = null proj;
          curr = Top { me = prog; up = Nil };
          lets = empty_scope;
          prompts = [];
          patched = None;
        })

type exn += Halt
type exn += Division_by_zero
type exn += Segmentation_fault of addr
type exn += Cfi_violation of addr
type exn += Runtime_error of string

let () =
  Exn.add_printer (function
    | Runtime_error msg ->
        Some (sprintf "Primus interpreter runtime error: %s" msg)
    | Halt -> Some "Halt"
    | Segmentation_fault x ->
        Some (asprintf "Segmentation fault at %a" Addr.pp_hex x)
    | Division_by_zero -> Some "Division by zero"
    | Cfi_violation where ->
        Some (asprintf "CFI violation at %a" Addr.pp_hex where)
    | _ -> None)

let division_by_zero_handler = "__primus_division_by_zero_handler"
let pagefault_handler = "__primus_pagefault_handler"
let cfi_violation_handler = "__primus_cfi_violation_handler"

module Make (Machine : Machine) = struct
  open Machine.Syntax
  open Machine.Let
  module Memory = Primus.Memory.Make (Machine)
  module Env = Primus.Env.Make (Machine)
  module Code = Linker.Make (Machine)
  module Value = Primus.Value.Make (Machine)

  type 'a m = 'a Machine.t

  let ( !! ) = Machine.Observation.make
  let post = Machine.Observation.post

  let failf fmt =
    Format.ksprintf (fun msg -> fun () -> Machine.raise (Runtime_error msg)) fmt

  let value = Value.of_word

  let word_of_type = function
    | Type.Imm t -> Word.zero t
    | Type.Mem _ | Type.Unk -> Word.b0

  let undefined t =
    value (word_of_type t) >>= fun r ->
    !!on_undefined r >>| fun () -> r

  let get v =
    !!on_reading v >>= fun () ->
    Env.get v >>= fun r ->
    post on_read ~f:(fun k -> k (v, r)) >>| fun () -> r

  let call_when_provided name =
    Code.is_linked (`symbol name) >>= fun provided ->
    if provided then Code.exec (`symbol name) >>| fun () -> true
    else Machine.return false

  let tick =
    Machine.Local.get state >>= fun s ->
    !!tick s.time >>= fun () ->
    Machine.Local.put state { s with time = Time.succ s.time }

  let unop op x =
    value (Bil.Apply.unop op x.value) >>= fun r ->
    tick >>= fun () ->
    post on_unop ~f:(fun k -> k ((op, x), r)) >>| fun () -> r

  let cast t s x =
    value (Bil.Apply.cast t s x.value) >>= fun r ->
    post on_cast ~f:(fun k -> k ((t, s, x), r)) >>| fun () -> r

  let concat x y =
    value (Word.concat x.value y.value) >>= fun r ->
    post on_concat ~f:(fun k -> k ((x, y), r)) >>| fun () -> r

  let extract ~hi ~lo x =
    value (Word.extract_exn ~hi ~lo x.value) >>= fun r ->
    post on_extract ~f:(fun k -> k ((hi, lo, x), r)) >>| fun () -> r

  let coerce s x =
    if Value.bitwidth x <> s then extract ~hi:(s - 1) ~lo:0 x
    else Machine.return x

  let binop op x y =
    match op with
    | (Bil.DIVIDE | Bil.SDIVIDE | Bil.MOD | Bil.SMOD) when Word.is_zero y.value
      ->
        !!will_divide_by_zero () >>= fun () ->
        call_when_provided division_by_zero_handler >>= fun called ->
        if called then undefined (Type.Imm (Word.bitwidth x.value))
        else Machine.raise Division_by_zero
    | _ ->
        let s = max (Value.bitwidth x) (Value.bitwidth y) in
        coerce s x >>= fun x ->
        coerce s y >>= fun y ->
        value (Bil.Apply.binop op x.value y.value) >>= fun r ->
        tick >>= fun () ->
        post on_binop ~f:(fun k -> k ((op, x, y), r)) >>| fun () -> r

  let const c =
    value c >>= fun r ->
    !!on_const r >>| fun () -> r

  let set v x =
    !!on_writing v >>= fun () ->
    let x =
      match Var.typ v with
      | Unk | Mem _ -> Machine.return x
      | Imm m ->
          if Value.bitwidth x <> m then extract ~hi:(m - 1) ~lo:0 x
          else Machine.return x
    in
    x >>= fun x ->
    Env.set v x >>= fun () -> post on_written ~f:(fun k -> k (v, x))

  let trapped_memory_access access =
    Machine.catch access (function
      | Bap_primus_memory.Pagefault a ->
          !!page_fail a >>= fun () ->
          call_when_provided pagefault_handler >>= fun trapped ->
          if trapped then access
          else
            !!will_segfault a >>= fun () -> Machine.raise (Segmentation_fault a)
      | exn -> Machine.raise exn)

  let load_byte a =
    !!on_loading a >>= fun () ->
    trapped_memory_access (Memory.get a.value) >>= fun r ->
    tick >>= fun () ->
    post on_loaded ~f:(fun k -> k (a, r)) >>| fun () -> r

  let notify_load a x =
    !!on_loading a >>= fun () -> post on_loaded ~f:(fun k -> k (a, x))

  let notify_store a x =
    !!on_storing a >>= fun () -> post on_stored ~f:(fun k -> k (a, x))

  let store_byte a x =
    !!on_storing a >>= fun () ->
    trapped_memory_access (Memory.set a.value x) >>= fun () ->
    tick >>= fun () -> post on_stored ~f:(fun k -> k (a, x))

  let ite cond yes no =
    value (if Word.is_one cond.value then yes.value else no.value) >>= fun r ->
    post on_ite ~f:(fun k -> k ((cond, yes, no), r)) >>| fun () -> r

  let get_lexical scope v = List.Assoc.find_exn scope ~equal:Var.equal v

  let update_lexical f =
    Machine.Local.update state ~f:(fun s -> { s with lets = f s.lets })

  let push_lexical v x =
    update_lexical @@ fun s ->
    {
      stack = (v, x) :: s.stack;
      bound = Map.update s.bound v ~f:(function None -> 1 | Some n -> n + 1);
    }

  let pop_lexical v =
    update_lexical @@ fun s ->
    {
      stack = List.tl_exn s.stack;
      bound =
        Map.change s.bound v ~f:(function
          | None -> None
          | Some 1 -> None
          | Some n -> Some (n - 1));
    }

  let memory typ name =
    match typ with
    | Type.Mem (ks, vs) ->
        let ks = Size.in_bits ks and vs = Size.in_bits vs in
        Primus.Memory.Descriptor.create ~addr_size:ks ~data_size:vs name
    | _ as t -> failwithf "type error - load from %s:%a" name Type.pps t ()

  let rec memory_of_storage : exp -> _ = function
    | Var v -> memory (Var.typ v) (Var.name v)
    | Unknown (_, typ) -> memory typ "unknown"
    | Store (s, _, _, _, _) | Ite (_, s, _) | Let (_, _, s) ->
        memory_of_storage s
    | x -> failwithf "expression `%a' is no a storage" Exp.pps x ()

  let switch_memory m =
    let m = memory_of_storage m in
    Memory.memory >>= fun m' ->
    if Primus.Memory.Descriptor.equal m m' then Machine.return ()
    else !!switching_memory m >>= fun () -> Memory.switch m

  let time = Machine.Local.get state >>| fun s -> s.time

  let rec eval_exp x =
    let eval = function
      | Bil.Load (m, a, _, _) -> eval_load m a
      | Bil.Store (m, a, x, _, _) -> eval_store m a x
      | Bil.BinOp (op, x, y) -> eval_binop op x y
      | Bil.UnOp (op, x) -> eval_unop op x
      | Bil.Var v -> eval_var v
      | Bil.Int c -> eval_int c
      | Bil.Cast (t, s, x) -> eval_cast t s x
      | Bil.Unknown (x, typ) -> eval_unknown x typ
      | Bil.Extract (hi, lo, x) -> eval_extract hi lo x
      | Bil.Concat (x, y) -> eval_concat x y
      | Bil.Ite (cond, yes, no) -> eval_ite cond yes no
      | Bil.Let (v, x, y) -> eval_let v x y
    in
    !!exp_entered x >>= fun () ->
    eval x >>= fun r ->
    !!exp_left x >>| fun () -> r

  and eval_let v x y =
    eval_exp x >>= fun x ->
    push_lexical v x >>= fun () ->
    eval_exp y >>= fun r ->
    pop_lexical v >>| fun () -> r

  and eval_ite cond yes no =
    eval_exp yes >>= fun yes ->
    eval_exp no >>= fun no ->
    eval_exp cond >>= fun cond -> ite cond yes no

  and eval_load m a =
    eval_exp a >>= fun a ->
    switch_memory m >>= fun () ->
    eval_storage m >>= fun () -> load_byte a

  and eval_store m a x =
    eval_exp a >>= fun a ->
    eval_exp x >>= fun x ->
    switch_memory m >>= fun () ->
    eval_storage m >>= fun () ->
    store_byte a x >>| fun () -> a

  and eval_binop op x y =
    eval_exp x >>= fun x ->
    eval_exp y >>= fun y -> binop op x y

  and eval_unop op x = eval_exp x >>= fun x -> unop op x

  and eval_var v =
    Machine.Local.get state >>= fun { lets } ->
    if Map.mem lets.bound v then Machine.return (get_lexical lets.stack v)
    else get v

  and eval_int = const
  and eval_cast t s x = eval_exp x >>= fun x -> cast t s x
  and eval_unknown _x t = undefined t
  and eval_extract hi lo x = eval_exp x >>= fun x -> extract ~hi ~lo x

  and eval_concat x y =
    eval_exp x >>= fun x ->
    eval_exp y >>= fun y -> concat x y

  and eval_storage = function
    | Var _ -> Machine.return ()
    | mem -> Machine.void (eval_exp mem)

  let eval_exp x = eval_exp (Exp.simpl (Exp.normalize x))
  let exp = eval_exp

  let mem =
    Machine.gets Project.target >>| fun t -> Var.reify (Theory.Target.data t)

  let succ x = Value.one (Value.bitwidth x) >>= fun one -> binop PLUS x one

  let rec do_load a e s =
    load_byte a >>= fun v ->
    if s = 8 then Machine.return v
    else
      succ a >>= fun a ->
      do_load a e (s - 8) >>= fun u ->
      match e with LittleEndian -> concat u v | BigEndian -> concat v u

  let load a e s = do_load a e (Size.in_bits s)

  let rec do_store a x s hd tl =
    cast hd 8 x >>= fun b ->
    store_byte a b >>= fun () ->
    if s = 8 then Machine.return ()
    else
      succ a >>= fun a ->
      cast tl (s - 8) x >>= fun x -> do_store a x (s - 8) hd tl

  let store a x e s =
    let open Bil.Types in
    let s = Size.in_bits s in
    let x =
      if Value.bitwidth x <> s then extract ~hi:(s - 1) ~lo:0 x
      else Machine.return x
    in
    x >>= fun x ->
    match e with
    | LittleEndian -> do_store a x s LOW HIGH
    | BigEndian -> do_store a x s HIGH LOW

  let infer x =
    match Type.infer x with
    | Ok (Imm m) -> Machine.return m
    | _ -> failf "ill-typed expression, expected a bitvector: %a" Exp.pps x ()

  let rec assign rhs x =
    match (rhs : exp) with
    | Var v -> set v x
    | Ite (c, yes, nay) ->
        let* c = exp c in
        if Value.is_one c then assign yes x else assign nay x
    | Cast (LOW, part, v) ->
        let* width = infer v in
        let* y = exp v in
        let* hi = cast HIGH (width - part) y in
        let* x = concat hi x in
        assign v x
    | Cast (HIGH, part, v) ->
        let* width = infer v in
        let* y = exp v in
        let* lo = cast LOW (width - part) y in
        let* x = concat x lo in
        assign v x
    | Cast (_widen, _, v) ->
        let* part = infer v in
        let* x = cast LOW part x in
        assign v x
    | Extract (hi, lo, v) ->
        let* size = infer v in
        let* y = exp v in
        let* hi = cast HIGH (size - hi - 1) y in
        let* lo = cast LOW lo y in
        let* x = concat hi x in
        let* x = concat x lo in
        assign v x
    | Load (mem, addr, endian, size) ->
        exp mem >>= fun _ ->
        exp addr >>= fun addr -> store addr x endian size
    | Concat (high, rest) ->
        let* size = infer high in
        let* hix = cast HIGH size x in
        let* lox = cast LOW (Value.bitwidth x - size) x in
        Machine.sequence [ assign high hix; assign rest lox ]
    | exp -> failf "not an lvalue: %a" Exp.pps exp ()

  (* the observers of the stops, e.g., a debugger, see only them, so
     that the executors, that run the code outside of the interpreter,
     e.g., Unicorn, stop only at them, see [Stops] *)
  let changed addr =
    !!pc_changed addr >>= fun () ->
    Machine.Global.get Stops.state >>= fun { Stops.addrs; stepping; _ } ->
    if stepping || Set.mem addrs addr then !!reached_stop addr
    else Machine.return ()

  let update_pc t =
    match Term.get_attr t address with
    | None -> Machine.return ()
    | Some addr ->
        Machine.Local.get state >>= fun s ->
        Machine.Local.put state { s with addr } >>= fun () ->
        if Addr.(s.addr <> addr) then changed addr else Machine.return ()

  let enter cls curr t =
    !!pos_entered curr >>= fun () ->
    !!term_entered (Term.tid t) >>= fun () ->
    Term.switch cls t ~program:!!top_entered ~sub:!!sub_entered
      ~arg:!!arg_entered ~blk:!!blk_entered ~phi:!!phi_entered
      ~def:!!def_entered ~jmp:!!jmp_entered

  let leave cls curr t =
    Term.switch cls t ~program:!!top_left ~sub:!!sub_left ~arg:!!arg_left
      ~blk:!!blk_left ~phi:!!phi_left ~def:!!def_left ~jmp:!!jmp_left
    >>= fun () ->
    !!term_left (Term.tid t) >>= fun () -> !!pos_left curr

  let branch cnd yes no =
    Value.zero (Value.bitwidth cnd) >>= fun zero ->
    binop Bil.EQ cnd zero >>= fun is_zero ->
    !!on_cond is_zero >>= fun () -> if Value.is_one is_zero then no else yes

  let rec repeat cnd body =
    cnd >>= fun x ->
    Value.zero (Value.bitwidth x) >>= fun zero ->
    binop Bil.EQ x zero >>= fun stop ->
    !!on_cond stop >>= fun () ->
    if Value.is_one stop then Machine.return stop
    else body >>= fun _ -> repeat cnd body

  let term return cls f x t =
    Machine.Local.get state >>= fun s ->
    match Pos.next s.curr cls t with
    | Error err -> Machine.raise err
    | Ok curr ->
        update_pc t >>= fun () ->
        Machine.Local.update state ~f:(fun s -> { s with curr }) >>= fun () ->
        enter cls curr t >>= fun () ->
        f x t >>= fun r ->
        leave cls curr t >>= fun () -> return r

  let normal = Machine.return
  let halt = !!will_halt () >>= fun () -> Machine.raise Halt
  let exit code = !!will_exit code >>= fun () -> halt
  let ( := ) v x = eval_exp x >>= set v
  let def () t = Def.lhs t := Def.rhs t
  let def = term normal def_t def ()

  let will_jump_to_tid cond dst =
    Code.resolve_addr (`tid dst) >>= function
    | None -> Machine.return ()
    | Some addr ->
        Value.of_word addr >>= fun addr ->
        tick >>= fun () -> post will_jump ~f:(fun k -> k (cond, addr))

  let exec_to_prompt dst =
    Machine.Local.get state >>= function
    | { prompts = p :: _ } when Tid.equal p dst -> Machine.return ()
    | _ -> Code.exec (`tid dst)

  let label cond : label -> _ = function
    | Direct dst -> will_jump_to_tid cond dst >>= fun () -> exec_to_prompt dst
    | Indirect x -> (
        eval_exp x >>= fun ({ value } as dst) ->
        tick >>= fun () ->
        post will_jump ~f:(fun k -> k (cond, dst)) >>= fun () ->
        Code.resolve_tid (`addr value) >>= function
        | None -> Code.exec (`addr value)
        | Some dst -> exec_to_prompt dst)

  let resolve_return call =
    match Call.return call with
    | None -> Machine.return None
    | Some (Direct dst) -> Machine.return (Some dst)
    | Some (Indirect dst) ->
        eval_exp dst >>= fun { value = dst } -> Code.resolve_tid (`addr dst)

  let push_prompt dst =
    match dst with
    | None -> Machine.return ()
    | Some dst ->
        Machine.Local.update state ~f:(fun s ->
            { s with prompts = dst :: s.prompts })

  let pop_prompt =
    Machine.Local.update state ~f:(function
      | { prompts = [] } as s -> s
      | { prompts = _ :: prompts } as s -> { s with prompts })

  let trap_cfi_violation callsite =
    !!cfi_will_diverge callsite >>= fun () ->
    call_when_provided cfi_violation_handler >>= function
    | true -> Machine.return ()
    | false -> Machine.raise (Cfi_violation callsite)

  let call cond call =
    Machine.Local.get state >>= fun { addr = callsite } ->
    resolve_return call >>= function
    (* a call that doesn't return is a tail call, so that a loop of
       them, e.g., a PLT entry jumping to itself, runs in constant space *)
    | None -> label cond (Call.target call)
    | ret -> (
        push_prompt ret >>= fun () ->
        label cond (Call.target call) >>= fun () ->
        Machine.Local.get state >>= function
        | { prompts = [] } -> Machine.return ()
        | { prompts = p :: _ } -> (
            match ret with
            | None -> Machine.return ()
            | Some p' when Tid.(p <> p') ->
                trap_cfi_violation callsite >>= fun () ->
                pop_prompt >>= fun () -> label cond (Direct p')
            | Some p -> pop_prompt >>= fun () -> label cond (Direct p)))

  let goto cond c = label cond c
  let interrupt n = !!will_interrupt n

  let jump cond t =
    match Jmp.kind t with
    | Ret dst -> label cond dst
    | Call c -> call cond c
    | Goto l -> goto cond l
    | Int (n, r) -> interrupt n >>= fun () -> Code.exec (`tid r)

  type constr = Init | Conj of Value.t | Disj of Value.t * Jmp.t

  let jmp constr t =
    eval_exp (Jmp.cond t) >>= fun v ->
    match (constr, Word.is_one v.value) with
    | Init, true -> !!on_cond v >>= fun () -> Machine.return (Disj (v, t))
    | Init, false ->
        !!on_cond v >>= fun () ->
        unop Bil.NOT v >>| fun u -> Conj u
    | Conj u, false ->
        binop Bil.AND u v >>= !!on_cond >>= fun () ->
        unop Bil.NOT v >>= fun v ->
        binop Bil.AND u v >>| fun w -> Conj w
    | Conj u, true ->
        binop Bil.AND u v >>= fun w ->
        !!on_cond w >>| fun () -> Disj (w, t)
    | Disj (u, t), _ ->
        unop Bil.NOT u >>= fun p ->
        binop Bil.AND p v >>= !!on_cond >>= fun () ->
        binop Bil.OR u v >>| fun w -> Disj (w, t)

  let jmp = term normal jmp_t jmp

  let code_stored addr =
    Machine.Local.update state ~f:(fun s ->
        match s.patched with
        | None -> { s with patched = Some (addr, addr) }
        | Some (lo, hi) ->
            { s with patched = Some (Addr.min lo addr, Addr.max hi addr) })

  (* the address of the instruction of the term [t], if it is after the
     instruction at [last], that ran, and its code may be changed, as the
     program stored to its bytes, before the next instruction, which is
     at the least address after it of the terms, that are yet to run, see
     [rest], or at most the size of an instruction after the last
     instruction of the block, at [hi], and if no term, that is yet to
     run, is of an instruction before it, e.g., the branch of MIPS, whose
     delay slot it is, or the delay slot, that ran before its branch *)
  let patched ~hi last rest t =
    match Term.get_attr t address with
    | Some addr when Option.for_all last ~f:(fun last -> Addr.(last < addr))
      -> (
        Machine.Local.get state >>| fun s ->
        match (s.patched, hi) with
        | Some (lo, up), Some hi when Addr.(addr <= up) ->
            let rest = rest () in
            let next =
              List.filter rest ~f:(fun a -> Addr.(addr < a))
              |> List.min_elt ~compare:Addr.compare
              |> Option.value ~default:Word.(hi ++ Bap_primus_lift.max_size)
            in
            if
              Addr.(lo < next)
              && List.for_all rest ~f:(fun a -> Addr.(addr <= a))
            then Some addr
            else None
        | _ -> None)
    | _ -> Machine.return None

  (* the instructions of the block run, unless the program changes the
     code of the next one, e.g., as the block stores to it, which then
     runs, as it is in the memory, from its address, see
     [Bap_primus_dynamic], as the jump to it does *)
  let blk_body () t =
    let addr_of t = Term.get_attr t address in
    let defs = Seq.to_list (Term.enum def_t t) in
    let jumps = Seq.to_list (Term.enum jmp_t t) in
    let jmp_addrs = List.filter_map jumps ~f:addr_of in
    let hi =
      List.max_elt ~compare:Addr.compare
        (jmp_addrs @ List.filter_map defs ~f:addr_of)
    in
    let from addr = Code.exec (`addr addr) >>| fun () -> Init in
    let rec run last = function
      | [] -> (
          match jumps with
          | [] -> jmps ()
          | jmp :: _ -> (
              patched ~hi last (fun () -> jmp_addrs) jmp >>= function
              | Some addr -> from addr
              | None -> jmps ()))
      | d :: ds -> (
          let rest () = List.filter_map ds ~f:addr_of @ jmp_addrs in
          patched ~hi last rest d >>= function
          | Some addr -> from addr
          | None ->
              def d >>= fun () ->
              let last =
                match addr_of d with Some addr -> Some addr | None -> last
              in
              run last ds)
    and jmps () = Machine.List.fold ~init:Init jumps ~f:jmp in
    Machine.Local.update state ~f:(fun s -> { s with patched = None })
    >>= fun () -> run None defs

  let finish = function
    | Init | Conj _ -> Machine.return () (* return from sub *)
    | Disj (cond, code) -> jump cond code

  let blk : blk term -> unit m = term finish blk_t blk_body ()

  (* the instruction, which is not a part of the program, is a part of
     the subroutine, that runs it *)
  let insn_sub = Sub.create ~name:"insn" ()

  let enter_insn =
    Machine.Local.update state ~f:(fun s ->
        match s.curr with
        | Top up -> { s with curr = Sub { me = insn_sub; up } }
        | Blk { up } | Arg { up } -> { s with curr = Sub up }
        (* the terms of the instruction, that ran, e.g., its last def *)
        | Def { up = { up; _ }; _ }
        | Jmp { up = { up; _ }; _ }
        | Phi { up = { up; _ }; _ } ->
            { s with curr = Sub up }
        | Sub _ -> s)

  (* the destination of the jump, that leaves the instruction *)
  let leave_insn cond dst =
    tick >>= fun () ->
    post will_jump ~f:(fun k -> k (cond, dst)) >>| fun () -> dst

  (* the instruction, whose jumps are not taken, falls through, and the
     jump to the next instruction is taken, if they are conditional, as
     the program has it *)
  let rec step_from ~next blks constr = function
    | [] -> (
        match constr with
        | Conj u -> Value.of_word next >>= leave_insn u
        | Init | Disj _ -> Value.of_word next)
    | b :: rest -> (
        enter_insn >>= fun () ->
        term Machine.return blk_t blk_body () b >>= function
        | (Init | Conj _) as c ->
            let c = match (c, constr) with Init, c -> c | c, _ -> c in
            step_from ~next blks c rest
        | Disj (cond, t) -> (
            let inside dst =
              match
                List.drop_while blks ~f:(fun b ->
                    not (Tid.equal (Term.tid b) dst))
              with
              | [] -> None
              | blks -> Some blks
            in
            (* the code of the label without an address, e.g., of an
               intrinsic, runs, by its name, as the jump of the program
               runs it, after which the instruction continues at the
               return of the call, if it is in the instruction *)
            let exec dst ~return =
              let code =
                match String.chop_prefix (Tid.name dst) ~prefix:"@" with
                | Some name -> `symbol name
                | None -> `tid dst
              in
              Code.exec code >>= fun () ->
              match Option.bind return ~f:inside with
              | Some blks' -> step_from ~next blks Init blks'
              | None -> Value.of_word next
            in
            let goto ?return : label -> _ = function
              | Indirect x -> eval_exp x >>= leave_insn cond
              | Direct dst -> (
                  match inside dst with
                  | Some blks' -> step_from ~next blks Init blks'
                  | None -> (
                      Code.resolve_addr (`tid dst) >>= function
                      | Some addr -> Value.of_word addr >>= leave_insn cond
                      | None -> (
                          (* the label of the program, e.g., of a function,
                             that a stub replaced, which is linked without
                             its address, is jumped to, as the stub runs,
                             when the machine reaches it *)
                          Machine.knowledge
                            (Bap_knowledge.Knowledge.collect
                               Bap_core_theory.Theory.Label.addr dst)
                          >>= function
                          | Some addr ->
                              Value.of_word
                                (Word.create addr (Word.bitwidth next))
                              >>= leave_insn cond
                          | None -> exec dst ~return)))
            in
            match Jmp.kind t with
            | Goto l | Ret l -> goto l
            | Call c ->
                let return =
                  match Call.return c with
                  | Some (Direct r) -> Some r
                  | _ -> None
                in
                goto ?return (Call.target c)
            | Int (n, r) -> (
                interrupt n >>= fun () ->
                match inside r with
                | Some blks' -> step_from ~next blks Init blks'
                | None -> Value.of_word next)))

  (* the position after the instruction is not a block, e.g., of an
     empty block, from which no term is entered *)
  let step ~next blks =
    step_from ~next blks Init blks >>= fun dst ->
    enter_insn >>| fun () -> dst

  let continue_at dst =
    Code.resolve_tid (`addr dst) >>= function
    | None -> Code.exec (`addr dst)
    | Some dst -> exec_to_prompt dst

  let call_at dst ~return =
    push_prompt (Some return) >>= fun () ->
    continue_at dst >>= fun () ->
    Machine.Local.get state >>= function
    | { prompts = p :: _ } when Tid.equal p return -> pop_prompt
    | _ -> Machine.return ()

  let arg_def () t =
    match Arg.intent t with
    | None | Some (In | Both) -> Arg.lhs t := Arg.rhs t
    | _ -> Machine.return ()

  let arg_def = term normal arg_t arg_def ()

  let arg_use () t =
    match Arg.intent t with
    | Some Out -> Arg.lhs t := Arg.rhs t
    | _ -> Machine.return ()

  let arg_use = term normal arg_t arg_use ()
  let is_out_intent x = match Arg.intent x with Some Out -> true | _ -> false
  let get_arg t = exp (Arg.rhs t)

  let get_args ~input sub =
    Term.enum arg_t sub
    |> Seq.filter ~f:(fun x ->
        match input with
        | true -> not @@ is_out_intent x
        | false -> is_out_intent x)
    |> Machine.Seq.map ~f:get_arg

  let iter_args t f = Machine.Seq.iter (Term.enum arg_t t) ~f

  let sub () t =
    match Term.first blk_t t with
    | None -> Machine.return ()
    | Some entry ->
        let name = Sub.name t in
        iter_args t arg_def >>= fun () ->
        get_args ~input:true t >>| Seq.to_list_rev >>= fun inputs ->
        post Linker.Trace.call_entered ~f:(fun k -> k (name, List.rev inputs))
        >>= fun () ->
        blk entry >>= fun () ->
        iter_args t arg_use >>= fun () ->
        post Linker.Trace.call_returned ~f:(fun k ->
            get_args ~input:false t >>| Seq.to_list >>= fun rets ->
            let args = List.rev_append inputs rets in
            k (name, args))

  let assume x = !!on_cond x
  let sub = term normal sub_t sub ()
  let pos = Machine.Local.get state >>| fun { curr } -> curr
  let pc = Machine.Local.get state >>| fun { addr } -> addr

  let set_pc addr =
    Machine.Local.update state ~f:(fun s -> { s with addr }) >>= fun () ->
    changed addr
end
