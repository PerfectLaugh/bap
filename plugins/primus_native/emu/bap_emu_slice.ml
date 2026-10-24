open Core
open Bap.Std
open Bap_core_theory

type location = Reg of string | Mem of int64 * int

type slice = {
  sites : int64 list;
  live : location list;
  calls : int64 list;
  complete : bool;
}

(* a byte of the memory, at a constant address, or in a slot of the
   frame, at the offset from a base register, the stack or the frame
   pointer, as the code addresses it *)
module Byte = struct
  module T = struct
    type t = Const of int64 | Slot of string * int64
    [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

(* the live, or the tainted, locations: the registers, by the names of
   their bases, the temporaries, and the bytes of the memory *)
type state = { regs : String.Set.t; bytes : Set.M(Byte).t }

let int64_of_word w = Bitvec.to_int64 (Word.to_bitvec w)
let name v = String.uppercase (Var.name (Var.base v))
let empty = { regs = String.Set.empty; bytes = Set.empty (module Byte) }

let union a b =
  { regs = Set.union a.regs b.regs; bytes = Set.union a.bytes b.bytes }

let is_subset a ~of_ =
  Set.is_subset a.regs ~of_:of_.regs && Set.is_subset a.bytes ~of_:of_.bytes

let equal_state a b = is_subset a ~of_:b && is_subset b ~of_:a
let is_empty { regs; bytes } = Set.is_empty regs && Set.is_empty bytes

let range byte n =
  List.init n ~f:(fun i ->
      match byte with
      | Byte.Const a -> Byte.Const Int64.(a + of_int i)
      | Slot (b, off) -> Slot (b, Int64.(off + of_int i)))
  |> Set.of_list (module Byte)

let is_const = function Byte.Const _ -> true | Slot _ -> false

(* the bytes of the memory, that a function passes to its callees, and
   gets back, as the slots of its frame are its own *)
let consts s = { s with bytes = Set.filter s.bytes ~f:is_const }
let slots s = { s with bytes = Set.filter s.bytes ~f:(Fn.non is_const) }

(* the register of the target, by its name, or the one, that it is an
   alias of, e.g., R0 for X0 of AArch64, as the variables of BIR *)
let canonical target r =
  let r = String.uppercase r in
  let regs = Theory.Target.regs target in
  match
    Set.find regs ~f:(fun v ->
        String.equal (String.uppercase (Theory.Var.name v)) r)
  with
  | None -> r
  | Some v -> (
      match Theory.Target.unalias target v with
      | None -> r
      | Some origin -> (
          match Theory.Origin.cast_sub origin with
          | Some sub ->
              String.uppercase (Theory.Var.name (Theory.Origin.reg sub))
          | None -> r))

let of_locations target locations =
  List.fold locations ~init:empty ~f:(fun s -> function
    | Reg r -> { s with regs = Set.add s.regs (canonical target r) }
    | Mem (a, n) -> { s with bytes = Set.union s.bytes (range (Const a) n) })

(* the bytes at the constant addresses, coalesced, as the slots of the
   frame are of the function *)
let to_locations { regs; bytes } =
  let regs =
    Set.to_list regs
    |> List.filter ~f:(fun r -> not (String.is_prefix r ~prefix:"#"))
    |> List.map ~f:(fun r -> Reg r)
  in
  let ranges =
    Set.to_list bytes
    |> List.filter_map ~f:(function Byte.Const a -> Some a | Slot _ -> None)
    |> List.fold ~init:[] ~f:(fun acc a ->
        match acc with
        | (lo, n) :: rest when Int64.(lo + of_int n = a) -> (lo, n + 1) :: rest
        | _ -> (a, 1) :: acc)
    |> List.rev_map ~f:(fun (a, n) -> Mem (a, n))
  in
  regs @ ranges

(* the stack and the frame pointers of the target, by the names of their
   bases *)
let bases target =
  List.filter_map
    Theory.Role.Register.[ stack_pointer; frame_pointer ]
    ~f:(fun role ->
      Option.map (Theory.Target.reg target role) ~f:(fun v ->
          canonical target (Theory.Var.name v)))
  |> String.Set.of_list

(* the registers, that the C ABI of the target passes the arguments in,
   which the callees read, and returns the results in, which the callees
   define *)
let abi target =
  match Bap_c.Std.C.Abi.lookup target with
  | None -> (String.Set.empty, String.Set.empty)
  | Some abi ->
      let long = Bap_c.Std.C.Type.basic `slong in
      let proto : Bap_c.Std.C.Type.proto =
        {
          return = long;
          args = List.init 8 ~f:(fun i -> (sprintf "a%d" i, long));
          variadic = false;
        }
      in
      let args =
        Bap_c.Std.C.Abi.apply abi
          (Bap_c.Std.C.Abi.model target)
          [] proto (Sub.create ())
        |> Term.enum arg_t |> Seq.to_list
      in
      let regs intent =
        List.concat_map args ~f:(fun a ->
            match (Arg.intent a, Arg.rhs a) with
            | Some i, Var v when Poly.equal i intent -> [ name v ]
            | Some i, (Cast (_, _, Var v) | Extract (_, _, Var v))
              when Poly.equal i intent ->
                [ name v ]
            | _ -> [])
        |> String.Set.of_list
      in
      (regs In, regs Out)

(* the address of a load or a store, as the folded code computes it *)
type address = Known of Byte.t | Unknown

let address_of ~bases (e : exp) =
  let slot v c =
    let b = name v in
    if Set.mem bases b then Known (Slot (b, c)) else Unknown
  in
  match e with
  | Int w -> Known (Const (int64_of_word w))
  | Var v -> slot v 0L
  | BinOp (PLUS, Var v, Int c) | BinOp (PLUS, Int c, Var v) ->
      slot v (int64_of_word c)
  | BinOp (MINUS, Var v, Int c) -> slot v Int64.(neg (int64_of_word c))
  | _ -> Unknown

(* what an expression reads: the registers and the temporaries, the bytes
   of the memory at the known addresses, and whether it loads from an
   address, that isn't known *)
type uses = { read : state; unknown : bool }

let no_uses = { read = empty; unknown = false }
let join a b = { read = union a.read b.read; unknown = a.unknown || b.unknown }

let rec uses ~bases ~addresses (e : exp) =
  let go = uses ~bases ~addresses in
  match e with
  | Var v -> (
      match Var.typ v with
      | Mem _ -> no_uses
      | _ ->
          {
            no_uses with
            read = { empty with regs = String.Set.singleton (name v) };
          })
  | Int _ | Unknown _ -> no_uses
  | Load (m, a, _, sz) ->
      let u =
        match address_of ~bases a with
        | Known byte ->
            {
              no_uses with
              read = { empty with bytes = range byte (Size.in_bytes sz) };
            }
        | Unknown -> { no_uses with unknown = true }
      in
      let u = join (go m) u in
      if addresses then join u (go a) else u
  | Store (m, a, x, _, _) ->
      let u = join (go m) (go x) in
      if addresses then join u (go a) else u
  | BinOp (_, x, y) | Concat (x, y) | Let (_, x, y) -> join (go x) (go y)
  | UnOp (_, x) | Cast (_, _, x) | Extract (_, _, x) -> go x
  | Ite (c, x, y) -> join (go c) (join (go x) (go y))

type store = { addr : address; size : int; value : exp; index : exp }

(* the stores of a def of the memory, the innermost, which runs first,
   first *)
let rec stores ~bases (e : exp) =
  match e with
  | Store (m, a, x, _, sz) ->
      stores ~bases m
      @ [
          {
            addr = address_of ~bases a;
            size = Size.in_bytes sz;
            value = x;
            index = a;
          };
        ]
  | _ -> []

type item = Def of def term | Jmp of jmp term

let items blk =
  (Term.enum def_t blk |> Seq.to_list |> List.map ~f:(fun d -> Def d))
  @ (Term.enum jmp_t blk |> Seq.to_list |> List.map ~f:(fun j -> Jmp j))

let site blk = function
  | Def d ->
      Option.first_some (Term.get_attr d address) (Term.get_attr blk address)
  | Jmp j ->
      Option.first_some (Term.get_attr j address) (Term.get_attr blk address)

(* the jump, that leaves the function: a return, which the lifters
   represent as a call, that doesn't return, or a tail call *)
let leaves j =
  match Jmp.kind j with
  | Ret _ -> true
  | Call c -> Option.is_none (Call.return c)
  | Goto _ | Int _ -> false

let has_exit blk = Term.enum jmp_t blk |> Seq.exists ~f:leaves

(* the sub of the program, that has the instruction at [addr], and the
   block and the indices of the terms of the instruction *)
let find proj addr =
  let width = Theory.Target.code_addr_size (Project.target proj) in
  let a = Addr.of_int64 ~width addr in
  Term.enum sub_t (Project.program proj)
  |> Seq.find_map ~f:(fun sub ->
      Term.enum blk_t sub
      |> Seq.find_map ~f:(fun blk ->
          let indices =
            List.filter_mapi (items blk) ~f:(fun i t ->
                Option.some_if (Option.exists (site blk t) ~f:(Addr.equal a)) i)
          in
          match
            ( List.min_elt indices ~compare:Int.compare,
              List.max_elt indices ~compare:Int.compare )
          with
          | Some first, Some last -> Some (sub, blk, first, last)
          | _ -> None))

let slice ?(forward = false) ?(addresses = false) ?(depth = 0) proj addr
    locations =
  match find proj addr with
  | None -> invalid_argf "Bap_emu.Static.slice: no instruction at %Lx" addr ()
  | Some (sub, start, first, last) ->
      let target = Project.target proj in
      let bases = bases target in
      let args, results = abi target in
      let uses = uses ~bases ~addresses in
      let stores = stores ~bases in
      let prog = Project.program proj in
      (* the subs, by their tids, which the direct calls name *)
      let subs = Tid.Table.create () in
      Term.enum sub_t prog
      |> Seq.iter ~f:(fun sub -> Hashtbl.set subs ~key:(Term.tid sub) ~data:sub);
      let callee c =
        match Call.target c with
        | Direct tid -> Hashtbl.find subs tid
        | Indirect _ -> None
      in
      (* the folded defs of the subs, once each *)
      let folded = Tid.Table.create () in
      let rhs sub =
        let table =
          Hashtbl.find_or_add folded (Term.tid sub) ~default:(fun () ->
              Bap_emu_fold.(defs (fold sub)))
        in
        fun d ->
          Option.value (Hashtbl.find table (Term.tid d)) ~default:(Def.rhs d)
      in
      let sites = Int64.Hash_set.create () in
      let calls = Int64.Hash_set.create () in
      let complete = ref true in
      let site blk t = Option.map (site blk t) ~f:int64_of_word in
      let mark blk t = Option.iter (site blk t) ~f:(Hash_set.add sites) in
      let mark_call blk t =
        Option.iter (site blk t) ~f:(fun a ->
            Hash_set.add sites a;
            Hash_set.add calls a)
      in
      let intersects a b = not (Set.is_empty (Set.inter a b)) in
      let tainted s (u : uses) =
        intersects u.read.regs s.regs || intersects u.read.bytes s.bytes
      in
      let is_slot_of b = function
        | Byte.Slot (b', _) -> String.equal b b'
        | Const _ -> false
      in
      (* the slots of the base register [b], after the def [b := a + c],
         are the slots of [a] before it, and the others are lost *)
      let rekey_back s b = function
        | Known (Slot (a, c)) ->
            {
              s with
              bytes =
                Set.map
                  (module Byte)
                  s.bytes
                  ~f:(function
                    | Slot (b', off) when String.equal b b' ->
                        Slot (a, Int64.(off + c))
                    | byte -> byte);
            }
        | _ ->
            let lost, kept = Set.partition_tf s.bytes ~f:(is_slot_of b) in
            if not (Set.is_empty lost) then complete := false;
            { s with bytes = kept }
      in
      (* the slots of [b] before the def [b := a + c] are the slots of [a]
         after it, at the other offsets, and the slots of [a] stay *)
      let rekey_forth s b = function
        | Known (Slot (a, c)) when String.equal a b ->
            {
              s with
              bytes =
                Set.map
                  (module Byte)
                  s.bytes
                  ~f:(function
                    | Slot (b', off) when String.equal b b' ->
                        Slot (b, Int64.(off - c))
                    | byte -> byte);
            }
        | def ->
            let kept = Set.filter s.bytes ~f:(Fn.non (is_slot_of b)) in
            let aliases =
              match def with
              | Known (Slot (a, c)) ->
                  Set.filter_map
                    (module Byte)
                    s.bytes
                    ~f:(function
                      | Slot (a', off) when String.equal a a' ->
                          Some (Byte.Slot (b, Int64.(off - c)))
                      | _ -> None)
              | _ -> Set.empty (module Byte)
            in
            { s with bytes = Set.union kept aliases }
      in
      (* the summaries of the callees, by their seeds, as the calls repeat *)
      let summaries = Tid.Table.create () in
      (* The locations, that flow to the [seed], backward, or from it,
         forward, over the [sub], from the positions, [starts], in the
         blocks, to its boundary, the entry, or the exits, whose state is
         the result, and through the callees, up to the [depth], whose
         summaries stand for the calls. *)
      let rec analyze ~depth sub ~starts seed =
        let rhs = rhs sub in
        let cfg = Sub.to_cfg sub in
        let boundary = ref empty in
        let seen = Tid.Table.create () in
        (* the callee runs with the state, and gives the state after it,
           or [None], if it isn't followed *)
        let follow blk t c s =
          match callee c with
          | Some callee when depth > 0 -> (
              let seed = consts s in
              let starts =
                if forward then
                  Option.to_list (Term.first blk_t callee)
                  |> List.map ~f:(fun b -> (b, 0))
                else
                  Term.enum blk_t callee |> Seq.to_list
                  |> List.filter ~f:has_exit
                  |> List.map ~f:(fun b -> (b, List.length (items b)))
              in
              match starts with
              | [] -> None
              | _ ->
                  mark_call blk t;
                  let out =
                    match
                      Hashtbl.find_multi summaries (Term.tid callee)
                      |> List.find ~f:(fun (seed', _) -> equal_state seed seed')
                    with
                    | Some (_, out) -> out
                    | None ->
                        let out =
                          analyze ~depth:(depth - 1) callee ~starts seed
                        in
                        Hashtbl.add_multi summaries ~key:(Term.tid callee)
                          ~data:(seed, out);
                        out
                  in
                  Some (union (slots s) (consts out)))
          | _ -> None
        in
        (* backward: the live locations before the item, from those after
           it *)
        let step_back blk s = function
          | Jmp j -> (
              match Jmp.kind j with
              | Call c
                when Option.is_some (Call.return c) && intersects s.regs results
                -> (
                  let live = Set.inter s.regs results in
                  let s = { s with regs = Set.diff s.regs results } in
                  match follow blk (Jmp j) c { s with regs = live } with
                  | Some s' -> s'
                  | None ->
                      mark_call blk (Jmp j);
                      s)
              | _ -> s)
          | Def d -> (
              let v = Def.lhs d in
              match Var.typ v with
              | Mem _ ->
                  List.fold
                    (List.rev (stores (rhs d)))
                    ~init:s
                    ~f:(fun s st ->
                      match st.addr with
                      | Known byte ->
                          let hit = Set.inter s.bytes (range byte st.size) in
                          if Set.is_empty hit then s
                          else begin
                            mark blk (Def d);
                            let u = uses st.value in
                            let u =
                              if addresses then join u (uses st.index) else u
                            in
                            if u.unknown then complete := false;
                            union { s with bytes = Set.diff s.bytes hit } u.read
                          end
                      | Unknown ->
                          if not (Set.is_empty s.bytes) then complete := false;
                          s)
              | _ ->
                  let n = name v in
                  let s =
                    if Set.mem s.regs n then begin
                      mark blk (Def d);
                      let u = uses (rhs d) in
                      if u.unknown then complete := false;
                      union { s with regs = Set.remove s.regs n } u.read
                    end
                    else s
                  in
                  if Set.mem bases n then
                    rekey_back s n (address_of ~bases (rhs d))
                  else s)
        in
        (* forward: the tainted locations after the item, from those before
           it *)
        let step_forth blk s = function
          | Jmp j -> (
              let u = uses (Jmp.cond j) in
              let u =
                match Jmp.kind j with
                | Goto (Indirect e) | Ret (Indirect e) -> join u (uses e)
                | Call c -> (
                    match Call.target c with
                    | Indirect e -> join u (uses e)
                    | Direct _ -> u)
                | Goto (Direct _) | Ret (Direct _) | Int _ -> u
              in
              if tainted s u then mark blk (Jmp j);
              match Jmp.kind j with
              | Call c when Option.is_some (Call.return c) -> (
                  (* the arguments flow to the callee, which defines the
                     results, when it returns *)
                  let passes = intersects s.regs args in
                  match if passes then follow blk (Jmp j) c s else None with
                  | Some s' -> s'
                  | None ->
                      if passes then mark_call blk (Jmp j);
                      { s with regs = Set.diff s.regs results })
              | Call c -> (
                  (* a tail call, whose exits are the exits of the
                     function, unless it is a return *)
                  match Call.target c with
                  | Direct _ ->
                      let passes = intersects s.regs args in
                      (match
                         if passes then follow blk (Jmp j) c s else None
                       with
                      | Some s' -> boundary := union !boundary s'
                      | None ->
                          if passes then mark_call blk (Jmp j);
                          boundary := union !boundary s);
                      s
                  | Indirect _ ->
                      boundary := union !boundary s;
                      s)
              | Ret _ ->
                  boundary := union !boundary s;
                  s
              | _ -> s)
          | Def d -> (
              let v = Def.lhs d in
              match Var.typ v with
              | Mem _ ->
                  List.fold
                    (stores (rhs d))
                    ~init:s
                    ~f:(fun s st ->
                      let u = uses st.value in
                      let u = if addresses then join u (uses st.index) else u in
                      let from = tainted s u in
                      if u.unknown && not (Set.is_empty s.bytes) then
                        complete := false;
                      match st.addr with
                      | Known byte ->
                          let bytes = range byte st.size in
                          if from then begin
                            mark blk (Def d);
                            { s with bytes = Set.union s.bytes bytes }
                          end
                          else { s with bytes = Set.diff s.bytes bytes }
                      | Unknown ->
                          if from then begin
                            mark blk (Def d);
                            complete := false
                          end;
                          s)
              | _ ->
                  let u = uses (rhs d) in
                  let n = name v in
                  if u.unknown && not (Set.is_empty s.bytes) then
                    complete := false;
                  let s =
                    if tainted s u then begin
                      mark blk (Def d);
                      { s with regs = Set.add s.regs n }
                    end
                    else { s with regs = Set.remove s.regs n }
                  in
                  if Set.mem bases n then
                    rekey_forth s n (address_of ~bases (rhs d))
                  else s)
        in
        let node blk = Graphs.Ir.Node.create blk in
        let next blk =
          (if forward then Graphs.Ir.Node.succs else Graphs.Ir.Node.preds)
            (node blk) cfg
          |> Seq.map ~f:Graphs.Ir.Node.label
          |> Seq.to_list
        in
        (* the exits, forward, put their states to the boundary themselves,
           as the jumps are stepped *)
        let is_exit blk = List.is_empty (next blk) && not forward in
        (* the items of the block, from the position, in the direction *)
        let run blk ~from s =
          let ts = items blk in
          let ts =
            if forward then List.drop ts from else List.rev (List.take ts from)
          in
          List.fold ts ~init:s
            ~f:(if forward then step_forth blk else step_back blk)
        in
        let rec visit blk ~from s =
          if not (is_empty s) then begin
            let s' = run blk ~from s in
            if is_exit blk then boundary := union !boundary s';
            (* a block, that falls off, forward, e.g., without a jump *)
            if forward && List.is_empty (next blk) && not (has_exit blk) then
              boundary := union !boundary s';
            List.iter (next blk) ~f:(fun b -> arrive b s')
          end
        and arrive blk s =
          let tid = Term.tid blk in
          let known = Option.value (Hashtbl.find seen tid) ~default:empty in
          if not (is_subset s ~of_:known) then begin
            let s = union known s in
            Hashtbl.set seen ~key:tid ~data:s;
            visit blk ~from:(if forward then 0 else List.length (items blk)) s
          end
        in
        List.iter starts ~f:(fun (blk, from) -> visit blk ~from seed);
        !boundary
      in
      (* without the locations, the slice is of what the instruction
         writes, forward, or reads, backward *)
      let seed =
        if not (List.is_empty locations) then of_locations target locations
        else
          let rhs = rhs sub in
          List.sub (items start) ~pos:first ~len:(last - first + 1)
          |> List.fold ~init:empty ~f:(fun s t ->
              match t with
              | Jmp j -> if forward then s else union s (uses (Jmp.cond j)).read
              | Def d -> (
                  if not forward then begin
                    let u = uses (rhs d) in
                    if u.unknown then complete := false;
                    union s u.read
                  end
                  else
                    match Var.typ (Def.lhs d) with
                    | Mem _ ->
                        List.fold
                          (stores (rhs d))
                          ~init:s
                          ~f:(fun s st ->
                            match st.addr with
                            | Known byte ->
                                {
                                  s with
                                  bytes = Set.union s.bytes (range byte st.size);
                                }
                            | Unknown ->
                                complete := false;
                                s)
                    | _ -> { s with regs = Set.add s.regs (name (Def.lhs d)) }))
          |> fun s ->
          {
            s with
            regs =
              Set.filter s.regs ~f:(fun r ->
                  not (String.is_prefix r ~prefix:"#"));
          }
      in
      let boundary =
        analyze ~depth sub
          ~starts:[ (start, if forward then last + 1 else first) ]
          seed
      in
      {
        sites = Hash_set.to_list sites |> List.sort ~compare:Int64.compare;
        live = to_locations boundary;
        calls = Hash_set.to_list calls |> List.sort ~compare:Int64.compare;
        complete = !complete;
      }
