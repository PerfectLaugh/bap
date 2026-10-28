(* the slots of the frame of a sub, i.e., the memory at the constant
   offsets from the stack pointer at its entry, which are the variables
   of LLVM, so that LLVM optimizes them, as the registers, e.g., the
   state of a flattened control flow, that the code keeps on the stack.

   The slots are promoted, only if the address of the frame doesn't
   escape: it isn't stored outside the frame, it isn't in a register, but
   the stack and the frame pointers, at the jumps, that leave the sub, and
   the memory isn't
   accessed at an unknown address in the frame, so that the other
   accesses of the memory don't access the slots. The slots, whose
   accesses overlap, but are not the same, stay in the memory. *)

open Core
open Bap.Std
open Bap_core_theory

(* the value of a variable: the stack pointer at the entry with the
   offset, a value, that is computed from the frame, or the other one *)
type value = Off of int | Derived | Other

let equal_value x y =
  match (x, y) with
  | Off a, Off b -> a = b
  | Derived, Derived | Other, Other -> true
  | _ -> false

let join x y =
  match (x, y) with
  | Off a, Off b when a = b -> x
  | Other, Other -> Other
  | _ -> Derived

type state = value Var.Map.t

module Var_state = struct
  let empty : state = Var.Map.empty
end

let get s v = Option.value (Map.find s v) ~default:Other
let set s v = function Other -> Map.remove s v | x -> Map.set s ~key:v ~data:x

let join_states a b =
  Map.merge a b ~f:(fun ~key:_ -> function
    | `Both (x, y) -> Some (join x y)
    | `Left x | `Right x -> Some (join x Other))
  |> Map.filter ~f:(fun x -> not (equal_value x Other))

type t = {
  sp : var;
  fp : var option;
  entries : state Tid.Map.t;
  slots : Int.Set.t Int.Map.t;  (** the sizes of the slots by offsets *)
  big_endian : bool;
}

let constant = function
  | Bil.Int w -> Some (Word.to_int64_exn (Word.signed w) |> Int64.to_int_exn)
  | _ -> None

exception Escapes of string

(* the value of the expression, and the accesses of the memory, that it
   makes, which [access] gets *)
let rec eval ~ptr ~access s (e : exp) =
  let eval = eval ~ptr ~access s in
  let involved xs =
    if List.for_all xs ~f:(equal_value Other) then Other else Derived
  in
  match e with
  | Var v -> get s v
  | Int _ | Unknown _ -> Other
  | Load (m, a, _, size) ->
      memory ~ptr ~access s m;
      access a (eval a) (Size.in_bits size);
      Other
  | Store _ -> raise (Escapes "the store as a value")
  | BinOp (PLUS, x, y) -> (
      match (eval x, eval y, constant x, constant y) with
      | Off k, _, _, Some c | _, Off k, Some c, _ -> Off (k + c)
      | x, y, _, _ -> involved [ x; y ])
  | BinOp (MINUS, x, y) -> (
      match (eval x, eval y, constant y) with
      | Off k, _, Some c -> Off (k - c)
      | Off _, Off _, _ -> Other
      | x, y, _ -> involved [ x; y ])
  | BinOp (_, x, y) -> involved [ eval x; eval y ]
  | UnOp (_, x) -> involved [ eval x ]
  | Cast ((UNSIGNED | SIGNED), _, x) -> eval x
  | Cast (_, _, x) | Extract (_, _, x) -> involved [ eval x ]
  | Concat (x, y) -> involved [ eval x; eval y ]
  | Ite (c, x, y) ->
      ignore (eval c : value);
      join (eval x) (eval y)
  | Let (_, x, body) ->
      if not (equal_value (eval x) Other) then
        raise (Escapes "the address of the frame in a let");
      eval body

and memory ~ptr ~access s (m : exp) =
  match m with
  | Store (m, a, v, _, size) ->
      memory ~ptr ~access s m;
      let address = eval ~ptr ~access s a in
      access a address (Size.in_bits size);
      if
        Size.in_bits size >= ptr
        && (not (equal_value (eval ~ptr ~access s v) Other))
        && not (match address with Off _ -> true | _ -> false)
      then raise (Escapes "stores the address of the frame")
  | Var _ -> ()
  | Ite (c, x, y) ->
      ignore (eval ~ptr ~access s c : value);
      memory ~ptr ~access s x;
      memory ~ptr ~access s y
  | _ -> ()

(* the variables, that are narrower than the pointers, e.g., the flags,
   that the arithmetic of the stack pointer sets, can't be the address *)
let step ~ptr ~access s d =
  match Var.typ (Def.lhs d) with
  | Mem _ ->
      memory ~ptr ~access s (Def.rhs d);
      s
  | Imm n when n < ptr ->
      ignore (eval ~ptr ~access s (Def.rhs d) : value);
      set s (Def.lhs d) Other
  | _ -> set s (Def.lhs d) (eval ~ptr ~access s (Def.rhs d))

let ignore_accesses _ _ _ = ()

(* the state after the jump, that leaves the sub, e.g., after the callee
   returns: only the stack and the frame pointers are known, and the
   call of x86 pushed the return address, which the callee popped *)
let after_exit ~sp ~fp ~push s =
  let s' =
    set Var.Map.empty sp
      (match get s sp with Off k -> Off (k + push) | x -> x)
  in
  match fp with Some fp -> set s' fp (get s fp) | None -> s'

let check_exit ~sp ~fp s =
  Map.iteri s ~f:(fun ~key ~data ->
      if
        Var.is_physical key
        && (not (equal_value data Other))
        && (not (Var.equal key sp))
        && not (Option.exists fp ~f:(Var.equal key))
      then
        raise
          (Escapes
             (sprintf "passes the address of the frame in %s" (Var.name key))))

(* the successors of the block in the sub, with their states *)
let successors ~ptr ~sp ~fp ~push ~access sub blk s =
  let is_block tid = Option.is_some (Term.find blk_t sub tid) in
  let returned = ref false in
  Term.enum jmp_t blk |> Seq.to_list
  |> List.concat_map ~f:(fun jmp ->
      ignore (eval ~ptr ~access s (Jmp.cond jmp) : value);
      let indirect e =
        if not (equal_value (eval ~ptr ~access s e) Other) then
          raise (Escapes "jumps to the address of the frame")
      in
      let leave () =
        check_exit ~sp ~fp s;
        after_exit ~sp ~fp ~push s
      in
      match Jmp.kind jmp with
      | (Goto (Direct tid) | Ret (Direct tid)) when is_block tid ->
          (* the call, that doesn't return, continues in the next block,
             by the address of its return, see [Opaque.fallthrough] *)
          [ (tid, if !returned then after_exit ~sp ~fp ~push s else s) ]
      | Goto (Direct _) | Ret (Direct _) ->
          ignore (leave () : state);
          []
      | Goto (Indirect e) | Ret (Indirect e) ->
          indirect e;
          ignore (leave () : state);
          []
      | Call c -> (
          (match Call.target c with Indirect e -> indirect e | Direct _ -> ());
          let s' = leave () in
          match Call.return c with
          | Some (Direct tid) -> [ (tid, s') ]
          | Some (Indirect e) ->
              indirect e;
              []
          | None ->
              returned := true;
              [])
      | Int (_, tid) -> [ (tid, s) ])

let block_states ~ptr ~sp ~fp ~push sub =
  match Term.first blk_t sub with
  | None -> Tid.Map.empty
  | Some first ->
      let entries =
        ref (Tid.Map.singleton (Term.tid first) (set Var.Map.empty sp (Off 0)))
      in
      let queue = Queue.of_list [ Term.tid first ] in
      while not (Queue.is_empty queue) do
        let tid = Queue.dequeue_exn queue in
        match Term.find blk_t sub tid with
        | None -> ()
        | Some blk ->
            let s =
              Term.enum def_t blk
              |> Seq.fold
                   ~init:(Map.find_exn !entries tid)
                   ~f:(step ~ptr ~access:ignore_accesses)
            in
            successors ~ptr ~sp ~fp ~push ~access:ignore_accesses sub blk s
            |> List.iter ~f:(fun (succ, s) ->
                let joined =
                  match Map.find !entries succ with
                  | None -> s
                  | Some old -> join_states old s
                in
                if
                  not
                    (Option.equal (Map.equal equal_value)
                       (Map.find !entries succ) (Some joined))
                then (
                  entries := Map.set !entries ~key:succ ~data:joined;
                  Queue.enqueue queue succ))
      done;
      !entries

(* the slots, that the accesses of the sub make, but the ones, that
   overlap the others *)
let slots_of ~ptr ~sp ~fp ~push sub entries =
  let accesses = ref Int.Map.empty in
  let access a value bits =
    match value with
    | Off k ->
        accesses :=
          Map.update !accesses k ~f:(fun sizes ->
              Set.add (Option.value sizes ~default:Int.Set.empty) bits)
    | Derived ->
        raise
          (Escapes
             (Format.asprintf "accesses the frame at %a, at an unknown offset"
                Exp.pp a))
    | Other -> ()
  in
  Map.iteri entries ~f:(fun ~key ~data ->
      Option.iter (Term.find blk_t sub key) ~f:(fun blk ->
          let s =
            Term.enum def_t blk |> Seq.fold ~init:data ~f:(step ~ptr ~access)
          in
          ignore (successors ~ptr ~sp ~fp ~push ~access sub blk s)));
  let ranges =
    Map.to_alist !accesses
    |> List.concat_map ~f:(fun (k, sizes) ->
        Set.to_list sizes |> List.map ~f:(fun bits -> (k, bits)))
  in
  let overlaps (k, b) (k', b') =
    (k <> k' || b <> b') && k < k' + (b' / 8) && k' < k + (b / 8)
  in
  List.filter ranges ~f:(fun r -> not (List.exists ranges ~f:(overlaps r)))
  |> List.fold ~init:Int.Map.empty ~f:(fun m (k, b) ->
      Map.update m k ~f:(fun s ->
          Set.add (Option.value s ~default:Int.Set.empty) b))

let register target role sub =
  Option.bind (Theory.Target.reg target role) ~f:(fun reg ->
      let name = Theory.Var.name reg in
      Term.enum blk_t sub
      |> Seq.find_map ~f:(fun blk ->
          Term.enum def_t blk
          |> Seq.find_map ~f:(fun d ->
              Set.find
                (Set.add (Def.free_vars d) (Def.lhs d))
                ~f:(fun v -> String.equal (Var.name v) name))))

let is_x86 target =
  List.exists (target :: Theory.Target.parents target) ~f:(fun t ->
      String.equal (KB.Name.unqualified (Theory.Target.name t)) "x86")

(* the frame of the sub, or the reason, why its slots can't be the
   variables of LLVM *)
let analyze ~target sub =
  match register target Theory.Role.Register.stack_pointer sub with
  | None -> Error "the sub doesn't use the stack pointer"
  | Some sp -> (
      let fp = register target Theory.Role.Register.frame_pointer sub in
      let push = if is_x86 target then Theory.Target.bits target / 8 else 0 in
      let ptr = match Var.typ sp with Imm n -> n | _ -> 64 in
      match block_states ~ptr ~sp ~fp ~push sub with
      | entries -> (
          match slots_of ~ptr ~sp ~fp ~push sub entries with
          | slots ->
              Ok
                {
                  sp;
                  fp;
                  entries;
                  slots;
                  big_endian =
                    Theory.Endianness.(
                      equal (Theory.Target.endianness target) eb);
                }
          | exception Escapes reason -> Error reason)
      | exception Escapes reason -> Error reason)

let entry t tid = Option.value (Map.find t.entries tid) ~default:Var.Map.empty
let pointer_width t = match Var.typ t.sp with Imm n -> n | _ -> 64
let step t s d = step ~ptr:(pointer_width t) ~access:ignore_accesses s d

(* the slot of the access of [bits] at the address [a] in the state *)
let slot t s a bits =
  match eval ~ptr:(pointer_width t) ~access:ignore_accesses s a with
  | Off k when Option.exists (Map.find t.slots k) ~f:(fun b -> Set.mem b bits)
    ->
      Some k
  | _ -> None
  | exception Escapes _ -> None

let slots t =
  Map.to_alist t.slots
  |> List.concat_map ~f:(fun (k, sizes) ->
      Set.to_list sizes |> List.map ~f:(fun bits -> (k, bits)))

let stack_pointer t = t.sp
let big_endian t = t.big_endian
