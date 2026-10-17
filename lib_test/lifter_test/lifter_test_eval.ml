open Core
open Bap.Std

(* A direct evaluator of the BIL of one instruction, with the semantics of
   Primus_bil: the variables and the memory that are not assigned are zero,
   as the registers of a Primus machine, a jump only records the
   destination, a goto continues at the label of the instruction, and the
   other special statements have no effect. The operations are the ones of
   Bil.Apply, so it is much faster than a Primus machine. *)

type t = { vars : word Var.Map.t; pc : word option }

(* the memory is a map of the addresses to the bytes *)
type value = Imm of word | Mem of word Addr.Map.t

let imm = function
  | Imm x -> x
  | Mem _ -> failwith "BIL evaluation: a memory is used as a word"

let mem = function
  | Mem m -> m
  | Imm _ -> failwith "BIL evaluation: a word is used as a memory"

let zero = function
  | Type.Imm n -> Imm (Word.zero n)
  | Type.Mem _ -> Mem Addr.Map.empty
  | Type.Unk -> Imm (Word.zero 1)

let byte m a = match Map.find m a with Some x -> x | None -> Word.zero 8

let load m a endian size =
  let n = Size.in_bytes size in
  let bytes = List.init n ~f:(fun i -> byte m (Addr.nsucc a i)) in
  let bytes =
    match endian with LittleEndian -> List.rev bytes | BigEndian -> bytes
  in
  List.reduce_exn bytes ~f:Word.concat

let store m a x endian size =
  let n = Size.in_bytes size in
  List.init n ~f:(fun i ->
      let k = match endian with LittleEndian -> i | BigEndian -> n - 1 - i in
      (Addr.nsucc a i, Word.extract_exn ~hi:((8 * k) + 7) ~lo:(8 * k) x))
  |> List.fold ~init:m ~f:(fun m (a, b) -> Map.set m ~key:a ~data:b)

let is_label dst s =
  match Bil.decode Bil.label s with
  | Some l -> String.equal l dst
  | None -> false

let eval bil =
  let env = ref Var.Map.empty and pc = ref None in
  let pending = ref None and steps = ref 0 in
  let var locals v =
    match Map.find locals v with
    | Some x -> x
    | None -> (
        match Map.find !env v with Some x -> x | None -> zero (Var.typ v))
  in
  let rec exp locals : exp -> value = function
    | Bil.Var v -> var locals v
    | Bil.Int x -> Imm x
    | Bil.Load (m, a, e, s) ->
        Imm (load (mem (exp locals m)) (imm (exp locals a)) e s)
    | Bil.Store (m, a, x, e, s) ->
        let m = mem (exp locals m) and a = imm (exp locals a) in
        Mem (store m a (imm (exp locals x)) e s)
    | Bil.BinOp (op, x, y) ->
        Imm (Bil.Apply.binop op (imm (exp locals x)) (imm (exp locals y)))
    | Bil.UnOp (op, x) -> Imm (Bil.Apply.unop op (imm (exp locals x)))
    | Bil.Cast (c, n, x) -> Imm (Bil.Apply.cast c n (imm (exp locals x)))
    | Bil.Let (v, x, y) -> exp (Map.set locals ~key:v ~data:(exp locals x)) y
    | Bil.Unknown (_, t) -> zero t
    | Bil.Ite (c, x, y) ->
        if Word.is_one (imm (exp locals c)) then exp locals x else exp locals y
    | Bil.Extract (hi, lo, x) ->
        Imm (Word.extract_exn ~hi ~lo (imm (exp locals x)))
    | Bil.Concat (x, y) ->
        Imm (Word.concat (imm (exp locals x)) (imm (exp locals y)))
  in
  let exp = exp Var.Map.empty in
  let rec stmts = function
    | [] -> ()
    | _ when Option.is_some !pending -> ()
    | s :: ss ->
        stmt s;
        stmts ss
  and stmt s =
    incr steps;
    if !steps > 1_000_000 then failwith "BIL evaluation doesn't terminate";
    match s with
    | Bil.Move (v, x) -> env := Map.set !env ~key:v ~data:(exp x)
    | Bil.Jmp dst -> pc := Some (imm (exp dst))
    | Bil.If (c, yes, no) ->
        stmts (if Word.is_one (imm (exp c)) then yes else no)
    | Bil.While (c, body) as loop ->
        if Word.is_one (imm (exp c)) then (
          stmts body;
          stmt loop)
    | Bil.Special _ -> (
        match Bil.decode Bil.goto s with
        | Some dst -> pending := Some dst
        | None -> ())
    | Bil.CpuExn _ -> ()
  in
  let rec program ss =
    stmts ss;
    match !pending with
    | None -> ()
    | Some dst -> (
        pending := None;
        match List.drop_while bil ~f:(Fn.non (is_label dst)) with
        | [] -> failwithf "BIL evaluation: no label %s" dst ()
        | rest -> program rest)
  in
  program bil;
  let vars =
    Map.filter_map !env ~f:(function Imm x -> Some x | Mem _ -> None)
  in
  { vars; pc = !pc }

(* the registers of a Primus machine are zero, so are the variables here *)
let lookup { vars } v =
  match (Map.find vars v, Var.typ v) with
  | (Some _ as x), _ -> x
  | None, Type.Imm n -> Some (Word.zero n)
  | None, (Type.Mem _ | Type.Unk) -> None

let pc { pc } = pc
