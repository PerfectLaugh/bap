(* optimizes the subs of BIR with the passes of LLVM: each sub is a
   function of LLVM, whose jumps, that leave it, e.g., the calls, are the
   calls of the opaque functions, which opt optimizes, and which is
   raised back to BIR, with the same jumps, that leave it *)

open Core
open Bap.Std
open Recompile_llvm

(* the jumps, that leave the sub, by their numbers, and the blocks, in which
   the code continues after them, e.g., after the call, that doesn't
   return, but whose callee returns to the address of the next block *)
type exits = (jmp term * tid option) Int.Table.t

module Opaque (S : sig
  val prog : program
  val sub : sub term
  val buf : Buffer.t
  val exits : exits
  val prefix : string
end) =
struct
  include Emit (struct
    let prog = S.prog
    let sub = S.sub
    let buf = S.buf
  end)

  (* the opaque call, after which the code continues in [return] *)
  let leave jmp target return =
    let k = Hashtbl.length S.exits in
    Hashtbl.set S.exits ~key:k ~data:(jmp, return);
    let arg =
      match target with
      | None -> ""
      | Some e ->
          let t, w = exp String.Map.empty e in
          sprintf "i64 %s" (resize t w 64)
    in
    sync_out ();
    line "  call void @%s.exit.%d(%s)" S.prefix k arg;
    match return with
    | Some tid ->
        sync_in ();
        line "  br label %%%s" (label tid)
    | None -> line "  unreachable"

  let return = function
    | Some (Direct tid) when is_block tid -> Some tid
    | Some (Direct tid) -> unsupported "the return to %a" Tid.pp tid
    | Some (Indirect _) -> unsupported "the indirect return"
    | None -> None

  let transfer ?fallthrough jmp =
    match Jmp.kind jmp with
    | (Goto (Direct tid) | Ret (Direct tid)) when is_block tid ->
        line "  br label %%%s" (label tid)
    | Goto (Direct _) | Ret (Direct _) -> leave jmp None None
    | Goto (Indirect e) | Ret (Indirect e) -> leave jmp (Some e) None
    | Call c ->
        let target =
          match Call.target c with Indirect e -> Some e | Direct _ -> None
        in
        let return =
          match return (Call.return c) with None -> fallthrough | ret -> ret
        in
        leave jmp target return
    | Int (_, ret) -> leave jmp None (Some ret)

  (* the next block, if the jumps, that follow, go to it *)
  let fallthrough rest =
    match rest with
    | jmp :: _ -> (
        match (Jmp.cond jmp, Jmp.kind jmp) with
        | Int w, Goto (Direct tid) when Word.is_one w && is_block tid ->
            Some tid
        | _ -> None)
    | [] -> None

  let jumps blk =
    let rec loop = function
      | [] -> unsupported "the block %a without a jump" Tid.pp (Term.tid blk)
      | jmp :: rest -> (
          match Jmp.cond jmp with
          | Int w when Word.is_one w ->
              transfer ?fallthrough:(fallthrough rest) jmp
          | cond ->
              let c, w = exp String.Map.empty cond in
              let c = resize c w 1 in
              let taken = fresh_label "taken" and next = fresh_label "next" in
              line "  br i1 %s, label %%%s, label %%%s" c taken next;
              line "%s:" taken;
              transfer ?fallthrough:(fallthrough rest) jmp;
              line "%s:" next;
              loop rest)
    in
    loop (Term.enum jmp_t blk |> Seq.to_list)

  let body () =
    Set.iter vars ~f:(fun v ->
        line "  %s = alloca %s" (local v) (ty (Option.value_exn (width v))));
    sync_in ();
    match Term.first blk_t S.sub with
    | None -> unsupported "the sub without blocks"
    | Some first ->
        line "  br label %%%s" (label (Term.tid first));
        Term.enum blk_t S.sub
        |> Seq.iter ~f:(fun blk ->
            line "%s:" (label (Term.tid blk));
            Term.enum def_t blk |> Seq.iter ~f:def;
            jumps blk)
end

(* the function of the sub, and its jumps, that leave it *)
type func = { sub : sub term; name : string; exits : exits }

let emit_func prog out n sub =
  let buf = Buffer.create 4096 in
  let exits = Int.Table.create () in
  let name = sprintf "f%d" n in
  let module E = Opaque (struct
    let prog = prog
    let sub = sub
    let buf = buf
    let exits = exits
    let prefix = name
  end) in
  match E.body () with
  | exception Unsupported msg -> Error msg
  | () ->
      Hashtbl.iteri exits ~f:(fun ~key ~data ->
          let indirect =
            match Jmp.kind (fst data) with
            | Goto (Indirect _) | Ret (Indirect _) -> true
            | Call c -> (
                match Call.target c with Indirect _ -> true | _ -> false)
            | _ -> false
          in
          bprintf out "declare void @%s.exit.%d(%s)\n" name key
            (if indirect then "i64" else ""));
      bprintf out "define void @%s() {\nentry:\n" name;
      Buffer.add_buffer out buf;
      bprintf out "}\n\n";
      Ok { sub; name; exits }

(* the subset of LLVM IR, that opt makes of the functions *)
module Parse = struct
  type value = E of exp | Global of string

  type item =
    | Assign of var * exp
    | Store of exp * exp * size
    | Leave of int * exp option

  type terminator =
    | Br of string
    | Cbr of exp * string * string
    | Switch of exp * int * (word * string) list * string
    | Unreachable
    | Return

  type block = {
    label : string;
    phis : (var * (exp * string) list) list;
    items : item list;
    terminator : terminator;
  }

  exception Error of string

  let error fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt

  let tokenize line =
    let line =
      match String.index line ';' with
      | Some i -> String.prefix line i
      | None -> line
    in
    let tokens = ref [] and buf = Buffer.create 16 in
    let flush () =
      if Buffer.length buf > 0 then (
        tokens := Buffer.contents buf :: !tokens;
        Buffer.clear buf)
    in
    String.iter line ~f:(fun c ->
        match c with
        | ' ' | '\t' -> flush ()
        | ',' | '(' | ')' | '[' | ']' | '{' | '}' | '=' | '<' | '>' ->
            flush ();
            tokens := String.of_char c :: !tokens
        | c -> Buffer.add_char buf c);
    flush ();
    List.rev !tokens

  (* the flags of the instructions, that don't change their semantics, as
     the code has no undefined behavior *)
  let flags =
    [
      "nuw";
      "nsw";
      "exact";
      "disjoint";
      "nneg";
      "samesign";
      "inbounds";
      "nusw";
      "tail";
      "musttail";
      "notail";
      "noundef";
      "signext";
      "zeroext";
      "volatile";
    ]

  let rec skip_flags = function
    | t :: rest when List.mem flags t ~equal:String.equal -> skip_flags rest
    | ts -> ts

  let width_of_type = function
    | "ptr" -> 64
    | t when String.is_prefix t ~prefix:"i" -> (
        match Int.of_string_opt (String.drop_prefix t 1) with
        | Some n -> n
        | None -> error "the type %s" t)
    | t -> error "the type %s" t
end

(* the raiser of the function, whose registers are [registers] *)
module Raise (S : sig
  val registers : var String.Map.t
  val mem : var
end) =
struct
  open Parse

  let vars = String.Table.create ()

  let var name w =
    match Hashtbl.find vars name with
    | Some v -> v
    | None ->
        let v =
          Var.create ~is_virtual:true
            ("l" ^ mangle (String.drop_prefix name 1))
            (Imm w)
        in
        Hashtbl.set vars ~key:name ~data:v;
        v

  let word_of w s =
    match s with
    | "true" -> Word.one w
    | "false" -> Word.zero w
    | s -> (
        match Int64.of_string_opt s with
        | None -> error "the constant %s" s
        | Some x ->
            if w <= 64 then Word.of_int64 ~width:w x
            else Word.extract_exn ~hi:(w - 1) (Word.signed (Word.of_int64 x)))

  let as_exp = function
    | E e -> e
    | Global g -> error "the address of %s as a value" g

  (* the pointers of LLVM are of 64 bits, and the addresses of the memory
     are of the width of the target *)
  let address_width =
    match Var.typ S.mem with Mem (a, _) -> Size.in_bits a | _ -> 64

  let address a =
    if address_width = 64 then a else Bil.(cast low address_width a)

  let resize e w n =
    if w = n then e
    else if w > n then Bil.(cast low n e)
    else Bil.(cast unsigned n e)

  (* the operand of the type [w], and the rest of the tokens *)
  let rec operand w tokens =
    match tokens with
    | ("poison" | "undef") :: rest -> (E (Bil.unknown "llvm" (Imm w)), rest)
    | "null" :: rest -> (E (Bil.int (Word.zero 64)), rest)
    | v :: rest when String.is_prefix v ~prefix:"%" ->
        (E (Bil.var (var v w)), rest)
    | g :: rest when String.is_prefix g ~prefix:"@bap_" ->
        (Global (String.drop_prefix g 5), rest)
    | ("inttoptr" | "ptrtoint" | "bitcast" | "zext" | "sext" | "trunc")
      :: "(" :: rest ->
        let op = List.hd_exn tokens in
        let t, rest = List.split_n rest 1 in
        let x, rest = operand (width_of_type (List.hd_exn t)) rest in
        let wx = width_of_type (List.hd_exn t) in
        let rest =
          match rest with "to" :: _ :: ")" :: rest -> rest | _ -> error "cast"
        in
        let x = as_exp x in
        let e =
          match op with "sext" -> Bil.(cast signed w x) | _ -> resize x wx w
        in
        (E e, rest)
    | "getelementptr" :: rest -> (
        match skip_flags rest with
        | "(" :: elt :: "," :: "ptr" :: rest ->
            let base, rest = operand 64 rest in
            let rest =
              match rest with "," :: rest -> rest | _ -> error "gep"
            in
            let it, rest = List.split_n rest 1 in
            let wi = width_of_type (List.hd_exn it) in
            let idx, rest = operand wi rest in
            let rest =
              match rest with ")" :: rest -> rest | _ -> error "gep"
            in
            (E (gep elt (as_exp base) (as_exp idx) wi), rest)
        | _ -> error "the constant gep")
    | c :: rest -> (E (Bil.int (word_of w c)), rest)
    | [] -> error "no operand"

  and gep elt base idx wi =
    let scale = width_of_type elt / 8 in
    let idx = if wi = 64 then idx else Bil.(cast signed 64 idx) in
    let off =
      if scale = 1 then idx else Bil.(idx * int (Word.of_int ~width:64 scale))
    in
    Bil.(base + off)

  let typed tokens =
    match tokens with
    | t :: rest ->
        let w = width_of_type t in
        let v, rest = operand w (skip_flags rest) in
        (v, w, rest)
    | [] -> error "no typed operand"

  let comma = function "," :: rest -> rest | ts -> ts

  let binops =
    [
      ("add", Bil.PLUS);
      ("sub", Bil.MINUS);
      ("mul", Bil.TIMES);
      ("udiv", Bil.DIVIDE);
      ("sdiv", Bil.SDIVIDE);
      ("urem", Bil.MOD);
      ("srem", Bil.SMOD);
      ("and", Bil.AND);
      ("or", Bil.OR);
      ("xor", Bil.XOR);
      ("shl", Bil.LSHIFT);
      ("lshr", Bil.RSHIFT);
      ("ashr", Bil.ARSHIFT);
    ]

  let icmp pred x y =
    match pred with
    | "eq" -> Bil.(x = y)
    | "ne" -> Bil.(x <> y)
    | "ult" -> Bil.(x < y)
    | "ule" -> Bil.(x <= y)
    | "ugt" -> Bil.(y < x)
    | "uge" -> Bil.(y <= x)
    | "slt" -> Bil.(x <$ y)
    | "sle" -> Bil.(x <=$ y)
    | "sgt" -> Bil.(y <$ x)
    | "sge" -> Bil.(y <=$ x)
    | p -> error "the predicate %s" p

  let const w x = Bil.int (Word.of_int ~width:w x)

  (* the intrinsics of LLVM, that instcombine makes, in BIL *)
  let intrinsic name w args =
    let base = String.chop_suffix_exn name ~suffix:(sprintf ".i%d" w) in
    match (base, args) with
    | "llvm.umin", [ x; y ] -> Bil.(ite (x < y) x y)
    | "llvm.umax", [ x; y ] -> Bil.(ite (x < y) y x)
    | "llvm.smin", [ x; y ] -> Bil.(ite (x <$ y) x y)
    | "llvm.smax", [ x; y ] -> Bil.(ite (x <$ y) y x)
    | "llvm.abs", x :: _ -> Bil.(ite (x <$ const w 0) (unop neg x) x)
    | "llvm.fshl", [ x; y; z ] ->
        let z = Bil.(z mod const w w) in
        Bil.(ite (z = const w 0) x ((x lsl z) lor (y lsr (const w w - z))))
    | "llvm.fshr", [ x; y; z ] ->
        let z = Bil.(z mod const w w) in
        Bil.(ite (z = const w 0) y ((x lsl (const w w - z)) lor (y lsr z)))
    | "llvm.ctpop", [ x ] ->
        List.init w ~f:(fun i -> Bil.(cast unsigned w (extract ~hi:i ~lo:i x)))
        |> List.reduce_exn ~f:Bil.( + )
    | "llvm.bswap", [ x ] ->
        List.init (w / 8) ~f:(fun i ->
            Bil.extract ~hi:((i * 8) + 7) ~lo:(i * 8) x)
        |> List.reduce_exn ~f:Bil.( ^ )
    | _ -> error "the intrinsic %s" name

  let call_args tokens =
    let rec loop acc = function
      | ")" :: rest -> (List.rev acc, rest)
      | tokens ->
          let v, _, rest = typed tokens in
          loop (v :: acc) (comma rest)
    in
    match tokens with "(" :: rest -> loop [] rest | _ -> error "the arguments"

  (* the definition of [lhs], and the item, that it makes *)
  let assign lhs tokens : [ `Item of item | `Phi of var * (exp * string) list ]
      =
    let op, rest =
      match tokens with
      | op :: rest -> (op, skip_flags rest)
      | [] -> error "empty"
    in
    let def w e = `Item (Assign (var lhs w, e)) in
    match op with
    | op when List.Assoc.mem binops op ~equal:String.equal ->
        let x, w, rest = typed rest in
        let y, _ = operand w (comma rest) in
        def w
          (Bil.binop
             (List.Assoc.find_exn binops op ~equal:String.equal)
             (as_exp x) (as_exp y))
    | "icmp" -> (
        match skip_flags rest with
        | pred :: rest ->
            let x, w, rest = typed rest in
            let y, _ = operand w (comma rest) in
            def 1 (icmp pred (as_exp x) (as_exp y))
        | [] -> error "icmp")
    | "select" ->
        let c, _, rest = typed rest in
        let x, w, rest = typed (comma rest) in
        let y, _, _ = typed (comma rest) in
        def w Bil.(ite (as_exp c) (as_exp x) (as_exp y))
    | "zext" | "sext" | "trunc" | "inttoptr" | "ptrtoint" | "bitcast" | "freeze"
      -> (
        let x, wx, rest = typed rest in
        let x = as_exp x in
        match rest with
        | "to" :: t :: _ ->
            let w = width_of_type t in
            def w
              (if String.equal op "sext" then Bil.(cast signed w x)
               else resize x wx w)
        | _ -> def wx x)
    | "load" -> (
        match rest with
        | t :: "," :: "ptr" :: rest -> (
            let w = width_of_type t in
            let p, _ = operand 64 rest in
            match p with
            | Global g -> (
                match Map.find S.registers g with
                | Some r -> def w (Bil.var r)
                | None -> error "the global %s" g)
            | E a ->
                def w
                  (Bil.load ~mem:(Bil.var S.mem) ~addr:(address a) LittleEndian
                     (Size.of_int_exn w)))
        | _ -> error "load")
    | "getelementptr" -> (
        match rest with
        | elt :: "," :: "ptr" :: rest -> (
            let base, rest = operand 64 rest in
            match comma rest with
            | it :: rest ->
                let wi = width_of_type it in
                let idx, _ = operand wi rest in
                def 64 (gep elt (as_exp base) (as_exp idx) wi)
            | [] -> error "gep")
        | _ -> error "gep")
    | "phi" -> (
        match rest with
        | t :: rest ->
            let w = width_of_type t in
            let rec incoming acc = function
              | "[" :: rest -> (
                  let v, rest = operand w rest in
                  match comma rest with
                  | l :: "]" :: rest ->
                      incoming
                        ((as_exp v, String.drop_prefix l 1) :: acc)
                        (comma rest)
                  | _ -> error "phi")
              | _ -> List.rev acc
            in
            `Phi (var lhs w, incoming [] rest)
        | [] -> error "phi")
    | "call" -> (
        match rest with
        | t :: f :: rest when String.is_prefix f ~prefix:"@llvm." ->
            let w = width_of_type t in
            let args, _ = call_args rest in
            def w
              (intrinsic (String.drop_prefix f 1) w (List.map args ~f:as_exp))
        | _ -> error "the call %s" (String.concat ~sep:" " tokens))
    | op -> error "the instruction %s" op

  let leave_of f =
    match String.split (String.drop_prefix f 1) ~on:'.' with
    | [ _; "exit"; k ] -> Int.of_string_opt k
    | _ -> None

  let statement tokens : [ `Item of item | `Skip | `Terminator of terminator ] =
    match tokens with
    | "store" :: rest -> (
        let v, w, rest = typed (skip_flags rest) in
        match comma rest with
        | "ptr" :: rest -> (
            let p, _ = operand 64 rest in
            match p with
            | Global g -> (
                match Map.find S.registers g with
                | Some r -> `Item (Assign (r, as_exp v))
                | None -> error "the global %s" g)
            | E a -> `Item (Store (address a, as_exp v, Size.of_int_exn w)))
        | _ -> error "store")
    | "call" :: rest -> (
        match skip_flags rest with
        | "void" :: f :: args -> (
            match leave_of f with
            | Some k ->
                let args, _ = call_args args in
                `Item (Leave (k, Option.map (List.hd args) ~f:as_exp))
            | None ->
                if String.is_prefix f ~prefix:"@llvm." then `Skip
                else error "the call of %s" f)
        | _ -> error "call")
    | "br" :: "label" :: l :: _ -> `Terminator (Br (String.drop_prefix l 1))
    | "br" :: rest -> (
        let c, _, rest = typed rest in
        match comma rest with
        | "label" :: a :: "," :: "label" :: b :: _ ->
            `Terminator
              (Cbr (as_exp c, String.drop_prefix a 1, String.drop_prefix b 1))
        | _ -> error "br")
    | "switch" :: rest -> (
        let v, w, rest = typed rest in
        match comma rest with
        | "label" :: d :: "[" :: rest ->
            let rec cases acc = function
              | "]" :: _ -> List.rev acc
              | _ :: c :: "," :: "label" :: l :: rest ->
                  cases ((word_of w c, String.drop_prefix l 1) :: acc) rest
              | _ -> error "switch"
            in
            `Terminator
              (Switch (as_exp v, w, cases [] rest, String.drop_prefix d 1))
        | _ -> error "switch")
    | "unreachable" :: _ -> `Terminator Unreachable
    | "ret" :: _ -> `Terminator Return
    | _ -> error "the statement %s" (String.concat ~sep:" " tokens)

  (* the blocks of the function, whose lines are [lines] *)
  let blocks lines =
    let blocks = ref [] in
    let label = ref "entry" and phis = ref [] and items = ref [] in
    let finish t =
      blocks :=
        {
          label = !label;
          phis = List.rev !phis;
          items = List.rev !items;
          terminator = t;
        }
        :: !blocks;
      phis := [];
      items := []
    in
    List.iter lines ~f:(fun line ->
        match tokenize line with
        | [] -> ()
        | [ l ] when String.is_suffix l ~suffix:":" ->
            label := String.drop_suffix l 1
        | lhs :: "=" :: rest when String.is_prefix lhs ~prefix:"%" -> (
            match assign lhs rest with
            | `Item i -> items := i :: !items
            | `Phi p -> phis := p :: !phis)
        | tokens -> (
            match statement tokens with
            | `Item i -> items := i :: !items
            | `Skip -> ()
            | `Terminator t -> finish t));
    List.rev !blocks
end

(* the functions of the module, that opt wrote, by their names *)
let functions text =
  let lines = String.split_lines text in
  (* the cases of the switches are on their own lines *)
  let rec join acc = function
    | [] -> List.rev acc
    | l :: rest
      when String.is_substring l ~substring:" switch "
           && not (String.is_substring l ~substring:"]") ->
        let cases, rest =
          List.split_while rest ~f:(fun l ->
              not (String.is_substring l ~substring:"]"))
        in
        let close, rest =
          match rest with c :: rest -> (c, rest) | [] -> ("]", [])
        in
        join (String.concat ~sep:" " ((l :: cases) @ [ close ]) :: acc) rest
    | l :: rest -> join (l :: acc) rest
  in
  let lines = join [] lines in
  let rec collect acc = function
    | [] -> acc
    | l :: rest when String.is_prefix l ~prefix:"define " ->
        let name =
          match String.lsplit2 l ~on:'@' with
          | Some (_, r) ->
              String.take_while r ~f:(fun c -> not (Char.equal c '('))
          | None -> ""
        in
        let body, rest =
          List.split_while rest ~f:(fun l -> not (String.equal l "}"))
        in
        collect (Map.set acc ~key:name ~data:body) (List.drop rest 1)
    | _ :: rest -> collect acc rest
  in
  collect String.Map.empty lines

(* substitutes the values, that the block uses once, after their
   definitions, into their uses, unless the memory or the registers, that
   they read, change before *)
let inline_values blocks =
  let open Parse in
  let uses = Var.Table.create () in
  let count e = Set.iter (Exp.free_vars e) ~f:(fun v -> Hashtbl.incr uses v) in
  List.iter blocks ~f:(fun b ->
      List.iter b.phis ~f:(fun (_, ins) ->
          List.iter ins ~f:(fun (e, _) -> count e));
      List.iter b.items ~f:(function
        | Assign (_, e) -> count e
        | Store (a, v, _) ->
            count a;
            count v
        | Leave (_, e) -> Option.iter e ~f:count);
      match b.terminator with
      | Cbr (c, _, _) -> count c
      | Switch (v, _, _, _) -> count v
      | Br _ | Unreachable | Return -> ());
  let once v =
    Var.is_virtual v && Option.equal Int.equal (Hashtbl.find uses v) (Some 1)
  in
  let reads_memory e =
    Exp.exists
      object
        inherit [unit] Exp.finder
        method! enter_load ~mem:_ ~addr:_ _ _ r = r.return (Some ())
      end
      e
  in
  let subst pending e =
    Map.fold pending ~init:e ~f:(fun ~key:v ~data:(x, _) e ->
        if Set.mem (Exp.free_vars e) v then Exp.substitute (Bil.var v) x e
        else e)
  in
  List.map blocks ~f:(fun b ->
      let pending = ref Var.Map.empty and out = ref [] in
      let take e =
        let e' = subst !pending e in
        pending :=
          Map.filter_keys !pending ~f:(fun v ->
              not (Set.mem (Exp.free_vars e) v));
        e'
      in
      let flush ~f =
        let keep, emit =
          Map.partition_tf !pending ~f:(fun (_, d) -> not (f d))
        in
        Map.iteri emit ~f:(fun ~key ~data:(x, _) ->
            out := Assign (key, x) :: !out);
        pending := keep
      in
      List.iter b.items ~f:(fun item ->
          match item with
          | Assign (v, e) ->
              let e = take e in
              (* the values, that read the register, are taken before it changes *)
              flush ~f:(fun d -> Set.mem (Exp.free_vars d) v);
              if once v then pending := Map.set !pending ~key:v ~data:(e, e)
              else out := Assign (v, e) :: !out
          | Store (a, v, s) ->
              let a = take a and v = take v in
              flush ~f:reads_memory;
              out := Store (a, v, s) :: !out
          | Leave (k, e) ->
              let e = Option.map e ~f:take in
              flush ~f:(fun _ -> true);
              out := Leave (k, e) :: !out);
      let terminator =
        match b.terminator with
        | Cbr (c, x, y) -> Cbr (take c, x, y)
        | Switch (v, w, cs, d) -> Switch (take v, w, cs, d)
        | t -> t
      in
      flush ~f:(fun _ -> true);
      { b with items = List.rev !out; terminator })

(* the sub of BIR, that the blocks of LLVM make, with the jumps of [exits] *)
let raise_sub ~mem sub exits (blocks : Parse.block list) =
  let open Parse in
  let tids = String.Table.create () in
  let tid l = Hashtbl.find_or_add tids l ~default:Tid.create in
  (* the entry keeps its identity, so that the jumps to it, e.g., from the
     code around an optimized region, still enter it *)
  (match (Term.first blk_t sub, blocks) with
  | Some first, b :: _ -> Hashtbl.set tids ~key:b.label ~data:(Term.tid first)
  | _ -> ());
  (* the addresses of the blocks, that the machines enter by their
     addresses: the entry, e.g., of the indirect calls, and the
     continuations of the calls, e.g., of the returns, as only they load the
     registers, while the other blocks use the values of their dominators *)
  let original =
    Term.enum blk_t sub
    |> Seq.filter_map ~f:(fun b ->
        Option.map (Term.get_attr b address) ~f:(fun a -> (Term.tid b, a)))
    |> Seq.to_list
    |> Tid.Map.of_alist_reduce ~f:(fun a _ -> a)
  in
  let addresses = Tid.Table.create () in
  Option.iter (Term.first blk_t sub) ~f:(fun first ->
      Option.iter
        (Map.find original (Term.tid first))
        ~f:(fun a ->
          match blocks with
          | b :: _ -> Hashtbl.set addresses ~key:(tid b.label) ~data:a
          | [] -> ()));
  let return_address k =
    Option.bind (snd (Hashtbl.find_exn exits k)) ~f:(Map.find original)
  in
  (* the copies of the phis, on the edge from [pred] to [succ] *)
  let edges = ref [] in
  let phis =
    String.Map.of_alist_exn (List.map blocks ~f:(fun b -> (b.label, b.phis)))
  in
  let target pred succ =
    match Map.find phis succ with
    | None | Some [] -> tid succ
    | Some ps ->
        let e = Tid.create () in
        let incoming =
          List.map ps ~f:(fun (v, ins) ->
              match List.find ins ~f:(fun (_, l) -> String.equal l pred) with
              | Some (x, _) -> (v, x)
              | None -> raise (Error (sprintf "no phi from %s to %s" pred succ)))
        in
        (* the copies are parallel, so they go through the temporaries,
           only if a value reads another phi of the edge *)
        let parallel =
          List.exists incoming ~f:(fun (v, x) ->
              Set.exists (Exp.free_vars x) ~f:(fun u ->
                  (not (Var.equal u v))
                  && List.exists incoming ~f:(fun (w, _) -> Var.equal u w)))
        in
        let defs =
          if not parallel then
            List.map incoming ~f:(fun (v, x) -> Def.create v x)
          else
            let temps =
              List.map incoming ~f:(fun (v, x) ->
                  ( v,
                    Var.create ~fresh:true ~is_virtual:true "phi" (Var.typ v),
                    x ))
            in
            List.map temps ~f:(fun (_, t, x) -> Def.create t x)
            @ List.map temps ~f:(fun (v, t, _) -> Def.create v (Bil.var t))
        in
        edges :=
          Blk.create ~tid:e ~defs
            ~jmps:[ Jmp.create_goto (Direct (tid succ)) ]
            ()
          :: !edges;
        e
  in
  let goto ?cond pred succ =
    Jmp.create_goto ?cond (Direct (target pred succ))
  in
  let rebuild k arg cont =
    let j = fst (Hashtbl.find_exn exits k) in
    let indirect () =
      let target =
        Option.value_exn arg ~message:"the indirect jump without a target"
      in
      (* the targets of the opaque calls are of 64 bits *)
      Indirect
        (match Var.typ mem with
        | Mem (a, _) when Size.in_bits a < 64 ->
            Bil.(cast low (Size.in_bits a) target)
        | _ -> target)
    in
    let jmp =
      match Jmp.kind j with
      | Call c ->
          let target =
            match Call.target c with Indirect _ -> indirect () | t -> t
          in
          (* the call, that doesn't return, continues by the address *)
          let return =
            match Call.return c with
            | None -> None
            | Some _ -> Option.map cont ~f:(fun t -> Direct t)
          in
          Jmp.create_call (Call.create ?return ~target ())
      | Goto (Indirect _) -> Jmp.create_goto (indirect ())
      | Goto l -> Jmp.create_goto l
      | Ret (Indirect _) -> Jmp.create_ret (indirect ())
      | Ret l -> Jmp.create_ret l
      | Int (n, _) -> Jmp.create_int n (Option.value_exn cont)
    in
    Term.with_attrs jmp (Term.attrs j)
  in
  let blks =
    List.concat_map blocks ~f:(fun b ->
        (* the opaque calls end the blocks of BIR, which continue in the next *)
        let rec split tid defs = function
          | [] ->
              let jmps =
                match b.terminator with
                | Br l -> [ goto b.label l ]
                | Cbr (c, x, y) -> [ goto ~cond:c b.label x; goto b.label y ]
                | Switch (v, w, cases, d) ->
                    List.map cases ~f:(fun (c, l) ->
                        goto ~cond:Bil.(v = int c) b.label l)
                    @ [ goto b.label d ]
                    |> fun js ->
                    ignore w;
                    js
                | Unreachable -> raise (Error "the unreachable code")
                | Return -> raise (Error "the return")
              in
              [ Blk.create ~tid ~defs:(List.rev defs) ~jmps () ]
          | Leave (k, arg) :: rest ->
              let continues =
                (not (List.is_empty rest))
                || match b.terminator with Unreachable -> false | _ -> true
              in
              if continues then (
                let next = Tid.create () in
                Option.iter (return_address k) ~f:(fun a ->
                    Hashtbl.set addresses ~key:next ~data:a);
                Blk.create ~tid ~defs:(List.rev defs)
                  ~jmps:[ rebuild k arg (Some next) ]
                  ()
                :: split next [] rest)
              else
                [
                  Blk.create ~tid ~defs:(List.rev defs)
                    ~jmps:[ rebuild k arg None ]
                    ();
                ]
          | Assign (v, e) :: rest -> split tid (Def.create v e :: defs) rest
          | Store (a, v, s) :: rest ->
              split tid
                (Def.create mem
                   (Bil.store ~mem:(Bil.var mem) ~addr:a v LittleEndian s)
                :: defs)
                rest
        in
        split (tid b.label) [] b.items)
  in
  let blks =
    List.map
      (blks @ List.rev !edges)
      ~f:(fun b ->
        match Hashtbl.find addresses (Term.tid b) with
        | Some a -> Term.set_attr b address a
        | None -> b)
  in
  let raised =
    Sub.create ~tid:(Term.tid sub) ~name:(Sub.name sub)
      ~args:(Term.enum arg_t sub |> Seq.to_list)
      ~blks ()
  in
  Term.with_attrs raised (Term.attrs sub)

let memory_of sub =
  let mem = ref None in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun b ->
      Term.enum def_t b
      |> Seq.iter ~f:(fun d ->
          if Option.is_none (width (Def.lhs d)) then mem := Some (Def.lhs d);
          Set.iter
            (Exp.free_vars (Def.rhs d))
            ~f:(fun v -> if Option.is_none (width v) then mem := Some v)));
  Option.value !mem ~default:(Var.create "mem" (Mem (`r64, `r8)))

let run_opt ~opt ~pipeline input =
  let dir = Stdlib.Filename.temp_dir "bap-recompile" "" in
  let src = Filename.concat dir "in.ll"
  and dst = Filename.concat dir "out.ll" in
  Out_channel.write_all src ~data:input;
  let cmd =
    sprintf "%s -S %s %s -o %s" (Filename.quote opt)
      (Filename.quote ("-passes=" ^ pipeline))
      (Filename.quote src) (Filename.quote dst)
  in
  let status = Stdlib.Sys.command cmd in
  let output = if status = 0 then Some (In_channel.read_all dst) else None in
  List.iter [ src; dst ] ~f:(fun f -> try Stdlib.Sys.remove f with _ -> ());
  (try Stdlib.Sys.rmdir dir with _ -> ());
  match output with
  | Some text -> text
  | None -> invalid_argf "%s failed with %d" cmd status ()

(* the subs, optimized by the [pipeline] of LLVM, in one run of [opt], or
   the errors, why they can't be *)
let optimize_subs ~opt ~pipeline subs =
  let out = Buffer.create 65536 in
  let registers =
    List.fold subs ~init:String.Map.empty ~f:(fun m s ->
        Set.fold (vars_of_sub s) ~init:m ~f:(fun m v ->
            if Var.is_physical v then
              Map.set m ~key:(mangle (Var.name v)) ~data:v
            else m))
  in
  Map.iteri registers ~f:(fun ~key ~data ->
      bprintf out "@bap_%s = external global %s\n" key
        (ty (Option.value_exn (width data))));
  let prog =
    {
      subs =
        Tid.Map.of_alist_reduce
          ~f:(fun s _ -> s)
          (List.map subs ~f:(fun s -> (Term.tid s, s)));
      externals = String.Set.empty;
      registers = Var.Set.of_list (Map.data registers);
    }
  in
  let funcs = List.mapi subs ~f:(fun n s -> (s, emit_func prog out n s)) in
  let optimized =
    if List.exists funcs ~f:(fun (_, f) -> Result.is_ok f) then
      Or_error.try_with (fun () ->
          functions (run_opt ~opt ~pipeline (Buffer.contents out)))
    else Ok String.Map.empty
  in
  List.map funcs ~f:(fun (sub, f) ->
      ( sub,
        match (f, optimized) with
        | Error msg, _ -> Or_error.error_string msg
        | Ok _, Error err -> Error err
        | Ok f, Ok optimized -> (
            match Map.find optimized f.name with
            | None -> Or_error.error_string "opt didn't write the function"
            | Some lines -> (
                let mem = memory_of f.sub in
                let module R = Raise (struct
                  let registers = registers
                  let mem = mem
                end) in
                match
                  R.blocks lines |> inline_values
                  |> raise_sub ~mem f.sub f.exits
                with
                | raised -> Ok raised
                | exception (Parse.Error msg | Unsupported msg) ->
                    Or_error.error_string msg
                | exception exn -> Or_error.of_exn exn)) ))
