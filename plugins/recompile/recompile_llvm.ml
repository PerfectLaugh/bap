(* the emitter of the programs of BIR as the modules of LLVM IR *)

open Core
open Bap.Std

exception Unsupported of string

let unsupported fmt = Format.kasprintf (fun msg -> raise (Unsupported msg)) fmt

(* the names of LLVM, which can't have the characters of the names of BIR,
   e.g., # of the virtual variables *)
let mangle name =
  String.map name ~f:(fun c ->
      if Char.is_alphanum c || Char.equal c '_' then c else '_')

let width var = match Var.typ var with Imm n -> Some n | Mem _ | Unk -> None
let ty n = sprintf "i%d" n
let global var = sprintf "@bap_%s" (mangle (Var.name var))

let local var =
  sprintf "%%r.%s%s"
    (if Var.is_virtual var then "t." else "")
    (mangle (Var.name var))

let label tid = sprintf "b.%s" (mangle (Tid.to_string tid))
let fn_name sub = sprintf "@f.%s" (mangle (Sub.name sub))

let addr_of term =
  Option.map (Term.get_attr term address) ~f:(fun a -> Word.to_int64_exn a)

let hex x = sprintf "u0x%Lx" x

(* the variables of the expressions, statements, and jumps of the sub *)
let vars_of_sub sub =
  let vars = ref Var.Set.empty in
  let add v = if Option.is_some (width v) then vars := Set.add !vars v in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      Term.enum def_t blk
      |> Seq.iter ~f:(fun def ->
          add (Def.lhs def);
          Set.iter (Exp.free_vars (Def.rhs def)) ~f:add);
      Term.enum jmp_t blk
      |> Seq.iter ~f:(fun jmp ->
          Set.iter (Exp.free_vars (Jmp.cond jmp)) ~f:add;
          let dst = function
            | Indirect e -> Set.iter (Exp.free_vars e) ~f:add
            | Direct _ -> ()
          in
          match Jmp.kind jmp with
          | Goto l | Ret l -> dst l
          | Call c ->
              dst (Call.target c);
              Option.iter (Call.return c) ~f:dst
          | Int _ -> ()));
  !vars

(* the arguments of the native calls, in the registers of System V *)
let native_args = [ "RDI"; "RSI"; "RDX"; "RCX"; "R8"; "R9" ]

type program = {
  subs : sub term Tid.Map.t;
  externals : String.Set.t;
  registers : Var.Set.t;
}

let is_external sub = Term.has_attr sub Sub.stub || Term.length blk_t sub = 0
let is_intrinsic sub = String.is_prefix (Sub.name sub) ~prefix:"intrinsic:"

(* the external sub, whose name BAP made up, e.g., of the stub of the PLT,
   that has no symbol, can't be called natively *)
let is_unnamed sub =
  match Term.get_attr sub address with
  | None -> false
  | Some addr ->
      String.equal (Sub.name sub)
        (sprintf "sub_%s"
           (Word.string_of_value ~hex:true addr |> String.lowercase))

(* the emitter of a function, whose instructions are in [buf] *)
module Emit (S : sig
  val prog : program
  val sub : sub term
  val buf : Buffer.t
end) =
struct
  open S

  let temps = ref 0
  let labels = ref 0

  let line fmt =
    Printf.ksprintf
      (fun s ->
        Buffer.add_string buf s;
        Buffer.add_char buf '\n')
      fmt

  let fresh () =
    incr temps;
    sprintf "%%t%d" !temps

  let fresh_label prefix =
    incr labels;
    sprintf "%s%d" prefix !labels

  let instr fmt =
    Printf.ksprintf
      (fun s ->
        let t = fresh () in
        line "  %s = %s" t s;
        t)
      fmt

  let vars = vars_of_sub sub
  let registers = Set.filter vars ~f:Var.is_physical

  let sync_out () =
    Set.iter registers ~f:(fun v ->
        let w = Option.value_exn (width v) in
        let x = instr "load %s, ptr %s" (ty w) (local v) in
        line "  store %s %s, ptr %s" (ty w) x (global v))

  let sync_in () =
    Set.iter registers ~f:(fun v ->
        let w = Option.value_exn (width v) in
        let x = instr "load %s, ptr %s" (ty w) (global v) in
        line "  store %s %s, ptr %s" (ty w) x (local v))

  (* converts the value [x] of the width [w] to the width [n] *)
  let resize ?(signed = false) x w n =
    if w = n then x
    else if w > n then instr "trunc %s %s to %s" (ty w) x (ty n)
    else
      instr "%s %s %s to %s" (if signed then "sext" else "zext") (ty w) x (ty n)

  (* the memory is in the order of the bytes of the host, so the values
     of the big endian are swapped *)
  let swap endian n x =
    match endian with
    | BigEndian when n > 8 ->
        instr "call %s @llvm.bswap.%s(%s %s)" (ty n) (ty n) (ty n) x
    | _ -> x

  let pointer addr w =
    let addr = resize addr w 64 in
    instr "inttoptr i64 %s to ptr" addr

  (* the shifts of BIL saturate, i.e., the shift by the width or more is
     zero, or the sign, while it is poison in LLVM *)
  let shift op x w a wa =
    let wide = max w wa in
    let a' = resize a wa wide in
    let big = instr "icmp uge %s %s, %d" (ty wide) a' w in
    let a = resize a' wide w in
    let r = instr "%s %s %s, %s" op (ty w) x a in
    let saturated =
      if String.equal op "ashr" then instr "ashr %s %s, %d" (ty w) x (w - 1)
      else "0"
    in
    instr "select i1 %s, %s %s, %s %s" big (ty w) saturated (ty w) r

  let rec exp env (e : exp) : string * int =
    match e with
    | Var v -> (
        match Map.find env (Var.name v) with
        | Some x -> x
        | None -> (
            match width v with
            | Some w -> (instr "load %s, ptr %s" (ty w) (local v), w)
            | None -> unsupported "the memory %a as a value" Var.pp v))
    | Int w ->
        let n = Word.bitwidth w in
        (sprintf "u0x%s" (Word.string_of_value ~hex:true w), n)
    | Load (m, a, endian, size) ->
        memory env m;
        let a, wa = exp env a in
        let p = pointer a wa in
        let n = Size.in_bits size in
        (swap endian n (instr "load %s, ptr %s, align 1" (ty n) p), n)
    | Store _ -> unsupported "the store as a value"
    | BinOp (op, x, y) -> binop env op x y
    | UnOp (NEG, x) ->
        let x, w = exp env x in
        (instr "sub %s 0, %s" (ty w) x, w)
    | UnOp (NOT, x) ->
        let x, w = exp env x in
        (instr "xor %s %s, -1" (ty w) x, w)
    | Cast (kind, n, x) -> (
        let x, w = exp env x in
        match kind with
        | UNSIGNED -> (resize x w n, n)
        | SIGNED -> (resize ~signed:true x w n, n)
        | LOW -> (resize x w n, n)
        | HIGH ->
            let x =
              if w > n then instr "lshr %s %s, %d" (ty w) x (w - n) else x
            in
            (resize x w n, n))
    | Let (v, x, body) ->
        let x = exp env x in
        exp (Map.set env ~key:(Var.name v) ~data:x) body
    | Unknown (_, Imm n) -> ("0", n)
    | Unknown _ -> unsupported "the unknown memory"
    | Ite (c, x, y) ->
        let c, wc = exp env c in
        let c = resize c wc 1 in
        let x, w = exp env x in
        let y, wy = exp env y in
        let y = resize y wy w in
        (instr "select i1 %s, %s %s, %s %s" c (ty w) x (ty w) y, w)
    | Extract (hi, lo, x) ->
        let x, w = exp env x in
        let n = hi - lo + 1 in
        let x = if lo > 0 then instr "lshr %s %s, %d" (ty w) x lo else x in
        (resize x w n, n)
    | Concat (x, y) ->
        let x, wx = exp env x in
        let y, wy = exp env y in
        let n = wx + wy in
        let x = resize x wx n and y = resize y wy n in
        let x = instr "shl %s %s, %d" (ty n) x wy in
        (instr "or %s %s, %s" (ty n) x y, n)

  and binop env op x y =
    let x, wx = exp env x in
    let y, wy = exp env y in
    match op with
    | LSHIFT -> (shift "shl" x wx y wy, wx)
    | RSHIFT -> (shift "lshr" x wx y wy, wx)
    | ARSHIFT -> (shift "ashr" x wx y wy, wx)
    | _ -> (
        let w = max wx wy in
        let x = resize x wx w and y = resize y wy w in
        let arith name = (instr "%s %s %s, %s" name (ty w) x y, w) in
        let cmp name = (instr "icmp %s %s %s, %s" name (ty w) x y, 1) in
        match op with
        | PLUS -> arith "add"
        | MINUS -> arith "sub"
        | TIMES -> arith "mul"
        | DIVIDE -> arith "udiv"
        | SDIVIDE -> arith "sdiv"
        | MOD -> arith "urem"
        | SMOD -> arith "srem"
        | AND -> arith "and"
        | OR -> arith "or"
        | XOR -> arith "xor"
        | EQ -> cmp "eq"
        | NEQ -> cmp "ne"
        | LT -> cmp "ult"
        | LE -> cmp "ule"
        | SLT -> cmp "slt"
        | SLE -> cmp "sle"
        | LSHIFT | RSHIFT | ARSHIFT -> assert false)

  (* the stores of the memory expression, in their order *)
  and memory env (m : exp) =
    match m with
    | Var _ -> ()
    | Store (m, a, v, endian, size) ->
        memory env m;
        let a, wa = exp env a in
        let v, wv = exp env v in
        let n = Size.in_bits size in
        let v = swap endian n (resize v wv n) in
        let p = pointer a wa in
        line "  store %s %s, ptr %s, align 1" (ty n) v p
    | _ -> unsupported "the memory %a" Exp.pp m

  let def d =
    let v = Def.lhs d in
    match width v with
    | None -> memory String.Map.empty (Def.rhs d)
    | Some w ->
        let x, wx = exp String.Map.empty (Def.rhs d) in
        line "  store %s %s, ptr %s" (ty w) (resize x wx w) (local v)

  (* the addresses of the blocks of the sub, that the indirect jumps
     inside of it may reach *)
  let blocks =
    Term.enum blk_t sub
    |> Seq.filter_map ~f:(fun blk ->
        Option.map (addr_of blk) ~f:(fun a -> (a, Term.tid blk)))
    |> Seq.to_list
    |> List.dedup_and_sort ~compare:(fun (x, _) (y, _) -> Int64.compare x y)

  let is_block tid = Option.is_some (Term.find blk_t sub tid)

  (* the indirect jump, which returns, if it jumps to the return address,
     continues in a block of the sub, or in the dispatcher otherwise *)
  let jump_to target =
    let t, w = exp String.Map.empty target in
    let t = resize t w 64 in
    let back = fresh_label "ret" and other = fresh_label "jmp" in
    let far = fresh_label "far" in
    let is_return = instr "icmp eq i64 %s, %%ret" t in
    line "  br i1 %s, label %%%s, label %%%s" is_return back other;
    line "%s:" back;
    sync_out ();
    line "  ret void";
    line "%s:" other;
    line "  switch i64 %s, label %%%s [" t far;
    List.iter blocks ~f:(fun (a, tid) ->
        line "    i64 %s, label %%%s" (hex a) (label tid));
    line "  ]";
    line "%s:" far;
    sync_out ();
    line "  call void @bap_dispatch(i64 %s, i64 %%ret)" t;
    line "  ret void"

  let return_address = function
    | Some (Direct tid) -> (
        match Term.find blk_t sub tid with
        | Some blk -> (
            match addr_of blk with
            | Some a -> hex a
            | None ->
                unsupported "the return to %a without an address" Tid.pp tid)
        | None -> unsupported "the return to %a outside of the sub" Tid.pp tid)
    | Some (Indirect _) -> unsupported "the indirect return"
    | None -> "%ret"

  let continue_at = function
    | Some (Direct tid) -> line "  br label %%%s" (label tid)
    | Some (Indirect e) -> jump_to e
    | None ->
        (* the call, that doesn't return, is the tail call *)
        line "  ret void"

  let native_call name =
    sync_out ();
    let args =
      List.map native_args ~f:(fun r ->
          sprintf "i64 %s" (instr "load i64, ptr @bap_%s" r))
    in
    let result = instr "call i64 @%s(%s)" name (String.concat ~sep:", " args) in
    line "  store i64 %s, ptr @bap_RAX" result;
    (* the native function returns as the ret, that pops the return
       address, that the call pushed *)
    let sp = instr "load i64, ptr @bap_RSP" in
    let sp = instr "add i64 %s, 8" sp in
    line "  store i64 %s, ptr @bap_RSP" sp;
    sync_in ()

  let call c =
    let return = Call.return c in
    match Call.target c with
    | Direct tid -> (
        match Map.find prog.subs tid with
        | None -> unsupported "the call of %a, which isn't a sub" Tid.pp tid
        | Some callee when is_intrinsic callee ->
            sync_out ();
            line "  call void @bap_rt_intrinsic(ptr @name.%s)"
              (mangle (Sub.name callee));
            line "  unreachable"
        | Some callee when is_external callee && is_unnamed callee ->
            sync_out ();
            line "  call void @bap_rt_unknown(i64 %s)"
              (hex (Option.value (addr_of callee) ~default:0L));
            line "  unreachable"
        | Some callee when is_external callee ->
            native_call (Sub.name callee);
            continue_at return
        | Some callee ->
            let ret = return_address return in
            sync_out ();
            line "  call void %s(i64 %s)" (fn_name callee) ret;
            sync_in ();
            continue_at return)
    | Indirect target -> (
        match return with
        | None -> jump_to target
        | Some _ ->
            let ret = return_address return in
            let t, w = exp String.Map.empty target in
            let t = resize t w 64 in
            sync_out ();
            line "  call void @bap_dispatch(i64 %s, i64 %s)" t ret;
            sync_in ();
            continue_at return)

  let transfer jmp =
    match Jmp.kind jmp with
    | Goto (Direct tid) | Ret (Direct tid) -> (
        if is_block tid then line "  br label %%%s" (label tid)
        else
          match Map.find prog.subs tid with
          | Some callee ->
              sync_out ();
              line "  call void %s(i64 %%ret)" (fn_name callee);
              line "  ret void"
          | None -> unsupported "the jump to %a" Tid.pp tid)
    | Goto (Indirect e) | Ret (Indirect e) -> jump_to e
    | Call c -> call c
    | Int (n, ret) ->
        sync_out ();
        line "  call void @bap_rt_interrupt(i64 %d)" n;
        sync_in ();
        line "  br label %%%s" (label ret)

  let jumps blk =
    let rec loop = function
      | [] ->
          line "  call void @bap_rt_unknown(i64 0)";
          line "  unreachable"
      | jmp :: rest -> (
          match Jmp.cond jmp with
          | Int w when Word.is_one w -> transfer jmp
          | cond ->
              let c, w = exp String.Map.empty cond in
              let c = resize c w 1 in
              let taken = fresh_label "taken" and next = fresh_label "next" in
              line "  br i1 %s, label %%%s, label %%%s" c taken next;
              line "%s:" taken;
              transfer jmp;
              line "%s:" next;
              loop rest)
    in
    loop (Term.enum jmp_t blk |> Seq.to_list)

  let body () =
    Set.iter vars ~f:(fun v ->
        line "  %s = alloca %s" (local v) (ty (Option.value_exn (width v))));
    sync_in ();
    match Term.first blk_t sub with
    | None -> line "  ret void"
    | Some first ->
        line "  br label %%%s" (label (Term.tid first));
        Term.enum blk_t sub
        |> Seq.iter ~f:(fun blk ->
            line "%s:" (label (Term.tid blk));
            Term.enum def_t blk |> Seq.iter ~f:def;
            jumps blk)
end

let emit_sub prog out sub =
  let buf = Buffer.create 4096 in
  let module E = Emit (struct
    let prog = prog
    let sub = sub
    let buf = buf
  end) in
  bprintf out "define internal void %s(i64 %%ret) {\nentry:\n" (fn_name sub);
  (match E.body () with
  | () -> Buffer.add_buffer out buf
  | exception Unsupported msg ->
      eprintf "bap-recompile: can't recompile %s: %s\n%!" (Sub.name sub) msg;
      let addr = Option.value (addr_of sub) ~default:0L in
      bprintf out "  call void @bap_rt_unsupported(i64 %s)\n  unreachable\n"
        (hex addr));
  bprintf out "}\n\n"

let emit ~entry ~path prog =
  let out = Buffer.create 65536 in
  let internals =
    Map.data prog.subs
    |> List.filter ~f:(fun s -> not (is_external s || is_intrinsic s))
  in
  bprintf out "; recompiled by bap from %s\n\n" path;
  bprintf out "@bap_image_path = constant [%d x i8] c\"%s\\00\"\n\n"
    (String.length path + 1)
    path;
  Set.iter prog.registers ~f:(fun v ->
      bprintf out "%s = global %s 0\n" (global v)
        (ty (Option.value_exn (width v))));
  List.iter ("RAX" :: "RSP" :: native_args) ~f:(fun r ->
      if
        not
          (Set.exists prog.registers ~f:(fun v -> String.equal (Var.name v) r))
      then bprintf out "@bap_%s = global i64 0\n" r);
  Buffer.add_char out '\n';
  Map.iter prog.subs ~f:(fun sub ->
      if is_intrinsic sub then
        let name = Sub.name sub in
        bprintf out "@name.%s = private constant [%d x i8] c\"%s\\00\"\n"
          (mangle name)
          (String.length name + 1)
          name);
  Set.iter prog.externals ~f:(fun name ->
      bprintf out "declare i64 @%s(...)\n" name);
  bprintf out
    "declare void @bap_rt_unknown(i64) noreturn\n\
     declare void @bap_rt_unsupported(i64) noreturn\n\
     declare void @bap_rt_intrinsic(ptr) noreturn\n\
     declare void @bap_rt_interrupt(i64)\n\n";
  List.iter internals ~f:(emit_sub prog out);
  (* the functions by their addresses, for the indirect calls *)
  bprintf out "define void @bap_dispatch(i64 %%t, i64 %%ret) {\nentry:\n";
  bprintf out "  switch i64 %%t, label %%unknown [\n";
  let entries =
    List.filter_map internals ~f:(fun s ->
        Option.map (addr_of s) ~f:(fun a -> (a, s)))
    |> List.dedup_and_sort ~compare:(fun (x, _) (y, _) -> Int64.compare x y)
  in
  List.iter entries ~f:(fun (a, s) ->
      bprintf out "    i64 %s, label %%%s\n" (hex a)
        (String.drop_prefix (fn_name s) 1));
  bprintf out "  ]\n";
  List.iter entries ~f:(fun (_, s) ->
      bprintf out "%s:\n  call void %s(i64 %%ret)\n  ret void\n"
        (String.drop_prefix (fn_name s) 1)
        (fn_name s));
  bprintf out
    "unknown:\n  call void @bap_rt_unknown(i64 %%t)\n  unreachable\n}\n\n";
  (match List.find internals ~f:(fun s -> String.equal (Sub.name s) entry) with
  | None -> invalid_argf "the program has no subroutine %s" entry ()
  | Some s ->
      bprintf out
        "define void @bap_start(i64 %%ret) {\n\
        \  call void %s(i64 %%ret)\n\
        \  ret void\n\
         }\n"
        (fn_name s));
  Buffer.contents out

let program_of proj =
  let prog = Project.program proj in
  let subs =
    Term.enum sub_t prog
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun subs s ->
        Map.set subs ~key:(Term.tid s) ~data:s)
  in
  let externals =
    Map.data subs
    |> List.filter ~f:(fun s ->
        is_external s && not (is_intrinsic s || is_unnamed s))
    |> List.map ~f:Sub.name |> String.Set.of_list
  in
  let registers =
    Map.data subs
    |> List.filter ~f:(fun s -> not (is_external s || is_intrinsic s))
    |> List.fold ~init:Var.Set.empty ~f:(fun regs s ->
        Set.union regs (Set.filter (vars_of_sub s) ~f:Var.is_physical))
  in
  { subs; externals; registers }

let main ~entry ~output proj =
  let path =
    match Project.get proj filename with
    | Some file -> Caml_unix.realpath file
    | None -> invalid_arg "the project has no file"
  in
  let ir = emit ~entry ~path (program_of proj) in
  Out_channel.write_all output ~data:ir;
  Out_channel.write_all (output ^ ".rt.c") ~data:Recompile_runtime.source;
  proj
