open Core
open Bap_core_theory
open Bap.Std
module P = Bap_protobuf_ir

type fmt = Bil_proto.fmt

let required = Bil_proto.required

module Get = struct
  let tid = Tid.from_string_exn
  let var what v = Bil_proto.var_of_proto (required what v)
  let exp what e = Bil_proto.exp_of_proto (required what e)

  let label : P.label -> label = function
    | Direct t -> Direct (tid t)
    | Indirect e -> Indirect (Bil_proto.exp_of_proto e)

  let intent : P.intent -> intent = function
    | In -> In
    | Out -> Out
    | Both -> Both

  let jump : P.jump -> jmp_kind = function
    | Goto dst -> Goto (label dst)
    | Ret dst -> Ret (label dst)
    | Interrupt { number; return_tid; _ } ->
        Int (Int32.to_int_exn number, tid return_tid)
    | Call { target; return_label; _ } ->
        Call
          (Call.create
             ?return:(Option.map ~f:label return_label)
             ~target:(label (required "target" target))
             ())

  let arg (a : P.arg) =
    let intent = if P.arg_has_intent a then Some (intent a.intent) else None in
    Arg.create ~tid:(tid a.tid) ?intent (var "variable" a.lhs)
      (exp "expression" a.rhs)

  let def ({ tid = t; lhs; rhs; _ } : P.def) =
    Def.create ~tid:(tid t) (var "variable" lhs) (exp "expression" rhs)

  let phi ({ tid = t; lhs; values; _ } : P.phi) =
    List.map values ~f:(fun ({ tid = t; exp = e; _ } : P.phi_value) ->
        (tid t, exp "expression" e))
    |> Phi.of_list ~tid:(tid t) (var "variable" lhs)

  (* the jumps to the handlers of the interrupts have the vector as their
     alternative destination, which is a label with the number of the
     interrupt, see Jmp.create *)
  let vector jmp : P.jump -> jmp term = function
    | Interrupt { number; vector_tid; _ } when not (String.is_empty vector_tid)
      ->
        let vector = tid vector_tid in
        Toplevel.exec
          (KB.provide Theory.Label.ivec vector (Some (Int32.to_int_exn number)));
        Jmp.with_alt jmp (Some (Jmp.resolved vector))
    | _ -> jmp

  let jmp ({ tid = t; cond; kind; _ } : P.jmp) =
    let kind = required "kind" kind in
    vector
      (Jmp.create ~tid:(tid t) ~cond:(exp "condition" cond) (jump kind))
      kind

  let blk ({ tid = t; phis; defs; jmps; _ } : P.blk) =
    let b = Blk.Builder.create ~tid:(tid t) () in
    List.iter phis ~f:(fun x -> Blk.Builder.add_phi b (phi x));
    List.iter defs ~f:(fun x -> Blk.Builder.add_def b (def x));
    List.iter jmps ~f:(fun x -> Blk.Builder.add_jmp b (jmp x));
    Blk.Builder.result b

  let sub ({ tid = t; name; args; blks; _ } : P.sub) =
    let b = Sub.Builder.create ~tid:(tid t) ~name () in
    List.iter args ~f:(fun x -> Sub.Builder.add_arg b (arg x));
    List.iter blks ~f:(fun x -> Sub.Builder.add_blk b (blk x));
    Sub.Builder.result b

  let program ({ tid = t; subs; _ } : P.program) =
    let b = Program.Builder.create ~tid:(tid t) () in
    List.iter subs ~f:(fun x -> Program.Builder.add_sub b (sub x));
    Program.Builder.result b
end

module Put = struct
  let tid = Tid.to_string
  let exp = Bil_proto.exp_to_proto
  let var = Bil_proto.var_to_proto

  let label : label -> P.label = function
    | Direct t -> Direct (tid t)
    | Indirect e -> Indirect (exp e)

  let intent : intent -> P.intent = function
    | In -> In
    | Out -> Out
    | Both -> Both

  let vector jmp =
    match Option.map ~f:Jmp.resolve (Jmp.alt jmp) with
    | Some (First vector) -> Some (tid vector)
    | _ -> None

  let jump jmp : jmp_kind -> P.jump = function
    | Goto dst -> Goto (label dst)
    | Ret dst -> Ret (label dst)
    | Int (number, ret) ->
        Interrupt
          (P.make_interrupt ~number:(Int32.of_int_exn number)
             ~return_tid:(tid ret) ?vector_tid:(vector jmp) ())
    | Call c ->
        Call
          (P.make_call
             ~target:(label (Call.target c))
             ?return_label:(Option.map ~f:label (Call.return c))
             ())

  let arg a =
    P.make_arg
      ~tid:(tid (Term.tid a))
      ~lhs:(var (Arg.lhs a))
      ~rhs:(exp (Arg.rhs a))
      ?intent:(Option.map ~f:intent (Arg.intent a))
      ()

  let def d =
    P.make_def
      ~tid:(tid (Term.tid d))
      ~lhs:(var (Def.lhs d))
      ~rhs:(exp (Def.rhs d))
      ()

  let phi p =
    P.make_phi
      ~tid:(tid (Term.tid p))
      ~lhs:(var (Phi.lhs p))
      ~values:
        (Phi.values p
        |> Seq.map ~f:(fun (t, e) ->
            P.make_phi_value ~tid:(tid t) ~exp:(exp e) ())
        |> Seq.to_list)
      ()

  let jmp j =
    P.make_jmp
      ~tid:(tid (Term.tid j))
      ~cond:(exp (Jmp.cond j))
      ~kind:(jump j (Jmp.kind j))
      ()

  let terms cls f parent = Term.enum cls parent |> Seq.map ~f |> Seq.to_list

  let blk b =
    P.make_blk
      ~tid:(tid (Term.tid b))
      ~phis:(terms phi_t phi b) ~defs:(terms def_t def b)
      ~jmps:(terms jmp_t jmp b) ()

  let sub s =
    P.make_sub
      ~tid:(tid (Term.tid s))
      ~name:(Sub.name s) ~args:(terms arg_t arg s) ~blks:(terms blk_t blk s) ()

  let program p =
    P.make_program ~tid:(tid (Term.tid p)) ~subs:(terms sub_t sub p) ()
end

let codec encode_pb encode_json decode_pb decode_json put get =
  ( (fun fmt x -> Bil_proto.encode fmt encode_pb encode_json (put x)),
    fun fmt s -> get (Bil_proto.decode fmt decode_pb decode_json s) )

let program_to_string, program_of_string =
  codec P.encode_pb_program P.encode_json_program P.decode_pb_program
    P.decode_json_program Put.program Get.program

let sub_to_string, sub_of_string =
  codec P.encode_pb_sub P.encode_json_sub P.decode_pb_sub P.decode_json_sub
    Put.sub Get.sub

let blk_to_string, blk_of_string =
  codec P.encode_pb_blk P.encode_json_blk P.decode_pb_blk P.decode_json_blk
    Put.blk Get.blk

let arg_to_string, arg_of_string =
  codec P.encode_pb_arg P.encode_json_arg P.decode_pb_arg P.decode_json_arg
    Put.arg Get.arg

let phi_to_string, phi_of_string =
  codec P.encode_pb_phi P.encode_json_phi P.decode_pb_phi P.decode_json_phi
    Put.phi Get.phi

let def_to_string, def_of_string =
  codec P.encode_pb_def P.encode_json_def P.decode_pb_def P.decode_json_def
    Put.def Get.def

let jmp_to_string, jmp_of_string =
  codec P.encode_pb_jmp P.encode_json_jmp P.decode_pb_jmp P.decode_json_jmp
    Put.jmp Get.jmp
