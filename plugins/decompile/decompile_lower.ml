open Core
open Bap.Std
open Bap_core_theory
module Ast = Decompile_ast
module Cfg = Decompile_cfg
module Types = Decompile_types
module Ssa = Decompile_ssa

let sanitize prefix name =
  let name =
    String.map name ~f:(fun c ->
        if Char.is_alphanum c || Char.equal c '_' then c else '_')
  in
  sprintf "%s%s" prefix name

let binop (operation : binop) =
  match operation with
  | PLUS -> "+"
  | MINUS -> "-"
  | TIMES -> "*"
  | DIVIDE | SDIVIDE -> "/"
  | MOD | SMOD -> "%"
  | LSHIFT -> "<<"
  | RSHIFT | ARSHIFT -> ">>"
  | AND -> "&"
  | OR -> "|"
  | XOR -> "^"
  | EQ -> "=="
  | NEQ -> "!="
  | LT | SLT -> "<"
  | LE | SLE -> "<="

type env = {
  target : Theory.Target.t;
  types : Types.t;
  program : program term;
  sub : sub term;
  normalized : Ssa.t;
  high : Decompile_high.t;
  cfg : Cfg.t option;
  mutable variables : Ast.variable Var.Map.t;
  mutable locals : Ast.variable list;
  mutable fresh : int;
  slots : (int * int, Ast.variable) Hashtbl.Poly.t;
  names : string Tid.Map.t;
  addresses : tid Word.Map.t;
  mutable final_frames : Bap_recompile.Frame.state Tid.Map.t;
  mutable final_versions : var Var.Map.t Tid.Map.t;
  mutable final_expressions : exp Var.Map.t Tid.Map.t;
}

let variable env var =
  let var = Decompile_high.representative env.high var in
  match Map.find env.variables var with
  | Some variable -> variable
  | None ->
      let id = env.fresh in
      env.fresh <- id + 1;
      let variable =
        {
          Ast.id;
          name = sanitize "v_" (Var.to_string var);
          typ = Types.typ env.types env.sub var;
        }
      in
      env.variables <- Map.set env.variables ~key:var ~data:variable;
      variable

let make_local env name typ =
  let id = env.fresh in
  env.fresh <- id + 1;
  let local = { Ast.id; name; typ } in
  env.locals <- env.locals @ [ local ];
  local

let slot_variable env offset bits =
  match Hashtbl.find env.slots (offset, bits) with
  | Some variable -> variable
  | None ->
      let name =
        if offset < 0 then sprintf "local_%x" (-offset)
        else sprintf "local_%x" offset
      in
      let variable = make_local env name (Ast.Int (bits, Ast.Unknown_sign)) in
      Hashtbl.set env.slots ~key:(offset, bits) ~data:variable;
      variable

let frame_slot env state addr bits =
  Option.bind env.normalized.frame ~f:(fun frame ->
      Option.bind state ~f:(fun state ->
          Bap_recompile.Frame.slot frame state addr bits))

let rec returned_register = function
  | Bil.Var var -> Some var
  | Bil.Cast (_, _, exp) | Bil.Extract (_, _, exp) -> returned_register exp
  | _ -> None

let return_variable env =
  let find_name name =
    Map.to_alist env.variables
    |> List.find_map ~f:(fun (var, _) ->
        if String.equal (Var.name var) name then Some (Var.base var) else None)
  in
  let from_arg =
    Term.enum arg_t env.sub
    |> Seq.find_map ~f:(fun arg ->
        match Arg.intent arg with
        | Some Out | Some Both -> (
            match returned_register (Arg.rhs arg) with
            | None -> None
            | Some var -> find_name (Var.name var))
        | _ -> None)
  in
  match from_arg with
  | Some var -> Some var
  | None -> (
      match Types.return_register env.target env.sub with
      | None -> None
      | Some reg -> find_name (Var.name reg))

let input_args sub =
  Term.enum arg_t sub |> Seq.to_list
  |> List.filter ~f:(fun arg ->
      match Arg.intent arg with Some Out -> false | _ -> true)

let expression_width exp =
  match Type.infer exp with Ok (Type.Imm bits) -> Some bits | _ -> None

let constant bits value =
  {
    Ast.node = Ast.Const (Word.of_int ~width:bits value);
    typ = Ast.Int (bits, Ast.Unknown_sign);
  }

let cast typ expression =
  { expression with Ast.node = Ast.Cast (typ, expression) }

let logical_shift expression bits amount =
  if amount = 0 then expression
  else
    {
      Ast.node =
        Ast.Binary
          ( ">>",
            cast (Ast.Int (bits, Ast.Unsigned)) expression,
            constant bits amount );
      typ = Ast.Int (bits, Ast.Unsigned);
    }

let rec lower_exp env state exp =
  let typ = Types.expression env.types env.sub exp in
  let expr node = { Ast.node; typ } in
  let lower = lower_exp env state in
  match exp with
  | Bil.Var var -> Ast.var (variable env var)
  | Bil.Int value -> expr (Ast.Const value)
  | Bil.Load (Bil.Var memory, addr, endian, size) -> (
      let bits = Size.in_bits size in
      match frame_slot env state addr bits with
      | Some offset -> Ast.var (slot_variable env offset bits)
      | None -> (
          match endian with
          | LittleEndian -> lower_load env state addr bits typ
          | BigEndian ->
              expr
                (Ast.Machine
                   ( sprintf "bir_load_be%d" bits,
                     [ lower (Bil.Var memory); lower addr ] ))))
  | Bil.Load (mem, addr, endian, size) ->
      let name =
        sprintf "bir_load_%s%d"
          (match endian with LittleEndian -> "le" | BigEndian -> "be")
          (Size.in_bits size)
      in
      expr (Ast.Machine (name, [ lower mem; lower addr ]))
  | Bil.Store (mem, addr, value, endian, size) ->
      let name =
        sprintf "bir_store_%s%d"
          (match endian with LittleEndian -> "le" | BigEndian -> "be")
          (Size.in_bits size)
      in
      expr (Ast.Machine (name, [ lower mem; lower addr; lower value ]))
  | Bil.BinOp (op, x, y) ->
      let x' = lower x and y' = lower y in
      let signed =
        match op with
        | SDIVIDE | SMOD | SLT | SLE | ARSHIFT -> true
        | _ -> false
      in
      let signed exp =
        if signed then
          match exp.Ast.typ with
          | Ast.Int (bits, _) ->
              { exp with node = Ast.Cast (Ast.Int (bits, Ast.Signed), exp) }
          | _ -> exp
        else exp
      in
      expr (Ast.Binary (binop op, signed x', signed y'))
  | Bil.UnOp (NEG, x) -> expr (Ast.Unary ("-", lower x))
  | Bil.UnOp (NOT, x) ->
      let operator =
        match typ with Ast.Bool | Ast.Int (1, _) -> "!" | _ -> "~"
      in
      expr (Ast.Unary (operator, lower x))
  | Bil.Cast (SIGNED, bits, x) ->
      expr (Ast.Cast (Ast.Int (bits, Ast.Signed), lower x))
  | Bil.Cast ((UNSIGNED | LOW), bits, x) ->
      expr (Ast.Cast (Ast.Int (bits, Ast.Unknown_sign), lower x))
  | Bil.Cast (HIGH, bits, x) ->
      let source = Option.value (expression_width x) ~default:bits in
      expr
        (Ast.Cast
           ( Ast.Int (bits, Ast.Unknown_sign),
             logical_shift (lower x) source (source - bits) ))
  | Bil.Let (var, value, body) ->
      expr
        (Ast.Machine
           ("bir_let", [ Ast.var (variable env var); lower value; lower body ]))
  | Bil.Unknown (description, _) ->
      let name = sanitize "bir_unknown_" description in
      expr (Ast.Machine (name, []))
  | Bil.Ite (c, x, y) -> expr (Ast.Conditional (lower c, lower x, lower y))
  | Bil.Extract (hi, lo, x) ->
      let source = Option.value (expression_width x) ~default:(hi + 1) in
      expr
        (Ast.Cast
           ( Ast.Int (hi - lo + 1, Ast.Unknown_sign),
             logical_shift (lower x) source lo ))
  | Bil.Concat (x, y) -> lower_concat env state exp x y

and lower_concat env state exp x y =
  let result = Option.value (expression_width exp) ~default:0 in
  let right = Option.value (expression_width y) ~default:0 in
  let typ = Ast.Int (result, Ast.Unknown_sign) in
  let left = cast typ (lower_exp env state x) in
  let right_value = cast typ (lower_exp env state y) in
  {
    Ast.node =
      Ast.Cast
        ( typ,
          {
            Ast.node =
              Ast.Binary
                ( "|",
                  {
                    Ast.node = Ast.Binary ("<<", left, constant result right);
                    typ;
                  },
                  right_value );
            typ;
          } );
    typ;
  }

and lower_load env state addr bits typ =
  let base = Types.address addr in
  match base with
  | Some (var, offset) -> (
      let pointer = Ast.var (variable env var) in
      match Types.typ env.types env.sub var with
      | Ast.Pointer (Ast.Structure _) when offset >= 0 ->
          {
            Ast.node = Ast.Field (pointer, sprintf "field_%x" offset, offset);
            typ;
          }
      | Ast.Pointer (Ast.Array _) when offset = 0 ->
          {
            Ast.node =
              Ast.Index (pointer, lower_exp env state (Bil.Int (Word.zero 64)));
            typ;
          }
      | Ast.Pointer pointee ->
          let address =
            if offset = 0 then pointer
            else
              {
                Ast.node =
                  Ast.Binary
                    ( "+",
                      pointer,
                      {
                        Ast.node = Ast.Const (Word.of_int ~width:64 offset);
                        typ = Ast.Int (64, Ast.Signed);
                      } );
                typ = Ast.Pointer pointee;
              }
          in
          { Ast.node = Ast.Deref address; typ }
      | _ ->
          let address =
            cast
              (Ast.Pointer (Ast.Int (bits, Ast.Unknown_sign)))
              (lower_exp env state addr)
          in
          { Ast.node = Ast.Deref address; typ })
  | None ->
      let address =
        cast
          (Ast.Pointer (Ast.Int (bits, Ast.Unknown_sign)))
          (lower_exp env state addr)
      in
      { Ast.node = Ast.Deref address; typ }

let rec memory_chain exp =
  match exp with
  | Bil.Store (mem, addr, value, endian, size) ->
      let stores, initial = memory_chain mem in
      (stores @ [ (addr, value, endian, size) ], initial)
  | _ -> ([], exp)

let lower_def env state def =
  let lhs = Def.lhs def in
  match Var.typ lhs with
  | Type.Mem _ ->
      let stores, initial = memory_chain (Def.rhs def) in
      let memory = ref (lower_exp env state initial) in
      let statements =
        List.concat_map stores ~f:(fun (addr, value, endian, size) ->
            let bits = Size.in_bits size in
            match frame_slot env state addr bits with
            | Some offset ->
                [
                  Ast.Assign
                    ( Ast.var (slot_variable env offset bits),
                      lower_exp env state value );
                ]
            | None -> (
                match endian with
                | LittleEndian ->
                    let pointer =
                      cast
                        (Ast.Pointer (Ast.Int (bits, Ast.Unknown_sign)))
                        (lower_exp env state addr)
                    in
                    [
                      Ast.Assign
                        ( {
                            Ast.node = Ast.Deref pointer;
                            typ = Ast.Int (bits, Ast.Unknown_sign);
                          },
                          lower_exp env state value );
                    ]
                | BigEndian ->
                    let name = sprintf "bir_store_be%d" bits in
                    let next =
                      {
                        Ast.node =
                          Ast.Machine
                            ( name,
                              [
                                !memory;
                                lower_exp env state addr;
                                lower_exp env state value;
                              ] );
                        typ = Ast.Unknown 0;
                      }
                    in
                    memory := next;
                    []))
      in
      if Exp.equal (Bil.var lhs) initial then statements
      else statements @ [ Ast.Assign (Ast.var (variable env lhs), !memory) ]
  | _ ->
      [
        Ast.Assign
          (Ast.var (variable env lhs), lower_exp env state (Def.rhs def));
      ]

let lower_block env blk =
  let frame_state =
    ref
      (Option.map env.normalized.frame ~f:(fun frame ->
           Bap_recompile.Frame.entry frame (Term.tid blk)))
  in
  let versions = ref Var.Map.empty in
  let expressions = ref Var.Map.empty in
  let statements =
    Term.enum def_t blk |> Seq.to_list
    |> List.concat_map ~f:(fun def ->
        let statements = lower_def env !frame_state def in
        versions :=
          Map.set !versions ~key:(Var.base (Def.lhs def)) ~data:(Def.lhs def);
        expressions :=
          Map.set !expressions ~key:(Var.base (Def.lhs def)) ~data:(Def.rhs def);
        Option.iter env.normalized.frame ~f:(fun frame ->
            Option.iter !frame_state ~f:(fun state ->
                frame_state := Some (Bap_recompile.Frame.step frame state def)));
        statements)
  in
  Option.iter !frame_state ~f:(fun state ->
      env.final_frames <-
        Map.set env.final_frames ~key:(Term.tid blk) ~data:state);
  env.final_versions <-
    Map.set env.final_versions ~key:(Term.tid blk) ~data:!versions;
  env.final_expressions <-
    Map.set env.final_expressions ~key:(Term.tid blk) ~data:!expressions;
  statements

let callee_tid env = function
  | Direct tid -> Some tid
  | Indirect (Bil.Int address) -> Map.find env.addresses address
  | Indirect _ -> None

let call_expression env state target signature arguments =
  let target_type = Ast.Function signature in
  let target =
    match callee_tid env target with
    | Some tid -> (
        match Map.find env.names tid with
        | Some name ->
            {
              Ast.node = Ast.Var { id = 0; name; typ = target_type };
              typ = target_type;
            }
        | None ->
            {
              Ast.node =
                Ast.Machine
                  (sprintf "bir_sub_%s" (sanitize "" (Tid.to_string tid)), []);
              typ = target_type;
            })
    | None -> (
        match target with
        | Direct _ -> assert false
        | Indirect exp -> lower_exp env state exp)
  in
  {
    Ast.node = Ast.Call { target; arguments; result = signature.Ast.return };
    typ = signature.Ast.return;
  }

let caller_block env jmp =
  Term.enum blk_t env.sub
  |> Seq.find ~f:(fun blk ->
      Term.enum jmp_t blk |> Seq.exists ~f:(Term.same jmp))

let resolve_variable env versions base =
  match Map.find versions base with
  | Some var -> var
  | None -> (
      match Map.find env.variables base with
      | Some _ -> base
      | None ->
          Map.to_alist env.variables
          |> List.find_map ~f:(fun (var, _) ->
              if Var.same var base then Some var else None)
          |> Option.value_exn)

let lower_actual env jmp state location =
  let definitions =
    Option.bind (caller_block env jmp) ~f:(fun blk ->
        Map.find env.final_expressions (Term.tid blk))
    |> Option.value ~default:Var.Map.empty
  in
  let rec resolve = function
    | Bil.Var var as original -> (
        match Map.find definitions (Var.base var) with
        | Some definition -> definition
        | None -> original)
    | Bil.Cast (kind, bits, exp) -> Bil.Cast (kind, bits, resolve exp)
    | Bil.Extract (hi, lo, exp) -> Bil.Extract (hi, lo, resolve exp)
    | exp -> exp
  in
  lower_exp env state (resolve location)

let return_locations env =
  match Types.return_locations env.types env.sub with
  | [] | [ _ ] -> []
  | locations -> locations

let lower_call env state ?(tail = false) jmp =
  match Jmp.kind jmp with
  | Call call ->
      let target = Call.target call in
      let callee =
        Option.bind (callee_tid env target) ~f:(Term.find sub_t env.program)
      in
      let signature =
        Option.value_map callee ~default:(Ast.signature [])
          ~f:(Types.signature env.types)
      in
      let arguments =
        Option.value_map callee ~default:[] ~f:(fun callee ->
            List.map (Types.parameters env.types callee) ~f:(fun parameter ->
                lower_actual env jmp state parameter.Types.location))
      in
      let expression = call_expression env state target signature arguments in
      let statements =
        match (tail, signature.Ast.return) with
        | true, _ -> [ Ast.Return (Some expression) ]
        | false, Ast.Unknown 0 -> [ Ast.Expr expression ]
        | false, Ast.Structure _ when not (List.is_empty (return_locations env))
          ->
            let temp = make_local env "return_value" signature.Ast.return in
            let versions =
              Option.bind (caller_block env jmp) ~f:(fun blk ->
                  Map.find env.final_versions (Term.tid blk))
              |> Option.value ~default:Var.Map.empty
            in
            Ast.Assign (Ast.var temp, expression)
            :: List.map (return_locations env) ~f:(fun location ->
                let var = resolve_variable env versions location.Types.var in
                Ast.Assign
                  ( Ast.var (variable env var),
                    {
                      Ast.node =
                        Ast.Field
                          ( Ast.var temp,
                            location.Types.field,
                            location.Types.offset );
                      typ = location.Types.typ;
                    } ))
        | false, _ -> (
            match return_variable env with
            | None -> [ Ast.Expr expression ]
            | Some base ->
                let versions =
                  Option.bind (caller_block env jmp) ~f:(fun blk ->
                      Map.find env.final_versions (Term.tid blk))
                  |> Option.value ~default:Var.Map.empty
                in
                let var = resolve_variable env versions base in
                [ Ast.Assign (Ast.var (variable env var), expression) ])
      in
      let statements =
        match (tail, Call.return call) with
        | false, Some (Direct _) | false, None -> statements
        | false, Some (Indirect exp) ->
            [
              Ast.Expr
                {
                  Ast.node =
                    Ast.Machine
                      ( "bir_call_with_continuation",
                        [ expression; lower_exp env state exp ] );
                  typ = Ast.Unknown 0;
                };
            ]
        | true, _ -> statements
      in
      statements
  | _ -> [ Ast.Raw_jump jmp ]

let return_shaped env jmp =
  match Jmp.kind jmp with
  | Ret _ -> true
  | Call call when Option.is_none (Call.return call) -> (
      match Call.target call with
      | Direct tid -> Option.is_none (Term.find sub_t env.program tid)
      | Indirect _ -> true)
  | _ -> false

let return_aggregate env state =
  match return_locations env with
  | [] -> None
  | locations ->
      Some
        {
          Ast.node =
            Ast.Aggregate
              (List.map locations ~f:(fun location ->
                   let var = resolve_variable env state location.Types.var in
                   (location.Types.field, Ast.var (variable env var))));
          typ = (Types.signature env.types env.sub).Ast.return;
        }

let lower_exit env state jmp =
  match Jmp.kind jmp with
  | (Ret _ | Call _) when return_shaped env jmp -> (
      match return_aggregate env state with
      | Some expression -> [ Ast.Return (Some expression) ]
      | None -> (
          match return_variable env with
          | None -> [ Ast.Return None ]
          | Some base -> (
              match Types.signature env.types env.sub with
              | { return = Ast.Unknown 0; _ } -> [ Ast.Return None ]
              | _ ->
                  let var = resolve_variable env state base in
                  [ Ast.Return (Some (Ast.var (variable env var))) ])))
  | Goto (Direct tid as target)
    when Option.is_some (Term.find sub_t env.program tid) ->
      let call = Call.create ~target () in
      lower_call env None ~tail:true (Jmp.create_call call)
  | Goto label ->
      let target =
        match label with
        | Direct tid ->
            {
              Ast.node =
                Ast.Machine
                  (sprintf "bir_label_%s" (sanitize "" (Tid.to_string tid)), []);
              typ = Ast.Unknown 0;
            }
        | Indirect exp ->
            let frame =
              Option.bind (caller_block env jmp) ~f:(fun blk ->
                  Map.find env.final_frames (Term.tid blk))
            in
            lower_exp env frame exp
      in
      [
        Ast.Expr
          {
            Ast.node = Ast.Machine ("bir_indirect_jump", [ target ]);
            typ = Ast.Unknown 0;
          };
      ]
  | Int (number, _) ->
      [
        Ast.Expr
          {
            Ast.node =
              Ast.Machine
                ( "bir_interrupt",
                  [
                    {
                      Ast.node = Ast.Const (Word.of_int ~width:32 number);
                      typ = Ast.Int (32, Ast.Unsigned);
                    };
                  ] );
            typ = Ast.Unknown 0;
          };
      ]
  | Call _ -> []
  | Ret _ -> [ Ast.Return None ]

let lower_edge env edge =
  if Cfg.is_exit (Option.value_exn env.cfg) edge.Cfg.dst then
    let versions =
      Map.find env.final_versions edge.src
      |> Option.value ~default:Var.Map.empty
    in
    lower_exit env versions edge.jump
  else
    let copies = Ssa.copies env.normalized.sub edge.src edge.dst in
    match copies with
    | [] -> []
    | [ (var, exp) ] ->
        let state = Map.find env.final_frames edge.src in
        [ Ast.Assign (Ast.var (variable env var), lower_exp env state exp) ]
    | copies ->
        let state = Map.find env.final_frames edge.src in
        let temporaries =
          List.map copies ~f:(fun (var, exp) ->
              let temp =
                make_local env
                  (sprintf "phi_%d" env.fresh)
                  (Types.typ env.types env.sub var)
              in
              (temp, var, lower_exp env state exp))
        in
        List.map temporaries ~f:(fun (temp, _, exp) ->
            Ast.Assign (Ast.var temp, exp))
        @ List.map temporaries ~f:(fun (temp, var, _) ->
            Ast.Assign (Ast.var (variable env var), Ast.var temp))

let lower_condition env exp = lower_exp env None exp

let collect_vars sub =
  let vars = ref Var.Set.empty in
  let add var = vars := Set.add !vars var in
  let add_exp exp = Set.iter (Exp.free_vars exp) ~f:add in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      Term.enum def_t blk
      |> Seq.iter ~f:(fun def ->
          add (Def.lhs def);
          add_exp (Def.rhs def));
      Term.enum phi_t blk
      |> Seq.iter ~f:(fun phi ->
          add (Phi.lhs phi);
          Set.iter (Phi.free_vars phi) ~f:add);
      Term.enum jmp_t blk
      |> Seq.iter ~f:(fun jmp ->
          Set.iter (Jmp.free_vars jmp) ~f:add;
          match Jmp.kind jmp with
          | Goto (Indirect exp) | Ret (Indirect exp) -> add_exp exp
          | Call call ->
              add_exp (Jmp.cond jmp);
              Option.iter (Call.return call) ~f:(function
                | Indirect exp -> add_exp exp
                | _ -> ())
          | _ -> ()));
  Term.enum arg_t sub
  |> Seq.iter ~f:(fun arg ->
      add (Arg.lhs arg);
      add_exp (Arg.rhs arg));
  !vars

let function_names prog =
  let used = String.Hash_set.create () in
  Term.enum sub_t prog
  |> Seq.fold ~init:(Tid.Map.empty, 0) ~f:(fun (names, id) sub ->
      let base = sanitize "fn_" (Sub.name sub) in
      let name =
        if Hash_set.mem used base then
          sprintf "%s_%s" base (sanitize "" (Tid.to_string (Term.tid sub)))
        else base
      in
      Hash_set.add used name;
      (Map.set names ~key:(Term.tid sub) ~data:name, id + 1))
  |> fst

let bookkeeping_names env =
  if Option.is_none env.normalized.frame then String.Set.empty
  else
    Theory.Role.Register.[ stack_pointer; frame_pointer ]
    |> List.fold ~init:String.Set.empty ~f:(fun names role ->
        match Theory.Target.reg env.target role with
        | None -> names
        | Some register ->
            let name = Theory.Var.name register in
            Map.to_alist env.variables
            |> List.find ~f:(fun (var, _) -> String.equal (Var.name var) name)
            |> Option.value_map ~default:names ~f:(fun (var, _) ->
                Set.add names (variable env var).Ast.name))

let lower_sub env id =
  let signature = Types.signature env.types env.sub in
  let args = Types.parameters env.types env.sub in
  let params =
    if List.length args = List.length signature.Ast.params then
      List.map2_exn args signature.params ~f:(fun arg (_, typ) ->
          ((variable env arg.Types.var).name, typ))
    else signature.params
  in
  let signature = { signature with params } in
  let body =
    if Term.length blk_t env.sub = 0 then []
    else
      Decompile_collapse.structure (Option.value_exn env.cfg)
        ~block:(lower_block env) ~edge:(lower_edge env)
        ~call:(fun jmp ->
          let state =
            Option.bind (caller_block env jmp) ~f:(fun blk ->
                Map.find env.final_frames (Term.tid blk))
          in
          let statements = lower_call env state jmp in
          match Jmp.cond jmp with
          | Bil.Int value when Word.is_one value -> statements
          | condition ->
              [ Ast.If (lower_condition env condition, statements, []) ])
        ~condition:(fun tid exp ->
          lower_exp env (Map.find env.final_frames tid) exp)
  in
  let body =
    Decompile_cleanup.statements ~bookkeeping:(bookkeeping_names env) body
  in
  let used = Decompile_cleanup.used_variables body in
  let arguments = List.map args ~f:(fun arg -> variable env arg.Types.var) in
  let locals =
    env.locals @ Map.data env.variables
    |> List.dedup_and_sort
         ~compare:(fun (x : Ast.variable) (y : Ast.variable) ->
           Int.compare x.Ast.id y.Ast.id)
    |> List.filter ~f:(fun local ->
        (not (List.mem arguments local ~equal:Poly.equal))
        && Set.mem used local.Ast.id)
  in
  {
    Ast.id;
    name = Map.find_exn env.names (Term.tid env.sub);
    signature;
    locals;
    body;
    external_ = Term.length blk_t env.sub = 0;
  }

let decompile ?(concise = false) ~target ?memory prog =
  let prog =
    Option.value_map memory ~default:prog ~f:(fun memory ->
        Decompile_jump.recover ~memory prog)
  in
  let normalized =
    Term.enum sub_t prog |> Seq.to_list
    |> List.map ~f:(fun sub -> (Term.tid sub, Ssa.normalize ~target sub))
  in
  let prog =
    List.fold normalized ~init:prog ~f:(fun prog (tid, normalized) ->
        Term.update sub_t prog normalized.Ssa.sub)
  in
  let types = Types.infer ~target prog in
  let names = function_names prog in
  let addresses =
    Term.enum sub_t prog
    |> Seq.fold ~init:Word.Map.empty ~f:(fun addresses sub ->
        match Term.get_attr sub address with
        | None -> addresses
        | Some address -> Map.set addresses ~key:address ~data:(Term.tid sub))
  in
  let structures = Types.structures types in
  let functions =
    Term.enum sub_t prog |> Seq.to_list
    |> List.mapi ~f:(fun id sub ->
        let normalized =
          List.Assoc.find_exn normalized (Term.tid sub) ~equal:Tid.equal
        in
        let cfg =
          if Term.length blk_t sub = 0 then None
          else Some (Cfg.analyze ~program:prog sub)
        in
        let variables =
          Set.fold (collect_vars sub) ~init:Var.Map.empty
            ~f:(fun variables var ->
              let id = Map.length variables in
              let variable =
                {
                  Ast.id;
                  name = sanitize "v_" (Var.to_string var);
                  typ = Types.typ types sub var;
                }
              in
              Map.set variables ~key:var ~data:variable)
        in
        let env =
          {
            target;
            types;
            program = prog;
            sub;
            normalized;
            high = Decompile_high.create normalized.Ssa.sub;
            cfg;
            variables;
            locals = [];
            fresh = Map.length variables;
            slots = Hashtbl.Poly.create ();
            names;
            addresses;
            final_frames = Tid.Map.empty;
            final_versions = Tid.Map.empty;
            final_expressions = Tid.Map.empty;
          }
        in
        lower_sub env id)
  in
  let program = { Ast.structures; functions } |> Decompile_cast.program in
  if concise then Decompile_optimize.program program |> Decompile_cast.program
  else program
