open Core
open Bap.Std
open Bap_core_theory
open Bap_c.Std
module Ast = Decompile_ast

module Scope = struct
  module T = struct
    type t = tid * var [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

type evidence = {
  bits : int;
  mutable sign : Ast.sign;
  mutable pointee : int option;
  mutable fields : (int * int) list;
  mutable strides : int list;
  mutable known : Ast.typ option;
  mutable valid_layout : bool;
}

type t = {
  target : Theory.Target.t;
  vars : evidence Scope.Map.t;
  mutable signatures : Ast.signature Tid.Map.t;
}

let bits_of_typ = function Type.Imm bits -> bits | _ -> 0

let new_evidence var =
  {
    bits = bits_of_typ (Var.typ var);
    sign = Ast.Unknown_sign;
    pointee = None;
    fields = [];
    strides = [];
    known = (match Var.typ var with Type.Mem _ -> Some Ast.Memory | _ -> None);
    valid_layout = true;
  }

let scope sub var = (Term.tid sub, Var.base var)

let evidence t sub var =
  Map.find t.vars (scope sub var) |> Option.value ~default:(new_evidence var)

let ensure vars sub var =
  let key = scope sub var in
  match Map.find vars key with
  | Some _ -> vars
  | None -> Map.set vars ~key ~data:(new_evidence var)

let update t sub var ~f =
  let key = scope sub var in
  let info = Option.value (Map.find t.vars key) ~default:(new_evidence var) in
  f info

let merge_sign current next =
  match (current, next) with
  | Ast.Unknown_sign, sign | sign, Ast.Unknown_sign -> sign
  | x, y when Poly.equal x y -> x
  | _ -> Ast.Unknown_sign

let mark_sign t sub var sign =
  update t sub var ~f:(fun info -> info.sign <- merge_sign info.sign sign)

let ranges_overlap (offset, bits) (offset', bits') =
  (offset <> offset' || bits <> bits')
  && offset < offset' + (bits' / 8)
  && offset' < offset + (bits / 8)

let mark_field t sub var offset bits =
  update t sub var ~f:(fun info ->
      if offset < 0 then info.valid_layout <- false
      else (
        if not (List.mem info.fields (offset, bits) ~equal:Poly.equal) then
          info.fields <- (offset, bits) :: info.fields;
        if List.exists info.fields ~f:(ranges_overlap (offset, bits)) then
          info.valid_layout <- false;
        info.pointee <-
          Some
            (Option.value_map info.pointee ~default:bits ~f:(fun old ->
                 if old = bits then old else 0))))

let rec int_const = function
  | Bil.Int value ->
      Some (Word.to_int64_exn (Word.signed value) |> Int64.to_int_exn)
  | Bil.Cast ((UNSIGNED | SIGNED | LOW), _, exp) -> int_const exp
  | _ -> None

let rec address = function
  | Bil.Var var -> Some (var, 0)
  | Bil.BinOp (PLUS, x, y) -> (
      match (address x, address y, int_const x, int_const y) with
      | Some (var, offset), _, _, Some constant
      | _, Some (var, offset), Some constant, _ ->
          Some (var, offset + constant)
      | _ -> None)
  | Bil.BinOp (MINUS, x, y) -> (
      match (address x, int_const y) with
      | Some (var, offset), Some constant -> Some (var, offset - constant)
      | _ -> None)
  | Bil.Cast ((UNSIGNED | SIGNED), _, exp) -> address exp
  | _ -> None

let is_stack_register t var =
  List.exists
    Theory.Role.Register.[ stack_pointer; frame_pointer ]
    ~f:(fun role ->
      match Theory.Target.reg t.target role with
      | None -> false
      | Some register -> String.equal (Theory.Var.name register) (Var.name var))

let rec mark_address t sub exp bits =
  match address exp with
  | Some (var, offset) when not (is_stack_register t var) ->
      mark_field t sub var offset bits
  | Some _ -> ()
  | None -> (
      match exp with
      | Bil.BinOp (PLUS, base, index) ->
          mark_array t sub base index bits;
          mark_array t sub index base bits
      | _ -> ())

and mark_array t sub base index bits =
  match address base with
  | None -> ()
  | Some (var, offset) ->
      let stride =
        match index with
        | Bil.BinOp (TIMES, _, Bil.Int value)
        | Bil.BinOp (TIMES, Bil.Int value, _)
        | Bil.BinOp (LSHIFT, _, Bil.Int value) ->
            int_const (Bil.Int value)
        | _ -> None
      in
      Option.iter stride ~f:(fun stride ->
          let stride =
            match index with
            | Bil.BinOp (LSHIFT, _, _) -> 1 lsl stride
            | _ -> stride
          in
          if stride > 0 && stride * 8 = bits then
            update t sub var ~f:(fun info ->
                info.pointee <- Some bits;
                if offset = 0 then
                  info.strides <-
                    List.dedup_and_sort ~compare:Int.compare
                      (stride :: info.strides)))

let rec scan_exp t sub = function
  | Bil.Var _ | Bil.Int _ | Bil.Unknown _ -> ()
  | Bil.Load (mem, addr, _, size) ->
      scan_exp t sub mem;
      mark_address t sub addr (Size.in_bits size)
  | Bil.Store (mem, addr, value, _, size) ->
      scan_exp t sub mem;
      mark_address t sub addr (Size.in_bits size);
      scan_exp t sub value
  | Bil.BinOp ((SLT | SLE | SDIVIDE | SMOD | ARSHIFT), x, y) ->
      scan_signed t sub x;
      scan_exp t sub x;
      scan_exp t sub y
  | Bil.BinOp ((LT | LE | DIVIDE | MOD), x, y) ->
      scan_unsigned t sub x;
      scan_exp t sub x;
      scan_exp t sub y
  | Bil.BinOp (_, x, y) | Bil.Concat (x, y) ->
      scan_exp t sub x;
      scan_exp t sub y
  | Bil.UnOp (_, x) | Bil.Extract (_, _, x) -> scan_exp t sub x
  | Bil.Cast (SIGNED, _, x) ->
      scan_signed t sub x;
      scan_exp t sub x
  | Bil.Cast (_, _, x) -> scan_exp t sub x
  | Bil.Let (_, value, body) ->
      scan_exp t sub value;
      scan_exp t sub body
  | Bil.Ite (c, x, y) ->
      scan_exp t sub c;
      scan_exp t sub x;
      scan_exp t sub y

and scan_signed t sub = function
  | Bil.Var var -> mark_sign t sub var Ast.Signed
  | Bil.Cast (_, _, exp) -> scan_signed t sub exp
  | _ -> ()

and scan_unsigned t sub = function
  | Bil.Var var -> mark_sign t sub var Ast.Unsigned
  | Bil.Cast (_, _, exp) -> scan_unsigned t sub exp
  | _ -> ()

let rec of_ctype model (ctype : C.Type.t) : Ast.typ =
  let size default = Option.value (model#bits ctype) ~default in
  match ctype with
  | `Void -> Ast.Unknown 0
  | `Basic { t = #C.Type.real as real; _ } ->
      Ast.Float (model#real real |> Size.in_bits)
  | `Basic { t = #C.Type.complex; _ } -> Ast.Unknown (size 0)
  | `Basic { t = `bool; _ } -> Ast.Bool
  | `Basic { t = basic; _ } ->
      let sign = if C.Type.is_signed ctype then Ast.Signed else Ast.Unsigned in
      Ast.Int (model#basic basic |> Size.in_bits, sign)
  | `Pointer { t = `Function { t = proto; _ }; _ } ->
      Ast.Pointer (Ast.Function (of_cproto model proto))
  | `Pointer { t; _ } -> Ast.Pointer (of_ctype model t)
  | `Array { t = { element; size = count }; _ } ->
      Ast.Array (of_ctype model element, count)
  | `Structure { t = { name; _ }; _ } | `Union { t = { name; _ }; _ } ->
      Ast.Structure name
  | `Function { t = proto; _ } -> Ast.Function (of_cproto model proto)

and of_cproto model (proto : C.Type.proto) : Ast.signature =
  {
    return = of_ctype model proto.return;
    params =
      List.map proto.args ~f:(fun (name, typ) -> (name, of_ctype model typ));
    variadic = proto.variadic;
  }

let sub_vars sub =
  let vars = ref Var.Set.empty in
  let add var = vars := Set.add !vars (Var.base var) in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      Term.enum def_t blk
      |> Seq.iter ~f:(fun def ->
          add (Def.lhs def);
          Set.iter (Def.free_vars def) ~f:add);
      Term.enum phi_t blk
      |> Seq.iter ~f:(fun phi ->
          add (Phi.lhs phi);
          Set.iter (Phi.free_vars phi) ~f:add);
      Term.enum jmp_t blk
      |> Seq.iter ~f:(fun jmp -> Set.iter (Jmp.free_vars jmp) ~f:add));
  Term.enum arg_t sub
  |> Seq.iter ~f:(fun arg ->
      add (Arg.lhs arg);
      Set.iter (Exp.free_vars (Arg.rhs arg)) ~f:add);
  !vars

let has_target target name =
  List.exists (target :: Theory.Target.parents target) ~f:(fun parent ->
      String.equal (KB.Name.unqualified (Theory.Target.name parent)) name)

let is_systemz target =
  has_target target "systemz" || has_target target "systemz9"

let is_x86 target =
  List.exists
    [ "x86"; "x86_64"; "i86"; "i286"; "i386"; "i486"; "i586"; "i686" ]
    ~f:(has_target target)

let target_var target name =
  match Theory.Target.var target name with
  | Some var -> Some var
  | None when is_systemz target ->
      Theory.Target.var (Theory.Target.get ~package:"bap" "systemz9") name
  | None -> None

let fallback_return_registers target =
  if is_systemz target then [ "R2" ]
  else if is_x86 target then
    match Theory.Target.bits target with
    | 16 -> [ "AX" ]
    | 32 -> [ "EAX" ]
    | _ -> [ "RAX" ]
  else []

let find_register target role sub =
  let registers = Theory.Target.regs target ~roles:[ role ] |> Set.to_list in
  let registers =
    if
      List.is_empty registers
      && Poly.equal role Theory.Role.Register.function_return
    then
      List.filter_map (fallback_return_registers target) ~f:(target_var target)
    else registers
  in
  List.find_map registers ~f:(fun reg ->
      let name = Theory.Var.name reg in
      Set.find (sub_vars sub) ~f:(fun var -> String.equal (Var.name var) name))

let return_register target sub =
  find_register target Theory.Role.Register.function_return sub

let return_arg sub =
  Term.enum arg_t sub
  |> Seq.find ~f:(fun arg ->
      match Arg.intent arg with Some Out | Some Both -> true | _ -> false)

let input_args sub =
  Term.enum arg_t sub |> Seq.to_list
  |> List.filter ~f:(fun arg ->
      match Arg.intent arg with Some Out -> false | _ -> true)

let infer_signature t sub =
  match Term.get_attr sub C.proto with
  | Some proto -> of_cproto (C.Abi.model t.target) proto
  | None ->
      let params =
        List.map (input_args sub) ~f:(fun arg ->
            let var = Arg.lhs arg in
            let info = evidence t sub var in
            ( Var.name var,
              Option.value info.known ~default:(Ast.Unknown info.bits) ))
      in
      let return =
        match return_arg sub with
        | Some arg ->
            let info = evidence t sub (Arg.lhs arg) in
            Option.value info.known ~default:(Ast.Unknown info.bits)
        | None -> (
            match
              find_register t.target Theory.Role.Register.function_return sub
            with
            | None -> Ast.Unknown 0
            | Some var ->
                let info = evidence t sub var in
                Option.value info.known ~default:(Ast.Unknown info.bits))
      in
      { Ast.return; params; variadic = false }

let sanitize name =
  String.map name ~f:(fun c ->
      if Char.is_alphanum c || Char.equal c '_' then c else '_')

let structure_name sub var =
  sprintf "recovered_%s_%s"
    (sanitize (Tid.to_string (Term.tid sub)))
    (sanitize (Var.name (Var.base var)))

let has_structural_fields info =
  info.valid_layout
  && List.exists info.fields ~f:(fun (offset, _) -> offset > 0)

let typ_of_evidence sub var info =
  match info.known with
  | Some typ -> typ
  | None when has_structural_fields info ->
      Ast.Pointer (Ast.Structure (structure_name sub var))
  | None -> (
      match info.pointee with
      | Some bits when bits > 0 ->
          if List.length info.strides = 1 then
            Ast.Pointer (Ast.Array (Ast.Int (bits, info.sign), None))
          else Ast.Pointer (Ast.Int (bits, Ast.Unknown_sign))
      | _ -> Ast.Int (info.bits, info.sign))

let typ t sub var = typ_of_evidence sub (Var.base var) (evidence t sub var)

let rec expression t sub exp =
  let open Ast in
  match exp with
  | Bil.Var var -> typ t sub var
  | Bil.Int value -> Int (Word.bitwidth value, Unknown_sign)
  | Bil.Load _ -> (
      match Type.infer exp with
      | Ok (Type.Imm bits) -> Int (bits, Unknown_sign)
      | _ -> Unknown 0)
  | Bil.Store _ -> Unknown 0
  | Bil.BinOp ((EQ | NEQ | LT | LE | SLT | SLE), _, _) -> Bool
  | Bil.BinOp ((SDIVIDE | SMOD), _, _) -> (
      match Type.infer exp with
      | Ok (Type.Imm bits) -> Int (bits, Signed)
      | _ -> Unknown 0)
  | Bil.BinOp _ | Bil.UnOp _ | Bil.Concat _ | Bil.Extract _ -> (
      match Type.infer exp with
      | Ok (Type.Imm bits) -> Int (bits, Unknown_sign)
      | _ -> Unknown 0)
  | Bil.Cast (SIGNED, bits, _) -> Int (bits, Signed)
  | Bil.Cast (_, bits, _) -> Int (bits, Unknown_sign)
  | Bil.Let (_, _, body) -> expression t sub body
  | Bil.Unknown (_, Type.Imm bits) -> Unknown bits
  | Bil.Unknown _ -> Unknown 0
  | Bil.Ite (_, x, _) -> expression t sub x

type parameter = { name : string; var : var; typ : Ast.typ; location : exp }

let argument_registers target =
  let generic =
    Theory.Target.regs target
      ~roles:Theory.Role.Register.[ function_argument; integer ]
    |> Set.to_list
  in
  if not (List.is_empty generic) then generic
  else
    let names =
      if Theory.Target.bits target = 64 && has_target target "x86_64" then
        if Theory.Abi.equal (Theory.Target.abi target) Theory.Abi.ms then
          [ "rcx"; "rdx"; "r8"; "r9" ]
        else [ "rdi"; "rsi"; "rdx"; "rcx"; "r8"; "r9" ]
      else if is_systemz target then [ "R2"; "R3"; "R4"; "R5"; "R6" ]
      else []
    in
    List.filter_map names ~f:(target_var target)

let parameters t sub =
  match input_args sub with
  | args when not (List.is_empty args) ->
      List.map args ~f:(fun arg ->
          let var = Arg.lhs arg in
          {
            name = Var.name var;
            var;
            typ = typ t sub var;
            location = Arg.rhs arg;
          })
  | _ -> (
      match Term.first blk_t sub with
      | None -> []
      | Some entry ->
          let live = Decompile_ssa.live_in sub entry in
          let candidates = argument_registers t.target in
          List.filter_map candidates ~f:(fun register ->
              let name = Theory.Var.name register in
              if
                not
                  (Set.exists live ~f:(fun var ->
                       String.equal (Var.name var) name))
              then None
              else
                Set.find (sub_vars sub) ~f:(fun var ->
                    String.equal (Var.name var) name)
                |> Option.map ~f:(fun var ->
                    { name; var; typ = typ t sub var; location = Bil.var var }))
      )

let final_signature t sub =
  match Term.get_attr sub C.proto with
  | Some proto ->
      let signature = of_cproto (C.Abi.model t.target) proto in
      if not (List.is_empty signature.Ast.params) then signature
      else
        let params =
          List.map (parameters t sub) ~f:(fun parameter ->
              (parameter.name, parameter.typ))
        in
        { signature with params }
  | None ->
      let base = infer_signature t sub in
      let params =
        List.map (parameters t sub) ~f:(fun parameter ->
            (parameter.name, parameter.typ))
      in
      let return =
        match return_arg sub with
        | Some arg -> typ t sub (Arg.lhs arg)
        | None -> (
            match
              find_register t.target Theory.Role.Register.function_return sub
            with
            | None -> Ast.Unknown 0
            | Some var -> typ t sub var)
      in
      { base with params; return }

let signature = final_signature

let refresh_signatures t prog =
  Term.enum sub_t prog
  |> Seq.iter ~f:(fun sub ->
      t.signatures <-
        Map.set t.signatures ~key:(Term.tid sub) ~data:(final_signature t sub))

let signatures_snapshot t prog =
  Term.enum sub_t prog
  |> Seq.map ~f:(fun sub ->
      (Term.tid sub, Map.find t.signatures (Term.tid sub)))
  |> Seq.to_list

let join_pointee x y =
  match (x, y) with
  | None, value | value, None -> value
  | Some x, Some y when x = y -> Some x
  | _ -> Some 0

let merge_info a b =
  let sign = merge_sign a.sign b.sign in
  let known = Option.first_some a.known b.known in
  let pointee = join_pointee a.pointee b.pointee in
  let fields =
    List.dedup_and_sort ~compare:Poly.compare (a.fields @ b.fields)
  in
  let strides =
    List.dedup_and_sort ~compare:Int.compare (a.strides @ b.strides)
  in
  let valid_layout =
    a.valid_layout && b.valid_layout
    && not
         (List.exists fields ~f:(fun field ->
              List.exists fields ~f:(ranges_overlap field)))
  in
  List.iter [ a; b ] ~f:(fun info ->
      info.sign <- sign;
      info.known <- known;
      info.pointee <- pointee;
      info.fields <- fields;
      info.strides <- strides;
      info.valid_layout <- valid_layout)

let connect t caller actual callee formal =
  match address actual with
  | Some (var, _) ->
      merge_info (evidence t caller var) (evidence t callee formal)
  | None -> ()

let propagate_calls t prog =
  let rec loop () =
    refresh_signatures t prog;
    let before = signatures_snapshot t prog in
    Term.enum sub_t prog
    |> Seq.iter ~f:(fun caller ->
        Term.enum blk_t caller
        |> Seq.iter ~f:(fun blk ->
            Term.enum jmp_t blk
            |> Seq.iter ~f:(fun jmp ->
                match Jmp.kind jmp with
                | Call call -> (
                    match Call.target call with
                    | Direct tid -> (
                        match Term.find sub_t prog tid with
                        | None -> ()
                        | Some callee ->
                            List.iter (parameters t callee) ~f:(fun formal ->
                                let actual = formal.location in
                                scan_exp t caller actual;
                                connect t caller actual callee formal.var))
                    | Indirect exp -> scan_exp t caller exp)
                | _ -> ())));
    refresh_signatures t prog;
    let after = signatures_snapshot t prog in
    if not (Poly.equal before after) then loop ()
  in
  loop ()

let structures t =
  Map.to_alist t.vars
  |> List.filter_map ~f:(fun ((tid, var), info) ->
      if has_structural_fields info then
        let fields =
          List.dedup_and_sort info.fields ~compare:(fun (x, _) (y, _) ->
              Int.compare x y)
          |> List.map ~f:(fun (offset, bits) ->
              ( sprintf "field_%x" offset,
                offset,
                Ast.Int (bits, Ast.Unknown_sign) ))
        in
        let sub_name = sanitize (Tid.to_string tid) in
        Some
          {
            Ast.name =
              sprintf "recovered_%s_%s" sub_name (sanitize (Var.name var));
            fields;
          }
      else None)
  |> List.dedup_and_sort ~compare:(fun x y ->
      String.compare x.Ast.name y.Ast.name)

let infer ~target prog =
  let vars =
    Term.enum sub_t prog
    |> Seq.fold ~init:Scope.Map.empty ~f:(fun vars sub ->
        let vars =
          Set.fold (sub_vars sub) ~init:vars ~f:(fun vars var ->
              ensure vars sub var)
        in
        Term.enum arg_t sub
        |> Seq.fold ~init:vars ~f:(fun vars arg ->
            let vars = ensure vars sub (Arg.lhs arg) in
            match Term.get_attr arg C.t with
            | None -> vars
            | Some ctype ->
                Map.set vars
                  ~key:(scope sub (Arg.lhs arg))
                  ~data:
                    {
                      (new_evidence (Arg.lhs arg)) with
                      known = Some (of_ctype (C.Abi.model target) ctype);
                    }))
  in
  let t = { target; vars; signatures = Tid.Map.empty } in
  Term.enum sub_t prog
  |> Seq.iter ~f:(fun sub ->
      t.signatures <-
        Map.set t.signatures ~key:(Term.tid sub) ~data:(infer_signature t sub));
  Term.enum sub_t prog
  |> Seq.iter ~f:(fun sub ->
      Term.enum blk_t sub
      |> Seq.iter ~f:(fun blk ->
          Term.enum def_t blk
          |> Seq.iter ~f:(fun def -> scan_exp t sub (Def.rhs def));
          Term.enum phi_t blk
          |> Seq.iter ~f:(fun phi ->
              Phi.values phi |> Seq.iter ~f:(fun (_, exp) -> scan_exp t sub exp));
          Term.enum jmp_t blk
          |> Seq.iter ~f:(fun jmp ->
              scan_exp t sub (Jmp.cond jmp);
              match Jmp.kind jmp with
              | Goto (Indirect exp) | Ret (Indirect exp) -> scan_exp t sub exp
              | Call call ->
                  Option.iter (Call.return call) ~f:(function
                    | Direct _ -> ()
                    | Indirect exp -> scan_exp t sub exp)
              | _ -> ())));
  propagate_calls t prog;
  t
