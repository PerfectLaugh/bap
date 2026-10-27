open Core
open Bap.Std
open Result.Monad_infix

let toolchain = "4.35.0"

type context = { mutable names : string Var.Map.t; mutable vars : Var.t list }

let rec waitpid pid =
  try Caml_unix.waitpid [] pid
  with Caml_unix.Unix_error (Caml_unix.EINTR, _, _) -> waitpid pid

let elan () =
  match Sys.getenv "HOME" with
  | Some home ->
      let installed = Filename.concat home ".elan/bin/elan" in
      if Stdlib.Sys.file_exists installed then installed else "elan"
  | None -> "elan"

let read_file path = In_channel.read_all path

let remove_file path =
  try Caml_unix.unlink path with Caml_unix.Unix_error _ -> ()

let check source =
  let proof = Stdlib.Filename.temp_file "bap-bil-proof-" ".lean" in
  let log = Stdlib.Filename.temp_file "bap-bil-lean-" ".log" in
  Fun.protect
    ~finally:(fun () ->
      remove_file proof;
      remove_file log)
    (fun () ->
      Out_channel.write_all proof ~data:source;
      let output =
        Caml_unix.openfile log [ Caml_unix.O_WRONLY; Caml_unix.O_TRUNC ] 0o600
      in
      let output_is_open = ref true in
      let close_output () =
        if !output_is_open then (
          Caml_unix.close output;
          output_is_open := false)
      in
      let result =
        try
          let program = elan () in
          let args =
            [|
              program;
              "run";
              toolchain;
              "lean";
              "--trust=0";
              "-DwarningAsError=true";
              proof;
            |]
          in
          let pid =
            Caml_unix.create_process program args Caml_unix.stdin output output
          in
          close_output ();
          let status = snd (waitpid pid) in
          let diagnostics = String.strip (read_file log) in
          match status with
          | Caml_unix.WEXITED 0 -> Ok ()
          | Caml_unix.WEXITED code ->
              Error
                (if String.is_empty diagnostics then
                   sprintf "Lean exited with status %d" code
                 else diagnostics)
          | Caml_unix.WSIGNALED signal ->
              Error (sprintf "Lean was terminated by signal %d" signal)
          | Caml_unix.WSTOPPED signal ->
              Error (sprintf "Lean was stopped by signal %d" signal)
        with
        | Caml_unix.Unix_error (error, function_name, argument) ->
            close_output ();
            Error
              (sprintf "could not run Lean: %s (%s%s)"
                 (Caml_unix.error_message error)
                 function_name
                 (if String.is_empty argument then "" else " " ^ argument))
        | exn ->
            close_output ();
            Error (sprintf "could not run Lean: %s" (Exn.to_string exn))
      in
      result)

let imm_width exp =
  match Type.infer exp with
  | Ok (Type.Imm width) when width > 0 -> Ok width
  | Ok (Type.Imm _) -> Error "BIL expression has a non-positive width"
  | Ok (Type.Mem _ | Type.Unk) ->
      Error "only immediate BIL expressions can be checked"
  | Error error ->
      Error
        (sprintf "ill-typed BIL expression: %s"
           (Type.sexp_of_error error |> Sexp.to_string_hum))

let variable_name context variable =
  match Var.typ variable with
  | Type.Mem _ | Type.Unk -> Error "only immediate BIL variables can be checked"
  | Type.Imm width when width <= 0 ->
      Error "BIL variable has a non-positive width"
  | Type.Imm _ -> (
      match Map.find context.names variable with
      | Some name -> Ok name
      | None ->
          let name = sprintf "v%d" (Map.length context.names) in
          context.names <- Map.set context.names ~key:variable ~data:name;
          context.vars <- variable :: context.vars;
          Ok name)

let parens value = "(" ^ value ^ ")"

let rec render context exp =
  let unary value = Result.map (render context value) ~f:parens in
  let binary left right f =
    render context left >>= fun left ->
    render context right >>| fun right -> f left right
  in
  let bitvector_unop name value =
    unary value >>| fun value -> sprintf "%s %s" name value |> parens
  in
  let bitvector_binop name left right =
    binary left right (fun left right ->
        sprintf "%s %s %s" name left right |> parens)
  in
  match exp with
  | Bil.Var variable -> variable_name context variable
  | Bil.Int word ->
      let value = Bitvec.to_bigint (Word.to_bitvec word) |> Z.to_string in
      Ok (sprintf "(BitVec.ofNat %d %s)" (Word.bitwidth word) value)
  | Bil.BinOp (operation, left, right) -> (
      match operation with
      | Bil.PLUS -> binary left right (fun x y -> sprintf "(%s + %s)" x y)
      | Bil.MINUS -> binary left right (fun x y -> sprintf "(%s - %s)" x y)
      | Bil.TIMES -> binary left right (fun x y -> sprintf "(%s * %s)" x y)
      | Bil.DIVIDE -> binary left right (fun x y -> sprintf "(%s / %s)" x y)
      | Bil.SDIVIDE -> bitvector_binop "BitVec.sdiv" left right
      | Bil.MOD -> binary left right (fun x y -> sprintf "(%s %% %s)" x y)
      | Bil.SMOD -> bitvector_binop "BitVec.srem" left right
      | Bil.LSHIFT ->
          binary left right (fun x y ->
              sprintf "(BitVec.shiftLeft %s (BitVec.toNat %s))" x y)
      | Bil.RSHIFT ->
          binary left right (fun x y ->
              sprintf "(BitVec.ushiftRight %s (BitVec.toNat %s))" x y)
      | Bil.ARSHIFT ->
          binary left right (fun x y ->
              sprintf "(BitVec.sshiftRight %s (BitVec.toNat %s))" x y)
      | Bil.AND -> binary left right (fun x y -> sprintf "(%s &&& %s)" x y)
      | Bil.OR -> binary left right (fun x y -> sprintf "(%s ||| %s)" x y)
      | Bil.XOR -> binary left right (fun x y -> sprintf "(%s ^^^ %s)" x y)
      | Bil.EQ ->
          binary left right (fun x y ->
              sprintf "(BitVec.ofBool (%s == %s))" x y)
      | Bil.NEQ ->
          binary left right (fun x y ->
              sprintf "(BitVec.ofBool (%s != %s))" x y)
      | Bil.LT ->
          bitvector_binop "BitVec.ult" left right >>| fun value ->
          sprintf "(BitVec.ofBool %s)" value
      | Bil.LE ->
          bitvector_binop "BitVec.ule" left right >>| fun value ->
          sprintf "(BitVec.ofBool %s)" value
      | Bil.SLT ->
          bitvector_binop "BitVec.slt" left right >>| fun value ->
          sprintf "(BitVec.ofBool %s)" value
      | Bil.SLE ->
          bitvector_binop "BitVec.sle" left right >>| fun value ->
          sprintf "(BitVec.ofBool %s)" value)
  | Bil.UnOp (Bil.NEG, value) ->
      unary value >>| fun value -> sprintf "(-%s)" value
  | Bil.UnOp (Bil.NOT, value) ->
      unary value >>| fun value -> sprintf "(~~~%s)" value
  | Bil.Cast (Bil.UNSIGNED, width, value) ->
      bitvector_unop (sprintf "BitVec.zeroExtend %d" width) value
  | Bil.Cast (Bil.SIGNED, width, value) ->
      bitvector_unop (sprintf "BitVec.signExtend %d" width) value
  | Bil.Cast (Bil.HIGH, width, value) ->
      imm_width value >>= fun source_width ->
      unary value >>| fun value ->
      sprintf "(BitVec.extractLsb %d %d %s)" (source_width - 1)
        (source_width - width) value
  | Bil.Cast (Bil.LOW, width, value) ->
      unary value >>| fun value ->
      sprintf "(BitVec.extractLsb %d 0 %s)" (width - 1) value
  | Bil.Extract (high, low, value) ->
      unary value >>| fun value ->
      sprintf "(BitVec.extractLsb %d %d %s)" high low value
  | Bil.Concat (left, right) ->
      binary left right (fun x y -> sprintf "(%s ++ %s)" x y)
  | Bil.Ite (condition, yes, no) ->
      render context condition >>= fun condition ->
      render context yes >>= fun yes ->
      render context no >>| fun no ->
      sprintf "(if %s = BitVec.ofNat 1 1 then %s else %s)" condition yes no
  | Bil.Load _ -> Error "loads are outside the verified pure BIL fragment"
  | Bil.Store _ -> Error "stores are outside the verified pure BIL fragment"
  | Bil.Let _ ->
      Error "let expressions are outside the verified pure BIL fragment"
  | Bil.Unknown _ ->
      Error "unknown values are outside the verified pure BIL fragment"

let theorem_source ~imports ~tactics context before after =
  let variables = List.rev context.vars in
  let binders =
    List.map variables ~f:(fun variable ->
        let name = Map.find_exn context.names variable in
        match Var.typ variable with
        | Type.Imm width -> sprintf "  (%s : BitVec %d)" name width
        | Type.Mem _ | Type.Unk -> assert false)
    |> String.concat ~sep:"\n"
  in
  let binders = if String.is_empty binders then "" else binders ^ "\n" in
  let imports =
    String.concat ~sep:"\n" (List.map imports ~f:(fun name -> "import " ^ name))
  in
  sprintf "%s\n\ntheorem bap_rewrite\n%s  : %s = %s := by\n%s\n" imports binders
    before after tactics

let proof before after =
  imm_width before >>= fun before_width ->
  imm_width after >>= fun after_width ->
  if before_width <> after_width then
    Error
      (sprintf "rewrite changes the result width from %d to %d" before_width
         after_width)
  else
    let context = { names = Var.Map.empty; vars = [] } in
    render context before >>= fun before ->
    render context after >>| fun after ->
    theorem_source ~imports:[ "Lean" ] ~tactics:"  bv_decide" context before
      after

let validate_application_with ~checker ~imports ~function_name ~projection
    ~unfold actual arguments =
  imm_width actual >>= fun _ ->
  let context = { names = Var.Map.empty; vars = [] } in
  render context actual >>= fun actual ->
  List.map arguments ~f:(render context) |> Result.all >>= fun arguments ->
  let projection =
    Option.value_map projection ~default:"" ~f:(fun name -> "." ^ name)
  in
  let application =
    sprintf "(%s%s)%s" function_name
      (String.concat ~sep:"" (List.map arguments ~f:(fun arg -> " " ^ arg)))
      projection
  in
  let tactics =
    match unfold with
    | [] -> "  bv_decide"
    | names ->
        sprintf "  simp [%s] <;> bv_decide" (String.concat ~sep:", " names)
  in
  checker (theorem_source ~imports ~tactics context actual application)

let proof_with_context before after =
  match proof before after with
  | Ok source -> Ok source
  | Error message ->
      Error
        (Format.asprintf "%s@.before: %a@.after:  %a" message Exp.pp before
           Exp.pp after)

let rec validate_exp ~checker before after =
  if Exp.equal before after then Ok ()
  else
    let descend = validate_exp ~checker in
    let descend2 (x, x') (y, y') = descend x x' >>= fun () -> descend y y' in
    match (before, after) with
    | Bil.BinOp (op, x, y), Bil.BinOp (op', x', y') when Poly.(op = op') ->
        descend2 (x, x') (y, y')
    | Bil.UnOp (op, x), Bil.UnOp (op', x') when Poly.(op = op') -> descend x x'
    | Bil.Cast (cast, size, x), Bil.Cast (cast', size', x')
      when Poly.(cast = cast') && size = size' ->
        descend x x'
    | Bil.Let (var, value, body), Bil.Let (var', value', body')
      when Var.same var var' ->
        descend value value' >>= fun () -> descend body body'
    | Bil.Ite (cond, yes, no), Bil.Ite (cond', yes', no') ->
        descend cond cond' >>= fun () -> descend2 (yes, yes') (no, no')
    | Bil.Extract (hi, lo, x), Bil.Extract (hi', lo', x')
      when hi = hi' && lo = lo' ->
        descend x x'
    | Bil.Concat (x, y), Bil.Concat (x', y') -> descend2 (x, x') (y, y')
    | Bil.Load (mem, addr, endian, size), Bil.Load (mem', addr', endian', size')
      when Poly.(endian = endian') && Poly.(size = size') ->
        descend2 (mem, mem') (addr, addr')
    | ( Bil.Store (mem, addr, value, endian, size),
        Bil.Store (mem', addr', value', endian', size') )
      when Poly.(endian = endian') && Poly.(size = size') ->
        descend2 (mem, mem') (addr, addr') >>= fun () -> descend value value'
    | _ -> (
        match proof_with_context before after with
        | Error _ as error -> error
        | Ok source -> checker source)

let rec validate_stmts ~checker before after =
  match (before, after) with
  | [], [] -> Ok ()
  | [], _ | _, [] -> Error "rewrite changes the number of BIL statements"
  | before :: rest, after :: rest' ->
      validate_stmt ~checker before after >>= fun () ->
      validate_stmts ~checker rest rest'

and validate_stmt ~checker before after =
  if Stmt.equal before after then Ok ()
  else
    match (before, after) with
    | Bil.Move (var, value), Bil.Move (var', value') when Var.same var var' ->
        validate_exp ~checker value value'
    | Bil.Jmp target, Bil.Jmp target' -> validate_exp ~checker target target'
    | Bil.While (cond, body), Bil.While (cond', body') ->
        validate_exp ~checker cond cond' >>= fun () ->
        validate_stmts ~checker body body'
    | Bil.If (cond, yes, no), Bil.If (cond', yes', no') ->
        validate_exp ~checker cond cond' >>= fun () ->
        validate_stmts ~checker yes yes' >>= fun () ->
        validate_stmts ~checker no no'
    | Bil.Special _, Bil.Special _ | Bil.CpuExn _, Bil.CpuExn _ ->
        Error "rewrite changes a special statement or CPU exception"
    | _ -> Error "rewrite changes the BIL statement structure"

let validate_with ~checker before after = validate_stmts ~checker before after
let validate_exp = validate_exp ~checker:check
let validate = validate_with ~checker:check
let validate_application = validate_application_with ~checker:check

let checked_fold_consts before =
  let after = Bil.fold_consts before in
  match validate before after with
  | Ok () -> after
  | Error message ->
      Error.raise
        (Error.of_string
           (sprintf "Lean rejected BIL constant folding: %s" message))
