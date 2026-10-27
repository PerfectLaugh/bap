open Core
open Bap.Std
open Result.Monad_infix
module Witness = Recompile_optimize
module Parse = Recompile_optimize.Parse

type context = {
  mutable vars : int Var.Map.t;
  mutable labels : int String.Map.t;
  mutable next_var : int;
  mutable next_label : int;
}

let context () =
  {
    vars = Var.Map.empty;
    labels = String.Map.empty;
    next_var = 0;
    next_label = 0;
  }

let var_id context var =
  match Map.find context.vars var with
  | Some id -> id
  | None ->
      let id = context.next_var in
      context.next_var <- id + 1;
      context.vars <- Map.set context.vars ~key:var ~data:id;
      id

let label_id context label =
  match Map.find context.labels label with
  | Some id -> id
  | None ->
      let id = context.next_label in
      context.next_label <- id + 1;
      context.labels <- Map.set context.labels ~key:label ~data:id;
      id

let imm_width exp =
  match Type.infer exp with
  | Ok (Type.Imm width) when width > 0 -> Ok width
  | Ok (Type.Imm _) -> Error "non-positive expression width"
  | Ok (Type.Mem _ | Type.Unk) ->
      Error "only immediate expressions are supported"
  | Error error ->
      Error
        (sprintf "ill-typed expression: %s"
           (Type.sexp_of_error error |> Sexp.to_string_hum))

let word_value word = Bitvec.to_bigint (Word.to_bitvec word) |> Z.to_string

let rec render_exp context exp =
  let unary value f = render_exp context value >>| f in
  let binary left right f =
    render_exp context left >>= fun left ->
    render_exp context right >>| fun right -> f left right
  in
  let unop name value =
    unary value (fun value -> sprintf "Exp.%s (%s)" name value)
  in
  let binop name left right =
    binary left right (fun left right ->
        sprintf "Exp.%s (%s) (%s)" name left right)
  in
  match exp with
  | Bil.Var var ->
      imm_width exp >>| fun width ->
      sprintf "Exp.var %d %d" (var_id context var) width
  | Bil.Int word ->
      let width = Word.bitwidth word in
      Ok
        (sprintf "Exp.int %d (BitVec.ofNat %d %s)" width width (word_value word))
  | Bil.UnOp (Bil.NEG, value) -> unop "neg" value
  | Bil.UnOp (Bil.NOT, value) -> unop "not" value
  | Bil.BinOp (operation, left, right) -> (
      match operation with
      | Bil.PLUS -> binop "add" left right
      | Bil.MINUS -> binop "sub" left right
      | Bil.TIMES -> binop "mul" left right
      | Bil.DIVIDE -> binop "udiv" left right
      | Bil.SDIVIDE -> binop "sdiv" left right
      | Bil.MOD -> binop "urem" left right
      | Bil.SMOD -> binop "srem" left right
      | Bil.LSHIFT -> binop "shiftLeft" left right
      | Bil.RSHIFT -> binop "ushiftRight" left right
      | Bil.ARSHIFT -> binop "sshiftRight" left right
      | Bil.AND -> binop "and" left right
      | Bil.OR -> binop "or" left right
      | Bil.XOR -> binop "xor" left right
      | Bil.EQ -> binop "eq" left right
      | Bil.NEQ -> binop "neq" left right
      | Bil.LT -> binop "ult" left right
      | Bil.LE -> binop "ule" left right
      | Bil.SLT -> binop "slt" left right
      | Bil.SLE -> binop "sle" left right)
  | Bil.Cast (Bil.UNSIGNED, width, value) ->
      unary value (fun value -> sprintf "Exp.zeroExtend %d (%s)" width value)
  | Bil.Cast (Bil.SIGNED, width, value) ->
      unary value (fun value -> sprintf "Exp.signExtend %d (%s)" width value)
  | Bil.Cast (Bil.HIGH, width, value) ->
      imm_width value >>= fun source ->
      unary value (fun value ->
          sprintf "Exp.extract %d %d (%s)" (source - 1) (source - width) value)
  | Bil.Cast (Bil.LOW, width, value) ->
      unary value (fun value ->
          sprintf "Exp.extract %d 0 (%s)" (width - 1) value)
  | Bil.Extract (high, low, value) ->
      unary value (fun value -> sprintf "Exp.extract %d %d (%s)" high low value)
  | Bil.Concat (left, right) -> binop "concat" left right
  | Bil.Ite (condition, yes, no) ->
      render_exp context condition >>= fun condition ->
      render_exp context yes >>= fun yes ->
      render_exp context no >>| fun no ->
      sprintf "Exp.ite (%s) (%s) (%s)" condition yes no
  | Bil.Load _ -> Error "loads are not supported in verified dispatcher paths"
  | Bil.Store _ -> Error "stores are not supported in verified dispatcher paths"
  | Bil.Let _ ->
      Error "let expressions are not supported in verified dispatcher paths"
  | Bil.Unknown _ ->
      Error "unknown values are not supported in verified dispatcher paths"

let list values = sprintf "[%s]" (String.concat ~sep:", " values)

let render_var var =
  match Var.typ var with
  | Type.Imm width when width > 0 -> Ok width
  | _ -> Error (sprintf "unsupported variable %s" (Var.name var))

let render_phi context (var, inputs) =
  render_var var >>= fun width ->
  List.map inputs ~f:(fun (exp, predecessor) ->
      render_exp context exp >>| fun exp ->
      sprintf "(%d, %s)" (label_id context predecessor) exp)
  |> Result.all
  >>| fun inputs ->
  sprintf "{ width := %d, lhs := %d, inputs := %s }" width (var_id context var)
    (list inputs)

let render_item context = function
  | Parse.Assign (var, exp) ->
      render_var var >>= fun width ->
      imm_width exp >>= fun exp_width ->
      if width <> exp_width then Error "assignment changes the value width"
      else
        render_exp context exp >>| fun rhs ->
        sprintf "{ width := %d, lhs := %d, rhs := %s }" width
          (var_id context var) rhs
  | Parse.Store _ | Parse.Leave _ ->
      Error "an effect item escaped the leaf boundary"

let render_terminator context = function
  | Parse.Br target -> Ok (sprintf "Terminator.br %d" (label_id context target))
  | Parse.Cbr (condition, yes, no) ->
      render_exp context condition >>| fun condition ->
      sprintf "Terminator.cbr (%s) %d %d" condition (label_id context yes)
        (label_id context no)
  | Parse.Switch (value, _, cases, default) ->
      imm_width value >>= fun width ->
      render_exp context value >>| fun value ->
      let cases =
        List.map cases ~f:(fun (word, target) ->
            sprintf "(BitVec.ofNat %d %s, %d)" width (word_value word)
              (label_id context target))
        |> list
      in
      sprintf "Terminator.switch (%s) %s %d" value cases
        (label_id context default)
  | Parse.Return -> Ok "Terminator.ret"
  | Parse.Unreachable -> Ok "Terminator.unreachable"

let has_effect items =
  List.exists items ~f:(function
    | Parse.Store _ | Parse.Leave _ -> true
    | Parse.Assign _ -> false)

let render_block context (block : Parse.block) =
  if has_effect block.items then
    Ok
      (sprintf
         "{ label := %d, phis := [], items := [], effect := true, terminator \
          := Terminator.unreachable }"
         (label_id context block.label))
  else
    List.map block.phis ~f:(render_phi context) |> Result.all >>= fun phis ->
    List.map block.items ~f:(render_item context) |> Result.all >>= fun items ->
    render_terminator context block.terminator >>| fun terminator ->
    sprintf
      "{ label := %d, phis := %s, items := %s, effect := false, terminator := \
       %s }"
      (label_id context block.label)
      (list phis) (list items) terminator

let render_blocks context blocks =
  List.map blocks ~f:(render_block context) |> Result.all >>| list

let rec validate_labels seen = function
  | [] -> Ok ()
  | (block : Parse.block) :: rest ->
      if Set.mem seen block.label then
        Error (sprintf "duplicate block label %s" block.label)
      else validate_labels (Set.add seen block.label) rest

let definition name value = sprintf "def %s := %s" name value

let source (witness : Witness.thread_witness) =
  validate_labels String.Set.empty (witness.edge :: witness.blocks)
  >>= fun () ->
  render_var witness.state >>= fun state_width ->
  if state_width <> Word.bitwidth witness.value then
    Error "the dispatcher state and value have different widths"
  else
    let context = context () in
    let threaded_blocks =
      witness.edge
      :: List.map witness.blocks ~f:(fun block ->
          if String.equal block.label witness.leaf.label then witness.leaf
          else block)
    in
    render_blocks context witness.blocks >>= fun original ->
    render_blocks context threaded_blocks >>= fun threaded ->
    let state = var_id context witness.state in
    let initial =
      sprintf "fun env => Env.set env %d (BitVec.ofNat %d %s)" state state_width
        (word_value witness.value)
    in
    let original_run =
      sprintf "run originalBlocks 65 %d %d (initial env)"
        (label_id context witness.header.label)
        (label_id context witness.predecessor)
    in
    let threaded_run =
      sprintf "run threadedBlocks 65 %d %d (initial env)"
        (label_id context witness.edge.label)
        (label_id context witness.edge_predecessor)
    in
    let definitions =
      [
        definition "originalBlocks : List Block" original;
        definition "threadedBlocks : List Block" threaded;
        definition "initial" initial;
        definition "original" ("fun env => " ^ original_run);
        definition "threaded" ("fun env => " ^ threaded_run);
      ]
    in
    let destination =
      "theorem destination (env : Env) : outcomeLabel (original env) = \
       outcomeLabel (threaded env) := by\n\
      \  rfl"
    in
    let values =
      Map.to_alist witness.env
      |> List.mapi ~f:(fun index (var, _) ->
          match render_var var with
          | Error message -> Error message
          | Ok width ->
              Ok
                (sprintf
                   "theorem definition_%d (env : Env) : outcomeVar (original \
                    env) %d (w := %d) = outcomeVar (threaded env) %d := by\n\
                   \  rfl"
                   index (var_id context var) width (var_id context var)))
      |> Result.all
    in
    values >>| fun values ->
    String.concat ~sep:"\n\n"
      ([ "import DeflattenProofs"; "open Deflatten" ]
      @ definitions @ [ destination ] @ values)
    ^ "\n"

let validate_split_shape (witness : Witness.split_witness) =
  match witness.split.terminator with
  | Parse.Cbr (condition, yes, no)
    when Exp.equal condition witness.condition
         && String.equal yes witness.left.edge.label
         && String.equal no witness.right.edge.label
         && List.is_empty witness.split.phis
         && List.is_empty witness.split.items ->
      Ok ()
  | _ -> Error "the split block does not match the certified conditional"

let split_source (witness : Witness.split_witness) =
  let left = witness.left and right = witness.right in
  validate_split_shape witness >>= fun () ->
  if not (Var.same left.state right.state) then
    Error "split edges have different dispatcher states"
  else
    validate_labels String.Set.empty
      (witness.split :: right.edge :: right.blocks)
    >>= fun () ->
    render_var left.state >>= fun state_width ->
    imm_width witness.condition >>= fun condition_width ->
    if condition_width <> 1 then Error "the split condition is not one bit"
    else if
      state_width <> Word.bitwidth left.value
      || state_width <> Word.bitwidth right.value
    then Error "the split state and values have different widths"
    else
      let context = context () in
      let edge_graph (edge : Parse.block) (leaf : Parse.block)
          (blocks : Parse.block list) =
        edge
        :: List.map blocks ~f:(fun block ->
            if String.equal block.label leaf.label then leaf else block)
      in
      let threaded_blocks = edge_graph witness.split right.leaf right.blocks in
      let left_original = left.blocks
      and left_threaded = edge_graph left.edge left.leaf left.blocks
      and right_original = right.blocks
      and right_threaded = edge_graph right.edge right.leaf right.blocks in
      render_blocks context left.blocks >>= fun original ->
      render_blocks context threaded_blocks >>= fun threaded ->
      render_blocks context left_original >>= fun left_original ->
      render_blocks context left_threaded >>= fun left_threaded ->
      render_blocks context right_original >>= fun right_original ->
      render_blocks context right_threaded >>= fun right_threaded ->
      render_exp context witness.condition >>= fun condition ->
      let state = var_id context left.state in
      let state_exp =
        sprintf
          "Exp.ite (%s) (Exp.int %d (BitVec.ofNat %d %s)) (Exp.int %d \
           (BitVec.ofNat %d %s))"
          condition state_width state_width (word_value left.value) state_width
          state_width (word_value right.value)
      in
      let initial =
        sprintf "fun env => Env.set env %d (eval env (%s))" state state_exp
      in
      let original_run =
        sprintf "run originalBlocks 65 %d %d (initial env)"
          (label_id context left.header.label)
          (label_id context left.predecessor)
      in
      let threaded_run =
        sprintf
          "if eval env (%s) = 1#1 then threadedLeft env else threadedRight env"
          condition
      in
      let branch_initial value =
        sprintf "Env.set env %d (BitVec.ofNat %d %s)" state state_width
          (word_value value)
      in
      let original_left =
        sprintf "run leftOriginalBlocks 65 %d %d (%s)"
          (label_id context left.header.label)
          (label_id context left.predecessor)
          (branch_initial left.value)
      and original_right =
        sprintf "run originalBlocks 65 %d %d (%s)"
          (label_id context left.header.label)
          (label_id context left.predecessor)
          (branch_initial right.value)
      and threaded_left =
        sprintf "run leftThreadedBlocks 65 %d %d (%s)"
          (label_id context left.edge.label)
          (label_id context left.edge_predecessor)
          (branch_initial left.value)
      and threaded_right =
        sprintf "run rightThreadedBlocks 65 %d %d (%s)"
          (label_id context right.edge.label)
          (label_id context right.edge_predecessor)
          (branch_initial right.value)
      in
      let definitions =
        [
          definition "originalBlocks : List Block" original;
          definition "threadedBlocks : List Block" threaded;
          definition "leftOriginalBlocks : List Block" left_original;
          definition "leftThreadedBlocks : List Block" left_threaded;
          definition "rightOriginalBlocks : List Block" right_original;
          definition "rightThreadedBlocks : List Block" right_threaded;
          definition "initial" initial;
          definition "originalLeft" ("fun env => " ^ original_left);
          definition "originalRight" ("fun env => " ^ original_right);
          definition "threadedLeft" ("fun env => " ^ threaded_left);
          definition "threadedRight" ("fun env => " ^ threaded_right);
          definition "original" ("fun env => " ^ original_run);
          definition "threaded" ("fun env => " ^ threaded_run);
        ]
      in
      let branch name projection left right original_blocks threaded_blocks =
        sprintf
          "theorem %s (env : Env) : %s (original%s env) = %s (threaded%s env) \
           := by\n\
          \  unfold original%s threaded%s %s %s\n\
          \  rfl"
          name projection left projection right left right original_blocks
          threaded_blocks
      in
      let compose name projection left right =
        sprintf
          "theorem %s (env : Env) : %s (original env) = %s (threaded env) := by\n\
          \  by_cases h : eval env (%s) = 1#1\n\
          \  · simp only [eval] at h\n\
          \    simpa [original, originalBlocks, leftOriginalBlocks, \
           originalLeft, threaded, initial, run_ite, eval, h, %s] using %s env\n\
          \  · simp only [eval] at h\n\
          \    simpa [original, originalBlocks, rightOriginalBlocks, \
           originalRight, threaded, initial, run_ite, eval, h, %s] using %s \
           env"
          name projection projection condition projection left projection right
      in
      let destination =
        branch "left_destination" "outcomeLabel" "Left" "Left"
          "leftOriginalBlocks" "leftThreadedBlocks"
        ^ "\n\n"
        ^ branch "right_destination" "outcomeLabel" "Right" "Right"
            "originalBlocks" "rightThreadedBlocks"
        ^ "\n\n"
        ^ compose "destination" "outcomeLabel" "left_destination"
            "right_destination"
      in
      let values =
        Map.merge left.env right.env ~f:(fun ~key:_ entry ->
            match entry with
            | `Both (_, value) | `Left value | `Right value -> Some value)
        |> Map.to_alist
        |> List.mapi ~f:(fun index (var, _) ->
            match render_var var with
            | Error message -> Error message
            | Ok width ->
                let id = var_id context var in
                let left = sprintf "left_definition_%d" index
                and right = sprintf "right_definition_%d" index in
                let branch_value name side original_blocks threaded_blocks =
                  sprintf
                    "theorem %s (env : Env) : outcomeVar (original%s env) %d \
                     (w := %d) = outcomeVar (threaded%s env) %d := by\n\
                    \  unfold original%s threaded%s %s %s\n\
                    \  rfl"
                    name side id width side id side side original_blocks
                    threaded_blocks
                in
                let compose_value name left right =
                  sprintf
                    "theorem %s (env : Env) : outcomeVar (original env) %d (w \
                     := %d) = outcomeVar (threaded env) %d := by\n\
                    \  by_cases h : eval env (%s) = 1#1\n\
                    \  · simp only [eval] at h\n\
                    \    simpa [original, originalBlocks, leftOriginalBlocks, \
                     originalLeft, threaded, initial, run_ite, eval, h, \
                     outcomeVar] using %s env\n\
                    \  · simp only [eval] at h\n\
                    \    simpa [original, originalBlocks, rightOriginalBlocks, \
                     originalRight, threaded, initial, run_ite, eval, h, \
                     outcomeVar] using %s env"
                    name id width id condition left right
                in
                Ok
                  (branch_value left "Left" "leftOriginalBlocks"
                     "leftThreadedBlocks"
                  ^ "\n\n"
                  ^ branch_value right "Right" "originalBlocks"
                      "rightThreadedBlocks"
                  ^ "\n\n"
                  ^ compose_value (sprintf "definition_%d" index) left right))
        |> Result.all
      in
      values >>| fun values ->
      String.concat ~sep:"\n\n"
        ([ "import DeflattenProofs"; "open Deflatten" ]
        @ definitions @ [ destination ] @ values)
      ^ "\n"

let split_proof = split_source

let validate_split witness =
  match split_source witness with
  | Error _ as error -> error
  | Ok source -> Bap_bil_plugin.Bil_lean.check source

let thread_proof = source

let validate_thread witness =
  match source witness with
  | Error _ as error -> error
  | Ok source -> Bap_bil_plugin.Bil_lean.check source
