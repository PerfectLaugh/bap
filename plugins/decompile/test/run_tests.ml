open Core
open Bap.Std
open Bap_core_theory
open Bap_decompile

let check name condition = if not condition then failwith name
let var name bits = Var.create ~is_virtual:true ~fresh:true name (Type.Imm bits)
let physical name bits = Var.create name (Type.Imm bits)
let int ?(width = 64) value = Bil.Int (Word.of_int ~width value)

let goto ?condition dst =
  Jmp.create_goto ?cond:condition (Direct (Term.tid dst))

let return () = Jmp.create_ret (Direct (Tid.create ()))

let block ?(phis = []) ?(defs = []) jumps =
  Blk.create ~phis ~defs ~jmps:jumps ()

let condition = var "condition" 1
let dummy_condition _ _ = { Ast.node = Ast.Const Word.b1; typ = Ast.Bool }

let structured sub =
  let cfg = Cfg.analyze sub in
  Collapse.structure cfg
    ~block:(fun _ -> [])
    ~edge:(fun _ -> [])
    ~call:(fun _ -> [])
    ~condition:dummy_condition

let rec exists_statement predicate statements =
  List.exists statements ~f:(fun stmt ->
      predicate stmt
      ||
      match stmt with
      | Ast.If (_, yes, no) -> exists_statement predicate (yes @ no)
      | Ast.While (_, body) | Ast.Do_while (body, _) ->
          exists_statement predicate body
      | Ast.Switch (_, cases, default) ->
          exists_statement predicate
            (List.concat_map cases ~f:snd @ Option.value default ~default:[])
      | _ -> false)

let test_diamond () =
  let yes = block [ return () ] and no = block [ return () ] in
  let entry = block [ goto ~condition:(Bil.var condition) yes; goto no ] in
  let sub = Sub.create ~name:"diamond" ~blks:[ entry; yes; no ] () in
  let ast = structured sub in
  check "diamond if"
    (exists_statement (function Ast.If _ -> true | _ -> false) ast)

let test_while () =
  let header_tid = Tid.create () and body_tid = Tid.create () in
  let exit = block [ return () ] in
  let enter_body =
    Jmp.create_goto ~cond:(Bil.var condition) (Direct body_tid)
  in
  let header = Blk.create ~tid:header_tid ~jmps:[ enter_body; goto exit ] () in
  let body =
    Blk.create ~tid:body_tid ~jmps:[ Jmp.create_goto (Direct header_tid) ] ()
  in
  let sub = Sub.create ~name:"while" ~blks:[ header; body; exit ] () in
  let ast = structured sub in
  check "while loop"
    (exists_statement (function Ast.While _ -> true | _ -> false) ast)

let test_do_while () =
  let exit = block [ return () ] in
  let self = Tid.create () in
  let back = Jmp.create_goto ~cond:(Bil.var condition) (Direct self) in
  let body = Blk.create ~tid:self ~jmps:[ back; goto exit ] () in
  let sub = Sub.create ~name:"do-while" ~blks:[ body; exit ] () in
  let ast = structured sub in
  check "do while loop"
    (exists_statement (function Ast.Do_while _ -> true | _ -> false) ast)

let test_switch () =
  let join = block [ return () ] in
  let case1 = block [ goto join ] and case2 = block [ goto join ] in
  let x = var "x" 32 in
  let entry =
    block
      [
        goto ~condition:(Bil.BinOp (EQ, Bil.var x, int 1)) case1;
        goto ~condition:(Bil.BinOp (EQ, Bil.var x, int 2)) case2;
        goto join;
      ]
  in
  let sub = Sub.create ~name:"switch" ~blks:[ entry; case1; case2; join ] () in
  let ast = structured sub in
  check "switch"
    (exists_statement (function Ast.Switch _ -> true | _ -> false) ast)

let test_irreducible () =
  let a = Tid.create () and b = Tid.create () in
  let exit = block [ return () ] in
  let to_a = Jmp.create_goto ~cond:(Bil.var condition) (Direct a) in
  let to_b = Jmp.create_goto (Direct b) in
  let entry = block [ to_a; to_b ] in
  let a_blk =
    Blk.create ~tid:a
      ~jmps:[ Jmp.create_goto ~cond:(Bil.var condition) (Direct b); goto exit ]
      ()
  in
  let b_blk = Blk.create ~tid:b ~jmps:[ Jmp.create_goto (Direct a) ] () in
  let sub =
    Sub.create ~name:"irreducible" ~blks:[ entry; a_blk; b_blk; exit ] ()
  in
  let ast = structured sub in
  check "irreducible goto"
    (exists_statement (function Ast.Goto _ -> true | _ -> false) ast)

let test_forward_collapse () =
  let next = block [ return () ] in
  let sub = Sub.create ~name:"forward" ~blks:[ block [ goto next ]; next ] () in
  let ast = structured sub in
  check "forward single predecessor collapse"
    (not
       (exists_statement
          (function Ast.Goto _ | Ast.Label _ -> true | _ -> false)
          ast))

let target () = Theory.Target.get ~package:"bap" "x86_64"

let test_ssa () =
  let a = var "a" 32 and dead = var "dead" 32 in
  let result = physical "result" 32 in
  let d1 = Def.create a (int 1) in
  let d2 = Def.create dead (int 2) in
  let d3 = Def.create result (Bil.BinOp (PLUS, Bil.var a, int 3)) in
  let blk = block ~defs:[ d1; d2; d3 ] [ return () ] in
  let sub = Sub.create ~name:"ssa" ~blks:[ blk ] () in
  let normalized = Ssa.normalize ~target:(target ()) sub in
  let defs =
    Term.enum def_t (Term.first blk_t normalized.sub |> Option.value_exn)
    |> Seq.to_list
  in
  check "dead definition" (List.length defs = 1);
  check "propagated definition" (Term.same (List.hd_exn defs) d3);
  check "propagated expression"
    (not (Set.mem (Def.free_vars (List.hd_exn defs)) a))

let test_types () =
  let pointer = var "pointer" 64 and value = var "value" 32 in
  let mem = Var.create "mem" (Type.Mem (`r64, `r8)) in
  let address = Bil.BinOp (PLUS, Bil.var pointer, int 8) in
  let load =
    Def.create value (Bil.Load (Bil.var mem, address, LittleEndian, `r32))
  in
  let arg = Arg.create pointer (Bil.var pointer) in
  let sub =
    Sub.create ~name:"fields" ~args:[ arg ]
      ~blks:[ block ~defs:[ load ] [ return () ] ]
      ()
  in
  let prog = Program.create ~subs:[ sub ] () in
  let types = Types.infer ~target:(target ()) prog in
  (match Types.typ types sub pointer with
  | Ast.Pointer (Ast.Structure _) -> ()
  | _ -> failwith "structure inference");
  check "field recovery"
    (List.exists (Types.structures types) ~f:(fun structure ->
         List.exists structure.Ast.fields ~f:(fun (_, offset, _) -> offset = 8)))

let test_overlap () =
  let pointer = var "pointer" 64 and x = var "x" 32 and y = var "y" 64 in
  let mem = Var.create "mem" (Type.Mem (`r64, `r8)) in
  let dx =
    Def.create x (Bil.Load (Bil.var mem, Bil.var pointer, LittleEndian, `r32))
  in
  let dy =
    Def.create y (Bil.Load (Bil.var mem, Bil.var pointer, LittleEndian, `r64))
  in
  let sub =
    Sub.create ~name:"overlap" ~blks:[ block ~defs:[ dx; dy ] [ return () ] ] ()
  in
  let types =
    Types.infer ~target:(target ()) (Program.create ~subs:[ sub ] ())
  in
  match Types.typ types sub pointer with
  | Ast.Pointer (Ast.Structure _) -> failwith "overlap accepted as structure"
  | _ -> ()

let test_signature_propagation () =
  let formal = var "formal" 64 and actual = var "actual" 64 in
  let value = var "value" 32 in
  let mem = Var.create "mem" (Type.Mem (`r64, `r8)) in
  let load =
    Def.create value
      (Bil.Load (Bil.var mem, Bil.var formal, LittleEndian, `r32))
  in
  let arg = Arg.create formal (Bil.var actual) in
  let callee =
    Sub.create ~name:"callee" ~args:[ arg ]
      ~blks:[ block ~defs:[ load ] [ return () ] ]
      ()
  in
  let after = block [ return () ] in
  let call =
    Jmp.create_call
      (Call.create
         ~return:(Direct (Term.tid after))
         ~target:(Direct (Term.tid callee))
         ())
  in
  let init = Def.create actual (int 0) in
  let caller =
    Sub.create ~name:"caller" ~blks:[ block ~defs:[ init ] [ call ]; after ] ()
  in
  let types =
    Types.infer ~target:(target ()) (Program.create ~subs:[ callee; caller ] ())
  in
  (match Types.typ types caller actual with
  | Ast.Pointer (Ast.Structure _) | Ast.Pointer (Ast.Int _) -> ()
  | _ -> failwith "signature propagation");
  let after_metadata = block [ return () ] in
  let metadata_call =
    Jmp.create_call
      (Call.create
         ~return:(Direct (Term.tid after_metadata))
         ~target:(Direct (Term.tid callee))
         ())
  in
  let metadata_caller =
    Sub.create ~name:"metadata_caller"
      ~blks:[ block [ metadata_call ]; after_metadata ]
      ()
  in
  let output =
    decompile ~target:(target ())
      (Program.create ~subs:[ callee; metadata_caller ] ())
    |> to_string
  in
  check
    ("metadata-only call argument\n" ^ output)
    (String.is_substring output ~substring:"fn_callee(v_")

let test_frame () =
  let sp = physical "RSP" 64 and value = var "value" 32 in
  let mem = Var.create "mem" (Type.Mem (`r64, `r8)) in
  let adjust = Def.create sp (Bil.BinOp (MINUS, Bil.var sp, int 16)) in
  let address = Bil.BinOp (PLUS, Bil.var sp, int 8) in
  let load =
    Def.create value (Bil.Load (Bil.var mem, address, LittleEndian, `r32))
  in
  let sub =
    Sub.create ~name:"frame"
      ~blks:[ block ~defs:[ adjust; load ] [ return () ] ]
      ()
  in
  let normalized = Ssa.normalize ~target:(target ()) sub in
  check "frame analysis" (Option.is_some normalized.frame)

let test_general_do_while () =
  let header = Tid.create () and latch = Tid.create () in
  let exit = block [ return () ] in
  let first =
    Blk.create ~tid:header ~jmps:[ Jmp.create_goto (Direct latch) ] ()
  in
  let last =
    Blk.create ~tid:latch
      ~jmps:
        [ Jmp.create_goto ~cond:(Bil.var condition) (Direct header); goto exit ]
      ()
  in
  let sub = Sub.create ~name:"general-do" ~blks:[ first; last; exit ] () in
  let ast = structured sub in
  check "general do while"
    (exists_statement (function Ast.Do_while _ -> true | _ -> false) ast)

let test_parallel_copies () =
  let a = physical "a" 32 and b = physical "b" 32 in
  let yes = block [] and no = block [] in
  let phi_a =
    Phi.of_list a [ (Term.tid yes, Bil.var b); (Term.tid no, Bil.var a) ]
  in
  let phi_b =
    Phi.of_list b [ (Term.tid yes, Bil.var a); (Term.tid no, Bil.var b) ]
  in
  let join = Blk.create ~phis:[ phi_a; phi_b ] ~jmps:[ return () ] () in
  let yes = Blk.create ~tid:(Term.tid yes) ~jmps:[ goto join ] () in
  let no = Blk.create ~tid:(Term.tid no) ~jmps:[ goto join ] () in
  let entry = block [ goto ~condition:(Bil.var condition) yes; goto no ] in
  let sub = Sub.create ~name:"parallel" ~blks:[ entry; yes; no; join ] () in
  let output =
    decompile ~target:(target ()) (Program.create ~subs:[ sub ] ()) |> to_string
  in
  check
    ("parallel phi temporaries\n" ^ output)
    (String.is_substring output ~substring:"phi_")

let test_killed_parameter () =
  let rdi = physical "RDI" 64 and rax = physical "RAX" 64 in
  let after = block ~defs:[ Def.create rax (Bil.var rdi) ] [ return () ] in
  let callee = Sub.create ~name:"callee" () in
  let call =
    Jmp.create_call
      (Call.create
         ~return:(Direct (Term.tid after))
         ~target:(Direct (Term.tid callee))
         ())
  in
  let caller = Sub.create ~name:"caller" ~blks:[ block [ call ]; after ] () in
  let types =
    Types.infer ~target:(target ()) (Program.create ~subs:[ callee; caller ] ())
  in
  check "parameter killed by call"
    (not
       (List.exists (Types.parameters types caller) ~f:(fun parameter ->
            String.equal parameter.Types.name "RDI")))

let test_implicit_parameters () =
  let rdi = physical "RDI" 64 and rax = physical "RAX" 64 in
  let def = Def.create rax (Bil.var rdi) in
  let sub =
    Sub.create ~name:"implicit" ~blks:[ block ~defs:[ def ] [ return () ] ] ()
  in
  let live = Ssa.live_in sub (Term.first blk_t sub |> Option.value_exn) in
  check "RDI entry liveness" (Set.mem live rdi);
  let types =
    Types.infer ~target:(target ()) (Program.create ~subs:[ sub ] ())
  in
  let params = Types.parameters types sub in
  check "implicit RDI parameter"
    (List.exists params ~f:(fun parameter ->
         String.equal parameter.Types.name "RDI"))

let test_condition_propagation () =
  let flag = physical "ZF" 1 and temporary = var "temporary" 1 in
  let def = Def.create temporary (Bil.var flag) in
  let yes = block [ return () ] and no = block [ return () ] in
  let entry =
    block ~defs:[ def ] [ goto ~condition:(Bil.var temporary) yes; goto no ]
  in
  let sub = Sub.create ~name:"condition" ~blks:[ entry; yes; no ] () in
  let original_jump = Term.first jmp_t entry |> Option.value_exn in
  let replaced =
    Jmp.substitute original_jump (Bil.var temporary) (Bil.var flag)
  in
  check "direct jump substitution"
    (Exp.equal (Jmp.cond replaced) (Bil.var flag));
  let replaced_block = Term.update jmp_t entry replaced in
  let replaced_jump = Term.first jmp_t replaced_block |> Option.value_exn in
  check "block jump substitution"
    (Exp.equal (Jmp.cond replaced_jump) (Bil.var flag));
  let normalized = Ssa.normalize ~target:(target ()) sub in
  let entry = Term.first blk_t normalized.sub |> Option.value_exn in
  let jump = Term.first jmp_t entry |> Option.value_exn in
  if not (Exp.equal (Jmp.cond jump) (Bil.var flag)) then
    failwithf "flag copy propagation: defs=%d cond=%s virtual=%b"
      (Term.length def_t entry)
      (Exp.to_string (Jmp.cond jump))
      (Var.is_virtual temporary) ()

let test_signed_comparison () =
  let a = var "a" 32 and b = var "b" 32 in
  let result = Bil.BinOp (MINUS, Bil.var a, Bil.var b) in
  let sign = Bil.Extract (31, 31, result) in
  let overflow =
    Bil.Extract
      ( 31,
        31,
        Bil.BinOp
          ( AND,
            Bil.BinOp (XOR, Bil.var a, Bil.var b),
            Bil.BinOp (XOR, Bil.var a, result) ) )
  in
  let simplified = Simplify.exp (Bil.BinOp (NEQ, sign, overflow)) in
  (match simplified with
  | Bil.BinOp (SLT, left, right)
    when Exp.equal left (Bil.var a) && Exp.equal right (Bil.var b) ->
      ()
  | _ -> failwithf "signed comparison: %s" (Exp.to_string simplified) ());
  let bit exp = Bil.Extract (31, 31, exp) in
  let neg exp = Bil.UnOp (NOT, exp) in
  let and3 x y z = Bil.BinOp (AND, x, Bil.BinOp (AND, y, z)) in
  let mem = Var.create "mem" (Type.Mem (`r32, `r8)) in
  let sp = physical "SP" 32 and fp = physical "R11" 32 in
  let a = Bil.Load (Bil.var mem, Bil.var sp, LittleEndian, `r32) in
  let b =
    Bil.Load
      ( Bil.var mem,
        Bil.BinOp (MINUS, Bil.var fp, int ~width:32 4),
        LittleEndian,
        `r32 )
  in
  let result = Bil.BinOp (MINUS, a, b) in
  let sign = bit result in
  let overflow =
    Bil.BinOp
      ( OR,
        and3 (bit a) (bit (neg b)) (neg sign),
        and3 (neg (bit a)) (neg (bit (neg b))) sign )
  in
  let simplified = Simplify.exp (Bil.BinOp (EQ, sign, overflow)) in
  (match simplified with
  | Bil.UnOp (NOT, Bil.BinOp (SLT, left, right))
    when Exp.equal left a && Exp.equal right b ->
      ()
  | _ -> failwithf "signed DNF comparison: %s" (Exp.to_string simplified) ());
  let narrow exp = Bil.Extract (31, 0, Bil.Cast (UNSIGNED, 64, exp)) in
  let a = narrow a and b = narrow b in
  let result = Bil.BinOp (MINUS, a, b) in
  let sign = bit result in
  let overflow =
    Bil.BinOp
      ( OR,
        and3 (bit (neg b)) (bit a) (neg sign),
        and3 (neg (bit (neg b))) (neg (bit a)) sign )
  in
  let simplified = Simplify.exp (Bil.BinOp (EQ, sign, overflow)) in
  match simplified with
  | Bil.UnOp (NOT, Bil.BinOp (SLT, left, right))
    when Exp.equal left a && Exp.equal right b ->
      ()
  | _ ->
      failwithf "signed cast DNF comparison: %s" (Exp.to_string simplified) ()

let test_physical_redefinition () =
  let x = physical "RAX" 64 and a = physical "A" 64 and b = physical "B" 64 in
  let yes = block [ return () ] and no = block [ return () ] in
  let entry =
    block
      ~defs:[ Def.create x (Bil.var a); Def.create x (Bil.var b) ]
      [ goto ~condition:(Bil.BinOp (EQ, Bil.var x, int 0)) yes; goto no ]
  in
  let sub = Sub.create ~name:"redefinition" ~blks:[ entry; yes; no ] () in
  let normalized = Ssa.normalize ~target:(target ()) sub in
  let entry = Term.first blk_t normalized.sub |> Option.value_exn in
  let jump = Term.first jmp_t entry |> Option.value_exn in
  let free = Jmp.free_vars jump in
  check "latest physical definition propagated" (Set.mem free b);
  check "stale physical definition blocked" (not (Set.mem free a))

let test_big_endian_frame () =
  let target = Theory.Target.get ~package:"bap" "powerpc" in
  let sp = physical "R1" 32 and value = var "value" 32 in
  let mem = Var.create "mem" (Type.Mem (`r32, `r8)) in
  let backchain = Bil.BinOp (MINUS, Bil.var sp, int ~width:32 32) in
  let save =
    Def.create mem
      (Bil.Store (Bil.var mem, backchain, Bil.var sp, BigEndian, `r32))
  in
  let load =
    Def.create value (Bil.Load (Bil.var mem, backchain, BigEndian, `r32))
  in
  let sub =
    Sub.create ~name:"backchain"
      ~blks:[ block ~defs:[ save; load ] [ return () ] ]
      ()
  in
  match Bap_recompile.Frame.analyze ~target sub with
  | Error error -> failwith ("big endian frame: " ^ error)
  | Ok frame ->
      let entry = Term.first blk_t sub |> Option.value_exn in
      let state = Bap_recompile.Frame.entry frame (Term.tid entry) in
      check "frame internal backchain"
        (Option.equal Int.equal
           (Bap_recompile.Frame.slot frame state backchain 32)
           (Some (-32)))

let test_exit_first_loop () =
  let header_tid = Tid.create () and body_tid = Tid.create () in
  let exit = block [ return () ] in
  let header =
    Blk.create ~tid:header_tid
      ~jmps:
        [
          Jmp.create_goto ~cond:(Bil.var condition) (Direct (Term.tid exit));
          Jmp.create_goto (Direct body_tid);
        ]
      ()
  in
  let body =
    Blk.create ~tid:body_tid ~jmps:[ Jmp.create_goto (Direct header_tid) ] ()
  in
  let sub = Sub.create ~name:"exit-first" ~blks:[ header; body; exit ] () in
  let cfg = Cfg.analyze sub in
  check "constant branch removes fallthrough"
    (List.length (Cfg.successors cfg body_tid) = 1);
  let ast = structured sub in
  check "exit-first while loop"
    (exists_statement (function Ast.While _ -> true | _ -> false) ast)

let test_condition_simplification () =
  let a = var "a" 32 and b = var "b" 32 in
  let packed =
    Bil.Concat
      ( Bil.BinOp (SLT, Bil.var a, Bil.var b),
        Bil.BinOp (EQ, Bil.var a, Bil.var b) )
  in
  (match Simplify.exp (Bil.Extract (1, 1, packed)) with
  | Bil.BinOp (SLT, _, _) -> ()
  | simplified ->
      failwithf "condition-register extraction: %s" (Exp.to_string simplified)
        ());
  (match
     Simplify.exp
       (Bil.BinOp
          ( PLUS,
            Bil.BinOp (PLUS, Bil.var a, Bil.UnOp (NOT, Bil.var b)),
            int ~width:32 1 ))
   with
  | Bil.BinOp (MINUS, left, right)
    when Exp.equal left (Bil.var a) && Exp.equal right (Bil.var b) ->
      ()
  | simplified ->
      failwithf "subtraction canonicalization: %s" (Exp.to_string simplified) ());
  (match
     Simplify.exp (Bil.BinOp (AND, Bil.var a, Bil.UnOp (NOT, Bil.var a)))
   with
  | Bil.Int zero when Word.is_zero zero -> ()
  | simplified ->
      failwithf "complement conjunction: %s" (Exp.to_string simplified) ());
  match
    Simplify.exp
      (Bil.BinOp (EQ, Bil.Extract (31, 31, Bil.var a), int ~width:1 0))
  with
  | Bil.BinOp (SLE, Bil.Int zero, left)
    when Word.is_zero zero && Exp.equal left (Bil.var a) ->
      ()
  | simplified ->
      failwithf "sign-bit comparison: %s" (Exp.to_string simplified) ()

let test_concise_loop_liveness () =
  let typ = Ast.Int (32, Ast.Signed) in
  let x = { Ast.id = 1; name = "x"; typ } in
  let y = { Ast.id = 2; name = "y"; typ } in
  let n = { Ast.id = 3; name = "n"; typ } in
  let zero = { Ast.node = Ast.Const (Word.zero 32); typ } in
  let one = { Ast.node = Ast.Const (Word.one 32); typ } in
  let binary operator left right =
    { Ast.node = Ast.Binary (operator, left, right); typ }
  in
  let func =
    {
      Ast.id = 0;
      name = "loop";
      signature = Ast.signature [];
      locals = [ x; y; n ];
      body =
        [
          Ast.Assign (Ast.var x, Ast.var n);
          Ast.Assign (Ast.var y, zero);
          Ast.While
            ( binary ">" (Ast.var x) zero,
              [
                Ast.Assign (Ast.var y, binary "+" (Ast.var y) one);
                Ast.Assign (Ast.var x, binary "-" (Ast.var x) one);
              ] );
          Ast.Return (Some (Ast.var y));
        ];
      external_ = false;
    }
  in
  let optimized = Optimize.program { structures = []; functions = [ func ] } in
  let body = (List.hd_exn optimized.functions).Ast.body in
  check "concise loop input live-in"
    (List.exists body ~f:(function
      | Ast.Assign ({ node = Ast.Var left; _ }, { node = Ast.Var right; _ })
        when left.Ast.id = x.Ast.id && right.Ast.id = n.Ast.id ->
          true
      | _ -> false));
  check "concise self-assignment rhs live-in"
    (exists_statement
       (function
         | Ast.Assign
             ( { node = Ast.Var left; _ },
               { node = Ast.Binary ("+", { node = Ast.Var right; _ }, _); _ } )
           when left.Ast.id = y.Ast.id && right.Ast.id = y.Ast.id ->
             true
         | _ -> false)
       body)

let test_readable_output () =
  let x = physical "x" 32 and rax = physical "RAX" 64 in
  let condition_var = var "condition" 1 in
  let mem = Var.create "mem" (Type.Mem (`r64, `r8)) in
  let cf = physical "CF" 1 and pf = physical "PF" 1 in
  let extracted = Bil.Extract (7, 4, Bil.var x) in
  let compare = Def.create condition_var (Bil.BinOp (EQ, extracted, int 0)) in
  let dead_cf = Def.create cf (Bil.Int Word.b0) in
  let dead_pf = Def.create pf (Bil.Int Word.b0) in
  let store =
    Def.create mem
      (Bil.Store (Bil.var mem, Bil.var x, int 1, LittleEndian, `r32))
  in
  let yes = block ~defs:[ Def.create rax (int 10) ] [ return () ] in
  let no = block ~defs:[ Def.create rax (int 20) ] [ return () ] in
  let entry =
    block
      ~defs:[ dead_cf; dead_pf; store; compare ]
      [ goto ~condition:(Bil.var condition_var) yes; goto no ]
  in
  let result = Arg.create ~intent:Out rax (Bil.var rax) in
  let sub =
    Sub.create ~name:"readable" ~args:[ result ] ~blks:[ entry; yes; no ] ()
  in
  let output =
    decompile ~target:(target ()) (Program.create ~subs:[ sub ] ()) |> to_string
  in
  List.iter
    [ "bir_extract_"; "bir_store_"; "bir_load_"; "block_"; "v_CF"; "v_PF" ]
    ~f:(fun unwanted ->
      check
        ("readable output contains " ^ unwanted ^ "\n" ^ output)
        (not (String.is_substring output ~substring:unwanted)));
  List.iter [ ">> 4"; "10"; "20"; "*v_x" ] ~f:(fun expected ->
      check
        ("readable output lacks " ^ expected ^ "\n" ^ output)
        (String.is_substring output ~substring:expected))

let test_frame_chain () =
  let rbp = { Ast.id = 1; name = "v_RBP"; typ = Ast.Int (64, Ast.Unsigned) } in
  let local =
    { Ast.id = 2; name = "local_8"; typ = Ast.Int (64, Ast.Unsigned) }
  in
  let temp =
    { Ast.id = 3; name = "v__150"; typ = Ast.Int (64, Ast.Unsigned) }
  in
  let result =
    { Ast.id = 4; name = "v_RAX"; typ = Ast.Int (64, Ast.Unsigned) }
  in
  let func =
    {
      Ast.id = 0;
      name = "fn_frame";
      signature = Ast.signature [];
      locals = [ rbp; local; temp; result ];
      body =
        [
          Ast.Assign (Ast.var local, Ast.var rbp);
          Ast.Assign (Ast.var temp, Ast.var local);
          Ast.Return (Some (Ast.var result));
        ];
      external_ = false;
    }
  in
  let optimized = Optimize.program { structures = []; functions = [ func ] } in
  let func = List.hd_exn optimized.functions in
  check "dead frame chain removed" (List.length func.body = 1);
  check "dead frame declarations removed"
    (List.for_all func.locals ~f:(fun local ->
         (not (String.equal local.Ast.name "v_RBP"))
         && (not (String.equal local.Ast.name "local_8"))
         && not (String.equal local.Ast.name "v__150")))

let test_concise_calls_and_bools () =
  let arg = { Ast.id = 10; name = "v_RDI"; typ = Ast.Int (64, Ast.Unsigned) } in
  let result =
    { Ast.id = 11; name = "v_RAX"; typ = Ast.Int (64, Ast.Unsigned) }
  in
  let x = { Ast.id = 12; name = "v_x"; typ = Ast.Int (32, Ast.Unsigned) } in
  let signature = Ast.signature [] in
  let fn = { Ast.id = 13; name = "fn_f"; typ = Ast.Function signature } in
  let call arguments =
    {
      Ast.node =
        Ast.Call { target = Ast.var fn; arguments; result = result.typ };
      typ = result.typ;
    }
  in
  let optimized =
    Optimize.statements
      [
        Ast.Assign (Ast.var arg, Ast.var x);
        Ast.Assign (Ast.var result, call [ Ast.var arg ]);
        Ast.Return (Some (Ast.var result));
      ]
  in
  (match optimized with
  | [ Ast.Return (Some { node = Ast.Call { arguments = [ actual ]; _ }; _ }) ]
    when Poly.equal actual (Ast.var x) ->
      ()
  | _ -> failwith "call/return inlining");
  let zero = { Ast.node = Ast.Const (Word.zero 32); typ = x.typ } in
  let comparison =
    { Ast.node = Ast.Binary ("==", Ast.var x, zero); typ = Ast.Bool }
  in
  let nested =
    { Ast.node = Ast.Binary ("==", comparison, zero); typ = Ast.Bool }
  in
  match Optimize.statements [ Ast.If (nested, [ Ast.Return None ], []) ] with
  | [ Ast.If ({ node = Ast.Binary ("!=", _, _); _ }, _, _) ] -> ()
  | _ -> failwith "nested boolean simplification"

let test_concise_source_forms () =
  let wide = { Ast.id = 1; name = "wide"; typ = Ast.Int (64, Ast.Unsigned) } in
  let narrow =
    { Ast.id = 2; name = "narrow"; typ = Ast.Int (32, Ast.Signed) }
  in
  let other = { Ast.id = 3; name = "other"; typ = narrow.typ } in
  let amount =
    { Ast.node = Ast.Const (Word.of_int ~width:64 32); typ = wide.typ }
  in
  let packed =
    {
      Ast.node =
        Ast.Binary
          ( "|",
            {
              Ast.node =
                Ast.Binary
                  ( "<<",
                    {
                      Ast.node = Ast.Binary (">>", Ast.var wide, amount);
                      typ = wide.typ;
                    },
                    amount );
              typ = wide.typ;
            },
            Ast.var narrow );
      typ = wide.typ;
    }
  in
  (match Optimize.statements [ Ast.Return (Some packed) ] with
  | [ Ast.Return (Some { node = Ast.Var value; _ }) ]
    when value.Ast.id = narrow.Ast.id ->
      ()
  | _ -> failwith "concise register concatenation");
  let cast_type = Ast.Int (32, Ast.Unknown_sign) in
  let cast =
    { Ast.node = Ast.Cast (cast_type, Ast.var narrow); typ = cast_type }
  in
  (match Optimize.statements [ Ast.Return (Some cast) ] with
  | [ Ast.Return (Some { node = Ast.Var value; _ }) ]
    when value.Ast.id = narrow.Ast.id ->
      ()
  | _ -> failwith "concise same-width cast");
  let less left right =
    { Ast.node = Ast.Binary ("<", left, right); typ = Ast.Bool }
  in
  let unequal =
    {
      Ast.node =
        Ast.Binary
          ( "|",
            less (Ast.var narrow) (Ast.var other),
            less (Ast.var other) (Ast.var narrow) );
      typ = Ast.Bool;
    }
  in
  match Optimize.statements [ Ast.If (unequal, [ Ast.Break ], []) ] with
  | [ Ast.If ({ node = Ast.Binary ("!=", _, _); _ }, _, _) ] -> ()
  | _ -> failwith "concise opposing comparisons"

let test_function_target_namespace () =
  let arg = { Ast.id = 0; name = "v_R0"; typ = Ast.Int (32, Ast.Unsigned) } in
  let x = { Ast.id = 1; name = "x"; typ = arg.typ } in
  let fn =
    { Ast.id = 0; name = "fn_target"; typ = Ast.Function (Ast.signature []) }
  in
  let call =
    {
      Ast.node =
        Ast.Call
          {
            target = Ast.var fn;
            arguments = [ Ast.var arg ];
            result = Ast.Unknown 0;
          };
      typ = Ast.Unknown 0;
    }
  in
  let optimized =
    Optimize.statements [ Ast.Assign (Ast.var arg, Ast.var x); Ast.Expr call ]
  in
  match optimized with
  | [
   Ast.Expr
     {
       node =
         Ast.Call
           {
             target = { node = Ast.Var target; _ };
             arguments = [ { node = Ast.Var actual; _ } ];
             _;
           };
       _;
     };
  ]
    when String.equal target.Ast.name "fn_target" && actual.Ast.id = x.Ast.id ->
      ()
  | _ -> failwith "function target/local namespace"

let test_concise_conditional_liveness () =
  let typ = Ast.Int (32, Ast.Unsigned) in
  let r1 = { Ast.id = 0; name = "v_R1"; typ } in
  let input = { Ast.id = 1; name = "input"; typ } in
  let copy = { Ast.id = 2; name = "copy"; typ } in
  let result = { Ast.id = 3; name = "result"; typ } in
  let one = { Ast.node = Ast.Const (Word.one 32); typ } in
  let ten = { Ast.node = Ast.Const (Word.of_int ~width:32 10); typ } in
  let func =
    {
      Ast.id = 0;
      name = "conditional";
      signature = Ast.signature ~return:typ [];
      locals = [ r1; input; copy; result ];
      body =
        [
          Ast.Assign (Ast.var r1, Ast.var input);
          Ast.Assign (Ast.var copy, Ast.var r1);
          Ast.If
            ( { Ast.node = Ast.Binary ("==", Ast.var r1, one); typ = Ast.Bool },
              [ Ast.Assign (Ast.var result, ten) ],
              [
                Ast.Assign (Ast.var result, Ast.var copy);
                Ast.Assign (Ast.var r1, Ast.var input);
              ] );
          Ast.Return (Some (Ast.var result));
        ];
      external_ = false;
    }
  in
  let optimized = Optimize.program { structures = []; functions = [ func ] } in
  let output = to_string optimized in
  check
    ("conditional temporary lost its definition\n" ^ output)
    ((not (String.is_substring output ~substring:"v_R1 =="))
    || String.is_substring output ~substring:"v_R1 =")

let test_concise () =
  let av = { Ast.id = 1; name = "v_RAX"; typ = Ast.Int (64, Ast.Unsigned) } in
  let xv = { Ast.id = 2; name = "v_x"; typ = Ast.Int (32, Ast.Unsigned) } in
  let pair =
    Optimize.statements
      [ Ast.Assign (Ast.var av, Ast.var xv); Ast.Return (Some (Ast.var av)) ]
  in
  (match pair with
  | [ Ast.Return (Some value) ] when Poly.equal value (Ast.var xv) -> ()
  | _ -> failwith "optimizer inlines assignment into return");
  let x = physical "x" 32 and temporary = physical "RBX" 64 in
  let result = physical "RAX" 64 in
  let result_arg = Arg.create ~intent:Out result (Bil.var result) in
  let temporary_def =
    Def.create temporary (Bil.Cast (UNSIGNED, 64, Bil.var x))
  in
  let use =
    Def.create result
      (Bil.BinOp (PLUS, Bil.Cast (LOW, 32, Bil.var temporary), Bil.var x))
  in
  let roundtrip =
    Sub.create ~name:"roundtrip" ~args:[ result_arg ]
      ~blks:[ block ~defs:[ temporary_def; use ] [ return () ] ]
      ()
  in
  let barrier =
    Sub.create ~name:"barrier" ~args:[ result_arg ]
      ~blks:
        [
          block ~defs:[ temporary_def; Def.create x (int 7); use ] [ return () ];
        ]
      ()
  in
  let default_output =
    decompile ~target:(target ()) (Program.create ~subs:[ roundtrip ] ())
    |> to_string
  in
  check
    ("default keeps precision cast\n" ^ default_output)
    (String.is_substring default_output ~substring:"(uint32_t)v_x");
  let concise_output =
    decompile ~concise:true ~target:(target ())
      (Program.create ~subs:[ roundtrip ] ())
    |> to_string
  in
  check
    ("concise removes temporary\n" ^ concise_output)
    (not (String.is_substring concise_output ~substring:"v_RBX"));
  check
    ("concise preserves result\n" ^ concise_output)
    (String.is_substring concise_output ~substring:"return v_x + v_x");
  let barrier_output =
    decompile ~concise:true ~target:(target ())
      (Program.create ~subs:[ barrier ] ())
    |> to_string
  in
  check
    ("concise respects reassignment\n" ^ barrier_output)
    ((not (String.is_substring barrier_output ~substring:"7 + 7"))
    && String.is_substring barrier_output ~substring:"v_x + 7");
  check
    ("concise barrier preserves result\n" ^ barrier_output)
    (String.is_substring barrier_output ~substring:"return v_x + 7")

let test_multi_return () =
  let r64 = Theory.Bitv.define 64 in
  let registers =
    List.map [ "RAX"; "RDX" ] ~f:(fun name ->
        Theory.Var.forget (Theory.Var.define r64 name))
  in
  let target =
    Theory.Target.declare ~package:"decompile-test" "multi-return"
      ~parent:(target ()) ~bits:64 ~vars:registers
      ~regs:Theory.Role.Register.[ ([ function_return ], registers) ]
  in
  let rax = physical "RAX" 64 and rdx = physical "RDX" 64 in
  let callee =
    Sub.create ~name:"callee"
      ~blks:
        [
          block
            ~defs:[ Def.create rax (int 1); Def.create rdx (int 2) ]
            [ return () ];
        ]
      ()
  in
  let after =
    block
      ~defs:[ Def.create rax (Bil.BinOp (PLUS, Bil.var rax, Bil.var rdx)) ]
      [ return () ]
  in
  let call =
    Jmp.create_call
      (Call.create
         ~return:(Direct (Term.tid after))
         ~target:(Direct (Term.tid callee))
         ())
  in
  let caller = Sub.create ~name:"caller" ~blks:[ block [ call ]; after ] () in
  let output =
    decompile ~target (Program.create ~subs:[ callee; caller ] ()) |> to_string
  in
  List.iter
    [
      "struct recovered_";
      ".field_0 = v_RAX";
      ".field_8 = v_RDX";
      "return_value.field_0";
      "return_value.field_8";
    ] ~f:(fun expected ->
      check
        ("multi return lacks " ^ expected ^ "\n" ^ output)
        (String.is_substring output ~substring:expected))

let test_external_and_emitter () =
  let external_sub = Sub.create ~name:"external" () in
  let x = physical "x" 32 and y = physical "y" 32 in
  let z = physical "RAX" 64 in
  let dz =
    Def.create z
      (Bil.BinOp (TIMES, Bil.BinOp (PLUS, Bil.var x, Bil.var y), int 3))
  in
  let result = Arg.create ~intent:Out z (Bil.var z) in
  let internal =
    Sub.create ~name:"internal" ~args:[ result ]
      ~blks:[ block ~defs:[ dz ] [ return () ] ]
      ()
  in
  let output =
    decompile ~target:(target ())
      (Program.create ~subs:[ external_sub; internal ] ())
    |> to_string
  in
  check "external prototype"
    (String.is_substring output ~substring:"fn_external");
  check
    ("unknown call\n" ^ Sub.to_string internal ^ "\n" ^ output)
    (not (String.is_substring output ~substring:"bir_sub_"));
  if not (String.is_substring output ~substring:"(v_x + v_y) *") then
    failwith ("emitter precedence\n" ^ output)

(* the [%] of C truncates, so SMOD is the helper, which is checked in C, if
   there is its compiler, on the table of the modulus, whose signs follow
   the divisor, and on the divisors, where [%] is undefined *)
let test_signed_modulus () =
  let x = physical "x" 32 and y = physical "y" 32 in
  let z = physical "RAX" 32 in
  let def = Def.create z (Bil.BinOp (SMOD, Bil.var x, Bil.var y)) in
  let sub =
    Sub.create ~name:"modulus"
      ~args:[ Arg.create ~intent:Out z (Bil.var z) ]
      ~blks:[ block ~defs:[ def ] [ return () ] ]
      ()
  in
  let output =
    decompile ~target:(target ()) (Program.create ~subs:[ sub ] ()) |> to_string
  in
  check
    ("signed modulus is not %\n" ^ output)
    (String.is_substring output ~substring:"bir_smod32(");
  check
    ("no truncating remainder\n" ^ output)
    (not (String.is_substring output ~substring:"v_x % "));
  let start = String.substr_index_exn output ~pattern:"static inline" in
  let finish = String.substr_index_exn ~pos:start output ~pattern:"\n}\n" + 3 in
  let helper = String.sub output ~pos:start ~len:(finish - start) in
  if Stdlib.Sys.command "command -v cc >/dev/null" = 0 then begin
    let path = Stdlib.Filename.temp_file "bap-smod" ".c" in
    let exe = path ^ ".exe" in
    let cases =
      [
        (-5, 3, 1);
        (5, -3, -1);
        (-5, -3, -2);
        (5, 3, 2);
        (6, 3, 0);
        (-6, 3, 0);
        (7, 0, 7);
        (-7, 0, -7);
        (5, -1, 0);
      ]
    in
    let checks =
      List.map cases ~f:(fun (x, y, r) ->
          sprintf "  if (bir_smod32(%d, %d) != %d) return 1;" x y r)
    in
    Out_channel.write_all path
      ~data:
        (String.concat ~sep:"\n"
           ([ "#include <stdint.h>"; helper; "int main(void) {" ]
           @ checks
           @ [
               "  if (bir_smod32(INT32_MIN, -1) != 0) return 2;";
               "  if (bir_smod32(-2, INT32_MIN) != -2) return 3;";
               "  if (bir_smod32(2, INT32_MIN) != 2 + INT32_MIN) return 4;";
               "  return 0;";
               "}";
             ]));
    let status =
      Stdlib.Sys.command
        (sprintf
           "cc -std=c11 -fsanitize=undefined \
            -fsanitize-undefined-trap-on-error -o %s %s && %s"
           exe path exe)
    in
    Stdlib.Sys.remove path;
    if Stdlib.Sys.file_exists exe then Stdlib.Sys.remove exe;
    check
      (sprintf "the helper in C exited with %d\n%s" status helper)
      (status = 0)
  end

let test_ranges_and_conditional_move () =
  let sum = Bil.BinOp (PLUS, int 1, int 2) in
  check "range exact arithmetic"
    (Option.equal Word.equal
       (Range.value (Range.eval Var.Map.empty sum))
       (Some (Word.of_int ~width:64 3)));
  let x = var "range-x" 32 and result = var "range-result" 1 in
  let extended = Bil.Cast (UNSIGNED, 64, Bil.var x) in
  check "range unsigned sign"
    (Range.sign_nonnegative (Range.eval Var.Map.empty extended));
  let comparison = Def.create result (Bil.BinOp (SLT, extended, int 3)) in
  let sub =
    Sub.create ~name:"range"
      ~blks:[ block ~defs:[ comparison ] [ return () ] ]
      ()
    |> Range.simplify_sub
  in
  let def =
    Term.first def_t (Term.first blk_t sub |> Option.value_exn)
    |> Option.value_exn
  in
  check "signed to unsigned comparison"
    (match Def.rhs def with Bil.BinOp (LT, _, _) -> true | _ -> false);
  let joined =
    Range.join_ranges
      (Range.constant (Word.of_int ~width:32 7))
      (Range.constant (Word.of_int ~width:32 7))
  in
  check "range exact phi join"
    (Option.equal Word.equal (Range.value joined)
       (Some (Word.of_int ~width:32 7)));
  let typ = Ast.Int (32, Ast.Signed) in
  let destination = { Ast.id = 1; name = "destination"; typ } in
  let condition = { Ast.id = 2; name = "condition"; typ = Ast.Bool } in
  let left = { Ast.node = Ast.Const (Word.of_int ~width:32 10); typ } in
  let right = { Ast.node = Ast.Const (Word.of_int ~width:32 20); typ } in
  let diamond =
    Ast.If
      ( Ast.var condition,
        [ Ast.Assign (Ast.var destination, left) ],
        [ Ast.Assign (Ast.var destination, right) ] )
  in
  (match Optimize.statements [ diamond ] with
  | [ Ast.Assign (_, { node = Ast.Conditional _; _ }) ] -> ()
  | _ -> failwith "conditional move");
  let call =
    {
      Ast.node =
        Ast.Call
          {
            target =
              {
                Ast.node = Ast.Var { destination with name = "fn" };
                typ = Ast.Function (Ast.signature []);
              };
            arguments = [];
            result = typ;
          };
      typ;
    }
  in
  match
    Optimize.statements
      [
        Ast.If
          ( Ast.var condition,
            [ Ast.Assign (Ast.var destination, call) ],
            [ Ast.Assign (Ast.var destination, right) ] );
      ]
  with
  | [ Ast.Assign (_, { node = Ast.Conditional _; _ }) ] ->
      failwith "conditional move side effects"
  | _ -> ()

let test_jump_tables () =
  let index = var "switch-index" 32
  and mem = Var.create "mem" (Type.Mem (`r64, `r8)) in
  let first = Sub.create ~name:"first" ()
  and second = Sub.create ~name:"second" () in
  let first = Term.set_attr first address (Word.of_int ~width:64 0x2000) in
  let second = Term.set_attr second address (Word.of_int ~width:64 0x3000) in
  let target = block [ return () ] in
  let table = Bil.Int (Word.of_int ~width:64 0x1000) in
  let address =
    Bil.BinOp
      ( PLUS,
        table,
        Bil.BinOp
          (TIMES, Bil.Cast (UNSIGNED, 64, Bil.var index), int ~width:64 8) )
  in
  let indirect =
    Jmp.create_goto
      (Indirect (Bil.Load (Bil.var mem, address, LittleEndian, `r64)))
  in
  let switch = block [ indirect ] in
  let guard =
    block
      [
        goto ~condition:(Bil.BinOp (LT, Bil.var index, int ~width:32 2)) switch;
      ]
  in
  let caller = Sub.create ~name:"caller" ~blks:[ guard; switch; target ] () in
  let make_memory values =
    let data = Bytes.make 16 '\000' in
    List.iteri values ~f:(fun i value ->
        Stdlib.Bytes.set_int64_le data (i * 8) (Int64.of_int value));
    let mem =
      Memory.create LittleEndian
        (Word.of_int ~width:64 0x1000)
        (Bigstring.of_bytes data)
      |> Or_error.ok_exn
    in
    Memmap.add Memmap.empty mem (Value.create Image.section "table")
  in
  let recover values =
    Jump.recover ~memory:(make_memory values)
      (Program.create ~subs:[ first; second; caller ] ())
  in
  let check_targets prog =
    let caller = Term.find_exn sub_t prog (Term.tid caller) in
    let switch = List.nth_exn (Term.enum blk_t caller |> Seq.to_list) 1 in
    let jmps = Term.enum jmp_t switch |> Seq.to_list in
    check "jump table branch count" (List.length jmps = 2);
    List.iter
      [ Term.tid first; Term.tid second ]
      ~f:(fun tid ->
        check
          ("jump table target " ^ Tid.to_string tid ^ "\n"
          ^ String.concat ~sep:"\n" (List.map jmps ~f:Jmp.to_string))
          (List.exists jmps ~f:(fun jmp ->
               match Jmp.kind jmp with
               | Goto (Direct target) -> Tid.equal tid target
               | _ -> false)))
  in
  check_targets (recover [ 0x2000; 0x3000 ]);
  check_targets (recover [ 0x1000; 0x2000 ]);
  let invalid = recover [ 0; 0 ] in
  let caller = Term.find_exn sub_t invalid (Term.tid caller) in
  let switch = List.nth_exn (Term.enum blk_t caller |> Seq.to_list) 1 in
  check "invalid jump table preserved"
    (List.exists
       (Term.enum jmp_t switch |> Seq.to_list)
       ~f:(fun jmp ->
         match Jmp.kind jmp with Goto (Indirect _) -> true | _ -> false))

let test_rule_scheduler () =
  let increment =
    Rule.rule ~operations:[ "int" ] "increment" (fun value -> Some (value + 1))
  in
  let result, summary =
    Rule.run ~limit:3
      ~key:(fun _ -> "int")
      ~equal:Int.equal
      ~map:(fun f value -> f value)
      [ increment ] 0
  in
  if not (result = 3 && summary.changes = 3) then
    failwithf "rule pass cap: result=%d changes=%d" result summary.changes ();
  check "rule application count"
    (Option.equal Int.equal
       (List.Assoc.find summary.applications "increment" ~equal:String.equal)
       (Some 3));
  let unused = Rule.rule ~operations:[ "other" ] "unused" (fun _ -> Some 99) in
  let result, _ =
    Rule.run ~limit:3
      ~key:(fun _ -> "int")
      ~equal:Int.equal
      ~map:(fun f value -> f value)
      [ unused; increment ] 0
  in
  check "rule operation indexing" (result = 3)

let test_high_variables () =
  let input = var "input" 64 and a = var "a" 64 and b = var "b" 64 in
  let result = var "result" 64 in
  let defs =
    [
      Def.create a (Bil.var input);
      Def.create b (Bil.var a);
      Def.create result (Bil.var b);
    ]
  in
  let sub = Sub.create ~name:"high" ~blks:[ block ~defs [ return () ] ] () in
  let high = High.create sub in
  let root = High.representative high input in
  check "copy chain source variable"
    (List.for_all [ a; b; result ] ~f:(fun var ->
         Var.equal root (High.representative high var)));
  let first = var "version" 64 and second = var "version" 64 in
  let use = var "use" 64 in
  let defs =
    [
      Def.create first (int 1);
      Def.create second (int 2);
      Def.create use (Bil.var first);
    ]
  in
  let sub = Sub.create ~name:"overlap" ~blks:[ block ~defs [ return () ] ] () in
  let high = High.create sub in
  check "overlapping source versions"
    (not
       (Var.equal
          (High.representative high first)
          (High.representative high second)));
  let phi_result = var "phi" 64 in
  let left = block [ return () ] and right = block [ return () ] in
  let join =
    Blk.create
      ~phis:
        [
          Phi.of_list phi_result
            [ (Term.tid left, Bil.var a); (Term.tid right, Bil.var b) ];
        ]
      ()
  in
  let high =
    High.create (Sub.create ~name:"phi" ~blks:[ left; right; join ] ())
  in
  check "phi source merge"
    (Var.equal
       (High.representative high phi_result)
       (High.representative high a))

let test_architecture name expected =
  let target = Theory.Target.get ~package:"bap" name in
  let bits = Theory.Target.bits target in
  let input =
    physical (if String.is_empty expected then "unused" else expected) bits
  in
  let result = physical "result" bits in
  let mem = Var.create "mem" (Type.Mem (`r64, `r8)) in
  let endian =
    if
      Theory.Endianness.equal
        (Theory.Target.endianness target)
        Theory.Endianness.eb
    then BigEndian
    else LittleEndian
  in
  let calc = Def.create result (Bil.BinOp (PLUS, Bil.var input, int 1)) in
  let load =
    Def.create result (Bil.Load (Bil.var mem, Bil.var input, endian, `r32))
  in
  let result_arg = Arg.create ~intent:Out result (Bil.var result) in
  let after = block [ return () ] in
  let callee_arg = Arg.create input (Bil.var input) in
  let callee = Sub.create ~name:"callee" ~args:[ callee_arg ] () in
  let callee = Term.set_attr callee address (Word.of_int ~width:bits 0x1234) in
  let call =
    Jmp.create_call
      (Call.create
         ~return:(Direct (Term.tid after))
         ~target:(Indirect (Bil.Int (Word.of_int ~width:bits 0x1234)))
         ())
  in
  let input_def = Def.create input (int 3) in
  let sub =
    Sub.create ~name:"architecture" ~args:[ result_arg ]
      ~blks:[ block ~defs:[ calc; load; input_def ] [ call ]; after ]
      ()
  in
  let prog = Program.create ~subs:[ sub; callee ] () in
  let types = Types.infer ~target prog in
  (if not (String.is_empty expected) then
     let parameters = Types.parameters types sub in
     check (name ^ " argument")
       (List.exists parameters ~f:(fun parameter ->
            String.equal parameter.Types.name expected)));
  List.iter [ false; true ] ~f:(fun concise ->
      let output = decompile ~concise ~target prog |> to_string in
      check (name ^ " decompile")
        (String.is_substring output ~substring:"fn_architecture");
      check
        (name ^ " direct call\n" ^ output)
        (String.is_substring output ~substring:"fn_callee(3)");
      match endian with
      | BigEndian ->
          check (name ^ " big endian")
            (String.is_substring output ~substring:"bir_load_be32")
      | LittleEndian -> ())

let test_all_architectures () =
  List.iter
    [
      ("x86_64", "RDI");
      ("i386", "");
      ("i86", "");
      ("aarch64", "R0");
      ("aarch64_be", "R0");
      ("armv7+le", "R0");
      ("armeb", "R0");
      ("armv7-m+le", "R0");
      ("mips", "R4");
      ("mipsel", "R4");
      ("mips64", "R4");
      ("mips64el", "R4");
      ("powerpc", "R3");
      ("powerpc64", "R3");
      ("riscv32", "X10");
      ("riscv64", "X10");
      ("systemz", "R2");
    ]
    ~f:(fun (name, expected) -> test_architecture name expected)

let () =
  X86_target.load ();
  Arm_target.load ();
  Bap_mips_target.load ();
  Bap_powerpc_target.load ();
  ignore Bap_riscv_target.parent;
  ignore Bap_systemz_target.parent;
  test_all_architectures ();
  test_diamond ();
  test_while ();
  test_do_while ();
  test_general_do_while ();
  test_parallel_copies ();
  test_switch ();
  test_irreducible ();
  test_ssa ();
  test_types ();
  test_overlap ();
  test_signature_propagation ();
  test_frame ();
  test_killed_parameter ();
  test_implicit_parameters ();
  test_condition_propagation ();
  test_signed_comparison ();
  test_physical_redefinition ();
  test_big_endian_frame ();
  test_exit_first_loop ();
  test_condition_simplification ();
  test_concise_loop_liveness ();
  test_readable_output ();
  test_frame_chain ();
  test_concise_calls_and_bools ();
  test_concise_source_forms ();
  test_function_target_namespace ();
  test_concise_conditional_liveness ();
  test_concise ();
  test_multi_return ();
  test_external_and_emitter ();
  test_signed_modulus ();
  test_ranges_and_conditional_move ();
  test_rule_scheduler ();
  test_high_variables ();
  test_forward_collapse ();
  test_jump_tables ();
  print_endline "decompiler tests passed"
