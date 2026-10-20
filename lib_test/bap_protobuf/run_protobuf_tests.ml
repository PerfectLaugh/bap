open Core
open OUnit2
open Bap.Std

module Example = struct
  let entry = Blk.create ()
  let b1 = Blk.create ()
  let b2 = Blk.create ()
  let b3 = Blk.create ()
  let b4 = Blk.create ()
  let b5 = Blk.create ()
  let b6 = Blk.create ()
  let b7 = Blk.create ()
  let exit = Blk.create ()
  let i = Var.create "i" reg32_t
  let j = Var.create "j" reg32_t
  let k = Var.create "k" bool_t
  let t = Var.create ~is_virtual:true "t" reg64_t
  let mem = Var.create "mem" (mem64_t `r8)
  let _1 = Bil.int (Word.one 32)
  let _2 = Bil.int (Word.of_int32 2l)
  let _F = Bil.int Word.b0
  let _T = Bil.int Word.b1
  let def var exp b = Term.append def_t b @@ Def.create var exp

  let cond blk cond t f =
    let jt = Jmp.create_goto ~cond (Label.direct (Term.tid t)) in
    let jf = Jmp.create_goto (Label.direct (Term.tid f)) in
    let blk = Term.append jmp_t blk jt in
    Term.append jmp_t blk jf

  let goto dst src =
    Term.append jmp_t src @@ Jmp.create_goto (Label.direct (Term.tid dst))

  let entry = entry |> goto b1
  let b1 = b1 |> def k _F |> def i _1 |> def j _2 |> goto b2
  let b2 = cond b2 Bil.(var i <= var j) b3 b4

  let b3 =
    b3
    |> def j Bil.(var j * _2)
    |> def k _T
    |> def i Bil.(var i + _1)
    |> goto b2

  let b4 = cond b4 Bil.(var k) b5 b6

  let b5 =
    let call =
      Call.create ()
        ~return:(Label.direct (Term.tid exit))
        ~target:(Label.indirect (Bil.var j))
    in
    Term.append jmp_t b5 (Jmp.create_call call)

  (* every kind of the expressions *)
  let b6 =
    b6
    |> def t
         Bil.(
           load ~mem:(var mem) ~addr:(int (Word.of_int64 0x1000L)) LittleEndian
             `r64)
    |> def mem
         Bil.(
           store ~mem:(var mem) ~addr:(var t) (extract ~hi:7 ~lo:0 (var t))
             BigEndian `r8)
    |> def i Bil.(cast signed 32 (cast low 16 (var i)))
    |> def j Bil.(let_ t (cast unsigned 64 (var i)) (cast high 32 (var t)))
    |> def k Bil.(ite ~if_:(var k) ~then_:(lnot (var k)) ~else_:(unknown "?" bool_t))
    |> def t Bil.(concat (var i) (unop neg (var j)))
    |> def j Bil.(var i lsl var j land (var i lxor var j))
    |> fun b ->
    Term.append jmp_t b (Jmp.create_int 0x80 (Term.tid b7))

  let b7 = Term.append jmp_t b7 (Jmp.create_ret (Label.indirect Bil.(var j)))
  let exit = def i Bil.(var i + _1) exit

  let sub =
    let sub = Sub.create ~name:"example" () in
    let sub = Term.append arg_t sub (Arg.create ~intent:In i Bil.(var i)) in
    let sub = Term.append arg_t sub (Arg.create j Bil.(var j)) in
    List.fold [ entry; b1; b2; b3; b4; b5; b6; b7; exit ] ~init:sub
      ~f:(Term.append blk_t)

  let program = Term.append sub_t (Program.create ()) sub

  let bil =
    Bil.
      [
        i := var i + _1;
        while_ (var i < var j) [ i := var i * _2; special "pause" ];
        if_ (var k) [ jmp (var j) ] [ cpuexn 3 ];
      ]
end

let fmts = [ ("pb", `pb); ("json", `json) ]

let program_roundtrip fmt ctxt =
  let program =
    Bir_proto.program_to_string fmt Example.program
    |> Bir_proto.program_of_string fmt
  in
  assert_equal ~ctxt ~cmp:Program.equal ~printer:Program.to_string
    Example.program program

let bil_roundtrip fmt ctxt =
  let bil =
    Bil_proto.bil_to_string fmt Example.bil |> Bil_proto.bil_of_string fmt
  in
  assert_equal ~ctxt ~cmp:(fun x y -> Bil.compare x y = 0) ~printer:Bil.to_string Example.bil bil

(* the formats, that the plugin registers *)
let data_roundtrip (name, _) ctxt =
  let data = Program.to_bytes ~fmt:name Example.program in
  assert_equal ~ctxt ~cmp:Program.equal ~printer:Program.to_string
    Example.program
    (Program.of_bytes ~fmt:name data)

let suite =
  "protobuf"
  >::: List.concat_map fmts ~f:(fun ((name, fmt) as f) ->
      [
        ("program/" ^ name >:: program_roundtrip fmt);
        ("bil/" ^ name >:: bil_roundtrip fmt);
        ("data/" ^ name >:: data_roundtrip f);
      ])

let () =
  match Bap_main.init () with
  | Error err ->
      Format.eprintf "Failed to initialize BAP: %a@\n%!"
        Bap_main.Extension.Error.pp err;
      exit 1
  | Ok () -> run_test_tt_main suite
