(**
   In order to test stub resolver we generate a dummy programs like
   in the example below:

   0000000b: program
   00000008: sub a()
   00000007:


   0000000a: sub b()
   00000009:

   ...

   and provide a knowledge about each symbol:
   if it's a stub and if it has aliases.

*)


open Core
open Bap_core_theory
open Bap_knowledge
open Bap.Std
open OUnit2

open KB.Syntax

module Cfg = Graphs.Cfg
module Dis = Disasm_expert.Basic

type sym = {
  is_stub : bool;
  aliases : string list;
}

let run dis mem =
  Or_error.ok_exn @@
  Dis.run dis mem
    ~init:[]
    ~return:Result.return
    ~stop_on:[`Valid]
    ~invalid:(fun state _ pos -> Dis.step state pos)
    ~hit:(fun state mem insn insns ->
        Dis.step state ((mem, Insn.of_basic insn) :: insns))

let block_of_bytes addr b =
  let code = Bigstring.of_string b in
  let mem =
    Or_error.ok_exn @@
    Memory.create LittleEndian addr code in
  let dis = Or_error.ok_exn @@ Dis.create ~backend:"llvm"
      (Arch.to_string `x86_64) in
  let insns = run dis mem in
  Block.create mem insns

let add_symbol symtab name addr bytes =
  let block = block_of_bytes addr bytes in
  Symtab.add_symbol symtab
    (name, block, Cfg.Node.insert block Cfg.empty)

let collect_stubs syms =
  Map.fold syms ~init:(Set.empty (module String))
    ~f:(fun ~key:name ~data:{is_stub} stubs ->
        if is_stub
        then Set.add stubs name
        else stubs)

let tag_stubs syms prog =
  let stubs = collect_stubs syms in
  let make_addr sub =
    Addr.of_int64 @@ Int63.to_int64 @@ KB.Object.id (Term.tid sub) in
  Term.map sub_t prog ~f:(fun sub ->
      if Set.mem stubs (Sub.name sub)
      then Term.set_attr sub Sub.stub ()
      else
        let addressed = Term.set_attr sub address (make_addr sub) in
        Term.set_attr addressed filename "test")



let cfg_of_block b = Cfg.Node.insert b Cfg.empty

let tid_for_name_exn prog name =
  Term.to_sequence sub_t prog |>
  Seq.find_map
    ~f:(fun s ->
        if String.equal (Sub.name s) name
        then Some (Term.tid s)
        else None) |> function
  | None -> failwithf "no tid for name %s" name ()
  | Some s -> s

let provide_aliases prog syms =
  Toplevel.exec begin
    Map.to_sequence syms |>
    KB.Seq.iter ~f:(fun (name,{aliases}) ->
        let tid = tid_for_name_exn prog name in
        let aliases = Set.of_list (module String) aliases in
        KB.provide Theory.Label.aliases tid aliases)
  end

let create_program syms =
  let nop = "\x66\x90" in
  let step = Addr.of_int64 2L in
  let rec loop symtab addr = function
    | [] -> symtab
    | name :: names ->
      let symtab = add_symbol symtab name addr nop in
      loop symtab Addr.(addr + step) names in
  let symtab = loop Symtab.empty (Addr.zero 64) (Map.keys syms) in
  let prog = Program.lift symtab |> tag_stubs syms in
  provide_aliases prog syms;
  prog


let string_of_tids tids =
  let content =
    Map.to_alist tids |>
    List.map ~f:(fun (src,dst) ->
        Format.asprintf "%s -> %s" (Tid.name src) (Tid.name dst)) in
  Format.asprintf "(%s)" (String.concat ~sep:", " content)

let run ?(skip=false) name symbols expected should_fail _ctxt =
  let syms =
    List.fold symbols ~init:(Map.empty (module String))
      ~f:(fun syms (name,data) ->
          Map.add_exn syms ~key:name ~data) in
  let prog = create_program syms in
  let expected =
    List.fold expected
      ~init:(Map.empty (module Tid))
      ~f:(fun tids (stub, impl) ->
          Map.add_exn tids
            ~key:(tid_for_name_exn prog stub)
            ~data:(tid_for_name_exn prog impl)) in
  let pairs = Stub_resolver.(links@@run prog) in
  let equal = Map.equal Tid.equal in
  let equal = if should_fail then fun x y -> not (equal x y) else equal in
  let msg = "the mappings shall " ^
            if should_fail then "differ" else "be the same" in
  OUnit.skip_if skip "To be fixed";
  assert_equal expected pairs
    ~cmp:equal
    ~msg
    ~printer:string_of_tids

let real name aliases = name, {is_stub = false; aliases}
let stub name aliases = name, {is_stub = true; aliases}

let test name ?skip ?(should_fail=false) ~expected symbols  =
  name >:: run ?skip name symbols expected should_fail

let suite = "stub-resolver" >::: [

    test "simple case: we have pairs" [
      real "a0"  [];
      stub "a1" ["a0"];
    ] ~expected:["a1", "a0"];

    test "simple case: mapping should be from stub to impl" [
      real "a0"  [];
      stub "a1" ["a0"];
    ] ~expected:["a0", "a1"] ~should_fail:true;

    test "simple case: no pairs" [
      real "b0" [];
      stub "b1" [];
    ] ~expected:[];

    test "simple case: still no pairs" [
      real "c0" [];
      stub "c1" ["c2"];
    ] ~expected:[];

    test "stubs only" [
      stub "d0" [];
      stub "d1" ["d0"];
    ] ~expected:[];

    test "impl only" [
      real "e0" [];
      real "e1" ["e0"];
    ] ~expected:[];

    test "impl can be aliased as well" [
      real "f0" ["f1"];
      stub "f1" [];
    ] ~expected:["f1", "f0"];

    test "many aliases" [
      real "g0" ["g1"; "g2"];
      stub "g1" [];
    ] ~expected:["g1", "g0"];

    test "ambiguous impl" [
      real "h0" ["h1"; "h2"];
      stub "h1" [];
      stub "h2" [];
    ] ~expected:[
      "h1", "h0";
      "h2", "h0";
    ];

    test "ambiguous stubs" [
      real "i0" [];
      stub "i1" ["i0"];
      stub "i2" ["i0"];
    ] ~expected:[
      "i1", "i0";
      "i2", "i0";
    ];

    test "crossreference" [
      real "j0" ["j1"];
      stub "j1" ["j0"];
    ] ~expected:["j1", "j0"];

    test "many pairs" [
      real "k0" [];
      real "k1" [];
      real "k2" [];
      stub "k3" ["k0"];
      stub "k4" ["k1"];
      stub "k5" ["k2"];
    ] ~expected:[
      "k3", "k0";
      "k4", "k1";
      "k5", "k2";
    ];

    test "several intersections 1" [
      stub "m0" ["m2"; "m3"; "m4"];
      real "m1" ["m0"];
      stub "m5" ["m6"; "m7"; "m8"];
      real "m6" ["m5"; "m9"];
      real "m9" ["m10"];
      stub "m10" [];
    ] ~expected:[
      "m0", "m1";
    ];

    test "several intersections 2" [
      stub "n0" ["n1"; "n2"; "n3"];
      real "n1" [];
      real "n4" ["n5"];
      stub "n5" [];
      real "n6" [];
      stub "n7" ["n6"];
      real "n8" ["n1"; "n5"]
    ] ~expected:["n7", "n6"];

    test "several intersections 3" [
      stub "p0" ["p1"; "p2"; "p3"];
      stub "p4" ["p5"; "p6"; "p7"];
      real "p5" [];
      stub "p6" ["p8"; "p9"; "p10"; "p4"];
      real "p11" ["p12"; "p13"; "p1"];
    ] ~expected:[
      "p0", "p11";
      "p4", "p5";
      "p6", "p5";
    ];
  ]
