open Core
open OUnit2

(* the joins are evaluated with hash lookups, the same constraints in
   the where clause are checked on the whole cross product, so the
   results of both must be the same, in the same order *)

let id = Ogre.Type.("id" %: int)
let key = Ogre.Type.("key" %: int)
let x = Ogre.Type.("x" %: int)
let y = Ogre.Type.("y" %: int)
let z = Ogre.Type.("z" %: str)

let a () =
  Ogre.declare ~name:"a"
    Ogre.Type.(scheme id $ key $ x)
    (fun id key x -> (id, key, x))

let b () =
  Ogre.declare ~name:"b"
    Ogre.Type.(scheme id $ key $ y)
    (fun id key y -> (id, key, y))

let c () =
  Ogre.declare ~name:"c"
    Ogre.Type.(scheme id $ y $ z)
    (fun id y z -> (id, y, z))

let doc ~seed ~n =
  let state = Random.State.make [| seed |] in
  let small () = Int64.of_int (Random.State.int state 4) in
  let facts attr make = List.init n ~f:(fun i -> make (Int64.of_int i) attr) in
  Ogre.sequence
    (facts a (fun i a -> Ogre.provide a i (small ()) (small ()))
    @ facts b (fun i b -> Ogre.provide b i (small ()) (small ()))
    @ facts c (fun i c ->
        Ogre.provide c i (small ()) (Int64.to_string (small ()))))
  |> Fn.flip Ogre.exec Ogre.Doc.empty
  |> ok_exn

let rows query doc = ok_exn (Ogre.eval query doc) |> Sequence.to_list
let ab (i, _, _) (j, _, _) = (i, j)
let abc (i, _, _) (j, _, _) (k, _, _) = (i, j, k)

let check ~msg ~printer ~ctxt joined filtered =
  for seed = 0 to 9 do
    let doc = doc ~seed ~n:12 in
    let expect = rows filtered doc in
    assert_bool (msg ^ ": the query is not trivial") (List.length expect > 0);
    assert_equal ~ctxt ~msg ~printer expect (rows joined doc)
  done

let print2 xs =
  List.map xs ~f:(fun (i, j) -> sprintf "%Ld,%Ld" i j) |> String.concat ~sep:" "

let print3 xs =
  List.map xs ~f:(fun (i, j, k) -> sprintf "%Ld,%Ld,%Ld" i j k)
  |> String.concat ~sep:" "

let unqualified ctxt =
  let open Ogre.Query in
  check ~ctxt ~msg:"unqualified" ~printer:print2
    (Ogre.foreach (select ~join:[ [ field key ] ] (from a $ b)) ~f:ab)
    (Ogre.foreach (select ~where:(a.(key) = b.(key)) (from a $ b)) ~f:ab)

(* the shape of the query of the segments in Image *)
let qualified ctxt =
  let open Ogre.Query in
  check ~ctxt ~msg:"qualified" ~printer:print3
    (Ogre.foreach
       (select
          ~join:[ [ field key ]; [ field y ~from:b; field y ~from:c ] ]
          (from a $ b $ c))
       ~f:abc)
    (Ogre.foreach
       (select ~where:(a.(key) = b.(key) && b.(y) = c.(y)) (from a $ b $ c))
       ~f:abc)

let join_and_where ctxt =
  let open Ogre.Query in
  check ~ctxt ~msg:"join and where" ~printer:print3
    (Ogre.foreach
       (select
          ~where:(a.(x) < int 2L)
          ~join:[ [ field y ~from:b; field y ~from:c ] ]
          (from a $ b $ c))
       ~f:abc)
    (Ogre.foreach
       (select ~where:(a.(x) < int 2L && b.(y) = c.(y)) (from a $ b $ c))
       ~f:abc)

(* the joined attribute is not the last one *)
let backward ctxt =
  let open Ogre.Query in
  check ~ctxt ~msg:"backward" ~printer:print3
    (Ogre.foreach
       (select ~join:[ [ field y ~from:c; field y ~from:b ] ] (from c $ a $ b))
       ~f:abc)
    (Ogre.foreach (select ~where:(c.(y) = b.(y)) (from c $ a $ b)) ~f:abc)

let suite =
  "Ogre joins"
  >::: [
         "unqualified" >:: unqualified;
         "qualified" >:: qualified;
         "join and where" >:: join_and_where;
         "backward" >:: backward;
       ]

let () = run_test_tt_main suite
