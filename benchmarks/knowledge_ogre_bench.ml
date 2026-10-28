open Core

let objects = 2_000
let rows = 200
let queries = 10

let elapsed start =
  Int63.(Time_now.nanoseconds_since_unix_epoch () - start)
  |> Int63.to_int64 |> Float.of_int64
  |> fun x -> x /. 1e9

let ok = function
  | Ok value -> value
  | Error conflict ->
      failwith (Bap_knowledge.Knowledge.Conflict.to_string conflict)

let kb () =
  let start = Time_now.nanoseconds_since_unix_epoch () in
  let module KB = Bap_knowledge.Knowledge in
  let cls = KB.Class.declare "ocaml-bench-program" () in
  let int = KB.Domain.total ~empty:0L ~order:Int64.compare "int" in
  let base = KB.Class.property cls "ocaml-bench-base" int in
  let derived = KB.Class.property cls "ocaml-bench-derived" int in
  KB.promise derived (fun obj ->
      let open KB.Syntax in
      let+ value = KB.collect base obj in
      Int64.(value + 1L));
  let created = ref [] in
  let rec populate index =
    let open KB.Syntax in
    if index = 0 then KB.return (List.hd_exn !created)
    else
      let* obj = KB.Object.create cls in
      let* () = KB.provide base obj (Int64.of_int index) in
      created := obj :: !created;
      populate (index - 1)
  in
  let _, state = KB.run cls (populate objects) KB.empty |> ok in
  let state = ref state in
  Printf.printf "kb_setup,%.9f,%d\n%!" (elapsed start) objects;
  let start = Time_now.nanoseconds_since_unix_epoch () in
  let checksum = ref 0L in
  List.iter !created ~f:(fun obj ->
      let _, next =
        KB.run cls
          (let open KB.Syntax in
           let+ value = KB.collect derived obj in
           (checksum := Int64.(!checksum + value));
           obj)
          !state
        |> ok
      in
      state := next);
  let expected = Int64.of_int ((objects * (objects + 1) / 2) + objects) in
  if Int64.(!checksum <> expected) then failwith "KB checksum";
  Printf.printf "kb_infer,%.9f,%d,%Ld\n%!" (elapsed start) objects !checksum

let ogre () =
  let start = Time_now.nanoseconds_since_unix_epoch () in
  let id = Ogre.Type.("id" %: int) in
  let key = Ogre.Type.("key" %: int) in
  let x = Ogre.Type.("x" %: int) in
  let y = Ogre.Type.("y" %: int) in
  let cid = Ogre.Type.("cid" %: int) in
  let z = Ogre.Type.("z" %: int) in
  let a () =
    Ogre.declare ~name:"a"
      Ogre.Type.(scheme id $ key $ x)
      (fun id key x -> (id, key, x))
  in
  let b () =
    Ogre.declare ~name:"b"
      Ogre.Type.(scheme id $ key $ y)
      (fun id key y -> (id, key, y))
  in
  let c () =
    Ogre.declare ~name:"c"
      Ogre.Type.(scheme cid $ y $ z)
      (fun cid y z -> (cid, y, z))
  in
  let document = ref Ogre.Doc.empty in
  let random = ref 7L in
  let small () =
    (random := Int64.((!random * 6364136223846793005L) + 1L));
    Int64.(shift_right_logical !random 32 land 3L)
  in
  let provide operation =
    document := Ogre.exec operation !document |> Or_error.ok_exn
  in
  for index = 0 to rows - 1 do
    let i = Int64.of_int index in
    let key = small () in
    let x = small () in
    provide (Ogre.provide a i key x);
    let key = small () in
    let y = small () in
    provide (Ogre.provide b i key y);
    let y = small () in
    let z = small () in
    provide (Ogre.provide c i y z)
  done;
  Printf.printf "ogre_setup,%.9f,%d\n%!" (elapsed start) (rows * 3);
  let open Ogre.Query in
  let query =
    select
      ~join:[ [ field key ]; [ field y ~from:b; field y ~from:c ] ]
      ~where:(a.(x) < int 3L)
      (from a $ b $ c)
  in
  let start = Time_now.nanoseconds_since_unix_epoch () in
  let count = ref 0 in
  let checksum = ref 0L in
  for _ = 1 to queries do
    Ogre.eval (Ogre.foreach query ~f:(fun a b c -> (a, b, c))) !document
    |> Or_error.ok_exn
    |> Sequence.iter ~f:(fun ((ai, _, _), (bi, _, _), (ci, _, _)) ->
        incr count;
        checksum := Int64.(!checksum + ai + bi + ci))
  done;
  Printf.printf "ogre_query,%.9f,%d,%d,%Ld\n%!" (elapsed start) queries !count
    !checksum

let () =
  kb ();
  ogre ()
