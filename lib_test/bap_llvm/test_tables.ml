open Core
open OUnit2
module Tables = Bap_llvm_tables

(* encodes tables the way the native loader does, see
   llvm_loader_utils.hpp *)
type value = I of int64 | B of bool | S of string

let encode ?(magic = "BAPT") ?(version = 1) ?(trailing = "") tables =
  let b = Buffer.create 64 and pool = Buffer.create 64 in
  let u32 x =
    for i = 0 to 3 do
      Buffer.add_char b (Char.of_int_exn ((x lsr (8 * i)) land 0xff))
    done
  in
  let u64 x =
    for i = 0 to 7 do
      Buffer.add_char b
        (Char.of_int_exn
           Int64.(to_int_exn (shift_right_logical x Int.(8 * i) land 0xffL)))
    done
  in
  Buffer.add_string b magic;
  u32 version;
  u32 (List.length tables);
  List.iter tables ~f:(fun (name, types, rows) ->
      u32 (String.length name);
      Buffer.add_string b name;
      u32 (List.length types);
      List.iter types ~f:(fun t ->
          Buffer.add_char b
            (Char.of_int_exn
               (match t with Tables.Int -> 0 | Bool -> 1 | Str -> 2)));
      u32 (List.length rows);
      let row = Buffer.create 64 in
      let saved = Buffer.contents b in
      Buffer.clear b;
      List.iter rows ~f:(fun values ->
          List.iter values ~f:(function
            | I x -> u64 x
            | B x -> Buffer.add_char b (if x then '\001' else '\000')
            | S s ->
                u32 (Buffer.length pool);
                u32 (String.length s);
                Buffer.add_string pool s));
      Buffer.add_buffer row b;
      Buffer.clear b;
      Buffer.add_string b saved;
      u64 (Int64.of_int (Buffer.length row));
      Buffer.add_buffer b row);
  u64 (Int64.of_int (Buffer.length pool));
  Buffer.add_buffer b pool;
  Buffer.add_string b trailing;
  Bigstring.of_string (Buffer.contents b)

let sections =
  ( "llvm:section-entry",
    Tables.[ Str; Int; Bool ],
    [
      [ S ".text"; I 0x1000L; B true ];
      [ S ".data"; I (-1L); B false ];
      [ S ".text"; I 0x1000L; B true ];
      [ S ""; I 0L; B false ];
    ] )

let decode data = ok_exn (Tables.of_bigstring data)

let fields ctxt =
  let doc = decode (encode [ sections ]) in
  let t =
    ok_exn (Tables.table doc "llvm:section-entry" Tables.[ Str; Int; Bool ])
  in
  assert_equal ~ctxt ~printer:Int.to_string 4 (Tables.length t);
  assert_equal ~ctxt ".data" (Tables.str t 1 0);
  assert_equal ~ctxt ~printer:Int64.to_string (-1L) (Tables.int t 1 1);
  assert_equal ~ctxt false (Tables.bool t 1 2);
  assert_equal ~ctxt "" (Tables.str t 3 0);
  assert_equal ~ctxt [ "llvm:section-entry" ] (Tables.names doc)

(* the distinct rows, the last added first, as Ogre enumerated them *)
let facts ctxt =
  let doc = decode (encode [ sections ]) in
  let t =
    ok_exn (Tables.table doc "llvm:section-entry" Tables.[ Str; Int; Bool ])
  in
  assert_equal ~ctxt
    ~printer:(fun xs -> String.concat ~sep:" " (List.map xs ~f:Int.to_string))
    [ 3; 1; 0 ] (Tables.facts t)

(* the strings are compared by their contents, not by their places *)
let facts_of_strings ctxt =
  let doc =
    decode
      (encode
         [
           ( "t",
             Tables.[ Str; Str ],
             [ [ S "ab"; S "c" ]; [ S "a"; S "bc" ]; [ S "ab"; S "c" ] ] );
         ])
  in
  let t = ok_exn (Tables.table doc "t" Tables.[ Str; Str ]) in
  assert_equal ~ctxt [ 1; 0 ] (Tables.facts t)

let missing ctxt =
  let doc = decode (encode []) in
  let t = ok_exn (Tables.table doc "llvm:code-entry" Tables.[ Str ]) in
  assert_equal ~ctxt 0 (Tables.length t);
  assert_equal ~ctxt [] (Tables.facts t)

let wrong_fields _ =
  let doc = decode (encode [ sections ]) in
  match Tables.table doc "llvm:section-entry" Tables.[ Str; Int ] with
  | Ok _ -> assert_failure "a table with different fields is accepted"
  | Error _ -> ()

let malformed ~msg data _ =
  match Tables.of_bigstring data with
  | Ok _ -> assert_failure (msg ^ ": a malformed document is accepted")
  | Error _ -> ()

let truncated =
  let data = encode [ sections ] in
  Bigstring.sub data ~pos:0 ~len:(Bigstring.length data - 3)

(* a string of the first row that points past the end of the pool *)
let out_of_pool =
  let data = encode [ ("t", Tables.[ Str ], [ [ S "abc" ] ]) ] in
  (* the row starts after the header: magic, version, count, the name, the
     field count, the type, the row count, and the size *)
  let row = 4 + 4 + 4 + 4 + 1 + 4 + 1 + 4 + 8 in
  Bigstring.set_uint32_le_exn data ~pos:row 1;
  data

let suite =
  "Tables"
  >::: [
         "fields" >:: fields;
         "facts" >:: facts;
         "facts of strings" >:: facts_of_strings;
         "missing table" >:: missing;
         "wrong fields" >:: wrong_fields;
         "bad magic" >:: malformed ~msg:"magic" (encode ~magic:"OGRE" []);
         "bad version" >:: malformed ~msg:"version" (encode ~version:2 []);
         "trailing bytes"
         >:: malformed ~msg:"trailing" (encode ~trailing:"x" []);
         "truncated" >:: malformed ~msg:"truncated" truncated;
         "string out of the pool" >:: malformed ~msg:"pool" out_of_pool;
         "duplicate table"
         >:: malformed ~msg:"duplicate" (encode [ sections; sections ]);
       ]

let () = run_test_tt_main suite
