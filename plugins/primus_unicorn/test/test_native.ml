(* Checks the native functions of libc on a memory of three pages: the
   first is readable, the second is not copied to Unicorn, and the
   third has a hole from 0x3800, on which Primus faults. *)

open Core
module Native = Bap_primus_unicorn_plugin.Primus_unicorn_native

let base = 0x1000L
let data = Bytes.make 0x3000 '\000'
let hole = 0x3800L
let missing = 0x2000L

let set addr s =
  Bytes.From_string.blit ~src:s ~src_pos:0 ~dst:data
    ~dst_pos:Int64.(to_int_exn (addr - base))
    ~len:(String.length s)

let readable addr n =
  let rec count addr n acc =
    if n = 0 then acc
    else if Int64.(addr >= missing && addr < missing + 0x1000L) then
      raise (Native.Missing addr)
    else if Int64.(addr < base || addr >= hole) then acc
    else count Int64.(addr + 1L) (n - 1) (acc + 1)
  in
  count addr n 0

let get addr n =
  Bytes.To_string.sub data ~pos:Int64.(to_int_exn (addr - base)) ~len:n

let memory : Native.memory =
  {
    read =
      (fun addr n ->
        if readable addr n < n then raise Native.Denied else get addr n);
    prefix = (fun addr n -> get addr (readable addr n));
  }

let call name args =
  match Native.find name with
  | Some fn -> fn memory args
  | None -> failwithf "%s is not native" name ()

let value name args expected =
  let r = call name args in
  if Int64.(r.value <> expected) then
    failwithf "%s: expected %Ld, got %Ld" name expected r.value ()

let writes name args expected =
  let r = call name args in
  if not ([%equal: (int64 * string) list] r.writes expected) then
    failwithf "%s: wrong writes" name ()

let fails name args =
  match call name args with
  | exception Native.Denied -> ()
  | _ -> failwithf "%s: expected to fail" name ()

let () =
  set 0x1000L "hello\000world\000\x80\000";
  value "strlen" [ 0x1000L ] 5L;
  value "strcmp" [ 0x1000L; 0x1006L ] (-1L);
  value "strcmp" [ 0x1006L; 0x1000L ] 1L;
  (* the bytes are unsigned *)
  value "strcmp" [ 0x100cL; 0x1000L ] 1L;
  value "memcmp" [ 0x1000L; 0x100cL; 1L ] (-1L);
  value "strncmp" [ 0x1000L; 0x1006L; 0L ] 0L;
  value "strchr" [ 0x1000L; Int64.of_int (Char.to_int 'l') ] 0x1002L;
  value "strchr" [ 0x1000L; 0L ] 0x1005L;
  value "strchr" [ 0x1000L; Int64.of_int (Char.to_int 'z') ] 0L;
  value "memchr" [ 0x1000L; Int64.of_int (Char.to_int 'o'); 4L ] 0L;
  writes "memset" [ 0x1100L; 0x161L; 3L ] [ (0x1100L, "aaa") ];
  writes "strcpy" [ 0x1100L; 0x1000L ] [ (0x1100L, "hello\000") ];
  set 0x1200L "ab\000";
  writes "strcat" [ 0x1200L; 0x1006L ] [ (0x1202L, "world\000") ];
  (* the overlapping strings are left to Lisp *)
  fails "strcat" [ 0x1000L; 0x1006L ];
  (* the destination inside the source repeats the bytes before it, as
     the Lisp stub copies them one by one, but memmove doesn't *)
  writes "memcpy" [ 0x1002L; 0x1000L; 4L ] [ (0x1002L, "hehe") ];
  writes "memmove" [ 0x1002L; 0x1000L; 4L ] [ (0x1002L, "hell") ];
  fails "strcpy" [ 0x1001L; 0x1000L ];
  (* the string, which ends before the hole, is read, the one that
     doesn't is left to Lisp, which faults *)
  set 0x3700L (String.make 0xFF 'x');
  value "strlen" [ 0x3700L ] 0xFFL;
  set 0x3700L (String.make 0x100 'x');
  fails "strlen" [ 0x3700L ];
  fails "memset" [ 0x1000L; 0L; -1L ];
  (* the page, which is not copied, is asked for *)
  match call "memcmp" [ 0x1000L; 0x1ff0L; 0x20L ] with
  | exception Native.Missing addr when Int64.(addr = missing) -> ()
  | _ -> failwith "memcmp: the missing page is not asked for"
