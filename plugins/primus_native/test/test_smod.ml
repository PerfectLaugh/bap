(* The signed modulus in the closures and in the JIT of the lifted engine, on a
   table of signed values, of several widths, with the zero divisor and the
   overflow of the minimum by -1, against Bitvec.smod, which is SMT-LIB bvsmod:
   the sign follows the divisor, and x smod 0 = x. *)

open Core
open Bap.Std
module Lifted = Bap_lifted.For_tests

let widths = [ 1; 2; 7; 8; 16; 31; 32; 63; 64; 65; 128 ]

let table w =
  let z = Z.of_int in
  let min = Z.neg (Z.shift_left Z.one (w - 1)) in
  let max = Z.pred (Z.shift_left Z.one (w - 1)) in
  [ z 0; z 1; z 2; z 3; z 5; z (-1); z (-2); z (-3); z (-5); min; max ]
  |> List.map ~f:(fun x -> Z.extract x 0 w)
  |> List.dedup_and_sort ~compare:Z.compare

let bitvec w x = Bitvec.(bigint x mod modulus w)
let word w x = Word.create (bitvec w x) w

let expected w x y =
  Z.extract
    (Bitvec.to_bigint Bitvec.(smod (bitvec w x) (bitvec w y) mod modulus w))
    0 w

let the_closures () =
  List.iter widths ~f:(fun w ->
      let table = table w in
      List.iter table ~f:(fun x ->
          List.iter table ~f:(fun y ->
              let r = Lifted.binop Bil.SMOD (word w x) (word w y) in
              let r = Bitvec.to_bigint (Word.to_bitvec r) in
              let e = expected w x y in
              if not (Z.equal r e) then
                failwithf "closures: %s smod %s:%d = %s, not %s" (Z.to_string x)
                  (Z.to_string y) w (Z.to_string r) (Z.to_string e) ())))

(* the literal of the bits, that LLVM reads signed *)
let literal w x =
  let x = Z.extract x 0 w in
  Z.to_string
    (if Z.testbit x (w - 1) then Z.sub x (Z.shift_left Z.one w) else x)

let main w rows =
  let b = Buffer.create 4096 in
  let i = sprintf "i%d" w in
  bprintf b
    "define i32 @main() {\nentry:\n  %%out = alloca %s\n  br label %%r0\n" i;
  List.iteri rows ~f:(fun k (x, y, e) ->
      bprintf b "r%d:\n" k;
      bprintf b "  %%ok%d = call i1 @binop(%s %s, %s %s, ptr %%out)\n" k i
        (literal w x) i (literal w y);
      bprintf b "  %%v%d = load %s, ptr %%out\n" k i;
      bprintf b "  %%c%d = icmp eq %s %%v%d, %s\n" k i k (literal w e);
      bprintf b "  %%a%d = and i1 %%ok%d, %%c%d\n" k k k;
      bprintf b "  br i1 %%a%d, label %%r%d, label %%bad%d\n" k (k + 1) k;
      bprintf b "bad%d:\n  ret i32 1\n" k);
  bprintf b "r%d:\n  ret i32 0\n}\n" (List.length rows);
  Buffer.contents b

let run_module name source =
  let path = Stdlib.Filename.temp_file "bap-smod" ".ll" in
  let optimized = path ^ ".opt.ll" in
  Out_channel.write_all path ~data:source;
  let status = Stdlib.Sys.command (sprintf "lli %s" path) in
  if status <> 0 then
    failwithf "%s: lli exited with %d\n%s" name status source ();
  (* an undefined division in the lowering would be folded here *)
  let status =
    Stdlib.Sys.command
      (sprintf "opt -S -O2 %s -o %s && lli %s" path optimized optimized)
  in
  if status <> 0 then
    failwithf "%s: optimized exited with %d\n%s" name status source ();
  Stdlib.Sys.remove path;
  Stdlib.Sys.remove optimized

let the_jit () =
  if
    Stdlib.Sys.command "command -v lli >/dev/null && command -v opt >/dev/null"
    <> 0
  then print_endline "skipped the JIT: no lli or opt"
  else
    List.iter widths ~f:(fun w ->
        let table = table w in
        let rows =
          List.concat_map table ~f:(fun x ->
              List.map table ~f:(fun y -> (x, y, expected w x y)))
        in
        run_module
          (sprintf "smod of %d bits" w)
          (Lifted.jit_binop Bil.SMOD w ^ main w rows))

(* the division still stops the instruction on a zero divisor, and in one bit
   its only divisor, -1, is not divided by, as LLVM's -1 by -1 overflows *)
let the_division () =
  if Stdlib.Sys.command "command -v lli >/dev/null" = 0 then begin
    let ir = Lifted.jit_binop Bil.SDIVIDE 1 in
    let source =
      ir
      ^ "define i32 @main() {\n\
         entry:\n\
        \  %out = alloca i1\n\
        \  %ok = call i1 @binop(i1 -1, i1 -1, ptr %out)\n\
        \  %v = load i1, ptr %out\n\
        \  %good = and i1 %ok, %v\n\
        \  %stops = call i1 @binop(i1 -1, i1 0, ptr %out)\n\
        \  %none = xor i1 %stops, true\n\
        \  %all = and i1 %good, %none\n\
        \  %r = select i1 %all, i32 0, i32 1\n\
        \  ret i32 %r\n\
         }\n"
    in
    run_module "sdiv of 1 bit" source
  end

let () =
  the_closures ();
  the_jit ();
  the_division ();
  print_endline "smod tests passed"
