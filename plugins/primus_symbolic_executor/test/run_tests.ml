(* The formulas of the division operators have to agree with the concrete
   semantics, that is Bitvec, on each sign and on a zero divisor, both when the
   operands are literals, which Z3 folds, and when they are symbolic. *)

open Core
open OUnit2
open Bap.Std
module SMT = Bap_primus_symbolic.SMT

let width = 8
let m8 = Bitvec.modulus width
let values = [ 0; 1; 2; 3; 7; 127; 128; 129; 249; 253; 254; 255 ]
let word x = Word.of_int ~width x

let concrete : Bil.binop -> _ = function
  | Bil.DIVIDE -> fun x y -> Bitvec.(div x y mod m8)
  | Bil.SDIVIDE -> fun x y -> Bitvec.(sdiv x y mod m8)
  | Bil.MOD -> fun x y -> Bitvec.(rem x y mod m8)
  | Bil.SMOD -> fun x y -> Bitvec.(smod x y mod m8)
  | _ -> assert false

let holds formulas = Option.is_some (SMT.check ~timeout:5000 formulas)
let equal x y = SMT.formula (SMT.binop Bil.EQ x y)

let expected op x y =
  let bits x = Word.to_bitvec (word x) in
  SMT.word (Word.create (concrete op (bits x) (bits y)) width)

let agrees_on_literals op _ =
  List.iter values ~f:(fun x ->
      List.iter values ~f:(fun y ->
          let result = SMT.binop op (SMT.word (word x)) (SMT.word (word y)) in
          assert_bool
            (sprintf "%s %d %d" (Sexp.to_string (Bil.sexp_of_binop op)) x y)
            (holds [ equal result (expected op x y) ])))

let agrees_on_variables op _ =
  let a = SMT.var "a" width and b = SMT.var "b" width in
  let result = SMT.binop op a b in
  List.iter values ~f:(fun x ->
      List.iter values ~f:(fun y ->
          let inputs =
            [ equal a (SMT.word (word x)); equal b (SMT.word (word y)) ]
          in
          let message = Sexp.to_string (Bil.sexp_of_binop op) in
          assert_bool
            (sprintf "%s %d %d" message x y)
            (holds (equal result (expected op x y) :: inputs));
          assert_bool
            (sprintf "%s %d %d has another result" message x y)
            (not
               (holds
                  (SMT.formula (SMT.binop Bil.NEQ result (expected op x y))
                  :: inputs)))))

let ops =
  [
    ("divide", Bil.DIVIDE);
    ("sdivide", Bil.SDIVIDE);
    ("mod", Bil.MOD);
    ("smod", Bil.SMOD);
  ]

let () =
  run_test_tt_main
    ("Symbolic_division"
    >::: List.concat_map ops ~f:(fun (name, op) ->
        [
          name ^ " literals" >:: agrees_on_literals op;
          name ^ " variables" >:: agrees_on_variables op;
        ]))
