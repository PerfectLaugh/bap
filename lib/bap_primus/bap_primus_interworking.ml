(* The interworking of ARM, which switches between its encodings, A32
   and Thumb, by the jumps, as the ARMv7 architecture does it: the
   branches with the immediate targets, e.g., [b label], stay in the
   mode, except [blx label], which switches it, the other writes to the
   program counter, e.g., [bx r3], [pop {pc}] or, in A32, [mov pc, r3],
   enter Thumb, if the lower bit of the target is set, and A32 otherwise,
   while [mov pc, r3] and [add pc, r3] of Thumb stay in Thumb.

   The IR of the instructions, that the lifters of BAP compute, clears
   the lower bit of the targets of some jumps, e.g., [bx r3], which
   [unmask] keeps, so that the jump tells the mode. *)

open Core
open Bap_core_theory
open Bap.Std

let language name =
  lazy
    (match Theory.Language.read ~package:"bap" name with
    | language -> Some language
    | exception _ -> None)

let thumb_language = language "llvm-thumb"
let a32_language = language "llvm-armv7"
let thumb () = Lazy.force thumb_language
let a32 () = Lazy.force a32_language
let encoding ~thumb:t = if t then thumb () else a32 ()

let is_thumb language =
  match thumb () with
  | Some thumb -> Theory.Language.equal thumb language
  | None -> false

(* the mask, that clears the lower bit *)
let is_mask m =
  let width = Word.bitwidth m in
  Word.equal m (Word.lnot (Word.one width))

let unmask_exp : exp -> exp = function
  | BinOp (AND, x, Int m) when is_mask m -> x
  | BinOp (AND, Int m, x) when is_mask m -> x
  | x -> x

let unmask_label : label -> label = function
  | Indirect x -> Indirect (unmask_exp x)
  | Direct _ as l -> l

let unmask blks =
  List.map blks ~f:(fun blk ->
      Term.map jmp_t blk ~f:(fun jmp ->
          match Jmp.kind jmp with
          | Goto l -> Jmp.with_kind jmp (Goto (unmask_label l))
          | Ret l -> Jmp.with_kind jmp (Ret (unmask_label l))
          | Call c ->
              Jmp.with_kind jmp
                (Call (Call.with_target c (unmask_label (Call.target c))))
          | Int _ -> jmp))

(* the jumps of the instruction have the immediate targets *)
let is_immediate blks =
  List.for_all blks ~f:(fun blk ->
      Term.enum jmp_t blk
      |> Seq.for_all ~f:(fun jmp ->
          let immediate : label -> bool = function
            | Direct _ | Indirect (Int _) -> true
            | Indirect _ -> false
          in
          match Jmp.kind jmp with
          | Goto l | Ret l -> immediate l
          | Call c -> immediate (Call.target c)
          | Int _ -> true))

(* the writes of the program counter of Thumb, that interwork, i.e.,
   the branches and the loads, but not the arithmetic, e.g., [mov pc, r3] *)
let interworks ~thumb name =
  (not thumb)
  || List.exists [ "BX"; "BLX"; "POP"; "LD" ] ~f:(fun part ->
      String.is_substring name ~substring:part)

let jump ~name ~thumb ~next blks dst =
  let width = Word.bitwidth dst in
  let odd = Word.(is_one (extract_exn ~hi:0 dst)) in
  let dst = Word.(dst land lnot (one width)) in
  if Word.equal dst next then (dst, thumb)
  else
    match name with
    | "BLXi" -> (dst, true)
    | "tBLXi" -> (dst, false)
    | _ when odd -> (dst, true)
    | _ when is_immediate blks -> (dst, thumb)
    | _ when interworks ~thumb name -> (dst, false)
    | _ -> (dst, thumb)
