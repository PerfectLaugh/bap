#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

let check condition message = if not condition then failwith message

let sym emu name =
  match List.Assoc.find (Emu.symbols emu) ~equal:String.equal name with
  | Some address -> address
  | None -> failwithf "symbol %s not found" name ()

let site_table emu =
  let base = sym emu "control_sites" in
  List.init 11 ~f:(fun i ->
      String.foldi
        (Emu.read emu Int64.(base + (of_int i * 8L)) 8)
        ~init:0L ~f:(fun i acc c ->
          let shift = 8 * i in
          Int64.(acc lor shift_left (of_int (Char.to_int c)) shift)))
  |> Array.of_list

let has_site (steps : Emu.step list) site =
  List.exists steps ~f:(fun s -> Int64.equal s.Emu.pc site)

let has_reason (unresolved : Emu.control_unresolved list) reason =
  List.exists unresolved ~f:(fun u -> Poly.equal u.Emu.reason reason)

let slice_call emu blocks ?(accesses = 128) ?every ?window name args =
  let accesses = if Option.is_some every then 0 else accesses in
  let trace =
    Emu.Trace.start ~blocks ~accesses ?every
      ~code_versions:(if blocks then 0 else 4096) emu
  in
  (match Emu.call emu (sym emu name) ~args with
  | Some _ -> ()
  | None ->
      let status =
        match Emu.status emu with
        | Paused -> sprintf "paused %Lx" (Emu.pc emu)
        | Running -> "running"
        | Exited code -> sprintf "exited %s" (Option.value_map code ~default:"?" ~f:Int.to_string)
        | Failed message -> "failed " ^ message
      in
      failwithf "%s didn't return, %s" name status ());
  Emu.Trace.stop trace;
  let criterion = [ Emu.Mem (sym emu "control_result", 8) ] in
  let plain = Emu.slice ~executed_bytes:true ?window trace criterion in
  let controlled =
    Emu.slice ~control:true ~executed_bytes:true ?window trace criterion
  in
  check (Option.is_none plain.control) "control result present by default";
  check
    (Poly.equal plain.steps controlled.steps
    && Poly.equal plain.live controlled.live
    && Poly.equal plain.gaps controlled.gaps
    && Bool.equal plain.complete controlled.complete
    && Poly.equal plain.reason controlled.reason
    && Poly.equal plain.decode_failures controlled.decode_failures)
    "control option changed data-only results";
  controlled

let control_exn (s : Emu.slice) = Option.value_exn s.control

let select emu blocks flag =
  let sites = site_table emu in
  let s = slice_call emu blocks "c_select" [ flag ] in
  let c = control_exn s in
  let selected, unselected, taken, target =
    if Int64.equal flag 0L then (sites.(5), sites.(4), true, sites.(5))
    else (sites.(4), sites.(5), false, sites.(4))
  in
  if not (has_site s.steps selected) then begin
    printf "wanted %Lx, sites %Lx %Lx %Lx %Lx %Lx %Lx\n" selected sites.(0)
      sites.(1) sites.(2) sites.(3) sites.(4) sites.(5);
    List.iter s.steps ~f:(fun s -> printf "data %Lx:%Ld\n" s.pc s.index);
    List.iter c.steps ~f:(fun s -> printf "control %Lx:%Ld\n" s.pc s.index);
    List.iter c.dependencies ~f:(fun d -> printf "guard %Lx -> %Lx\n" d.site d.target);
    List.iter c.unresolved ~f:(fun u -> printf "unresolved %Lx\n" u.pc)
  end;
  check (has_site s.steps selected) "selected producer missing";
  check (not (has_site s.steps unselected)) "unselected data producer selected";
  check (not (has_site c.steps unselected)) "unselected control producer selected";
  List.iter [ sites.(0); sites.(1); sites.(2) ] ~f:(fun site ->
      check (has_site c.steps site) (sprintf "predicate producer %Lx missing" site));
  check (not (has_site c.steps sites.(3))) "branch included as a data producer";
  (match c.dependencies with
  | [ d ] ->
      check Int64.(d.index >= 0L) "negative branch index";
      check Int64.(d.site = sites.(3)) "wrong branch site";
      check Int64.(d.target = target) "wrong actual branch target";
      check (Bool.equal d.taken taken) "wrong branch outcome";
      check (d.thread = Emu.thread emu) "wrong effective TID"
  | _ -> failwith "expected exactly one selected guard");
  check (List.exists c.live ~f:(function Emu.Reg "RDI" -> true | _ -> false))
    "flag input isn't control-live";
  check (List.is_empty s.gaps && not (List.is_empty c.gaps))
    "control gap isn't independent";
  check (has_reason c.unresolved Emu.Outside_writes) "control gap isn't explicit";
  check (has_reason c.unresolved Emu.Missing_producer)
    "missing flag producer isn't explicit";
  check (not c.complete) "incomplete predicate input claimed complete"

let post_join emu blocks =
  let c = control_exn (slice_call emu blocks "c_post" [ 0L ]) in
  check (List.is_empty c.dependencies) "post-join branch overclaimed";
  check (List.is_empty c.steps) "post-join control producers invented";
  check c.complete "post-join control result incomplete"

let conditional emu blocks =
  let c = control_exn (slice_call emu blocks "c_conditional" [ 1L; 2L; 3L; 4L ]) in
  check (List.is_empty c.dependencies) "conditional definition became a branch";
  check (List.is_empty c.unresolved) "conditional definition left unresolved control";
  check c.complete "conditional definition control result incomplete"

let loops emu blocks =
  let sites = site_table emu in
  let c = control_exn (slice_call emu blocks "c_loop" []) in
  match c.dependencies with
  | [ first; second ] ->
      check Int64.(first.site = sites.(7) && second.site = sites.(7))
        "wrong loop branch occurrences";
      check Int64.(first.index < second.index) "loop occurrences not distinct and ordered";
      check (first.taken && second.taken) "loop outcomes wrong"
  | _ -> failwith "expected two earlier loop guards"

let nested emu blocks flag =
  let sites = site_table emu in
  let c = control_exn (slice_call emu blocks "c_outer" [ flag; 1L ]) in
  match c.dependencies with
  | [ outer; inner ] ->
      check Int64.(outer.site = sites.(8) && inner.site = sites.(3))
        "nested guards not retained";
      check Int64.(outer.index < inner.index) "nested guards out of order";
      check (not outer.taken) "conditional call outcome wrong";
      check (Bool.equal inner.taken (Int64.(flag = 0L))) "nested selected path wrong"
  | _ -> failwith "expected caller and callee guards"

let incomplete_window emu blocks =
  let c = control_exn (slice_call emu blocks ~window:1 "c_select" [ 0L ]) in
  check (has_reason c.unresolved Emu.Window_scope) "mid-scope window not explicit";
  check (not c.complete) "mid-scope window claimed complete"

let evicted_predicate emu blocks =
  let c = control_exn (slice_call emu blocks ~accesses:2 "c_select" [ 0L ]) in
  check (has_reason c.unresolved Emu.Access_history) "access eviction not explicit";
  check (not c.complete) "evicted predicate producer claimed complete"

let sampled emu =
  let c = control_exn (slice_call emu false ~every:2 "c_select" [ 0L ]) in
  check (has_reason c.unresolved Emu.Unknown_outcome) "sampled outcome not explicit";
  check (not c.complete) "sampled trace claimed complete"

let run blocks =
  let prog = List.hd_exn (Bap_script.args ()) in
  let emu = Emu.create (Bap_script.project prog) in
  List.iter [ 0L; 1L ] ~f:(select emu blocks);
  post_join emu blocks;
  conditional emu blocks;
  loops emu blocks;
  List.iter [ 0L; 1L ] ~f:(nested emu blocks);
  incomplete_window emu blocks;
  evicted_predicate emu blocks;
  if not blocks then sampled emu;
  let engine = Option.value (Sys.getenv "BAP_EMU_ENGINE") ~default:"lifted" in
  printf "%s blocks %b: control slice ok\n%!" engine blocks

let () =
  if List.length (Bap_script.args ()) <> 1 then failwith "expected CONTROL-SLICE";
  run false;
  run true
