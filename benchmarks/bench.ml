type t = Test of string * (unit -> unit) | Group of string * t list

let create ~name f = Test (name, fun () -> ignore (Sys.opaque_identity (f ())))

let create_indexed ~name ~args f =
  Group (name, List.map (fun n -> create ~name:(string_of_int n) (f n)) args)

let create_group ~name tests = Group (name, tests)

let rec flatten prefix = function
  | Test (name, f) -> [ (prefix ^ name, f) ]
  | Group (name, tests) -> List.concat_map (flatten (prefix ^ name ^ "/")) tests

let contains name part =
  let n = String.length name and m = String.length part in
  let rec at i = i + m <= n && (String.sub name i m = part || at (i + 1)) in
  at 0

(* the runs double, until they take the quota, so that the clock, whose
   resolution is coarse for one run, measures many *)
let measure clock quota f =
  f ();
  let rec loop runs total =
    let start = Eio.Time.Mono.now clock in
    for _ = 1 to runs do
      f ()
    done;
    let span = Mtime.span start (Eio.Time.Mono.now clock) in
    let total = Mtime.Span.add total span and count = runs in
    if Mtime.Span.compare total quota >= 0 then (count, span)
    else loop (runs * 2) total
  in
  let runs, span = loop 1 Mtime.Span.zero in
  (runs, Mtime.Span.to_float_ns span /. float runs)

let pp_time ns =
  if ns < 1e3 then Printf.sprintf "%.1f ns" ns
  else if ns < 1e6 then Printf.sprintf "%.2f us" (ns /. 1e3)
  else if ns < 1e9 then Printf.sprintf "%.2f ms" (ns /. 1e6)
  else Printf.sprintf "%.2f s" (ns /. 1e9)

let run ~clock ?(quota = Mtime.Span.(500 * ms)) ?(only = []) tests =
  let tests =
    List.concat_map (flatten "") tests
    |> List.filter (fun (name, _) ->
        only = [] || List.exists (contains name) only)
  in
  let width =
    List.fold_left (fun w (name, _) -> max w (String.length name)) 0 tests
  in
  Printf.printf "%-*s %12s %10s\n%!" width "name" "time/run" "runs";
  List.iter
    (fun (name, f) ->
      let runs, ns = measure clock quota f in
      Printf.printf "%-*s %12s %10d\n%!" width name (pp_time ns) runs)
    tests
