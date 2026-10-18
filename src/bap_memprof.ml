(* samples the allocations with Gc.Memprof, when BAP_MEMPROF is the sampling
   rate, and prints at exit the code that allocated the sampled blocks that
   are still live, as the estimated live megabytes of each call site *)

open Stdlib

type sample = { words : float; callstack : Printexc.raw_backtrace }

(* the frame of a call site, a function and its location *)
let frame slot =
  match Printexc.Slot.location slot with
  | None -> None
  | Some { Printexc.filename; line_number; _ } ->
      let name = Option.value (Printexc.Slot.name slot) ~default:"?" in
      Some (Printf.sprintf "%s (%s:%d)" name filename line_number)

(* the first [depth] frames of [callstack], without the frames of the
   libraries if [skip] *)
let site ?(skip = false) depth callstack =
  let library frame =
    List.exists
      (fun prefix -> String.starts_with ~prefix frame)
      [ "Base"; "Core"; "Stdlib"; "Camlinternal" ]
  in
  match Printexc.backtrace_slots callstack with
  | None -> "<no callstack>"
  | Some slots ->
      Array.to_list slots |> List.filter_map frame
      |> List.filter (fun frame -> not (skip && library frame))
      |> List.filteri (fun i _ -> i < depth)
      |> String.concat "\n    "

let report live =
  let by_site ?skip depth =
    let sites = Hashtbl.create 64 in
    Hashtbl.iter
      (fun _ { words; callstack } ->
        let site = site ?skip depth callstack in
        let prev = Option.value (Hashtbl.find_opt sites site) ~default:0. in
        Hashtbl.replace sites site (prev +. words))
      live;
    Hashtbl.fold (fun site words acc -> (words, site) :: acc) sites []
    |> List.sort (fun (x, _) (y, _) -> Float.compare y x)
  in
  let mb words = words *. float (Sys.word_size / 8) /. 1048576. in
  let total = Hashtbl.fold (fun _ { words; _ } acc -> acc +. words) live 0. in
  Printf.eprintf "memprof: %.0f MB of the sampled blocks are live\n" (mb total);
  List.iter
    (fun depth ->
      Printf.eprintf "\nmemprof: the live megabytes by the %d first frames:\n"
        depth;
      by_site depth
      |> List.filteri (fun i _ -> i < 25)
      |> List.iter (fun (words, site) ->
          Printf.eprintf "%8.1f  %s\n" (mb words) site))
    [ 1; 6 ];
  Printf.eprintf
    "\n\
     memprof: the live megabytes by the 4 first frames out of the libraries:\n";
  by_site ~skip:true 4
  |> List.filteri (fun i _ -> i < 30)
  |> List.iter (fun (words, site) ->
      Printf.eprintf "%8.1f  %s\n" (mb words) site);
  flush stderr

let start () =
  match Sys.getenv_opt "BAP_MEMPROF" with
  | None -> ()
  | Some rate ->
      let rate = float_of_string rate in
      let live = Hashtbl.create 4096 in
      let next = ref 0 in
      let track (info : Gc.Memprof.allocation) =
        incr next;
        Hashtbl.replace live !next
          { words = float info.n_samples /. rate; callstack = info.callstack };
        Some !next
      in
      let release id = Hashtbl.remove live id in
      let _ : Gc.Memprof.t =
        Gc.Memprof.start ~sampling_rate:rate ~callstack_size:64
          {
            alloc_minor = track;
            alloc_major = track;
            promote = Option.some;
            dealloc_minor = release;
            dealloc_major = release;
          }
      in
      at_exit (fun () ->
          Gc.Memprof.stop ();
          report live)
