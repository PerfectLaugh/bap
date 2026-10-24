open Core
open Bap.Std
open Bap_primus_types
module Observation = Bap_primus_observation
module Value = Bap_primus_value

let page_size = 0x1000L

(* the values, whose identities the analyses track, e.g., the tainted
   or the symbolic ones, and the locations of the memory, which hold
   them, or which the analyses track themselves, e.g., the indirectly
   tainted ones, with the number of the marked bytes of their pages *)
type t = {
  values : Value.Id.Set.t;
  addrs : Addr.Set.t;
  pages : int Int64.Map.t;
  version : int;
  covered : int String.Map.t;
      (** the numbers of the observers of the observations, by their names, that
          need the events of the tracked values only, see [cover] *)
  code_covered : int String.Map.t;
      (** the numbers of the observers of the observations, by their names, that
          need the events of the code of the program only, see [cover_code] *)
  opaque : bool;  (** see [opaque] *)
}

let state =
  Bap_primus_machine.State.declare ~uuid:"6a0ab0e4-1f3e-4c56-9f0e-4f5b2a6c3d17"
    ~name:"tracked" (fun _ ->
      {
        values = Value.Id.Set.empty;
        addrs = Addr.Set.empty;
        pages = Int64.Map.empty;
        version = 0;
        covered = String.Map.empty;
        code_covered = String.Map.empty;
        opaque = false;
      })

let marked, on_marked =
  Observation.provide "location-marked" ~inspect:Bap_primus_sexp.sexp_of_word
    ~desc:"Occurs when a location of the memory becomes tracked."

let page_of addr =
  Int64.(Bitvec.to_int64 (Word.to_bitvec addr) land lnot (page_size - 1L))

module Make (Machine : Machine) = struct
  open Machine.Syntax

  let update f =
    Machine.Local.update state ~f:(fun s ->
        let s' = f s in
        if phys_equal s s' then s else { s' with version = s.version + 1 })

  let track v =
    update (fun s ->
        if Set.mem s.values (Value.id v) then s
        else { s with values = Set.add s.values (Value.id v) })

  let untrack v =
    update (fun s ->
        if Set.mem s.values (Value.id v) then
          { s with values = Set.remove s.values (Value.id v) }
        else s)

  let is_tracked v =
    Machine.Local.get state >>| fun s ->
    (not (Set.is_empty s.values)) && Set.mem s.values (Value.id v)

  let mark addr =
    Machine.Local.get state >>= fun s ->
    if Set.mem s.addrs addr then Machine.return ()
    else
      let page = page_of addr in
      Machine.Local.put state
        {
          addrs = Set.add s.addrs addr;
          pages =
            Map.update s.pages page ~f:(function None -> 1 | Some n -> n + 1);
          values = s.values;
          version = s.version + 1;
          covered = s.covered;
          code_covered = s.code_covered;
          opaque = s.opaque;
        }
      >>= fun () -> Machine.Observation.make on_marked addr

  let unmark addr =
    update (fun s ->
        if not (Set.mem s.addrs addr) then s
        else
          {
            s with
            addrs = Set.remove s.addrs addr;
            pages =
              Map.change s.pages (page_of addr) ~f:(function
                | Some n when n > 1 -> Some (n - 1)
                | _ -> None);
          })

  (* marks or unmarks the locations at once, see [mark] *)
  let set_marks marks =
    Machine.Local.get state >>= fun s ->
    let s', marked =
      List.fold marks ~init:(s, []) ~f:(fun (s, marked) (addr, on) ->
          let page = page_of addr in
          match (on, Set.mem s.addrs addr) with
          | true, false ->
              ( {
                  s with
                  addrs = Set.add s.addrs addr;
                  pages =
                    Map.update s.pages page ~f:(function
                      | None -> 1
                      | Some n -> n + 1);
                },
                addr :: marked )
          | false, true ->
              ( {
                  s with
                  addrs = Set.remove s.addrs addr;
                  pages =
                    Map.change s.pages page ~f:(function
                      | Some n when n > 1 -> Some (n - 1)
                      | _ -> None);
                },
                marked )
          | _ -> (s, marked))
    in
    if phys_equal s s' then Machine.return ()
    else
      Machine.Local.put state { s' with version = s.version + 1 } >>= fun () ->
      Machine.List.iter (List.rev marked)
        ~f:(Machine.Observation.make on_marked)

  let is_marked addr =
    Machine.Local.get state >>| fun s ->
    (not (Set.is_empty s.addrs)) && Set.mem s.addrs addr

  let page_marked addr =
    Machine.Local.get state >>| fun s ->
    (not (Map.is_empty s.pages)) && Map.mem s.pages (page_of addr)

  let stored addr v =
    Machine.Local.get state >>= fun s ->
    if Set.is_empty s.values && Set.is_empty s.addrs then Machine.return ()
    else if Set.mem s.values (Value.id v) then mark addr
    else unmark addr

  let active =
    Machine.Local.get state >>| fun s ->
    not (Set.is_empty s.values && Set.is_empty s.addrs)

  let has_marks =
    Machine.Local.get state >>| fun s -> not (Set.is_empty s.addrs)

  let version = Machine.Local.get state >>| fun s -> s.version

  let cover key =
    Machine.Local.update state ~f:(fun s ->
        {
          s with
          covered =
            Map.update s.covered (Observation.name key) ~f:(function
              | None -> 1
              | Some n -> n + 1);
        })

  let opaque = Machine.Local.update state ~f:(fun s -> { s with opaque = true })
  let is_opaque = Machine.Local.get state >>| fun s -> s.opaque

  let cover_code key =
    Machine.Local.update state ~f:(fun s ->
        {
          s with
          code_covered =
            Map.update s.code_covered (Observation.name key) ~f:(function
              | None -> 1
              | Some n -> n + 1);
        })

  let count covered key =
    Option.value (Map.find covered (Observation.name key)) ~default:0

  let uncovered key =
    Machine.Observation.observers key >>= fun n ->
    Machine.Local.get state >>| fun s ->
    n > count s.covered key + count s.code_covered key

  let code_covered key =
    Machine.Observation.observers key >>= fun n ->
    Machine.Local.get state >>| fun s ->
    let code = count s.code_covered key in
    code > 0 && n <= count s.covered key + code
end
