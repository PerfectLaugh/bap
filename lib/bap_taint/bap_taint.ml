open Core
open Bap.Std
open Bap_primus.Std
open Monads.Std
open Bap_strings.Std
module Vid = Primus.Value.Id

type vid = Vid.t
type value = Primus.value

module type Value = sig
  type t
  type 'a m

  val to_value : t -> Primus.value m
  val of_value : Primus.value -> t m
end

module type comparable_with_value =
  Comparable.S_plain
    with type comparator_witness = Primus.Value.comparator_witness

module Ident (Machine : Primus.Machine.S) = struct
  type t = value
  type 'a m = 'a Machine.t

  let to_value = Machine.return
  let of_value = Machine.return
end

(* a global registry of all ever created objects *)
type kinds = { objects : value Primus.Value.Map.t }

let kinds =
  Primus.Machine.State.declare ~name:"tainter-object-kinds"
    ~uuid:"a97f9cf6-541a-4127-9eb6-6c24f67ed8b9" (fun _ ->
      { objects = Primus.Value.Map.empty })

module Object = struct
  type Primus.exn += Bad_object of Primus.value

  let t = Primus.Lisp.Type.Spec.word 63

  module Make (Machine : Primus.Machine.S) = struct
    module Value = Primus.Value.Make (Machine)
    open Machine.Syntax

    let next_key { objects } =
      match Map.max_elt objects with
      | None -> Value.of_int 1 ~width:63
      | Some (k, _) -> Value.succ k

    let create kind =
      Machine.Global.get kinds >>= fun s ->
      next_key s >>= fun key ->
      Machine.Global.put kinds { objects = Map.set s.objects ~key ~data:kind }
      >>| fun () -> key

    let kind v =
      Machine.Global.get kinds >>= fun { objects } ->
      match Map.find objects v with
      | None -> Machine.raise (Bad_object v)
      | Some x -> Machine.return x

    include Ident (Machine)
  end

  include (Primus.Value : comparable_with_value with type t = value)

  let to_string x = Format.asprintf "%a" Word.pp_dec (Primus.Value.to_word x)
  let sexp_of_t x = Sexp.Atom (to_string x)
  let inspect x = sexp_of_t x
end

type objects = Object.Set.t

(* state of the taint engine.
 *
 * The taint engine maintains a set of values and pointers that
 * reference tainted objects. Another interpretation is that we are
 * attaching some semantic information (represented as identifiers) to
 * immediate _and_ addresses.
 *
 * Each object is represented by a unique id that was assigned to it,
 * when the object was originally tainted (i.e., when the taint was introduced).
 *
 * So far we have only two kinds of relations between a value and a
 * tainted value - direct, when a value either contains bits of the
 * tainted object or is influenced by them, and indirect, when a value
 * is an address to a tainted value. We may later add more relations,
 * for example, when a value is not influenced by the object that we
 * track, but in fact contains the object (or bits of this
 * object). So far we are keeping the relation object abstract that
 * will allow us to extend it later.
 *
 * If a tainted object is no longer reachable, then we say that the
 * taint is killed. Thus precise tainting is an instance of the
 * garbage collection problem.
 *)
type tainter = {
  direct : objects Vid.Map.t;
  indirect : objects Primus.Value.Map.t;
}
[@@deriving fields]

type relation_kind = Direct | Indirect [@@deriving compare, sexp_of]

(* generalized access to the tainter fields
 *
 * - [select.field] selects either direct or indirect field of the
 *   tainter (should be used with [Field.get] and [Field.fset])
 *  - [select.key] maps value to the key of the appropriate type
 *   (i.e., to Id in case of direct, and addr in case of indirect)
 *
 *  With the selector object it is possible to write a function that
 *  will be polymorphic across two fields of the tainter (sort of
 *  extremely bounded polymorphism).
 *)
type relation =
  | Rel : {
      field : (tainter, ('k, objects, 'c) Map.t) Field.t;
      key : Primus.value -> 'k;
      kind : relation_kind;
    }
      -> relation

type gc_local = { old : tainter }

let empty_tainter =
  { direct = Vid.Map.empty; indirect = Primus.Value.Map.empty }

let tainter =
  Primus.Machine.State.declare ~name:"primus-tainter"
    ~uuid:"2d4a4208-f918-4cf7-8e1b-5d8400a106d3" (fun _ -> empty_tainter)

let gc =
  Primus.Machine.State.declare ~name:"primus-taint-gc"
    ~uuid:"2357826e-d5b7-40a3-8f90-0cfd7b48eadc" (fun _ ->
      { old = empty_tainter })

let vid = Primus.Value.id

let indirect =
  Rel { field = Fields_of_tainter.indirect; key = Fn.id; kind = Indirect }

let direct = Rel { field = Fields_of_tainter.direct; key = vid; kind = Direct }

module Kind = struct
  type t = value

  module Make (Machine : Primus.Machine.S) = struct
    module Value = Primus.Value.Make (Machine)

    let create = Value.Symbol.to_value
    let name = Value.Symbol.of_value

    include Ident (Machine)
  end

  include (Primus.Value : comparable_with_value with type t := t)
end

module Rel = struct
  type t = relation

  let direct = direct
  let indirect = indirect

  let compare (Rel { kind = x; _ }) (Rel { kind = y; _ }) =
    compare_relation_kind x y

  let equal x y = compare x y = 0
end

(* a set of live tainted objects *)
let objects { direct; indirect } : objects =
  let to_set m : objects =
    Map.to_sequence m |> Seq.map ~f:snd
    |> Seq.fold ~init:Object.Set.empty ~f:Set.union
  in
  Set.union (to_set direct) (to_set indirect)

module Taint = struct
  type Primus.exn += Bad_cast of Primus.value

  let inspect (Rel { kind }, o, v) =
    Sexp.List
      [ sexp_of_relation_kind kind; Object.sexp_of_t o; Primus.sexp_of_value v ]

  let attached, attach =
    Primus.Observation.provide ~inspect "taint-attached"
      ~desc:"Occurs when a taint is attached to the value."

  module Make (Machine : Primus.Machine.S) = struct
    module Value = Primus.Value.Make (Machine)
    module Taint = Object.Make (Machine)
    open Machine.Syntax
    module Track = Primus.Track.Make (Machine)

    let report_attached r t v = Machine.Observation.make attach (r, t, v)

    (* the tainted values and locations are left to the interpreter *)
    let track (Rel { kind }) v =
      match kind with
      | Direct -> Track.track v
      | Indirect -> Track.mark (Primus.Value.to_word v)

    let change v (Rel { field; key }) ~f =
      Machine.Local.update tainter ~f:(fun t ->
          Field.fset field t @@ Map.change (Field.get field t) (key v) ~f)

    let attach v r ts =
      change v r ~f:(function
        | None -> Some ts
        | Some ts' -> Some (Set.union ts ts'))
      >>= fun () ->
      (if Set.is_empty ts then Machine.return () else track r v) >>= fun () ->
      Machine.Observation.post attach ~f:(fun report ->
          Set.to_sequence ts |> Machine.Seq.iter ~f:(fun o -> report (r, o, v)))

    let detach v r ts =
      change v r ~f:(function
        | None -> None
        | Some ts' ->
            let ts = Set.diff ts' ts in
            if Set.is_empty ts then None else Some ts)

    let lookup v (Rel { field; key }) =
      Machine.Local.get tainter >>| fun t ->
      match Map.find (Field.get field t) (key v) with
      | None -> Object.Set.empty
      | Some s -> s

    let int_of_value x =
      match Word.to_int (Value.to_word x) with
      | Error _ -> Machine.raise (Bad_cast x)
      | Ok x -> Machine.return x

    let new_direct value kind =
      Taint.create kind >>= fun taint ->
      Machine.Local.update tainter ~f:(fun s ->
          {
            s with
            direct =
              Map.update s.direct (Primus.Value.id value) ~f:(function
                | None -> Object.Set.singleton taint
                | Some taints -> Set.add taints taint);
          })
      >>= fun () ->
      Track.track value >>= fun () ->
      report_attached Rel.direct taint value >>| fun () -> taint

    let new_indirect ~addr ~len kind =
      Taint.create kind >>= fun taint ->
      int_of_value len >>= fun len ->
      Machine.Local.get tainter >>= fun s ->
      Seq.range 0 len
      |> Machine.Seq.fold ~init:s.indirect ~f:(fun indirect off ->
          Value.nsucc addr off >>= fun addr ->
          Track.mark (Primus.Value.to_word addr) >>= fun () ->
          report_attached Rel.indirect taint addr >>| fun () ->
          Map.update indirect addr ~f:(function
            | None -> Object.Set.singleton taint
            | Some taints -> Set.add taints taint))
      >>= fun indirect ->
      Machine.Local.put tainter { s with indirect } >>| fun () -> taint

    let kill_objects kill =
      Map.filter_map ~f:(fun objects ->
          match Set.diff objects kill with
          | s when Set.is_empty s -> None
          | s -> Some s)

    let sanitize v r k =
      Machine.Global.get kinds >>= fun { objects } ->
      lookup v r
      >>| Set.filter ~f:(fun t ->
          match Map.find objects t with
          | None -> false
          | Some k' -> Kind.(k = k'))
      >>= fun kill ->
      Machine.Local.update tainter ~f:(fun { direct; indirect } ->
          {
            direct = kill_objects kill direct;
            indirect = kill_objects kill indirect;
          })

    let objects = Machine.Local.get tainter >>| objects
  end
end

module Propagation = struct
  type policies = {
    servers : Primus.value Kind.Map.t;
    default : Primus.value option;
  }

  let policies =
    Primus.Machine.State.declare ~name:"taint-policies"
      ~uuid:"4c370c33-ef1b-4e10-be27-ee751a4d6cf3" (fun _ ->
        { servers = Kind.Map.empty; default = None })

  module Policy = struct
    type t = value

    module Make (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Tracker = Taint.Make (Machine)

      let select p k =
        Machine.Local.update policies ~f:(fun s ->
            {
              servers = Map.set s.servers ~key:k ~data:p;
              default = Option.first_some s.default (Some p);
            })

      let set_default p =
        Machine.Local.update policies ~f:(fun s -> { s with default = Some p })

      let has_selected ~policy:p ~kind:k { servers; default } =
        match Map.find servers k with
        | Some p' -> Primus.Value.equal p p'
        | None -> (
            match default with
            | None -> false
            | Some p' -> Primus.Value.equal p p')

      let selected policy kind =
        Machine.Local.get policies >>| has_selected ~policy ~kind

      let select_objects { objects } policies ~policy ts =
        Set.filter ts ~f:(fun v ->
            match Map.find objects v with
            | None -> false
            | Some kind -> has_selected policies ~policy ~kind)

      let collect_taints p (Rel ms) srcs s =
        Machine.Global.get kinds >>= fun kinds ->
        Machine.Local.get policies >>| fun policies ->
        let filter = select_objects kinds policies ~policy:p in
        List.fold srcs ~init:Object.Set.empty ~f:(fun objs src ->
            match Map.find (Field.get ms.field s) (ms.key src) with
            | None -> objs
            | Some objs' -> Set.union (filter objs') objs)

      let append_taints m key ts =
        Map.update m key ~f:(function
          | None -> ts
          | Some ts' -> Set.union ts ts')

      let propagate p ms md srcs dst =
        Machine.Local.get tainter >>= fun s ->
        collect_taints p ms srcs s >>= fun taints ->
        Tracker.attach dst md taints

      include Ident (Machine)
    end
  end
end

(* tracks live tainted objects, removes unnecessary references.

   A tainted object is live, if it is reachable either directly or
   indirectly in the tainted. The indirect references are dropped
   implicitly, when an address is overwritten with the new tainted
   object (since we have finite set of addresses). The direct
   references use value identifiers, that are dynamic, so we need to
   track which of them still live. Since values are stored only in
   Env, we can easily compute the set of live values.

   Finally, we compute a set of live objects on the entrance to a
   basic block, and a set of live objects at the exit of the basic
   block, the difference between these two are the objects that were
   killed in the block. We make an observation about each killed
   object.

*)
module Gc = struct
  let sexp_of_finish (t, live) =
    Sexp.List [ Primus.sexp_of_value t; sexp_of_bool live ]

  let taint_finalize, taint_finished =
    Primus.Observation.provide ~inspect:sexp_of_finish "taint-finalize"
      ~desc:"Occurs when the taint becomes unreachable."

  module Conservative (Machine : Primus.Machine.S) = struct
    open Machine.Syntax
    module Env = Primus.Env.Make (Machine)
    module Value = Primus.Value.Make (Machine)

    let finish ~live t = Machine.Observation.make taint_finished (t, live)

    (* removes directly dead taints *)
    let collect_direct =
      Machine.Local.get tainter >>= fun s ->
      Env.all >>= fun vars ->
      Machine.Seq.fold vars ~init:Vid.Set.empty ~f:(fun live var ->
          Env.is_set var >>= function
          | false -> !!live
          | true -> Env.get var >>| fun v -> Set.add live (Value.id v))
      >>= fun live ->
      Machine.Local.put tainter
        { s with direct = Map.filter_keys s.direct ~f:(Set.mem live) }

    let finish_taints ~live objects =
      Set.to_sequence objects |> Machine.Seq.iter ~f:(finish ~live)

    let main _ =
      Machine.Local.get gc >>= fun { old } ->
      collect_direct >>= fun () ->
      Machine.Local.get tainter >>= fun cur ->
      let dying = Set.diff (objects old) (objects cur) in
      Machine.forks ()
      >>= Machine.Seq.fold ~init:dying ~f:(fun dying id ->
          Machine.Other.get id tainter >>| fun taints ->
          Set.diff dying (objects taints))
      >>= fun dead ->
      let live = Set.diff dying dead in
      Machine.sequence
        [
          Machine.Local.put gc { old = cur };
          finish_taints dead ~live:false;
          finish_taints live ~live:true;
        ]

    let init () = Machine.sequence Primus.Interpreter.[ pc_change >>> main ]
  end
end

(* The taint of the machine, which the checkpoints keep, see
   [Primus.Checkpoint]: the kinds of the objects, the objects of the
   addresses, and the objects of the values of the variables, which are
   the only values, that have them, see [Gc], as the values are created
   anew, when the machine continues from the checkpoint, and the values
   and the locations, that have the objects, are tracked again, see
   [Primus.Track]. *)
module Persistent = struct
  type t = {
    kinds : (word * string) list;  (** the objects and their kinds *)
    direct : (var * word list) list;  (** the objects of the variables *)
    indirect : (word * word list) list;  (** the objects of the addresses *)
  }
  [@@deriving bin_io]

  module Extension (Machine : Primus.Machine.S) = struct
    open Machine.Syntax
    module Env = Primus.Env.Make (Machine)
    module Value = Primus.Value.Make (Machine)
    module Track = Primus.Track.Make (Machine)

    let words objects = Set.to_list objects |> List.map ~f:Primus.Value.to_word

    let objects words =
      Machine.List.map words ~f:Value.of_word >>| Object.Set.of_list

    let save =
      Machine.Global.get kinds >>= fun { objects } ->
      Machine.Local.get tainter >>= fun { direct; indirect } ->
      Machine.List.map (Map.to_alist objects) ~f:(fun (obj, kind) ->
          Value.Symbol.of_value kind >>| fun name ->
          (Primus.Value.to_word obj, name))
      >>= fun kinds ->
      Env.all >>| Seq.to_list >>= fun vars ->
      Machine.List.filter_map vars ~f:(fun var ->
          Env.is_set var >>= function
          | false -> Machine.return None
          | true ->
              Env.get var >>| fun x ->
              Map.find direct (Primus.Value.id x)
              |> Option.bind ~f:(fun objects ->
                  Option.some_if
                    (not (Set.is_empty objects))
                    (var, words objects)))
      >>| fun direct ->
      (* the locations without the taint, e.g., that were attached
         nothing, aren't tracked, when the checkpoint is restored *)
      let indirect =
        Map.to_alist indirect
        |> List.filter_map ~f:(fun (addr, objects) ->
            Option.some_if
              (not (Set.is_empty objects))
              (Primus.Value.to_word addr, words objects))
      in
      if List.is_empty kinds then None
      else
        Some
          (Binable.to_string
             (module struct
               type nonrec t = t [@@deriving bin_io]
             end)
             { kinds; direct; indirect })

    let restore data =
      let saved =
        Binable.of_string
          (module struct
            type nonrec t = t [@@deriving bin_io]
          end)
          data
      in
      Machine.List.map saved.kinds ~f:(fun (obj, name) ->
          Value.of_word obj >>= fun obj ->
          Value.Symbol.to_value name >>| fun kind -> (obj, kind))
      >>= fun kinds' ->
      Machine.Global.put kinds
        { objects = Primus.Value.Map.of_alist_reduce kinds' ~f:(fun _ k -> k) }
      >>= fun () ->
      Machine.List.fold saved.direct ~init:Vid.Map.empty
        ~f:(fun direct (var, words) ->
          Env.get var >>= fun x ->
          Track.track x >>= fun () ->
          objects words >>| fun objects ->
          Map.set direct ~key:(Primus.Value.id x) ~data:objects)
      >>= fun direct ->
      Machine.List.fold saved.indirect ~init:Primus.Value.Map.empty
        ~f:(fun indirect (addr, words) ->
          Track.mark addr >>= fun () ->
          Value.of_word addr >>= fun addr ->
          objects words >>| fun objects ->
          Map.set indirect ~key:addr ~data:objects)
      >>= fun indirect ->
      let restored = { direct; indirect } in
      Machine.Local.put tainter restored >>= fun () ->
      Machine.Local.put gc { old = restored }
  end

  let () = Primus.Checkpoint.register ~package:"bap" "taint" (module Extension)
end

module Std = struct
  module type Value = Value

  module Taint = struct
    module Object = Object
    module Kind = Kind
    module Rel = Rel
    module Tracker = Taint
    module Propagation = Propagation
    module Gc = Gc

    let attached = Taint.attached
  end
end
