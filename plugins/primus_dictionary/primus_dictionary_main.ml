open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std

include Self()

type dict = {dict : Primus.value Primus.Value.Map.t}

type t = {
  dicts : dict Primus.Value.Map.t;
}

let pair key data = {dict = Primus.Value.Map.singleton key data}
let add key data s = {dict = Map.set s.dict ~key ~data}

(* idea: initialize the dictionary with initial
   properties of a project and terms.
*)
let state = Primus.Machine.State.declare
    ~uuid:"F050079C-7FDB-4A8F-8A59-72C9693ADBCE"
    ~name:"lisp-dictionaries"
    (fun _  ->
       {dicts = Primus.Value.Map.empty})

module Pre(Machine : Primus.Machine.S) = struct
  include Machine.Syntax
  module Value = Primus.Value.Make(Machine)
  let nil = Value.b0
  let bool = function
    | false -> nil
    | true -> Value.b1
end

module Add(Machine : Primus.Machine.S) = struct
  [@@@warning "-P"]
  include Pre(Machine)

  let run [dic; key; data] =
    Machine.Local.update state ~f:(fun s -> {
          dicts = Map.update s.dicts dic ~f:(function
              | None -> pair key data
              | Some dict -> add key data dict)
        }
      ) >>| fun () ->
    key
end

module Get(Machine : Primus.Machine.S) = struct
  [@@@warning "-P"]
  include Pre(Machine)

  let run [dic; key] =
    Machine.Local.get state >>= fun s ->
    match Map.find s.dicts dic with
    | None -> nil
    | Some {dict} -> match Map.find dict key with
      | None -> nil
      | Some x -> Machine.return x
end

module Next(Machine : Primus.Machine.S) = struct
  [@@@warning "-P"]
  include Pre(Machine)

  let run [dic; key] =
    Machine.Local.get state >>= fun s ->
    match Map.find s.dicts dic with
    | None -> nil
    | Some {dict} ->
      match Map.closest_key dict `Greater_than key with
      | None -> nil
      | Some (x,_) -> Machine.return x
end

module First(Machine : Primus.Machine.S) = struct
  [@@@warning "-P"]
  include Pre(Machine)

  let run [dic] =
    Machine.Local.get state >>= fun s ->
    match Map.find s.dicts dic with
    | None -> nil
    | Some {dict} -> match Map.min_elt dict with
      | None -> nil
      | Some (x,_) -> Machine.return x
end


module Length(Machine : Primus.Machine.S) = struct
  [@@@warning "-P"]
  include Pre(Machine)

  let run [dic] =
    Machine.gets Project.target >>| Theory.Target.bits >>= fun width ->
    Machine.Local.get state >>= fun s ->
    match Map.find s.dicts dic with
    | None -> nil
    | Some {dict} -> Value.of_int ~width (Map.length dict)
end

module Del(Machine : Primus.Machine.S) = struct
  [@@@warning "-P"]
  include Pre(Machine)

  let run = function
    | [dic] -> Machine.Local.update state ~f:(fun s -> {
          dicts = Map.remove s.dicts dic
        }) >>= fun () -> nil
    | [dic; key] -> Machine.Local.update state ~f:(fun s -> {
          dicts = Map.change s.dicts dic ~f:(function
              | None -> None
              | Some {dict} -> Some {
                  dict = Map.remove dict key
                })
        }) >>= fun () -> nil
end

module Has(Machine : Primus.Machine.S) = struct
  [@@@warning "-P"]
  include Pre(Machine)

  let run [dic; key] =
    Machine.Local.get state >>= fun {dicts} ->
    match Map.find dicts dic with
    | None -> nil
    | Some {dict} -> bool (Map.mem dict key)
end

module Main(Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  open Primus.Lisp.Type.Spec
  module Lisp = Primus.Lisp.Make(Machine)

  let def name types closure docs =
    Lisp.define ~docs  ~types name closure

  let init () =
    Machine.sequence [
      def "dict-add" (tuple [sym; a; b] @-> bool) (module Add)
        {|(dict-add DIC KEY DATA) associates DATA with KEY in the
          dictionary DIC. Returns KEY.|};

      def "dict-get" (tuple [sym; a] @-> b) (module Get)
        {|(dict-get DIC KEY) returns data associated with KEY in the
          dictionary DIC, and returns NIL if either DIC doesn't exist on
          no data are associated|};

      def "dict-has" (tuple [sym; a] @-> bool) (module Has)
        {|(dict-has DIC KEY) returns T if the dictionary DIC has the
          key KEY|};

      def "dict-del" (tuple [sym; a] @-> bool) (module Del)
        {|(dict-del DIC KEY) deletes any association with KEY in the
          dictionary DIC|};

      def "dict-first" (tuple [sym] @-> a) (module First)
        {|(dict-first DIC) is the first key in DIC or nil if DIC is empty.|};

      def "dict-next" (tuple [sym; a] @-> a) (module Next)
        {|(dict-next DIC KEY) returns the next key after KEY

        Returns nil if KEY was the last key in the dictionary.
        Could be used together with DICT-FIRST for iterating.|};

      def "dict-length" (tuple [sym] @-> int) (module Length)
        {|(dict-first DIC) is the total number of keys in DIC.|};
    ]
end


let desc = "Provides a key-value storage for Primus Lisp \
            programs. Dictionaries are represented with symbols and it is a \
            responsibility of user to prevent name clashing between different \
            dictionaries."

let () = Config.manpage [
    `S "DESCRIPTION";
    `P desc;
  ]

let () = Config.declare_extension
    ~doc:"provides a Primus Lisp key-value storage library"
    ~provides:["primus"; "primus-library"; "dictionary"]
  @@ fun _ ->
  Primus.Machine.add_component (module Main) [@warning "-D"];
  Primus.Components.register_generic "lisp-dictionary" (module Main)
    ~package:"bap"
    ~desc
