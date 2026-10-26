open Core
open Bap.Std
open Bap_core_theory

type kind = Call | Jump | Load | Store | Address
[@@deriving bin_io, compare, equal, sexp]

type xref = { site : int64; target : int64; kind : kind; slot : int64 option }
[@@deriving bin_io, compare, equal, sexp]

type t = {
  width : int;
  digest : string option;
  memory : value memmap;
  refs : xref list Int64.Table.t;  (** by the targets *)
  sites : xref list Int64.Table.t;  (** by the sites *)
  owners : int64 Int64.Table.t;  (** the functions of the sites *)
  bodies : int64 list Int64.Table.t;  (** the sites of the functions *)
  names : string Int64.Table.t;  (** the names of the functions *)
}

let live_digest =
  Value.Tag.register ~name:"live-digest"
    ~uuid:"5b1c7a2e-8d43-4f6a-9e21-3c0b7d5f8a64"
    (module String)

let project_digest proj = Project.get proj live_digest
let set_project_digest proj digest = Project.set proj live_digest digest
let int64_of_word w = Bitvec.to_int64 (Word.to_bitvec w)

(* the word of the width of the addresses at [addr], from the memory *)
let word_at t addr =
  let a = Addr.of_int64 ~width:t.width addr in
  Memmap.lookup t.memory a
  |> Seq.find_map ~f:(fun (mem, _) ->
      match Memory.get ~addr:a ~scale:(Size.of_int_exn t.width) mem with
      | Ok w -> Some (int64_of_word w)
      | Error _ -> None)

let is_mapped t addr =
  not
    (Seq.is_empty (Memmap.lookup t.memory (Addr.of_int64 ~width:t.width addr)))

(* the references of the expression, at the [site], the address of the
   instruction *)
let rec scan t ~site acc (e : exp) =
  let add kind target slot acc =
    if is_mapped t target then { site; target; kind; slot } :: acc else acc
  in
  match e with
  | Load (m, Int a, _, _) ->
      scan t ~site (add Load (int64_of_word a) None acc) m
  | Load (m, a, _, _) -> scan t ~site (scan t ~site acc m) a
  | Store (m, Int a, x, _, _) ->
      scan t ~site (scan t ~site (add Store (int64_of_word a) None acc) m) x
  | Store (m, a, x, _, _) ->
      scan t ~site (scan t ~site (scan t ~site acc m) a) x
  | Int w when Word.bitwidth w = t.width ->
      add Address (int64_of_word w) None acc
  | Int _ | Var _ | Unknown _ -> acc
  | BinOp (_, x, y) | Concat (x, y) | Let (_, x, y) ->
      scan t ~site (scan t ~site acc x) y
  | UnOp (_, x) | Cast (_, _, x) | Extract (_, _, x) -> scan t ~site acc x
  | Ite (c, x, y) -> scan t ~site (scan t ~site (scan t ~site acc c) x) y

(* the target of an indirect jump, a constant, or the word of a slot,
   which may be outside of the memory, e.g., the trampoline of an
   external function, which the slots of GOT hold in the emulator *)
let indirect t ~site kind (e : exp) acc =
  match e with
  | Int a -> { site; target = int64_of_word a; kind; slot = None } :: acc
  | Load (_, Int slot, _, _) -> (
      let slot = int64_of_word slot in
      match word_at t slot with
      | Some target -> { site; target; kind; slot = Some slot } :: acc
      | None -> acc)
  | _ -> scan t ~site acc e

let scan_program proj selected =
  let width = Theory.Target.code_addr_size (Project.target proj) in
  let t =
    {
      width;
      digest = project_digest proj;
      memory = Project.memory proj;
      refs = Int64.Table.create ();
      sites = Int64.Table.create ();
      owners = Int64.Table.create ();
      bodies = Int64.Table.create ();
      names = Int64.Table.create ();
    }
  in
  let prog = Project.program proj in
  (* the addresses of the subs, by their tids, once, as the subs are many *)
  let subs = Tid.Table.create () in
  Term.enum sub_t prog
  |> Seq.iter ~f:(fun sub ->
      Option.iter (Term.get_attr sub address) ~f:(fun a ->
          Hashtbl.set subs ~key:(Term.tid sub) ~data:(int64_of_word a)));
  let address_of_sub = Hashtbl.find subs in
  selected
  |> Seq.iter ~f:(fun sub ->
      match Term.get_attr sub address with
      | None -> ()
      | Some entry ->
          let entry = int64_of_word entry in
          Hashtbl.set t.names ~key:entry ~data:(Sub.name sub);
          let { Bap_emu_fold.ssa = sub; simplify; resolve } =
            Bap_emu_fold.fold sub
          in
          let sites = Int64.Hash_set.create () in
          (* the return addresses of the calls, which the calls of x86
             push, aren't references *)
          let blks = Tid.Table.create () in
          Term.enum blk_t sub
          |> Seq.iter ~f:(fun b ->
              Option.iter (Term.get_attr b address) ~f:(fun a ->
                  Hashtbl.set blks ~key:(Term.tid b) ~data:(int64_of_word a)));
          let returns =
            Term.enum blk_t sub
            |> Seq.concat_map ~f:(Term.enum jmp_t)
            |> Seq.filter_map ~f:(fun j ->
                match Jmp.kind j with
                | Call c -> (
                    match Call.return c with
                    | Some (Direct tid) -> Hashtbl.find blks tid
                    | _ -> None)
                | _ -> None)
            |> Seq.to_list |> Int64.Hash_set.of_list
          in
          let found xrefs =
            List.filter xrefs ~f:(fun x ->
                not (equal_kind x.kind Address && Hash_set.mem returns x.target))
          in
          Term.enum blk_t sub
          |> Seq.iter ~f:(fun blk ->
              let blk_addr =
                Option.map (Term.get_attr blk address) ~f:int64_of_word
              in
              let site term =
                match Term.get_attr term address with
                | Some a -> Some (int64_of_word a)
                | None -> blk_addr
              in
              let found xrefs =
                List.iter (found xrefs) ~f:(fun x ->
                    Hash_set.add sites x.site;
                    Hashtbl.add_multi t.refs ~key:x.target ~data:x;
                    Hashtbl.add_multi t.sites ~key:x.site ~data:x)
              in
              Term.enum def_t blk
              |> Seq.iter ~f:(fun d ->
                  match site d with
                  | None -> ()
                  | Some site ->
                      Hash_set.add sites site;
                      found (scan t ~site [] (simplify (Def.rhs d))));
              Term.enum jmp_t blk
              |> Seq.iter ~f:(fun j ->
                  match site j with
                  | None -> ()
                  | Some site ->
                      Hash_set.add sites site;
                      let acc = scan t ~site [] (simplify (Jmp.cond j)) in
                      let acc =
                        match Jmp.kind j with
                        | Call c -> (
                            match Call.target c with
                            | Direct tid -> (
                                match address_of_sub tid with
                                | Some target ->
                                    { site; target; kind = Call; slot = None }
                                    :: acc
                                | None -> acc)
                            | Indirect e ->
                                indirect t ~site Call (resolve e) acc)
                        | Goto (Indirect e) ->
                            indirect t ~site Jump (resolve e) acc
                        | Goto (Direct _) | Ret _ | Int _ -> acc
                      in
                      found acc));
          let sites = Hash_set.to_list sites in
          List.iter sites ~f:(fun site ->
              Hashtbl.set t.owners ~key:site ~data:entry);
          Hashtbl.set t.bodies ~key:entry
            ~data:(List.sort sites ~compare:Int64.compare));
  t

let create proj = scan_program proj (Term.enum sub_t (Project.program proj))

let create_focused proj entry =
  let prog = Project.program proj in
  let target =
    Term.enum sub_t prog
    |> Seq.find ~f:(fun sub ->
        Option.exists (Term.get_attr sub address) ~f:(fun addr ->
            Int64.equal (int64_of_word addr) entry))
  in
  match target with
  | None -> scan_program proj Seq.empty
  | Some target ->
      let tid = Term.tid target in
      let calls_target sub =
        Term.enum blk_t sub
        |> Seq.concat_map ~f:(Term.enum jmp_t)
        |> Seq.exists ~f:(fun jmp ->
            match Jmp.kind jmp with
            | Call call -> (
                match Call.target call with
                | Direct callee -> Tid.equal callee tid
                | Indirect _ -> false)
            | _ -> false)
      in
      Term.enum sub_t prog
      |> Seq.filter ~f:(fun sub ->
          Tid.equal (Term.tid sub) tid || calls_target sub)
      |> scan_program proj

let by_site xs =
  List.dedup_and_sort xs ~compare:(fun a b ->
      match Int64.compare a.site b.site with 0 -> compare_xref a b | n -> n)

let find t addr = Hashtbl.find_multi t.refs addr |> by_site
let of_insn t addr = Hashtbl.find_multi t.sites addr |> by_site
let function_of t addr = Hashtbl.find t.owners addr
let name t addr = Hashtbl.find t.names addr

let of_function t addr =
  Hashtbl.find_multi t.bodies addr
  |> List.concat_map ~f:(Hashtbl.find_multi t.sites)
  |> by_site

let callers t addr =
  find t addr
  |> List.filter_map ~f:(fun x ->
      if equal_kind x.kind Call then function_of t x.site else None)
  |> List.dedup_and_sort ~compare:Int64.compare

let callees t addr =
  of_function t addr
  |> List.filter_map ~f:(fun x ->
      Option.some_if (equal_kind x.kind Call) x.target)
  |> List.dedup_and_sort ~compare:Int64.compare

let all t = Hashtbl.data t.sites |> List.concat |> by_site
let functions t = Hashtbl.keys t.names |> List.sort ~compare:Int64.compare

(* the calls, that a trace recorded, see [Bap_emu.Trace.calls], are the
   references too, e.g., through the slots, that the program fills at
   run time *)
let add_calls t calls =
  List.iter calls ~f:(fun (site, targets) ->
      List.iter targets ~f:(fun (target, _) ->
          let x = { site; target; kind = Call; slot = None } in
          if
            not (List.mem (Hashtbl.find_multi t.sites site) x ~equal:equal_xref)
          then begin
            Hashtbl.add_multi t.refs ~key:target ~data:x;
            Hashtbl.add_multi t.sites ~key:site ~data:x
          end))

(* the index, as the files keep it, without the memory, which only
   [create] reads *)
module Saved = struct
  type t = {
    width : int;
    digest : string option;
    refs : xref list Int64.Table.t;
    sites : xref list Int64.Table.t;
    owners : int64 Int64.Table.t;
    bodies : int64 list Int64.Table.t;
    names : string Int64.Table.t;
  }
  [@@deriving bin_io]

  let magic = "bap-emu-xrefs 2\n"
end

let save t file =
  let saved =
    {
      Saved.width = t.width;
      digest = t.digest;
      refs = t.refs;
      sites = t.sites;
      owners = t.owners;
      bodies = t.bodies;
      names = t.names;
    }
  in
  Out_channel.write_all file
    ~data:(Saved.magic ^ Binable.to_string (module Saved) saved)

let load proj file =
  let data =
    try In_channel.read_all file
    with Sys_error msg -> failwithf "Bap_emu.Xrefs.load: %s" msg ()
  in
  match String.chop_prefix data ~prefix:Saved.magic with
  | None -> failwithf "Bap_emu.Xrefs.load: %s is not a saved index" file ()
  | Some data -> (
      match Binable.of_string (module Saved) data with
      | { Saved.width; digest; refs; sites; owners; bodies; names } ->
          if not (Option.equal String.equal digest (project_digest proj)) then
            failwithf "Bap_emu.Xrefs.load: %s is of another project" file ();
          {
            width;
            digest;
            memory = Memmap.empty;
            refs;
            sites;
            owners;
            bodies;
            names;
          }
      | exception exn ->
          failwithf "Bap_emu.Xrefs.load: %s is broken: %s" file
            (Exn.to_string exn) ())
