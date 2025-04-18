open Core
open Bap.Std
open Bap_core_theory
open Monads.Std

open Bap_primus_lisp_types
open Bap_primus_lisp_attributes

module Attribute = Bap_primus_lisp_attribute
module Program = Bap_primus_lisp_program
module Context = Bap_primus_lisp_context
module Source = Bap_primus_lisp_source
module Resolve = Bap_primus_lisp_resolve
module Def = Bap_primus_lisp_def
module Type = Bap_primus_lisp_type
module Key = Bap_primus_lisp_program.Items

open KB.Syntax
open KB.Let

module State = struct
  type t = {
    binds : unit Theory.Value.t Map.M(Theory.Var.Top).t;
    arith : (module Bitvec.S);
    scope : unit Theory.var list Map.M(Theory.Var.Top).t;
  }

  let empty = {
    binds = Map.empty (module Theory.Var.Top);
    arith = (module Bitvec.M32);
    scope = Map.empty (module Theory.Var.Top);
  }

  let var = KB.Context.declare ~package:"bap" "lisp-interpter-state"
      !!empty


  let get = KB.Context.get var
  let set = KB.Context.set var
  let update = KB.Context.update var
end


type value = unit Theory.Value.t
type effect_ = unit Theory.Effect.t

type KB.Conflict.t +=
  | Unresolved_definition of string
  | User_error of string

let package = "bap"
let language = Theory.Language.declare ~package "primus-lisp"

let program =
  KB.Class.property Theory.Source.cls "primus-lisp-program"
    ~public:true
    ~package @@
  KB.Domain.flat "lisp-program"
    ~empty:Program.empty
    ~equal:Program.equal
    ~join:(fun x y -> Ok (Program.merge x y))

let context = Context.slot


type kind = Prim | Defn | Meth | Data [@@deriving sexp]

type program = {
  prog : Program.t;
  places : unit Theory.var Map.M(KB.Name).t;
  names : kind Map.M(KB.Name).t;
}

let typed = KB.Class.property Theory.Source.cls "typed-program"
    ~package @@
  KB.Domain.optional "typed-lisp-program"
    ~equal:(fun x y ->
        Program.equal x.prog y.prog)


type problem =
  | Resolution of Resolve.resolution
  | Uncallable
  | Unexpected of kind

let pp_problem ppf = function
  | Resolution err -> Resolve.pp_resolution ppf err
  | Uncallable ->
    Format.fprintf ppf "This item is not callable"
  | Unexpected Prim -> ()
  | Unexpected kind ->
    Format.fprintf ppf "internal error, unexpected %a"
      Sexp.pp (sexp_of_kind kind)


let unresolved name problem =
  let msg =
    Format.asprintf "Failed to find a definition for %a.@ %a@."
      KB.Name.pp name
      pp_problem problem in
  KB.fail (Unresolved_definition msg)

let resolve prog item name =
  match Resolve.semantics prog item name () with
  | None -> !!None
  | Some (Error problem) -> unresolved name (Resolution problem)
  | Some (Ok (fn,_)) -> !!(Some fn)

let check_arg _ _ = true

let is_external def =
  not @@ Set.is_empty (Attribute.Set.get External.t (Def.attributes def))

type body = (Theory.Target.t -> (Theory.Label.t -> Theory.Value.Top.t list -> unit Theory.eff) KB.t)

type info = {
  types : (Theory.Target.t -> Type.signature);
  docs : string;
  body : body option;
  kind : [`meth | `defn]
}

let library = Hashtbl.create (module KB.Name)

module Property = struct
  let name = KB.Class.property Theory.Program.cls ~package "lisp-name" @@
    KB.Domain.optional "lisp-name"
      ~equal:KB.Name.equal
      ~inspect:KB.Name.sexp_of_t

  type args = Theory.Value.Top.t list [@@deriving equal, sexp]


  type KB.conflict += Unequal_arity

  let args = KB.Class.property Theory.Program.cls ~package "lisp-args" @@
    KB.Domain.optional "lisp-args"
      ~equal:equal_args
      ~inspect:sexp_of_args
      ~join:(fun xs ys ->
          List.map2 xs ys ~f:(KB.Domain.join Theory.Value.Top.domain) |>
          function
          | Ok rs -> Result.all rs
          | Unequal_lengths -> Error Unequal_arity)
end

let definition =
  KB.Class.property Theory.Program.cls "lisp-definition"
    ~package
    ~public:true
    ~persistent:(KB.Persistent.of_binable (module struct
                   type t = Theory.Label.t option [@@deriving bin_io]
                 end)) @@
  KB.Domain.optional "label"
    ~equal:Theory.Label.equal
    ~inspect:Theory.Label.sexp_of_t

let dummy_type _ = Type.{
    args = [];
    rest = Some any;
    ret = any;
  }


let declare
    ?(types=dummy_type)
    ?(docs="undocumented") ?package ?body name =
  let name = KB.Name.create ?package name in
  if Hashtbl.mem library name
  then invalid_argf "A semantic primitive `%s' already exists, \
                     please choose a different name for your \
                     primitive"
      (KB.Name.show name) ();
  Hashtbl.add_exn library ~key:name ~data:{
    docs;
    types;
    body;
    kind = `defn;
  }

let signal ?params ?(docs="undocumented") property reflect =
  let name = KB.Slot.name property in
  if Hashtbl.mem library name
  then invalid_argf "The signal `%s' is already reflected."
      (KB.Name.show name) ();
  let app ts t = List.(ts >>| fun typ -> typ t) in
  let types t = match params with
    | None -> dummy_type t
    | Some (`All typ) -> Type.signature ~rest:(typ t) [] Any
    | Some (`Tuple ts) -> Type.signature (app ts t) Any
    | Some (`Gen (ts,r)) ->
      Type.signature ~rest:(r t) (app ts t) Any in
  KB.observe property @@begin fun lbl x ->
    let* args = reflect lbl x in
    KB.sequence [
      KB.provide Property.name lbl (Some name);
      KB.provide Property.args lbl (Some args);
    ] >>= fun () ->
    KB.collect Theory.Semantics.slot lbl >>| ignore
  end;
  Hashtbl.add_exn library ~key:name ~data:{
    docs;
    types;
    body=None;
    kind=`meth;
  }



let sort = Theory.Value.sort
let size x = Theory.Bitv.size (sort x)
let lisp_machine =
  Theory.Effect.Sort.(join [data "unrepresented-lisp-machine"] [top])

let forget = Theory.Value.forget
let create eff res =
  KB.Value.put Theory.Semantics.value eff (forget res)


let symbol =
  KB.Class.property Theory.Value.cls "lisp-symbol" @@
  KB.Domain.optional "symbol"
    ~equal:String.equal
    ~inspect:(fun x -> Sexp.Atom x)

let static_slot =
  KB.Class.property Theory.Value.cls "static-value"
    ~package
    ~public:true
    ~persistent:(KB.Persistent.of_binable (module struct
                   type t = Bitvec_binprot.t option [@@deriving bin_io]
                 end)) @@
  KB.Domain.optional "bitvec"
    ~equal:Bitvec.equal
    ~inspect:(fun x -> Sexp.Atom (Bitvec.to_string x))

let update_value r f =
  let v = KB.Value.get Theory.Semantics.value r in
  KB.Value.put Theory.Semantics.value r (f v)

let set_static r x = update_value r @@ fun v ->
  KB.Value.put static_slot v (Some x)

let symsort = Bap_primus_value.Index.key_width
let res = KB.Value.get Theory.Semantics.value
let bits = Theory.Bitv.define

let (!) = KB.(!!)

let empty = Theory.Effect.empty Theory.Effect.Sort.bot

let intern name =
  let open KB.Syntax in
  let name = KB.Name.read name in
  KB.Symbol.intern (KB.Name.unqualified name) Theory.Value.cls >>|
  KB.Object.id >>| Int63.to_int64 >>|
  Bitvec.M64.int64

let make_reg var =
  let open KB.Syntax in
  let empty = Theory.Value.empty (Theory.Var.sort var) in
  let name = Theory.Var.name var in
  intern name >>| fun value ->
  let res = KB.Value.put symbol empty (Some name) in
  KB.Value.put static_slot res (Some value)

let sym str =
  let v = update_value empty @@ fun v ->
    KB.Value.put symbol v (Some str) in
  match str with
  | "t" -> KB.return@@set_static v Bitvec.one
  | "nil" -> KB.return@@set_static v Bitvec.zero
  | name ->
    intern name >>|
    set_static v

module Value = struct
  type t = value
  let empty : t  = Theory.Value.Top.empty
  let custom p x = empty.$[p] <- x
  let static x = custom static_slot (Some x)
  let symbol s = custom symbol (Some s)
  let nil = static Bitvec.zero
end

module Effect = struct
  type t = effect_
  let pure x : t = empty.$[Theory.Semantics.value] <- x
  let return x : t KB.t = KB.return@@pure x
end


let static x =
  KB.Value.get static_slot (res x)

let reify_sym x = match static x with
  | Some _ -> KB.return x
  | None -> match KB.Value.get symbol (res x) with
    | None -> KB.return x
    | Some name ->
      intern name >>|
      set_static x

let is_machine_var t v =
  Set.mem (Theory.Target.vars t) (Theory.Var.forget v)

let machine_var_by_name t name =
  Set.find (Theory.Target.vars t) ~f:(fun v ->
      String.equal (Theory.Var.name v) name)

let make_var ?t:constr places target name  =
  let word = Theory.Target.bits target in
  match Map.find places name with
  | Some v -> v
  | None ->
    let t = Option.value constr ~default:word in
    Theory.Var.forget@@Theory.Var.define (bits t) (KB.Name.to_string name)

let lookup_parameter prog v =
  let v = KB.Name.read @@ Theory.Var.name v in
  let name = KB.Name.unqualified v in
  Program.in_package (KB.Name.package v) prog @@ fun prog ->
  match Program.get ~name prog Key.para with
  | p :: _ -> Some (Def.Para.default p)
  | [] -> None

let is_parameter prog v = Option.is_some (lookup_parameter prog v)

module Env = struct

  let lookup v =
    let v = Theory.Var.forget v in
    let+ {binds} = State.get in
    Map.find binds v


  let set v x =
    State.update @@ fun s -> {
      s with binds = Map.set s.binds
                 ~key:(Theory.Var.forget v) ~data:x
    }

  let del v =
    State.update @@ fun s -> {
      s with binds = Map.remove s.binds (Theory.Var.forget v)
    }

  let is_bound v = lookup v >>| Option.is_some

  let var word {data={exp=n; typ=t}} =
    let s = match t with
      | Any | Name _ -> word
      | Symbol -> symsort
      | Type m -> m in
    Theory.Var.forget@@Theory.Var.define (bits s) (KB.Name.to_string n)

  let set_args ws bs =
    let* s = State.get in
    let binds,old =
      List.fold bs ~init:(s.binds,[]) ~f:(fun (s,old) (v,x) ->
          let v = var ws v in
          Map.set s ~key:v ~data:x,(v,Map.find s v) :: old) in
    State.set {s with binds} >>| fun () ->
    List.rev old

  let del_args bs = State.update @@ fun s -> {
      s with binds = List.fold bs ~init:s.binds ~f:(fun s (v,x) ->
      match x with
      | None -> Map.remove s v
      | Some x -> Map.set s ~key:v ~data:x)
    }
end

module Scope = struct
  let forget = Theory.Var.forget

  let push orig =
    let orig = forget orig in
    Theory.Var.fresh (Theory.Var.sort orig) >>= fun v ->
    State.update  (fun s -> {
          s with scope = Map.update s.scope orig ~f:(function
        | None -> [v]
        | Some vs -> v::vs)
        }) >>| fun () ->
    v

  let lookup orig =
    let+ {scope} = State.get in
    match Map.find scope orig with
    | None | Some [] -> None
    | Some (x :: _) -> Some x

  let pop orig =
    State.update @@ fun s -> {
      s with scope = Map.change s.scope (forget orig) ~f:(function
        | None | Some [] | Some [_] -> None
        | Some (_::xs) -> Some xs)
    }

  let clear =
    let* s = State.get in
    let+ () = State.set {
        s with scope = Map.empty (module Theory.Var.Top)
      } in
    s.scope

  let restore scope = State.update @@ fun s -> {
      s with scope
    }

end

module Prelude(CT : Theory.Core) = struct
  let null = KB.Object.null Theory.Program.cls
  let fresh = KB.Object.create Theory.Program.cls

  let rec seq = function
    | [] -> CT.perform Theory.Effect.Sort.bot
    | [x] -> x
    | x :: xs ->
      let* xs = seq xs in
      let* x = x in
      CT.seq (KB.return x) (KB.return xs)

  let skip = CT.perform Theory.Effect.Sort.bot
  let pass = CT.perform Theory.Effect.Sort.bot

  let pure res =
    res >>| fun res ->
    create empty res

  let bigint x m =
    let s = bits m in
    let m = Bitvec.modulus m in
    let x = Bitvec.(bigint x mod m) in
    pure @@ CT.int s x >>| fun r ->
    set_static r x

  let (:=) v x = CT.set v x

  let full eff res =
    seq eff >>= fun eff ->
    res >>| fun res ->
    create eff res

  let data xs =
    let* data = seq xs in
    CT.blk null !data skip

  let ctrl xs =
    let* ctrl = seq xs in
    CT.blk null pass !ctrl

  let blk lbl xs = seq [
      CT.blk lbl pass skip;
      seq xs;
    ]

  let nil = !!(Theory.Value.empty Theory.Bool.t)
  let undefined = full [] nil
  let purify eff =
    full [] !!(res eff)

  let coerce_bits s x f =
    let open Theory.Value.Match in
    let| () = can Theory.Bitv.refine x @@ fun x ->
      CT.cast s CT.b0 !x >>= f in
    let| () = can Theory.Bool.refine x @@ fun cnd ->
      CT.ite !cnd
        (CT.int s Bitvec.one)
        (CT.int s Bitvec.zero) >>= fun x ->
      f x in
    undefined

  let coerce_bool x f =
    let open Theory.Value.Match in
    let| () = can Theory.Bool.refine x f in
    let| () = can Theory.Bitv.refine x @@ fun x ->
      CT.non_zero !x >>= fun x -> f x in
    undefined

  let is_static eff = Option.is_some (static eff)

  let assign ?(local=false) target v eff =
    let v = Theory.Var.forget v in
    match static eff with
    | Some _ when local || not (is_machine_var target v) ->
      Env.set v (res eff) >>= fun () ->
      purify eff
    | _ ->
      Env.del v >>= fun () ->
      full [!!eff; data [v := !(res eff)]] !!(res eff)

  let reify ppf program defn target name args =
    let word = Theory.Target.bits target in
    let {prog; places} = program in
    let var ?t n = make_var ?t places target n in
    let rec eval : ast -> unit Theory.Effect.t KB.t = function
      | {data=Int {data={exp=x; typ=Type m}}} -> bigint x m
      | {data=Int {data={exp=x}}} -> bigint x word
      | {data=Var {data={exp=n; typ=Type t}}} -> lookup@@var ~t n
      | {data=Var {data={exp=n}}} -> lookup@@var n
      | {data=Sym {data=s}} -> sym (KB.Name.unqualified s)
      | {data=Ite (cnd,yes,nay)} -> ite cnd yes nay
      | {data=Let ({data={exp=n}},x,y)} -> let_ n x y
      | {data=App (Dynamic name,args)} -> app name args
      | {data=Seq xs} -> seq_ xs
      | {data=Set ({data={exp=n; typ=Type t}},x)} -> set_ (var ~t n) x
      | {data=Set ({data={exp=n}},x)} -> set_ (var n) x
      | {data=Rep (cnd,body)} -> rep cnd body
      | {data=Msg (fmt,args)} -> msg fmt args
      | {data=Err msg} -> err msg
      | _ -> undefined
    and ite cnd yes nay =
      let* cnd = eval cnd in
      match static cnd with
      | Some cnd ->
        if Bitvec.(equal cnd zero)
        then eval nay
        else eval yes
      | None ->
        coerce_bool (res cnd) @@ fun cres ->
        Theory.Var.fresh Theory.Bool.t >>= fun c ->
        let* yes = eval yes in
        let* nay = eval nay in
        full [
          !!cnd;
          data [c := !cres];
          CT.branch (CT.var c) !yes !nay;
        ] @@
        CT.ite (CT.var c) !(res yes) !(res nay)
    and rep cnd body =
      let* r = eval cnd in
      match static r with
      | Some x ->
        if Bitvec.(equal x zero)
        then !!r
        else
          eval body >>= fun _ ->
          rep cnd body
      | None ->
        let* body = eval body in
        let* head = fresh and* loop = fresh and* tail = fresh in
        coerce_bool (res r) @@ fun cres ->
        full [
          blk head [ctrl [CT.goto tail]];
          blk loop [!!body];
          blk tail [!!r; ctrl [
              CT.branch !cres (CT.goto head) skip
            ]]
        ] !!cres
    and call ?(toplevel=false) name xs =
      match Map.find program.names name with
      | None when toplevel -> !!Insn.empty
      | Some Prim | None -> call_primitive name xs
      | Some Defn -> call_defn name xs
      | Some Meth -> call_meth name xs
      | Some Data -> unresolved name Uncallable
    and call_defn name xs =
      match Resolve.defun check_arg prog Key.func name xs with
      | Some (Ok (fn,_)) when is_external fn ->
        sym (Def.name fn) >>= fun dst ->
        prim "invoke-subroutine" (res dst::xs)
      | Some (Ok (fn,bs)) ->
        Env.set_args word bs >>= fun bs ->
        Scope.clear >>= fun scope ->
        eval (Def.Func.body fn) >>= fun eff ->
        Scope.restore scope >>= fun () ->
        Env.del_args bs >>= fun () ->
        !!eff
      | Some (Error problem) ->
        unresolved name (Resolution problem)
      | None -> unresolved name (Unexpected Defn)
    and call_meth name xs =
      match Resolve.meth check_arg prog Key.meth name xs with
      | Some (Error problem) -> unresolved name (Resolution problem)
      | Some (Ok mets) ->
        KB.List.fold mets ~init:empty ~f:(fun effects (meth,bs) ->
            Env.set_args word bs >>= fun bs ->
            Scope.clear >>= fun scope ->
            eval (Def.Meth.body meth) >>= fun eff ->
            Scope.restore scope >>= fun () ->
            Env.del_args bs >>| fun () ->
            KB.Value.merge effects eff)
      | None -> unresolved name (Unexpected Meth)
    and call_primitive name xs =
      match Resolve.semantics prog Key.semantics name () with
      | Some Ok (sema,()) ->
        Def.Sema.apply sema defn xs >>= reify_sym
      | Some (Error problem) -> unresolved name (Resolution problem)
      | None -> unresolved name (Unexpected Prim)
    and app name xs =
      map xs >>= fun (aeff,xs) ->
      call name xs >>= fun peff ->
      full [!!aeff; !!peff] !!(res peff)
    and map args =
      seq [] >>= fun eff ->
      KB.List.fold args ~init:(eff,[]) ~f:(fun (eff,args) arg ->
          let* eff' = eval arg in
          let+ eff = seq [!!eff; !!eff'] in
          (eff,forget (res eff')::args)) >>| fun (eff,args) ->
      eff, List.rev args
    and seq_ xs =
      pure nil >>= fun init ->
      KB.List.fold ~init xs ~f:(fun eff x  ->
          let* eff' = eval x in
          full [!!eff; !!eff'] !!(res eff'))
    and msg fmt args =
      map args >>= fun (aeff,args) ->
      List.iter fmt ~f:(function
          | Lit s -> Format.printf "%s" s
          | Pos n -> match List.nth args n with
            | None -> failwithf "bad positional %d" n ()
            | Some v -> match KB.Value.get static_slot v with
              | Some v -> Format.printf "%a" Bitvec.pp v
              | None -> Format.printf "@[<hv>%a@]" KB.Value.pp v);
      Format.fprintf ppf "@\n";
      !!aeff
    and err msg = KB.fail (User_error msg)
    and lookup v =
      Scope.lookup v >>= function
      | Some v -> lookup v
      | None ->
        Env.lookup v >>= function
        | Some v -> pure !!v
        | None -> match lookup_parameter prog v with
          | Some def -> eval def >>= assign target v
          | None -> pure@@CT.var v
    and set_ v x =
      Scope.lookup v >>= function
      | Some v -> eval x >>= assign target ~local:true v
      | None -> eval x >>= assign target v
    and let_ v x b =
      let* xeff = eval x in
      let s = Theory.Value.sort (res xeff) in
      let orig = Theory.Var.define s (KB.Name.to_string v) in
      if is_parameter prog orig
      then
        Env.set orig (res xeff) >>= fun () ->
        let* beff = eval b in
        Env.del orig >>= fun () ->
        full [!!beff] !!(res beff)
      else
        Scope.push orig >>= fun v ->
        let* aeff = assign ~local:true target v xeff in
        let* beff = eval b in
        Scope.pop orig >>= fun () ->
        full [
          !!aeff;
          !!beff;
        ] !!(res beff)
    and prim ?(package="core") name args =
      call (KB.Name.read ~package name) args in
    match args with
    | Some args ->
      call ~toplevel:true name args
    | None ->
      resolve prog Key.func name >>= function
      | Some fn ->
        eval (Def.Func.body fn)
      | None -> !!Insn.empty
end

module Unit = struct
  open KB.Syntax
  open KB.Let

  let slot = KB.Class.property Theory.Unit.cls "lisp-unit"
      ~package
      ~public:true @@ KB.Domain.optional "unit-name"
      ~inspect:sexp_of_string
      ~equal:equal_string


  let create ?(name="core") target : Theory.Unit.t KB.t =
    let* unit = KB.Symbol.intern ~package:"lisp" name Theory.Unit.cls in
    KB.sequence [
      KB.provide slot unit (Some name);
      KB.provide Theory.Unit.target unit target
    ] >>| fun () ->
    unit

  let is_lisp obj =
    KB.collect slot obj >>| Option.is_some

  let language = language
end

type KB.conflict += Illtyped_program of Program.Type.error list
type KB.conflict += Failed_primitive of KB.Name.t * string
type KB.conflict += Primitive_failed of string

let failp fmt =
  Format.kasprintf (fun msg ->
      KB.fail (Primitive_failed msg)) fmt

let primitive name defn args =
  let open KB.Syntax in
  KB.Object.scoped Theory.Program.cls @@ fun obj ->
  KB.sequence [
    KB.provide Property.name obj (Some name);
    KB.provide definition obj (Some defn);
    KB.provide Property.args obj (Some args);
  ] >>= fun () ->
  KB.catch (KB.collect Theory.Semantics.slot obj)
    (function Primitive_failed msg ->
       KB.fail (Failed_primitive (name,msg))
            | other -> KB.fail other)

let link_library target prog =
  let open KB.Let in
  Hashtbl.to_alist library |>
  KB.List.fold ~init:prog ~f:(fun prog (name,{types; docs; body; kind}) ->
      let types = types target in
      match kind with
      | `meth ->
        KB.return @@
        Program.add prog Program.Items.signal @@
        Def.Signal.create ~types ~docs (KB.Name.show name)
      | `defn ->
        match body with
        | None ->
          KB.return @@
          Program.add prog Program.Items.semantics @@
          Def.Sema.create ~docs ~types name (primitive name)
        | Some body ->
          let+ fn = body target in
          Program.add prog Program.Items.semantics @@
          Def.Sema.create ~docs ~types name fn)


let collect_names kind key prog =
  Program.fold prog key ~f:(fun ~package def names ->
      if Program.is_applicable prog def
      then
        let name = Def.name def in
        Map.set names ~key:(KB.Name.create ~package name) ~data:kind
      else names)
    ~init:(Map.empty (module KB.Name))

let merge_names names =
  List.reduce names ~f:(Map.merge_skewed
                          ~combine:(fun ~key:_ _ v -> v)) |>
  function None -> Map.empty (module KB.Name)
         | Some r -> r


let obtain_typed_program unit =
  let open KB.Syntax in
  let open KB.Let in
  KB.collect Theory.Unit.source unit >>= fun src ->
  KB.collect Theory.Unit.target unit >>= fun target ->
  match KB.Value.get typed src with
  | Some prog -> !!prog
  | None ->
    let* context = unit-->context in
    let input =
      let init = KB.Value.get program src in
      Program.with_context init @@
      Context.merge (Program.context init) context in
    let* prog =
      link_library target @@ Program.with_places input target in
    let tprog = Program.Type.infer prog in
    let prog = Program.Type.program tprog in
    let places = Program.fold prog Key.place
        ~f:(fun ~package place places ->
            let name = KB.Name.create ~package (Def.name place) in
            Map.set places ~key:name ~data:(Def.Place.location place))
        ~init:(Map.empty (module KB.Name)) in
    let names = merge_names  [
        collect_names Defn Key.func prog;
        collect_names Prim Key.semantics prog;
        collect_names Data Key.para prog;
        collect_names Data Key.const prog;
        collect_names Meth Key.meth prog;
      ] in
    let program = {prog; places; names} in
    match Program.Type.errors tprog with
    | [] ->
      let src = KB.Value.put typed src (Some program) in
      KB.provide Theory.Unit.source unit src >>| fun () ->
      program
    | errs -> KB.fail (Illtyped_program errs)


let typed_program unit =
  let open KB.Syntax in
  obtain_typed_program unit >>| fun {prog} -> prog


let provide_semantics ?(stdout=Format.std_formatter) () =
  let open KB.Syntax in
  KB.Rule.(begin
      declare "primus-lisp-semantics" |>
      require Property.name |>
      require Property.args |>
      require Theory.Label.unit |>
      require Theory.Unit.source |>
      require Theory.Unit.target |>
      require program |>
      provide Theory.Semantics.slot |>
      comment "reifies Primus Lisp definitions"
    end);
  let require p k = if p then k () else !!Insn.empty in
  KB.promise Theory.Semantics.slot @@ fun obj ->
  let* unit = obj-->?Theory.Label.unit in
  let* name = obj-->?Property.name in
  let* prog = obtain_typed_program unit in
  require (Map.mem prog.names name) @@ fun () ->
  let* args = obj-->Property.args in
  let* target = KB.collect Theory.Unit.target unit in
  let bits = Theory.Target.bits target in
  KB.Context.set State.var State.{
      binds = Map.empty (module Theory.Var.Top);
      scope = Map.empty (module Theory.Var.Top);
      arith = (module (Bitvec.Make(struct
                         let modulus = Bitvec.modulus bits
                       end)));
    } >>= fun () ->
  let* (module Core) = Theory.current in
  let open Prelude(Core) in
  let* res = reify stdout prog obj target name args in
  KB.collect Disasm_expert.Basic.Insn.slot obj >>| function
  | Some basic when Insn.(res <> empty) ->
    Insn.with_basic res basic
  | _ -> res

let provide_attributes () =
  let open KB.Syntax in
  let empty = Attribute.Set.empty in
  let (>>=?) x f = x >>= function
    | None -> !!empty
    | Some x -> f x in
  KB.promise Attribute.Set.slot @@ fun this ->
  KB.collect Theory.Label.unit this >>=? fun unit ->
  KB.collect Property.name this >>=? fun name ->
  obtain_typed_program unit >>= fun {prog} ->
  let package = KB.Name.package name
  and name = KB.Name.unqualified name in
  Program.in_package package prog @@ fun prog ->
  Program.get ~name prog Key.func |>
  List.fold ~init:(Ok empty) ~f:(fun attrs fn ->
      match attrs with
      | Error c -> Error c
      | Ok attrs ->
        KB.Value.join attrs (Def.attributes fn)) |> function
  | Ok attrs -> !!attrs
  | Error conflict -> KB.fail conflict

let enable ?stdout () =
  provide_semantics ?stdout ();
  provide_attributes ()

let static = static_slot

let () = KB.Conflict.register_printer @@ function
  | Unresolved_definition msg -> Option.some @@ sprintf "%s" msg
  | Property.Unequal_arity ->
    Some "The number of arguments is different"
  | User_error msg -> Some ("error: " ^ msg)
  | Illtyped_program errs ->
    let open Format in
    let msg = asprintf "%a"
        (pp_print_list
           ~pp_sep:pp_print_newline
           Program.Type.pp_error) errs in
    Some msg
  | _ -> None

include Property
