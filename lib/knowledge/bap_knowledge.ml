open Core
open Monads.Std
module Unix = Core_unix

type ('a,'b) eq = ('a,'b) Type_equal.t = T : ('a,'a) eq

module Order = struct
  type partial = LT | EQ | GT | NC [@@deriving sexp, equal]
  module type S = sig
    type t
    val order : t -> t -> partial
  end
end

type conflict = exn = ..

module Conflict = struct
  type t = conflict = ..
  let to_string = Stdlib.Printexc.to_string
  let pp ppf err = Format.fprintf ppf "%s" (to_string err)
  let register_printer = Stdlib.Printexc.register_printer
  let sexp_of_t err = Sexp.Atom (to_string err)
end

module type Id = sig
  type t [@@deriving sexp, hash]
  val zero : t
  val pp : Format.formatter -> t -> unit
  val of_string : string -> t
  include Comparable.S_binable with type t := t
  include Binable.S with type t := t
end

module Oid : sig
  include Id
  val zero : t
  val first : t
  val succ : t -> t

  val fits : int -> bool
  val of_int : int -> t
  val fits_int : t -> bool
  val to_int : t -> int
  val to_int63 : t -> Int63.t
  val incr : t ref -> unit
  module Tree : sig
    type key = t
    type 'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val find_exn : 'a t -> key -> 'a
    val find : 'a t -> key -> 'a option
    val max_elt : 'a t -> (key * 'a) option
    val min_elt : 'a t -> (key * 'a) option
    val mem : 'a t -> key -> bool
    val singleton : key -> 'a -> 'a t
    val set : 'a t -> key -> 'a -> 'a t
    val remove : 'a t -> key -> 'a t
    val update : 'a t -> key -> f:('a option -> 'a) -> 'a t
    val update_with : 'a t -> key -> has:('a -> 'a) -> nil:(unit -> 'a) -> 'a t
    val merge : 'a t -> 'a t -> f:(key -> 'a -> 'a -> 'a) -> 'a t
    val iter : 'a t -> f:(key -> 'a -> unit) -> unit
    val fold : 'a t -> init:'b -> f:(key -> 'a -> 'b -> 'b) -> 'b
    val keys : 'a t -> key list
    val elements : 'a t -> 'a list
    val to_list : 'a t -> (key * 'a) list
    val to_sequence : 'a t -> (key * 'a) Sequence.t
  end
end
= struct
  include Int63
  let first = one
  let is_null x = x = zero
  let to_int = to_int_trunc
  let to_int63 x = x
  let fits _ = true [@@inline]
  let fits_int _ = true [@@inline]
  let pp ppf x =
    Format.fprintf ppf "<%#0Lx>" (to_int64 x)

  module Tree = struct
    type key = t

    (* sets bit to zero and all lower bits to one *)
    let mask ~bit x =
      let m = one lsl to_int bit in
      (x lor (m-one)) land (lnot m)

    let (lsr) = shift_right_logical

    let clz v = of_int (clz v) [@@inline]

    let numbits v = of_int 63 - clz v [@@inline]

    let highest_bit x = numbits x - one
    let is_zero ~bit x = x land (one lsl to_int bit) = zero

    module Key = struct

      (*

        +-----------+-------------------------+
        | branching |        payload          |
        +-----------+-------------------------+
        62        57 56                       0

         Note, that we store the branching bit position,
         not the mask itself.

       *)
      type t = {key : key} [@@unboxed]
      let payload_size = 57
      let branching_size = 6

      let branching_mask = of_int64_exn (-144115188075855872L)  (* 0b1111110000....0 *)
      let payload_mask = of_int64_exn 144115188075855871L     (* 0b0000001111....1 *)

      let branching {key} =
        (key land branching_mask) lsr 57 [@@inline]

      let payload {key} = (key land payload_mask) [@@inline]

      let create ~branching ~payload = {
        key = branching lsl 57 lor payload
      }
      type order = NA | LB | RB


      let compare k k' =
        let x = payload k in
        let bit = branching k in
        let m = one lsl to_int bit in
        let y = (k' lor (m-one)) land (lnot m) in
        if x = y
        then if k' land m = zero then LB else RB
        else NA
      [@@inline]

      let equal {key=k1} {key=k2} = equal k1 k2 [@@inline]

      let pp ppf key =
        Format.fprintf ppf "%a:%a" pp (branching key) pp (payload key)
    end

    type +'a t =
      | Bin of Key.t * 'a t * 'a t
      | Tip of key * 'a
      | Nil


    let empty = Nil

    let[@inline] is_empty = function
      | Nil -> true
      | _ -> false


    let branching_bit a b = highest_bit (a lxor b)

    let rec find_exn t k = match t with
      | Nil -> raise Stdlib.Not_found
      | Tip (k', v) when k = k' -> v
      | Tip _ -> raise Stdlib.Not_found
      | Bin (k', l, r) -> match Key.compare k' k with
        | NA -> raise Stdlib.Not_found
        | LB -> find_exn l k
        | RB -> find_exn r k

    let find t k =
      try Some (find_exn t k)
      with Stdlib.Not_found -> None

    let mem k t =
      try ignore (find_exn k t); true
      with Stdlib.Not_found -> false

    let node payload branching l r = match l, r with
      | Nil, o | o, Nil -> o
      | _ -> Bin (Key.create ~branching ~payload, l, r)

    let of_key key l r = match l, r with
      | Nil, o | o, Nil -> o
      | _ -> Bin (key, l, r)

    let join t1 p1 t2 p2 =
      let switch = branching_bit p1 p2 in
      let prefix = mask p1 ~bit:switch in
      if is_zero p1 ~bit:switch
      then node prefix switch t1 t2
      else node prefix switch t2 t1

    let singleton k v = Tip (k, v)

    let rec update_with t k ~has ~nil = match t with
      | Nil -> Tip (k, nil ())
      | Tip (k', v') ->
        if k = k'
        then Tip (k, has v')
        else join t k' (Tip (k, nil ())) k
      | Bin (k', l, r) -> match Key.compare k' k with
        | NA -> join (Tip (k,nil ())) k t (Key.payload k')
        | LB -> Bin (k', update_with l k ~has ~nil, r)
        | RB -> Bin (k', l, update_with r k ~has ~nil)
    [@@specialise]

    let rec update t k ~f = match t with
      | Nil -> Tip (k, f None)
      | Tip (k', v') ->
        if k = k'
        then Tip (k, f (Some v'))
        else join t k' (Tip (k, f None)) k
      | Bin (k', l, r) -> match Key.compare k' k with
        | NA -> join (Tip (k,f None)) k t (Key.payload k')
        | LB -> Bin (k', update l k ~f, r)
        | RB -> Bin (k', l, update r k ~f)
    [@@specialise]

    let rec set t k v = match t with
      | Nil -> Tip (k, v)
      | Tip (k', _) ->
        if k = k'
        then Tip (k, v)
        else join t k' (Tip (k, v)) k
      | Bin (k', l, r) -> match Key.compare k' k with
        | NA -> join (Tip (k,v)) k t (Key.payload k')
        | LB -> Bin (k', set l k v, r)
        | RB -> Bin (k', l, set r k v)

    let rec remove t k = match t with
      | Nil -> Nil
      | Tip (k', _) -> if k = k' then Nil else t
      | Bin (k', l, r) -> match Key.compare k' k with
        | NA -> t
        | LB -> of_key k' (remove l k) r
        | RB -> of_key k' l (remove r k)

    let rec merge t1 t2 ~f = match t1, t2 with
      | Nil, t | t, Nil -> t
      | Tip (k, v1), t
      | t, Tip (k, v1) -> update t k ~f:(function
          | None -> v1
          | Some v2 -> f k v1 v2)
      | Bin (p1, l1, r1), Bin (p2, l2, r2) ->
        if Key.equal p1 p2
        then of_key p1 (merge l1 l2 ~f) (merge r1 r2 ~f)
        else
          let k1 = Key.payload p1 and k2 = Key.payload p2 in
          let b1 = Key.branching p1 and b2 = Key.branching p2 in
          match Key.compare p1 k2 with
          | NA -> join t1 k1 t2 k2
          | RB -> if is_zero ~bit:b1 k2
            then Bin (p1,merge l1 t2 ~f,r1)
            else Bin (p1,l1,merge r1 t2 ~f)
          | LB -> if is_zero ~bit:b2 k1
            then Bin (p2,merge t1 l2 ~f,r2)
            else Bin (p2,l2,merge t1 r2 ~f)
    [@@specialise]

    let rec iter t ~f = match t with
      | Nil -> ()
      | Tip (k, v) -> f k v
      | Bin (_, l, r) -> iter l ~f; iter r ~f
    [@@specialise]

    let rec fold t ~init ~f = match t with
      | Nil -> init
      | Tip (k, v) -> f k v init
      | Bin (_, l, r) ->
        fold r ~f ~init:(fold l ~init ~f)
    [@@specialise]

    let rec max_elt = function
      | Nil -> None
      | Tip (k,v) -> Some (k,v)
      | Bin (_,_,r) -> max_elt r

    let rec min_elt = function
      | Nil -> None
      | Tip (k,v) -> Some (k,v)
      | Bin (_,_,r) -> min_elt r

    let elements = fold ~f:(fun _ x xs -> x::xs) ~init:[]
    let keys = fold ~f:(fun x _ xs -> x::xs) ~init:[]

    let to_list tree =
      let rec list acc = function
        | Nil -> acc
        | Tip (k,x) -> (k,x) :: acc
        | Bin (_,l,r) -> list (list acc l) r in
      list [] tree

    let to_sequence tree =
      let open Sequence.Generator in
      let rec seq = function
        | Nil -> return ()
        | Tip (k,x) -> yield (k,x)
        | Bin (_,l,r) -> seq l >>= fun () -> seq r in
      run (seq tree)
  end
end

module Pid = Oid
let user_package = "user"
let keyword_package = "keyword"



type fullname = {
  package : string;
  name : string;
} [@@deriving bin_io, equal, compare, sexp]


module Name : sig
  type t [@@deriving bin_io, compare, sexp]
  val create : ?package:string -> string -> t
  val read : ?package:string -> string -> t
  val show : t -> string
  val unqualified : t -> string
  val package : t -> string
  val str : unit -> t -> string
  val hash : t -> int

  val full : t -> fullname

  module Full : sig
    type t = fullname
    val create : ?package:string -> string -> t
    val read : ?package:string -> string -> t
    val short : t -> string
    val package : t -> string
    val to_string : t -> string
    include Base.Comparable.S with type t := t
  end

  val normalize_name : [`Literal | `Reading] -> package:string ->
    string -> string
  val normalize_package : [`Literal | `Reading] -> string -> string

  val find_separator : string -> int option
  include Base.Comparable.S with type t := t
  include Binable.S with type t := t
  include Stringable.S with type t := t
  include Pretty_printer.S with type t := t
end = struct
  let full {package; name} =
    if String.(package = keyword_package || package = user_package)
    then name
    else package ^ ":" ^ name

  let separator = ':'
  let escape_char = '\\'
  let escapeworthy = [separator]

  let is_escaped s = String.Escaping.is_char_escaped s ~escape_char

  let find_separator s =
    if String.is_empty s then None
    else String.Escaping.index s ~escape_char separator

  let is_separator_unescaped s p c =
    Char.equal separator c && not (is_escaped s p)

  let unescaped_exists_so_escape ?(skip_pos=(-1)) s =
    let buf = Buffer.create (String.length s + 1) in
    Stdlib.StringLabels.iteri s ~f:(fun p c ->
        if p <> skip_pos && is_separator_unescaped s p c
        then Buffer.add_char buf escape_char;
        Buffer.add_char buf c);
    Buffer.contents buf

  let has_unescaped ?pos s =
    Option.is_some @@
    String.lfindi ?pos s ~f:(fun p c ->
        is_separator_unescaped s p c)

  let escape_all_unescaped ?(is_keyword=false) s =
    match s with
    | "" -> s
    | ":" -> if is_keyword then s else "\\:"
    | _ ->
      let pos = if is_keyword then 1 else 0 in
      if has_unescaped ~pos s
      then unescaped_exists_so_escape ~skip_pos:pos s
      else s

  let escape_all_literally =
    unstage @@
    String.Escaping.escape ~escapeworthy ~escape_char

  let unescape =
    unstage @@
    String.Escaping.unescape ~escape_char

  (* invariant, keywords are always prefixed with [:] *)
  let normalize_name input ~package name = match input with
    | `Literal ->
      if String.equal package keyword_package
      then ":" ^ escape_all_literally name
      else escape_all_literally name
    | `Reading ->
      let escape = escape_all_unescaped in
      if String.equal package keyword_package
      then
        if not (String.is_prefix ~prefix:":" name)
        then ":" ^ escape name
        else ":" ^ escape @@ String.subo ~pos:1 name
      else escape name

  let normalize_package input package =
    let package = if String.is_empty package
      then user_package
      else package in
    match input with
    | `Literal -> escape_all_literally package
    | `Reading -> escape_all_unescaped package


  module Full = struct
    type t = fullname
    let create ?(package=user_package) name =
      let package = normalize_package `Literal package in
      let name = normalize_name `Literal ~package name in
      {package; name}
    let short x = unescape @@ x.name
    let package x = unescape @@ x.package
    let to_string name = full name

    let read ?(package=user_package) s : t =
      let package = normalize_package `Literal package in
      let escape = escape_all_unescaped in
      match find_separator s with
      | None ->
        let name = normalize_name `Reading ~package s in
        {package; name}
      | Some 0 ->
        let package = keyword_package
        and name = escape ~is_keyword:true s in
        {package; name}
      | Some len ->
        let package = escape (String.sub s ~pos:0 ~len) in
        let name = normalize_name `Reading ~package @@
          String.subo s ~pos:(len+1) in
        {package; name}

    include Base.Comparable.Make(struct
        type t = fullname [@@deriving compare, sexp]
      end)
  end

  module Id : sig
    type t [@@deriving bin_io, compare, sexp]
    val intern : fullname -> t
    val fullname : t -> fullname
    val hash : t -> int
  end = struct

    let registry = Hashtbl.create (module Int63)

    (* using FNV-1a algorithm *)
    let hash_name =
      let open Int63 in
      let init = of_int64_exn 0xCBF29CE484222325L in
      let m = of_int64_exn 0x100000001B3L in
      let hash init = String.fold ~init ~f:(fun h c ->
          (h lxor of_int (Char.to_int c)) * m) in
      fun {package; name} ->
        hash (hash init package) name

    let intern name =
      let id = hash_name name in
      match Hashtbl.find registry id with
      | None -> Hashtbl.add_exn registry ~key:id ~data:name; id
      | Some name' ->
        if equal_fullname name name'
        then id
        else invalid_argf "Names %S and %S have the same hash value, \
                           Change one of them."
            (full name) (full name') ()

    let fullname id = match Hashtbl.find registry id with
      | Some name -> name
      | None -> {
          package="id";
          name=sprintf "%Lx" (Int63.to_int64 id)
        }

    include Int63
    let sexp_of_t id =
      Sexp.Atom (Full.to_string (fullname id))
    let t_of_sexp = function
      | Sexp.Atom str -> intern (Full.read str)
      | _ -> invalid_arg "KB.Name.sexp_of_t: expects an atom"

  end
  type t = Id.t [@@deriving bin_io, compare, sexp]


  let full = Id.fullname

  let create ?package name =
    Id.intern @@ Full.create ?package name

  let keyword = create ~package:keyword_package

  let read ?package name = Id.intern @@ Full.read ?package name

  let package t = Full.package Id.(fullname t)
  let short t = Full.short Id.(fullname t)
  let unqualified t = short t
  let to_string t = Full.to_string Id.(fullname t)
  let show t = to_string t
  let of_string s = read s

  let str () s = to_string s
  let pp ppf x = Format.fprintf ppf "%s" (show x)

  let hash = Id.hash

  include Base.Comparable.Make(struct
      type t = Id.t [@@deriving bin_io, compare, sexp]
    end)
end


module Agent : sig
  type t
  type id
  type reliability
  type signs

  val register :
    ?desc:string ->
    ?package:string ->
    ?reliability:reliability -> string -> t

  val registry : unit -> id list

  val authorative : reliability
  val reliable    : reliability
  val trustworthy : reliability
  val doubtful    : reliability
  val unreliable  : reliability

  val name : id -> Name.t
  val desc : id -> string
  val reliability : id -> reliability

  val set_reliability : id -> reliability -> unit

  val pp : Format.formatter -> t -> unit
  val pp_id : Format.formatter -> id -> unit
  val pp_reliability : Format.formatter -> reliability -> unit

  (* the private interface *)

  val weight : t -> int
  val id : t -> id

  include Base.Comparable.S with type t := t
end = struct
  module Id = String
  type t = Id.t
  type agent = Id.t
  type id = Id.t
  type reliability = A | B | C | D | E [@@deriving sexp]
  type info = {
    name : Name.t;
    desc : string;
    rcls : reliability;
  }
  type signs = Set.M(String).t

  let agents : (agent,info) Hashtbl.t = Hashtbl.create (module String)

  let authorative = A
  let reliable = B
  let trustworthy = C
  let doubtful = D
  let unreliable = E

  let weight = function
    | A -> 16
    | B -> 8
    | C -> 4
    | D -> 2
    | E -> 1

  let id x = x

  let register
      ?(desc="no description provided")
      ?package
      ?(reliability=trustworthy) name =
    let name = Name.create ?package name in
    let agent = Stdlib.Digest.string (Name.show name) in
    if Hashtbl.mem agents agent then
      failwithf "An agent with name `%a' already exists, \
                 please choose another name" Name.str name ();
    Hashtbl.add_exn agents ~key:agent ~data:{
      desc; name; rcls = reliability;
    };
    agent

  let registry () = Hashtbl.keys agents

  let info agent = Hashtbl.find_exn agents agent
  let name agent = (info agent).name
  let desc agent = (info agent).desc
  let reliability agent = (info agent).rcls
  let weight agent = weight (reliability agent)

  let set_reliability agent rcls =
    Hashtbl.update agents agent ~f:(function
        | None -> assert false
        | Some agent -> {agent with rcls})

  let pp ppf agent = Name.pp ppf (name agent)

  let pp_reliability ppf r =
    Sexp.pp ppf (sexp_of_reliability r)

  let pp_id ppf agent =
    let {name; desc; rcls} = info agent in
    Format.fprintf ppf "Class %a %a - %s"
      pp_reliability rcls Name.pp name desc

  include (String : Base.Comparable.S with type t := t)
end

module Opinions : sig
  type 'a t

  val empty : equal:('a -> 'a -> bool) -> 'a -> 'a t

  val inspect : ('a -> Sexp.t) -> 'a t -> Sexp.t

  val add : Agent.t -> 'a -> 'a t -> 'a t
  val of_list : equal:('a -> 'a -> bool) -> 'a -> (Agent.t,'a) List.Assoc.t -> 'a t
  val choice : 'a t -> 'a

  val compare_votes : 'a t -> 'a t -> int
  val join : 'a t -> 'a t -> 'a t
end = struct
  type 'a opinion = {
    opinion : 'a;
    votes   : Set.M(Agent).t;
  }

  type 'a t = {
    opinions : 'a opinion list;
    equal : 'a -> 'a -> bool;
    empty : 'a;
  }

  let empty ~equal empty = {opinions=[]; equal; empty}

  let inspect sexp_of_opinion {opinions} =
    Sexp.List (List.rev_map opinions ~f:(fun {opinion} ->
        sexp_of_opinion opinion))


  let add_opinion op ({opinions; equal} as ops) =
    let casted,opinions =
      List.fold opinions ~init:(false,[])
        ~f:(fun (casted,opinions) ({opinion; votes} as elt) ->
            if not casted && equal opinion op.opinion
            then true, {
                opinion; votes = Set.union votes op.votes;
              } :: opinions
            else casted,elt :: opinions) in
    if casted
    then {ops with opinions}
    else {
      ops with opinions = op :: opinions
    }

  let add agent opinion ({empty; equal} as ops) =
    if equal opinion empty then ops
    else
      add_opinion {
        opinion;
        votes = Set.singleton (module Agent) agent;
      } ops

  let join x y =
    List.fold y.opinions ~init:x ~f:(fun ops op -> add_opinion op ops)

  let votes_sum =
    Set.fold ~init:0 ~f:(fun sum agent -> sum + Agent.weight agent)

  let count_votes {opinions} =
    List.fold opinions ~init:0 ~f:(fun sum {votes} ->
        sum + votes_sum votes)

  let compare_votes x y =
    compare (count_votes x) (count_votes y)

  let of_list ~equal bot =
    let init = empty ~equal bot in
    List.fold ~init ~f:(fun opts (agent,data) ->
        add agent data opts)

  let compare x y =
    let w1 = votes_sum x.votes
    and w2 = votes_sum y.votes in
    match Int.compare w1 w2 with
    | 0 -> Set.compare_direct x.votes y.votes
    | n -> n

  let choice {opinions; empty} =
    List.max_elt opinions ~compare |> function
    | Some {opinion} -> opinion
    | None -> empty

end

module Domain = struct
  type 'a t = {
    inspect : 'a -> Sexp.t;
    empty : 'a;
    order : 'a -> 'a -> Order.partial;
    join : 'a -> 'a -> ('a,conflict) result;
    name : string;
  }

  let inspect d = d.inspect
  let empty d = d.empty
  let order d = d.order
  let join d = d.join
  let name d = d.name

  let is_empty {empty; order} x = Order.equal_partial (order empty x) EQ

  type conflict += Join : string * ('a -> Sexp.t) * 'a * 'a -> conflict

  let () = Conflict.register_printer @@ function
    | Join (dom,inspect, x, y) -> Option.some @@
      Format.asprintf
        "Domain %s doesn't have a join for values %a and %a"
        dom Sexp.pp_hum (inspect x) Sexp.pp_hum (inspect y)
    | _ -> None

  let make_join name inspect order x y =
    match order x y with
    | Order.GT -> Ok x
    | EQ | LT -> Ok y
    | NC -> Error (Join (name, inspect, x, y))

  let define ?(inspect=sexp_of_opaque) ?join ~empty ~order name = {
    inspect; empty; order; name;
    join = match join with
      | Some f -> f
      | None -> (make_join name inspect order)
  }

  let partial_of_total order x y : Order.partial = match order x y with
    | 0 -> EQ
    | 1 -> GT
    | _ -> LT

  let total ?inspect ?join ~empty ~order name =
    define ?inspect ?join ~empty name ~order:(partial_of_total order)

  let flat ?inspect ?join ~empty ~equal name =
    define ?inspect ?join ~empty name ~order:(fun x y ->
        match equal empty x, equal empty y with
        | true,true -> EQ
        | true,false -> LT
        | false,true -> GT
        | false,false -> if equal x y then EQ else NC)

  let powerset (type t o)
      (module S : Base.Comparator.S with type t = t
                                and type comparator_witness = o)
      ?(inspect=S.comparator.sexp_of_t) name =
    let empty = Set.empty (module S) in
    let order x y : Order.partial =
      if Set.equal x y then EQ else
      if Set.is_subset x ~of_:y then LT else
      if Set.is_subset y ~of_:x then GT else NC in
    let join x y = Ok (Set.union x y) in
    let module Inspectable = struct
      include S
      let sexp_of_t = inspect
    end in
    let inspect = [%sexp_of: Base.Set.M(Inspectable).t] in
    define ~inspect ~empty ~order ~join name

  let opinions ?(inspect=sexp_of_opaque) ~empty ~equal name =
    let empty = Opinions.empty ~equal empty in
    let order = partial_of_total (Opinions.compare_votes) in
    let inspect = Opinions.inspect inspect in
    define ~inspect ~empty ~order name

  let mapping (type k o d)
      (module K : Base.Comparator.S with type t = k
                                and type comparator_witness = o)
      ?(inspect=sexp_of_opaque)
      ?join
      ~equal
      name =
    let empty = Map.empty (module K) in
    let join = match join with
      | Some join -> join
      | None -> fun x y ->
        if equal x y then Ok y else Error (Join (name, inspect, x, y)) in
    let join x y =
      let module Join = struct exception Conflict of conflict end in
      try Result.return @@ Map.merge x y ~f:(fun ~key:_ -> function
          | `Left v | `Right v -> Some v
          | `Both (x,y) -> match join x y with
            | Error conflict -> raise @@ Join.Conflict conflict
            | Ok z -> Some z)
      with Join.Conflict err -> Error err in
    let inspect xs =
      Sexp.List (Map.keys xs |> List.map ~f:K.comparator.sexp_of_t) in
    let order x y =
      Map.symmetric_diff x y ~data_equal:equal |>
      Sequence.fold ~init:(0,0,0) ~f:(fun (l,m,r) -> function
          | (_,`Left _)     -> (l+1,m,r)
          | (_,`Right _)    -> (l,m,r+1)
          | (_, `Unequal _) -> (l,m+1,r)) |> function
      | 0,0,0 -> Order.EQ
      | 0,0,_ -> LT
      | _,0,0 -> GT
      | _,_,_ -> NC in
    define ~inspect ~join ~empty ~order name

  let optional ?(inspect=sexp_of_opaque) ?join ~equal name =
    let join_data = match join with
      | Some join -> join
      | None -> fun x y ->
        if equal x y then Ok y
        else Error (Join (name, inspect, x, y)) in
    let inspect = sexp_of_option inspect in
    let join x y = match x,y with
      | None,x | x,None -> Ok x
      | Some x, Some y -> match join_data x y with
        | Ok x -> Ok (Some x)
        | Error err -> Error err in
    flat ~inspect ~join ~empty:None ~equal:(Option.equal equal) name

  let string = define "string" ~empty:""
      ~inspect:sexp_of_string ~order:(fun x y ->
          match String.is_empty x, String.is_empty y with
          | true, true -> EQ
          | true,false -> GT
          | false,true -> LT
          | false,false -> partial_of_total String.compare x y)

  let bool = optional ~inspect:sexp_of_bool ~equal:Bool.equal "bool"
end

module Persistent = struct
  type 'a t =
    | String : string t
    | Define : {
        of_string : string -> 'a;
        to_string : 'a -> string;
      } -> 'a t
    | Derive : {
        of_persistent : 'b -> 'a;
        to_persistent : 'a -> 'b;
        persistent : 'b t;
      } -> 'a t


  let string = String

  let define ~to_string ~of_string = Define {
      to_string;
      of_string;
    }

  let derive ~to_persistent ~of_persistent persistent = Derive {
      to_persistent;
      of_persistent;
      persistent;
    }

  let of_binable
    : type a. (module Binable.S with type t = a) -> a t =
    fun r -> Define {
        to_string = Binable.to_string r;
        of_string = Binable.of_string r
      }

  let rec to_string
    : type a. a t -> a -> string =
    fun p x -> match p with
      | String -> x
      | Define {to_string} -> to_string x
      | Derive {to_persistent; persistent} ->
        to_string persistent (to_persistent x)

  let rec of_string
    : type a. a t -> string -> a =
    fun p s -> match p with
      | String -> s
      | Define {of_string} -> of_string s
      | Derive {of_persistent; persistent} ->
        of_persistent (of_string persistent s)



  module Chunk = struct
    (* bin_io will pack len+data, and restore it correspondingly *)
    type t = {data : string} [@@deriving bin_io]
  end

  module KV = struct
    type t = {key : string; data : string}
    [@@deriving bin_io]
  end

  module Chunks = struct
    type t = Chunk.t list [@@deriving bin_io]
  end
  module KVS = struct
    type t = KV.t list [@@deriving bin_io]
  end

  let chunks = of_binable (module Chunks)
  let kvs = of_binable (module KVS)

  let list p = derive chunks
      ~to_persistent:(List.rev_map ~f:(fun x ->
          {Chunk.data = to_string p x}))
      ~of_persistent:(List.rev_map ~f:(fun {Chunk.data} ->
          of_string p data))

  let array p = derive chunks
      ~to_persistent:(Array.fold ~init:[] ~f:(fun xs x ->
          {Chunk.data = to_string p x} :: xs))
      ~of_persistent:(Array.of_list_rev_map ~f:(fun {Chunk.data} ->
          of_string p data))

  let sequence p = derive chunks
      ~to_persistent:(fun xs ->
          Sequence.to_list_rev @@
          Sequence.map xs ~f:(fun x ->
              {Chunk.data = to_string p x}))
      ~of_persistent:(fun xs ->
          Sequence.of_list @@
          List.rev_map xs ~f:(fun {Chunk.data} ->
              of_string p data))

  let set c p = derive (list p)
      ~to_persistent:Set.to_list
      ~of_persistent:(Set.of_list c)

  let map c pk pd = derive kvs
      ~to_persistent:(Map.fold ~init:[] ~f:(fun ~key ~data xs -> {
            KV.key = to_string pk key;
            KV.data = to_string pd data
          } :: xs))
      ~of_persistent:(List.fold ~init:(Map.empty c)
                        ~f: (fun xs {KV.key;data} ->
                            let key = of_string pk key
                            and data = of_string pd data in
                            Map.add_exn xs ~key ~data))

  let name = of_binable (module Name)
end


type 'a obj = Oid.t


module Registry = struct
  type info = {
    desc : string option;
  }

  type 'a rule = {
    name : Name.t;
    provides : 'a;
    requires : Name.t list;
    parameters : string list list;
    comment : string;
  }
  type unfinished = Unifinished
  type finished = Name.t
  type def = unfinished rule
  type doc = finished rule

  let sexp_of_rule {name} = Name.sexp_of_t name

  module Rule = struct
    type t = finished rule
    let hash {provides=name} = Name.hash name
    let sexp_of_t = sexp_of_rule
    include Base.Comparable.Inherit(Name)(struct
        type t = finished rule
        let component {name} = name
        let sexp_of_t = sexp_of_rule
      end)
  end

  let public = Hashtbl.create (module Name)
  let classes = Hashtbl.create (module String)
  let slots = Hashtbl.create (module String)
  let rules = Hash_set.create (module Rule)

  let is_present ~package namespace name =
    match Hashtbl.find namespace package with
    | None -> false
    | Some names -> Map.mem names name

  let register kind namespace ?desc ?(package=user_package) name =
    if is_present ~package namespace name
    then failwithf
        "Failed to declare a new %s, there is already a %s \
         named `%s' in package `%s'" kind kind name package ();
    let info = {desc} in
    Hashtbl.update namespace package ~f:(function
        | None -> Map.singleton (module String) name info
        | Some names -> Map.add_exn names ~key:name ~data:info);
    Name.create ~package name

  let start_rule ?package name = {
    name = Name.create ?package name;
    provides = Unifinished;
    requires = [];
    parameters = [];
    comment = ""
  }

  let rule_require name rule = {
    rule with requires = name :: rule.requires;
  }

  let rule_provide name rule = {
    rule with provides = name;
  }

  let rule_dynamic params rule = {
    rule with parameters = params :: rule.parameters;
  }

  let rule_comment comment rule =
    Hash_set.add rules {
      rule with comment
    }

  let add_class = register "class" classes
  let add_slot  = register "property" slots

  let is_public cls = Hashtbl.mem public cls

  let public_class cls =
    Hashtbl.add_exn public ~key:cls ~data:[]

  let update_class ~cls ~slot =
    if is_public cls
    then Hashtbl.add_multi public ~key:cls ~data:slot

  let find namespace name =
    let names = Hashtbl.find_exn namespace (Name.package name) in
    Map.find_exn names (Name.unqualified name)
end

module Documentation = struct
  module type Element = sig
    type t
    val name : t -> Name.t
    val desc : t -> string
  end

  let agents = Agent.registry

  module Agent = struct
    type t = Agent.id
    let of_agent = Agent.id
    let name = Agent.name
    let desc = Agent.desc
  end

  module Pair = struct
    type t = Name.t * Registry.info
    let name = fst
    let desc (_,{Registry.desc}) = match desc with
      | None -> ""
      | Some d -> d
  end
  module Class = Pair
  module Property = Pair

  module Rule = struct
    open Registry
    type t = Rule.t
    let name t = t.name
    let desc r = r.comment
    let property name = name, Registry.(find slots) name
    let provides r = property r.provides
    let requires r = List.map ~f:property r.requires
    let parameters r = r.parameters

    let refmt input =
      let max_column = 70 in
      let buffer = Buffer.create 64 in
      Buffer.add_string buffer "-- ";
      let column = ref 3 in
      let prev = ref ' ' in
      let in_white () = Char.(!prev = ' ') in
      let push c =
        if !column >= max_column && in_white () then begin
          Buffer.add_string buffer "\n-- ";
          column := 4;
        end;
        Buffer.add_char buffer c;
        if Char.is_whitespace c
        then prev := ' '
        else prev := c;
        incr column; in
      let skip = () in
      String.iter input ~f:(fun c ->
          if Char.is_whitespace c then
            if in_white () then skip else push ' '
          else push c);
      Buffer.contents buffer

    let pp_parameters ppf = function
      | [] -> ()
      | ps ->
        List.iter ps ~f:(fun ps ->
            let pp_sep ppf () = Format.fprintf ppf ", " in
            Format.fprintf ppf "(%a)"
              Format.(pp_print_list ~pp_sep pp_print_string) ps)

    let pp ppf {parameters; provides; requires; name; comment} =
      if String.(comment <> "") then
        Format.fprintf ppf "%s@\n" (refmt comment);
      Format.fprintf ppf "@[<v2>%a%a ::=@\n"
        Name.pp name pp_parameters parameters;
      let max_len = ref (String.length (Name.to_string provides)) in
      List.iter requires ~f:(fun name ->
          let len = String.length (Name.to_string name) in
          max_len := Int.max len !max_len;
          Format.fprintf ppf "%a@\n" Name.pp name;);
      let sep = String.make !max_len '-' in
      Format.fprintf ppf "%s@\n%a@]@\n"
        sep Name.pp provides
  end

  let classes () =
    Hashtbl.to_alist Registry.public |>
    List.map ~f:(fun (cls,slots) ->
        (cls,Registry.(find classes) cls),
        List.map slots ~f:(fun slot ->
            slot,
            Registry.(find slots) slot))

  let rules () =
    Hash_set.to_list Registry.rules
end

module Class = struct
  type +'s info = {
    name : Name.t;
    sort : 's;
  }
  let id {name} = name

  type (+'a,+'s) t = 's info


  let newclass ?(public=false) ?desc ?package name sort =
    let name = Registry.add_class ?desc ?package name in
    if public then Registry.public_class name;
    {name; sort}

  let declare
    : ?public:bool -> ?desc:string -> ?package:string -> string -> 's -> ('k,'s) t =
    fun ?public ?desc ?package name data ->
    newclass ?public ?desc ?package name data

  let refine {name} sort = {name; sort}

  let same x y = Name.equal x.name y.name

  let equal : type a b. (a,_) t -> (b,_) t -> (a obj,b obj) Type_equal.t option =
    fun x y -> Option.some_if (same x y) Type_equal.T

  let assert_equal x y = match equal x y with
    | Some t -> t
    | None ->
      failwithf "assert_equal: wrong assertion, classes of %s and %s \
                 are different"
        (Name.to_string x.name)
        (Name.to_string y.name)
        ()



  let sort = fun {sort} -> sort
  let name {name} = name
end

module Dict = struct
  module Key = struct
    module Uid = Int
    let last_id = ref 0

    type 'a witness = ..

    module type Witness = sig
      type t
      type _ witness += Id : t witness
    end

    type 'a typeid = (module Witness with type t = 'a)

    type 'a t = {
      ord : Uid.t;
      key : 'a typeid;
      name : Name.t;
      show : 'a -> Sexp.t;
    }

    let newtype (type a) () : a typeid =
      let module Type = struct
        type t = a
        type _ witness += Id : t witness
      end in
      (module Type)


    let create ~name show =
      let key = newtype () in
      incr last_id;
      {key; ord = !last_id; name; show}

    let uid {ord} = ord [@@inline]
    let compare k1 k2 =
      let k1 = uid k1 and k2 = uid k2 in
      (Uid.compare [@inlined]) k1 k2
    [@@inline]

    let name x = x.name
    let to_sexp x = x.show
    let equal x y = Int.equal x.ord y.ord [@@inline]

    let same (type a b) x y : (a,b) Type_equal.t =
      if equal x y then
        let module X = (val x.key : Witness with type t = a) in
        let module Y = (val y.key : Witness with type t = b) in
        match X.Id with
        | Y.Id -> Type_equal.T
        | _ -> failwith "broken type equality"
      else failwith "types are not equal"

    let (<) x y = uid x < uid y [@@inline]
    let (>) x y = uid x > uid y [@@inline]
    let (=) x y = uid x = uid y [@@inline]
    let (<>) x y = uid x <> uid y [@@inline]


    (** Allen's Interval Algebra

        The Allen's Interval Algebra [1,2] describes 13 possible
        relations between two intervals. See also [3] for the nice
        visualizations and an available description.

        [1]: https://doi.org/10.1145/182.358434
        [2]: https://doi.org/10.1111/j.1467-8640.1989.tb00329.x
        [3]: https://www.thomasalspaugh.org/pub/fnd/allen.html
    *)
    module Interval = struct
      type order =
        | Before
        | Meets
        | Overlaps
        | Finished
        | Contains
        | Starts
        | Equals
        | Started
        | During
        | Finishes
        | Overlapped
        | Met
        | After

      let invert f a b c d = f c d a b [@@inline]

      let meets _ b c _ = b = c [@@inline]
      let met a b c d = invert meets a b c d [@@inline] [@@specialise]
      let before _ b c _ = b < c [@@inline]
      let after a b c d = invert before a b c d [@@inline] [@@specialise]
      let overlaps a b c d = a < c && b < d && b > c [@@inline]
      let overlapped a b c d = invert overlaps a b c d [@@inline] [@@specialise]
      let starts a b c d = a = c && b < d [@@inline]
      let started a b c d = invert starts a b c d [@@inline] [@@specialise]
      let finishes a b c d = a > c && b = d [@@inline]
      let finished a b c d = invert finishes a b c d [@@inline] [@@specialise]
      let during a b c d = a > c && b < d [@@inline]
      let contains a b c d = invert during a b c d [@@inline] [@@specialise]
      let equals a b c d = a = c && b = d [@@inline]

      let relate a b c d = match () with
        | () when meets a b c d -> Meets
        | () when met a b c d -> Met
        | () when before a b c d -> Before
        | () when after a b c d -> After
        | () when overlaps a b c d -> Overlaps
        | () when overlapped a b c d -> Overlapped
        | () when starts a b c d -> Starts
        | () when started a b c d -> Started
        | () when finishes a b c d -> Finishes
        | () when finished a b c d -> Finished
        | () when during a b c d -> During
        | () when contains a b c d -> Contains
        | () when equals a b c d -> Equals
        | () -> assert false
      [@@inline]
    end

    (** Extension of the Allen's Algebra over points.

        A point can have only five relations to an interval.

    *)
    module Point = struct
      type order =
        | Before                (* preceeds the interval *)
        | Starts                (* equal to the start *)
        | During                (* inside of the interval *)
        | Finishes              (* equal to the end *)
        | After                 (* follows the interval *)

      let before p a _ = p < a [@@inline]
      let starts p a _ = p = a [@@inline]
      let during p a b = p > a && p < b [@@inline]
      let finishes p _ b = p = b [@@inline]
      let after p _ b = p > b [@@inline]
      let relate p a b = match () with
        | () when before p a b -> Before
        | () when starts p a b -> Starts
        | () when during p a b -> During
        | () when finishes p a b -> Finishes
        | () when after p a b -> After
        | () -> assert false
      [@@inline]
    end
  end
  type 'a key = 'a Key.t

  (* five leaves holding from zero to four elements and
     three non-leaf trees that can either lean left (when
     the left tree/leg is shorter, lean right (the right one
     is shorter), or stand on equal legs.
  *)
  type record =
    | T0
    | T1 : 'a key * 'a -> record
    | T2 : 'a key * 'a *
           'b key * 'b -> record
    | T3 : 'a key * 'a *
           'b key * 'b *
           'c key * 'c -> record
    | T4 : 'a key * 'a *
           'b key * 'b *
           'c key * 'c *
           'd key * 'd -> record
    | LL : record * 'a key * 'a * record -> record (* h(x) = h(y) - 1 *)
    | EQ : record * 'a key * 'a * record -> record (* h(x) = h(y) *)
    | LR : record * 'a key * 'a * record -> record (* h(x) = h(y) + 1 *)

  type t = record

  let pp_field ppf (k,v) =
    Format.fprintf ppf "%s : %a"
      (Name.to_string (Key.name k))
      Sexp.pp_hum (Key.to_sexp k v)

  let rec pp_fields ppf = function
    | T0 -> ()
    | T1 (ka,a) ->
      Format.fprintf ppf "%a" pp_field (ka,a)
    | T2 (ka,a,kb,b) ->
      Format.fprintf ppf "%a;@ %a"
        pp_field (ka,a)
        pp_field (kb,b)
    | T3 (ka,a,kb,b,kc,c) ->
      Format.fprintf ppf "%a;@ %a;@ %a"
        pp_field (ka,a)
        pp_field (kb,b)
        pp_field (kc,c)
    | T4 (ka,a,kb,b,kc,c,kd,d) ->
      Format.fprintf ppf "%a;@ %a;@ %a;@ %a"
        pp_field (ka,a)
        pp_field (kb,b)
        pp_field (kc,c)
        pp_field (kd,d)
    | LR (x,ka,a,y) ->
      Format.fprintf ppf "%a;@ %a;@ %a"
        pp_fields x pp_field (ka,a) pp_fields y
    | LL (x,ka,a,y) ->
      Format.fprintf ppf "%a;@ %a;@ %a"
        pp_fields x pp_field (ka,a) pp_fields y
    | EQ (x,ka,a,y) ->
      Format.fprintf ppf "%a;@ %a;@ %a"
        pp_fields x pp_field (ka,a) pp_fields y

  let pp ppf t =
    Format.fprintf ppf "{@[<2>@,%a@]}" pp_fields t

  let pp_elt ppf (k,v) =
    Format.fprintf ppf "%d:%a" (Key.uid k) Sexp.pp_hum (Key.to_sexp k v)

  let pp_elt ppf (k,_) =
    Format.fprintf ppf "%d" (Key.uid k)

  let rec pp_tree ppf = function
    | T0 -> Format.fprintf ppf "()"
    | T1 (ka,a) ->
      Format.fprintf ppf "(%a)" pp_elt (ka,a)
    | T2 (ka,a,kb,b) ->
      Format.fprintf ppf "(%a,%a)"
        pp_elt (ka,a)
        pp_elt (kb,b)
    | T3 (ka,a,kb,b,kc,c) ->
      Format.fprintf ppf "(%a,%a,%a)"
        pp_elt (ka,a)
        pp_elt (kb,b)
        pp_elt (kc,c)
    | T4 (ka,a,kb,b,kc,c,kd,d) ->
      Format.fprintf ppf "(%a,%a,%a,%a)"
        pp_elt (ka,a)
        pp_elt (kb,b)
        pp_elt (kc,c)
        pp_elt (kd,d)
    | LR (x,k,a,y) ->
      Format.fprintf ppf "LR(%a,%a,%a)"
        pp_tree x pp_elt (k,a) pp_tree y
    | LL (x,k,a,y) ->
      Format.fprintf ppf "LL(%a,%a,%a)"
        pp_tree x pp_elt (k,a) pp_tree y
    | EQ (x,k,a,y) ->
      Format.fprintf ppf "EQ(%a,%a,%a)"
        pp_tree x pp_elt (k,a) pp_tree y

  let empty = T0
  let is_empty = function
    | T0 -> true
    | _ -> false

  (*
     - LL (x,y) : h(x) = h(y) - 1
     - EQ (x,y) : h(x) = h(y)
     - LR (x,y) : h(x) = h(y) + 1
 *)

  let (<$) k1 k2 =
    let k1 = Key.uid k1 and k2 = Key.uid k2 in
    (Key.Uid.(<)[@inlined]) k1 k2
  [@@inline]

  let make0 = T0
  let make1 k a = T1 (k,a) [@@inline]
  let make2 ka a kb b = T2 (ka,a,kb,b) [@@inline]
  let make3 ka a kb b kc c = T3 (ka,a,kb,b,kc,c) [@@inline]
  let make4 ka a kb b kc c kd d = T4 (ka,a, kb,b, kc,c, kd,d) [@@inline]
  let make5 ka a kb b kc c kd d ke e =
    EQ (make2 ka a kb b,kc,c,make2 kd d ke e)
  [@@inline]
  let make6 ka a kb b kc c kd d ke e kf f =
    EQ (T2 (ka,a,kb,b),kc,c,T3(kd,d,ke,e,kf,f))
  [@@inline]
  let make7 ka a kb b kc c kd d ke e kf f kg g =
    EQ (T3 (ka,a,kb,b,kc,c), kd,d, T3 (ke,e,kf,f,kg,g))
  [@@inline]
  let make8 ka a kb b kc c kd d ke e kf f kg g kh h =
    EQ (T3 (ka,a,kb,b,kc,c),kd,d, T4(ke,e,kf,f,kg,g,kh,h))
  [@@inline]
  let make9 ka a kb b kc c kd d ke e kf f kg g kh h ki i =
    EQ (T4 (ka,a,kb,b,kc,c,kd,d),ke,e,T4(kf,f,kg,g,kh,h,ki,i))
  [@@inline]
  let make10 ka a kb b kc c kd d ke e kf f kg g kh h ki i kj j =
    LL (make4 ka a kb b kc c kd d, ke, e, make5 kf f kg g kh h ki i kj j)
  [@@inline]

  type 'r visitor = {
    visit : 'a. 'a key -> 'a -> 'r -> 'r;
  }

  let rec foreach x ~init f = match x with
    | T0 -> init
    | T1 (ka,a) -> f.visit ka a init
    | T2 (ka,a,kb,b) ->
      f.visit ka a init |>
      f.visit kb b
    | T3 (ka,a,kb,b,kc,c) ->
      f.visit ka a init |>
      f.visit kb b |>
      f.visit kc c
    | T4 (ka,a,kb,b,kc,c,kd,d) ->
      f.visit ka a init |>
      f.visit kb b |>
      f.visit kc c |>
      f.visit kd d
    | LL (x,k,a,y) ->
      foreach y f ~init:(f.visit k a @@ foreach x ~init f)
    | EQ (x,k,a,y) ->
      foreach y f ~init:(f.visit k a @@ foreach x ~init f)
    | LR (x,k,a,y) ->
      foreach y f ~init:(f.visit k a @@ foreach x ~init f)

  type ('b,'r) app = {
    app : 'a. 'a key -> 'a -> 'b -> 'r
  }

  let cmp x y = Key.compare x y [@@inline]
  let eq x y = Key.compare x y = 0 [@@inline]

  exception Rol_wrong_rank of record
  exception Ror_wrong_rank of record

  let rol = function
    | LL (x,ka,a,LL (y,kb,b,z)) ->
      (*
       * h(x) = m-2
       * h(LL(y,b,z)=m
       * h(y)=m-2
       * h(z)=m-1
       * ----------------
       * h(EQ(x,a,y)) = m-1
       * h(EQ(EQ(x,ka,a,y),b,z)) = m
       *)
      EQ (EQ(x,ka,a,y),kb,b,z)
    | LL (x,ka,a,EQ (y,kb,b,z)) ->
      (*
       * h(x) = m-2
       * h(EQ(y,b,z))=m
       * h(y)=m-1
       * h(z)=m-1
       * ----------------
       * h(LL(x,a,y)) = m
       * h(LR(LL(x,a,y),b,z)) = m+1
       *)
      LR (LL(x,ka,a,y),kb,b,z)
    | LL (w,ka,a,LR (LL(x,kb,b,y),kc,c,z)) ->
      (*
       * h(w) = m-2
       * h(LR(LL(x,b,y),c,z))=m
       * h(z)=m-2
       * h(LL(x,b,y))=m-1
       * h(y)=m-2
       * h(x)=m-3
       * ----------------
       * h(LR(w,a,x))=m-1, h(x) < h(w)
       * h(EQ(y,kc,c,z))=m-1, h(y) = h(z)
       * h(EQ (LR(w,ka,a,x),kb,b,EQ(y,kc,c,z))) = m
       *)
      EQ (LR(w,ka,a,x),kb,b,EQ(y,kc,c,z))
    | LL (w,ka,a,LR (EQ(x,kb,b,y),kc,c,z)) ->
      (*
       * h(w) = m-2
       * h(LR(EQ(x,b,y),c,z))=m
       * h(z)=m-2
       * h(EQ(x,b,y))=m-1
       * h(y)=m-2
       * h(x)=m-2
       * ----------------
       * h(EQ(w,a,x))=m-1, h(x) = h(w)
       * h(EQ(y,kc,c,z))=m-1, h(y) = h(z)
       * h(EQ (EQ(w,ka,a,x),kb,b,EQ(y,kc,c,z))) = m
       *)
      EQ (EQ(w,ka,a,x),kb,b,EQ(y,kc,c,z))
    | LL (w,ka,a,LR (LR(x,kb,b,y),kc,c,z)) ->
      (*
       * h(w) = m-2
       * h(LR(LR(x,b,y),c,z))=m
       * h(z)=m-2
       * h(LR(x,b,y))=m-1
       * h(y)=m-3
       * h(x)=m-2
       * ----------------
       * h(EQ(w,a,x))=m-1, h(x) = h(w)
       * h(LL(y,kc,c,z))=m-1, h(y) < h(z)
       * h(EQ (EQ(w,ka,a,x),kb,b,LL(y,kc,c,z))) = m
       *)
      EQ (EQ(w,ka,a,x),kb,b,LL(y,kc,c,z))
    | r -> raise (Rol_wrong_rank r)
  [@@inline]


  let ror = function
    | LR (LR(x,ka,a,y),kb,b,z) ->
      (*
       * h(z) = m-2
       * h(LR(x,a,y))=m
       * h(y)=m-2
       * h(x)=m-1
       * ------------------
       * h(EQ(y,b,z))=m-1, h(y) = h(z)
       * h(EQ (x,a,EQ(y,kb,b,z))) = m
       *)
      EQ (x,ka,a,EQ(y,kb,b,z))
    | LR (EQ(x,ka,a,y),kb,b,z) ->
      (*
       * h(z) = m-2
       * h(EQ(x,a,y))=m
       * h(y)=m-1
       * h(x)=m-1
       * ------------------
       * h(LR(y,b,z))=m, h(y) > h(z)
       * h(LL (x,a,LR(y,b,z))) = m+1, h(x) < m
       *)
      LL (x,ka,a,LR(y,kb,b,z))
    | LR (LL (w,ka,a,LR(x,kb,b,y)),kc,c,z) ->
      (*
       * h(z) = m-2
       * h(LL (w,a,LR(x,b,y)))=m
       * h(LR(x,b,y))=m-1
       * h(w)=m-2
       * h(x)=m-2
       * h(y)=m-3
       * -------------------------
       * h(EQ(w,a,x)) = m-1, h(x) = h(w)
       * h(LL(y,c,z)) = m-1, h(y) < h(z)
       *)
      EQ (EQ(w,ka,a,x), kb,b, LL(y,kc,c,z))
    | LR (LL (w,ka,a,EQ(x,kb,b,y)),kc,c,z) ->
      (*
       * h(z) = m-2
       * h(LL (w,a,EQ(x,b,y)))=m
       * h(EQ(x,b,y))=m-1
       * h(w)=m-2
       * h(x)=m-2
       * h(y)=m-2
       * -------------------------
       * h(EQ(w,a,x)) = m-1, h(x) = h(w)
       * h(EQ(y,c,z)) = m-1, h(y) = h(z)
       *)
      EQ (EQ(w,ka,a,x), kb,b, EQ(y,kc,c,z))
    | LR (LL (w,ka,a,LL(x,kb,b,y)),kc,c,z) ->
      (*
       * h(z) = m-2
       * h(LL (w,a,LL(x,b,y)))=m
       * h(LL(x,b,y))=m-1
       * h(w)=m-2
       * h(x)=m-3
       * h(y)=m-2
       * -------------------------
       * h(LR(w,a,x)) = m-1, h(x) < h(w)
       * h(EQ(y,c,z)) = m-1, h(y) = h(z)
       *)
      EQ (LR(w,ka,a,x), kb,b, EQ(y,kc,c,z))
    | r -> raise (Ror_wrong_rank r)
  [@@inline]

  let rank_increases was now = match was,now with
    | (T0 | T1 _ | T2 _ | T3 _ | T4 _), LR _
    | (T0 | T1 _ | T2 _ | T3 _ | T4 _), EQ _
    | (T0 | T1 _ | T2 _ | T3 _ | T4 _), LL _ -> true
    | EQ _, LL _
    | EQ _, LR _ -> true
    | LR _, LL _
    | LL _, LR _ -> false
    | _ -> false
  [@@inline]

  (* [p += c] updates the right subtree of [p] with [c].
     pre: rank p > 1 /\ rank c > 1 *)
  let (+=) p c' = match p with
    | LL (b,k,x,c) ->
      if rank_increases c c'
      then rol (LL (b,k,x,c'))
      else LL (b,k,x,c')
    | LR (b,k,x,c) ->
      if rank_increases c c'
      then EQ (b,k,x,c')
      else LR (b,k,x,c')
    | EQ (b,k,x,c) ->
      if rank_increases c c'
      then LL (b,k,x,c')
      else EQ (b,k,x,c')
    | _ -> failwith "+=: rank < 2"
  [@@inline]

  (* [b =+ p] updates the left subtree of [p] with [b].
     pre: rank p > 1 /\ rank b > 1 *)
  let (=+) b' p = match p with
    | LL (b,k,x,c) ->
      if rank_increases b b'
      then EQ (b',k,x,c)
      else LL (b',k,x,c)
    | LR (b,k,x,c) ->
      if rank_increases b b'
      then ror (LR (b',k,x,c))
      else LR (b',k,x,c)
    | EQ (b,k,x,c) ->
      if rank_increases b b'
      then LR (b',k,x,c)
      else EQ (b',k,x,c)
    | _ -> failwith "=+: rank < 2"
  [@@inline]

  (* pre:
     - a is not in t;
     - for all functions except [bal] t is balanced;
     - for [bal] the input is t is disbalanced.

     post:
     - a is in t', and len t' = len t + 1
     - h(t') >= h(t)
     - t' is balanced
  *)
  let rec insert
    : type a. a key -> a -> record -> record = fun ka a -> function
    | T0 -> make1 ka a
    | T1 (kb,b) -> if ka <$ kb
      then make2 ka a kb b
      else make2 kb b ka a
    | T2 (kb,b,kc,c) -> if ka <$ kb
      then make3 ka a kb b kc c else if ka <$ kc
      then make3 kb b ka a kc c
      else make3 kb b kc c ka a
    | T3 (kb,b,kc,c,kd,d) ->
      if ka <$ kc
      then if ka <$ kb
        then make4 ka a kb b kc c kd d
        else make4 kb b ka a kc c kd d
      else if ka <$ kd
      then make4 kb b kc c ka a kd d
      else make4 kb b kc c kd d ka a
    | T4 (kb,b,kc,c,kd,d,ke,e) ->
      if ka <$ kd then
        if ka <$ kc then
          if ka <$ kb
          then make5 ka a kb b kc c kd d ke e
          else make5 kb b ka a kc c kd d ke e
        else make5 kb b kc c ka a kd d ke e
      else if ka <$ ke
      then make5 kb b kc c kd d ka a ke e
      else make5 kb b kc c kd d ke e ka a
    | LL (b,k,_,c) as t ->
      if ka <$ k
      then insert ka a b =+ t
      else t += insert ka a c
    | LR (b,k,_,c) as t ->
      if ka <$ k
      then insert ka a b =+ t
      else t += insert ka a c
    | EQ (b,k,_,c) as t ->
      if ka <$ k
      then insert ka a b =+ t
      else t += insert ka a c

  (* [merge k x y] *)
  type merge = {
    merge : 'a. 'a key -> 'a -> 'a -> 'a
  }

  let merge
    : type a b. merge -> a key -> b key -> b -> a -> a =
    fun {merge} ka kb b a ->
    let T = Key.same ka kb in
    merge kb b a

  let app = merge


  let rec upsert ~update:ret ~insert:add ka a t = match t with
    | T0 -> add (make1 ka a)
    | T1 (kb,b) -> if eq ka kb
      then ret (fun f -> make1 ka (app f ka kb b a))
      else add (insert ka a t)
    | T2 (kb,b,kc,c) -> if eq ka kb
      then ret (fun f -> make2 ka (app f ka kb b a) kc c) else if eq ka kc
      then ret (fun f -> make2 kb b ka (app f ka kc c a))
      else add (insert ka a t)
    | T3 (kb,b,kc,c,kd,d) -> begin match cmp ka kc with
        | 0 -> ret (fun f -> make3 kb b ka (app f ka kc c a) kd d)
        | 1 -> if eq ka kd
          then ret (fun f -> make3 kb b kc c ka (app f ka kd d a))
          else add (insert ka a t)
        | _ -> if eq ka kb
          then ret (fun f -> make3 ka (app f ka kb b a) kc c kd d)
          else add@@insert ka a t
      end
    | T4 (kb,b,kc,c,kd,d,ke,e) -> begin match cmp ka kd with
        | 0 -> ret@@fun f ->
          make4 kb b kc c ka (app f ka kd d a) ke e
        | 1 -> if eq ka ke
          then ret@@fun f -> make4 kb b kc c kd d ka (app f ka ke e a)
          else add@@insert ka a t
        | _ -> match cmp ka kc with
          | 0 -> ret@@fun f ->
            make4 kb b ka (app f ka kc c a) kd d ke e
          | 1 -> add@@insert ka a t
          | _ -> if eq ka kb
            then ret@@fun f ->
              make4 ka (app f ka kb b a) kc c kd d ke e
            else add@@insert ka a t
      end
    | LL (x,kb,b,y) -> begin match cmp ka kb with
        | 0 -> ret@@fun f -> LL (x,ka,app f ka kb b a,y)
        | 1 -> upsert ka a y
                 ~update:(fun k -> ret@@fun f -> LL (x,kb,b,k f))
                 ~insert:(fun y -> add (t += y))
        | _ ->
          upsert ka a x
            ~update:(fun k -> ret@@fun f -> LL (k f,kb,b, y))
            ~insert:(fun x -> add (x =+ t))
      end
    | EQ (x,kb,b,y) -> begin match cmp ka kb with
        | 0 -> ret@@fun f -> EQ (x,ka,app f ka kb b a,y)
        | 1 -> upsert ka a y
                 ~update:(fun k -> ret@@fun f -> EQ (x,kb,b,k f))
                 ~insert:(fun y -> add (t += y))
        | _ -> upsert ka a x
                 ~update:(fun k -> ret@@fun f -> EQ (k f,kb,b,y))
                 ~insert:(fun x -> add (x =+ t))
      end
    | LR (x,kb,b,y) -> begin match cmp ka kb with
        | 0 -> ret@@fun f -> LR (x,ka,app f ka kb b a,y)
        | 1 -> upsert ka a y
                 ~update:(fun k -> ret@@fun f -> LR (x,kb,b,k f))
                 ~insert:(fun y -> add (t += y))
        | _ -> upsert ka a x
                 ~update:(fun k -> ret@@fun f -> LR (k f,kb,b,y))
                 ~insert:(fun x -> add (x =+ t))
      end
  [@@specialise]

  let monomorphic_merge
    : type t. t key -> (t -> t -> t) -> merge =
    fun k f -> {
        merge = fun (type a)
          (kb : a key) (b : a) (a : a) : a ->
          let T = Key.same k kb in
          f b a
      }
  [@@specialise]

  let update f ka a x =
    let f = monomorphic_merge ka f in
    upsert ka a x
      ~update:(fun k -> k f)
      ~insert:(fun x -> x)
  [@@specialise]

  let set ka a x =
    let f = monomorphic_merge ka (fun _ x -> x) in
    upsert ka a x
      ~update:(fun k -> k f)
      ~insert:(fun x -> x)

  exception Field_not_found

  let return (type a b) (k : a key) (ka : b key) (a : b) : a =
    let T = Key.same k ka in
    a
  [@@inline]

  let rec get k = function
    | T0 -> raise Field_not_found
    | T1 (ka,a) -> if eq k ka then return k ka a
      else raise Field_not_found
    | T2 (ka,a,kb,b) -> begin match cmp k kb with
        | 0 -> return k kb b
        | 1 -> raise Field_not_found
        | _ -> if eq k ka then return k ka a
          else raise Field_not_found
      end
    | T3 (ka,a,kb,b,kc,c) -> begin match cmp k kb with
        | 0 -> return k kb b
        | 1 -> if eq k kc then return k kc c
          else raise Field_not_found
        | _ -> if eq k ka then return k ka a
          else raise Field_not_found
      end
    | T4 (ka,a,kb,b,kc,c,kd,d) -> begin match cmp k kc with
        | 0 -> return k kc c
        | 1 -> if eq k kd then return k kd d
          else raise Field_not_found
        | _ -> match cmp k kb with
          | 0 -> return k kb b
          | 1 -> raise Field_not_found
          | _ -> if eq k ka then return k ka a
            else raise Field_not_found
      end
    | LL (x,ka,a,y) -> begin match cmp k ka with
        | 0 -> return k ka a
        | 1 -> get k y
        | _ -> get k x
      end
    | EQ (x,ka,a,y) -> begin match cmp k ka with
        | 0 -> return k ka a
        | 1 -> get k y
        | _ -> get k x
      end
    | LR (x,ka,a,y) -> begin match cmp k ka with
        | 0 -> return k ka a
        | 1 -> get k y
        | _ -> get k x
      end


  let find k x = try Some (get k x) with
    | Field_not_found -> None

  let fold_merge (type a) m x y =
    foreach y ~init:x {
      visit = fun (type b c) (ka : b key) (a : b) x ->
        upsert ka a x
          ~insert:(fun x -> x)
          ~update:(fun k -> k m)
    }

  let merge_11 m ka a kb b = match Key.compare ka kb with
    | 0 -> make1 ka (app m ka kb b a)
    | 1 -> make2 kb b ka a
    | _ -> make2 ka a kb b
  [@@inline]

  let merge_12 m ka a kb b kc c =
    match Key.Point.relate ka kb kc with
    | Before   -> make3 ka a kb b kc c
    | Starts   -> make2 ka (app m ka kb b a) kc c
    | During   -> make3 kb b ka a kc c
    | Finishes -> make2 kb b ka (app m ka kc c a)
    | After    -> make3 kb b kc c ka a
  [@@inline]

  let merge_13 m ka a kb b kc c kd d =
    match Key.Point.relate ka kb kd with
    | Before   -> make4 ka a kb b kc c kd d
    | Starts   -> make3 ka (app m ka kb b a) kc c kd d
    | Finishes -> make3 kb b kc c kd (app m kd ka a d)
    | After    -> make4 kb b kc c kd d ka a
    | During   -> match Key.compare ka kc with
      | 0      -> make3 kb b kc (app m kc ka a c) kd d
      | 1      -> make4 kb b kc c ka a kd d
      | _      -> make4 kb b ka a kc c kd d
  [@@inline]

  let merge_22 m ka a kb b kc c kd d =
    match Key.Interval.relate ka kb kc kd with
    | Meets      -> make3 ka a kb (app m kb kc c b) kd d
    | Met        -> make3 kc c kd (app m kd ka a d) kb b
    | Before     -> make4 ka a kb b kc c kd d
    | After      -> make4 kc c kd d ka a kb b
    | Overlaps   -> make4 ka a kc c kb b kd d
    | Overlapped -> make4 kc c ka a kd d kb b
    | Starts     -> make3 ka (app m ka kc c a) kb b kd d
    | Started    -> make3 ka (app m ka kc c a) kd d kb b
    | Finishes   -> make3 kc c ka a kb (app m kb kd d b)
    | Finished   -> make3 ka a kc c kb (app m kb kd d b)
    | During     -> make4 kc c ka a kb b kd d
    | Contains   -> make4 ka a kc c kd d kb b
    | Equals     -> make2 ka (app m ka kc c a) kb (app m kb kd d b)
  [@@inline]

  let merge m x y =
    if phys_equal x y then x
    else match x,y with
      | T0,x | x, T0 -> x
      | T1 (ka, a), T1 (kb, b) ->
        merge_11 m ka a kb b
      | T1 (ka, a), T2 (kb, b, kc, c) ->
        merge_12 m ka a kb b kc c
      | T2 (kb, b, kc, c), T1 (ka, a) ->
        merge_12 m ka a kb b kc c
      | T1 (ka, a), T3 (kb, b, kc, c, kd, d) ->
        merge_13 m ka a kb b kc c kd d
      | T3 (kb, b, kc, c, kd, d), T1 (ka, a) ->
        merge_13 m ka a kb b kc c kd d
      | T2 (ka, a, kb, b), T2 (kc, c, kd, d) ->
        merge_22 m ka a kb b kc c kd d
      | _ -> fold_merge m x y
  [@@inline]

  let sexp_of_t dict = Sexp.List (foreach ~init:[] dict {
      visit = fun k x xs ->
        Sexp.List [
          Sexp.Atom (Name.to_string (Key.name k));
          (Key.to_sexp k x)
        ] :: xs
    })



  let pp_key ppf {Key.name} =
    Format.fprintf ppf "%s" (Name.to_string name)
end

module Record = struct
  module Key = Dict.Key
  module Uid = Dict.Key.Uid

  type record = Dict.t
  type t = record
  type 'a key = 'a Dict.key

  module Repr = struct
    type entry = {
      name : Name.t;
      data : string;
    } [@@deriving bin_io]

    type t = entry list [@@deriving bin_io]
  end

  type vtable = {
    order   : 'a. 'a key -> 'a -> 'a -> Order.partial;
    join    : 'a. 'a key -> 'a -> 'a -> ('a,conflict) result;
    inspect : 'a. 'a key -> 'a -> Sexp.t;
  }

  type slot_io = {
    reader : string -> record -> record;
    writer : record -> string option;
  }

  let io : slot_io Hashtbl.M(Name).t =
    Hashtbl.create (module Name)

  let vtables : vtable Hashtbl.M(Uid).t =
    Hashtbl.create (module Uid)

  let empty = Dict.empty
  let is_empty = Dict.is_empty

  let uid = Key.uid
  let domain k = Hashtbl.find_exn vtables (uid k)

  exception Not

  let (<:=) x y =
    try
      Dict.foreach ~init:() x {
        visit = fun k x () ->
          match Dict.find k y with
          | None -> raise Not
          | Some y -> match (domain k).order k x y with
            | LT | EQ -> ()
            | GT | NC -> raise Not
      };
      true
    with Not -> false

  let order : t -> t -> Order.partial = fun x y ->
    if phys_equal x y then EQ
    else match x,y with
      | T0, (T1 _ | T2 _ | T3 _ | T4 _) -> LT
      | (T1 _ | T2 _ | T3 _ | T4 _), T0 -> GT
      | _ -> match x <:= y, y <:= x with
        | true,false  -> LT
        | true,true   -> EQ
        | false,true  -> GT
        | false,false -> NC

  exception Merge_conflict of conflict

  let domain_merge = {
    Dict.merge = fun k x y ->
      match (domain k).join k x y with
      | Ok x -> x
      | Error err -> raise (Merge_conflict err)
  }

  let resolving_merge on_conflict = {
    Dict.merge = fun k x y ->
      match (domain k).join k x y with
      | Ok b -> b
      | Error err -> match on_conflict with
        | `drop_left -> y
        | `drop_right -> x
        | `fail -> raise (Merge_conflict err)
  }

  let commit (type p) _ (key : p Key.t) v x =
    match v with
    | Dict.T0 -> Ok (Dict.make1 key x)
    | _ ->
      try Result.return@@Dict.upsert key x v
          ~insert:Fn.id
          ~update:(fun k -> k domain_merge)
      with Merge_conflict err -> Error err

  let put k v x = Dict.set k x v
  let get
    : type a. a Key.t -> a Domain.t -> record -> a =
    fun k {Domain.empty} data ->
    match Dict.find k data with
    | None -> empty
    | Some x -> x

  let splice = Dict.app


  let join x y =
    try Ok (Dict.merge domain_merge x y)
    with Merge_conflict err -> Error err

  let try_merge ~on_conflict x y =
    try Ok (Dict.merge (resolving_merge on_conflict) x y)
    with Merge_conflict err -> Error err

  let eq = Dict.Key.same

  let register_persistent (type p)
      (key : p Key.t)
      (p : p Persistent.t) =
    let slot = Key.name key in
    Hashtbl.add_exn io ~key:slot ~data:{
      reader = begin fun x dict ->
        let x = Persistent.of_string p x in
        Dict.insert key x dict
      end;
      writer = begin fun dict ->
        match Dict.find key dict with
        | None -> None
        | Some s -> Some (Persistent.to_string p s)
      end
    }

  include Binable.Of_binable_with_uuid(Repr)(struct
      type t = record
      let to_binable s =
        Dict.foreach s ~init:[] {
          visit = fun k _ xs ->
            let name = Key.name k in
            match Hashtbl.find io name with
            | None -> xs
            | Some {writer} ->
              match writer s with
              | None -> xs
              | Some data -> Repr.{name; data} :: xs
        }

      let of_binable entries =
        List.fold entries ~init:empty ~f:(fun s {Repr.name; data} ->
            match Hashtbl.find io name with
            | None -> s
            | Some {reader} -> reader data s)

      let caller_identity = 
        Bin_shape.Uuid.of_string "1b0bac12-16f0-42f7-89c9-aef05e549537"
    end)
  

  let eq = Dict.Key.same

  let register_domain
    : type p. p Key.t -> p Domain.t -> unit =
    fun key dom ->
    let vtable = {
      order = begin fun (type a) (k : a key) (x : a) (y : a) ->
        let T = eq k key in
        dom.order x y
      end;
      inspect = begin fun (type a) (k : a key) (x : a) ->
        let T = eq k key in
        dom.inspect x;
      end;
      join = begin fun (type a) (k : a key) (x : a) (y : a) :
        (a,conflict) result ->
        let T = eq k key in
        dom.join x y
      end;
    } in
    Hashtbl.add_exn vtables ~key:(uid key) ~data:vtable

  let sexp_of_t x = Dict.sexp_of_t x
  let t_of_sexp = opaque_of_sexp
  let inspect = sexp_of_t

  let pp_text ppf s =
    Format.fprintf ppf "@[<1>\"%a\"@]" Format.pp_print_text s

  let is_text = String.exists ~f:Char.is_whitespace

  let rec pp_hum ppf = function
    | Sexp.Atom s -> if is_text s
      then pp_text ppf s
      else Format.pp_print_string ppf s
    | Sexp.List xs ->
      Format.fprintf ppf "(@[<hv>";
      Format.pp_print_list pp_hum ppf xs
        ~pp_sep:Format.pp_print_space;
      Format.fprintf ppf "@])"

  let pp_payload ppf = function
    | [Sexp.Atom str] ->
      Format.fprintf ppf "@[<1>\"%a\"@]" Format.pp_print_text str
    | other ->
      Format.fprintf ppf "%a" pp_hum (Sexp.List other)


  let pp ppf x = pp_hum ppf (inspect x)
  let pp_slots slots ppf x =
    let slots = Set.of_list (module String) slots in
    let no_name = Option.is_none (Set.nth slots 1) in
    match (inspect x : Sexp.t) with
    | Atom _ -> assert false
    | List xs ->
      let first = ref true in
      Format.fprintf ppf "@[<v>";
      List.iter xs ~f:(function
          | Sexp.List (Atom slot :: payload ) as data
            when Set.mem slots slot ->
            if not first.contents then Format.fprintf ppf "@,";
            first := false;
            if no_name
            then Format.fprintf ppf "%a" pp_payload payload
            else Format.fprintf ppf "%a" pp_hum data
          | _ -> ());
      Format.fprintf ppf "@]"

end

module Knowledge = struct

  type +'a value = {
    cls  : 'a;
    data : Record.t;
    time : Int63.t;
  }
  type (+'a,+'s) cls = ('a,'s) Class.t
  type 'a obj = Oid.t
  type 'p domain = 'p Domain.t
  type 'a persistent = 'a Persistent.t
  type 'a ord = Oid.comparator_witness
  type conflict = Conflict.t = ..
  type pid = Pid.t
  type oid = Oid.t [@@deriving bin_io, compare, sexp]

  type cell = {
    car : oid;
    cdr : oid;
  } [@@deriving bin_io, compare, sexp]

  module Cell = struct
    type t = cell
    include Comparable.Make_binable(struct
        type t = cell [@@deriving bin_io,compare, sexp]
      end)
  end


  module Env = struct
    type workers = {
      waiting : unit Pid.Tree.t;
      current : unit Pid.Tree.t;
    }

    type work = Done | Work of workers
    type info = {
      data : Record.t;
      comp : work Map.M(Name).t;
      name : fullname option;
    }

    type objects = {
      last : Oid.t;
      vals : info Oid.Tree.t;
      objs : Oid.t Map.M(Name.Full).t;
      pubs : Oid.Set.t Map.M(String).t;
    }

    let empty_class = {
      last = Oid.first;
      vals = Oid.Tree.empty;
      objs = Map.empty (module Name.Full);
      pubs = Map.empty (module String);
    }

    type t = {
      classes : objects Map.M(Name).t;
      package : string;
      context : Dict.t;
    }
  end

  type state = Env.t


  let empty : Env.t = {
    package = user_package;
    classes = Map.empty (module Name);
    context = Dict.empty;
  }

  let noinfo : Env.info = {
    data = Record.empty;
    comp = Map.empty (module Name);
    name = None;
  }


  type 'a knowledge = {
    run : 'r. reject:(conflict -> 'r) -> accept:('a -> state -> 'r) -> state -> 'r
  }

  module Knowledge = struct
    type 'a t = 'a knowledge
    type _ error = conflict
    let fail p : 'a t = {run = fun ~reject ~accept:_ _ -> reject p}
    [@@inline]
    let catch x err = {
      run = fun ~reject ~accept s -> x.run s
          ~accept
          ~reject:(fun p -> (err p).run ~reject ~accept s)
    } [@@inline]

    include Monad.Make(struct
        type 'a t = 'a knowledge
        let return x : 'a t = {
          run = fun ~reject:_ ~accept s -> accept x s
        } [@@inline]

        let bind : 'a t -> ('a -> 'b t) -> 'b t = fun x f -> {
            run = fun ~reject ~accept s -> x.run s
                ~reject
                ~accept:(fun x s ->
                    (f x).run ~reject ~accept s)
          } [@@inline]

        let map : 'a t -> f:('a -> 'b) -> 'b t = fun x ~f -> {
            run = fun ~reject ~accept s -> x.run s
                ~reject
                ~accept:(fun x s -> accept (f x) s)
          } [@@inline]
        let map = `Custom map
      end)

  end

  open Knowledge.Syntax

  module Slot = struct
    type ('p,'r) action = {
      run : Oid.t -> 'r;
      pid : pid;
    }

    type (+'a,'p) t = {
      cls : ('a,unit) cls;
      dom : 'p Domain.t;
      key : 'p Dict.Key.t;
      name : Name.t;
      desc : string option;
      promises : (pid, ('p,unit knowledge) action) Hashtbl.t;
      watchers : (pid, ('p,'p -> unit knowledge) action) Hashtbl.t;
    }

    type pack = Pack : ('a,'p) t -> pack
    let repository = Hashtbl.create (module Name)

    let register slot =
      Hashtbl.update repository slot.cls.name ~f:(function
          | None -> [Pack slot]
          | Some xs -> Pack slot :: xs)

    let enum {Class.name} = Hashtbl.find_multi repository name

    let declare ?(public=false) ?desc ?persistent ?package cls name (dom : 'a Domain.t) =
      let name = Registry.add_slot ?desc ?package name in
      let key = Dict.Key.create ~name dom.inspect in
      if public then Registry.update_class ~cls:cls.Class.name ~slot:name;
      Option.iter persistent ~f:(Record.register_persistent key);
      Record.register_domain key dom;
      let promises = Hashtbl.create (module Pid) in
      let watchers = Hashtbl.create (module Pid) in
      let cls = Class.refine cls () in
      let slot = {cls; dom; key; name; desc; promises; watchers} in
      register slot;
      slot

    let cls x = x.cls
    let domain x = x.dom
    let name {name} = name
    let desc x = match x.desc with
      | None -> "no description"
      | Some s -> s
  end

  type (+'a,'p) slot = ('a,'p) Slot.t

  module Value = struct
    type +'a t = 'a value

    (* we could use an extension variant or create a new OCaml object
       instead of incrementing a second, but they are less reliable
       and heavier *)
    let next_second =
      let current = ref Int63.zero in
      fun () -> Int63.incr current; !current

    let empty cls =
      {cls; data=Record.empty; time = next_second ()}

    let is_empty {data} = Record.is_empty data

    let order {data=x} {data=y} = Record.order x y

    let refine {data; cls; time} s=
      {data; time; cls = Class.refine cls s}

    let cls {cls} = cls
    let create cls data = {cls; data; time = next_second ()}
    let put {Slot.key; dom} v x =
      if Domain.is_empty dom x then v
      else {
        v with data = Record.put key v.data x;
               time = next_second ()
      }
    let get {Slot.key; dom} {data} = Record.get key dom data
    let has {Slot.key; dom} {data} =
      not @@ Domain.is_empty dom @@ Record.get key dom data

    let strip
      : type a b. (a value, b value) Type_equal.t -> (a,b) Type_equal.t =
      fun T -> T

    type strategy = [`drop_left | `drop_right ]

    let merge ?(on_conflict=`drop_old) x y =
      let on_conflict : strategy = match on_conflict with
        | `drop_old -> if Int63.(x.time < y.time)
          then `drop_left else `drop_right
        | `drop_new -> if Int63.(x.time < y.time)
          then `drop_right else `drop_left
        | #strategy as other -> other in
      match Record.try_merge ~on_conflict x.data y.data with
      | Ok data -> {
          x with time = next_second ();
                 data;
        }
      | Error _ ->
        (* try_merge fails only if `fail is passed *)
        assert false

    let join x y = match Record.join x.data y.data with
      | Ok data -> Ok {x with data; time = next_second ()}
      | Error c -> Error c

    module type S = sig
      type t [@@deriving sexp]
      val empty : t
      val domain : t domain
      include Base.Comparable.S with type t := t
      include Binable.S with type t := t
    end

    module Comparator = Base.Comparator.Make1(struct
        type 'a t = 'a value
        let sexp_of_t = sexp_of_opaque
        let compare x y = match Record.order x.data y.data with
          | LT -> -1
          | EQ -> 0
          | GT -> 1
          | NC -> Int63.compare x.time y.time
      end)

    include Comparator

    type 'a ord = comparator_witness

    let derive
      : type a b. (a,b) cls ->
        (module S with type t = (a,b) cls t
                   and type comparator_witness = (a,b) cls ord) =
      fun cls ->
      let module R = struct
        type t = (a,b) cls value
        let sexp_of_t x = Record.sexp_of_t x.data
        let t_of_sexp = opaque_of_sexp
        let empty = empty cls

        include Binable.Of_binable_with_uuid(Record)(struct
            type t = (a,b) cls value
            let to_binable : 'a value -> Record.t =
              fun {data} -> data
            let of_binable : Record.t -> 'a value =
              fun data -> {cls; data; time = next_second ()}
            let caller_identity = 
              Bin_shape.Uuid.of_string "6c440a4b-2be3-4d8a-9559-40f6971df733"
          end) 
        type comparator_witness = Comparator.comparator_witness
        include Base.Comparable.Make_using_comparator(struct
            type t = (a,b) cls value
            let sexp_of_t = sexp_of_t
            include Comparator
          end)
        let domain = Domain.define ~empty ~order ~join
            ~inspect:sexp_of_t
            (Name.unqualified (Class.name cls))
      end in
      (module R)

    let pp ppf x = Record.pp ppf x.data
    let pp_slots slots ppf x = Record.pp_slots slots ppf x.data
  end

  module Class = struct
    include Class
    let property = Slot.declare
    module Abstract = struct
      let property = Slot.declare
    end
  end

  let get () : state knowledge = {
    run = fun ~reject:_ ~accept s -> accept s s
  } [@@inline]

  let put s = {
    run = fun ~reject:_ ~accept _ -> accept () s
  } [@@inline]

  let gets f = {
    run = fun ~reject:_ ~accept s -> accept (f s) s
  } [@@inline]
  [@@specialise]

  let update f = {
    run = fun ~reject:_ ~accept s -> accept () (f s)
  } [@@inline]
  [@@specialise]

  let objects {Class.name} =
    get () >>| fun {classes} ->
    match Map.find classes name with
    | None -> Env.empty_class
    | Some objs -> objs
  [@@inline]

  let update_objects {Class.name} f =
    update @@ fun state ->
    let objs = f @@ match Map.find state.classes name with
      | None -> Env.empty_class
      | Some objs -> objs in
    {state with classes = Map.set state.classes ~key:name ~data:objs}
  [@@specialise]

  let map_update_objects {Class.name} f =
    get () >>= fun state ->
    let objs = match Map.find state.classes name with
      | None -> Env.empty_class
      | Some objs -> objs in
    f objs @@ fun objs res ->
    put {state with classes = Map.set state.classes ~key:name ~data:objs} >>| fun () ->
    res
  [@@specialise]


  module Object = struct
    type +'a t = 'a obj
    type 'a ord = Oid.comparator_witness

    let with_new_object objs f =
      let next = Oid.succ objs.Env.last in
      f next {objs with Env.last = next}

    let create : ('a,_) cls -> 'a obj Knowledge.t = fun cls ->
      objects cls >>= fun objs ->
      with_new_object objs @@ fun obj objs ->
      update @@begin function {classes} as s -> {
          s with classes = Map.set classes ~key:cls.name ~data:objs
        }
      end >>| fun () ->
      obj

    let null _ = Oid.zero
    let is_null = Oid.equal Oid.zero

    (* an interesting question, what we shall do if
       1) an symbol is deleted
       2) a data object is deleted?

       So far we ignore both deletes.
    *)
    let delete {Class.name} obj =
      update @@ function {classes} as s -> {
          s with
          classes = Map.change classes name ~f:(function
              | None -> None
              | Some objs -> Some {
                  objs with
                  vals = Oid.Tree.remove objs.vals obj;
                })
        }

    let scoped cls scope =
      create cls >>= fun obj ->
      scope  obj >>= fun r ->
      delete cls obj >>| fun () ->
      r

    let do_intern =
      let is_public {package} obj {Env.pubs} =
        match Map.find pubs package with
        | None -> false
        | Some pubs -> Set.mem pubs obj in
      let unchanged id = Knowledge.return id in
      let publicize {package} obj: Env.objects -> Env.objects =
        fun objects -> {
            objects with pubs = Map.update objects.pubs package ~f:(function
            | None -> Set.singleton (module Oid) obj
            | Some pubs -> Set.add pubs obj)
          } in
      let createsym ~public name classes clsid objects s =
        with_new_object objects @@ fun obj objects ->
        let vals = Oid.Tree.update_with objects.vals obj
            ~has:(fun info -> {info with name = Some name})
            ~nil:(fun () -> {noinfo with name = Some name}) in
        let objs = Map.add_exn objects.objs ~key:name ~data:obj in
        let objects = {objects with objs; vals} in
        let objects = if public
          then publicize name obj objects else objects in
        put {s with classes = Map.set classes ~key:clsid ~data:objects} >>| fun () ->
        obj in

      fun ?(public=false) ?desc:_ name {Class.name=id} ->
        get () >>= fun ({classes} as s) ->
        let objects = match Map.find classes id with
          | None -> Env.empty_class
          | Some objs -> objs in
        match Map.find objects.objs name with
        | None -> createsym ~public name classes id objects s
        | Some obj when not public -> unchanged obj
        | Some obj ->
          if is_public name obj objects then unchanged obj
          else
            let objects = publicize name obj objects in
            put {s with classes = Map.set classes ~key:id ~data:objects} >>| fun () ->
            obj

    (* any [:] in names here are never treated as separators,
       contrary to [read], where they are, and [do_intern] where
       a leading [:] in a name will be left for keywords *)
    let intern ?public ?desc ?package name cls =
      match package with
      | Some package ->
        do_intern ?public ?desc (Name.Full.create ~package name) cls
      | None ->
        get () >>= fun {Env.package} ->
        let name = {
          package;
          name = Name.normalize_name `Literal ~package name
        } in
        do_intern ?public ?desc name cls

    let uninterned_repr cls obj =
      Format.asprintf "#<%s %a>" cls Oid.pp obj

    let to_string
        {Class.name=cls as cname} {Env.package; classes} obj =
      let cls = if String.equal package (Name.package cls)
        then Name.unqualified cls
        else Name.to_string cls in
      match Map.find classes cname with
      | None -> uninterned_repr cls obj
      | Some {Env.vals} -> match Oid.Tree.find vals obj with
        | Some {name = Some fname} -> if String.equal fname.package package
          then fname.name
          else Name.Full.to_string fname
        | _  -> uninterned_repr cls obj

    let repr cls obj =
      if is_null obj then !!"nil"
      else
        get () >>| fun env ->
        to_string cls env obj

    let read cls = function
      | "nil" -> !!(null cls)
      | input ->
        try
          Scanf.sscanf input "#<%s %s@>" @@ fun _ obj ->
          Knowledge.return (Oid.of_string obj)
        with _ ->
          get () >>= fun {Env.package} ->
          do_intern (Name.Full.read ~package input) cls

    let cast : type a b. (a obj, b obj) Type_equal.t -> a obj -> b obj =
      fun Type_equal.T x -> x

    let id x = Oid.to_int63 x

    module type S = sig
      type t [@@deriving sexp]
      include Base.Comparable.S with type t := t
      include Binable.S with type t := t
    end

    let derive : type a. (a,_) cls ->
      (module S
        with type t = a obj
         and type comparator_witness = a ord) = fun _ ->
      let module Comparator = struct
        type t = a obj
        let sexp_of_t = Oid.sexp_of_t
        let t_of_sexp = Oid.t_of_sexp
        type comparator_witness = a ord
        let comparator = Oid.comparator
      end in
      let module R = struct
        include Comparator
        include Binable.Of_binable_with_uuid(Oid)(struct
            type t = a obj
            let to_binable = Fn.id
            let of_binable = Fn.id
            let caller_identity = Bin_shape.Uuid.of_string "97c4dd90-34db-4ebb-a8b9-43b75164144e"
          end) 
        include Base.Comparable.Make_using_comparator(Comparator)
      end in
      (module R)
  end

  type conflict += Non_monotonic_update of {
      slot : Name.t;
      repr : string;
      error : Conflict.t;
      trace : Stdlib.Printexc.raw_backtrace;
    }

  let () = Conflict.register_printer (function
      | Non_monotonic_update {slot; repr; error; trace} ->
        Option.some @@
        Format.asprintf
          "Unable to update the slot %a of %s,\n%a\n\
           Backtrace:\n%s"
          Name.pp slot repr Conflict.pp error
          (Stdlib.Printexc.raw_backtrace_to_string trace)
      | _ -> None)


  let non_monotonic slot obj error trace =
    Object.repr (Slot.cls slot) obj >>= fun obj ->
    Knowledge.fail (Non_monotonic_update {
        slot = Slot.name slot;
        repr = obj;
        error;
        trace;
      })

  let commit : type a p. (a,p) slot -> a obj -> p -> unit Knowledge.t =
    fun slot obj x ->
    get () >>= function {classes} as s ->
      let {Env.vals} as objs =
        match Map.find classes slot.cls.name with
        | None -> Env.empty_class
        | Some objs -> objs in
      try put {
          s with classes = Map.set classes ~key:slot.cls.name ~data:{
          objs with
          vals = Oid.Tree.update_with vals obj
              ~nil:(fun () -> {noinfo with data = Record.(put slot.key empty x)} )
              ~has:(fun info ->
                  match Record.commit slot.dom slot.key info.data x with
                  | Ok data -> {info with data}
                  | Error err -> raise (Record.Merge_conflict err))}}
      with Record.Merge_conflict err ->
        non_monotonic slot obj err @@
        Stdlib.Printexc.get_raw_backtrace ()

  let notify {Slot.watchers} obj data =
    Hashtbl.data watchers |>
    Knowledge.List.iter ~f:(fun {Slot.run} ->
        run obj data)

  let provide : type a p. (a,p) slot -> a obj -> p -> unit Knowledge.t =
    fun slot obj x ->
    if Object.is_null obj || Domain.is_empty slot.dom x
    then Knowledge.return ()
    else
      commit slot obj x >>= fun () ->
      notify slot obj x


  let pids = ref Pid.zero

  type conflict += Empty : ('a,'b) slot -> conflict
                | Reject : conflict

  let reject () = Knowledge.fail Reject
  let guard cnd = if not cnd
    then reject ()
    else Knowledge.return ()
  let proceed ~unless:cnd = guard (not cnd)
  let on cnd yes = if cnd
    then yes
    else reject ()
  let unless cnd no = if cnd
    then reject ()
    else no

  let with_empty ~missing scope =
    Knowledge.catch (scope ())
      (function Empty _ | Reject -> Knowledge.return missing
              | other -> Knowledge.fail other)

  let register_watcher (type a b)(s : (a,b) slot) run =
    Pid.incr pids;
    let pid = !pids in
    Hashtbl.add_exn s.watchers ~key:pid ~data:{run; pid};
    pid

  let register_promise (type a b)(s : (a,b) slot) run =
    Pid.incr pids;
    let pid = !pids in
    Hashtbl.add_exn s.promises ~key:pid ~data:{run; pid};
    pid

  let remove_promise (s : _ slot) pid =
    Hashtbl.remove s.promises pid

  let remove_watcher (s : _ slot) pid =
    Hashtbl.remove s.watchers pid

  let wrap (s : _ slot) get obj =
    let missing = Domain.empty s.dom in
    with_empty ~missing @@ fun () ->
    get obj

  let promising s ~promise:get scoped =
    let pid = register_promise s @@ fun obj ->
      wrap s get obj >>= fun x ->
      if Domain.is_empty s.dom x
      then Knowledge.return ()
      else provide s obj x in
    scoped () >>= fun r ->
    remove_promise s pid;
    Knowledge.return r

  let promise s get =
    ignore @@
    register_promise s @@ fun obj ->
    wrap s get obj >>= fun x ->
    if Domain.is_empty s.dom x
    then Knowledge.return ()
    else provide s obj x


  let uid {Slot.name} = name


  type slot_status =
    | Sleep
    | Awoke
    | Ready of Dict.record

  let is_empty {Slot.dom; key} v =
    Domain.is_empty dom (Record.get key dom v)
  [@@inline]

  let status
    : ('a,_) slot -> 'a obj -> slot_status knowledge =
    fun slot obj ->
    objects slot.cls >>| fun {vals} ->
    match Oid.Tree.find_exn vals obj with
    | exception Stdlib.Not_found -> Sleep
    | {data; comp=slots} -> match Map.find slots (uid slot) with
      | Some Work _ -> Awoke
      | other -> match other,Record.is_empty data with
        | Some Work _,_ -> assert false
        | None,true -> Sleep
        | Some Done,true -> Ready Record.empty
        | Some Done,false -> Ready data
        | None,false -> if is_empty slot data then Sleep else Ready data

  let update_slot
    : ('a,_) slot -> 'a obj -> _ -> unit knowledge =
    fun slot obj f ->
    update_objects slot.cls @@ fun ({vals} as objs) ->
    let vals = Oid.Tree.update_with vals obj
        ~nil:(fun () -> {
              noinfo
              with comp = Map.singleton (module Name) (uid slot)
                       (f None)
            })
        ~has:(fun info -> {
              info with
              comp = Map.update info.comp (uid slot) ~f
            }) in
    {objs with vals}

  let enter_slot : ('a,_) slot -> 'a obj -> unit knowledge = fun s x ->
    update_slot s x @@ function
    | Some _ -> assert false
    | None ->  Work {
        waiting = Pid.Tree.empty;
        current = Pid.Tree.empty;
      }

  let leave_slot : ('a,'p) slot -> 'a obj -> unit Knowledge.t = fun s x ->
    update_slot s x @@ function
    | Some (Work _) -> Done
    | _ -> assert false

  let update_work s x f =
    update_slot s x @@ function
    | Some (Work w) -> f w
    | _ -> assert false

  let enter_promise s x p =
    update_work s x @@ fun {waiting; current} ->
    Work {waiting; current = Pid.Tree.set current p ()}

  let leave_promise s x p =
    update_work s x @@ fun {waiting; current} ->
    Work {waiting; current = Pid.Tree.remove current p}

  let enqueue_promises s x =
    update_work s x @@ fun {waiting; current} ->
    Work {current;
          waiting = Pid.Tree.merge current waiting ~f:(fun _ _ _ -> ())}

  let no_work = Env.Work {
      waiting = Pid.Tree.empty;
      current = Pid.Tree.empty;
    }

  let dequeue_waiting
    : ('a,'p) slot -> 'a obj -> _ Knowledge.t = fun s x ->
    map_update_objects s.cls @@ fun ({vals} as objs) k ->
    let {Env.comp=works} as info = Oid.Tree.find_exn vals x in
    Map.find_exn works (uid s) |> function
    | Env.Done -> assert false
    | Env.Work {waiting} ->
      let waiting = Pid.Tree.fold waiting ~init:[] ~f:(fun p () ps ->
          Hashtbl.find_exn s.Slot.promises p :: ps) in
      let info = {info with comp=Map.set works ~key:(uid s) ~data:no_work} in
      let objs = {objs with vals = Oid.Tree.set vals x info} in
      k objs waiting

  let initial_promises {Slot.promises} = Hashtbl.data promises

  let current : type a p. (a,p) slot -> a obj -> p Knowledge.t =
    fun slot id ->
    objects slot.cls >>| fun {Env.vals} ->
    match Oid.Tree.find_exn vals id with
    | exception Stdlib.Not_found -> slot.dom.empty
    | {data} -> Record.get slot.key slot.dom data

  let rec collect_inner
    : ('a,'p) slot -> 'a obj -> _ -> _ =
    fun slot obj promises ->
    current slot obj >>= fun was ->
    Knowledge.List.iter promises ~f:(fun {Slot.run; pid} ->
        enter_promise slot obj pid >>= fun () ->
        run obj >>= fun () ->
        leave_promise slot obj pid) >>= fun () ->
    dequeue_waiting slot obj >>= fun waiting ->
    match waiting with
    | [] -> Knowledge.return ()
    | promises ->
      current slot obj >>= fun now ->
      match slot.dom.order now was with
      | EQ | LT -> Knowledge.return ()
      | GT | NC -> collect_inner slot obj promises

  let collect : type a p. (a,p) slot -> a obj -> p Knowledge.t =
    fun slot id ->
    if Object.is_null id
    then !!(Domain.empty slot.dom)
    else status slot id >>= function
      | Ready v ->
        Knowledge.return @@ Record.get slot.key slot.dom v
      | Awoke ->
        enqueue_promises slot id >>= fun () ->
        current slot id
      | Sleep ->
        enter_slot slot id >>= fun () ->
        collect_inner slot id (initial_promises slot) >>= fun () ->
        leave_slot slot id >>= fun () ->
        current slot id


  let observe s run =
    ignore @@ register_watcher s run

  let observing s ~observe:run scoped =
    let pid = register_watcher s run in
    scoped () >>= fun r ->
    remove_watcher s pid;
    Knowledge.return r

  let require (slot : _ slot) obj =
    collect slot obj >>= fun x ->
    if (Domain.is_empty slot.dom x)
    then Knowledge.fail (Empty slot)
    else !!x

  let resolve slot obj =
    collect slot obj >>| Opinions.choice

  let suggest agent slot obj x =
    current slot obj >>= fun opinions ->
    provide slot obj (Opinions.add agent x opinions)

  let wrap_opinion get obj =
    with_empty ~missing:None @@ fun () ->
    get obj >>| Option.some

  let propose agent s get =
    ignore @@
    register_promise s @@ fun obj ->
    wrap_opinion get obj >>= function
    | None -> Knowledge.return ()
    | Some opinions -> suggest agent s obj opinions

  let proposing agent s ~propose:get scoped =
    let pid = register_promise s @@ fun obj ->
      wrap_opinion get obj >>= function
      | None -> Knowledge.return ()
      | Some opinions -> suggest agent s obj opinions in
    scoped () >>= fun r ->
    remove_promise s pid;
    Knowledge.return r

  module Domain = struct
    include Domain

    let inspect_obj name x =
      Sexp.Atom (Format.asprintf "#<%s %a>" name Oid.pp x)

    let obj {Class.name} =
      let name = Name.to_string name in
      total ~inspect:(inspect_obj name) ~empty:Oid.zero
        ~order:Oid.compare name
  end
  module Order = Order
  module Persistent = Persistent

  module Symbol = struct
    let intern = Object.intern
    let keyword = keyword_package

    let in_package package f =
      get () >>= function {Env.package=old_package} as s ->
        put {s with package} >>= fun () ->
        f () >>= fun r ->
        update (fun s -> {s with package = old_package}) >>| fun () ->
        r


    exception Import of fullname * fullname [@@deriving sexp_of]

    let intern_symbol name obj cls =
      Knowledge.return Env.{
          cls
          with objs = Map.add_exn cls.objs ~key:name ~data:obj
        }


    (* imports names inside a class.

       All names that [needs_import] will be imported
       into the [package]. If the [package] already had
       the same name but with different value, then a
       [strict] import will raise an error, otherwise it
       will be overwritten with the new value.
    *)
    let import_class ~strict ~package ~needs_import
      : Env.objects -> Env.objects knowledge
      = fun cls ->
        Oid.Tree.to_sequence cls.vals |>
        Knowledge.Seq.fold ~init:cls ~f:(fun cls (obj,(info : Env.info)) ->
            match info.name with
            | None -> Knowledge.return cls
            | Some sym ->
              if not (needs_import cls sym obj)
              then Knowledge.return cls
              else
                let obj' =
                  match Map.find cls.objs {package; name=sym.name} with
                  | None -> Oid.zero
                  | Some obj' -> obj' in
                if not strict || Oid.(obj' = zero || obj' = obj)
                then intern_symbol sym obj cls
                else
                  let info = Oid.Tree.find_exn cls.vals obj' in
                  let sym' = Option.value_exn info.name in
                  Knowledge.fail (Import (sym,sym')))

    let package_exists package = Map.exists ~f:(fun {Env.objs} ->
        Map.existsi objs ~f:(fun ~key:name ~data:_ ->
            String.equal package name.package))

    let name_exists name = Map.exists ~f:(fun {Env.objs} ->
        Map.mem objs name)

    exception Not_a_package of string [@@deriving sexp_of]
    exception Not_a_symbol of fullname [@@deriving sexp_of]

    let check_name classes = function
      | `Pkg pkg -> if package_exists pkg classes
        then Knowledge.return ()
        else Knowledge.fail (Not_a_package pkg)
      | `Sym sym -> if name_exists sym classes
        then Knowledge.return ()
        else Knowledge.fail (Not_a_symbol sym)

    let current = function
      | Some p -> Knowledge.return (Name.normalize_package `Literal p)
      | None -> gets (fun s -> s.package)

    let import ?(strict=false) ?package imports : unit knowledge =
      current package >>= fun package ->
      get () >>= fun s ->
      Knowledge.List.fold ~init:s.classes imports ~f:(fun classes name ->
          let name = match Name.find_separator name with
            | None -> `Pkg name
            | Some _ -> `Sym (Name.Full.read name) in
          let needs_import {Env.pubs} sym obj = match name with
            | `Sym s -> [%compare.equal : fullname] sym s
            | `Pkg p -> match Map.find pubs p with
              | None -> false
              | Some pubs -> Set.mem pubs obj in
          check_name classes name >>= fun () ->
          Map.to_sequence classes |>
          Knowledge.Seq.fold ~init:classes
            ~f:(fun classes (clsid,objects) ->
                import_class ~strict ~package ~needs_import objects
                >>| fun objects ->
                Map.set classes ~key:clsid ~data:objects))
      >>= fun classes -> put {s with classes}

    let package = get () >>| fun {Env.package} -> package
    let set_package name = update @@ fun s -> {s with package = name}
  end

  module Syntax = struct
    include Knowledge.Syntax
    include Knowledge.Let

    let (-->) x p = collect p x
    let (<--) p f = promise p f
    let (//) c s = Object.read c s

    let (-->?) x p =
      collect p x >>= function
      | None -> Knowledge.fail (Empty p)
      | Some x -> !!x

    let (>>=?) x f = {
      run = fun ~reject ~accept s ->
        x.run s
          ~reject
          ~accept:(fun x s ->
              match x with
              | None -> accept None s
              | Some x ->
                (f x).run ~accept ~reject s)
    } [@@inline]
    [@@specialise]

    let (>>|?) x f = {
      run = fun ~reject ~accept s ->
        x.run s
          ~reject
          ~accept:(fun x s -> match x with
              | None -> accept None s
              | Some x -> accept (f x) s)
    } [@@inline]
    [@@specialise]

    let (let*?) = (>>=?)
    let (let+?) = (>>|?)

    let (and+) x y = {
      run = fun ~reject ~accept s ->
        x.run s
          ~reject
          ~accept:(fun x s ->
              y.run s
                ~reject
                ~accept:(fun y s ->
                    accept (x,y) s))
    } [@@inline]
    [@@specialise]

    let (and*) = (and+)


    let (.$[]) v s = Value.get s v
    let (.$[]<-) v s x = Value.put s v x

    let (.?[]) v s = match v.$[s] with
      | Some v -> !!v
      | None -> Knowledge.fail (Empty s)

    let (.![]) v s =
      let r = v.$[s] in
      if Domain.is_empty (Slot.domain s) r
      then Knowledge.fail (Empty s)
      else !!r
  end

  module type S = sig
    include Monad.S with type 'a t = 'a knowledge
                     and module Syntax := Syntax
    include Monad.Fail.S with type 'a t := 'a knowledge
                          and type 'a error = conflict
  end
  include (Knowledge : S)


  let compute_value
    : type a p . (a,p) cls -> p obj -> unit knowledge
    = fun cls obj ->
      Slot.enum cls |>
      Base.List.filter ~f:(function Slot.Pack {promises} ->
          not (Hashtbl.is_empty promises)) |>
      List.iter ~f:(fun (Slot.Pack s) ->
          ignore_m @@ collect s obj)

  let get_value cls obj =
    compute_value cls obj >>= fun () ->
    objects cls >>| fun {Env.vals} ->
    match Oid.Tree.find_exn vals obj with
    | exception Stdlib.Not_found -> Value.empty cls
    | {data=x} -> Value.create cls x

  let run cls obj s = (obj >>= get_value cls).run s
      ~reject:(fun err -> Error err)
      ~accept:(fun x s -> Ok (x,s))

  let pp_fullname ~package ppf {package=p; name} =
    if String.equal package p
    then Format.fprintf ppf "%s" name
    else Format.fprintf ppf "%s:%s" p name

  let pp_state ppf {Env.classes; package} =
    Format.fprintf ppf "@[<v0>(in-package %s)@;" package;
    Map.iteri classes ~f:(fun ~key:name ~data:{vals} ->
        if not (Oid.Tree.is_empty vals) then begin
          Format.fprintf ppf "(in-class %a)@;"
            (pp_fullname ~package) (Name.full name);
          Format.fprintf ppf "@[<v>";
          Oid.Tree.iter vals ~f:(fun oid {data; name} ->
              if not (Dict.is_empty data) then
                let () = match name with
                  | None ->
                    Format.fprintf ppf "@[<hv2>(%a@ " Oid.pp oid
                  | Some name ->
                    Format.fprintf ppf "@[<hv2>(%a@ "
                      (pp_fullname ~package) name in
                Format.fprintf ppf "%a)@]@;"
                  Record.pp_hum (Dict.sexp_of_t data));
          Format.fprintf ppf "@]"
        end);
    Format.fprintf ppf "@]";


  module Io = struct
    type version = V1 | V2 [@@deriving bin_io]

    module List = Base.List

    type data = {
      key : Oid.t;
      sym : fullname option;
      data : (Name.t * string) array;
      comp : Name.t list;
    } [@@deriving bin_io]

    type v1 = data list [@@deriving bin_io]
    type v2 = Oid.t * v1 [@@deriving bin_io]
    type 'a objects = 'a [@@deriving bin_io]
    type 'a payload = (Name.t * 'a) list [@@deriving bin_io]

    type 'a canonical = {
      version : version;
      payload : 'a payload;
    } [@@deriving bin_io]

    let magic = "CMU:KB"

    let check_magic data =
      let len = String.length magic in
      if String.(Bigstring.To_string.subo ~len data <> magic)
      then invalid_arg "Not a valid knowledge base";
      len

    let make_value data =
      let init = Record.empty in
      Array.fold data ~init ~f:(fun record (name,data) ->
          match Hashtbl.find Record.io name with
          | None -> record
          | Some {Record.reader=read} ->
            read data record)

    let expand_comp comp =
      List.fold comp
        ~init:(Map.empty (module Name))
        ~f:(fun works slot ->
            Map.add_exn works ~key:slot ~data:Env.Done)

    let add_object
        ({Env.vals; objs} as self)
        {key; sym; data; comp} =
      let self = {
        self with vals = Oid.Tree.set vals key {
          data = make_value data;
          comp = expand_comp comp;
          name = sym;
        }
      } in
      match sym with
      | None -> self
      | Some s -> {
          self with
          objs = Map.add_exn objs ~key:s ~data:key;
        }

    let names_in_syms = Oid.Tree.fold
        ~init:(Set.empty (module String))
        ~f:(fun _ {package;name} names ->
            Set.add (Set.add names package) name)


    (* let names = Map.fold
     *     ~init:(Set.empty (module String))
     *     ~f:(fun ~key:_ ~data:{Env.syms} names ->
     *         Set.union names @@
     *         names_in_syms syms) *)

    let serialize_record record =
      let fields = Dict.foreach record ~init:[] {
          visit = fun k _ xs ->
            let name = Record.Key.name k in
            match Hashtbl.find Record.io name with
            | None -> xs
            | Some {writer} -> match writer record with
              | None -> xs
              | Some data -> (name,data) :: xs
        } in
      let result = Array.of_list fields in
      Array.sort result ~compare:(fun (k1,_) (k2,_) ->
          Name.compare k1 k2);
      result

    let collect_comps comp oid =
      match Oid.Tree.find comp oid with
      | None -> []
      | Some works -> Map.keys works

    let to_canonical {Env.classes} : v2 canonical =
      let payload =
        Map.to_alist classes |>
        List.map ~f:(fun (cid, {Env.vals; last}) ->
            let data =
              Oid.Tree.to_list vals |>
              List.filter_map ~f:(fun (oid,{Env.data; name; comp}) ->
                  let data = serialize_record data in
                  let comp = Map.keys comp in
                  if Array.is_empty data && Option.is_none name
                  then None
                  else Some {key=oid; sym=name; data; comp}) in
            cid,(last,data)) in {
        version = V2;
        payload;
      }

    let init_last : state -> state = fun state -> {
        state with
        classes = Map.map state.classes ~f:(fun cls -> {
              cls with
              last = match Oid.Tree.max_elt cls.vals with
                | None -> cls.last
                | Some (k,_) -> Oid.succ k
            })
      }

    let of_canonical_v1 {payload} =
      let init = Map.empty (module Name) in
      let classes =
        List.fold payload ~init ~f:(fun state (cid,objs) ->
            Map.add_exn state ~key:cid
              ~data:(List.fold objs ~f:add_object
                       ~init:Env.empty_class)) in
      init_last {empty with classes}

    let of_canonical_v2 {payload} =
      let init = Map.empty (module Name) in
      let classes =
        List.fold payload ~init ~f:(fun state (cid,(last,objs)) ->
            let init = {
              Env.empty_class with last
            } in
            Map.add_exn state ~key:cid
              ~data:(List.fold objs ~f:add_object
                       ~init)) in
      {empty with classes}


    let of_bigstring data =
      let pos_ref = ref (check_magic data) in
      let version = bin_read_version data ~pos_ref in
      match version with
      | V1 -> of_canonical_v1 {
          version;
          payload = bin_read_payload bin_read_v1 data ~pos_ref
        }
      | V2 -> of_canonical_v2 {
          version;
          payload = bin_read_payload bin_read_v2 data ~pos_ref
        }

    let load path =
      let fd = Unix.openfile path ~mode: Unix.[O_RDONLY] ~perm: 0o400 in
      try
        let data =
          Bigarray.array1_of_genarray @@
          Unix.map_file fd
            Bigarray.char Bigarray.c_layout ~shared:false [| -1 |]in
        let r = of_bigstring data in
        Unix.close fd;
        r
      with exn ->
        Unix.close fd; raise exn

    let blit_canonical_to_bigstring repr buf =
      Bigstring.From_string.blito ~src:magic ~dst:buf ();
      let pos = String.length magic in
      let _p = bin_write_canonical bin_write_v2 ~pos buf repr in
      ()

    let to_bigstring state =
      let repr = to_canonical state in
      let size = String.length magic +
                 bin_size_canonical bin_size_v2 repr in
      let data = Bigstring.create size in
      blit_canonical_to_bigstring repr data;
      data

    let save state path =
      let repr = to_canonical state in
      let size = String.length magic +
                 bin_size_canonical bin_size_v2 repr in
      let fd = Unix.openfile path ~mode: Unix.[O_RDWR; O_CREAT; O_TRUNC] ~perm: 0o660 in
      try
        let dim = [|size |]in
        let buf =
          Bigarray.array1_of_genarray @@
          Unix.map_file fd Bigarray.char Bigarray.c_layout ~shared:true dim in
        blit_canonical_to_bigstring repr buf;
        Unix.close fd
      with exn ->
        Unix.close fd;
        raise exn
  end

  let save = Io.save
  and load = Io.load
  and to_bigstring = Io.to_bigstring
  and of_bigstring = Io.of_bigstring

  let objects cls = objects cls >>| fun {vals} ->
    Sequence.of_list (Oid.Tree.keys vals)

  module Context = struct
    type 'a var = {
      nil : 'a knowledge;
      key : 'a Dict.Key.t;
    }

    let declare ?(inspect=sexp_of_opaque) ?package name init =
      let name = Name.create ?package name in {
        nil = init;
        key = Dict.Key.create ~name inspect;
      }

    let set {key} x = update @@ fun s -> {
        s with context = Dict.set key x s.context
      }

    let get {key; nil} = get () >>= fun {context=s} ->
      match Dict.find key s with
      | None -> nil
      | Some x -> !!x

    let update v f =
      get v >>= fun x ->
      set v (f x)

    let with_var v x f =
      get v >>= fun x' ->
      set v x >>= fun () ->
      f () >>= fun r ->
      set v x' >>| fun () ->
      r
  end

  module Rule = struct
    type def = Registry.def
    type doc = Registry.doc
    let declare = Registry.start_rule
    let require {Slot.name} = Registry.rule_require name
    let provide {Slot.name} = Registry.rule_provide name
    let dynamic = Registry.rule_dynamic
    let comment = Registry.rule_comment
  end

  module Conflict = Conflict
  module Agent = Agent
  type 'a opinions = 'a Opinions.t
  type agent = Agent.t
  let sexp_of_conflict = Conflict.sexp_of_t
  module Name = Name
  type name = Name.t
  module Documentation = Documentation

  module Enum = struct
    module type S = sig
      type t
      val declare : ?package:string -> string -> t
      val read : ?package:string -> string -> t
      val name : t -> Name.t
      val unknown : t
      val is_unknown : t -> bool
      val domain : t domain
      val persistent : t persistent
      val hash : t -> int
      val members : unit -> t list


      include Base.Comparable.S with type t := t
      include Binable.S with type t := t
      include Stringable.S with type t := t
      include Pretty_printer.S with type t := t
      include Sexpable.S with type t := t
    end

    module Make() = struct
      type t = Name.t [@@deriving bin_io, sexp]

      let unknown = Name.of_string ":unknown"
      let elements = Hash_set.of_list (module Name) [unknown]
      let declare ?package name =
        let name = Name.create ?package name in
        if Hash_set.mem elements name
        then invalid_argf
            "Enum.declare: the element %s is already declared \
             please choose a unique name" (Name.to_string name) ();
        Hash_set.add elements name;
        name

      let read ?package name =
        let name = Name.read ?package name in
        if not (Hash_set.mem elements name)
        then invalid_argf "Enum.read: %s is not a member of the given \
                           enumeration." (Name.to_string name) ();
        name

      let name x = x
      let is_unknown = Name.equal unknown
      let hash = Name.hash
      let members () = Hash_set.to_list elements
      include Base.Comparable.Make(Name)
      include (Name : Stringable.S with type t := t)
      include (Name : Pretty_printer.S with type t := t)
      let domain = Domain.flat "enum"
          ~inspect:sexp_of_t
          ~empty:unknown
          ~equal
      let persistent = Persistent.name
    end
  end
end

type 'a knowledge = 'a Knowledge.t
