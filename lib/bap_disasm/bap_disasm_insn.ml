open Core
open Bap_core_theory
open Regular.Std
open Bap_types.Std
open Bap_disasm_types

module Insn = Bap_disasm_basic.Insn
let package = "bap"

type must = Must
type may = May
type 'a property = Z.t * string

let known_properties = ref []

let new_property _ name : 'a property =
  let name = sprintf ":%s" name in
  let bit = List.length !known_properties in
  let property = Z.shift_left Z.one bit, name in
  known_properties := !known_properties @ [property];
  property

let prop = new_property ()
(* must be the first one *)
let invalid             = prop "invalid"

let jump                = prop "jump"
let conditional         = prop "cond"
let indirect            = prop "indirect"
let call                = prop "call"
let return              = prop "return"
let barrier             = prop "barrier"
let affect_control_flow = prop "affect-control-flow"
let load                = prop "load"
let store               = prop "store"

module Props = struct
  type t = Z.t [@@deriving compare]
  module Bits = struct
    type t = Z.t
    let to_string = Z.to_bits
    let of_string = Z.of_bits
    let caller_identity = Bin_shape.Uuid.of_string "650d7d34-27fc-46c5-b678-080321d2ef84"
  end
  let empty = Z.zero
  let (+) flags (flag,_) = Z.logor flags flag
  let (-) flags (flag,_) = Z.logand flags (Z.lognot flag)
  let has flags (flag,_) =
    [%compare.equal : t] (Z.logand flags flag) flag
  let set_if cond flag =
    if cond then fun flags -> flags + flag else Fn.id

  module T = struct
    type t = Z.t
    include Sexpable.Of_stringable(Bits)
    include Binable.Of_stringable_with_uuid(Bits)
  end


  let name = snd

  let assoc_of_props props =
    List.map !known_properties ~f:(fun p ->
        name p, has props p)

  let domain = KB.Domain.flat "props"
      ~empty:Z.one ~equal:Z.equal
      ~inspect:(fun props ->
          [%sexp_of: (string * bool) list]
            (assoc_of_props props))

  let persistent = KB.Persistent.of_binable (module T)

  let slot = KB.Class.property ~package:"bap"
      Theory.Semantics.cls "insn-properties" domain
      ~persistent
      ~public:true
      ~desc:"semantic properties of an instruction"
end


type t = Theory.Semantics.t
type op = Op.t [@@deriving bin_io, compare, sexp]

module Slot = struct
  type 'a t = (Theory.Effect.cls, 'a) KB.slot
  let empty = "#undefined"
  let text = KB.Domain.flat "text"
      ~inspect:sexp_of_string ~empty
      ~equal:String.equal

  let delay_t = KB.Domain.optional "delay_t"
      ~inspect:sexp_of_int
      ~equal:Int.equal


  let name = KB.Class.property ~package:"bap"
      Theory.Semantics.cls "insn-opcode" text
      ~persistent:KB.Persistent.string
      ~public:true
      ~desc:"instruction opcode"

  let asm = KB.Class.property ~package:"bap"
      Theory.Semantics.cls "insn-asm" text
      ~persistent:KB.Persistent.string
      ~public:true
      ~desc:"an assembly string"

  let sexp_of_op = function
    | Op.Reg r -> Sexp.Atom (Reg.name r)
    | Op.Imm w -> sexp_of_int64 (Imm.to_int64 w)
    | Op.Fmm w -> sexp_of_float (Fmm.to_float w)


  let ops_domain = KB.Domain.optional "insn-ops"
      ~equal:[%compare.equal: Op.t array]
      ~inspect:[%sexp_of: op array]

  let ops_persistent = KB.Persistent.of_binable (module struct
      type t = Op.t array option [@@deriving bin_io]
    end)

  let ops = KB.Class.property ~package:"bap"
      Theory.Semantics.cls "insn-ops" ops_domain
      ~persistent:ops_persistent
      ~public:true
      ~desc:"an array of instruction operands"

  let delay = KB.Class.property ~package:"bap"
      Theory.Semantics.cls "insn-delay" delay_t
      ~persistent:(KB.Persistent.of_binable (module struct
                     type t = int option [@@deriving bin_io]
                   end))
      ~public:true
      ~desc:"the length of the delay slot"

  type KB.conflict += Jump_vs_Move

  let dests =
    let empty = Some (Set.empty (module Theory.Label)) in
    let order x y : KB.Order.partial = match x,y with
      | Some x,_ when Set.is_empty x -> LT
      | _,Some x when Set.is_empty x -> GT
      | None,None -> EQ
      | None,_ | _,None -> NC
      | Some x, Some y ->
        if Set.equal x y then EQ else
        if Set.is_subset x ~of_:y then LT else
        if Set.is_subset y ~of_:x then GT else NC in
    let join x y = match x,y with
      | None,None -> Ok None
      | None,Some x |Some x,None ->
        if Set.is_empty x then Ok None
        else Error Jump_vs_Move
      | Some x, Some y -> Ok (Some (Set.union x y)) in
    let module IO = struct
      module Set = Set.Make_binable_using_comparator(Theory.Label)
      type t = Set.t option [@@deriving bin_io, sexp_of]
    end in
    let inspect = IO.sexp_of_t in
    let data = KB.Domain.define ~empty ~order ~join ~inspect "dest-set" in
    let persistent = KB.Persistent.of_binable (module IO) in
    KB.Class.property ~package:"bap" Theory.Semantics.cls
      "insn-dests" data
      ~persistent
      ~public:true
      ~desc:"a set of destinations of a control-flow instruction"


  type KB.Conflict.t += Different_sizes

  let subs =
    let dom = Theory.Semantics.domain in
    let open KB.Order in
    let exception Escape of KB.Conflict.t in
    let order x y = match x,y with
      | [||],[||] -> EQ
      | [||],_ -> LT
      | _,[||] -> GT
      | xs, ys ->
        if Array.length xs <> Array.length ys then NC
        else Array.fold2_exn xs ys ~init:EQ ~f:(fun result x y ->
            match result with
            | NC -> NC
            | _ -> match result, KB.Domain.order dom x y with
              | EQ, GT -> GT
              | EQ, LT -> LT
              | r, r' -> if Poly.equal r r' then r' else NC) in
    let join xs ys = match xs, ys with
      | [||],x | x,[||] -> Ok x
      | xs, ys ->
        try
          if Array.length xs <> Array.length ys
          then Error Different_sizes
          else Result.return @@ Array.map2_exn xs ys ~f:(fun x y ->
              match KB.Domain.join dom x y with
              | Ok z -> z
              | Error problem -> raise (Escape problem))
        with Escape problem -> Error problem in
    let inspect xs =
      Sexp.List (List.map ~f:(KB.Domain.inspect dom)
                   (Array.to_list xs)) in
    let domain = KB.Domain.define ~empty:[||] "instructions"
        ~order ~join ~inspect in
    KB.Class.property Theory.Semantics.cls "subinstructions"
      ~package:"bap"
      ~public:true
      ~desc:"a sequence of subinstructions"
      ~persistent:(KB.Persistent.of_binable (module struct
                     type t = Theory.Semantics.t array [@@deriving bin_io]
                   end))
      domain
end

module Analyzer = struct
  module Effects = Set.Make(struct
      type t = Kind.t [@@deriving compare, sexp]
    end)
  type vis = {
    jump : bool;
    cond : bool;
    indirect : bool;
  }

  let no_jumps = {jump=false;cond=false;indirect=false}

  let analyzer =
    let jump ?(cond=false) v = { v with jump = true; cond } in
    let conditional v = jump ~cond:true v in
    let indirect f v = f { v with indirect=true } in
    object
      inherit [Effects.t * vis] Stmt.visitor as super
      method! enter_store ~mem:_ ~addr:_ ~exp:_ _ _ (effs,jumps) =
        Set.add effs `May_store,jumps
      method! enter_load ~mem:_ ~addr:_ _ _ (effs,jumps) =
        Set.add effs `May_load,jumps
      method! enter_jmp ex (effs,jumps) = effs,match ex with
        | Bil.Int _ when under_condition -> conditional jumps
        | Bil.Int _ -> jump jumps
        | _ when under_condition -> indirect conditional jumps
        | _ -> indirect jump jumps
      method! enter_stmt s (effs,jumps) = match Bil.(decode call s) with
        | None -> super#enter_stmt s (effs,jumps)
        | Some _ -> Set.add effs `Call, jumps
    end

  let run bil =
    let cons c = Fn.flip @@ if c then Set.add else Fn.const in
    let effs,jump = analyzer#run bil (Effects.empty,no_jumps) in
    if not jump.jump then effs
    else
      cons (not jump.cond) `Unconditional_branch effs |>
      cons jump.cond `Conditional_branch |>
      cons jump.indirect `Indirect_branch
end

let derive_props ?bil insn =
  let bil_effects = match bil with
    | Some bil -> Analyzer.run bil
    | None -> Analyzer.Effects.empty in
  let is = Insn.is insn in
  let is_bil = if Option.is_some bil
    then Set.mem bil_effects else is in
  let is_return = is `Return in
  let is_call = is_bil `Call || is `Call in
  let is_conditional_jump = is_bil `Conditional_branch in
  let is_jump = is_conditional_jump || is_bil `Unconditional_branch in
  let is_indirect_jump = is_bil `Indirect_branch in
  let may_affect_control_flow =
    is_jump ||
    is `May_affect_control_flow in
  let is_barrier = is_jump &&  not is_call && not is_conditional_jump in
  let may_load = is_bil `May_load in
  let may_store = is_bil `May_store in
  Props.empty                                              |>
  Props.set_if is_jump jump                                |>
  Props.set_if is_conditional_jump conditional             |>
  Props.set_if is_indirect_jump indirect                   |>
  Props.set_if is_call call                                |>
  Props.set_if is_return return                            |>
  Props.set_if is_barrier barrier                          |>
  Props.set_if may_affect_control_flow affect_control_flow |>
  Props.set_if may_load load                               |>
  Props.set_if may_store store

let (<--) slot value insn = KB.Value.put slot insn value

let write init ops =
  List.fold ~init ops ~f:(fun init f -> f init)

let set_basic eff insn : t =
  write eff Slot.[
      name <-- Insn.name insn;
      asm <-- Insn.asm insn;
      ops <-- Some (Insn.ops insn);
    ]

let of_basic ?bil insn : t =
  let eff =
    KB.Value.put Bil.slot
      (KB.Value.empty Theory.Semantics.cls)
      (Option.value bil ~default:[]) in
  write (set_basic eff insn) Slot.[
      Props.slot <-- derive_props ?bil insn;
    ]

let with_basic eff insn : t =
  let bil = KB.Value.get Bil.slot eff in
  write (set_basic eff insn) Slot.[
      Props.slot <-- derive_props ~bil insn
    ]


let get = KB.Value.get Props.slot
let put = KB.Value.put Props.slot
let is flag t = Props.has (get t) flag
let may = is
let must flag insn =  put insn Props.(get insn + flag)
let mustn't flag insn = put insn Props.(get insn - flag)
let should = must
let shouldn't = mustn't

let name = KB.Value.get Slot.name
let asm  = KB.Value.get Slot.asm
let bil insn = KB.Value.get Bil.slot insn
let ops s = match KB.Value.get Slot.ops s with
  | None -> [||]
  | Some ops -> ops

let empty = KB.Value.empty Theory.Semantics.cls

module Adt = struct
  let pr fmt = Format.fprintf fmt

  let rec pp_ops ch = function
    | [] -> ()
    | [x] -> pr ch "%a" Op.pp_adt x
    | x :: xs -> pr ch "%a, %a" Op.pp_adt x pp_ops xs

  let props insn =
    List.filter !known_properties ~f:(fun p -> is p insn) |>
    List.map ~f:snd |>
    String.concat ~sep:", "

  let pp ppf insn =
    let name = name insn in
    if String.equal name Slot.empty
    then pr ppf "Undefined()"
    else pr ppf "%s(%a, Props(%s))"
        (String.capitalize name)
        pp_ops (Array.to_list (ops insn))
        (props insn)
end

let pp_adt = Adt.pp

module Trie = struct
  module Key = struct
    type token = string * Op.t array [@@deriving bin_io, compare, sexp]
    type t = token array

    let length = Array.length
    let nth_token = Array.get
    let token_hash = Hashtbl.hash
  end

  module Normalized = Trie.Make(struct
      include Key
      let compare_token (x,xs) (y,ys) =
        let r = compare_string x y in
        if r = 0 then Op.Normalized.compare_ops xs ys else r
      let hash_ops = Array.fold ~init:0
          ~f:(fun h x -> h lxor Op.Normalized.hash x)
      let hash (x,xs) =
        x lxor hash_ops xs
    end)

  let token_of_insn insn = name insn, ops insn
  let key_of_insns = Array.of_list_map ~f:token_of_insn

  include Trie.Make(Key)
end

include Regular.Make(struct
    type t = Theory.Semantics.t [@@deriving sexp, bin_io, compare]
    let hash t = Hashtbl.hash t
    let module_name = Some "Bap.Std.Insn"
    let version = "2.0.0"

    let string_of_ops ops =
      Array.map ops ~f:Op.to_string |> Array.to_list |>
      String.concat ~sep:","

    let pp fmt insn =
      let name = name insn in
      if String.equal name Slot.empty
      then Format.fprintf fmt "%s" name
      else Format.fprintf fmt "%s(%s)" name (string_of_ops (ops insn))
  end)

let pp_asm ppf insn =
  Format.fprintf ppf "%s" (asm insn)


module Seqnum = struct
  type t = int
  let slot = KB.Class.property Theory.Program.cls "seqnum"
      ~public:true
      ~persistent:(KB.Persistent.of_binable (module struct
                     type t = Int.t option [@@deriving bin_io]
                   end))
      ~desc:"the sequential number of a subinstruction"
      ~package:"bap" @@
    KB.Domain.optional "int"
      ~inspect:Int.sexp_of_t
      ~equal:Int.equal

  let freshnum =
    let cls = KB.Class.declare "seqnum-generator" ()
        ~package:"bap" in
    let open KB.Syntax in
    KB.Object.create cls >>| KB.Object.id >>| Int63.to_int_exn

  let label ?package num =
    let open KB.Syntax in
    let s = Format.asprintf "subinstruction#%a" Int.pp num in
    KB.Symbol.intern ?package s Theory.Program.cls >>= fun obj ->
    KB.provide slot obj (Some num) >>| fun () ->
    obj

  let fresh = KB.Syntax.(freshnum >>= label)
end

let () =
  Data.Write.create ~pp:Adt.pp () |>
  add_writer ~desc:"Abstract Data Type pretty printing format"
    ~ver:version "adt";
  Data.Write.create ~pp:pp_asm () |>
  add_writer ~desc:"Target assembly language" ~ver:"1.0" "asm";
  set_default_printer "asm"
