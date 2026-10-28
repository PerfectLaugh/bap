open Core
open Bap.Std
open Graphlib.Std
module G = Graphlib.Make (Tid) (Unit)

type edge = { src : tid; dst : tid; condition : exp; jump : jmp term }
type loop = { header : tid; nodes : Tid.Set.t; latches : Tid.Set.t }

type t = {
  sub : sub term;
  entry : tid;
  exit : tid;
  nodes : Tid.Set.t;
  edges : edge list Tid.Map.t;
  incoming : edge list Tid.Map.t;
  calls : jmp term list Tid.Map.t;
  dominators : Tid.t tree;
  post_dominators : Tid.t tree;
  loops : loop list;
}

let label tid = sprintf "block_%s" (String.drop_prefix (Tid.to_string tid) 1)
let local sub tid = Option.is_some (Term.find blk_t sub tid)

let always exp =
  match exp with Bil.Int value -> Word.is_one value | _ -> false

let return_target program jump =
  match Jmp.kind jump with
  | Ret target -> Some target
  | Call call when Option.is_none (Call.return call) -> (
      match Call.target call with
      | Direct tid
        when Option.is_none program
             || Option.is_none
                  (Option.bind program ~f:(fun program ->
                       Term.find sub_t program tid)) ->
          Some (Direct tid)
      | Indirect _ -> Some (Call.target call)
      | _ -> None)
  | _ -> None

let destinations program sub blk exit =
  let edges_of_jump jump =
    let source = Term.tid blk in
    let condition = Jmp.cond jump in
    let edge dst = [ { src = source; dst; condition; jump } ] in
    let direct tid = if local sub tid then edge tid else edge exit in
    let label = function Direct tid -> direct tid | Indirect _ -> edge exit in
    match return_target program jump with
    | Some target -> label target
    | None -> (
        match Jmp.kind jump with
        | Goto target | Ret target -> label target
        | Call call -> (
            match Call.return call with
            | Some target -> label target
            | None -> [])
        | Int (_, tid) -> direct tid)
  in
  Term.enum jmp_t blk |> Seq.to_list
  |> List.fold_until ~init:[]
       ~f:(fun edges jump ->
         let condition = Jmp.cond jump in
         match condition with
         | Bil.Int value when Word.is_zero value -> Continue edges
         | _ ->
             let edges = edges @ edges_of_jump jump in
             if always condition then Stop edges else Continue edges)
       ~finish:Fn.id

let call_terms program blk =
  Term.enum jmp_t blk
  |> Seq.filter ~f:(fun jmp ->
      match Jmp.kind jmp with
      | Call _ -> Option.is_none (return_target program jmp)
      | _ -> false)
  |> Seq.to_list

let insert_edge map edge =
  Map.update map edge.src ~f:(function
    | None -> [ edge ]
    | Some edges -> edges @ [ edge ])

let insert_incoming map edge =
  Map.update map edge.dst ~f:(function
    | None -> [ edge ]
    | Some edges -> edges @ [ edge ])

let ancestors tree node = Seq.cons node (Tree.ancestors tree node)

let dominates tree node tid =
  Tid.equal node tid || Seq.exists (Tree.ancestors tree tid) ~f:(Tid.equal node)

let natural_loop preds header latch =
  let rec gather seen node =
    if Set.mem seen node then seen
    else
      let seen = Set.add seen node in
      if Tid.equal node header then seen
      else
        Map.find preds node |> Option.value ~default:[]
        |> List.fold ~init:seen ~f:(fun seen edge -> gather seen edge.src)
  in
  gather (Tid.Set.singleton header) latch

let analyze ?program sub =
  match Term.first blk_t sub with
  | None -> invalid_arg "cannot build a CFG for an empty subroutine"
  | Some entry_blk ->
      let entry = Term.tid entry_blk and exit = Tid.create () in
      let nodes =
        Term.enum blk_t sub
        |> Seq.fold ~init:(Tid.Set.singleton exit) ~f:(fun nodes blk ->
            Set.add nodes (Term.tid blk))
      in
      let edge_list =
        Term.enum blk_t sub |> Seq.to_list
        |> List.concat_map ~f:(fun blk ->
            let edges = destinations program sub blk exit in
            List.filter edges ~f:(fun edge ->
                always edge.condition
                || not
                     (List.exists edges ~f:(fun other ->
                          Tid.equal edge.dst other.dst && always other.condition))))
      in
      let edges = List.fold edge_list ~init:Tid.Map.empty ~f:insert_edge in
      let incoming =
        List.fold edge_list ~init:Tid.Map.empty ~f:insert_incoming
      in
      let graph =
        List.fold edge_list ~init:G.empty ~f:(fun graph edge ->
            G.Edge.insert
              (G.Edge.create (G.Node.create edge.src) (G.Node.create edge.dst)
                 ())
              graph)
      in
      let graph =
        Set.fold nodes ~init:graph ~f:(fun graph node ->
            G.Node.insert (G.Node.create node) graph)
      in
      let dominators = Graphlib.dominators (module G) graph entry in
      let post_dominators =
        Graphlib.dominators ~rev:true (module G) graph exit
      in
      let back_edges : edge list =
        List.filter edge_list ~f:(fun edge ->
            dominates dominators edge.dst edge.src)
      in
      let loops =
        List.fold back_edges ~init:Tid.Map.empty ~f:(fun groups edge ->
            Map.update groups edge.dst ~f:(function
              | None -> [ edge ]
              | Some edges -> edge :: edges))
        |> Map.to_alist
        |> List.map ~f:(fun (header, backedges) ->
            let nodes =
              List.fold backedges ~init:(Tid.Set.singleton header)
                ~f:(fun nodes edge ->
                  Set.union nodes (natural_loop incoming header edge.src))
            in
            ({
               header;
               nodes;
               latches =
                 List.fold backedges ~init:Tid.Set.empty ~f:(fun set edge ->
                     Set.add set edge.src);
             }
              : loop))
        |> List.sort ~compare:(fun (x : loop) (y : loop) ->
            Int.compare (Set.length x.nodes) (Set.length y.nodes))
      in
      let calls =
        Term.enum blk_t sub
        |> Seq.fold ~init:Tid.Map.empty ~f:(fun map blk ->
            Map.set map ~key:(Term.tid blk) ~data:(call_terms program blk))
      in
      {
        sub;
        entry;
        exit;
        nodes;
        edges;
        incoming;
        calls;
        dominators;
        post_dominators;
        loops;
      }

let entry t = t.entry
let exit t = t.exit
let block t tid = Term.find blk_t t.sub tid
let nodes t = Set.remove t.nodes t.exit
let successors t tid = Map.find t.edges tid |> Option.value ~default:[]
let predecessors t tid = Map.find t.incoming tid |> Option.value ~default:[]
let dominates (t : t) = dominates t.dominators

let post_dominates (t : t) node tid =
  Tid.equal node tid
  || Seq.exists (Tree.ancestors t.post_dominators tid) ~f:(Tid.equal node)

let join t x y =
  ancestors t.post_dominators x
  |> Seq.find ~f:(fun candidate -> post_dominates t candidate y)

let loops t = t.loops
let loop_at t tid = List.find t.loops ~f:(fun loop -> Tid.equal loop.header tid)
let calls t tid = Map.find t.calls tid |> Option.value ~default:[]
let is_exit t tid = Tid.equal t.exit tid
