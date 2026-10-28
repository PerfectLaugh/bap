open Bap.Std

type edge = { src : tid; dst : tid; condition : exp; jump : jmp term }
type loop = { header : tid; nodes : Tid.Set.t; latches : Tid.Set.t }
type t

val analyze : ?program:program term -> sub term -> t
val entry : t -> tid
val exit : t -> tid
val block : t -> tid -> blk term option
val nodes : t -> Tid.Set.t
val successors : t -> tid -> edge list
val predecessors : t -> tid -> edge list
val dominates : t -> tid -> tid -> bool
val post_dominates : t -> tid -> tid -> bool
val join : t -> tid -> tid -> tid option
val loops : t -> loop list
val loop_at : t -> tid -> loop option
val calls : t -> tid -> jmp term list
val is_exit : t -> tid -> bool
val label : tid -> string
