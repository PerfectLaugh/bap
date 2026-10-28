type 'a t
type 'a summary = { changes : int; applications : (string * int) list }

val rule : ?operations:string list -> string -> ('a -> 'a option) -> 'a t

val run :
  ?limit:int ->
  key:('a -> string) ->
  equal:('a -> 'a -> bool) ->
  map:(('a -> 'a) -> 'a -> 'a) ->
  'a t list ->
  'a ->
  'a * 'a summary
