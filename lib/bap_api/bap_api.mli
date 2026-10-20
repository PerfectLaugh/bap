(** An interface to the api pass.

    Api pass will apply a high level model of a program [api] to a low level
    representation, i.e., the [program term].

    The module is actually a static registry of language processors, that will
    be applied by the api pass.

    The language processors are provide by plugins supporting corresponding
    languages. Sometimes an abi information is required to apply the api, so the
    processors are actually provided by even lower level modules, that supports
    specific architectures. *)

open Core
open Bap.Std

type filename = string
type api = string

(** Language processor interface. *)
module type S = sig
  type t

  val language : string
  (** [language] a name of a language, e.g., ["C"] *)

  val parse : (api -> filename option) -> api list -> t Or_error.t
  (** [parse get_api apis] creates a language processor from a list of api.
      Function [get_api api] must return a name of an existing file, that
      corresponds to the given [api]. The [apis] parameter is a list of [api]
      names. *)

  val mapper : t -> Term.mapper
  (** the processor itself *)
end

type t = (module S)
(** language processor type *)

val process : t -> unit
(** apply the language processor *)

val processors : unit -> t list
(** enumerate all registered language processors *)

val provide_noreturn :
  language:string -> (filename -> string list Or_error.t) -> unit
(** [provide_noreturn ~language read] registers [read], such that [read file]
    lists the names of the functions in the api [file] in the [language] that
    never return.

    @since 2.6.0 *)

val noreturn_reader : string -> (filename -> string list Or_error.t) option
(** [noreturn_reader language] is the reader of the names of the functions that
    never return in the api files in the [language], if one is registered.

    @since 2.6.0 *)

val with_paths : project -> string list -> project
(** [with_paths project paths] the [project], to which the api pass applies the
    api files of the folders [paths] too, e.g., [api/powerpc], whose files are
    in the folders of their languages, e.g., [api/powerpc/c/powerpc.h], besides
    the folders of the options.

    @since 2.6.0 *)

val paths : project -> string list
(** [paths project] the folders, that {!with_paths} added to the [project]

    @since 2.6.0 *)
