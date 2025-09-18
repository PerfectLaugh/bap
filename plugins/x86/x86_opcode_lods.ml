open Core

type lods = [ `LODSB | `LODSW | `LODSD | `LODSQ ]
[@@deriving bin_io, sexp, compare, enumerate]
