open Core

type cdq = [ `CBW | `CWD | `CWDE | `CDQ | `CDQE | `CQO ]
[@@deriving bin_io, sexp, compare, enumerate]
