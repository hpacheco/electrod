
open Containers

type t = (Valuations.t list) option

val empty : t

val is_empty : t -> bool

val size : t -> int

val equal : t -> t -> bool

val rename : (Atom.t, Atom.t) List.Assoc.t -> t -> t

val to_yojson : t -> Yojson.Safe.t
val of_yojson : Yojson.Safe.t -> (t, string) result

val indices_of : Tuple.t -> t -> int list