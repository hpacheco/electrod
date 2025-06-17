
open Containers

type t = (Valuations.t list) option

val empty : t

val is_empty : t -> bool
val is_null : t -> bool

val size : t -> int

val equal : t -> t -> bool

val rename : (Atom.t, Atom.t) List.Assoc.t -> t -> t

val to_yojson : t -> Yojson.Safe.t
val of_yojson : Yojson.Safe.t -> (t, string) result

val indices_of : Tuple.t -> t -> int list

val of_set : Valuations_set.t -> t
val to_set : t -> Valuations_set.t

val truncate : Tuple_set.t -> Tuple_set.t -> t -> t

val apply_multiplicity : Raw.raw_multiplicity -> Tuple_set.t -> t -> t

val product : (Tuple_set.t * t) -> (Tuple_set.t * t) -> t

val explicit : Tuple_set.t -> t -> Valuations.t list

val raw_binop : Raw.raw_bin -> Tuple_set.t -> t -> Tuple_set.t -> t -> t