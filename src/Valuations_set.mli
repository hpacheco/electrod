
open Containers

type t = Valuations.Set.t option

val empty : t

val is_empty : t -> bool

val size : t -> int

val equal : t -> t -> bool

val rename : (Atom.t, Atom.t) List.Assoc.t -> t -> t

val to_yojson : t -> Yojson.Safe.t
val of_yojson : Yojson.Safe.t -> (t, string) result

val truncate : Tuple_set.t -> Tuple_set.t -> t -> t

(*val product_with_multiplicities : (Tuple_set.t * t) -> Raw.raw_multiplicity -> Raw.raw_multiplicity -> (Tuple_set.t * t) -> (Tuple_set.t * t)*)
    
val apply_multiplicity : Raw.raw_multiplicity -> Tuple_set.t -> t -> t

val product : (Tuple_set.t * t) -> (Tuple_set.t * t) -> t

val raw_binop : Raw.raw_bin -> Tuple_set.t -> t -> Tuple_set.t -> t -> t