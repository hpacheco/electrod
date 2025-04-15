open Containers

type t

val equal : t -> t -> bool

val compare : t -> t -> int

val rename : (Atom.t, Atom.t) List.Assoc.t -> t -> t

val add : Tuple.t -> t -> t
val remove : Tuple.t -> t -> t
val removes : Tuple_set.t -> t -> t

val mem : Tuple.t -> t -> bool

module Set : CCSet.S with type elt = t

val to_yojson : t -> Yojson.Safe.t
val of_yojson : Yojson.Safe.t -> (t, string) result

val make_one : Tuple.t -> t
val make_none : t

val is_one : t -> bool
val is_lone : t -> bool
val is_some : t -> bool

val all_valuations : Tuple_set.t -> Set.t

val product : t -> t -> t

val product_right : Tuple_set.t -> t -> [ `Lone | `One | `Some ] -> Tuple_set.t -> t Iter.t
val product_left : Tuple_set.t -> [ `Lone | `One | `Some ] -> Tuple_set.t -> t -> t Iter.t