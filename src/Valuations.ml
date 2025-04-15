open Containers

(*let map_keys (f : Tuple.t -> Tuple.t) (m : 'a Tuple.Map.t) : 'a Tuple.Map.t =
    Tuple.Map.fold (fun k v acc -> Tuple.Map.add (f k) v acc) m Tuple.Map.empty*)

(* register only tuples that are true *)
type t = Tuple_set.t

let equal = Tuple_set.equal

let compare = Tuple_set.compare

let rename = Tuple_set.rename

module Set = CCSet.Make (struct
  type nonrec t = t

  let compare = compare
  
end)

let add : Tuple.t -> t -> t = Tuple_set.add

let remove : Tuple.t -> t -> t = Tuple_set.remove

let removes (ts : Tuple_set.t) (xs : t) : t =
    Tuple_set.diff xs ts

let mem : Tuple.t -> t -> bool = Tuple_set.mem

let to_yojson = Tuple_set.to_yojson

let of_yojson = Tuple_set.of_yojson
  
(* when t is true all other tuples must be false *)
let make_one (t : Tuple.t) : t =
    Tuple_set.singleton t
      
(* a valuation where all tuples are false *)
let make_none : t =
    Tuple_set.empty
    
let is_one (xs : t) : bool =
    Tuple_set.cardinal xs = 1
    
let is_lone (xs : t) : bool =
    Tuple_set.cardinal xs <= 1

let is_some (xs : t) : bool =
    Tuple_set.cardinal xs >= 1

let product (b1 : t) (b2 : t) : t =
    let prod =
      Iter.product (Tuple_set.to_iter b1) (Tuple_set.to_iter b2)
      |> Iter.map (Fun.uncurry (Tuple.(@@@)))
      |> Tuple_set.of_iter
    in prod

let all_valuations (ts : Tuple_set.t) : Set.t =
    let rec aux xs = match xs with
        | [] -> Set.singleton Tuple_set.empty
        | y :: ys ->
            let tail = aux ys in
            Set.union (Set.map (Tuple_set.add y) tail) tail
    in
    let res = aux (Tuple_set.to_list ts) in
    Printf.printf "all_valuations TS: %s\n" (Yojson.Safe.to_string (Tuple_set.to_yojson ts));
    Printf.printf "all_valuations RES: %s\n" (Yojson.Safe.to_string (`List (List.map Tuple_set.to_yojson (Set.elements res))));
    res

let rec tuple_right ((t1,b1) : Tuple.t * bool) (m2 : [ `Lone | `One | `Some ]) (ts2 : Tuple_set.t) : t Iter.t =
    match m2 with
    | `One  -> if b1
        then Tuple_set.to_iter ts2 |> Iter.map (fun t2 -> Tuple_set.singleton (Tuple.(@@@) t1 t2))
        else Iter.empty
    | `Lone -> tuple_right (t1,b1) `One ts2 |> Iter.cons Tuple_set.empty
    | `Some -> if b1
        then Tuple_set.map (fun t2 -> Tuple.(@@@) t1 t2) ts2 |> all_valuations |> Set.remove Tuple_set.empty |> Set.to_iter
        else Iter.empty

let rec tuple_left (ts1 : Tuple_set.t) (m1 : [ `Lone | `One | `Some ]) ((t2,b2) : Tuple.t * bool) : t Iter.t =
    match m1 with
    | `One  -> if b2
        then Tuple_set.to_iter ts1 |> Iter.map (fun t1 -> Tuple_set.singleton (Tuple.(@@@) t1 t2))
        else Iter.empty
    | `Lone -> tuple_left ts1 `One (t2,b2) |> Iter.cons Tuple_set.empty
    | `Some -> if b2
        then Tuple_set.map (fun t1 -> Tuple.(@@@) t1 t2) ts1 |> all_valuations |> Set.remove Tuple_set.empty |> Set.to_iter
        else Iter.empty

let to_assoc (ts : Tuple_set.t) (vs : t) : (Tuple.t * bool) list =
    Tuple_set.to_iter ts |> Iter.map (fun t -> (t,Tuple_set.mem t vs)) |> Iter.to_list

let rec tupleMapCatM (go : Tuple.t * bool -> t Iter.t) (s : (Tuple.t * bool) list) : t Iter.t =
    match s with
    | [] -> Iter.return Tuple_set.empty
    | x :: xs ->
        let rest = tupleMapCatM go xs in
        Iter.flat_map (fun vs -> Iter.map (fun tail -> Tuple_set.union vs tail) rest) (go x)

let product_right (ts1 : Tuple_set.t) (v1 : t) (m2 : [ `Lone | `One | `Some ]) (ts2 : Tuple_set.t) : t Iter.t =
    tupleMapCatM (fun tb1 -> tuple_right tb1 m2 ts2) (to_assoc ts1 v1)

let product_left (ts1 : Tuple_set.t) (m1 : [ `Lone | `One | `Some ]) (ts2 : Tuple_set.t) (v2 : t) : t Iter.t =
    tupleMapCatM (fun tb2 -> tuple_left ts1 m1 tb2) (to_assoc ts2 v2)

