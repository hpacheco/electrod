open Containers

type t = (Valuations.t list) option
    [@@deriving yojson]

let empty = None

let is_empty vs = match vs with
    | None -> true
    | Some _ -> false

let size vs = match vs with
    | None -> 0
    | Some xs -> List.length xs

let equal b1 b2 = match b1,b2 with
    | None, None -> true
    | Some x1, Some x2 -> List.equal Valuations.equal x1 x2
    | _, _ -> false

let rename atom_renaming vs = match vs with
    | None -> None
    | Some x -> Some (List.map (Valuations.rename atom_renaming) x)
    
(* indices when a certain tuple is true *)
let indices_of (t:Tuple.t) (vs : t) =
    match vs with
    | None -> []
    | Some xs ->
        CCList.mapi (fun i x -> (i, x)) xs
        |> CCList.filter_map (fun (i, v) -> if Valuations.mem t v then Some i else None)

let of_set vs = match vs with
    | None -> None
    | Some xs -> Some (Valuations.Set.to_list xs)

let to_set vs = match vs with
    | None -> None
    | Some xs -> Some (Valuations.Set.of_list xs)

let apply_multiplicity (m : Raw.raw_multiplicity) (ts : Tuple_set.t) (vs : t) : t =
    of_set (Valuations_set.apply_multiplicity m ts (to_set vs))
    
let truncate (inf : Tuple_set.t) (sup : Tuple_set.t) (vs : t) : t = 
    of_set (Valuations_set.truncate inf sup (to_set vs))

let product ((ts1,vs1) : Tuple_set.t * t) ((ts2,vs2) : Tuple_set.t * t) : t =
    of_set (Valuations_set.product (ts1,to_set vs1) (ts2,to_set vs2))
    
    
