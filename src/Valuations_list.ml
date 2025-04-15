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