open Containers

module VS = Valuations.Set

(* optional because we avoid computing all valuations explicitely when there are no multiplicities *)
type t = VS.t option

let empty = None

let is_empty vs = match vs with
    | None -> true
    | Some _ -> false

let size vs = match vs with
    | None -> 0
    | Some xs -> VS.cardinal xs

let equal b1 b2 = match b1,b2 with
    | None, None -> true
    | Some x1, Some x2 -> VS.equal x1 x2
    | _, _ -> false

let rename atom_renaming vs = match vs with
    | None -> None
    | Some x -> Some (VS.map (Valuations.rename atom_renaming) x)

let vs_map f ts = VS.to_iter ts |> Iter.map f |> VS.of_iter

let vs_to_yojson (set : VS.t) : Yojson.Safe.t =
  `List (List.map Valuations.to_yojson (VS.elements set))

let vs_of_yojson (json : Yojson.Safe.t) : (VS.t, string) result =
  match json with
  | `List lst ->
      let rec convert acc = function
        | [] -> Ok (VS.of_list acc)
        | x :: xs -> (
            match Valuations.of_yojson x with
            | Ok tuple -> convert (tuple :: acc) xs
            | Error e -> Error ("Valuations.of_yojson failed: " ^ e))
      in
      convert [] lst
  | _ -> Error "Expected a JSON list"

let to_yojson (v : t) : Yojson.Safe.t =
  match v with
  | None -> `Null
  | Some x -> vs_to_yojson x  

let of_yojson (json : Yojson.Safe.t) : (t, string) result =
  match json with
  | `Null -> Ok None
  | other -> (
      match vs_of_yojson other with  
      | Ok x -> Ok (Some x)
      | Error e -> Error e
    )

let remove_tuples (inf : Tuple_set.t) (vs : VS.t) : VS.t =
    VS.map (Valuations.removes inf) vs

let truncate (inf : Tuple_set.t) (sup : Tuple_set.t) (vs : t) : t = 
    if Tuple_set.is_empty inf then vs
    else match vs with
    | None -> Some (Valuations.all_valuations (Tuple_set.diff sup inf))
    | Some xs -> Some (remove_tuples inf xs)

(*let vs_product (b1 : VS.t) (b2 : VS.t) : VS.t =
    let prod =
      Iter.product (VS.to_iter b1) (VS.to_iter b2)
      |> Iter.map (Fun.uncurry Valuations.product)
      |> VS.of_iter
    in
    (*Printf.printf "left: %s\n" (Yojson.Safe.to_string (vs_to_yojson b1));
    Printf.printf "right: %s\n" (Yojson.Safe.to_string (vs_to_yojson b2));
    Printf.printf "product: %s\n" (Yojson.Safe.to_string (vs_to_yojson prod));*)
    prod*)

let vs_hproduct (b1 : VS.t) (b2 : VS.t) : VS.t =
    Iter.product (VS.to_iter b1) (VS.to_iter b2)
    |> Iter.map (fun (x1,x2) -> Valuations.union x1 x2)
    |> VS.of_iter
    
let rec make_multiplicity (m : Raw.raw_multiplicity) (ts : Tuple_set.t) : VS.t =
    match m with
    | Some `One -> Tuple_set.fold (fun t acc -> VS.add (Valuations.make_one t) acc) ts VS.empty
    | Some `Lone -> VS.add (Valuations.make_none) (make_multiplicity (Some `One) ts)
    | None -> Valuations.all_valuations ts
    | Some `Some -> VS.remove (Valuations.make_none) (make_multiplicity None ts)

let apply_vs_multiplicity (m : Raw.raw_multiplicity) (vs : VS.t) : VS.t =
    match m with
    | None -> vs
    | Some `One -> VS.filter Valuations.is_one vs
    | Some `Lone -> VS.filter Valuations.is_lone vs
    | Some `Some -> VS.filter Valuations.is_some vs
    
let apply_multiplicity (m : Raw.raw_multiplicity) (ts : Tuple_set.t) (vs : t) : t =
    match vs with
        | None -> (match m with
            | None -> None
            | Some m -> Some (make_multiplicity (Some m) ts))
        | Some vs -> Some (apply_vs_multiplicity m vs)

let tuple_product_right (t1 : Tuple.t) (vs2 : VS.t) : VS.t =
    VS.map (fun v2 -> Valuations.tuple_product_right t1 v2) vs2
    
let tuple_product_left (vs1 : VS.t) (t2 : Tuple.t) : VS.t =
    VS.map (fun v1 -> Valuations.tuple_product_left v1 t2) vs1

let product_right (ts1 : Tuple_set.t) (vs2 : VS.t) : VS.t =
    let rec go xs = match xs with
        | [] -> VS.singleton Valuations.make_none
        | x :: ys -> vs_hproduct (tuple_product_right x vs2) (go ys)
    in go (Tuple_set.to_list ts1)

let product_left (vs1 : VS.t) (ts2 : Tuple_set.t) : VS.t =
    let rec go xs = match xs with
        | [] ->  VS.singleton Valuations.make_none
        | x :: ys -> vs_hproduct (tuple_product_left vs1 x) (go ys)
    in go (Tuple_set.to_list ts2)

let product ((ts1,vs1) : Tuple_set.t * t) ((ts2,vs2) : Tuple_set.t * t) : t =
    match vs1,vs2 with
    | None, None -> None
    | None, Some vs2' -> Some (product_right ts1 vs2')
    | Some vs1', None -> Some (product_left vs1' ts2)
    | Some vs1', Some vs2' ->
        let r = product_right ts1 vs2' in
        let l = product_left vs1' ts2 in
        Some (VS.inter l r)
    
(*    let vs12 = match vs1,vs2 with
        | None, None -> None
        | None, Some vs2' -> let vs1' = Valuations.all_valuations ts1 in Some (vs_product vs1' vs2')
        | Some vs1', None -> let vs2' = Valuations.all_valuations ts2 in Some (vs_product vs1' vs2')
        | Some vs1', Some vs2' -> Some (vs_product vs1' vs2')
    in vs12*)
    
let explicit (ts : Tuple_set.t) (vs : t) : VS.t =
    match vs with
    | None -> Valuations.all_valuations ts
    | Some vs -> vs
    
(*let product_right (ts1 : Tuple_set.t) (vs1 : VS.t) (m2 : [ `Lone | `One | `Some ]) (ts2 : Tuple_set.t) : VS.t =
    Printf.printf "product right VS1: %s\n" (Yojson.Safe.to_string (vs_to_yojson vs1));
    Printf.printf "product right TS2: %s\n" (Yojson.Safe.to_string (Tuple_set.to_yojson ts2));
    VS.to_iter vs1 |> Iter.flat_map (fun v1 -> Valuations.product_right ts1 v1 m2 ts2) |> VS.of_iter

let product_left (ts1 : Tuple_set.t) (m1 : [ `Lone | `One | `Some ]) (ts2 : Tuple_set.t) (vs2 : VS.t) : VS.t =
    VS.to_iter vs2 |> Iter.flat_map (fun v2 -> Valuations.product_left ts1 m1 ts2 v2) |> VS.of_iter

let product_with_multiplicities ((ts1,vs1) : Tuple_set.t * t) (m1 : Raw.raw_multiplicity) (m2 : Raw.raw_multiplicity) ((ts2,vs2) : Tuple_set.t * t) : Tuple_set.t * t =
    let ts12 = Tuple_set.product ts1 ts2 in
    let vs12 = match m1,m2 with
        | None, None -> product (ts1,vs1) (ts2,vs2)
        | None, Some m2 ->
            let r = product_right ts1 (explicit ts1 vs1) m2 ts2 in (*TODO what happens to vs2? check that it is null!*)
            Some r
        | Some m1, None ->
            let l = product_left ts1 m1 ts2 (explicit ts2 vs2) in
            Some l
        | Some m1, Some m2 ->
            let l = product_left ts1 m1 ts2 (explicit ts2 vs2) in
            let r = product_right ts1 (explicit ts1 vs1) m2 ts2 in
            Some (VS.inter l r)
    in (ts12,vs12)*)

(* restrict valuations to a domain of tuples *)
let restrict_with_tuples (vs1 : VS.t) (ts2 : Tuple_set.t) : VS.t =
    VS.map (Tuple_set.inter ts2) vs1

let raw_binop (o : Raw.raw_bin) (ts1 : Tuple_set.t) (vs1 : t) (ts2 : Tuple_set.t) (vs2 : t) : t =
    match vs1,o,vs2 with
    | None, _, None -> None
    | Some vs1, `Inter, None -> Some (restrict_with_tuples vs1 ts2)
    | None, `Inter, Some vs2 -> Some (restrict_with_tuples vs2 ts1)
    | Some vs1, `Diff, None -> Some (remove_tuples ts2 vs1)
    | _ ->
        let evs1 = explicit ts1 vs1 in
        let evs2 = explicit ts2 vs2 in
        (match o with
        | `Union -> Some (VS.union evs1 evs2)
        | `Inter -> Some (VS.inter evs1 evs2)
        | `Diff ->  Some (VS.diff evs1 evs2)
        | `Join ->  failwith "raw_binop: dot of valuations yet unsupported"
        )
    

