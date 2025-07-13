
open Containers

let unzip_iter iter =
  let a_rev = ref [] in
  let b_rev = ref [] in
  Iter.iter
    (fun (a, b) ->
       a_rev := a :: !a_rev;
       b_rev := b :: !b_rev)
    iter;
  (Iter.of_list (List.rev !a_rev), Iter.of_list (List.rev !b_rev))

type partial_atom = PAtom of Atom.t | PVals of Valuations_list.t * Tuple_set.t
type partial_tuple = partial_atom list

let partial_atom_to_yojson = function
  | PAtom a ->
      `Assoc [("PAtom", Atom.to_yojson a)]
  | PVals (vals, tset) ->
      `Assoc [("PVals", `List [Valuations_list.to_yojson vals; Tuple_set.to_yojson tset])]

let partial_tuple_to_yojson (lst : partial_tuple) : Yojson.Safe.t =
  `List (List.map partial_atom_to_yojson lst)
  
let partial_atom_of_yojson = function
  | `Assoc [("PAtom", j)] ->
      (match Atom.of_yojson j with
       | Ok a -> Ok (PAtom a)
       | Error e -> Error ("PAtom: " ^ e))
  | `Assoc [("PVals", `List [j1; j2])] ->
      (match Valuations_list.of_yojson j1 with
       | Ok v ->
           (match Tuple_set.of_yojson j2 with
            | Ok t -> Ok (PVals (v, t))
            | Error e -> Error ("PVals (Tuple_set): " ^ e))
       | Error e -> Error ("PVals (Valuations_list): " ^ e))
  | _ -> Error "partial_atom_of_yojson: unexpected JSON structure"

let partial_tuple_of_yojson = function
  | `List lst ->
      let rec aux acc = function
        | [] -> Ok (List.rev acc)
        | x :: xs ->
            (match partial_atom_of_yojson x with
             | Ok v -> aux (v :: acc) xs
             | Error e -> Error e)
      in
      aux [] lst
  | _ -> Error "partial_tuple_of_yojson: expected a list"

let to_partial_tuple (t : Tuple.t) : partial_tuple =
    List.map (fun x -> PAtom x) (Tuple.to_list t)

let rec tuple_to_full (t : Tuple.t) (pt : partial_tuple) : Tuple.t =
    let rec tail xs = match xs with
        | [] -> []
        | (PAtom a :: xs) -> List.cons a (tail xs)
        | (PVals _ :: xs) -> failwith "multiple vals: should not happen"
    in let rec go xs = match xs with
        | [] -> []
        | (PAtom a :: xs) -> List.cons a (go xs)
        | (PVals (vs,_) :: xs) -> (Tuple.to_list t) @ tail xs
    in Tuple.of_list1 (go pt)
    
let partial_atom_to_string a = match a with
    | PAtom a -> [Atom.to_string a]
    | PVals (vs,ts) -> List.init (Tuple_set.inferred_arity ts) (fun _ -> "__")
    
let rec partial_vals (t : partial_tuple) : (Valuations_list.t * Tuple_set.t) option = match t with
    | [] -> None
    | (PAtom a :: xs) -> partial_vals xs
    | (PVals (vs,ts) :: xs) -> (match partial_vals xs with
        | None -> Some (vs,ts)
        | Some _ -> failwith "more than one valuation set per variable is unsupported")

let join_partial_tuples (t1 : partial_tuple Iter.t) (t2 : partial_tuple Iter.t) : partial_tuple Iter.t =
    Iter.product t1 t2 |> Iter.map (fun (x,y) -> x @ y)

let split_tuples (n:int) (tuples : Tuple_set.t) : Tuple_set.t * Tuple_set.t =
    let (ls,rs) = Tuple_set.to_iter tuples |> Iter.map (fun t -> Tuple.split t n) |> unzip_iter in
    (Tuple_set.of_iter ls,Tuple_set.of_iter rs)

let rec mk_partial_tuples (s : Scope.sup_t) (tuples : Tuple_set.t) : partial_tuple Iter.t =
  match s with
  | SupNode (ts,vs) -> (match vs with
      | None -> Tuple_set.to_iter (Tuple_set.inter ts tuples) |> Iter.map to_partial_tuple
      | Some vs -> Iter.return [PVals (Some vs,tuples)])
  | SupArrow (s1,s2) ->
      let (tuples1,tuples2) = split_tuples (Scope.sup_arity s1) tuples in
      join_partial_tuples (mk_partial_tuples s1 tuples1) (mk_partial_tuples s2 tuples2)

let tuple_to_string tuple = Fmtc.(str "%a" @@ list ~sep:minus Atom.pp) (Tuple.to_list tuple)

