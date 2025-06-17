(*******************************************************************************
 * electrod - a model finder for relational first-order linear temporal logic
 * 
 * Copyright (C) 2016-2024 ONERA
 * Authors: Julien Brunel (ONERA), David Chemouil (ONERA)
 * 
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 * 
 * SPDX-License-Identifier: MPL-2.0
 * License-Filename: LICENSE.md
 ******************************************************************************)

open Containers

(*$
  inject

  open Test
*)

module TS = Tuple.Set

type t = TS.t

let pp out b =
  Fmtc.pf out "@[<hov 2>{";
  TS.pp (* ~start:"" ~stop:"" *) ~pp_sep:Fmtc.(const string " ") Tuple.pp out b;
  Fmtc.pf out "}@]"

module P = Intf.Print.Mixin (struct
  type nonrec t = t

  let pp = pp
end)

include P

let to_list = TS.elements
let to_iter = TS.to_iter
let of_iter = TS.of_iter
let empty = TS.empty

let of_tuples tuples =
  match tuples with
  | [] -> empty
  | t :: ts ->
      let ar = Tuple.arity t in
      assert (List.for_all (fun t2 -> Tuple.arity t2 = ar) ts);
      TS.of_list tuples

let is_empty = TS.is_empty
let inferred_arity b = if is_empty b then 0 else Tuple.arity @@ TS.choose b
let singleton = TS.singleton
let add = TS.add
let tuples t = t
let inter b1 b2 = TS.inter b1 b2
let size bnd = TS.cardinal bnd
let subset b1 b2 = TS.subset b1 b2
let equal b1 b2 = TS.equal b1 b2

(* |> Fun.tap (fun res -> *)
(*       Msg.debug *)
(*         (fun m -> m "equal %a %a -> %B" *)
(*                     pp b1 pp b2 res)) *)

let compare b1 b2 = TS.compare b1 b2

let product b1 b2 =
  let prod =
    Iter.product (TS.to_iter b1) (TS.to_iter b2)
    |> Iter.map Fun.(uncurry Tuple.( @@@ ))
    |> TS.of_iter
  in
  assert (TS.cardinal prod = TS.cardinal b1 * TS.cardinal b2);
  prod

let union b1 b2 = TS.union b1 b2
let diff = TS.diff
let map f ts = TS.to_iter ts |> Iter.map f |> TS.of_iter
let filter = TS.filter

(*$Q transpose
  any_tupleset (fun ts -> \
  let ar = inferred_arity ts in\
  Q.assume (ar = 2 || ar = 0);\
  equal ts (transpose @@ transpose ts))
*)
let transpose b =
  let ar = inferred_arity b in
  assert (ar = 2 || ar = 0);
  map Tuple.transpose b

(* r ++ s (so we need the first column of s) *)
let override r s =
  let in_r_but_not_in_s1 =
    filter
      (fun tr ->
        not
        @@ TS.exists (fun ts1 -> Tuple.(Atom.equal (ith 0 tr) (ith 0 ts1))) s)
      r
  in
  TS.union s in_r_but_not_in_s1

(* [s <: r] *)
let lproj s r = filter (fun tr -> TS.mem Tuple.([ ith 0 tr ] |> of_list1) s) r
let rproj r s = lproj s @@ transpose r
let diagonal b = map Tuple.(fun e -> e @@@ e) b

(*$Q join
  any_tupleset1 (fun ts -> \
  Q.assume (size ts <> 0);\
  let diag = diagonal ts in\
  equal diag @@ join diag diag\
  )
*)
let join b1 b2 =
  let module S = Iter in
  let ar1 = inferred_arity b1 in
  let ar2 = inferred_arity b2 in
  assert (ar1 <> 1 || ar2 <> 1);
  let s1 = to_iter b1 in
  let s2 = to_iter b2 in
  S.product s1 s2
  |> S.filter_map (fun (t1, t2) ->
         if Atom.equal (Tuple.ith (ar1 - 1) t1) (Tuple.ith 0 t2) then
           Some (Tuple.join t1 t2)
         else None)
  |> of_iter

let transitive_closure b =
  let ar = inferred_arity b in
  assert (ar = 2 || ar = 0);
  if ar = 0 then b
  else
    let old = ref b in
    let cur = ref (union b (join b b)) in
    let b_to_the_k = ref (join b b) in
    while not @@ TS.equal !old !cur do
      old := !cur;
      b_to_the_k := join b !b_to_the_k;
      cur := union !cur !b_to_the_k
      (* Msg.debug (fun m -> *)
      (*     m "current 2 =  %a " pp !cur); *)
      (* Msg.debug (fun m -> *)
      (*     m "old 2 =  %a " pp !old); *)
      (* Msg.debug (fun m -> m "egalité? %b " (TS.equal !old !cur)) *)
    done;
    !cur

(*$Q transitive_closure_is
  any_tupleset2 (fun ts -> \
  equal (transitive_closure_is ts) (transitive_closure ts)\
  )
*)
(* computes the transitive closure of tue tuple set b using iterative squares *)
let transitive_closure_is b =
  let ar = inferred_arity b in
  assert (ar = 2 || ar = 0);
  if ar = 0 then b
  else
    let old = ref b in
    let cur = ref (union b (join b b)) in
    while not @@ TS.equal !old !cur do
      old := !cur;
      cur := union !cur (join !cur !cur)
      (* Msg.debug (fun m -> *)
      (*     m "current 2 =  %a " pp !cur); *)
      (* Msg.debug (fun m -> *)
      (*     m "old 2 =  %a " pp !old); *)
      (* Msg.debug (fun m -> m "egalité? %b " (TS.equal !old !cur)) *)
    done;
    !cur

(* let mem_aux (t, bnd) = *)
(*   TS.mem t bnd *)

(* let mem t bnd = *)
(*   CCCache.(with_cache *)
(*              (lru ~eq:(Pair.equal Tuple.equal equal) *)
(*                 ~hash:(Hash.pair Tuple.hash hash) 597) *)
(*              mem_aux) (t, bnd) *)

let mem t bnd = TS.mem t bnd
let rename atom_renaming ts = TS.map (Tuple.rename atom_renaming) ts

let to_yojson (set : t) : Yojson.Safe.t =
  `List (List.map Tuple.to_yojson (TS.elements set))

let of_yojson (json : Yojson.Safe.t) : (t, string) result =
  match json with
  | `List lst ->
      let rec convert acc = function
        | [] -> Ok (of_tuples acc)
        | x :: xs -> (
            match Tuple.of_yojson x with
            | Ok tuple -> convert (tuple :: acc) xs
            | Error e -> Error ("Tuple.of_yojson failed: " ^ e))
      in
      convert [] lst
  | _ -> Error "Expected a JSON list"

let fold = TS.fold

let iter = TS.iter

let remove = TS.remove

let cardinal = TS.cardinal

(*let rec mapM (go : Tuple.t -> Tuple.t Iter.t) (s : t) : t Iter.t =
    match TS.elements s with
    | [] -> Iter.return TS.empty
    | x :: xs ->
        let rest = mapM go (TS.of_list xs) in
        Iter.flat_map (fun v -> Iter.map (fun tail -> TS.add v tail) rest) (go x)

let rec mapMaybeM (go : Tuple.t -> (Tuple.t option) Iter.t) (s : t) : t Iter.t =
    let addMaybe mbv r = match mbv with
        | None -> r
        | Some v -> TS.add v r in
    match TS.elements s with
    | [] -> Iter.return TS.empty
    | x :: xs ->
        let rest = mapMaybeM go (TS.of_list xs) in
        Iter.flat_map (fun mbv -> Iter.map (fun tail -> addMaybe mbv tail) rest) (go x)

let rec mapCatM (go : Tuple.t -> t Iter.t) (s : t) : t Iter.t =
    match TS.elements s with
    | [] -> Iter.return TS.empty
    | x :: xs ->
        let rest = mapCatM go (TS.of_list xs) in
        Iter.flat_map (fun vs -> Iter.map (fun tail -> TS.union vs tail) rest) (go x)*)

let elements = TS.elements

let raw_binop (o : Raw.raw_bin) : t -> t -> t =
    match o with
    | `Union -> union
    | `Inter -> inter
    | `Diff -> diff
    | `Join -> product