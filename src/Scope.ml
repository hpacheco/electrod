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
module TS = Tuple_set
module VL = Valuations_list

type inf_t = TS.t
  [@@deriving yojson]

type sup_t
    = SupNode of TS.t * VL.t (* all possible valuations, when there are multiplicities *)
    | SupArrow of sup_t * sup_t (* when there are no multiplicities involved *)
  [@@deriving yojson]

type t = Exact of TS.t | Inexact of inf_t * sup_t
  [@@deriving yojson]

(*let valuations scope = 
    match scope with
    | Exact _ -> VL.empty
    | Inexact (_,vs) -> vs*)

(*let is_enum scope = not @@ VL.is_empty (valuations scope)*)

let rec sup_is_simple s = match s with
    | SupNode (ts,vs) -> Valuations_list.is_empty vs
    | SupArrow (l,r) -> sup_is_simple l && sup_is_simple r

let rec sup_equal s1 s2 = match s1,s2 with
    | SupNode (t1,v1), SupNode (t2,v2) -> TS.equal t1 t2 && VL.equal v1 v2
    | SupArrow (l1,r1), SupArrow (l2,r2) -> sup_equal l1 l2 && sup_equal r1 r2
    | _ -> false

let equal sc1 sc2 =
  match (sc1, sc2) with
  | Exact (ts1), Exact (ts2) -> TS.equal ts1 ts2
  | Exact _, Inexact _ | Inexact _, Exact _ -> false
  | Inexact (l1,s1), Inexact (l2,s2) -> TS.equal l1 l2 && sup_equal s1 s2

let exact (bound) = Exact (bound)

let inexact (l,s) = Inexact (l,s)

let rec sup_arity s = match s with
    | SupNode (t,v) -> TS.inferred_arity t
    | SupArrow (x,y) -> sup_arity x + sup_arity y

let rec sup_tuples s = match s with
    | SupNode (t,v) -> t
    | SupArrow (x,y) -> TS.product (sup_tuples x) (sup_tuples y)

let inferred_arity = function
  | Exact (b) -> TS.inferred_arity b
  | Inexact (_,s) -> sup_arity s

let included_in tupleset = function
  | Exact exact -> TS.subset tupleset exact
  | Inexact (inf, sup) ->
      TS.subset inf tupleset && TS.subset tupleset (sup_tuples sup)

let inf = function
  | Exact (ts) -> ts
  | Inexact (ts, _) -> ts

let sup = function
  | Exact (ts) -> ts
  | Inexact (_, s) -> sup_tuples s

let must = inf

let may_aux sc =
  assert (TS.subset (inf sc) (sup sc));
  match sc with
  | Exact _ -> TS.empty
  | Inexact (inf, sup) -> TS.diff (sup_tuples sup) inf

let may = CCCache.(with_cache (lru ~eq:equal 253) may_aux)

let pp out = function
  | Exact (bound) -> TS.pp out bound
  | Inexact (inf, sup) ->
      Fmtc.(box @@ pair ~sep:sp (box2 TS.pp) (box2 TS.pp)) out (inf, sup_tuples sup)

let rec sup_rename atom_renaming = function
    | SupNode (ts,vs) -> SupNode (TS.rename atom_renaming ts,VL.rename atom_renaming vs)
    | SupArrow (l,r) -> SupArrow (sup_rename atom_renaming l,sup_rename atom_renaming r)

let rename atom_renaming = function
  | Exact (bound) -> Exact (TS.rename atom_renaming bound)
  | Inexact (inf, sup) -> Inexact (TS.rename atom_renaming inf,sup_rename atom_renaming sup)

module P = Intf.Print.Mixin (struct
  type nonrec t = t

  let pp = pp
end)

include P

let rec sup_flatten (sup : sup_t) : (TS.t * VL.t) =
    match sup with
    | SupNode (ts,vs) -> (ts,vs)
    | SupArrow (sup1,sup2) ->
        let (ts1,vs1) = sup_flatten sup1 in
        let (ts2,vs2) = sup_flatten sup2 in
        (TS.product ts1 ts2,VL.product (ts1,vs1) (ts2,vs2)) (*TODO this product needs to be revised and fixed*)

let sup_apply_multiplicity (mult : Raw.raw_multiplicity) (sup : sup_t) : sup_t =
    match mult with
    | None -> sup
    | Some m ->
        let (sup_ts,sup_vs) = sup_flatten sup in
        SupNode (sup_ts,VL.apply_multiplicity mult sup_ts sup_vs)

let sup_truncate (inf : inf_t) (sup : sup_t) : sup_t =
    if TS.is_empty inf then sup
    else
        let (sup_ts,sup_vs) = sup_flatten sup in
        let sup_vs' = VL.truncate inf sup_ts sup_vs in
        SupNode (sup_ts,sup_vs')

let sup_arrow (s1 : sup_t) (s2 : sup_t) : sup_t =
    match sup_is_simple s1, sup_is_simple s2 with
    | true, true ->
        let (ts,vs) = sup_flatten (SupArrow (s1,s2))
        in SupNode (ts,vs)
    | false, false ->
        let (ts,vs) = sup_flatten (SupArrow (s1,s2))
        in SupNode (ts,vs)
    | _, _ -> SupArrow (s1,s2)

let sup_product_with_multiplicities (s1 : sup_t) (m1 : Raw.raw_multiplicity) (m2 : Raw.raw_multiplicity) (s2 : sup_t) : sup_t =
    let s1' = sup_apply_multiplicity m1 s1 in
    let s2' = sup_apply_multiplicity m2 s2 in
    sup_arrow s1' s2'

let rec sup_binop (s1 : sup_t) (o : Raw.raw_bin) (s2 : sup_t) : sup_t =
    match s1,s2 with
    | SupArrow (ls1,rs1), SupArrow (ls2,rs2) -> SupArrow (sup_binop ls1 o ls2,sup_binop rs1 o rs2)
    | _ ->
        let (ts1,vs1) = sup_flatten s1 in
        let (ts2,vs2) = sup_flatten s2 in
        let ts12 = TS.raw_binop o ts1 ts2 in
        let vs12 = VL.raw_binop o ts1 vs1 ts2 vs2 in
        SupNode (ts12,vs12)
    

(* a partial tuple *)
type patom = Atom.t option
type ptuple = patom list

let patom_pp (fmt : Format.formatter) (pa : patom) : unit =
    match pa with
    | None -> Format.fprintf fmt "-"
    | Some a -> Atom.pp fmt a

let ptuple_pp (fmt : Format.formatter) (pt : ptuple) : unit =
    List.pp patom_pp fmt pt

let rec split_ptuple (i : int) (xs : ptuple) : (ptuple * ptuple) =
    if i <= 0
        then (List.empty,xs)
        else
            match xs with
            | [] -> failwith "split_ptuple empty"
            | x :: ys -> 
                let (l,r) = split_ptuple (i-1) ys in
                (List.cons x l,r)

let join_patom (x : patom) (y : patom) : patom =
    match x,y with
    | Some n1,Some n2 -> if Atom.equal n1 n2 then Some n1 else None
    | _ -> None

(* just the similar sections of two ptuples *)
let join_ptuple (x : ptuple) (y : ptuple) : ptuple =
    List.map (fun (x,y) -> join_patom x y) (List.combine x y)

let is_full_ptuple (pt : ptuple) : bool =
    let isSome mb = (match mb with
        | Some _ -> true
        | None -> false)
    in List.fold_left (fun b mb -> b && isSome mb) true pt

let to_ptuple (t : Tuple.t) : ptuple =
    List.map (fun x -> Some x) (Tuple.to_list t)

let from_ptuple (pt : ptuple) : Tuple.t =
    let fromSome mb = (match mb with
            | None -> failwith "from_ptuple"
            | Some x -> x) in
    Tuple.of_list (List.map fromSome pt)

let rec ptuple_sup (pt : ptuple) (sup : sup_t) : sup_t = match sup with
    | SupNode (ts,vs) -> SupNode (ts,vs)
    | SupArrow (l,r) ->
        let (ptl,ptr) = split_ptuple (sup_arity l) pt in
        if is_full_ptuple ptl
            then SupArrow (l,ptuple_sup ptr r)
            else if is_full_ptuple ptr
                then SupArrow (ptuple_sup ptl l,r)
                else let (ts,vs) = sup_flatten sup in SupNode (ts,vs)

let rec filter_sup (pt : ptuple) (f : Valuations.t -> bool) (s : sup_t) : sup_t = match s with
    | SupNode (ts,vs) ->
        let vs1 = VL.explicit ts vs in
        let vs2 = List.filter f vs1 in
        SupNode (ts,Some vs2)
    | SupArrow (l,r) ->
        let (ptl,ptr) = split_ptuple (sup_arity l) pt in
        if is_full_ptuple ptl
            then
                let fr vsr = f (Valuations.tuple_product_right (from_ptuple ptl) vsr) in
                SupArrow (l,filter_sup ptr fr r)
            else if is_full_ptuple ptr
                then 
                    let fl vsl = f (Valuations.tuple_product_left vsl (from_ptuple ptr)) in
                    SupArrow (filter_sup ptr fl l,r)
                else 
                    let (ts,vs) = sup_flatten s in
                    let vs1 = VL.explicit ts vs in
                    let vs2 = List.filter f vs1 in
                    SupNode (ts,Some vs2)

let filter_scope (pt : ptuple) (f : Valuations.t -> bool) (s : t) : t = match s with
    | Exact ts -> Exact ts
    | Inexact (inf,sup) -> Inexact (inf,filter_sup pt f sup)

