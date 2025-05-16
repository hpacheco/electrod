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
