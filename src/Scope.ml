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

type t = Exact of TS.t | Inexact of (TS.t * TS.t) * VL.t
  [@@deriving yojson]

let valuations scope = 
    match scope with
    | Exact _ -> VL.empty
    | Inexact (_,vs) -> vs

let is_enum scope = not @@ VL.is_empty (valuations scope)

let equal sc1 sc2 =
  match (sc1, sc2) with
  | Exact (ts1), Exact (ts2) -> TS.equal ts1 ts2
  | Exact _, Inexact _ | Inexact _, Exact _ -> false
  | Inexact ((l1,s1),vs1), Inexact ((l2,s2),vs2) -> TS.equal l1 l2 && TS.equal s1 s2 && VL.equal vs1 vs2

let exact (bound) = Exact (bound)

let inexact ((l,s),vs) = Inexact ((l,s),vs)

let inferred_arity = function
  | Exact (b)
  | Inexact ((_, b),_)
    -> TS.inferred_arity b

let included_in tupleset = function
  | Exact exact -> TS.subset tupleset exact
  | Inexact ((inf, sup),_) ->
      TS.subset inf tupleset && TS.subset tupleset sup

let inf = function
  | Exact (ts) | Inexact ((ts, _),_) -> ts

let sup = function
  | Exact (ts) | Inexact ((_, ts),_) -> ts

let must = inf

let may_aux sc =
  assert (TS.subset (inf sc) (sup sc));
  match sc with
  | Exact _ -> TS.empty
  | Inexact ((inf, sup),_) -> TS.diff sup inf

let may = CCCache.(with_cache (lru ~eq:equal 253) may_aux)

let pp out = function
  | Exact (bound) -> TS.pp out bound
  | Inexact ((inf, sup),_) ->
      Fmtc.(box @@ pair ~sep:sp (box2 TS.pp) (box2 TS.pp)) out (inf, sup)

let rename atom_renaming = function
  | Exact (bound) -> Exact (TS.rename atom_renaming bound)
  | Inexact ((inf, sup),vs) -> Inexact ((TS.rename atom_renaming inf, TS.rename atom_renaming sup),VL.rename atom_renaming vs)

module P = Intf.Print.Mixin (struct
  type nonrec t = t

  let pp = pp
end)

include P
