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

(** Relation scopes. *)

type inf_t = Tuple_set.t

type sup_t
    = SupNode of Tuple_set.t * Valuations_list.t (* all possible valuations, when there are multiplicities *)
    | SupArrow of sup_t * sup_t (* when there are no multiplicities involved *)

type t = Exact of Tuple_set.t | Inexact of inf_t * sup_t

val sup_is_simple : sup_t -> bool
val sup_arity : sup_t -> int

(*val valuations : t -> ((Valuations.t list) option)

val is_enum : t -> bool*)

(** {1 Constructors} *)

val exact : Tuple_set.t -> t
val inexact : inf_t * sup_t -> t
val equal : t -> t -> bool

val included_in : Tuple_set.t -> t -> bool
(** [included_in ts scope] tells whether [ts] is in the scope (meaning
    it also contains the lower bound of the scope if the latter is
    inexact.) *)

val inf : t -> Tuple_set.t
(** Return the inf and sup bounds of the scope. *)

val sup : t -> Tuple_set.t
val sup_tuples : sup_t -> Tuple_set.t

val must : t -> Tuple_set.t
(** Return the must and may (= sup - inf; computation is {b cached})
    bounds of the scope. *)

val may : t -> Tuple_set.t

val inferred_arity : t -> int
(** 0 if the arity cannot be inferred (= is unknown), [n > 0] otherwise. *)

val rename : (Atom.t, Atom.t) List.Assoc.t -> t -> t

include Intf.Print.S with type t := t

val to_yojson : t -> Yojson.Safe.t
val of_yojson : Yojson.Safe.t -> (t, string) result

val sup_flatten : sup_t -> (Tuple_set.t * Valuations_list.t)
val sup_apply_multiplicity : Raw.raw_multiplicity -> sup_t -> sup_t
val sup_truncate : inf_t -> sup_t -> sup_t
val sup_arrow : sup_t -> sup_t -> sup_t
val sup_product_with_multiplicities : sup_t -> Raw.raw_multiplicity -> Raw.raw_multiplicity -> sup_t -> sup_t
val sup_binop : sup_t -> Raw.raw_bin -> sup_t -> sup_t

type ptuple = (Atom.t option) list
val ptuple_pp : Format.formatter -> ptuple -> unit
val join_ptuple : ptuple -> ptuple -> ptuple
val to_ptuple : Tuple.t -> ptuple
val from_ptuple : ptuple -> Tuple.t

val filter_scope : ptuple -> (Valuations.t -> bool) -> t -> t

