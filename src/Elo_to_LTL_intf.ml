(*******************************************************************************
 * Time-stamp: <2017-11-14 CET 14:06:50 David Chemouil>
 * 
 * electrod - a model finder for relational first-order linear temporal logic
 * 
 * Copyright (C) 2016-2017 ONERA
 * Authors: Julien Brunel (ONERA), David Chemouil (ONERA)
 * 
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 * 
 * SPDX-License-Identifier: MPL-2.0
 * License-Filename: LICENSES/MPL-2.0.txt
 ******************************************************************************)

(** Abstract type for a converter from Elo models to (abstract) LTL formulas.  *)

open Containers

module type S = sig
  type atomic                     (* LTL propositional atoms *)
  type ltl                      (* ltl formula *)

  val color :
    Elo.t ->
    (Elo.var, Elo.ident) GenGoal.fml ->
    Invar_computation.goal_color

  val convert :
    Elo.t ->
    (Elo.var, Elo.ident) GenGoal.fml ->
    string * ltl

end
