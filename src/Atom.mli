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

(** Atoms (= urelements). *)

type t
(** Type of atoms. *)

module Set : CCSet.S with type elt = t

val atom : ?loc:Location.t -> string -> t
(** [atom ~loc:loc s] creates an atom with name [s] and optional location [loc]. *)

val to_string : t -> string

val of_raw_ident : Raw_ident.t -> t
(** creates an atom out of a raw_ident. *)

val pp_list : t list CCFormat.printer
(** Prints a list of atoms as a bound. *)

val hash : t -> int

include Intf.Print.S with type t := t
include Intf.COMPARE with type t := t

val to_yojson : t -> Yojson.Safe.t
val of_yojson : Yojson.Safe.t -> (t, string) result
