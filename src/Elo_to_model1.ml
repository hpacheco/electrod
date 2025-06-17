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

(** Provides a converter from Electrod models to (part of) a solver
    model.  *)

open Containers
module S = Iter

module Make
    (Ltl : Solver.LTL)
    (ConvertFormulas : Elo_to_ltl_intf.S
                         with type ltl = Ltl.t
                          and type atomic = Ltl.Atomic.t)
    (Model : Solver.MODEL
               with type ltl = ConvertFormulas.ltl
                and type atomic = ConvertFormulas.atomic) =
struct
  type atomic = Ltl.Atomic.t

  (** Computes the LTL (the only temporal connective is "next") formula encoding
      the symmetry 
      in a single state only (int the initial state if symmetry_offset = 0) *)
  let single_state_sym_to_ltl symmetry_offset elo (sym : Symmetry.t) =
    let open Elo in
    let open Ltl in
    let sym_fml =
      Symmetry.fold
        (fun (name1, tuple1) (name2, tuple2) (fml_acc : Ltl.t) ->
          (*We assume that a symmetry is well-formed: each pair of
               name and tuple (name, tuple) share the same name *)
          if not (Name.equal name1 name2) then
            failwith
              Format.(
                sprintf "Badly-formed symmetry: %a != %a" Name.pp name1 Name.pp
                  name2)
          else
            let at1 = Ltl.Atomic.make elo.domain name1 tuple1 in
            let at_fml1 = atomic at1 in
            let at2 = Ltl.Atomic.make elo.domain name2 tuple2 in
            let at_fml2 = atomic at2 in
            and_
              (implies at_fml1 (lazy at_fml2))
              (lazy (implies (iff at_fml1 at_fml2) (lazy fml_acc))))
        sym true_
    in
    let rec iter_next_ltl k phi =
      if k = 0 then phi else iter_next_ltl (k - 1) (next phi)
    in
    iter_next_ltl symmetry_offset sym_fml

  (** Computes the full LTL formula encoding the symmetry in a temporal context *)
  let temporal_sym_to_ltl i single_formula elo (sym : Symmetry.t) =
    let open Elo in
    let open Ltl in
    let all_equiv =
      Symmetry.fold
        (fun (name1, tuple1) (name2, tuple2) (fml_acc : Ltl.t) ->
          (*We assume that a symmetry is well-formed: each pair of
            name and tuple (name, tuple) share the same name *)
          if not (Name.equal name1 name2) then assert false
          else
            let at1 = Ltl.Atomic.make elo.domain name1 tuple1 in
            let at_fml1 = atomic at1 in
            let at2 = Ltl.Atomic.make elo.domain name2 tuple2 in
            let at_fml2 = atomic at2 in
            and_ (iff at_fml1 at_fml2) (lazy fml_acc))
        sym true_
    in
    if single_formula then ("",always @@ implies (zesterday @@ historically all_equiv) (lazy (single_state_sym_to_ltl 0 elo sym)))
    else
        let all_equiv_str = Printf.sprintf "__sym_%i" i in
        let all_equiv_expr = Format.asprintf "%a" (fun fmt -> pp fmt 0) all_equiv in
        let all_equiv_def = Printf.sprintf "DEFINE %s := %s;\n" all_equiv_str all_equiv_expr in
        let h_str = Printf.sprintf "__H_%i" i in
        let z_h_str = Printf.sprintf "__Z_H_%i" i in
        let z_h_all_equiv = auxiliary (Symbol.make z_h_str) in
        let h_def = Printf.sprintf "VAR %s : boolean;\nASSIGN\n\tinit(%s) := TRUE;\n\tnext(%s) := %s & %s;\n" h_str h_str h_str h_str all_equiv_str in
        (* we do not create var here for z_h_all_equiv, as it will be created later as an auxiliary variable *)
        let z_h_def = Printf.sprintf "ASSIGN\n\tinit(%s) := TRUE;\n\tnext(%s) := %s;\n" z_h_str z_h_str h_str in
        let str = all_equiv_def ^ h_def ^ z_h_def in
        (str,implies z_h_all_equiv (lazy (single_state_sym_to_ltl 0 elo sym)))

  (* Computes an LTL formula for the whole list of symmetries.
     According to the value of the argument temporal_symmetry, the LTL formula
     either deals with the initial state or with the whole temporal trace. *)
  let syms_to_ltl single_formula temporal_symmetry symmetry_offset elo =
    let open Elo in
    let convert_sym i s =
      if temporal_symmetry || symmetry_offset > 0 || single_formula then temporal_sym_to_ltl i single_formula elo s
      else ("--  (symmetry)",single_state_sym_to_ltl symmetry_offset elo s)
    in
    List.fold_left
      (fun (i,fmls_acc) sym -> (i+1,List.cons (convert_sym i sym) fmls_acc))
      (0,List.empty) elo.sym

  let add_sym_comment_to_ltl_fml_list fml_list =
    List.fold_left
      (fun fmls_acc fml -> S.cons ("--  (symmetry)", fml) fmls_acc)
      S.empty fml_list
  let sym_to_ltl_fml_list fml_list =
    List.fold_left
      (fun fmls_acc fml -> S.cons fml fmls_acc)
      S.empty fml_list

  (* Splits a list of formulas lf into four lists (initf, invf,
     transf, restf): the list of init formulas, invar formulas, the
     list of trans formulas and the list of the rest of the
     formulas. In case restf is empty, then the last formula of transf
     (or invf if transf is also empty) is put in restf.*)
  let split_invar_noninvar_fmls elo blk =
    let open Invar_computation in
    let invf, tmp_restf =
      List.partition_filter_map
        (fun fml ->
          let color = Invar_computation.color elo fml in
          Msg.debug (fun m ->
              m "Color of formula %a : %a\n"
              (Elo.pp_fml 0) fml Invar_computation.pp color);
          match color with
          | Invar -> `Left (remove_always_from_invar fml)
          | Static_prop | Init | Primed_prop | Trans | Temporal -> `Right fml)
        blk
    in
    let transf, tmp_restf2 =
      List.partition_filter_map
        (fun fml ->
          let color = Invar_computation.color elo fml in
          (* Msg.debug (fun m ->
              m "Color of formula %a : %a\n"
              Elo.pp_fml fml Invar_computation.pp color); *)
          match color with
          | Trans -> `Left (remove_always_from_invar fml)
          | _ -> `Right fml)
        tmp_restf
    in
    let initf, restf =
      List.partition_filter_map
        (fun fml ->
          let color = Invar_computation.color elo fml in
          (* Msg.debug (fun m ->
              m "Color of formula %a : %a\n"
              Elo.pp_fml fml Invar_computation.pp color); *)
          match color with Init | Static_prop -> `Left fml | _ -> `Right fml)
        tmp_restf2
    in
    match (restf, List.rev invf, List.rev transf, List.rev initf) with
    | _ :: _, _, _, _ -> (initf, invf, transf, restf)
    | [], _, hd :: tl, _ ->
        (initf, invf, List.rev tl, [ add_always_to_invar hd ])
    | [], hd :: tl, _, _ ->
        (initf, List.rev tl, transf, [ add_always_to_invar hd ])
    | [], _, _, hd :: tl -> (List.rev tl, invf, transf, [ hd ])
    | _ -> assert false

  (*the goal cannot be empty*)

  (* From a non-empty list f1, f2, ..., fn of elo formulas, this
     function computes the elo formula "(f1 and ... and fn-1) implies not
     fn" *)
  let dualise_fmls fmls =
    let open Elo in
    match List.rev fmls with
    | [] -> assert false
    | (Fml { node; _ } as hd) :: tl ->
        let premise = List.fold_left (fun x y -> lbinary x and_ y) true_ tl in
        let rhs_fml =
          match node with LUn (Not, subfml) -> subfml | _ -> lunary not_ hd
        in
        lbinary premise impl rhs_fml

  type defs = (Scope.ptuple Name.Map.t) option
  
  let union_defs (x : defs) (y : defs) : defs =
      match x,y with
      | Some ns1,Some ns2 -> Some (Name.Map.union (fun k x y -> Some (Scope.join_ptuple x y)) ns1 ns2)
      | _ -> None

  let rec defs_ltl (e : Ltl.t) : defs = match e with
      | Comp (tc,te1,te2) -> union_defs (defs_term te1) (defs_term te2)
      | True -> Some Name.Map.empty
      | False -> Some Name.Map.empty
      | Atomic a -> (match Ltl.Atomic.split a with
          | None -> None
          | Some (n,tu) -> Some (Name.Map.singleton n (Scope.to_ptuple tu)))
      | Auxiliary a -> None
      | Not t -> defs_ltl t
      | And (t1,t2) -> union_defs (defs_ltl t1) (defs_ltl t2)
      | Or (t1,t2) -> union_defs (defs_ltl t1) (defs_ltl t2)
      | Imp (t1,t2) -> union_defs (defs_ltl t1) (defs_ltl t2)
      | Iff (t1,t2) -> union_defs (defs_ltl t1) (defs_ltl t2)
      | Xor (t1,t2) -> union_defs (defs_ltl t1) (defs_ltl t2) 
      | Ite (t1,t2,t3) -> union_defs (union_defs (defs_ltl t1) (defs_ltl t2)) (defs_ltl t3)
      | X _ | F _ | G _ | Y _ | Z _ | O _ | H _ | U _ | R _ | S _ | T _ -> None
  and defs_term (te : Ltl.term) : defs = match te with
      | Num i -> Some Name.Map.empty
      | Neg te1 -> defs_term te1
      | Bin (te1,o,te2) -> union_defs (defs_term te1) (defs_term te2)
      | AIte (t,te1,te2) -> union_defs (union_defs (defs_ltl t) (defs_term te1)) (defs_term te2)

  let is_single_static_ltl (e : Ltl.t) : (Name.t * Scope.ptuple) option = match defs_ltl e with
        | None -> None
        | Some ns -> 
            (*Msg.debug (fun m ->
                  m "Names of formula %a : %a\n"
                  (fun fmt -> Ltl.pp fmt 0) e (Name.Map.pp Name.pp Scope.ptuple_pp) ns);*)
            if Stdlib.(Name.Map.cardinal ns == 1) then Name.Map.choose_opt ns else None

  let eval_comp (c : Ltl.tcomp) (e1 : int) (e2 : int) : bool = match c with
      | Lte -> e1 <= e2
      | Lt -> e1 < e2
      | Gte -> e1 >= e2
      | Gt -> e1 > e2
      | Eq -> Stdlib.(e1 == e2)
      | Neq -> not Stdlib.(e1 == e2)

  let eval_binop (o : Ltl.binop) (e1 : int) (e2 : int) : int = match o with
      | Plus -> e1 + e2
      | Minus -> e1 - e2
      | Mul -> e1 * e2
      | Div -> failwith "eval_binop div"
      | Rem -> failwith "eval_binop rem"

  let xor a b = (a || b) && not (a && b)
  let implies a b = (not a) || b
  let rec eval_ltl (n : Name.t) (vs : Valuations.t) (e : Ltl.t) : bool = match e with
    | Comp (tc,te1,te2) -> eval_comp tc (eval_term n vs te1) (eval_term n vs te2)
    | True -> true
    | False -> false
    | Atomic a ->
        (match Ltl.Atomic.split a with
        | None -> failwith "eval_ltl: atom not found"
        | Some (an,at) -> if Name.equal n an
            then Valuations.mem at vs
            else failwith "eval_ltl: unexpected name")
    | Auxiliary a -> failwith "eval_ltl: auxiliary not supported"
    | Not t -> not (eval_ltl n vs t)
    | And (t1,t2) -> (eval_ltl n vs t1) && (eval_ltl n vs t2)
    | Or (t1,t2) -> (eval_ltl n vs t1) || (eval_ltl n vs t2)
    | Imp (t1,t2) -> implies (eval_ltl n vs t1) (eval_ltl n vs t2)
    | Iff (t1,t2) -> Stdlib.(eval_ltl n vs t1 == eval_ltl n vs t2)
    | Xor (t1,t2) -> xor (eval_ltl n vs t1) (eval_ltl n vs t2) 
    | Ite (t1,t2,t3) -> if (eval_ltl n vs t1) then (eval_ltl n vs t2) else (eval_ltl n vs t3)
    | X _ | F _ | G _ | Y _ | Z _ | O _ | H _ | U _ | R _ | S _ | T _ -> failwith "eval_ltl: LTL not supported"
  and eval_term (n : Name.t) (vs : Valuations.t) (e : Ltl.term) : int = match e with
      | Num i -> i
      | Neg t -> 0 - (eval_term n vs t)
      | Bin (t1,o,t2) -> eval_binop o (eval_term n vs t1) (eval_term n vs t2)
      | AIte (a,t1,t2) ->
          if (eval_ltl n vs a) then eval_term n vs t1 else eval_term n vs t2

  let refine_scope (n : Name.t) (pt : Scope.ptuple) (e : Ltl.t) (s : Scope.t) : Scope.t =
        Scope.filter_scope pt (fun vs -> eval_ltl n vs e) s

  (* we take the change to evaluate some init/invar statements that can be migrated to the scope *)
  let prepare_elo (elo : Elo.t) (inits : (string * Ltl.t) Iter.t) (invars : (string * Ltl.t) Iter.t) : (Elo.t * (string * Ltl.t) Iter.t * (string * Ltl.t) Iter.t) =
      let newElo = ref elo in
      let newInits = ref Iter.empty in
      let newInvars = ref Iter.empty in
      
      let rec prepare_and prep ((s,e) : (string * Ltl.t)) =
          Msg.debug (fun m -> m "Preparing formula %a\n"(fun fmt -> Ltl.pp fmt 0) e); 
          match e with
          | And (t1,t2) -> prepare_and prep (s,t1); prepare_and prep (s,t2)
          | _ -> prep (s,e)
      in
      let prepare_init (s,e) = match is_single_static_ltl e with
          | None -> newInits := Iter.cons (s,e) !newInits
          | Some (n,pt) ->
              let elo = !newElo in
              let dom = elo.domain in
              let rel = Domain.get_exn n dom in
              let scope = Relation.scope rel in
              if Relation.is_const rel
                  then
                      (Msg.debug (fun m ->
                        m "Evaluating init formula %a : %a %a\n"
                        (fun fmt -> Ltl.pp fmt 0) e Name.pp n Scope.ptuple_pp pt);
                      let newScope = refine_scope n pt e scope in
                      Msg.debug (fun m -> m "New scope %a\n" Scope.pp newScope);
                      let newRel = Relation.set_scope newScope rel in
                      (*Msg.debug (fun m -> m "New relation %a\n" Relation.pp newRel);*)
                      let newDomain = Domain.update n newRel dom in
                      Msg.debug (fun m -> m "New domain %a\n" Domain.pp newDomain);
                      newElo := { elo with domain = newDomain })
                  else newInits := Iter.cons (s,e) !newInits
      in
      
      let prepare_invar (s,e) = match is_single_static_ltl e with
          | None -> newInvars := Iter.cons (s,e) !newInvars
          | Some (n,pt) ->
              Msg.debug (fun m ->
                    m "Evaluating invar formula %a : %a %a\n"
                    (fun fmt -> Ltl.pp fmt 0) e Name.pp n Scope.ptuple_pp pt);
              let elo = !newElo in
              let dom = elo.domain in
              let rel = Domain.get_exn n dom in
              let scope = Relation.scope rel in
              newElo := { elo with domain = Domain.update n (Relation.set_scope (refine_scope n pt e scope) rel) dom }
      in
      
      Iter.iter (prepare_and prepare_init) inits;
      Iter.iter (prepare_and prepare_invar) invars;
      (!newElo,!newInits,!newInvars)

  let run (elo, temporal_symmetry, symmetry_offset, single_formula) =
    let open Elo in
    (* #781 Handle instance:

       To handle the instance, one possibility would be to update the bound
       computation (bounds_exp) and [build_Ident].

       However, apparently, we won't need to differentiate the domain and the
       instance in the future. So we take the simpler path that consists in
       updating the domain itself. As this is confined to the following
       functions, we do this for the time being. If the need arises, a
       refactoring won't be too painful. *)
    let elo =
      Elo.
        {
          elo with
          domain = Domain.update_domain_with_instance elo.domain elo.instance;
          instance = Instance.empty;
        }
    in
    Msg.debug (fun m ->
        m "Elo_to_model1.run: after instance update:@ %a" Elo.pp elo);
    (* walk through formulas, convert them to LTL and accumulate rigid
       and flexible variables. *)
    (* let exception Early_stop in *)
    let translate_formulas fmls =
      (* try *)
      List.fold_left
        (fun acc_fml fml ->
          let fml_str, ltl = ConvertFormulas.convert elo fml in
          (* if ltl = Ltl.false_ then *)
          (*   raise Early_stop *)
          (* else *)
          S.cons (fml_str, ltl) acc_fml)
        S.empty fmls
      (* with *)
      (*   Early_stop -> S.(empty, empty, Ltl.false_) *)
      |> S.rev
    in
    (* handling symmetries *)
    let (_,sym_ltls) = syms_to_ltl single_formula temporal_symmetry symmetry_offset elo in
    (* handling the goal *)
    let goal_blk = match elo.goal with Elo.Run (g, _) -> g in
    (* Partition the goal fmls into invars and non invars *)
    let detected_inits, detected_invars, detected_trans, general_fmls =
      if single_formula then
        (* the user wants only a single big LTL formula as a goal *)
        ([], [], [], goal_blk)
      else split_invar_noninvar_fmls elo goal_blk
    in

    (* Msg.debug (fun m ->
       m "Detected init : %a" Elo.pp_block detected_inits); *)

    (* Msg.debug (fun m ->
       m "Detected invariants : %a" Elo.pp_block detected_invars); *)

    (* Msg.debug (fun m ->
       m "Detected trans : %a" Elo.pp_block detected_trans); *)
    let fml_prop = dualise_fmls general_fmls in
    (* Msg.debug (fun m -> m "Elo property : %a" Elo.pp_fml spec_fml); *)
    let fml_prop_comment, ltl_prop =
      let comment, p = ConvertFormulas.convert elo fml_prop in
      if not temporal_symmetry && (symmetry_offset > 0 || single_formula) then
        ( "-- A symmetry breaking predicate is added at the beginning of the \
           LTLSPEC formula. This is due to option --single-formula.\n" ^ comment,
          Ltl.and_ (Ltl.conj (List.map snd sym_ltls)) (lazy p) )
      else (comment, p)
    in
    (* handling init, invariants and trans *)
    let inits =
      if temporal_symmetry || symmetry_offset > 0 || single_formula then
        translate_formulas detected_inits
      else
        S.append
          (sym_to_ltl_fml_list sym_ltls)
          (translate_formulas detected_inits)
    in
    let invars = let fs = translate_formulas @@ List.append detected_invars elo.Elo.invariants in
      if temporal_symmetry && not single_formula then S.append (sym_to_ltl_fml_list sym_ltls) fs
      else fs
    in
    let trans = translate_formulas detected_trans in
    let (newElo,newInits,newInvars) = prepare_elo elo inits invars in
    Model.make ~elo:newElo ~init:newInits ~invariant:newInvars ~trans
      ~property:(fml_prop_comment, ltl_prop)
end
