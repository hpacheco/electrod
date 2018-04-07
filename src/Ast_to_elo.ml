
open Containers

(* This module is supposed to happen after a simplification that addresses: 
   let bindings, *multiple* sim_bindings, quantified expressions, no lone/one quantifier; the input is also supposed to be arity-correct *)

module E = Elo2

let convert_arity = function
  | None -> 0
  | Some n when n > 0 -> n
  | Some _ -> assert false

(* The "convert_xxx" functions handle conversion from an AST with globally-unique variable names to a hashconsed-De Bruijn-encoded representation. Essentially, we keep a stack of bounded variables (in the current call context) and, if we meet a variable reference, we return its index in the stack. So a variable equal to 0 represents a variable bound by the last binder met.  *)

let get_var x stack = match List.find_idx (fun v -> Var.equal x v) stack with
  | None -> 
      Format.kasprintf failwith "%s.get_var: variable %a not found in %a"
        __FILE__  
        Var.pp x
        Fmtc.(brackets @@ list ~sep:(sp **> comma) @@ Var.pp) stack
  | Some (i, _) -> i

let new_env vars stack = 
  List.rev_map (function Ast.BVar v -> v) vars @ stack

let rec convert_fml stack ({ prim_fml; _ }: (Ast.var, Ast.ident) GenGoal.fml) =
  match prim_fml with
    | Qual (_, _) -> assert false (* simplified *)
    | Let (_, _) -> assert false (* simplified *)
    | Quant (_, _::_::_, _) -> assert false (* simplified *)
    | Quant (_, [], _) -> assert false (* impossible *)
    | Quant (q, [disj, vars, range], block) -> 
        let range' = convert_exp stack range in
        let block' = convert_block (new_env vars stack) block in
        E.quant (convert_quant q) (disj, List.length vars, range') block'
    | True -> E.true_
    | False -> E.false_
    | RComp (e1, comp, e2) -> 
        E.rcomp (convert_exp stack e1) 
          (convert_comp_op comp) (convert_exp stack e2)
    | IComp (e1, comp, e2) ->           
        E.icomp (convert_iexp stack e1) 
          (convert_icomp_op comp) (convert_iexp stack e2)
    | LUn (op, f) -> 
        E.lunary (convert_lunop op) (convert_fml stack f)
    | LBin (f1, op, f2) -> 
        E.lbinary (convert_fml stack f1) (
          convert_lbinop op) (convert_fml stack f2)
    | FIte (c, t, e) -> 
        E.fite (convert_fml stack c) (convert_fml stack t) (convert_fml stack e)
    | Block fmls -> 
        E.block @@ convert_block stack fmls

and convert_block stack fmls = 
  List.map (convert_fml stack) fmls

and convert_quant (q : GenGoal.quant) = match q with
  | One | Lone -> assert false (* simplified *)
  | All -> E.all
  | Some_ -> E.some
  | No -> E.no_

and convert_comp_op (comp : GenGoal.comp_op) = match comp with
  | In -> E.in_
  | NotIn -> E.not_in
  | REq -> E.req
  | RNEq -> E.rneq

and convert_icomp_op (comp : GenGoal.icomp_op) = match comp with
  | IEq -> E.ieq
  | INEq -> E.ineq
  | Lt -> E.lt
  | Lte -> E.lte
  | Gt -> E.gt
  | Gte -> E.gte

and convert_lunop (op : GenGoal.lunop) = match op with
  | F -> E.sometime
  | G -> E.always
  | Not -> E.not_
  | O -> E.once
  | X -> E.next
  | H -> E.historically
  | P -> E.previous

and convert_lbinop (op : GenGoal.lbinop) = match op with
  | And -> E.and_
  | Or -> E.or_
  | Imp -> E.impl
  | Iff -> E.iff
  | U -> E.until
  | R -> E.releases
  | S -> E.since

and convert_exp stack 
      ({ prim_exp; arity; _ } : (Ast.var, Ast.ident) GenGoal.exp) =
  let ar = convert_arity arity in
  match prim_exp with
    | BoxJoin (_, _) -> assert false (* simplified *)
    | Compr ([], _) -> assert false (* impossible *)
    | None_ -> E.none
    | Univ -> E.univ
    | Iden -> E.iden
    | Ident (Var v) ->
        E.var ~ar @@ get_var v stack
    | Ident (Name n) -> E.name ~ar n
    | RUn (op, e) -> E.runary ~ar (convert_runop op) (convert_exp stack e)
    | RBin (e1, op, e2) -> 
        E.rbinary ~ar (convert_exp stack e1) 
          (convert_rbinop op) (convert_exp stack e2)
    | RIte (c, t, e) -> 
        E.rite ~ar (convert_fml stack c) 
          (convert_exp stack t) (convert_exp stack e)
    | Prime e -> E.prime ~ar @@ convert_exp stack e
    | Compr (decls, block) -> 
        let decls' = 
          List.map (fun (disj, vars, range) -> 
                (disj, List.length vars, convert_exp stack range)) decls in
        let vars = List.flat_map (fun (_, vars, _) -> vars) decls in
        let block' = convert_block (new_env vars stack) block in
        E.compr ~ar decls' block'

and convert_runop (op : GenGoal.runop) = match op with
  | Transpose -> E.transpose
  | TClos -> E.tclos
  | RTClos -> E.rtclos

and convert_rbinop (op : GenGoal.rbinop) = match op with
  | Union -> E.union
  | Inter -> E.inter
  | Over -> E.over
  | LProj -> E.lproj
  | RProj -> E.rproj
  | Prod -> E.prod
  | Diff -> E.diff
  | Join -> E.join

and convert_iexp stack 
      ({ prim_iexp; _ } : (Ast.var, Ast.ident) GenGoal.iexp) = 
  match prim_iexp with
    | Num n -> E.num n
    | Card e -> E.card @@ convert_exp stack e
    | IUn (Neg, e) -> E.iunary E.neg @@ convert_iexp stack e
    | IBin (e1, op, e2) -> 
        E.ibinary (convert_iexp stack e1) 
          (convert_ibinop op) (convert_iexp stack e2)

and convert_ibinop (op : GenGoal.ibinop) = match op with
  | Add -> E.add
  | Sub -> E.sub

let convert_goal (GenGoal.Run fmls) = 
  E.run @@ convert_block [] fmls


module Test = struct
  let%test _ =
    let open E in
    let t = rbinary ~ar:1 (var ~ar:1 1) join (name ~ar:2 @@ Name.name "r") in
    let u = rbinary ~ar:1 (var ~ar:1 1) join (name ~ar:2 @@ Name.name "r") in
    Pervasives.(t == u)

  let%expect_test _ =
    let g = 
      let open E in
      quant some (sim_binding false 1 univ)
        [quant all (sim_binding true 2 @@ univ)
           [rcomp (var ~ar:1 1) in_ univ]] in
    let s = Fmt.to_to_string (E.pp_fml 0) g in 
    Printf.printf "%s" s;
    [%expect{| (some v/1 : univ {(all disj v/2, v/3 : univ {(v/2 in univ)})}) |}]

  open GenGoal
  open Ast
  let x = Var.fresh "x"
  let y = Var.fresh "y"
  let f : (Ast.var, Ast.ident) fml =
    fml Location.dummy @@ quant all [ (true, [bound_var x; bound_var y], exp (Some 1) Location.dummy univ)] [ fml Location.dummy @@ rcomp (exp (Some 1) Location.dummy @@ ident @@ var_ident x) in_ (exp (Some 1) Location.dummy univ)]
  let g : (Ast.var, Ast.ident) fml =
    fml Location.dummy @@ quant all [ (true, [bound_var x; bound_var y], exp (Some 1) Location.dummy univ)] [ fml Location.dummy @@ rcomp (exp (Some 1) Location.dummy @@ ident @@ var_ident x) in_ (exp (Some 1) Location.dummy univ)]

  let f' = Ast_to_elo.(convert_fml []) f
  let g' = Ast_to_elo.(convert_fml []) g

  let%test _ =
    Pervasives.(f' == g')


  let%expect_test _ =
    let fs = Fmt.to_to_string (E.pp_fml 0) f' in 
    let gs = Fmt.to_to_string (E.pp_fml 0) f' in 
    Printf.printf "%s" fs;
    [%expect{| (all disj v/1, v/2 : univ {(v/1 in univ)}) |}];
    Printf.printf "%s" gs;
    [%expect{| (all disj v/1, v/2 : univ {(v/1 in univ)}) |}]

  let cst = 
    Parser_main.parse_string 
      {| 
         univ : { a b c d };
         const r : univ->univ;
         run
         all disj x, y : r.univ, z : x.iden {
         some z : univ | { x, y : univ | x =z } in iden };
      |}
  let ast  = 
    cst 
    |> Transfo.run Raw_to_ast.transfo
    |> Shortnames.rename_elo true
    |> Transfo.run Simplify2.transfo
  let elo_goal = convert_goal ast.goal 

  let%expect_test _ =
    Fmt.pr "AST:@\n%a@\nELO:@\n%a"
      Ast.pp_goal ast.goal
      Elo2.pp_goal elo_goal;
    [%expect {|
      AST:
      run
        (all disj x/2, y/3 : (r.univ)
          {(all z/4 : (x/2.iden)
             {(some z/5 : univ {({ x/6, y/7 : univ {(x/6 = z/5)} } in iden)})})
          })
      ELO:
      run
        (all disj v/1, v/2 : (r.univ)
          {(all v/3 : (v/1.iden)
             {(some v/4 : univ {({ v/5, v/6 : univ {(v/5 = v/4)} } in iden)})})
          }) |}]


  let cst = 
    Parser_main.parse_string 
      {| 
         univ : { a b c d };
         const r : univ->univ;
         run
         all disj x, y : r.univ, z : x.iden {
            some z : univ | { x, y : univ | x =z } in iden };
         all disj u, v : r.univ, z : u.iden {
            some z : univ | { x, v : univ | x =z } in iden };
      |}
  let ast  = 
    cst 
    |> Transfo.run Raw_to_ast.transfo
    |> Shortnames.rename_elo true
    |> Transfo.run Simplify2.transfo
  let elo_goal = convert_goal ast.goal 

  let%test _ = match elo_goal with
    | Run [f1;f2] -> Pervasives.(f1 == f2)
    | Run _ -> false

  let%expect_test _ =
    Fmt.pr "AST:@\n%a@\nELO:@\n%a"
      Ast.pp_goal ast.goal
      Elo2.pp_goal elo_goal;
    [%expect {|
      AST:
      run
        (all disj x/8, y/9 : (r.univ)
          {(all z/10 : (x/8.iden)
             {(some z/11 : univ {({ x/12, y/13 : univ {(x/12 = z/11)} } in iden)})})
          })
        (all disj u/14, v/15 : (r.univ)
          {(all z/16 : (u/14.iden)
             {(some z/17 : univ {({ x/18, v/19 : univ {(x/18 = z/17)} } in iden)})})
          })
      ELO:
      run
        (all disj v/1, v/2 : (r.univ)
          {(all v/3 : (v/1.iden)
             {(some v/4 : univ {({ v/5, v/6 : univ {(v/5 = v/4)} } in iden)})})
          })
        (all disj v/1, v/2 : (r.univ)
          {(all v/3 : (v/1.iden)
             {(some v/4 : univ {({ v/5, v/6 : univ {(v/5 = v/4)} } in iden)})})
          }) |}]
end
