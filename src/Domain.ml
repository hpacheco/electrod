open Containers

module Map = Name.Map


type t = Relation.t Map.t

let empty =
  Map.empty


let mem = Map.mem

let add name rel domain =
  assert (not @@ Map.mem name domain);
  Map.add name rel domain

let get_exn = Map.find

let get = Map.get

let to_list = Map.to_list

let univ_atoms domain =
  let open Relation in
  let open Scope in
  match get_exn Name.univ domain with
    | Const { scope; _ } ->
        (match scope with
          | Exact b -> b
          | Inexact _ -> assert false)
    | Var _ -> assert false

let pp out rels =
  let open Fmtc in
  (vbox @@ Map.print ~sep:" " ~arrow:" : " ~start:"" ~stop:""
             Name.pp (hbox2 @@ Relation.pp ~print_name:false)) out rels

module P = Intf.Print.Mixin(struct type nonrec t = t let pp = pp end)
include P 
