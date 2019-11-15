open Base
open Types

type context = {
  vars: (string * scheme_type) list;

  (* e.g. tree -> 1 if it takes 1 type argument *)
  types: (string * int) list;

  (* e.g. Branch(x,l,r) is (Branch,('a,'a tree,'a tree), 'a tree)*)
  constructs: (string * (scheme_type list) * scheme_type) list
}

let empty : context = {
  vars = [];
  types = [];
  constructs = []
}

let add_var (ctx : context) vr typ =
  {ctx with vars = ((vr, typ) :: ctx.vars)}

let find_var (ctx : context) name =
  let rec search vs =
    match vs with
    | [] -> None
    | ((vr, typ) :: vs') -> if (String.equal vr name) then Some(typ) else (search vs')
  in search ctx.vars

let add_type (ctx : context) name args =
  {ctx with types = ((name, args) :: ctx.types)}

let map_vars (ctx : context) f =
  {ctx with vars = List.map ctx.vars ~f:(fun (x,y) -> (x,f y))}

let get_var_list (ctx : context) =
  ctx.vars

let find_type (ctx : context) name =
  let rec search ts =
    match ts with
    | [] -> None
    | ((ts,args) :: ts') -> if (String.equal ts name) then Some(args) else (search ts')
  in search ctx.types
