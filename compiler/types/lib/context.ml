open Core_kernel
open Types

type context = {
  vars: (string * scheme) list;

  (* e.g. tree -> 1 if it takes 1 type argument *)
  types: (string * int * (string list)) list;

  (* e.g. Branch(x,l,r) is (Branch,('a,'a tree,'a tree), 'a tree)*)
  constructs: (string * (scheme_type list) * string) list
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
  {ctx with types = ((name, List.length args, args) :: ctx.types)}

let map_vars (ctx : context) f =
  {ctx with vars = List.map ctx.vars ~f:(fun (x,y) -> (x,f y))}

let get_var_list (ctx : context) =
  ctx.vars

let find_type (ctx : context) name =
  let rec search ts =
    match ts with
    | [] -> None
    | ((ts, argcount, args) :: ts') -> if (String.equal ts name) then Some((argcount,args)) else (search ts')
  in search ctx.types

let add_constr ctx cname args tname =
  {ctx with constructs = ((cname, args, tname) :: ctx.constructs)}

let print (ctx : context) =
  Stdio.print_endline "Context(";
  Stdio.print_endline "  vars:";
  List.iter ctx.vars ~f:(fun (n,s) ->
    Stdio.print_endline ("    " ^ n ^ ": " ^ (string_of_scheme s)));
  Stdio.print_endline "  types:";
  List.iter ctx.types ~f:(fun (n,_,vars) ->
    let tvarstr = (String.concat ~sep:" " (List.map vars ~f:(fun s -> "'" ^ s))) in
    Stdio.print_endline ("    " ^ tvarstr ^ " " ^ n));
  Stdio.print_endline "  constructors:";
  List.iter ctx.constructs ~f:(fun (cname, args, tname) ->
    let argsstr = string_of_scheme_type (T_tuple(args)) in
    Stdio.print_endline ("    " ^ cname ^ argsstr ^ " -> " ^ tname));
  Stdio.print_endline ")"
