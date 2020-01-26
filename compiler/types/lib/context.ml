open Core_kernel
open Types

type variant_type = {
  name: string;
  args: string list;
  (* The constructor names, in order of id *)
  constructors: string list;
}

type constructor = {
  name: string;
  type_name: string;
  args: scheme_type list;

  (* Index in the variant type's constructor list *)
  index: int;
}

type context = {
  vars: (string * scheme) list;

  (* e.g. tree -> 1 if it takes 1 type argument *)
  (* name of type, number of type args, type args list *)
  types: (string, variant_type) Map.Poly.t;

  (* e.g. Branch(x,l,r) is (Branch,('a,'a tree,'a tree), 'a tree)*)
  (* construct name, types of arguments, type name *)
  constructs: (string, constructor) Map.Poly.t
}

let empty : context = {
  vars = [];
  types = Map.Poly.empty;
  constructs = Map.Poly.empty
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
  let variant = {
    name = name;
    args = args;
    constructors = []
  }
  in
  {
    ctx with
    types = Map.Poly.set ctx.types ~key:name ~data:variant
  }

let map_vars (ctx : context) f =
  {ctx with vars = List.map ctx.vars ~f:(fun (x,y) -> (x,f y))}

let get_var_list (ctx : context) =
  ctx.vars

let find_type (ctx : context) name =
  Map.Poly.find ctx.types name

(* context, name of construct, types of construct args, name of type *)
let add_constr ctx cname args tname =
  let variant = Map.Poly.find_exn ctx.types tname in
  let index = List.length variant.constructors in
  let variant' = {
    variant with
    constructors = variant.constructors @ [cname]
  }
  in
  let constr = {
    name = cname;
    type_name = tname;
    args = args;
    index = index
  }
  in
  {
    ctx with
    types = Map.Poly.set ctx.types ~key:tname ~data:variant';
    constructs = Map.Poly.set ctx.constructs ~key:cname ~data:constr
  }

let find_constr ctx name =
  Map.Poly.find ctx.constructs name

(* Adds list constructors to context *)
let empty_with_lists =
  let list_type = add_type empty "list" ["a"] in
  let with_nil = add_constr list_type "[]" [] "list" in
  add_constr with_nil "::" [T_var("a"); T_constr("list", [T_var("a")])] "list"

let empty_lists_refs =
  add_type empty_with_lists "ref" ["a"]

exception InvalidType of scheme_type * string

(* Checks if typ is valid in this context *)
let rec check_type (ctx : context) (typ : scheme_type) =
  match typ with
  | T_var(_) -> ()
  | T_val(_) -> ()
  | T_func(a,b) ->
      let () = check_type ctx a in
      check_type ctx b
  | T_tuple(ls) -> List.iter ls ~f:(check_type ctx)
  | T_constr(str, ls) ->
      let () = List.iter ls ~f:(check_type ctx) in
      let variant_opt = find_type ctx str in
      (match variant_opt with
      | Some(variant) ->
          if ((List.length ls) = (List.length variant.args)) then
            ()
          else raise (InvalidType (typ, "Type " ^ str ^ " has invalid number of arguments"))
      | None -> raise (InvalidType (typ, "Unknown type " ^ str)))

let print (ctx : context) =
  Stdio.print_endline "Context(";
  Stdio.print_endline "  vars:";
  List.iter ctx.vars ~f:(fun (n,s) ->
    Stdio.print_endline ("    " ^ n ^ ": " ^ (string_of_scheme s)));
  Stdio.print_endline "  types:";
  Map.iter ctx.types ~f:(fun variant ->
    let tvarstr = (String.concat ~sep:" " (List.map variant.args ~f:(fun s -> "'" ^ s))) in
    Stdio.print_endline ("    " ^ tvarstr ^ " " ^ variant.name));
  Stdio.print_endline "  constructors:";
  Map.iter ctx.constructs ~f:(fun constr ->
    let argsstr = string_of_scheme_type (T_tuple(constr.args)) in
    Stdio.print_endline ("    " ^ (constr.name) ^ argsstr ^ " -> " ^ (constr.type_name)));
  Stdio.print_endline ")"
