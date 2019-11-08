
type ocaml_type =
  | T_any
  | T_bool
  | T_int
  | T_func of ocaml_type * ocaml_type

let rec print typ =
  match typ with
  | T_any -> "any"
  | T_bool -> "bool"
  | T_int -> "int"
  | T_func(a,b) -> "(" ^ (print a) ^ " -> " ^ (print b) ^ ")"


exception UnifyFailure of ocaml_type * ocaml_type

let rec unify_types a b =
  match (a, b) with
  | (T_any, _) -> b
  | (_, T_any) -> a
  | (T_bool, T_bool) -> T_bool
  | (T_int, T_int) -> T_int
  | (T_func(p, q), T_func(x, y)) ->
      let ltype = unify_types p x in
      let rtype = unify_types q y in
      T_func(ltype, rtype)
  | _ -> raise (UnifyFailure(a,b))
