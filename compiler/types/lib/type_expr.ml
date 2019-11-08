open Parsetree
open Types

exception TypeError of string

let type_constant (const : constant) =
  match const with
  | Pconst_integer(_, _) -> T_int
  | _ -> raise (TypeError "Unknown constant type")

let rec type_expr (expr : expression) =
  match expr.pexp_desc with
  | Pexp_constant(const) -> type_constant const
  | Pexp_construct(loc, expr_opt) -> type_construct loc expr_opt
  | Pexp_apply(f, args) -> type_apply f args
  | Pexp_ident(ident) -> type_ident ident
  | _ -> raise (TypeError "Unsupported expression")

and type_construct loc _ =
  match loc.txt with
  | Lident("true") -> T_bool
  | Lident("false") -> T_bool
  | _ -> raise (TypeError "Unknown construct")

and type_apply f args =
  let ftype = type_expr f in
  let rec partial fc args =
    match args with
    | [] -> fc
    | ((_, expr) :: args') ->
        match fc with
        | T_func(a, b) ->
            let argtype = type_expr expr in
            let _ = unify_types a argtype in
            partial b args'
        | _ -> raise (TypeError "Cannot apply non_function")
  in
  partial ftype args

and type_ident ident =
  match ident.txt with
  | Lident("+") -> T_func(T_int, T_func(T_int, T_int))
  | Lident("f") -> T_func(T_int, T_func(T_bool, T_func(T_int, T_bool)))
  | Lident(str) -> raise (TypeError ("Unknown identifier '" ^ str ^ "'"))
  | _ -> raise (TypeError ("Unknown strange identifier"))
