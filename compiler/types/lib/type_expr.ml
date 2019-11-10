open Parsetree
open Types

exception TypeError of string

type environment = (string * ocaml_type) list

let create_env () = []

let update_env env var typ = (var, typ) :: env

let rec remove_env env name =
  match env with
  | [] -> []
  | ((var, typ) :: env') ->
      if name = var then
        remove_env env' name
      else (var, typ) :: (remove_env env' name)

let rec lookup_env env name =
  match env with
  | [] -> None
  | ((var, typ) :: env') -> if name = var then Some typ else lookup_env env' name

let type_constant (const : constant) =
  match const with
  | Pconst_integer(_, _) -> T_int
  | _ -> raise (TypeError "Unknown constant type")

let rec type_expr (env : environment) (expr : expression) (con : ocaml_type) =
  let (nenv, typ) = match expr.pexp_desc with
  | Pexp_constant(const) -> (env, type_constant const)
  | Pexp_construct(loc, expr_opt) -> type_construct env loc expr_opt
  | Pexp_apply(f, args) -> type_apply env f args
  | Pexp_ident(ident) -> type_ident env ident con
  | Pexp_fun(_, _, pat, body) -> type_fun env pat body
  | Pexp_let(_, bindings, body) ->
      let env' = env_of_bindings env bindings in
      let (_, typ) = type_expr env' body T_any in
      (env, typ)
  | _ -> raise (TypeError "Unsupported expression")
  in (nenv, unify_types typ con)

and type_construct env loc _ =
  match loc.txt with
  | Lident("true") -> (env, T_bool)
  | Lident("false") -> (env, T_bool)
  | _ -> raise (TypeError "Unknown construct")

(* TODO environments in this? I just hacked them in without thinking *)
and type_apply env f args =
  let (_, ftype) = type_expr env f T_any in
  let rec partial ev fc args =
    match args with
    | [] -> (ev, fc)
    | ((_, expr) :: args') ->
        (match fc with
        | T_func(a, b) ->
            let (ev', _) = type_expr ev expr a in
            partial ev' b args'
        | _ -> raise (TypeError "Cannot apply non_function"))
  in
  partial env ftype args

and type_fun env pat body =
  match pat.ppat_desc with
  | Ppat_var(strloc) ->
      let varname = strloc.txt in
      let env' = update_env env varname T_any in
      let (env'', typ) = type_expr env' body T_any in
      let vartype = Option.get (lookup_env env'' varname) in
      let nenv = remove_env env'' varname in
      (nenv, T_func(vartype, typ))
  | _ -> raise (TypeError "Please only variables")

and env_of_bindings env bindings =
  match bindings with
  | [] -> env
  | (binding :: bindings') -> env_of_bindings (env_of_binding env binding) bindings'

and env_of_binding env binding =
  let (_, typ) = type_expr env binding.pvb_expr T_any in
  match binding.pvb_pat.ppat_desc with
  | Ppat_var(strloc) ->
      let varname = strloc.txt in
      let env' = update_env env varname typ in
      env'
  | _ -> raise (TypeError "Please only variables")

and type_ident env ident con =
  match ident.txt with
  | Lident("+") -> (env, T_func(T_int, T_func(T_int, T_int)))
  | Lident("f") -> (env, T_func(T_int, T_func(T_bool, T_func(T_int, T_bool))))
  | Lident(str) ->
      (match lookup_env env str with
      | Some(typ) ->
          let typ' = unify_types typ con in
          (update_env env str typ', typ')
      | None -> raise (TypeError ("Unknown identifier '" ^ str ^ "'")))
  | _ -> raise (TypeError ("Unknown strange identifier"))
