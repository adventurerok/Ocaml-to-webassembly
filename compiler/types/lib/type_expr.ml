open Base
open Parsetree
open Types

exception TypeError of string

type evar = string

type context = (evar * scheme_type) list

let new_context () : context = []

let extend_context ctx vr sch =
  (vr, sch) :: ctx

let rec search_context (ctx : context) name =
  match ctx with
  | [] -> None
  | ((vr, sch) :: ctx') -> if (String.equal vr name) then Some(sch) else (search_context ctx' name)


let nexttvar = ref 0
let fresh () =
  let rec int_to_tvar x =
    let ccode = (x % 26) + 97 in
    let c = Char.of_int_exn ccode in
    let nx = x / 26 in
    match nx with
    | 0 -> [c]
    | _ -> c :: (int_to_tvar nx)
  in
  let index = !nexttvar in
  (nexttvar := index + 1; String.of_char_list (List.rev (int_to_tvar index)))


let infer_constant (const : constant) =
  match const with
  | Pconst_integer(_, _) -> ([], T_val(V_int))
  | _ -> raise (TypeError "Unknown constant type")

(* context -> expression -> (uni_pair list * scheme) *)
let rec infer_expr (ctx : context) (expr : expression) : (uni_pair list * scheme_type) =
  match expr.pexp_desc with
  | Pexp_constant(const) -> infer_constant const
  | Pexp_apply(f, args) -> infer_apply ctx f args
  | Pexp_ident(ident) -> infer_ident ctx ident
  | Pexp_fun(_, _, pat, body) -> infer_fun ctx pat body
  | Pexp_let(_, bindings, body) ->
      let (ccs, ctx') = ctx_of_bindings ctx bindings in
      let (ecs, typ) = infer_expr ctx' body in
      (ccs @ ecs, typ)
  | _ -> raise (TypeError "Unsupported expression")

and infer_apply ctx f args =
  let (fcs, ftype) = infer_expr ctx f in
  let rec partial fc args =
    match args with
    | [] -> ([], fc)
    | ((_, expr) :: args') ->
        let (acs, atyp) = infer_expr ctx expr in
        (match fc with
        | T_func(a, b) ->
            let (bcs, btyp) = partial b args' in
            (((Uni(a, atyp)) :: acs) @ bcs, btyp)
        | T_var(_) ->
            let a = T_var(fresh ()) in
            let b = T_var(fresh ()) in
            let (bcs, btyp) = partial b args' in
            let ccs = ((Uni(fc, T_func(a, b))) :: (Uni(a, atyp)) :: (Uni(b, btyp)) :: acs) @ bcs in
            (ccs, btyp)
        | _ -> raise (TypeError "Cannot apply a non_function"))
  in let (argcs, typ) = partial ftype args in
  (fcs @ argcs, typ)

and infer_fun ctx pat body =
  match pat.ppat_desc with
  | Ppat_var(strloc) ->
      let varname = strloc.txt in
      let tv = fresh () in
      let ctx' = extend_context ctx varname (T_var(tv)) in
      let (bcs, btyp) = infer_expr ctx' body in
      (bcs, T_func(T_var(tv), btyp))
  | _ -> raise (TypeError "Please only variables")

and ctx_of_bindings ctx bindings =
  match bindings with
  | [] -> ([], ctx)
  | (binding :: bindings') ->
      let (ccs, ctx') = ctx_of_binding ctx binding in
      let (cbcs, ctx'') = ctx_of_bindings ctx' bindings' in
      (ccs @ cbcs, ctx'')

and ctx_of_binding ctx binding =
  let (ccs, typ) = infer_expr ctx binding.pvb_expr in
  match binding.pvb_pat.ppat_desc with
  | Ppat_var(strloc) ->
      let varname = strloc.txt in
      let ctx' = extend_context ctx varname typ in
      (ccs, ctx')
  | _ -> raise (TypeError "Please only variables")

and infer_ident ctx ident =
  match ident.txt with
  | Lident("+") -> ([], T_func(T_val(V_int), T_func(T_val(V_int), T_val(V_int))))
  | Lident(str) ->
      (match search_context ctx str with
      | Some(typ) -> ([], typ)
      | None -> raise (TypeError ("Unknown identifer '" ^ str ^ "'")))
  | _ -> raise (TypeError ("Unknown strange identifer"))

let type_expr (ctx : context) (expr : expression) =
  let (ccs, typ) = infer_expr ctx expr in
  let subs = unify_many ccs in
  substitute_list subs typ
