open Base
open Parsetree
open Types
open Predefined

exception TypeError of string


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

let instantiate (Forall(s, t)) =
  let subs = List.map (Set.to_list s) ~f:(fun old -> (old, T_var(fresh()))) in
  substitute_list subs t

let context_ftv (ctx: Context.context) =
  Set.union_list (module String) (List.map (Context.get_var_list ctx) ~f:(fun (_,t) -> ftv t))

let generalize (ctx: Context.context) t =
  let free_vars = Set.diff (ftv t) (context_ftv ctx)
  in Forall(free_vars, t)

let infer_constant (const : constant) =
  match const with
  | Pconst_integer(_, _) -> ([], T_val(V_int))
  | _ -> raise (TypeError "Unknown constant type")

(* context -> expression -> (uni_pair list * scheme) *)
let rec infer_expr (ctx : Context.context) (expr : expression) : (uni_pair list * scheme_type) =
  match expr.pexp_desc with
  | Pexp_constant(const) -> infer_constant const
  | Pexp_construct(ident, expr_opt) -> infer_construct ctx ident expr_opt
  | Pexp_apply(f, args) -> infer_apply ctx f args
  | Pexp_ident(ident) -> infer_ident ctx ident
  | Pexp_fun(_, _, pat, body) -> infer_fun ctx pat body
  | Pexp_let(_, bindings, body) ->
      let (ccs, ctx') = ctx_of_bindings ctx bindings in
      let (ecs, typ) = infer_expr ctx' body in
      (ccs @ ecs, typ)
  | Pexp_tuple(lst) ->
      let ctlst = List.map lst ~f:(infer_expr ctx) in
      let (ccslst, tlst) = List.unzip ctlst in
      let ccs = List.concat ccslst in
      (ccs, T_tuple(tlst))
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
  let (acs, atyp, ctx') = infer_pattern ctx pat in
  let (bcs, btyp) = infer_expr ctx' body in
  (acs @ bcs, T_func(atyp, btyp))

and ctx_of_bindings ctx bindings =
  match bindings with
  | [] -> ([], ctx)
  | (binding :: bindings') ->
      let (ccs, ctx') = ctx_of_binding ctx binding in
      let (cbcs, ctx'') = ctx_of_bindings ctx' bindings' in
      (ccs @ cbcs, ctx'')

and ctx_of_binding ctx binding =
  let (ccs, typ) = infer_expr ctx binding.pvb_expr in
  let (pcs, ptyp, pctx) = infer_pattern ctx binding.pvb_pat in
  ((Uni(typ, ptyp)) :: (ccs @ pcs), pctx)

(* context -> pattern -> (constraints * type * new_ctx) *)
and infer_pattern ctx pat =
  match pat.ppat_desc with
  | Ppat_var(ident) ->
      let varname = ident.txt in
      let tv = fresh () in
      let typ = (T_var(tv)) in
      let ctx' = Context.add_var ctx varname typ in
      ([], typ, ctx')
  | Ppat_tuple(lst) ->
      let rec loop cx ls =
        match ls with
        | [] -> ([], [], cx)
        | (pat::ls') ->
            let (ccs, typ, cx') = infer_pattern cx pat in
            let (ccs', tlst, cx'') = loop cx' ls' in
            (ccs @ ccs', typ :: tlst, cx'')
      in let (ccs, tlst, ctx') = loop ctx lst in
      (ccs, T_tuple(tlst), ctx')
  | _ -> raise (TypeError "Unsupported pattern")

and infer_ident ctx ident =
  match ident.txt with
  | Lident(str) ->
      (match Context.find_var ctx str with
      | Some(typ) -> ([], typ)
      | None ->
          (match lookup_ident str with
          | Some(t2) -> ([], t2)
          | None -> raise (TypeError ("Unknown identifer '" ^ str ^ "'"))))
  | _ -> raise (TypeError ("Unknown strange identifer"))

and infer_construct ctx ident expr_opt =
  match ident.txt with
  | Lident("true") -> ([], T_val(V_bool))
  | Lident("false") -> ([], T_val(V_bool))
  | Lident("[]") ->
      let ltyp = T_var(fresh ()) in
      ([], T_constr("list", [ltyp]))
  | Lident("::") ->
      let ltyp = T_var(fresh ()) in
      let lsttyp = T_constr("list", [ltyp]) in
      let tuptyp = T_tuple([ltyp; lsttyp]) in
      let (ccs,ttyp) =
        (match expr_opt with
        | Some(expr) -> infer_expr ctx expr
        | None -> raise (TypeError "Expecting an expression with a cons"))
      in ((Uni(tuptyp, ttyp)) :: ccs, lsttyp)
  | _ -> raise (TypeError "Unknown construct")

let type_expr (ctx : Context.context) (expr : expression) =
  let (ccs, typ) = infer_expr ctx expr in
  let subs = unify_many ccs in
  substitute_list subs typ
