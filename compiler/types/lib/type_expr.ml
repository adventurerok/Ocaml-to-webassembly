open Core_kernel
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
  Set.union_list (module String) (List.map (Context.get_var_list ctx) ~f:(fun (_,t) -> ftv_scheme t))

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
  | Pexp_let(recflag, bindings, body) ->
      let (ctx') = ctx_of_bindings ctx recflag bindings in
      let (ecs, typ) = infer_expr ctx' body in
      (ecs, typ)
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
  let (atyp, ctx', _) = infer_pattern ctx pat in
  let (bcs, btyp) = infer_expr ctx' body in
  (bcs, T_func(atyp, btyp))

and ctx_of_bindings ctx recflag bindings =
  match recflag with
  | Asttypes.Nonrecursive -> ctx_of_nonrec_bindings ctx bindings
  | Asttypes.Recursive -> ctx_of_rec_bindings ctx bindings

and ctx_of_nonrec_bindings ctx bindings =
  match bindings with
  | [] -> (ctx)
  | (binding :: bindings') ->
      let (ctx') = ctx_of_nonrec_binding ctx binding in
      let (ctx'') = ctx_of_nonrec_bindings ctx' bindings' in
      (ctx'')

and ctx_of_nonrec_binding ctx binding =
  let typ = type_expr ctx binding.pvb_expr in
  let (ptyp, _, vars) = infer_pattern ctx binding.pvb_pat in
  let subs = unify ptyp typ in
  (addvars subs ctx ctx vars)

and addvars subs ctx cx vlist =
  match vlist with
  | [] -> cx
  | ((v,t)::vlist') ->
      let truetype = substitute_list subs t in
      let genscheme = generalize ctx truetype in
      let cx' = Context.add_var cx v genscheme in
      Stdio.print_endline ("Bind " ^ v ^ " to " ^ (string_of_scheme genscheme));
      addvars subs ctx cx' vlist'

and ctx_of_rec_bindings ctx bindings =
  let pe_list = List.map bindings ~f:(fun vb -> (vb.pvb_pat, vb.pvb_expr)) in
  let (pat_list, expr_list) = List.unzip pe_list in
  let pinfer_list = List.map pat_list ~f:(infer_pattern ctx) in
  let (ptyp_ls, _, pvar_ls) = List.unzip3 pinfer_list in
  let allvars = List.concat pvar_ls in
  let ctx' = List.fold allvars ~init:ctx ~f:(fun cx (v,t) -> Context.add_var cx v (Forall(empty_tvar_set, t))) in
  let rec handle plist elist =
    match (plist, elist) with
    | ([], []) -> ([], [])
    | ((ptyp :: plist'), (expr :: elist')) ->
        let (ccs, etyp) = infer_expr ctx' expr in
        let (ecs, typs) = handle plist' elist' in
        (ccs @ [(Uni(ptyp, etyp))] @ ecs, etyp :: typs)
    | _ -> raise (TypeError "Unequal number of pattern types and expression types. Impossible?")
  in let (ccs, _) = handle ptyp_ls expr_list in
  let subs = unify_many ccs in
  (addvars subs ctx ctx allvars)

(* context -> pattern -> (type * new_ctx * new_vars) *)
and infer_pattern ctx pat =
  match pat.ppat_desc with
  | Ppat_var(ident) ->
      let varname = ident.txt in
      let tv = fresh () in
      let typ = (T_var(tv)) in
      let ctx' = Context.add_var ctx varname (Forall(empty_tvar_set, typ)) in
      (typ, ctx', [(varname, typ)])
  | Ppat_tuple(lst) ->
      let rec loop cx ls =
        match ls with
        | [] -> ([], cx, [])
        | (pat::ls') ->
            let (typ, cx', vars) = infer_pattern cx pat in
            let (tlst, cx'', vars') = loop cx' ls' in
            (typ :: tlst, cx'', vars @ vars')
      in let (tlst, ctx', vars) = loop ctx lst in
      (T_tuple(tlst), ctx', vars)
  | _ -> raise (TypeError "Unsupported pattern")

and infer_ident ctx ident =
  match ident.txt with
  | Lident(str) ->
      (match Context.find_var ctx str with
      | Some(typ) -> ([], instantiate typ)
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

and type_expr (ctx : Context.context) (expr : expression) =
  let (ccs, typ) = infer_expr ctx expr in
  let subs = unify_many ccs in
  substitute_list subs typ

let type_structure_item (ctx : Context.context) (item : structure_item) =
  match item.pstr_desc with
  | Pstr_eval(expr, _) -> (ctx, type_expr ctx expr)
  | Pstr_value(recflag, bindings) -> (ctx_of_bindings ctx recflag bindings, v_unit)
  | _ -> raise (TypeError ("Unsupported structure"))

let rec type_structure (ctx : Context.context) (struc : structure) =
  match struc with
  | [] -> ctx
  | (struc_item :: struc') ->
      let (ctx', _) = type_structure_item ctx struc_item in
      type_structure ctx' struc'
