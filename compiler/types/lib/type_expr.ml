open Core_kernel
open Parsetree
open Types
open Predefined
open Typed_ast

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

let subs_to_fresh tvars =
  List.map tvars ~f:(fun old -> (old, T_var(fresh())))

let instantiate (Forall(s, t)) =
  let subs = subs_to_fresh (Set.to_list s) in
  substitute_list subs t

let context_ftv (ctx: Context.context) =
  Set.union_list (module String) (List.map (Context.get_var_list ctx) ~f:(fun (_,t) -> ftv_scheme t))

let generalize (ctx: Context.context) t =
  let free_vars = Set.diff (ftv t) (context_ftv ctx)
  in Forall(free_vars, t)

let extract_outer_constraints ctx subs =
  let ctx_ftv = context_ftv ctx in
  let rec inner slist =
    match slist with
    | [] -> []
    | ((tv, typ) :: slist') ->
        if Set.mem ctx_ftv tv then
          (Uni(T_var(tv), typ)) :: (inner slist')
        else
          inner slist'
  in inner subs

let rec core_to_scheme_type (ct: core_type) =
  match ct.ptyp_desc with
  | Ptyp_var(str) -> T_var(str)
  | Ptyp_arrow(_, a, b) -> T_func(core_to_scheme_type a, core_to_scheme_type b)
  | Ptyp_tuple(ct_list) -> T_tuple(List.map ct_list ~f:core_to_scheme_type)
  | Ptyp_constr(id, ct_list) -> ct_constr_to_scheme_type id ct_list
  | Ptyp_poly(_, ct') -> core_to_scheme_type ct' (* Not sure about this one. What does poly do? *)
  | _ -> raise (TypeError "Unsupported core type")

and ct_constr_to_scheme_type id ct_list =
  match id.txt with
  | Lident("int") -> v_int
  | Lident("bool") -> v_bool
  | Lident("unit") -> v_unit
  | Lident(str) -> (T_constr(str, List.map ct_list ~f:core_to_scheme_type))
  | _ -> raise (TypeError "Unsupported core type construct")

let ct_to_st_with_check (ctx : Context.context) (ct: core_type) =
  let st = core_to_scheme_type ct in
  let () = Context.check_type ctx st in
  st

let list_to_single_or_tuple st_lst =
  match st_lst with
  | [] -> raise (TypeError "Expecting nonempty list of types")
  | [single] -> single
  | _ -> T_tuple(st_lst)

let type_constant (const : constant) =
  match const with
  | Pconst_integer(str, _) -> (T_val(V_int), str)
  | _ -> raise (TypeError "Unknown constant type")

(* context -> expression -> (uni_pair list * texpression) *)
let rec infer_expr (ctx : Context.context) (expr : expression) : (uni_pair list * texpression) =
  let (ccs, etyp, desc) =
    match expr.pexp_desc with
    | Pexp_constant(const) ->
        let (typ, str) = type_constant const in
        ([], typ, Texp_constant(str))
    | Pexp_construct(ident, expr_opt) -> infer_construct ctx ident expr_opt
    | Pexp_apply(f, args) -> infer_apply ctx f args
    | Pexp_ident(ident) -> infer_ident ctx ident
    | Pexp_fun(_, _, pat, body) -> infer_fun ctx pat body
    | Pexp_let(recflag, bindings, body) ->
        let (ocs, ctx', tvb_lst) = ctx_of_bindings ctx recflag bindings in
        let (ecs, ast) = infer_expr ctx' body in
        let typ = ast.texp_type in
        (ocs @ ecs, typ, Texp_let(recflag, tvb_lst, ast))
    | Pexp_tuple(lst) ->
        let ctlst = List.map lst ~f:(infer_expr ctx) in
        let (ccslst, astlst) = List.unzip ctlst in
        let tlst = List.map astlst ~f:(fun e -> e.texp_type) in
        let ccs = List.concat ccslst in
        (ccs, T_tuple(tlst), Texp_tuple(astlst))
    | Pexp_ifthenelse(iexpr, texpr, eexpr_opt) ->
        let (ics, i_ast) = infer_expr ctx iexpr in
        let ityp = i_ast.texp_type in
        let (tcs, t_ast) = infer_expr ctx texpr in
        let ttyp = t_ast.texp_type in
        (match eexpr_opt with
        | Some(eexpr) ->
            let (ecs, e_ast) = infer_expr ctx eexpr in
            let etyp = e_ast.texp_type in
            let ccs = (Uni(ityp, v_bool)) :: (Uni(ttyp, etyp)) :: (ics @ tcs @ ecs) in
            (ccs, ttyp, Texp_ifthenelse(i_ast, t_ast, Some(e_ast)))
        | None -> ((Uni(ityp, v_bool)) :: (ics @ tcs), ttyp, Texp_ifthenelse(i_ast, t_ast, None)))
    | Pexp_constraint(expr, ct) ->
        let st = ct_to_st_with_check ctx ct in
        let (ccs, ast) = infer_expr ctx expr in
        ((Uni(ast.texp_type, st)) :: ccs, ast.texp_type, ast.texp_desc)
    | Pexp_match(expr, cases) -> infer_match ctx expr cases
    | _ -> raise (TypeError "Unsupported expression")
  in (ccs, {
    texp_loc = expr.pexp_loc;
    texp_desc = desc;
    texp_type = etyp
  })

and infer_apply ctx f args =
  (* Check the function first *)
  let (fcs, f_ast) = infer_expr ctx f in
  let ftype = f_ast.texp_type in
  (* The AST has flat applies with a list of args, rather than a tree of apply with 1 arg
   * Loop through each arg and compute a new function type by partially applying it *)
  let rec partial fc args =
    match args with
    | [] -> ([], fc, [])
    | ((_, expr) :: args') ->
        (* Infer the arg *)
        let (acs, a_ast) = infer_expr ctx expr in
        let atyp = a_ast.texp_type in
        (match fc with
        | T_func(a, b) ->
            let (bcs, btyp, ast_lst) = partial b args' in
            (((Uni(a, atyp)) :: acs) @ bcs, btyp, a_ast :: ast_lst)
        | T_var(_) ->
            let a = T_var(fresh ()) in
            let b = T_var(fresh ()) in
            let (bcs, btyp, ast_lst) = partial b args' in
            let ccs = ((Uni(fc, T_func(a, b))) :: (Uni(a, atyp)) :: acs) @ bcs in
            (ccs, btyp, a_ast :: ast_lst)
        | _ -> raise (TypeError "Cannot apply a non_function"))
  in let (argcs, typ, ast_lst) = partial ftype args in
  (fcs @ argcs, typ, Texp_apply(f_ast, ast_lst))

and infer_fun ctx pat body =
  (* Get a context from the pattern *)
  let a_ast = infer_pattern ctx pat in
  let atyp = a_ast.tpat_type in
  let vars = a_ast.tpat_vars in
  let ctx' = List.fold vars ~init:ctx ~f:(fun cx (v,t) -> Context.add_var cx v (Forall(empty_tvar_set, t))) in
  (* Use this context to check the body *)
  let (bcs, b_ast) = infer_expr ctx' body in
  let btyp = b_ast.texp_type in
  (bcs, T_func(atyp, btyp), Texp_fun(a_ast, b_ast))

and ctx_of_bindings ctx recflag bindings =
  match recflag with
  | Asttypes.Nonrecursive -> ctx_of_nonrec_bindings ctx bindings
  | Asttypes.Recursive -> ctx_of_rec_bindings ctx bindings

and ctx_of_nonrec_bindings ctx bindings =
  match bindings with
  | [] -> ([], ctx, [])
  | (binding :: bindings') ->
      let (acs, ctx', tvb) = ctx_of_nonrec_binding ctx binding in
      let (bcs, ctx'', tvb_lst) = ctx_of_nonrec_bindings ctx' bindings' in
      (acs @ bcs, ctx'', tvb :: tvb_lst)

and ctx_of_nonrec_binding ctx binding =
  (* Type the expression, so no constraints *)
  let (tcs, e_ast) = type_expr ctx binding.pvb_expr in
  let typ = e_ast.texp_type in
  (* Then the pattern *)
  let p_ast = infer_pattern ctx binding.pvb_pat in
  let ptyp = p_ast.tpat_type in
  let vars = p_ast.tpat_vars in
  (* Then unify *)
  let subs = unify ptyp typ in
  let ocs = extract_outer_constraints ctx subs in
  let (ctx', svars) = addvars subs ctx ctx vars in
  (tcs @ ocs, ctx', {
    tvb_pat = tpattern_substitute subs p_ast;
    tvb_expr = e_ast;
    tvb_vars = svars
  })

(* For a list of (variable,scheme_type), substitute subs,
 * then convert types into a scheme by making them forall over type variables not in ctx,
 * before adding them to cx. Was originally part of another function but I need it twice. *)
and addvars subs ctx cx vlist =
  match vlist with
  | [] -> (cx, [])
  | ((v,t)::vlist') ->
      let truetype = substitute_list subs t in
      let genscheme = generalize ctx truetype in
      let cx' = Context.add_var cx v genscheme in
      Stdio.print_endline ("Bind " ^ v ^ " to " ^ (string_of_scheme genscheme));
      let (cx'', svars) = addvars subs ctx cx' vlist' in
      (cx'', (v,genscheme) :: svars)

and ctx_of_rec_bindings ctx bindings =
  (* Extract a list of lhs patterns and rhs expressions *)
  let pe_list = List.map bindings ~f:(fun vb -> (vb.pvb_pat, vb.pvb_expr)) in
  let (pat_list, expr_list) = List.unzip pe_list in
  (* Type check the patterns, getting their types and vars *)
  let p_ast_lst = List.map pat_list ~f:(infer_pattern ctx) in
  let (ptyp_ls, pvar_ls) = List.unzip (List.map p_ast_lst ~f:(fun p -> (p.tpat_type, p.tpat_vars))) in
  (* Join the vars and create a context from them *)
  let allvars = List.concat pvar_ls in
  let ctx' = List.fold allvars ~init:ctx ~f:(fun cx (v,t) -> Context.add_var cx v (Forall(empty_tvar_set, t))) in
  (* tpattern list -> scheme_type list -> expression list -> (uni list * scheme_type list * tvalue_binding list) *)
  (* For each let binding, we take it's tpattern p_ast, pattern's scheme_type ptyp and expression,
   * And produce constraints, an expression type and a tvalue_binding *)
  let rec handle pa_lst pt_lst e_lst =
    match (pa_lst, pt_lst, e_lst) with
    | ([], [], []) -> ([], [], [])
    | ((p_ast :: pa_lst'), (ptyp :: pt_lst'), (expr :: e_lst')) ->
        let (ccs, e_ast) = infer_expr ctx' expr in
        let etyp = e_ast.texp_type in
        let (ecs, typs, tvb_lst) = handle pa_lst' pt_lst' e_lst' in
        let tvb = {
          tvb_pat = p_ast;
          tvb_expr = e_ast; (* Need to substitute later *)
          tvb_vars = [] (* Compute this later *)
        } in
        (* The pattern type and expression type must unify *)
        (ccs @ [(Uni(ptyp, etyp))] @ ecs, etyp :: typs, tvb :: tvb_lst)
    | _ -> raise (TypeError "Unequal number of pattern types and expression types. Impossible?")
  in let (ccs, _, tvb_lst) = handle p_ast_lst ptyp_ls expr_list in
  let subs = unify_many ccs in
  let ocs = extract_outer_constraints ctx subs in
  (* fctx is the final context, svars is the substituted version of allvars *)
  let (fctx, svars) = addvars subs ctx ctx allvars in
  (* Loop through tvalue_bindings fixing them.
   * As allvars and svars are in order, we just take from the head that number of vars for the tvb_vars *)
  let rec fixup tlst svars =
    match tlst with
    | [] -> []
    | (tvb :: tlst') ->
        let var_count = List.length tvb.tvb_pat.tpat_vars in
        let (ourvars, othervars) = List.split_n svars var_count in
        let tvb' = {
          tvb_pat = tpattern_substitute subs tvb.tvb_pat;
          tvb_expr = texpression_substitute subs tvb.tvb_expr;
          tvb_vars = ourvars
        } in
        let fixedlst = fixup tlst' othervars in
        (tvb' :: fixedlst)
  in
  (ocs, fctx, fixup tvb_lst svars)

(* context -> pattern -> tpattern *)
and infer_pattern ctx pat =
  let(ptyp, pvars, pdesc) =
    match pat.ppat_desc with
    | Ppat_var(ident) ->
        (* Maps to a fresh variable *)
        let varname = ident.txt in
        let tv = fresh () in
        let typ = (T_var(tv)) in
        (typ, [(varname, typ)], Tpat_var(varname))
    | Ppat_tuple(lst) ->
        (* Loop through subpatterns, returning type list, combined vars list and tpattern list *)
        let rec loop ls =
          match ls with
          | [] -> ([], [], [])
          | (pat::ls') ->
              let (p_ast) = infer_pattern ctx pat in
              let typ = p_ast.tpat_type in
              let vars = p_ast.tpat_vars in
              let (tlst, vars', ast_lst) = loop ls' in
              (typ :: tlst, vars @ vars', p_ast :: ast_lst)
        in let (tlst, vars, ast_lst) = loop lst in
        (T_tuple(tlst), vars, Tpat_tuple(ast_lst))
    | Ppat_constraint(pat', ct) ->
        (* Check the underlying pattern and unify with constraint *)
        let st = ct_to_st_with_check ctx ct in
        let p_ast = infer_pattern ctx pat' in
        let subs = unify p_ast.tpat_type st in
        let vars' = List.map p_ast.tpat_vars ~f:(fun (v, t) -> (v, substitute_list subs t)) in
        (st, vars', p_ast.tpat_desc)
    | Ppat_constant(const) ->
        let (ctyp, str) = type_constant const in
        (ctyp, [], Tpat_constant(str))
    | Ppat_construct(id, pat_opt) -> infer_pattern_construct ctx id pat_opt
    | Ppat_any ->
        let tv = fresh () in
        let typ = (T_var(tv)) in
        (typ, [], Tpat_any)
    | _ -> raise (TypeError "Unsupported pattern")
  in {
    tpat_desc = pdesc;
    tpat_loc = pat.ppat_loc;
    tpat_type = ptyp;
    tpat_vars = pvars
  }

and infer_ident ctx ident =
  match ident.txt with
  | Lident(str) ->
      (match Context.find_var ctx str with
      | Some(typ) -> ([], instantiate typ, Texp_ident(str))
      | None ->
          (match lookup_ident str with
          | Some(t2) -> ([], t2, Texp_ident(str))
          | None -> raise (TypeError ("Unknown identifer '" ^ str ^ "'"))))
  | _ -> raise (TypeError ("Unknown strange identifer"))

and infer_construct ctx ident expr_opt =
  match ident.txt with
  | Lident("true") -> ([], T_val(V_bool), Texp_constant("true"))
  | Lident("false") -> ([], T_val(V_bool), Texp_constant("false"))
  | Lident(str) -> infer_ctx_construct ctx str expr_opt
  | _ -> raise (TypeError "Unknown construct")

and infer_pattern_construct ctx ident pat_opt =
  match ident.txt with
  | Lident("true") -> (v_bool, [], Tpat_constant("true"))
  | Lident("false") -> (v_bool, [], Tpat_constant("false"))
  | Lident(str) -> infer_pattern_ctx_construct ctx str pat_opt
  | _ -> raise (TypeError "Unknown construct")

(* Infer a construct from the context *)
and infer_ctx_construct ctx name expr_opt =
  match Context.find_constr ctx name with
  | Some(constr) ->
      let variant = Option.value_exn (Context.find_type ctx constr.type_name) in
      let subs = subs_to_fresh variant.args in
      let constr_type = T_constr(variant.name, List.map variant.args ~f:(fun tv -> T_var(tv))) in
      (match (expr_opt, List.is_empty constr.args) with
      | (None, true) -> ([], substitute_list subs constr_type, Texp_construct(name, None))
      | (Some(expr), false) ->
          let (ccs, actual_ast) = infer_expr ctx expr in
          let actual_type = actual_ast.texp_type in
          let expected_type = substitute_list subs (list_to_single_or_tuple constr.args) in
          let ccs' = (Uni(expected_type, actual_type)) :: ccs in
          let subs_type = substitute_list subs constr_type in
          (ccs', subs_type, Texp_construct(name, Some(actual_ast)))
      | (_, true) -> raise (TypeError ("No arguments expected for constructor " ^ name))
      | (_, false) -> raise (TypeError ("Arguments expected for constructor " ^ name)))
  | _ -> raise (TypeError ("Unknown constructor " ^ name))

(* Infer a construct from the context, but a pattern is supplied instead of an expression *)
(* TODO maybe there's a way to combine these? *)
and infer_pattern_ctx_construct ctx name pat_opt =
  match Context.find_constr ctx name with
  | Some(constr) ->
      let variant = Option.value_exn (Context.find_type ctx constr.type_name) in
      let subs = subs_to_fresh variant.args in
      let constr_type = T_constr(variant.name, List.map variant.args ~f:(fun tv -> T_var(tv))) in
      (match (pat_opt, List.is_empty constr.args) with
      | (None, true) -> (substitute_list subs constr_type, [], Tpat_construct(name, None))
      | (Some(pat), false) ->
          let p_ast = infer_pattern ctx pat in
          let actual_type = p_ast.tpat_type in
          let vars = p_ast.tpat_vars in
          let expected_type = substitute_list subs (list_to_single_or_tuple constr.args) in
          let subs' = unify expected_type actual_type in
          let vars' = List.map vars ~f:(fun (v,t) -> (v, substitute_list subs' t)) in
          (substitute_list subs' constr_type, vars', Tpat_construct(name, Some(tpattern_substitute subs' p_ast)))
      | (_, true) -> raise (TypeError ("No arguments expected for constructor " ^ name))
      | (_, false) -> raise (TypeError ("Arguments expected for constructor " ^ name)))
  | _ -> raise (TypeError ("Unknown constructor " ^ name))

and infer_match ctx expr cases =
  let (ecs, e_ast) = infer_expr ctx expr in
  let etyp = e_ast.texp_type in
  (* case -> incoming type -> (constraints * tcase list) *)
  let rec handle_cases cs ityp =
    match cs with
    | [] -> ([], [])
    | (case :: cs') ->
        let (p_ast) = infer_pattern ctx case.pc_lhs in
        let ptyp = p_ast.tpat_type in
        let vars = p_ast.tpat_vars in
        let ctx' = List.fold vars ~init:ctx ~f:(fun cx (v,t) -> Context.add_var cx v (Forall(empty_tvar_set, t))) in
        let (ccs, c_ast) = infer_expr ctx' case.pc_rhs in
        let ctyp = c_ast.texp_type in
        let (ccs', tc_lst) = handle_cases cs' ctyp in
        let tcase = {
          tc_lhs = p_ast;
          tc_rhs = c_ast
        } in
        ((Uni(ptyp, etyp)) :: (Uni(ityp, ctyp)) :: (ccs @ ccs'), tcase :: tc_lst)
  in let restyp = (T_var(fresh())) in
  let (ccs, tc_lst) = handle_cases cases restyp in
  (ecs @ ccs, restyp, Texp_match(e_ast, tc_lst))


(* Infer the type and constraints, and then solve these to get just a type *)
and type_expr (ctx : Context.context) (expr : expression) =
  let (ccs, t_ast) = infer_expr ctx expr in
  let subs = unify_many ccs in
  let fixed_tree = texpression_substitute subs t_ast in
  let ocs = extract_outer_constraints ctx subs in
  (ocs, fixed_tree)

let add_types_to_context (ctx : Context.context) (type_decls : type_declaration list) =
  let map_ct_to_tvar (ct, _) =
    match ct.ptyp_desc with
    | Ptyp_var(str) -> str
    | _ -> raise (TypeError "Expecting a type variable")
  in let fold_decl cx decl =
    let name = decl.ptype_name.txt in
    let tvars = List.map decl.ptype_params ~f:map_ct_to_tvar in
    Context.add_type cx name tvars
  in List.fold type_decls ~init:ctx ~f:fold_decl

let ctx_of_decls (ctx : Context.context) (type_decls : type_declaration list) =
  let ctx' = add_types_to_context ctx type_decls in
  let ctx_of_constr tname cx constr =
    let name = constr.pcd_name.txt in
    match constr.pcd_args with
    | Pcstr_tuple(ct_list) ->
        let st_list = List.map ct_list ~f:(ct_to_st_with_check cx)
        in Context.add_constr cx name st_list tname
    | Pcstr_record(_) -> raise (TypeError "Records are not supported")
  in let ctx_of_decl cx decl =
    let name = decl.ptype_name.txt in
    match decl.ptype_kind with
    | Ptype_variant(constrs) -> List.fold constrs ~init:cx ~f:(ctx_of_constr name)
    | _ -> raise (TypeError "Unsupported type kind")
  in List.fold type_decls ~init:ctx' ~f:ctx_of_decl

let type_structure_item (ctx : Context.context) (item : structure_item) =
  let (nctx, typ, desc) =
    match item.pstr_desc with
    | Pstr_eval(expr, _) ->
        (* TODO more outer constraints *)
        let (_, e_ast) = type_expr ctx expr in
        (ctx, e_ast.texp_type, Tstr_eval(e_ast))
    | Pstr_value(recflag, bindings) ->
        (* TODO watch out for the global constraints _ below *)
        let (_, ctx', tvb_lst) = ctx_of_bindings ctx recflag bindings in
        (ctx', v_unit, Tstr_value(recflag, tvb_lst))
    | Pstr_type(_, type_decls) -> (ctx_of_decls ctx type_decls, v_unit, Tstr_type)
    | _ -> raise (TypeError ("Unsupported structure"))
  in (nctx, {
    tstr_desc = desc;
    tstr_loc = item.pstr_loc;
    tstr_type = typ
  })

let rec type_structure (ctx : Context.context) (struc : structure) =
  match struc with
  | [] -> (ctx, [])
  | (struc_item :: struc') ->
      let (ctx', si_ast) = type_structure_item ctx struc_item in
      let (ctx'', si_ast_lst) = type_structure ctx' struc' in
      (ctx'', si_ast :: si_ast_lst)
