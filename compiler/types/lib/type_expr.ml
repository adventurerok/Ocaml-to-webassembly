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

let type_constant (const : constant) =
  match const with
  | Pconst_integer(_, _) -> (T_val(V_int))
  | _ -> raise (TypeError "Unknown constant type")

(* context -> expression -> (uni_pair list * scheme) *)
let rec infer_expr (ctx : Context.context) (expr : expression) : (uni_pair list * scheme_type) =
  match expr.pexp_desc with
  | Pexp_constant(const) -> ([], type_constant const)
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
  | Pexp_ifthenelse(iexpr, texpr, eexpr_opt) ->
      let (ics, ityp) = infer_expr ctx iexpr in
      let (tcs, ttyp) = infer_expr ctx texpr in
      (match eexpr_opt with
      | Some(eexpr) ->
          let (ecs, etyp) = infer_expr ctx eexpr in
          ((Uni(ityp, v_bool)) :: (Uni(ttyp, etyp)) :: (ics @ tcs @ ecs), ttyp)
      | None -> ((Uni(ityp, v_bool)) :: (ics @ tcs), ttyp))
  | Pexp_constraint(expr, ct) ->
      let st = ct_to_st_with_check ctx ct in
      let (ccs, typ) = infer_expr ctx expr in
      ((Uni(typ, st)) :: ccs, typ)
  | Pexp_match(expr, cases) -> infer_match ctx expr cases
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
  let (atyp, vars) = infer_pattern ctx pat in
  let ctx' = List.fold vars ~init:ctx ~f:(fun cx (v,t) -> Context.add_var cx v (Forall(empty_tvar_set, t))) in
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
  let (ptyp, vars) = infer_pattern ctx binding.pvb_pat in
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
  let (ptyp_ls, pvar_ls) = List.unzip pinfer_list in
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
      (typ, [(varname, typ)])
  | Ppat_tuple(lst) ->
      let rec loop ls =
        match ls with
        | [] -> ([], [])
        | (pat::ls') ->
            let (typ, vars) = infer_pattern ctx pat in
            let (tlst, vars') = loop ls' in
            (typ :: tlst, vars @ vars')
      in let (tlst, vars) = loop lst in
      (T_tuple(tlst), vars)
  | Ppat_constraint(pat', ct) ->
      let st = ct_to_st_with_check ctx ct in
      let (typ, vars) = infer_pattern ctx pat' in
      let subs = unify typ st in
      let vars' = List.map vars ~f:(fun (v, t) -> (v, substitute_list subs t)) in
      (st, vars')
  | Ppat_constant(const) -> (type_constant const, [])
  | Ppat_construct(id, pat_opt) -> infer_pattern_construct ctx id pat_opt
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
  | Lident(str) -> infer_ctx_construct ctx str expr_opt
  | _ -> raise (TypeError "Unknown construct")

and infer_pattern_construct ctx ident pat_opt =
  match ident.txt with
  | Lident("true") -> (v_bool, [])
  | Lident("false") -> (v_bool, [])
  | Lident(str) -> infer_pattern_ctx_construct ctx str pat_opt
  | _ -> raise (TypeError "Unknown construct")

and infer_ctx_construct ctx name expr_opt =
  let constr = Context.find_constr ctx name in
  match constr with
  | Some(args, tname) ->
      let (_, tvargs) = Option.value_exn (Context.find_type ctx tname) in
      let subs = subs_to_fresh tvargs in
      let constr_type = T_constr(tname, List.map tvargs ~f:(fun tv -> T_var(tv))) in
      (match (expr_opt, List.is_empty args) with
      | (None, true) -> ([], substitute_list subs constr_type)
      | (Some(expr), false) ->
          let (ccs, actual_type) = infer_expr ctx expr in
          let expected_type = substitute_list subs (T_tuple(args)) in
          ((Uni(expected_type, actual_type)) :: ccs, substitute_list subs constr_type)
      | (_, true) -> raise (TypeError ("No arguments expected for constructor " ^ name))
      | (_, false) -> raise (TypeError ("Arguments expected for constructor " ^ name)))
  | _ -> raise (TypeError ("Unknown constructor " ^ name))

and infer_pattern_ctx_construct ctx name pat_opt =
  let constr = Context.find_constr ctx name in
  match constr with
  | Some(args, tname) ->
      let (_, tvargs) = Option.value_exn (Context.find_type ctx tname) in
      let subs = subs_to_fresh tvargs in
      let constr_type = T_constr(tname, List.map tvargs ~f:(fun tv -> T_var(tv))) in
      (match (pat_opt, List.is_empty args) with
      | (None, true) -> (substitute_list subs constr_type, [])
      | (Some(pat), false) ->
          let (actual_type, vars) = infer_pattern ctx pat in
          let expected_type = substitute_list subs (T_tuple(args)) in
          let subs' = unify expected_type actual_type in
          let vars' = List.map vars ~f:(fun (v,t) -> (v, substitute_list subs' t)) in
          (substitute_list subs constr_type, vars')
      | (_, true) -> raise (TypeError ("No arguments expected for constructor " ^ name))
      | (_, false) -> raise (TypeError ("Arguments expected for constructor " ^ name)))
  | _ -> raise (TypeError ("Unknown constructor " ^ name))

and infer_match ctx expr cases =
  let (ecs, etyp) = infer_expr ctx expr in
  let rec handle_cases cs ityp =
    match cs with
    | [] -> []
    | (case :: cs') ->
        let (ptyp, vars) = infer_pattern ctx case.pc_lhs in
        let ctx' = List.fold vars ~init:ctx ~f:(fun cx (v,t) -> Context.add_var cx v (Forall(empty_tvar_set, t))) in
        let (ccs, ctyp) = infer_expr ctx' case.pc_rhs in
        let ccs' = handle_cases cs' ctyp in
        ((Uni(ptyp, etyp)) :: (Uni(ityp, ctyp)) :: (ccs @ ccs'))
  in let restyp = (T_var(fresh())) in
  let ccs = handle_cases cases restyp in
  (ecs @ ccs, restyp)


and type_expr (ctx : Context.context) (expr : expression) =
  let (ccs, typ) = infer_expr ctx expr in
  let subs = unify_many ccs in
  substitute_list subs typ

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
  match item.pstr_desc with
  | Pstr_eval(expr, _) -> (ctx, type_expr ctx expr)
  | Pstr_value(recflag, bindings) -> (ctx_of_bindings ctx recflag bindings, v_unit)
  | Pstr_type(_, type_decls) -> (ctx_of_decls ctx type_decls, v_unit)
  | _ -> raise (TypeError ("Unsupported structure"))

let rec type_structure (ctx : Context.context) (struc : structure) =
  match struc with
  | [] -> ctx
  | (struc_item :: struc') ->
      let (ctx', _) = type_structure_item ctx struc_item in
      type_structure ctx' struc'
