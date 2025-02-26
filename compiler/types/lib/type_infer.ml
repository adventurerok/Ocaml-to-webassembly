open Core_kernel
open Parsetree
open Otwa_base
open Types
open Predefined
open Typed_ast

exception TypeError of string

type state = {
  mutable next_tvar : int;
  mutable next_var : int;
}

let fresh state =
  let rec int_to_tvar x =
    let ccode = (x % 26) + 97 in
    let c = Char.of_int_exn ccode in
    let nx = x / 26 in
    match nx with
    | 0 -> [c]
    | _ -> c :: (int_to_tvar nx)
  in
  let index = state.next_tvar in
  (state.next_tvar <- index + 1; String.of_char_list (List.rev (int_to_tvar index)))

let subs_to_fresh state name tvars =
  (if Config.global.trace then
    Stdio.print_endline ("Subs to fresh for " ^ name)
  );
  List.map tvars ~f:(fun old ->
    let fresh_var = fresh state in
    (if Config.global.trace then
      Stdio.print_endline ("Stf map '" ^ old ^ " to '" ^ fresh_var)
    );
    (old, T_var(fresh_var))
  )

let instantiate state name (Forall(s, t)) =
  let subs = subs_to_fresh state ("instantiate " ^ name) (Set.to_list s) in
  substitute_list subs t

let context_ftv (ctx: Context.context) =
  Set.Poly.union_list (List.map (Context.get_var_list ctx) ~f:(fun var -> ftv_scheme var.typ))

let generalize (ctx: Context.context) t =
  let free_vars = Set.diff (ftv t) (context_ftv ctx)
  in Forall(free_vars, t)

let mk_uni (a, b, loc, txt) =
  (if Config.global.trace then
    Stdio.print_endline ("Make uni " ^ (string_of_scheme_type a) ^ " to " ^ (string_of_scheme_type b) ^
     "    at" ^ (loc_to_string loc) ^ " with reason " ^ txt)
  );
  (Uni(a, b, loc))

let extract_outer_constraints ctx subs =
  let ctx_ftv = context_ftv ctx in
  let rec inner slist =
    match slist with
    | [] -> []
    | ((tv, typ) :: slist') ->
        if Set.mem ctx_ftv tv then
          (mk_uni(T_var(tv), typ, Location.none, "extract outer constraints")) :: (inner slist')
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
  | Lident("float") -> v_float
  | Lident(str) -> (T_constr(str, List.map ct_list ~f:core_to_scheme_type))
  | _ -> raise (TypeError "Unsupported core type construct")

let ct_to_st_with_check (ctx : Context.context) (ct: core_type) =
  let st = core_to_scheme_type ct in
  let () = Context.check_type ctx st in
  st

let type_constant (const : constant) =
  match const with
  | Pconst_integer(str, _) -> (v_int, str)
  | Pconst_float(str, _) -> (v_float, str)
  | _ -> raise (TypeError "Unknown constant type")

(* context -> expression -> (uni_pair list * texpression) *)
let rec infer_expr (state : state) (ctx : Context.context) (expr : expression) : (uni_pair list * texpression) =
  let (ccs, etyp, desc) =
    match expr.pexp_desc with
    | Pexp_constant(const) ->
        let (typ, str) = type_constant const in
        ([], typ, Texp_constant(str))
    | Pexp_construct(ident, expr_opt) -> infer_construct state ctx ident expr_opt
    | Pexp_apply(f, args) -> infer_apply state ctx f args
    | Pexp_ident(ident) -> infer_ident state ctx ident
    | Pexp_fun(_, _, pat, body) -> infer_fun state ctx pat body
    | Pexp_let(recflag, bindings, body) ->
        let (ocs, ctx', tvb_lst) = ctx_of_bindings state ctx recflag bindings in
        let (ecs, ast) = infer_expr state ctx' body in
        let typ = ast.texp_type in
        (ocs @ ecs, typ, Texp_let(recflag, tvb_lst, ast))
    | Pexp_tuple(lst) ->
        let ctlst = List.map lst ~f:(infer_expr state ctx) in
        let (ccslst, astlst) = List.unzip ctlst in
        let tlst = List.map astlst ~f:(fun e -> e.texp_type) in
        let ccs = List.concat ccslst in
        (ccs, T_tuple(tlst), Texp_tuple(astlst))
    | Pexp_ifthenelse(iexpr, texpr, eexpr_opt) ->
        let (ics, i_ast) = infer_expr state ctx iexpr in
        let ityp = i_ast.texp_type in
        let (tcs, t_ast) = infer_expr state ctx texpr in
        let ttyp = t_ast.texp_type in
        (match eexpr_opt with
        | Some(eexpr) ->
            let (ecs, e_ast) = infer_expr state ctx eexpr in
            let etyp = e_ast.texp_type in
            let ccs = (mk_uni(ityp, v_bool, expr.pexp_loc, "if")) :: (mk_uni(ttyp, etyp, expr.pexp_loc, "thenelse")) :: (ics @ tcs @ ecs) in
            (ccs, ttyp, Texp_ifthenelse(i_ast, t_ast, Some(e_ast)))
        | None -> ((mk_uni(ityp, v_bool, expr.pexp_loc, "if")) :: (ics @ tcs), ttyp, Texp_ifthenelse(i_ast, t_ast, None)))
    | Pexp_constraint(expr, ct) ->
        let st = ct_to_st_with_check ctx ct in
        let (ccs, ast) = infer_expr state ctx expr in
        ((mk_uni(ast.texp_type, st, expr.pexp_loc, "constraint")) :: ccs, ast.texp_type, ast.texp_desc)
    | Pexp_match(expr, cases) -> infer_match state ctx expr cases
    | Pexp_while(condition, inner) -> infer_while state ctx condition inner
    | Pexp_for(pat, min, max, dir, inner) -> infer_for state ctx pat min max dir inner
    | Pexp_sequence(a, b) ->
        let (acs, a_ast) = infer_expr state ctx a in
        let (bcs, b_ast) = infer_expr state ctx b in
        (acs @ bcs, b_ast.texp_type, Texp_sequence(a_ast, b_ast))
    | _ -> raise (TypeError "Unsupported expression")
  in (ccs, {
    texp_loc = expr.pexp_loc;
    texp_desc = desc;
    texp_type = etyp
  })

and infer_apply state ctx f args =
  (* Check the function first *)
  let (fcs, f_ast) = infer_expr state ctx f in
  let ftype = f_ast.texp_type in
  (* The AST has flat applies with a list of args, rather than a tree of apply with 1 arg
   * Loop through each arg and compute a new function type by partially applying it *)
  let rec partial fc args =
    match args with
    | [] -> ([], fc, [])
    | ((_, expr) :: args') ->
        (* Infer the arg *)
        let (acs, a_ast) = infer_expr state ctx expr in
        let atyp = a_ast.texp_type in
        (match fc with
        | T_func(a, b) ->
            let (bcs, btyp, ast_lst) = partial b args' in
            (((mk_uni(a, atyp, expr.pexp_loc, "applyend")) :: acs) @ bcs, btyp, a_ast :: ast_lst)
        | T_var(_) ->
            let a_var = fresh state in
            let b_var = fresh state in
            (if Config.global.trace then
              Stdio.print_endline ("New apply type vars '" ^ a_var ^ " -> '" ^ b_var)
            );
            let a = T_var(a_var) in
            let b = T_var(b_var) in
            let (bcs, btyp, ast_lst) = partial b args' in
            let ccs = ((mk_uni(fc, T_func(a, b), expr.pexp_loc, "applyfunc")) :: (mk_uni(a, atyp, expr.pexp_loc, "applyarg")) :: acs) @ bcs in
            (ccs, btyp, a_ast :: ast_lst)
        | _ -> raise (TypeError "Cannot apply a non_function"))
  in let (argcs, typ, ast_lst) = partial ftype args in
  (fcs @ argcs, typ, Texp_apply(f_ast, ast_lst))

and infer_fun state ctx pat body =
  (* Get a context from the pattern *)
  let a_ast = infer_pattern state ctx pat in
  let atyp = a_ast.tpat_type in
  let vars = a_ast.tpat_vars in
  let ctx' = List.fold vars ~init:ctx ~f:(fun cx (v,t) -> Context.add_var cx v (Forall(Set.Poly.empty, t))) in
  (* Use this context to check the body *)
  let (bcs, b_ast) = infer_expr state ctx' body in
  let btyp = b_ast.texp_type in
  (bcs, T_func(atyp, btyp), Texp_fun(a_ast, b_ast))

and ctx_of_bindings state ctx recflag bindings =
  match recflag with
  | Asttypes.Nonrecursive -> ctx_of_nonrec_bindings state ctx bindings
  | Asttypes.Recursive -> ctx_of_rec_bindings state ctx bindings

and ctx_of_nonrec_bindings state ctx bindings =
  match bindings with
  | [] -> ([], ctx, [])
  | (binding :: bindings') ->
      let (acs, ctx', tvb) = ctx_of_nonrec_binding state ctx binding in
      let (bcs, ctx'', tvb_lst) = ctx_of_nonrec_bindings state ctx' bindings' in
      (acs @ bcs, ctx'', tvb :: tvb_lst)

and ctx_of_nonrec_binding state ctx binding =
  (* Type the expression, so no constraints *)
  let (tcs, e_ast) = type_expr state ctx binding.pvb_expr in
  let typ = e_ast.texp_type in
  (* Then the pattern *)
  let p_ast = infer_pattern state ctx binding.pvb_pat in
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
      (if Config.global.trace then
        Stdio.print_endline ("Bind " ^ (tident_to_string v) ^ " to " ^ (string_of_scheme genscheme))
      );
      let (cx'', svars) = addvars subs ctx cx' vlist' in
      (cx'', (v,genscheme) :: svars)

and ctx_of_rec_bindings state ctx bindings =
  (* Extract a list of lhs patterns and rhs expressions *)
  let pe_list = List.map bindings ~f:(fun vb -> (vb.pvb_pat, vb.pvb_expr)) in
  let (pat_list, expr_list) = List.unzip pe_list in
  (* Type check the patterns, getting their types and vars *)
  let p_ast_lst = List.map pat_list ~f:(infer_pattern state ctx) in
  let (ptyp_ls, pvar_ls) = List.unzip (List.map p_ast_lst ~f:(fun p -> (p.tpat_type, p.tpat_vars))) in
  (* Join the vars and create a context from them *)
  let allvars = List.concat pvar_ls in
  let ctx' = List.fold allvars ~init:ctx ~f:(fun cx (v,t) -> Context.add_var cx v (Forall(Set.Poly.empty, t))) in
  (* tpattern list -> scheme_type list -> expression list -> (uni list * scheme_type list * tvalue_binding list) *)
  (* For each let binding, we take it's tpattern p_ast, pattern's scheme_type ptyp and expression,
   * And produce constraints, an expression type and a tvalue_binding *)
  let rec handle pa_lst pt_lst e_lst =
    match (pa_lst, pt_lst, e_lst) with
    | ([], [], []) -> ([], [], [])
    | ((p_ast :: pa_lst'), (ptyp :: pt_lst'), (expr :: e_lst')) ->
        let (ccs, e_ast) = infer_expr state ctx' expr in
        let etyp = e_ast.texp_type in
        let (ecs, typs, tvb_lst) = handle pa_lst' pt_lst' e_lst' in
        let tvb = {
          tvb_pat = p_ast;
          tvb_expr = e_ast; (* Need to substitute later *)
          tvb_vars = [] (* Compute this later *)
        } in
        (* The pattern type and expression type must unify *)
        (ccs @ [(mk_uni(ptyp, etyp, expr.pexp_loc, "recbind"))] @ ecs, etyp :: typs, tvb :: tvb_lst)
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
and infer_pattern state ctx pat =
  (if Config.global.trace then
    Stdio.print_endline ("Infer pattern start")
  );
  let(ptyp, pvars, pdesc) =
    match pat.ppat_desc with
    | Ppat_var(ident) ->
        (* Maps to a fresh variable *)
        let varname = ident.txt in
        let tv = fresh state in
        let typ = (T_var(tv)) in
        let var_id = state.next_var in
        (if Config.global.trace then
          Stdio.print_endline ("New ident " ^ (tident_to_string (varname, var_id)) ^ " with tvar '" ^ tv)
        );
        state.next_var <- var_id + 1;
        (typ, [((varname, var_id), typ)], Tpat_var((varname, var_id)))
    | Ppat_tuple(lst) ->
        (* Loop through subpatterns, returning type list, combined vars list and tpattern list *)
        let rec loop ls =
          match ls with
          | [] -> ([], [], [])
          | (pat::ls') ->
              let (p_ast) = infer_pattern state ctx pat in
              let typ = p_ast.tpat_type in
              let vars = p_ast.tpat_vars in
              let (tlst, vars', ast_lst) = loop ls' in
              (typ :: tlst, vars @ vars', p_ast :: ast_lst)
        in let (tlst, vars, ast_lst) = loop lst in
        (T_tuple(tlst), vars, Tpat_tuple(ast_lst))
    | Ppat_constraint(pat', ct) ->
        (* Check the underlying pattern and unify with constraint *)
        let st = ct_to_st_with_check ctx ct in
        let p_ast = infer_pattern state ctx pat' in
        let subs = unify p_ast.tpat_type st in
        let vars' = List.map p_ast.tpat_vars ~f:(fun (v, t) -> (v, substitute_list subs t)) in
        (st, vars', p_ast.tpat_desc)
    | Ppat_constant(const) ->
        let (ctyp, str) = type_constant const in
        (ctyp, [], Tpat_constant(str))
    | Ppat_construct(id, pat_opt) -> infer_pattern_construct state ctx id pat_opt
    | Ppat_any ->
        let tv = fresh state in
        let typ = (T_var(tv)) in
        (typ, [], Tpat_any)
    | _ -> raise (TypeError "Unsupported pattern")
  in
  (if Config.global.trace then
    Stdio.print_endline ("Infer pattern end with typ = " ^ (string_of_scheme_type ptyp))
  );
  {
    tpat_desc = pdesc;
    tpat_loc = pat.ppat_loc;
    tpat_type = ptyp;
    tpat_vars = pvars
  }

and infer_ident state ctx ident =
  match ident.txt with
  | Lident(str) ->
      (match Context.find_var ctx str with
      | Some(var) -> ([], instantiate state str var.typ, Texp_ident((str, var.id)))
      | None ->
          (match lookup_ident str with
          | Some(sch) ->
              let t2 = instantiate state str sch in
              ([], t2, Texp_ident((str, -1)))
          | None -> raise (TypeError ("Unknown identifer '" ^ str ^ "'"))))
  | _ -> raise (TypeError ("Unknown strange identifer"))

and infer_construct state ctx ident expr_opt =
  match ident.txt with
  | Lident("true") -> ([], T_val(V_bool), Texp_constant("true"))
  | Lident("false") -> ([], T_val(V_bool), Texp_constant("false"))
  | Lident("()") -> ([], T_val(V_unit), Texp_constant("unit"))
  | Lident(str) -> infer_ctx_construct state ctx str expr_opt
  | _ -> raise (TypeError "Unknown construct")

and infer_pattern_construct state ctx ident pat_opt =
  match ident.txt with
  | Lident("true") -> (v_bool, [], Tpat_constant("true"))
  | Lident("false") -> (v_bool, [], Tpat_constant("false"))
  | Lident("()") -> (v_unit, [], Tpat_constant("unit"))
  | Lident(str) -> infer_pattern_ctx_construct state ctx str pat_opt
  | _ -> raise (TypeError "Unknown construct")

(* Infer a construct from the context *)
and infer_ctx_construct state ctx name expr_opt =
  match Context.find_constr ctx name with
  | Some(constr) ->
      let variant = Option.value_exn (Context.find_type ctx constr.type_name) in
      let subs = subs_to_fresh state name variant.args in
      let constr_typ = substitute_list subs (T_constr(variant.name, List.map variant.args ~f:(fun tv -> T_var(tv)))) in
      (match (expr_opt, List.is_empty constr.args) with
      | (None, true) -> ([], constr_typ, Texp_construct(name, []))
      | (Some(expr), false) ->
          let (ccs, actual_ast) = infer_expr state ctx expr in
          let expected_typ = substitute_list subs (T_tuple(constr.args)) in
          (* Our typed ast is actually different from the OCaml one for constructs *)
          (* Theirs uses an optional tuple or other expression, while ours uses a list *)
          if (List.length constr.args) = 1 then
            let actual_typ = T_tuple([actual_ast.texp_type]) in
            let ccs' = (mk_uni(expected_typ, actual_typ, expr.pexp_loc, "construct1arg")) :: ccs in
            (ccs', constr_typ, Texp_construct(name, [actual_ast]))
          else
            let actual_typ = actual_ast.texp_type in
            let ccs' = (mk_uni(expected_typ, actual_typ, expr.pexp_loc, "constructNarg")) :: ccs in
            (match actual_ast.texp_desc with
            | Texp_tuple(ls) ->
                (ccs', constr_typ, Texp_construct(name, ls))
            | _ -> raise (TypeError ("Expecting a tuple for constructor aruments " ^ name)))
      | (_, true) -> raise (TypeError ("No arguments expected for constructor " ^ name))
      | (_, false) -> raise (TypeError ("Arguments expected for constructor " ^ name)))
  | _ -> raise (TypeError ("Unknown constructor " ^ name))

(* Infer a construct from the context, but a pattern is supplied instead of an expression *)
(* TODO maybe there's a way to combine these? *)
and infer_pattern_ctx_construct state ctx name pat_opt =
  match Context.find_constr ctx name with
  | Some(constr) ->
      let variant = Option.value_exn (Context.find_type ctx constr.type_name) in
      let subs = subs_to_fresh state name variant.args in
      let constr_typ = substitute_list subs (T_constr(variant.name, List.map variant.args ~f:(fun tv -> T_var(tv)))) in
      (match (pat_opt, List.is_empty constr.args) with
      | (None, true) -> (constr_typ, [], Tpat_construct(name, []))
      | (Some(pat), false) ->
          let p_ast = infer_pattern state ctx pat in
          let expected_typ = substitute_list subs (T_tuple(constr.args)) in
          (if Config.global.trace then
            Stdio.print_endline ("Infer construct " ^ name ^ " expected type is " ^ (string_of_scheme_type expected_typ))
          );
          let vars = p_ast.tpat_vars in
          if (List.length constr.args) = 1 then
            let actual_typ = T_tuple([p_ast.tpat_type]) in
            (if Config.global.trace then
              Stdio.print_endline ("Infer 1 arg construct " ^ name ^ " actual type is " ^ (string_of_scheme_type actual_typ))
            );
            let subs' = unify expected_typ actual_typ in
            let vars' = List.map vars ~f:(fun (v,t) -> (v, substitute_list subs' t)) in
            let subs_typ = substitute_list subs' constr_typ in
            let subs_ast_lst = [tpattern_substitute subs' p_ast] in
            (subs_typ, vars', Tpat_construct(name, subs_ast_lst))
          else
            let actual_typ = p_ast.tpat_type in
            (if Config.global.trace then
              Stdio.print_endline ("Infer 2+ arg construct " ^ name ^ " actual type is " ^ (string_of_scheme_type actual_typ))
            );
            let subs' = unify expected_typ actual_typ in
            let vars' = List.map vars ~f:(fun (v,t) -> (v, substitute_list subs' t)) in
            let subs_typ = substitute_list subs' constr_typ in
            (if Config.global.trace then
              Stdio.print_endline ("Subs typ is " ^ (string_of_scheme_type subs_typ))
            );
            (match p_ast.tpat_desc with
            | Tpat_tuple(ls) ->
                let subs_ast_lst = List.map ls ~f:(tpattern_substitute subs') in
                (subs_typ, vars', Tpat_construct(name, subs_ast_lst))
            | _ -> raise (TypeError ("Expecting a tuple for constructor arguments " ^ name)))
      | (_, true) -> raise (TypeError ("No arguments expected for constructor " ^ name))
      | (_, false) -> raise (TypeError ("Arguments expected for constructor " ^ name)))
  | _ -> raise (TypeError ("Unknown constructor " ^ name))

and infer_match state ctx expr cases =
  let (ecs, e_ast) = infer_expr state ctx expr in
  let etyp = e_ast.texp_type in
  (* case -> incoming type -> (constraints * tcase list) *)
  let rec handle_cases cs ityp =
    match cs with
    | [] -> ([], [])
    | (case :: cs') ->
        let (p_ast) = infer_pattern state ctx case.pc_lhs in
        let ptyp = p_ast.tpat_type in
        let vars = p_ast.tpat_vars in
        let ctx' = List.fold vars ~init:ctx ~f:(fun cx (v,t) -> Context.add_var cx v (Forall(Set.Poly.empty, t))) in
        let (ccs, c_ast) = infer_expr state ctx' case.pc_rhs in
        let ctyp = c_ast.texp_type in
        let (ccs', tc_lst) = handle_cases cs' ctyp in
        let tcase = {
          tc_lhs = p_ast;
          tc_rhs = c_ast
        } in
        ((mk_uni(ptyp, etyp, expr.pexp_loc, "matchpat")) :: (mk_uni(ityp, ctyp, expr.pexp_loc, "matchexpr")) :: (ccs @ ccs'), tcase :: tc_lst)
  in
  let restyp_var = fresh state in
  let restyp = (T_var(restyp_var)) in
  (if Config.global.trace then
    Stdio.print_endline ("Match statement with result type variable '" ^ restyp_var)
  );
  let (ccs, tc_lst) = handle_cases cases restyp in
  (ecs @ ccs, restyp, Texp_match(e_ast, tc_lst))

and infer_while state ctx condition inner =
  let (ccs, c_ast) = infer_expr state ctx condition in
  let (ics, i_ast) = infer_expr state ctx inner in
  (
    (mk_uni(c_ast.texp_type, v_bool, c_ast.texp_loc, "whilecond"))
    :: (mk_uni(i_ast.texp_type, v_unit, i_ast.texp_loc, "whilebody"))
    :: (ccs @ ics),
    v_unit, Texp_while(c_ast, i_ast)
  )

and infer_for state ctx pat min max dir inner =
  let (inner_ctx, var_opt) =
    match pat.ppat_desc with
    | Ppat_any -> (ctx, None)
    | Ppat_var(ident) ->
        let varname = ident.txt in
        let var_id = state.next_var in
        state.next_var <- var_id + 1;
        let ctx' = Context.add_var ctx (varname, var_id) (Forall(Set.Poly.empty, v_int)) in
        (ctx', Some(varname))
    | _ -> raise (TypeError("For loop index must be variable or _"))
  in
  let (min_cs, min_ast) = infer_expr state ctx min in
  let (max_cs, max_ast) = infer_expr state ctx max in
  let (inner_cs, inner_ast) = infer_expr state inner_ctx inner in
  let for_cs = [(mk_uni(min_ast.texp_type, v_int, min_ast.texp_loc, "formin"));
                (mk_uni(max_ast.texp_type, v_int, max_ast.texp_loc, "formax"));
                (mk_uni(inner_ast.texp_type, v_unit, inner_ast.texp_loc, "forbody"))]
  in (min_cs @ max_cs @ inner_cs @ for_cs, v_unit, Texp_for(var_opt, min_ast, max_ast, dir, inner_ast))

(* Infer the type and constraints, and then solve these to get just a type *)
and type_expr (state : state) (ctx : Context.context) (expr : expression) =
  let (ccs, t_ast) = infer_expr state ctx expr in
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

let type_structure_item (state : state) (ctx : Context.context) (item : structure_item) =
  let (nctx, typ, desc) =
    match item.pstr_desc with
    | Pstr_eval(expr, _) ->
        (* TODO more outer constraints *)
        let (_, e_ast) = type_expr state ctx expr in
        (ctx, e_ast.texp_type, Tstr_eval(e_ast))
    | Pstr_value(recflag, bindings) ->
        (* TODO watch out for the global constraints _ below *)
        let (_, ctx', tvb_lst) = ctx_of_bindings state ctx recflag bindings in
        (ctx', v_unit, Tstr_value(recflag, tvb_lst))
    | Pstr_type(_, type_decls) -> (ctx_of_decls ctx type_decls, v_unit, Tstr_type)
    | _ -> raise (TypeError ("Unsupported structure"))
  in (nctx, {
    tstr_desc = desc;
    tstr_loc = item.pstr_loc;
    tstr_type = typ
  })

type result = {
  tres_structure : tstructure;
  tres_context : Context.context;
  tres_next_var : int;
}

let type_structure (ctx : Context.context) (struc : structure) =
  let state = {
    next_tvar = 0;
    next_var = 0;
  }
  in
  let (tstruc_rev, ctx') = List.fold struc ~init:([], ctx) ~f:(fun (lst, cx) si ->
    let (cx', si_ast) = type_structure_item state cx si in
    (si_ast :: lst, cx')
  )
  in
  let tstruc = List.rev tstruc_rev in
  {
    tres_structure = tstruc;
    tres_context = ctx';
    tres_next_var = state.next_var;
  }
