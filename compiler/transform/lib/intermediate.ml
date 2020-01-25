open Core_kernel
open Otwa_types
open Typed_ast
open Types
open Intermediate_ast
open Intermediate_program

exception IntermediateFailure of string


let transform_listi (context : Context.context) ~f:mapi (vars : Vars.vars) lst =
  let (vars', code_list_rev) = List.foldi lst ~init:(vars, []) ~f:(fun pos (vrs, c_lst) item ->
    let (vrs', code) = mapi context vrs pos item in
    (vrs', code :: c_lst))
  in
  let full_code = List.concat (List.rev code_list_rev) in
  (vars', full_code)

let transform_list context ~f:map vars lst =
  transform_listi context vars lst ~f:(fun ctx vrs _ item -> map ctx vrs item)

(* Gives a new vars and list of iexpression *)
let rec transform_expr (context: Context.context) (vars: Vars.vars) (expr: texpression) =
  let ityp = stoitype expr.texp_type in
  match expr.texp_desc with
  | Texp_ident(id) ->
      let var_id = Vars.lookup_var_or_global vars id in
      (vars, [Iexp_pushvar(ityp, var_id)])
  | Texp_constant(str) -> (vars, [Iexp_pushconst(ityp, str)])
  | Texp_let (rf, tvb_list, expr) ->
      let (vars1, tvb_iexprs) = transform_value_bindings context vars rf tvb_list in
      let (vars2, in_iexprs) = transform_expr context vars1 expr in
      let (vars3, block_name) = Vars.add_block vars2 in
      let res_type = stoitype expr.texp_type in
      (vars3, [Iexp_block(block_name, res_type, tvb_iexprs @ in_iexprs)])
  | Texp_fun (_, _) -> raise (IntermediateFailure "Perform closure conversion first")
  | Texp_apply (fexpr, args) -> transform_apply context vars expr.texp_type fexpr args
  | Texp_match (e, cases) -> transform_match context vars expr.texp_type e cases
  | Texp_tuple(_) ->
      let (vars1, tuple_codelst) = transform_tupleargs ~poly_wrap:true context vars expr in
      let (vars2, var_name) = Vars.add_temp_var vars1 It_pointer in
      let ituptype = tupletoitype expr.texp_type in
      (vars2, [Iexp_pushtuple(ituptype, var_name, tuple_codelst)])
  | Texp_construct (name, expr_opt) -> transform_construct context vars name expr_opt
  | Texp_ifthenelse (i, t, e_opt) ->
      let (vars1, block_name) = Vars.add_block vars in
      let (vars2, icode) = transform_expr context vars1 i in
      let (vars3, tcode) = transform_expr context vars2 t in
      (match e_opt with
      | Some(e) ->
          let (vars4, ecode) = transform_expr context vars3 e in
          (vars4, icode @ [Iexp_ifthenelse(block_name, ityp, tcode, Some(ecode))])
      | None ->
          (vars3, icode @ [Iexp_ifthenelse(block_name, ityp, tcode, None)]))


and transform_value_bindings context vars rf tvb_list =
  match rf with
  | Asttypes.Nonrecursive -> transform_value_bindings_nonrecursive context vars tvb_list
  | Asttypes.Recursive -> transform_value_bindings_recursive context vars tvb_list

and transform_value_bindings_nonrecursive context vars tvb_list =
  let (vars', code_list) = transform_list context vars tvb_list ~f:(fun _ vrs tvb ->
    let (vrs1, expr_code) = transform_expr context vrs tvb.tvb_expr in
    let (vrs2, pat_code) = transform_pat context vrs1 tvb.tvb_pat in
    (vrs2, expr_code @ pat_code)
  )
  in
  (vars', code_list)

(* Helper function, for a tuple pattern, returns it's list, otherwise a list containing just the pattern *)
and pat_tuple_list (pat : tpattern) =
  match pat.tpat_desc with
  | Tpat_tuple(ls) -> ls
  | _ -> [pat]

and transform_pat ?check:(check = true)
                  ?escape:(escape = Iexp_ifthenelse("$escape", It_none, [Iexp_fail], None))
                  ?wrapped:(wrapped = false)
                  context
                  vars
                  (pat :tpattern) =
  match pat.tpat_desc with
  | Tpat_any -> (vars, [Iexp_drop(stoitype pat.tpat_type)])
  | Tpat_var(name) ->
      let ityp = stoitype pat.tpat_type in
      let (vars1, named_var) = Vars.add_named_var vars name ityp in
      if (wrapped && (itype_needs_wrap ityp)) then
        let (vars2, wrapped_var) = Vars.add_temp_var vars1 It_poly in
        (vars2,
          [Iexp_newvar(It_poly, wrapped_var);
          Iexp_unwrap(ityp, wrapped_var, named_var)]
        )
      else
      (vars1, [Iexp_newvar(ityp, named_var)])
  | Tpat_constant(const) ->
      (* This would be shorthand for an equality check, e.g. evaluate this and make sure it's equal to 3 *)
      let (vars', check_code) =
        if check then
          let ityp = stoitype pat.tpat_type in
          if (wrapped && (itype_needs_wrap ityp)) then
            let (vars1, wrap_var) = Vars.add_temp_var vars It_poly in
            let (vars2, unwrap_var) = Vars.add_temp_var vars1 ityp in
            (vars2,
              [Iexp_newvar(It_poly, wrap_var);
              Iexp_unwrap(ityp, wrap_var, unwrap_var);
              Iexp_pushvar(ityp, unwrap_var);
              Iexp_pushconst(ityp, const);
              Iexp_binop(ityp, Ibin_ne);
              escape]
            )
          else
            (vars, [Iexp_pushconst(ityp, const); Iexp_binop(ityp, Ibin_ne); escape])
        else (vars, [])
      in
      (vars', check_code)
  | Tpat_tuple(plist) ->
      let (vars1, var_name) = Vars.add_temp_var vars It_pointer in
      let ituptype = tupletoitype pat.tpat_type in
      let (vars2, code) = transform_listi context vars1 plist ~f:(fun _ vrs pos tpat ->
        let (vrs', pat_code) = transform_pat ~check:check ~escape:escape ~wrapped:true context vrs tpat in
        (vrs', (Iexp_pushvar(It_pointer, var_name) :: Iexp_loadtupleindex(ituptype, pos) :: pat_code)))
      in
      (vars2, Iexp_newvar(It_pointer, var_name) :: code)
  | Tpat_construct (name, tpat_opt) ->
      let (vars1, var_name) = Vars.add_temp_var vars It_pointer in
      let construct = Option.value_exn (Context.find_constr context name) in
      let check_code =
        if check then
          (Iexp_pushvar(It_pointer, var_name)
          :: Iexp_loadconstructid
          :: Iexp_pushconst(It_int, Int.to_string construct.index)
          :: Iexp_binop(It_int, Ibin_ne)
          :: [escape])
        else []
      in
      let (vars2, destruct_code) =
        (match(tpat_opt) with
        | Some(tpat) ->
            let plist =
              if (List.length construct.args > 1) then
                pat_tuple_list tpat
              else
                [tpat]
            in
            let ituptype = List.map plist ~f:(fun p -> stoitype p.tpat_type) in
            transform_listi context vars1 plist ~f:(fun _ vrs pos cpat ->
              let (vrs', pat_code) = transform_pat ~check:check ~escape:escape ~wrapped:true context vrs cpat in
              (vrs', (Iexp_pushvar(It_pointer, var_name) :: Iexp_loadconstructindex(ituptype, pos) :: pat_code)))
        | None -> (vars1, []))
      in
      (vars2, Iexp_newvar(It_pointer, var_name) :: (check_code @ destruct_code))


and transform_value_bindings_recursive context vars tvb_list =
  (* Make a var for each recursive function *)
  let details = List.map tvb_list ~f:(fun tvb ->
    let rec_name =
      match tvb.tvb_pat.tpat_desc with
      | Tpat_var(name) -> name
      | _ -> raise (IntermediateFailure "Recursive bindings must be functions")
    in
    let iftype = functoitype tvb.tvb_expr.texp_type in
    let (fexpr, args) =
      match tvb.tvb_expr.texp_desc with
      | Texp_apply(fexpr_match, args_match) -> (fexpr_match, args_match)
      | _ -> raise (IntermediateFailure "Recursive bindings must be functions")
    in
    let func_name =
      match fexpr.texp_desc with
      | Texp_ident(name) ->
          if String.is_prefix name ~prefix:"$$f_" then
            name
          else raise (IntermediateFailure "Recursive bindings must be functions")
      | _ -> raise (IntermediateFailure "Recursive bindings must be functions")
    in
    let tuple_expr = List.hd_exn args in
    let ituptype = tupletoitype tuple_expr.texp_type in
    (rec_name, func_name, iftype, ituptype, tuple_expr)
  )
  in
  let (vars1, new_closure_code) = transform_list context vars details
                                    ~f:(fun _ vrs (rec_name, func_name, iftype, ituptype, _) ->
    let (vrs', var_name) = Vars.add_named_var vrs rec_name It_pointer in
    (vrs', [Iexp_newclosure(iftype, func_name, ituptype, var_name)])
  )
  in
  let (vars2, fill_closure_code) = transform_list context vars1 details
                                    ~f:(fun _ vrs (rec_name, _, _, ituptype, tuple_expr) ->
    let var_name = Option.value_exn (Vars.lookup_var vrs rec_name) in
    let (vrs', tuple_codelst) = transform_tupleargs ~poly_wrap:false context vrs tuple_expr in
    (vrs', [Iexp_fillclosure(ituptype, var_name, tuple_codelst)])
  )
  in
  (vars2, new_closure_code @ fill_closure_code)
  (* get all the closure functions and then build them all at once *)

and transform_match context vars st_res_typ expr cases =
  let (vars1, expr_code) = transform_expr context vars expr in
  let match_type = stoitype expr.texp_type in
  let result_type = stoitype st_res_typ in
  let (vars2, expr_var) = Vars.add_temp_var vars1 match_type in
  let (vars3, result_var) = Vars.add_temp_var vars2 result_type in
  let (vars4, match_block) = Vars.add_block vars3 in
  let (vars5, inner_code) = transform_list context vars4 cases ~f:(fun _ vrs case ->
    let (vrs1, case_block) = Vars.add_block vrs in
    (* These instructions check and destructure the pattern *)
    let (vrs2, pat_code) = transform_pat ~check:true ~escape:(Iexp_exitblockif(case_block))
                                            context vrs1 case.tc_lhs
    in
    (* Case expression, possibly using variables from the pattern *)
    let (vrs3, matched_code) = transform_expr context vrs2 case.tc_rhs in
    let inside_block = [Iexp_pushvar(match_type, expr_var)] @
                       pat_code @ matched_code @
                       [Iexp_newvar(result_type, result_var);
                       Iexp_exitblock(match_block)]
    in
    (vrs3, [Iexp_block(case_block, It_none, inside_block)])
  )
  in
  (vars5,
    expr_code @
    [Iexp_newvar(match_type, expr_var);
    Iexp_block(match_block, It_none, inner_code @ [Iexp_fail]);
    Iexp_pushvar(result_type, result_var)
    ]
  )

and transform_apply context vars typ fexpr args =
  match fexpr.texp_desc with
  | Texp_ident(name) ->
      let lookup = Predefined.lookup_ident name in
      (match lookup with
      | Some(_) -> transform_op context vars name args
      | None ->
          if String.is_prefix name ~prefix:"$$f_" then
            transform_mk_closure context vars typ name args
          else
            let var_name = Vars.lookup_var_or_global vars name in
            transform_apply_closure context vars fexpr.texp_type var_name args)
  | _ ->
      let (vars1, other_code) = transform_expr context vars fexpr in
      let (vars2, var_name) = Vars.add_temp_var vars1 It_pointer in
      let (vars3, apply_code) = transform_apply_closure context vars2 fexpr.texp_type var_name args in
      (vars3, other_code @ [Iexp_newvar(It_pointer, var_name)] @ apply_code)

and transform_op context vars name args =
  let (vars', arg_code) = transform_list context vars args ~f:transform_expr in
  let typ = ((List.hd_exn args).texp_type) in
  let ityp = stoitype typ in
  match name with
  | "~-" -> (vars', [Iexp_pushconst(ityp, "0")] @ arg_code @ [Iexp_binop(ityp, Ibin_sub)])
  | "ref" ->
      let (vars2, wrap_code) = transform_wrap context vars' typ in
      let (vars3, data_var) = Vars.add_temp_var vars2 It_poly in
      let (vars4, ref_var) = Vars.add_temp_var vars3 It_pointer in
      (vars4, arg_code
              @ wrap_code
              @ [Iexp_newvar(It_poly, data_var);
                 Iexp_wrap(It_poly, data_var, ref_var);
                 Iexp_pushvar(It_pointer, ref_var)]
      )
  | "!" ->
      let (vars2, ref_var) = Vars.add_temp_var vars' It_pointer in
      let (vars3, data_var) = Vars.add_temp_var vars2 It_poly in
      let ref_typ =
        match typ with
        | T_constr("ref", [a]) -> a
        | _ -> raise (IntermediateFailure "Cannot derefence non ref type")
      in
      let (vars4, unwrap_code) = transform_unwrap context vars3 ref_typ in
      (vars4, arg_code
              @ [Iexp_newvar(It_pointer, ref_var);
                 Iexp_unwrap(It_poly, ref_var, data_var);
                 Iexp_pushvar(It_poly, data_var)]
              @ unwrap_code
      )
  | ":=" ->
      let ref_typ =
        match typ with
        | T_constr("ref", [a]) -> a
        | _ -> raise (IntermediateFailure "Cannot derefence non ref type")
      in
      let (vars2, wrap_code) = transform_wrap context vars' ref_typ in
      let (vars3, data_var) = Vars.add_temp_var vars2 It_poly in
      let (vars4, ref_var) = Vars.add_temp_var vars3 It_pointer in
      (vars4, arg_code
              @ wrap_code
              @ [Iexp_newvar(It_poly, data_var);
                 Iexp_newvar(It_pointer, ref_var);
                 Iexp_update_wrap(It_poly, data_var, ref_var);
                 Iexp_pushconst(It_unit, "()")]
      )
  | _ ->
    let bop =
      (match name with
      | "+" -> Ibin_add
      | "+." -> Ibin_add
      | "-" -> Ibin_sub
      | "-." -> Ibin_sub
      | "*" -> Ibin_mul
      | "*." -> Ibin_mul
      | "/" -> Ibin_div
      | "/." -> Ibin_div
      | "<" -> Ibin_lt
      | ">" -> Ibin_gt
      | "<=" -> Ibin_le
      | ">=" -> Ibin_ge
      | "=" -> Ibin_eq
      | "&&" -> Ibin_and
      | "||" -> Ibin_or
      | _ -> raise (IntermediateFailure "Unsupported binary operation"))
    in
    (vars', arg_code @ [Iexp_binop(ityp, bop)])

(* Transforms an expression
 * If that expression is a tuple, do not add the final pushtuple instruction *)
and transform_tupleargs ?poly_wrap:(poly_wrap=false) context vars expr =
  match expr.texp_desc with
  | Texp_tuple(lst) ->
      let (vars', code_list_rev) = List.fold lst ~init:(vars, []) ~f:(fun (vrs, c_lst) item ->
        let (vrs', code) = transform_expr_wrap ~wrap:poly_wrap context vrs item in
        (vrs', code :: c_lst))
      in
      (vars', List.rev code_list_rev)
  | _ ->
      let (vars, code) = transform_expr_wrap ~wrap:poly_wrap context vars expr in
      (vars, [code])

and transform_mk_closure context vars typ name args =
  let tuple_expr = List.hd_exn args in
  let iftype = functoitype typ in
  let ituptype = tupletoitype tuple_expr.texp_type in
  let (vars1, tuple_codelst) = transform_tupleargs ~poly_wrap:false context vars tuple_expr in
  let (vars2, var_name) = Vars.add_temp_var vars1 It_pointer in
  (vars2,
    [Iexp_newclosure(iftype, name, ituptype, var_name);
     Iexp_fillclosure(ituptype, var_name, tuple_codelst);
     Iexp_pushvar(It_pointer, var_name)])

and transform_expr_wrap ?wrap:(wrap = true) context vars expr =
  let (vars1, code) = transform_expr context vars expr in
  if wrap then
    let (vars2, wrap_code) = transform_wrap context vars1 expr.texp_type in
    (vars2, code @ wrap_code)
  else (vars1, code)

and transform_wrap _context vars typ =
  let ityp = stoitype typ in
  if itype_needs_wrap ityp then
    let (vars1, unwrap_var) = Vars.add_temp_var vars ityp in
    let (vars2, wrap_var) = Vars.add_temp_var vars1 It_poly in
    (vars2,
      [Iexp_newvar(ityp, unwrap_var);
      Iexp_wrap(ityp, unwrap_var, wrap_var);
      Iexp_pushvar(It_poly, wrap_var)]
    )
  else (vars, [])

and transform_unwrap _context vars typ =
  let ityp = stoitype typ in
  if itype_needs_wrap ityp then
    let (vars1, wrap_var) = Vars.add_temp_var vars It_poly in
    let (vars2, unwrap_var) = Vars.add_temp_var vars1 ityp in
    (vars2,
      [Iexp_newvar(It_poly, wrap_var);
      Iexp_unwrap(ityp, wrap_var, unwrap_var);
      Iexp_pushvar(ityp, unwrap_var)]
    )
  else (vars, [])

and transform_apply_closure context vars typ var_name args =
  let rec loop ftyp vrs arg_list =
    match arg_list with
    | [] -> (vrs, [])
    | (arg :: arg_list') ->
        (match ftyp with
        | T_func(atyp, btyp) ->
            let iatyp = stoitype atyp in
            let ibtyp = stoitype btyp in
            let (vrs1, closure_var) = Vars.add_temp_var vrs It_pointer in
            let (vrs2, code) = transform_expr_wrap context vrs1 arg in
            let (vrs3, unwrap_code) = transform_unwrap context vrs2 btyp in
            let (vrs4, final_code) = loop btyp vrs3 arg_list' in
            (vrs4,
              [Iexp_newvar(It_pointer, closure_var);
              Iexp_callclosure((iatyp, ibtyp), closure_var, code)]
              @ unwrap_code
              @ final_code
            )
        | _ -> raise (IntermediateFailure "Cannot apply non function type "))
  in
  let (vars', loop_code) = loop typ vars args in
  (vars', (Iexp_pushvar(It_pointer, var_name)) :: loop_code)

and transform_construct context vars name expr_opt =
  let constr = Option.value_exn (Context.find_constr context name) in
  let ituptype = List.map constr.args ~f:stoitype in
  let (vars1, var_name) = Vars.add_temp_var vars It_pointer in
  match expr_opt with
  | Some(expr) ->
      (* We need to watch out for if there is one argument only, but it is a tuple *)
      if ((List.length ituptype) > 1) then
        let (vars2, tuple_codelst) = transform_tupleargs ~poly_wrap:true context vars1 expr in
        (vars2, [Iexp_pushconstruct(ituptype, var_name, constr.index, tuple_codelst)])
      else
        let (vars2, expr_code) = transform_expr_wrap ~wrap:true context vars1 expr in
        (vars2, [Iexp_pushconstruct(ituptype, var_name, constr.index, [expr_code])])
  | None ->
      (vars1, [Iexp_pushconstruct(ituptype, var_name, constr.index, [])])


let transform_structure_item context vars (si : tstructure_item) =
  match si.tstr_desc with
  | Tstr_eval(e) ->
      let(vars1, code) = transform_expr context vars e in
      (* We need to drop the resulting value on the stack *)
      (vars1, code @ [Iexp_drop(stoitype e.texp_type)])
  | Tstr_value (rf, tvb_list) -> transform_value_bindings context vars rf tvb_list
  | Tstr_type -> (vars, [])


let transform_structure context vars (st : tstructure) =
  transform_list context vars st ~f:transform_structure_item

let transform_function context (fd : Functions.func_data) =
  let vars = Vars.make_local_vars fd in
  let (vars', arg_code) = transform_pat context vars fd.fd_pat in
  let (vars'', expr_code) = transform_expr context vars' fd.fd_expr in
  let arg_type = stoitype fd.fd_pat.tpat_type in
  (vars'', (Iexp_pushvar(arg_type, Vars.function_arg)) :: (arg_code @ expr_code))

let fix_globals global_vars local_vars code =
  let fix_var (scope, name) =
    match scope with
    | Global ->
        (match Vars.lookup_var global_vars name with
        | Some(gvar) -> gvar
        | None -> raise (IntermediateFailure ("Missing global variable " ^ name)))
    | Local ->
      (match Vars.lookup_var local_vars name with
        | None -> (Global, name)
        | _ -> (Local, name))
  in
  let rec fix_instr instr =
    match instr with
    | Iexp_newvar(t, name) ->
        Iexp_newvar(t, fix_var name)
    | Iexp_pushvar(t, name) ->
        Iexp_pushvar(t, fix_var name)
    | Iexp_ifthenelse(bname, t, tcode, ecode_opt) ->
        let tcode' = fix_instr_list tcode in
        let ecode_opt' = Option.map ecode_opt ~f:fix_instr_list in
        Iexp_ifthenelse(bname, t, tcode', ecode_opt')
    | Iexp_block(bname, btyp, bcode) ->
        Iexp_block(bname, btyp, fix_instr_list bcode)
    | Iexp_newclosure(ift, fname, itt, var) ->
        Iexp_newclosure(ift, fname, itt, fix_var var)
    | Iexp_fillclosure(itt, name, tuple_lst) ->
        Iexp_fillclosure(itt, fix_var name, fix_instr_list_list tuple_lst)
    | Iexp_pushtuple(itt, name, tuple_lst) ->
        Iexp_pushtuple(itt, fix_var name, fix_instr_list_list tuple_lst)
    | Iexp_pushconstruct(itt, name, id, tuple_lst) ->
        Iexp_pushconstruct(itt, fix_var name, id, fix_instr_list_list tuple_lst)
    | _ -> instr
  and fix_instr_list lst = List.map lst ~f:fix_instr
  and fix_instr_list_list lst = List.map lst ~f:fix_instr_list
  in
  fix_instr_list code

let transform_program ?debug:(debug = false) context structure =
  let (funcs, fast) = Functions.func_transform_structure structure in
  let () = if debug then (
    Stdio.print_endline (Typed_ast.tstructure_to_string fast);
    Functions.print_func_datas funcs)
  in
  let (global_vars, init_code) = transform_structure context Vars.empty_global_vars fast in
  let ifuncs = List.map funcs ~f:(fun fd ->
    let (vars, code) = transform_function context fd in
    (fd.fd_name, {
      pf_name = fd.fd_name;
      pf_vars = vars;
      pf_code = code;
      pf_type = functoitype fd.fd_type;
      pf_cvars = List.map fd.fd_cvars ~f:(fun (name,st) -> (name, stoitype st));
      pf_export_name = fd.fd_export_name
    }))
  in
  let init_func = {
    pf_name = "$init";
    pf_vars = Vars.make_init_vars global_vars;
    pf_code = init_code;
    pf_type = (It_none, It_none);
    pf_cvars = [];
    pf_export_name = None
  }
  in
  let all_funcs = ("$init", init_func) :: ifuncs in
  let corrected_funcs = List.map all_funcs ~f:(fun (name, f) ->
    (name, {
      f with
      pf_code = fix_globals global_vars f.pf_vars f.pf_code
    }))
  in
  {
    prog_functions = Map.Poly.of_alist_exn corrected_funcs;
    prog_globals = global_vars;
    prog_initfunc = "$init"
  }
