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
      let (vars1, tuple_codelst) = transform_tupleargs context vars expr in
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

and transform_pat ?check:(check = true) ?escape:(escape = Iexp_ifthenelse("$escape", It_unit, [Iexp_fail], None)) context vars (pat :tpattern) =
  match pat.tpat_desc with
  | Tpat_any -> (vars, [Iexp_drop(stoitype pat.tpat_type)])
  | Tpat_var(name) ->
      let ityp = stoitype pat.tpat_type in
      let (vars', var_name) = Vars.add_named_var vars name ityp in
      (vars', [Iexp_newvar(ityp, var_name)])
  | Tpat_constant(const) ->
      (* This would be shorthand for an equality check, e.g. evaluate this and make sure it's equal to 3 *)
      let check_code =
        if check then
          let typ = stoitype pat.tpat_type in
          [Iexp_pushconst(typ, const); Iexp_binop(typ, Ibin_ne); escape]
        else []
      in
      (vars, check_code)
  | Tpat_tuple(plist) ->
      let (vars1, var_name) = Vars.add_temp_var vars It_pointer in
      let ituptype = tupletoitype pat.tpat_type in
      let (vars2, code) = transform_listi context vars1 plist ~f:(fun _ vrs pos tpat ->
        let (vrs', pat_code) = transform_pat ~check:check ~escape:escape context vrs tpat in
        (vrs', (Iexp_pushvar(It_pointer, var_name) :: Iexp_loadtupleindex(ituptype, pos) :: pat_code)))
      in
      (vars2, Iexp_newvar(It_pointer, var_name) :: code)
  | Tpat_construct (name, tpat_opt) ->
      let (vars1, var_name) = Vars.add_temp_var vars It_pointer in
      let check_code =
        if check then
          let construct = Option.value_exn (Context.find_constr context name) in
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
            let plist = pat_tuple_list tpat in
            let ituptype = List.map plist ~f:(fun p -> stoitype p.tpat_type) in
            transform_listi context vars1 plist ~f:(fun _ vrs pos cpat ->
              let (vrs', pat_code) = transform_pat ~check:check ~escape:escape context vrs cpat in
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
          if String.is_prefix name ~prefix:"$f_" then
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
    let (vrs', tuple_codelst) = transform_tupleargs context vrs tuple_expr in
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
          if String.is_prefix name ~prefix:"$f_" then
            transform_mk_closure context vars typ name args
          else
            transform_apply_closure context vars fexpr.texp_type name args)
  | _ -> raise (IntermediateFailure "Applying other expressions not yet supported")

and transform_op context vars name args =
  let (vars', arg_code) = transform_list context vars args ~f:transform_expr in
  let ityp = stoitype ((List.hd_exn args).texp_type) in
  let bop =
    match name with
    | "+" -> Ibin_add
    | "-" -> Ibin_sub
    | "*" -> Ibin_mul
    | "/" -> Ibin_div
    | "<" -> Ibin_lt
    | ">" -> Ibin_gt
    | "<=" -> Ibin_le
    | ">=" -> Ibin_ge
    | "=" -> Ibin_eq
    | "&&" -> Ibin_and
    | "||" -> Ibin_or
    | _ -> raise (IntermediateFailure "Unsupported binary operation")
  in
  (vars', arg_code @ [Iexp_binop(ityp, bop)])

(* Transforms an expression
 * If that expression is a tuple, do not add the final pushtuple instruction *)
and transform_tupleargs context vars expr =
  match expr.texp_desc with
  | Texp_tuple(lst) ->
      let (vars', code_list_rev) = List.fold lst ~init:(vars, []) ~f:(fun (vrs, c_lst) item ->
        let (vrs', code) = transform_expr context vrs item in
        (vrs', code :: c_lst))
      in
      (vars', List.rev code_list_rev)
  | _ ->
      let (vars, code) = transform_expr context vars expr in
      (vars, [code])

and transform_mk_closure context vars typ name args =
  let tuple_expr = List.hd_exn args in
  let iftype = functoitype typ in
  let ituptype = tupletoitype tuple_expr.texp_type in
  let (vars1, tuple_codelst) = transform_tupleargs context vars tuple_expr in
  let (vars2, var_name) = Vars.add_temp_var vars1 It_pointer in
  (vars2,
    [Iexp_newclosure(iftype, name, ituptype, var_name);
     Iexp_fillclosure(ituptype, var_name, tuple_codelst)])

and transform_apply_closure context vars typ name args =
  (* Arg goes on top of stack, and closure 1 down *)
  let rec loop ftyp vrs arg_list =
    match arg_list with
    | [] -> (vrs, [])
    | (arg :: arg_list') ->
        (match ftyp with
        | T_func(atyp, btyp) ->
            let iatyp = stoitype atyp in
            let ibtyp = stoitype btyp in
            let (vrs', code) = transform_expr context vars arg in
            let (vrs'', final_code) = loop btyp vrs' arg_list' in
            (vrs'', code @ [Iexp_callclosure((iatyp, ibtyp))] @ final_code)
        | _ -> raise (IntermediateFailure "Cannot apply non function type "))
  in
  let (vars', loop_code) = loop typ vars args in
  let var_name = Vars.lookup_var_or_global vars' name in
  (vars', (Iexp_pushvar(It_pointer, var_name)) :: loop_code)

and transform_construct context vars name expr_opt =
  let constr = Option.value_exn (Context.find_constr context name) in
  let ituptype = List.map constr.args ~f:stoitype in
  let (vars1, var_name) = Vars.add_temp_var vars It_pointer in
  match expr_opt with
  | Some(expr) ->
      let (vars2, tuple_codelst) = transform_tupleargs context vars1 expr in
      (vars2, [Iexp_pushconstruct(ituptype, var_name, constr.index, tuple_codelst)])
  | None ->
      (vars1, [Iexp_pushconstruct(ituptype, var_name, constr.index, [])])


let transform_structure_item context vars (si : tstructure_item) =
  match si.tstr_desc with
  | Tstr_eval(e) -> transform_expr context vars e
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
    | Global -> Option.value_exn (Vars.lookup_var global_vars name)
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
  let () = if debug then
    Stdio.print_endline (Typed_ast.tstructure_to_string fast);
    Functions.print_func_datas funcs
  in
  let (global_vars, init_code) = transform_structure context Vars.empty_global_vars fast in
  let ifuncs = List.map funcs ~f:(fun fd ->
    let (vars, code) = transform_function context fd in
    (fd.fd_name, {
      pf_name = fd.fd_name;
      pf_vars = vars;
      pf_code = code;
      pf_type = functoitype fd.fd_type;
      pf_cvars = List.map fd.fd_cvars ~f:(fun (name,st) -> (name, stoitype st))
    }))
  in
  let init_func = {
    pf_name = "$init";
    pf_vars = Vars.make_init_vars global_vars;
    pf_code = init_code @ [Iexp_pushconst(It_unit, "unit")];
    pf_type = (It_unit, It_unit);
    pf_cvars = []
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
