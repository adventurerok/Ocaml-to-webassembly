open Core_kernel
open Otwa_types
open Typed_ast
open Types
open Intermediate_ast
open Intermediate_program

exception IntermediateFailure of string

(* Transform and flatten a list *)
let transform_listi ~f:mapi lst =
  List.concat (List.mapi ~f:mapi lst)

let transform_list ~f:map lst =
  List.concat (List.map ~f:map lst)

type state = {
  context: Context.context;
  mutable vars: Vars.vars
}

let update_vars (state : state) (vars, thing) =
  state.vars <- vars;
  thing

(* Gives a new vars and list of iexpression *)
let rec transform_expr (state: state) (expr: texpression) =
  let ityp = stoitype expr.texp_type in
  match expr.texp_desc with
  | Texp_ident(id) ->
      let var_id = Vars.lookup_var_or_global state.vars id in
      [Iexp_getvar(ityp, var_id)]
  | Texp_constant(str) -> [Iexp_pushconst(ityp, str)]
  | Texp_let (rf, tvb_list, expr) ->
      let tvb_iexprs = transform_value_bindings state rf tvb_list in
      let in_iexprs = transform_expr state expr in
      let block_name = update_vars state (Vars.add_block state.vars) in
      let res_type = stoitype expr.texp_type in
      [Iexp_block(block_name, res_type, tvb_iexprs @ in_iexprs)]
  | Texp_fun (_, _) -> raise (IntermediateFailure "Perform closure conversion first")
  | Texp_apply (fexpr, args) -> transform_apply state expr.texp_type fexpr args
  | Texp_match (e, cases) -> transform_match state expr.texp_type e cases
  | Texp_tuple(_) ->
      let tuple_codelst = transform_tupleargs ~poly_box:true state expr in
      let var_name = update_vars state (Vars.add_temp_var state.vars It_pointer) in
      let ituptype = tupletoitype expr.texp_type in
      [Iexp_pushtuple(ituptype, var_name, tuple_codelst)]
  | Texp_construct (name, ls) -> transform_construct state name ls
  | Texp_ifthenelse (i, t, e_opt) ->
      let block_name = update_vars state (Vars.add_block state.vars) in
      let icode = transform_expr state i in
      let tcode = transform_expr state t in
      (match e_opt with
      | Some(e) ->
          let ecode = transform_expr state e in
          icode @ [Iexp_ifthenelse(block_name, ityp, tcode, Some(ecode))]
      | None ->
          icode @ [Iexp_ifthenelse(block_name, ityp, tcode, None)])
  | Texp_while(cond, inner) ->
      transform_while state cond inner
  | Texp_for(var_opt, min, max, dir, inner) ->
      transform_for state var_opt min max dir inner
  | Texp_sequence(a, b) ->
      transform_sequence state a b


and transform_value_bindings state rf tvb_list =
  match rf with
  | Asttypes.Nonrecursive -> transform_value_bindings_nonrecursive state tvb_list
  | Asttypes.Recursive -> transform_value_bindings_recursive state tvb_list

and transform_value_bindings_nonrecursive state tvb_list =
  let code_list = List.concat (List.map tvb_list ~f:(fun tvb ->
    let expr_code = transform_expr state tvb.tvb_expr in
    let pat_code = transform_pat state tvb.tvb_pat in
    expr_code @ pat_code
  ))
  in
  code_list

(* Helper function, for a tuple pattern, returns it's list, otherwise a list containing just the pattern *)
and pat_tuple_list (pat : tpattern) =
  match pat.tpat_desc with
  | Tpat_tuple(ls) -> ls
  | _ -> [pat]

and transform_pat ?check:(check = true)
                  ?escape:(escape = Iexp_ifthenelse("$escape", It_none, [Iexp_fail], None))
                  ?boxed:(boxed = false)
                  state
                  (pat :tpattern) =
  match pat.tpat_desc with
  | Tpat_any -> [Iexp_drop(stoitype pat.tpat_type)]
  | Tpat_var(name) ->
      let ityp = stoitype pat.tpat_type in
      let named_var = update_vars state (Vars.add_named_var state.vars name ityp) in
      if (boxed && (itype_needs_box ityp)) then
        let boxed_var = update_vars state (Vars.add_temp_var state.vars It_poly) in
        [Iexp_setvar(It_poly, boxed_var);
        Iexp_unbox(ityp, boxed_var, named_var)]
      else
      [Iexp_setvar(ityp, named_var)]
  | Tpat_constant(const) ->
      (* This would be shorthand for an equality check, e.g. evaluate this and make sure it's equal to 3 *)
      if check then
        let ityp = stoitype pat.tpat_type in
        if (boxed && (itype_needs_box ityp)) then
          let box_var = update_vars state (Vars.add_temp_var state.vars It_poly) in
          let unbox_var = update_vars state (Vars.add_temp_var state.vars ityp) in
          [Iexp_setvar(It_poly, box_var);
          Iexp_unbox(ityp, box_var, unbox_var);
          Iexp_getvar(ityp, unbox_var);
          Iexp_pushconst(ityp, const);
          Iexp_binop(ityp, Ibin_ne);
          escape]
        else
          [Iexp_pushconst(ityp, const); Iexp_binop(ityp, Ibin_ne); escape]
      else []
  | Tpat_tuple(plist) ->
      let var_name = update_vars state (Vars.add_temp_var state.vars It_pointer) in
      let ituptype = tupletoitype pat.tpat_type in
      let code = transform_listi plist ~f:(fun pos tpat ->
        let pat_code = transform_pat ~check:check ~escape:escape ~boxed:true state tpat in
        (Iexp_getvar(It_pointer, var_name) :: Iexp_loadtupleindex(ituptype, pos) :: pat_code))
      in
      (Iexp_setvar(It_pointer, var_name) :: code)
  | Tpat_construct (name, plist) ->
      let var_name = update_vars state (Vars.add_temp_var state.vars It_pointer) in
      let construct = Option.value_exn (Context.find_constr state.context name) in
      let check_code =
        if check then
          (Iexp_getvar(It_pointer, var_name)
          :: Iexp_loadconstructid
          :: Iexp_pushconst(It_int, Int.to_string construct.index)
          :: Iexp_binop(It_int, Ibin_ne)
          :: [escape])
        else []
      in
      let destruct_code =
        let ituptype = List.map plist ~f:(fun p -> stoitype p.tpat_type) in
        transform_listi plist ~f:(fun pos cpat ->
          let pat_code = transform_pat ~check:check ~escape:escape ~boxed:true state cpat in
          (Iexp_getvar(It_pointer, var_name) :: Iexp_loadconstructindex(ituptype, pos) :: pat_code))
      in
      (Iexp_setvar(It_pointer, var_name) :: (check_code @ destruct_code))


and transform_value_bindings_recursive state tvb_list =
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
  let new_closure_code = transform_list details
                                    ~f:(fun (rec_name, func_name, iftype, ituptype, _) ->
    let var_name = update_vars state (Vars.add_named_var state.vars rec_name It_pointer) in
    [Iexp_newclosure(iftype, func_name, ituptype, var_name)]
  )
  in
  let fill_closure_code = transform_list details
                                    ~f:(fun (rec_name, _, _, ituptype, tuple_expr) ->
    let var_name = Option.value_exn (Vars.lookup_var state.vars rec_name) in
    let tuple_codelst = transform_tupleargs ~poly_box:false state tuple_expr in
    [Iexp_fillclosure(ituptype, var_name, tuple_codelst)]
  )
  in
  new_closure_code @ fill_closure_code
  (* get all the closure functions and then build them all at once *)

and transform_match state st_res_typ expr cases =
  let expr_code = transform_expr state expr in
  let match_type = stoitype expr.texp_type in
  let result_type = stoitype st_res_typ in
  let expr_var = update_vars state (Vars.add_temp_var state.vars match_type) in
  let result_var = update_vars state (Vars.add_temp_var state.vars result_type) in
  let match_block = update_vars state (Vars.add_block state.vars) in
  let inner_code = transform_list cases ~f:(fun case ->
    let case_block = update_vars state (Vars.add_block state.vars) in
    (* These instructions check and destructure the pattern *)
    let pat_code = transform_pat ~check:true ~escape:(Iexp_exitblockif(case_block))
                                            state case.tc_lhs
    in
    (* Case expression, possibly using variables from the pattern *)
    let matched_code = transform_expr state case.tc_rhs in
    let inside_block = [Iexp_getvar(match_type, expr_var)] @
                       pat_code @ matched_code @
                       [Iexp_setvar(result_type, result_var);
                       Iexp_exitblock(match_block)]
    in
    [Iexp_block(case_block, It_none, inside_block)]
  )
  in
  expr_code @
  [Iexp_setvar(match_type, expr_var);
  Iexp_block(match_block, It_none, inner_code @ [Iexp_fail]);
  Iexp_getvar(result_type, result_var)
  ]

and transform_apply state typ fexpr args =
  match fexpr.texp_desc with
  | Texp_ident(name) ->
      let lookup = Predefined.lookup_ident name in
      (match lookup with
      | Some(_) -> transform_op state name args
      | None ->
          if String.is_prefix name ~prefix:"$$f_" then
            transform_mk_closure state typ name args
          else
            let var_name = Vars.lookup_var_or_global state.vars name in
            transform_apply_closure state fexpr.texp_type var_name args)
  | _ ->
      let other_code = transform_expr state fexpr in
      let var_name = update_vars state (Vars.add_temp_var state.vars It_pointer) in
      let apply_code = transform_apply_closure state fexpr.texp_type var_name args in
      (other_code @ [Iexp_setvar(It_pointer, var_name)] @ apply_code)

and transform_op state name args =
  let arg_code = transform_list args ~f:(transform_expr state) in
  let typ = ((List.hd_exn args).texp_type) in
  let ityp = stoitype typ in
  match name with
  | "~-" | "~-." ->
      (match ityp with
      | It_float ->
          arg_code @ [Iexp_unop(ityp, Iun_neg)]
      | _ ->
          [Iexp_pushconst(ityp, "0")] @ arg_code @ [Iexp_binop(ityp, Ibin_sub)])
  | "ref" ->
      let box_code = transform_box state typ in
      let data_var = update_vars state (Vars.add_temp_var state.vars It_poly) in
      let ref_var = update_vars state (Vars.add_temp_var state.vars It_pointer) in
      arg_code
      @ box_code
      @ [Iexp_setvar(It_poly, data_var);
         Iexp_newbox(It_poly, data_var, ref_var);
         Iexp_getvar(It_pointer, ref_var)]
  | "!" ->
      let ref_var = update_vars state (Vars.add_temp_var state.vars It_pointer) in
      let data_var = update_vars state (Vars.add_temp_var state.vars It_poly) in
      let ref_typ =
        match typ with
        | T_constr("ref", [a]) -> a
        | _ -> raise (IntermediateFailure "Cannot derefence non ref type")
      in
      let unbox_code = transform_unbox state ref_typ in
      arg_code
      @ [Iexp_setvar(It_pointer, ref_var);
         Iexp_unbox(It_poly, ref_var, data_var);
         Iexp_getvar(It_poly, data_var)]
      @ unbox_code
  | ":=" ->
      let ref_typ =
        match typ with
        | T_constr("ref", [a]) -> a
        | _ -> raise (IntermediateFailure "Cannot derefence non ref type")
      in
      let box_code = transform_box state ref_typ in
      let data_var = update_vars state (Vars.add_temp_var state.vars It_poly) in
      let ref_var = update_vars state (Vars.add_temp_var state.vars It_pointer) in
      arg_code
      @ box_code
      @ [Iexp_setvar(It_poly, data_var);
         Iexp_setvar(It_pointer, ref_var);
         Iexp_updatebox(It_poly, data_var, ref_var);
         Iexp_pushconst(It_unit, "()")]
  | "not" ->
      (arg_code @ [Iexp_unop(ityp, Iun_eqz)])
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
    (arg_code @ [Iexp_binop(ityp, bop)])

(* Transforms an expression
 * If that expression is a tuple, do not add the final pushtuple instruction *)
and transform_tupleargs ?poly_box:(poly_box=false) state expr =
  match expr.texp_desc with
  | Texp_tuple(lst) ->
      List.map lst ~f:(transform_expr_box ~box:poly_box state)
  | _ ->
      let code = transform_expr_box ~box:poly_box state expr in
      [code]

and transform_mk_closure state typ name args =
  let tuple_expr = List.hd_exn args in
  let iftype = functoitype typ in
  let ituptype = tupletoitype tuple_expr.texp_type in
  let tuple_codelst = transform_tupleargs ~poly_box:false state tuple_expr in
  let var_name = update_vars state (Vars.add_temp_var state.vars It_pointer) in
  [Iexp_newclosure(iftype, name, ituptype, var_name);
   Iexp_fillclosure(ituptype, var_name, tuple_codelst);
   Iexp_getvar(It_pointer, var_name)]

and transform_expr_box ?box:(box = true) state expr =
  let code = transform_expr state expr in
  if box then
    let box_code = transform_box state expr.texp_type in
    (code @ box_code)
  else code

and transform_box state typ =
  let ityp = stoitype typ in
  if itype_needs_box ityp then
    let unbox_var = update_vars state (Vars.add_temp_var state.vars ityp) in
    let box_var = update_vars state (Vars.add_temp_var state.vars It_poly) in
    [Iexp_setvar(ityp, unbox_var);
    Iexp_newbox(ityp, unbox_var, box_var);
    Iexp_getvar(It_poly, box_var)]
  else []

and transform_unbox state typ =
  let ityp = stoitype typ in
  if itype_needs_box ityp then
    let box_var = update_vars state (Vars.add_temp_var state.vars It_poly) in
    let unbox_var = update_vars state (Vars.add_temp_var state.vars ityp) in
    [Iexp_setvar(It_poly, box_var);
    Iexp_unbox(ityp, box_var, unbox_var);
    Iexp_getvar(ityp, unbox_var)]
  else []

and transform_apply_closure state typ var_name args =
  let rec loop ftyp arg_list =
    match arg_list with
    | [] -> []
    | (arg :: arg_list') ->
        (match ftyp with
        | T_func(atyp, btyp) ->
            let iatyp = stoitype atyp in
            let ibtyp = stoitype btyp in
            let closure_var = update_vars state (Vars.add_temp_var state.vars It_pointer) in
            let code = transform_expr_box state arg in
            let unbox_code = transform_unbox state btyp in
            let final_code = loop btyp arg_list' in
            [Iexp_setvar(It_pointer, closure_var);
            Iexp_callclosure((iatyp, ibtyp), closure_var, code)]
            @ unbox_code
            @ final_code
        | _ -> raise (IntermediateFailure "Cannot apply non function type "))
  in
  let loop_code = loop typ args in
  ((Iexp_getvar(It_pointer, var_name)) :: loop_code)

and transform_construct state name ls =
  let constr = Option.value_exn (Context.find_constr state.context name) in
  let ituptype = List.map constr.args ~f:stoitype in
  let var_name = update_vars state (Vars.add_temp_var state.vars It_pointer) in
  let tuple_codelst = List.map ~f:(transform_expr_box ~box:true state) ls in
  [Iexp_pushconstruct(ituptype, var_name, constr.index, tuple_codelst)]


and transform_while state cond inner =
  let cond_code = transform_expr state cond in
  let inner_code = transform_expr state inner in
  let break_block = update_vars state (Vars.add_block state.vars) in
  let continue_block = update_vars state (Vars.add_block state.vars) in
  let loop_inside =
    cond_code
    @ [Iexp_unop(It_bool, Iun_eqz);
       Iexp_exitblockif(break_block)]
    @ inner_code
    @ [Iexp_drop(It_unit)]
  in
  [Iexp_loop(break_block, continue_block, loop_inside); Iexp_pushconst(It_unit, "()")]

and transform_for state var_opt min max dir inner =
  let for_var =
    match var_opt with
    | Some(var_name) -> update_vars state (Vars.add_named_var state.vars var_name It_int)
    | None -> update_vars state (Vars.add_temp_var state.vars It_int)
  in
  let min_code = transform_expr state min in
  let max_var = update_vars state (Vars.add_temp_var state.vars It_int) in
  let max_code = transform_expr state max in
  let inner_code = transform_expr state inner in
  let break_block = update_vars state (Vars.add_block state.vars) in
  let continue_block = update_vars state (Vars.add_block state.vars) in
  let is_forwards =
    match dir with
    | Asttypes.Upto -> true
    | Asttypes.Downto -> false
  in
  let pre_loop =
    min_code
    @ [Iexp_setvar(It_int, for_var)]
    @ max_code
    @ [Iexp_setvar(It_int, max_var)]
  in
  let loop_inside =
    [Iexp_getvar(It_int, for_var);
     Iexp_getvar(It_int, max_var);
     Iexp_binop(It_int, if is_forwards then Ibin_gt else Ibin_lt);
     Iexp_exitblockif(break_block)]
    @ inner_code
    @ [Iexp_drop(It_unit);
       Iexp_getvar(It_int, for_var);
       Iexp_pushconst(It_int, "1");
       Iexp_binop(It_int, if is_forwards then Ibin_add else Ibin_sub);
       Iexp_setvar(It_int, for_var)]
  in
  (pre_loop @ [Iexp_loop(break_block, continue_block, loop_inside); Iexp_pushconst(It_unit, "()")])


and transform_sequence state a b =
  let a_code = transform_expr state a in
  let b_code = transform_expr state b in
  (a_code @ [Iexp_drop(stoitype a.texp_type)] @ b_code)

let transform_structure_item state (si : tstructure_item) =
  match si.tstr_desc with
  | Tstr_eval(e) ->
      let code = transform_expr state e in
      (* We need to drop the resulting value on the stack *)
      (code @ [Iexp_drop(stoitype e.texp_type)])
  | Tstr_value (rf, tvb_list) -> transform_value_bindings state rf tvb_list
  | Tstr_type -> []


let transform_structure state (st : tstructure) =
  transform_list st ~f:(transform_structure_item state)

let transform_function context (fd : Functions.func_data) =
  let vars = Vars.make_local_vars fd in
  let state = {
    context = context;
    vars = vars
  }
  in
  let arg_code = transform_pat state fd.fd_pat in
  let expr_code = transform_expr state fd.fd_expr in
  let arg_type = stoitype fd.fd_pat.tpat_type in
  (state.vars, (Iexp_getvar(arg_type, Vars.function_arg)) :: (arg_code @ expr_code))

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
    | Iexp_setvar(t, name) ->
        Iexp_setvar(t, fix_var name)
    | Iexp_getvar(t, name) ->
        Iexp_getvar(t, fix_var name)
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
  let global_state = {
    context = context;
    vars = Vars.empty_global_vars
  }
  in
  let init_code = transform_structure global_state fast in
  let global_vars = global_state.vars in
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
