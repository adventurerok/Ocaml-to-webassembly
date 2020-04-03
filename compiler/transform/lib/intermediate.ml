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
  functions: (string, Functions.func_data) Hashtbl.t;
  mutable vars: Vars.vars;
  mutable globals: Vars.vars;
  named_loops: (string, (string * string)) Hashtbl.t
}

let update_vars (state : state) (vars, thing) =
  state.vars <- vars;
  thing

let add_named_var ?global:(global = false) (state : state) name typ =
  if global then
    let (globals', var) = Vars.add_named_var state.globals name typ in
    state.globals <- globals';
    var
  else
    let (vars', var) = Vars.add_named_var state.vars name typ in
    state.vars <- vars';
    var

let quick_temp_var (state : state) typ =
  update_vars state (Vars.add_temp_var state.vars typ)

(* Gives a new vars and list of iinstruction *)
let rec transform_expr (state: state) (expr: texpression) =
  let ityp = stoitype expr.texp_type in
  match expr.texp_desc with
  | Texp_ident((name,_)) ->
      let var_id = Vars.lookup_var_or_global state.vars name in
      (var_id, [])
  | Texp_constant(str) ->
      let var = quick_temp_var state ityp in
      (var, [Iins_setvar(ityp, var, str)])
  | Texp_let (rf, tvb_list, expr) ->
      let tvb_iinss = transform_value_bindings state rf tvb_list in
      let (res, in_iinss) = transform_expr state expr in
      (res, tvb_iinss @ in_iinss)
  | Texp_fun (_, _) -> raise (IntermediateFailure "Perform closure conversion first")
  | Texp_apply (fexpr, args) -> transform_apply state expr.texp_type fexpr args
  | Texp_special (mode, name, args) -> transform_special state expr.texp_type mode name args
  | Texp_match (e, cases) -> transform_match state expr.texp_type e cases
  | Texp_tuple(_) ->
      let (tuple_vars, tuple_codelst) = transform_tupleargs ~poly_box:true state expr in
      let tuple_lincode = List.concat tuple_codelst in
      let var_name = update_vars state (Vars.add_temp_var state.vars It_pointer) in
      let ituptype = tupletoitype expr.texp_type in
      (var_name, tuple_lincode @ [Iins_pushtuple(ituptype, var_name, tuple_vars)])
  | Texp_construct (name, ls) -> transform_construct state name ls
  | Texp_ifthenelse (i, t, e_opt) ->
      let block_name = update_vars state (Vars.add_block state.vars) in
      let (ires, icode) = transform_expr state i in
      let (tres, tcode) = transform_expr state t in
      (match e_opt with
      | Some(e) ->
          let (eres, ecode) = transform_expr state e in
          let res = quick_temp_var state ityp in
          (res,
            icode
            @ [Iins_startif(block_name, ires)]
            @ tcode
            @ [Iins_copyvar(ityp, res, tres);
               Iins_else(block_name)]
            @ ecode
            @ [Iins_copyvar(ityp, res, eres);
               Iins_endif(block_name)]
          )
      | None ->
          (tres,
            icode
            @ [Iins_startif(block_name, ires)]
            @ tcode
            @ [Iins_endif(block_name)]
          ))
  | Texp_while(cond, inner) ->
      transform_while state cond inner
  | Texp_for(var_opt, min, max, dir, inner) ->
      transform_for state var_opt min max dir inner
  | Texp_sequence(a, b) ->
      transform_sequence state a b


and transform_value_bindings ?global:(global = false) state rf tvb_list =
  match rf with
  | Asttypes.Nonrecursive -> transform_value_bindings_nonrecursive ~global:global state tvb_list
  | Asttypes.Recursive -> transform_value_bindings_recursive ~global:global state tvb_list

and transform_value_bindings_nonrecursive ?global:(global = false) state tvb_list =
  let code_list = List.concat (List.map tvb_list ~f:(fun tvb ->
    let (var, expr_code) = transform_expr state tvb.tvb_expr in
    let pat_code = transform_pat ~global:global state tvb.tvb_pat var in
    expr_code @ pat_code
  ))
  in
  code_list


and transform_pat_escape state escape test_var =
  match escape with
  | [] -> []
  | [Iins_exitblock(leave_block)] ->
      [Iins_exitblockif(leave_block, test_var)]
  | _ ->
      let escape_block = update_vars state (Vars.add_block state.vars) in
      [Iins_startif(escape_block, test_var)]
      @ escape
      @ [Iins_endif(escape_block)]

and transform_pat ?check:(check = true)
                  ?escape:(escape = [Iins_fail])
                  ?boxed:(boxed = false)
                  ?global:(global = false)
                  state
                  (pat :tpattern)
                  var
                  =
  match pat.tpat_desc with
  | Tpat_any -> []
  | Tpat_var((name,_)) ->
      let ityp = stoitype pat.tpat_type in
      let named_var = add_named_var ~global:global state name ityp in
      if (boxed && (itype_needs_box ityp)) then
        [Iins_unbox(ityp, var, named_var)]
      else
      [Iins_copyvar(ityp, named_var, var)]
  | Tpat_constant(const) ->
      (* This would be shorthand for an equality check, e.g. evaluate this and make sure it's equal to 3 *)
      if check then
        let ityp = stoitype pat.tpat_type in
        let const_var = quick_temp_var state ityp in
        let test_var = quick_temp_var state It_bool in
        let escape_code = transform_pat_escape state escape test_var in
        if (boxed && (itype_needs_box ityp)) then
          let unbox_var = quick_temp_var state ityp in
            [Iins_unbox(ityp, var, unbox_var);
            Iins_setvar(ityp, const_var, const);
            Iins_binop(ityp, Ibin_ne, test_var, unbox_var, const_var)]
          @ escape_code
        else
            [Iins_setvar(ityp, const_var, const);
            Iins_binop(ityp, Ibin_ne, test_var, var, const_var)]
          @ escape_code
      else []
  | Tpat_tuple(plist) ->
      let ituptype = tupletoitype pat.tpat_type in
      let code = transform_listi plist ~f:(fun pos tpat ->
        let pvar = quick_temp_var state It_poly in
        let pat_code = transform_pat ~check:check ~escape:escape ~boxed:true ~global:global state tpat pvar in
        (Iins_loadtupleindex(ituptype, pos, pvar, var) :: pat_code))
      in
      code
  | Tpat_construct (name, plist) ->
      let construct = Option.value_exn (Context.find_constr state.context name) in
      let check_code =
        if check then
          let id_var = quick_temp_var state It_int in
          let const_var = quick_temp_var state It_int in
          let test_var = quick_temp_var state It_bool in
          let escape_code = transform_pat_escape state escape test_var in
            [Iins_loadconstructid(id_var, var);
            Iins_setvar(It_int, const_var, Int.to_string construct.index);
            Iins_binop(It_int, Ibin_ne, test_var, id_var, const_var)]
          @ escape_code
        else []
      in
      let destruct_code =
        let ituptype = List.map plist ~f:(fun p -> stoitype p.tpat_type) in
        transform_listi plist ~f:(fun pos cpat ->
          let pvar = quick_temp_var state It_poly in
          let pat_code = transform_pat ~check:check ~escape:escape ~boxed:true ~global:global state cpat pvar in
          (Iins_loadconstructindex(ituptype, pos, pvar, var) :: pat_code))
      in
      (check_code @ destruct_code)


and transform_value_bindings_recursive ?global:(global = false) state tvb_list =
  (* Make a var for each recursive function *)
  let details = List.map tvb_list ~f:(fun tvb ->
    let rec_name =
      match tvb.tvb_pat.tpat_desc with
      | Tpat_var((name, _)) -> name
      | _ -> raise (IntermediateFailure "Recursive bindings must be functions")
    in
    let iftype = functoitype tvb.tvb_expr.texp_type in
    let (func_name, args) =
      match tvb.tvb_expr.texp_desc with
      | Texp_special(Tspec_mkclosure, fname_match, args_match) -> (fname_match, args_match)
      | _ -> raise (IntermediateFailure "Recursive bindings must be functions")
    in
    let tuple_expr = List.hd_exn args in
    let ituptype = tupletoitype tuple_expr.texp_type in
    (rec_name, func_name, iftype, ituptype, tuple_expr)
  )
  in
  let new_closure_code = transform_list details
                                    ~f:(fun (rec_name, func_name, iftype, ituptype, _) ->
    let var_name = add_named_var ~global:global state rec_name It_pointer in
    [Iins_newclosure(iftype, func_name, ituptype, var_name)]
  )
  in
  let fill_closure_code = transform_list details
                                    ~f:(fun (rec_name, _, _, ituptype, tuple_expr) ->
    let var_name =
      if global then
        Option.value_exn (Vars.lookup_var state.globals rec_name)
      else
        Option.value_exn (Vars.lookup_var state.vars rec_name)
    in
    let (tuple_varlst, tuple_codelst) = transform_tupleargs ~poly_box:false state tuple_expr in
    let tuple_lincode = List.concat tuple_codelst in
    tuple_lincode @ [Iins_fillclosure(ituptype, var_name, tuple_varlst)]
  )
  in
  new_closure_code @ fill_closure_code
  (* get all the closure functions and then build them all at once *)

and transform_match state st_res_typ expr cases =
  let (expr_var, expr_code) = transform_expr state expr in
  let result_type = stoitype st_res_typ in
  let result_var = update_vars state (Vars.add_temp_var state.vars result_type) in
  let match_block = update_vars state (Vars.add_block state.vars) in
  let inner_code = transform_list cases ~f:(fun case ->
    let case_block = update_vars state (Vars.add_block state.vars) in
    (* These instructions check and destructure the pattern *)
    let pat_code = transform_pat ~check:true ~escape:([Iins_exitblock(case_block)])
                                            state case.tc_lhs expr_var
    in
    (* Case expression, possibly using variables from the pattern *)
    let (matched_var, matched_code) = transform_expr state case.tc_rhs in
    let inside_block = pat_code @ matched_code @
                       [Iins_copyvar(result_type, result_var, matched_var);
                       Iins_exitblock(match_block)]
    in
      [Iins_startblock(case_block)]
    @ inside_block
    @ [Iins_endblock(case_block)]
  )
  in
  (result_var,
    expr_code
    @ [Iins_startblock(match_block)]
    @ inner_code
    @ [Iins_fail;
       Iins_endblock(match_block)]
  )

and transform_apply state _typ fexpr args =
  match fexpr.texp_desc with
  | Texp_ident((name,_)) ->
      let lookup = Predefined.lookup_ident name in
      (match lookup with
      | Some(_) -> transform_op state name args
      | None ->
          let var_name = Vars.lookup_var_or_global state.vars name in
          transform_apply_closure state fexpr.texp_type var_name args)
  | _ ->
      let (var_name, other_code) = transform_expr state fexpr in
      let (res, apply_code) = transform_apply_closure state fexpr.texp_type var_name args in
      (res, (other_code @ apply_code))

and transform_special state typ mode name args =
  match mode with
  | Tspec_mkclosure ->
      transform_mk_closure state typ name args
  | Tspec_directapply ->
      transform_direct_apply state typ name args
  | Tspec_namedloop ->
      transform_named_loop state name args
  | Tspec_breakloop ->
      let loop_info = Hashtbl.find state.named_loops name in
      (match loop_info with
      | Some((break_block, _)) ->
          let res = quick_temp_var state It_unit in
          (res, [Iins_setvar(It_unit, res, "()"); Iins_exitblock(break_block)])
      | None ->
          raise (IntermediateFailure("No loop named " ^ name)))
  | Tspec_continueloop ->
      let loop_info = Hashtbl.find state.named_loops name in
      match loop_info with
      | Some((_, continue_block)) ->
          let res = quick_temp_var state It_unit in
          (res, [Iins_setvar(It_unit, res, "()"); Iins_exitblock(continue_block)])
      | None ->
          raise (IntermediateFailure("No loop named " ^ name))

and transform_op state name args =
  let (arg_vars, arg_codelst) = List.unzip (List.map args ~f:(transform_expr state)) in
  let arg_code = List.concat arg_codelst in
  let typ = ((List.hd_exn args).texp_type) in
  let ityp = stoitype typ in
  match name with
  | "~-" | "~-." ->
      (match ityp with
      | It_float ->
          let res = quick_temp_var state ityp in
          (res, arg_code @ [Iins_unop(ityp, Iun_neg, res, List.nth_exn arg_vars 0)])
      | _ ->
          let const_var = quick_temp_var state ityp in
          let res = quick_temp_var state ityp in
          (res,
            [Iins_setvar(ityp, const_var, "0")]
            @ arg_code
            @ [Iins_binop(ityp, Ibin_sub, res, const_var, List.nth_exn arg_vars 0)]))
  | "ref" ->
      let (data_var, box_code) = transform_box state typ (List.nth_exn arg_vars 0) in
      let ref_var = update_vars state (Vars.add_temp_var state.vars It_pointer) in
      (ref_var, arg_code
      @ box_code
      @ [Iins_newbox(It_poly, data_var, ref_var)])
  | "!" ->
      let ref_var = List.nth_exn arg_vars 0 in
      let data_var = update_vars state (Vars.add_temp_var state.vars It_poly) in
      let ref_typ =
        match typ with
        | T_constr("ref", [a]) -> a
        | _ -> raise (IntermediateFailure "Cannot derefence non ref type")
      in
      let (unbox_var, unbox_code) = transform_unbox state ref_typ data_var in
      (unbox_var, arg_code
      @ [Iins_unbox(It_poly, ref_var, data_var)]
      @ unbox_code)
  | ":=" ->
      let ref_typ =
        match typ with
        | T_constr("ref", [a]) -> a
        | _ -> raise (IntermediateFailure "Cannot derefence non ref type")
      in
      let (data_var, box_code) = transform_box state ref_typ (List.nth_exn arg_vars 1) in
      let ref_var = List.nth_exn arg_vars 0 in
      let unit_var = quick_temp_var state It_unit in
      (unit_var, arg_code
      @ box_code
      @ [Iins_updatebox(It_poly, data_var, ref_var);
         Iins_setvar(It_unit, unit_var, "()")])
  | "not" ->
      let res = quick_temp_var state It_bool in
      (res, (arg_code @ [Iins_unop(ityp, Iun_eqz, res, List.nth_exn arg_vars 0)]))
  | _ ->
    let (bop, res_typ) =
      (match name with
      | "+" -> (Ibin_add, ityp)
      | "+." -> (Ibin_add, ityp)
      | "-" -> (Ibin_sub, ityp)
      | "-." -> (Ibin_sub, ityp)
      | "*" -> (Ibin_mul, ityp)
      | "*." -> (Ibin_mul, ityp)
      | "/" -> (Ibin_div, ityp)
      | "/." -> (Ibin_div, ityp)
      | "mod" -> (Ibin_rem, ityp)
      | "<" -> (Ibin_lt, It_bool)
      | ">" -> (Ibin_gt, It_bool)
      | "<=" -> (Ibin_le, It_bool)
      | ">=" -> (Ibin_ge, It_bool)
      | "=" -> (Ibin_eq, It_bool)
      | "!=" -> (Ibin_ne, It_bool)
      | "&&" -> (Ibin_and, It_bool)
      | "||" -> (Ibin_or, It_bool)
      | _ -> raise (IntermediateFailure "Unsupported binary operation"))
    in
    let res = quick_temp_var state res_typ in
    (res, (arg_code @ [Iins_binop(ityp, bop, res, List.nth_exn arg_vars 0, List.nth_exn arg_vars 1)]))

(* Transforms an expression
 * If that expression is a tuple, do not add the final pushtuple instruction *)
and transform_tupleargs ?poly_box:(poly_box=false) state expr =
  match expr.texp_desc with
  | Texp_tuple(lst) ->
      let zipped = List.map lst ~f:(transform_expr_box ~box:poly_box state) in
      List.unzip zipped
  | _ ->
      let (var, code) = transform_expr_box ~box:poly_box state expr in
      ([var], [code])


and transform_tupleargs_boxcomp state itt expr =
  match expr.texp_desc with
  | Texp_tuple(lst) ->
      let zipped = List.map2_exn lst itt ~f:(fun e it ->
        match it with
        | It_poly ->
            transform_expr_box ~box:true state e
        | _ ->
            transform_expr_box ~box:false state e
      )
      in
      List.unzip zipped
  | _ ->
      let (var, code) =
        match itt with
        | [It_poly] -> transform_expr_box ~box:true state expr
        | [_] -> transform_expr_box ~box:false state expr
        | _ -> raise (IntermediateFailure "Mismatch in tuple and itt length")
      in
      ([var], [code])

and transform_mk_closure state typ name args =
  let tuple_expr = List.hd_exn args in
  let iftype = functoitype typ in
  let ituptype = tupletoitype tuple_expr.texp_type in
  let (tuple_vars, tuple_codelst) = transform_tupleargs ~poly_box:false state tuple_expr in
  let tuple_lincode = List.concat tuple_codelst in
  let var_name = update_vars state (Vars.add_temp_var state.vars It_pointer) in
  (var_name,
    tuple_lincode
    @ [Iins_newclosure(iftype, name, ituptype, var_name);
      Iins_fillclosure(ituptype, var_name, tuple_vars)]
  )

and transform_direct_apply state typ name args =
  let tuple_expr = List.hd_exn args in
  let ret_typ = stoitype typ in
  let fd = Hashtbl.find_exn state.functions name in
  let cvar_types = List.map fd.fd_cvars ~f:(fun (_, t) -> t) in
  let da_tuple = T_tuple(cvar_types @ [fd.fd_expr.texp_type]) in
  let ituptype = tupletoitype da_tuple in
  let (tuple_vars, tuple_codelst) = transform_tupleargs_boxcomp state ituptype tuple_expr in
  let tuple_lincode = List.concat tuple_codelst in
  let var_name = quick_temp_var state ret_typ in
  let iret_fd = stoitype fd.fd_expr.texp_type in
  let (unbox_var, unbox_code) =
    match iret_fd with
    | It_poly -> transform_unbox state typ var_name
    | _ -> (var_name, [])
  in
  (unbox_var,
    tuple_lincode
    @ [Iins_calldirect(var_name, name, ituptype, tuple_vars)]
    @ unbox_code
  )


and transform_expr_box ?box:(box = true) state expr =
  let (var, code) = transform_expr state expr in
  if box then
    let (out_var, box_code) = transform_box state expr.texp_type var in
    (out_var, (code @ box_code))
  else (var, code)

and transform_box state typ unbox_var =
  let ityp = stoitype typ in
  if itype_needs_box ityp then
    let box_var = update_vars state (Vars.add_temp_var state.vars It_poly) in
    (box_var,
      [Iins_newbox(ityp, unbox_var, box_var)]
    )
  else (unbox_var, [])

and transform_unbox state typ box_var =
  let ityp = stoitype typ in
  if itype_needs_box ityp then
    let unbox_var = update_vars state (Vars.add_temp_var state.vars ityp) in
    (unbox_var,
      [Iins_unbox(ityp, box_var, unbox_var)]
    )
  else (box_var, [])

and transform_apply_closure state typ var_name args =
  let rec loop ftyp arg_list prev_result =
    match arg_list with
    | [] -> (prev_result, [])
    | (arg :: arg_list') ->
        (match ftyp with
        | T_func(atyp, btyp) ->
            let iatyp = stoitype atyp in
            let ibtyp = stoitype btyp in
            let (arg_var, arg_code) = transform_expr_box state arg in
            let result_var = quick_temp_var state It_poly in
            let (unbox_var, unbox_code) = transform_unbox state btyp result_var in
            let (final_result, final_code) = loop btyp arg_list' unbox_var in
            (final_result,
              arg_code
              @ [Iins_callclosure((iatyp, ibtyp), result_var, prev_result, arg_var)]
              @ unbox_code
              @ final_code
            )
        | _ -> raise (IntermediateFailure "Cannot apply non function type "))
  in
  loop typ args var_name

and transform_construct state name ls =
  let constr = Option.value_exn (Context.find_constr state.context name) in
  let ituptype = List.map constr.args ~f:stoitype in
  let var_name = update_vars state (Vars.add_temp_var state.vars It_pointer) in
  let (tuple_vars, tuple_codelst) = List.unzip (List.map ~f:(transform_expr_box ~box:true state) ls) in
  let tuple_lincode = List.concat tuple_codelst in
  (var_name,
    tuple_lincode
    @ [Iins_pushconstruct(ituptype, var_name, constr.index, tuple_vars)]
  )


and transform_named_loop state name args =
  let break_block = update_vars state (Vars.add_block state.vars) in
  let continue_block = update_vars state (Vars.add_block state.vars) in
  Hashtbl.set state.named_loops ~key:name ~data:(break_block, continue_block);
  let inner = List.hd_exn args in
  let _, inner_code = transform_expr state inner in
  let final_var = quick_temp_var state It_unit in
  (final_var,
    [Iins_startloop(break_block, continue_block)]
    @ inner_code
    @ [Iins_endloop(break_block, continue_block);
       Iins_setvar(It_unit, final_var, "()")]
  )


and transform_while state cond inner =
  let (cond_var, cond_code) = transform_expr state cond in
  let test_var = quick_temp_var state It_bool in
  let (_, inner_code) = transform_expr state inner in
  let break_block = update_vars state (Vars.add_block state.vars) in
  let continue_block = update_vars state (Vars.add_block state.vars) in
  let loop_inside =
    cond_code
    @ [Iins_unop(It_bool, Iun_eqz, test_var, cond_var);
       Iins_exitblockif(break_block, test_var)]
    @ inner_code
  in
  let final_var = quick_temp_var state It_unit in
  (final_var,
    [Iins_startloop(break_block, continue_block)]
    @ loop_inside
    @ [Iins_endloop(break_block, continue_block);
       Iins_setvar(It_unit, final_var, "()")]
  )

and transform_for state var_opt min max dir inner =
  let for_var =
    match var_opt with
    | Some(var_name) -> update_vars state (Vars.add_named_var state.vars var_name It_int)
    | None -> update_vars state (Vars.add_temp_var state.vars It_int)
  in
  let (min_var, min_code) = transform_expr state min in
  let (max_var, max_code) = transform_expr state max in
  let (_, inner_code) = transform_expr state inner in
  let break_block = update_vars state (Vars.add_block state.vars) in
  let continue_block = update_vars state (Vars.add_block state.vars) in
  let is_forwards =
    match dir with
    | Asttypes.Upto -> true
    | Asttypes.Downto -> false
  in
  let pre_loop =
    min_code
    @ [Iins_copyvar(It_int, for_var, min_var)]
    @ max_code
  in
  let test_var = quick_temp_var state It_bool in
  let const_1_var = quick_temp_var state It_int in
  let loop_inside =
    [Iins_binop(It_int, (if is_forwards then Ibin_gt else Ibin_lt), test_var, for_var, max_var);
     Iins_exitblockif(break_block, test_var)]
    @ inner_code
    @ [Iins_setvar(It_int, const_1_var, "1");
       Iins_binop(It_int, (if is_forwards then Ibin_add else Ibin_sub), for_var, for_var, const_1_var)]
  in
  let final_var = quick_temp_var state It_unit in
  (final_var,
    pre_loop
    @ [Iins_startloop(break_block, continue_block)]
    @ loop_inside
    @ [Iins_endloop(break_block, continue_block);
       Iins_setvar(It_unit, final_var, "()")]
  )


and transform_sequence state a b =
  let (_, a_code) = transform_expr state a in
  let (b_var, b_code) = transform_expr state b in
  (b_var, (a_code @ b_code))

let transform_structure_item state (si : tstructure_item) =
  match si.tstr_desc with
  | Tstr_eval(e) ->
      let (_, code) = transform_expr state e in
      (* We need to drop the resulting value on the stack *)
      code
  | Tstr_value (rf, tvb_list) -> transform_value_bindings ~global:true state rf tvb_list
  | Tstr_type -> []


let transform_structure state (st : tstructure) =
  transform_list st ~f:(transform_structure_item state)

let transform_function globals func_map context (fd : Functions.func_data) =
  let vars = Vars.make_local_vars fd in
  let state = {
    context = context;
    functions = func_map;
    vars = vars;
    globals = globals;
    named_loops = Hashtbl.create (module String);
  }
  in
  let arg_code = transform_pat state fd.fd_pat Vars.function_arg in
  let (result_var, expr_code) = transform_expr state fd.fd_expr in
  let return_type = stoitype fd.fd_expr.texp_type in
  (state.vars, (arg_code @ expr_code @ [Iins_return(return_type, result_var)]))


let fix_globals globals locals code =
  let fix_var (scope, name) =
    match scope with
    | Global ->
        (match Vars.lookup_var globals name with
        | Some(gvar) -> gvar
        | None -> raise (IntermediateFailure ("Missing global variable " ^ name)))
    | Local ->
        (match Vars.lookup_var locals name with
        | Some(_) -> (Local, name)
        | None -> raise (IntermediateFailure ("Missing local variable " ^ name)))
  in
  iinstruction_list_map_vars ~f:fix_var code

let transform_program ?debug:(debug = false) context next_var structure =
  let (funcs_1, fast_1, next_var1) = Functions.func_transform_structure next_var structure in
  let (funcs_2, fast) = Direct_call_generator.direct_call_transform funcs_1 fast_1 in
  let (funcs, _next_var2) = Tail_calls.tail_recursion_transform funcs_2 next_var1 in
  let () = if debug then (
    Stdio.print_endline (Typed_ast.tstructure_to_string fast);
    Functions.print_func_datas funcs)
  in
  let func_map =
    List.map funcs ~f:(fun func -> (func.fd_name, func))
    |> Hashtbl.of_alist_exn (module String)
  in
  let global_state = {
    context = context;
    functions = func_map;
    vars = Vars.empty_init_vars;
    globals = Vars.empty_global_vars;
    named_loops = Hashtbl.create (module String);
  }
  in
  let init_code = transform_structure global_state fast in
  let global_vars = global_state.globals in
  let ifuncs = List.map funcs ~f:(fun fd ->
    let (vars, code) = transform_function global_state.globals func_map context fd in
    (fd.fd_name, {
      pf_name = fd.fd_name;
      pf_vars = vars;
      pf_code = fix_globals global_vars vars code;
      pf_type = functoitype fd.fd_type;
      pf_cvars = List.map fd.fd_cvars ~f:(fun ((name,_),st) -> (name, stoitype st));
      pf_export_name = fd.fd_export_name
    }))
  in
  let init_func = {
    pf_name = "$init";
    pf_vars = global_state.vars;
    pf_code = fix_globals global_vars global_state.vars init_code;
    pf_type = (It_none, It_none);
    pf_cvars = [];
    pf_export_name = None
  }
  in
  let all_funcs = ("$init", init_func) :: ifuncs in
  let corrected_funcs = List.map all_funcs ~f:(fun (name, f) ->
    (name, f))
  in
  let prog = {
    prog_functions = Map.Poly.of_alist_exn corrected_funcs;
    prog_globals = global_vars;
    prog_initfunc = "$init"
  }
  in
  let () = if debug then (
    let (_, only_funcs) = List.unzip corrected_funcs in
    let fa_lst = List.map ~f:(Analysis.analyse_function prog.prog_globals) only_funcs in
    let strs = List.map ~f:Analysis.func_analysis_to_string fa_lst in
    List.iter ~f:Stdio.print_endline strs)
  in
  Optimise.optimise prog
