open Core_kernel
open Otwa_types
open Typed_ast
open Types
open Intermediate_ast

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
  let none = (vars, []) in
  match expr.texp_desc with
  | Texp_ident(id) ->
      let var_id = Vars.lookup_var_or_global vars id in
      (vars, [Iexp_pushvar(ityp, var_id)])
  | Texp_constant(str) -> (vars, [Iexp_pushconst(ityp, str)])
  | Texp_let (rf, tvb_list, expr) ->
      let (vars', tvb_iexprs) = transform_value_bindings context vars rf tvb_list in
      let (vars'', in_iexprs) = transform_expr context vars' expr in
      (vars'', [Iexp_block(tvb_iexprs @ in_iexprs)])
  | Texp_fun (_, _) -> raise (IntermediateFailure "Perform closure conversion first")
  | Texp_apply (fexpr, args) -> transform_apply context vars expr.texp_type fexpr args
  | Texp_match (_, _) -> none
  | Texp_tuple(els) ->
      let (vars', ils) = transform_list context vars els ~f:transform_expr in
      let ituptype = tupletoitype expr.texp_type in
      (vars', ils @ [Iexp_pushtuple(ituptype)])
  | Texp_construct (name, expr_opt) -> transform_construct context vars name expr_opt
  | Texp_ifthenelse (i, t, e_opt) ->
      let (vars1, icode) = transform_expr context vars i in
      let (vars2, tcode) = transform_expr context vars1 t in
      (match e_opt with
      | Some(e) ->
          let (vars3, ecode) = transform_expr context vars2 e in
          (vars3, icode @ [Iexp_ifthenelse(ityp, tcode, Some(ecode))])
      | None ->
          (vars2, icode @ [Iexp_ifthenelse(ityp, tcode, None)]))


and transform_value_bindings context vars rf tvb_list =
  match rf with
  | Asttypes.Nonrecursive -> transform_value_bindings_nonrecursive context vars tvb_list
  | Asttypes.Recursive -> transform_value_bindings_recursive context vars tvb_list

and transform_value_bindings_nonrecursive context vars tvb_list =
  let (vars', code_list) = transform_list context vars tvb_list ~f:(fun _ vrs tvb ->
    let (vrs1, expr_code) = transform_expr context vrs tvb.tvb_expr in
    let (vrs2, pat_code) = transform_pat_assign context vrs1 tvb.tvb_pat in
    (vrs2, expr_code @ pat_code)
  )
  in
  (vars', code_list)

(* Helper function, for a tuple pattern, returns it's list, otherwise a list containing just the pattern *)
and pat_tuple_list (pat : tpattern) =
  match pat.tpat_desc with
  | Tpat_tuple(ls) -> ls
  | _ -> [pat]

and transform_pat_assign ?check_constructs:(check_constructs = true) context vars (pat :tpattern) =
  match pat.tpat_desc with
  | Tpat_var(name) ->
      let ityp = stoitype pat.tpat_type in
      let (vars', var_name) = Vars.add_named_var vars name ityp in
      (vars', [Iexp_newvar(ityp, var_name)])
  | Tpat_constant _ -> raise (IntermediateFailure "Cannot assign to constant")
  | Tpat_tuple(plist) ->
      let (vars1, var_name) = Vars.add_temp_var vars It_pointer in
      let ituptype = tupletoitype pat.tpat_type in
      let (vars2, code) = transform_listi context vars1 plist ~f:(fun _ vrs pos tpat ->
        let (vrs', pat_code) = transform_pat_assign context vrs tpat in
        (vrs', (Iexp_pushvar(It_pointer, var_name) :: Iexp_loadtupleindex(ituptype, pos) :: pat_code)))
      in
      (vars2, Iexp_newvar(It_pointer, var_name) :: code)
  | Tpat_construct (name, tpat_opt) ->
      let (vars1, var_name) = Vars.add_temp_var vars It_pointer in
      let check_code =
        if check_constructs then
          let construct = Option.value_exn (Context.find_constr context name) in
          (Iexp_pushvar(It_pointer, var_name)
          :: Iexp_loadconstructid
          :: Iexp_pushconst(It_int, Int.to_string construct.index)
          :: Iexp_binop(It_int, Ibin_ne)
          :: [Iexp_ifthenelse(It_unit, [Iexp_fail], None)])
        else []
      in
      let (vars2, destruct_code) =
        (match(tpat_opt) with
        | Some(tpat) ->
            let plist = pat_tuple_list tpat in
            let ituptype = List.map plist ~f:(fun p -> stoitype p.tpat_type) in
            transform_listi context vars1 plist ~f:(fun _ vrs pos cpat ->
              let (vrs', pat_code) = transform_pat_assign context vrs cpat in
              (vrs', (Iexp_pushvar(It_pointer, var_name) :: Iexp_loadconstructindex(ituptype, pos) :: pat_code)))
        | None -> (vars1, []))
      in
      (vars2, Iexp_newvar(It_pointer, var_name) :: (check_code @ destruct_code))


and transform_value_bindings_recursive _context _vars tvb_list =
  let _closure_names = List.map tvb_list ~f:(fun tvb ->
    (match tvb.tvb_pat.tpat_desc with
    | Tpat_var(name) -> name
    | _ -> raise (IntermediateFailure "Recursive bindings must be functions")))
  in raise (IntermediateFailure "Not yet supported")
  (* get all the closure functions and then build them all at once *)

and transform_apply context vars typ fexpr args =
  match fexpr.texp_desc with
  | Texp_ident(name) ->
      let lookup = Predefined.lookup_ident name in
      (match lookup with
      | Some(_) -> transform_op context vars name args
      | None ->
          if String.is_prefix name ~prefix:"@f_" then
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
and transform_notuple context vars expr =
  match expr.texp_desc with
  | Texp_tuple(ls) -> transform_list context vars ls ~f:transform_expr
  | _ -> transform_expr context vars expr

and transform_mk_closure context vars typ name args =
  let tuple_expr = List.hd_exn args in
  let iftype = functoitype typ in
  let ituptype = tupletoitype tuple_expr.texp_type in
  let (vars', tuple_codelst) = transform_notuple context vars tuple_expr in
  (vars', tuple_codelst @
    [Iexp_newclosure(iftype, String.drop_prefix name 3, ituptype);
     Iexp_fillclosure(ituptype)])

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
  (vars', (Iexp_pushvar(It_pointer, name)) :: loop_code)

and transform_construct context vars name expr_opt =
  let constr = Option.value_exn (Context.find_constr context name) in
  let ituptype = List.map constr.args ~f:stoitype in
  match expr_opt with
  | Some(expr) ->
      let (vars', args_code) = transform_notuple context vars expr in
      (vars', args_code @ [Iexp_pushconstruct(ituptype, constr.index)])
  | None ->
      (vars, [Iexp_pushconstruct(ituptype, constr.index)])


let transform_structure_item context vars (si : tstructure_item) =
  match si.tstr_desc with
  | Tstr_eval(e) -> transform_expr context vars e
  | Tstr_value (rf, tvb_list) -> transform_value_bindings context vars rf tvb_list
  | Tstr_type -> (vars, [])


let transform_structure context vars (st : tstructure) =
  transform_list context vars st ~f:transform_structure_item

let transform_function context (fd : Functions.func_data) =
  let vars = Vars.make_local_vars fd in
  let (vars', arg_code) = transform_pat_assign context vars fd.fd_pat in
  let (vars'', expr_code) = transform_expr context vars' fd.fd_expr in
  let arg_type = stoitype fd.fd_pat.tpat_type in
  (vars'', (Iexp_pushvar(arg_type, Vars.function_arg)) :: (arg_code @ expr_code))
