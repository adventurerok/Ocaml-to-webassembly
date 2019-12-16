open Core_kernel
open Otwa_types
open Typed_ast
open Types
open Intermediate_ast

type type_map = (string, scheme_type) Map.Poly.t

exception IntermediateFailure of string

let stoitype (typ : scheme_type) =
  match typ with
  | T_var(_) -> raise (IntermediateFailure "Cannot convert type variable into inter type")
  | T_val(V_unit) -> It_unit
  | T_val(V_int) -> It_int
  | T_val(V_bool) -> It_bool
  | T_tuple _ -> It_pointer
  | T_constr (_, _) -> It_pointer
  | T_func (_, _) -> It_pointer (* Closure pointer *)

let functoitype (typ : scheme_type) =
  match typ with
  | T_func(a,b) -> (stoitype a, stoitype b)
  | _ -> raise (IntermediateFailure "Expecting function type")

let tupletoitype (typ : scheme_type) =
  match typ with
  | T_tuple(ls) -> List.map ls ~f:stoitype
  | _ -> raise (IntermediateFailure "Expecting tuple type")

(* Gives a list of iexpression *)
let rec transform_expr (vars: type_map) (expr: texpression) =
  let ityp = stoitype expr.texp_type in
  let none = [] in
  match expr.texp_desc with
  | Texp_ident(id) -> [Iexp_pushvar(ityp, id)]
  | Texp_constant(str) -> [Iexp_pushconst(ityp, str)]
  | Texp_let (rf, tvb_list, expr) ->
      let (tvb_iexprs, vars') = transform_value_bindings vars rf tvb_list in
      let in_iexprs = transform_expr vars' expr in
      [Iexp_block(tvb_iexprs @ in_iexprs)]
  | Texp_fun (_, _) -> raise (IntermediateFailure "Perform closure conversion first")
  | Texp_apply (fexpr, args) -> transform_apply vars expr.texp_type fexpr args
  | Texp_match (_, _) -> none
  | Texp_tuple _ -> none
  | Texp_construct (_, _) -> none
  | Texp_ifthenelse (_, _, _) -> none

and transform_value_bindings vars rf tvb_list =
  match rf with
  | Asttypes.Nonrecursive -> transform_value_bindings_nonrecursive vars tvb_list
  | Asttypes.Recursive -> transform_value_bindings_recursive vars tvb_list

and transform_value_bindings_nonrecursive vars tvb_list =
  let code_list = List.map tvb_list ~f:(fun tvb ->
    let expr_code = transform_expr vars tvb.tvb_expr in
    let pat_code = transform_pat_assign tvb.tvb_pat in
    (expr_code @ pat_code))
  in
  let vars' = List.fold tvb_list ~init:vars ~f:(fun vrs tvb ->
    List.fold tvb.tvb_vars ~init:vrs ~f:(fun vs (v, Forall(_, st)) -> Map.Poly.set vs ~key:v ~data:st)
  )
  in (List.concat code_list, vars')

and transform_pat_assign (pat :tpattern) =
  match pat.tpat_desc with
  | Tpat_var(name) -> [Iexp_newvar(stoitype(pat.tpat_type), name)]
  | Tpat_constant _ -> raise (IntermediateFailure "Cannot assign to constant")
  | Tpat_tuple _ -> raise (IntermediateFailure "Not yet supported")
  | Tpat_construct (_, _) -> raise (IntermediateFailure "Not yet supported")

and transform_value_bindings_recursive _vars tvb_list =
  let _closure_names = List.map tvb_list ~f:(fun tvb ->
    (match tvb.tvb_pat.tpat_desc with
    | Tpat_var(name) -> name
    | _ -> raise (IntermediateFailure "Recursive bindings must be functions")))
  in raise (IntermediateFailure "Not yet supported")
  (* get all the closure functions and then build them all at once *)

and transform_apply vars typ fexpr args =
  match fexpr.texp_desc with
  | Texp_ident(name) ->
      let lookup = Predefined.lookup_ident name in
      (match lookup with
      | Some(_) -> transform_op vars name args
      | None ->
          if String.is_prefix name ~prefix:"@f_" then
            transform_mk_closure vars typ name args
          else
            transform_apply_closure vars fexpr.texp_type name args)
  | _ -> raise (IntermediateFailure "Applying other expressions not yet supported")

and transform_op vars name args =
  let arg_code = List.concat (List.map args ~f:(transform_expr vars)) in
  let ityp = stoitype ((List.hd_exn args).texp_type) in
  match name with
  | "+" -> arg_code @ [Iexp_binop(ityp, Ibin_add)]
  | "-" -> arg_code @ [Iexp_binop(ityp, Ibin_sub)]
  | "*" -> arg_code @ [Iexp_binop(ityp, Ibin_mul)]
  | "/" -> arg_code @ [Iexp_binop(ityp, Ibin_div)]
  | "<" -> arg_code @ [Iexp_binop(ityp, Ibin_lt)]
  | ">" -> arg_code @ [Iexp_binop(ityp, Ibin_gt)]
  | "<=" -> arg_code @ [Iexp_binop(ityp, Ibin_le)]
  | ">=" -> arg_code @ [Iexp_binop(ityp, Ibin_ge)]
  | "=" -> arg_code @ [Iexp_binop(ityp, Ibin_eq)]
  | "&&" -> arg_code @ [Iexp_binop(ityp, Ibin_and)]
  | "||" -> arg_code @ [Iexp_binop(ityp, Ibin_or)]
  | _ -> raise (IntermediateFailure "Unsupported binary operation")

and transform_mk_closure vars typ name args =
  let tuple_expr = List.hd_exn args in
  let iftype = functoitype typ in
  let ituptype = tupletoitype tuple_expr.texp_type in
  let tuple_exprlst =
    match tuple_expr.texp_desc with
    | Texp_tuple(ls) -> ls
    | _ -> raise (IntermediateFailure "Expecting tuple to make closure")
  in let tuple_codelst = List.concat (List.map tuple_exprlst ~f:(transform_expr vars)) in
  (tuple_codelst @
    [Iexp_newclosure(iftype, String.drop_prefix name 3, ituptype);
     Iexp_fillclosure(ituptype)])

and transform_apply_closure vars typ name args =
  (* Arg goes on top of stack, and closure 1 down *)
  let rec loop ftyp arg_list =
    match arg_list with
    | [] -> []
    | (arg :: arg_list') ->
        (match ftyp with
        | T_func(atyp, btyp) ->
            let iatyp = stoitype atyp in
            let ibtyp = stoitype btyp in
            let code = transform_expr vars arg in
            code @ [Iexp_callclosure((iatyp, ibtyp))] @ (loop btyp arg_list')
        | _ -> raise (IntermediateFailure "Cannot apply non function type "))
  in (Iexp_pushvar(It_pointer, name)) :: (loop typ args)


and transform_structure_item vars (si : tstructure_item) =
  match si.tstr_desc with
  | Tstr_eval(e) -> transform_expr vars e
  | Tstr_value (rf, tvb_list) ->
      let (code, _) = transform_value_bindings vars rf tvb_list in
      code
  | Tstr_type -> []


and transform_structure vars (st : tstructure) =
  List.concat (List.map st ~f:(transform_structure_item vars))
