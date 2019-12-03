open Core_kernel
open Otwa_types
open Types
open Typed_ast

(* The purpose of this transform is to extract all function definitions to the top level *)
(* Input shall be a typed-ast and a typed context *)
(* Output shall be top-level functions, and left-over code transformed into a main function *)

let counter = ref 0

let func_mk_closure = "@mk_closure"

let fresh_func_name () =
  let id = !counter in
  counter := id + 1;
  ("@f_" ^ (Int.to_string id))

type func_data = {
  fd_pat: tpattern;
  fd_expr: texpression;
  fd_cvars: (string * scheme_type) list;
  fd_type: scheme_type;
  fd_name: string
}

type type_map = (string, scheme_type) Map.Poly.t

let add_vars map vars =
  List.fold ~init:map ~f:(fun m (tv, t) -> Map.Poly.set m ~key:tv ~data:t) vars


(* So on an expression, we'll need the modified expression, and the map of id to function *)
(* Globals: Not in closure (global variables or arguments), Locals: In closure *)

let rec func_transform_expr (locals: type_map) (expr: texpression) =
  let none = ([], expr.texp_desc) in
  let (funcs, desc) =
    match expr.texp_desc with
    | Texp_ident(x) -> ([], Texp_ident(x))
    | Texp_constant(c) -> ([], Texp_constant(c))
    | Texp_let (rf, tvb_list, e) -> func_transform_let locals rf tvb_list e
    | Texp_fun (p, e) -> func_transform_func locals expr.texp_type p e
    | Texp_apply (a, blist) ->
        let (ft_a, a') = func_transform_expr locals a in
        let (ft_b_list, blist') = List.unzip (List.map blist ~f:(func_transform_expr locals)) in
        let ft_b = List.concat ft_b_list in
        (ft_a @ ft_b, Texp_apply(a', blist'))
    | Texp_match (_, _) -> none
    | Texp_tuple(ls) ->
        let (funcs_list, exprs) = List.unzip (List.map ls ~f:(func_transform_expr locals)) in
        let funcs = List.concat funcs_list in
        (funcs, Texp_tuple(exprs))
    | Texp_construct (name, e_opt) ->
        (match e_opt with
        | Some(e) ->
            let (funcs, e') = func_transform_expr locals e in
            (funcs, Texp_construct(name, Some(e')))
        | None -> ([], Texp_construct(name, None)))
    | Texp_ifthenelse (_, _, _) -> none
  in (funcs, {expr with texp_desc = desc})

and func_transform_value_bindings locals rf tvb_list =
  let vars = List.concat (List.map tvb_list ~f:(fun tvb -> tvb.tvb_pat.tpat_vars)) in
  let locals' = List.fold ~init:locals ~f:(fun a (v, t) -> Map.Poly.set a ~key:v ~data:t) vars in
  let inner_locals =
    (match rf with
    | Asttypes.Nonrecursive -> locals
    | Asttypes.Recursive -> locals')
  in
  let (funcs_list, tvb_list') = List.unzip (List.map tvb_list ~f:(fun tvb ->
    let (funcs, e') = func_transform_expr inner_locals tvb.tvb_expr in
    (funcs, {tvb with tvb_expr = e'})))
  in
  let tvb_funcs = List.concat funcs_list in
  (tvb_funcs, locals', tvb_list')

and func_transform_let locals rf tvb_list e =
  let (tvb_funcs, locals', tvb_list') = func_transform_value_bindings locals rf tvb_list in
  let (e_funcs, e') = func_transform_expr locals' e in
  (e_funcs @ tvb_funcs, Texp_let(rf, tvb_list', e'))

and func_transform_func locals typ pat expr =
  let fname = fresh_func_name() in
  let locals' = List.fold ~init:locals ~f:(fun a (t, v) -> Map.Poly.set a ~key:t ~data:v) pat.tpat_vars in
  let (funcs, expr_trans) = func_transform_expr locals' expr in
  let vars_used = texpression_free_vars expr in
  let closure_vars = Map.Poly.filter_keys vars_used ~f:(Map.Poly.mem locals) in
  let closure_list = Map.to_alist closure_vars in
  let fdata = {
    fd_pat = pat;
    fd_expr = expr_trans;
    fd_cvars = closure_list;
    fd_type = typ;
    fd_name = fname
  }
  in
  let closure_tuple_items = List.map closure_list ~f:(fun (v, t) ->
    {
      texp_desc = Texp_ident(v);
      texp_type = t;
      texp_loc = Location.none
    })
  in
  let (_, cvar_types) = List.unzip closure_list in
  let tuple = {
    texp_desc = Texp_tuple(closure_tuple_items);
    texp_type = T_tuple(cvar_types);
    texp_loc = Location.none
  }
  in
  let fident = {
    texp_desc = Texp_ident(fname);
    texp_type = T_func(T_tuple(cvar_types), typ);
    texp_loc = Location.none
  }
  in (fdata :: funcs, Texp_apply(fident, [tuple]))

and func_transform_structure_item (si: tstructure_item) =
  let (funcs, desc) =
    match si.tstr_desc with
    | Tstr_eval(e) ->
        let (funcs, e') = func_transform_expr Map.Poly.empty e in
        (funcs, Tstr_eval(e'))
    | Tstr_value (rf, tvb_list) ->
        let (funcs, _, tvb_list') = func_transform_value_bindings Map.Poly.empty rf tvb_list in
        (funcs, Tstr_value(rf, tvb_list'))
    | Tstr_type -> ([], si.tstr_desc)
  in (funcs, {si with tstr_desc = desc})


and func_transform_structure (struc: tstructure) =
  let (funcs_list, si_list) = List.unzip (List.map struc ~f:func_transform_structure_item) in
  let funcs = List.concat funcs_list in
  (funcs, si_list)


let func_data_to_string fdata =
  let pstr = tpattern_to_string fdata.fd_pat in
  let estr = texpression_to_string fdata.fd_expr in
  let tstr = string_of_scheme_type fdata.fd_type in
  let cvstr = String.concat ~sep:", " (List.map fdata.fd_cvars ~f:(fun (v,t) ->
    (v ^ " : " ^ (string_of_scheme_type t))))
  in fdata.fd_name ^ "{\n  pat = " ^ pstr ^ "\n  expr = " ^ estr ^ "\n  type = " ^ tstr ^ "\n  vars = " ^ cvstr ^ "\n}"


let print_func_datas fdlist =
  List.iter fdlist ~f:(fun fd ->
    let str = func_data_to_string fd in
    Stdio.print_endline str)


(* let function_transform (ctx : Context.context) (ast : tstructure) = *)
