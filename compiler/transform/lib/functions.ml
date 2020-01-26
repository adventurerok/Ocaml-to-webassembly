open Core_kernel
open Otwa_types
open Types
open Typed_ast

(* The purpose of this transform is to extract all function definitions to the top level *)
(* Input shall be a typed-ast and a typed context *)
(* Output shall be top-level functions, and left-over code transformed into a main function *)

type func_names = {
  temp_count: int;
  names: string Set.Poly.t;
}

let add_anon_func fnames =
  let base_name = "anon_" ^ (Int.to_string fnames.temp_count) in
  let anon_name = "$$f_" ^ base_name in
  ({
    temp_count = fnames.temp_count + 1;
    names = Set.Poly.add fnames.names anon_name
  }, anon_name, base_name ^ "-app")

let add_named_func fnames n =
  let rec find_free_name test_name cnt =
    let extension = if cnt = 0 then "" else "-" ^ (Int.to_string cnt) in
    let full_name = test_name ^ extension in
    if Set.Poly.mem fnames.names full_name then
      find_free_name test_name (cnt + 1)
    else
      full_name
  in
  let func_name = find_free_name ("$$f_" ^ n) 0 in
  let base_name = String.chop_prefix_exn func_name ~prefix:"$$f_" in
  ({
    fnames with
    names= Set.Poly.add fnames.names func_name
  }, func_name, base_name ^ "-app")

type func_data = {
  fd_pat: tpattern;
  fd_expr: texpression;
  fd_cvars: (string * scheme_type) list;
  fd_type: scheme_type;
  fd_name: string;
  fd_export_name: string option;
}

type type_map = (string, scheme_type) Map.Poly.t

let add_vars map vars =
  List.fold ~init:map ~f:(fun m (tv, t) -> Map.Poly.set m ~key:tv ~data:t) vars

let rec remove_apps name count =
  if String.is_suffix name ~suffix:"-app" then
    remove_apps (String.chop_suffix_exn name ~suffix:"-app") (count + 1)
  else (name, count)

(* Gives export names to the functions to export *)
(* Current criteria: named functions with all their arguments (most -apps on the end), with no cvars *)
let select_export_functions fnames funcs =
  List.map funcs ~f:(fun func ->
    let with_app = func.fd_name ^ "-app" in
    let (noapp_name, app_count) = remove_apps func.fd_name 0 in
    if ((not (String.is_prefix func.fd_name ~prefix:"$$f_anon_")) &&
        (not (Set.mem fnames.names with_app)) &&
        ((List.length func.fd_cvars) = app_count)) then
      let export_name = (String.chop_prefix_exn noapp_name ~prefix:"$$f_") in
      {
        func with
        fd_export_name = Some(export_name)
      }
    else
      func)

(* TODO inconsistent naming with intermediate's transform_list which also concats the results *)
let transform_list ~f:map fnames locals lst =
  let (fnames', funcs_rev, result_rev) = List.fold lst ~init:(fnames, [], []) ~f:(fun (fn, f_lst, out_lst) item ->
    let (fn', item_funcs, item_ast) = map fn locals item in
    (fn', item_funcs :: f_lst, item_ast :: out_lst))
  in
  let funcs = List.concat (List.rev funcs_rev) in
  (fnames', funcs, List.rev result_rev)


(* So on an expression, we'll need the modified expression, and the map of id to function *)
(* Globals: Not in closure (global variables or arguments), Locals: In closure *)

let rec func_transform_expr ?next_name:(next_name=None) (fnames: func_names) (locals: type_map) (expr: texpression) =
  let (fnames', funcs, desc) =
    match expr.texp_desc with
    | Texp_ident(x) -> (fnames, [], Texp_ident(x))
    | Texp_constant(c) -> (fnames, [], Texp_constant(c))
    | Texp_let (rf, tvb_list, e) -> func_transform_let fnames locals rf tvb_list e
    | Texp_fun (p, e) -> func_transform_func next_name fnames locals expr.texp_type p e
    | Texp_apply (a, blist) ->
        let (fnames1, ft_a, a') = func_transform_expr fnames locals a in
        let (fnames2, ft_b, blist') = transform_list ~f:func_transform_expr fnames1 locals blist in
        (fnames2, ft_a @ ft_b, Texp_apply(a', blist'))
    | Texp_match (e, cases) -> func_transform_match fnames locals e cases
    | Texp_tuple(ls) ->
        let (fnames1, fcs, ls') = transform_list fnames locals ls ~f:func_transform_expr in
        (fnames1, fcs, Texp_tuple(ls'))
    | Texp_construct (name, ls) ->
        let (fnames1, fcs, ls') = transform_list fnames locals ls ~f:func_transform_expr in
        (fnames1, fcs, Texp_construct(name, ls'))
    | Texp_ifthenelse (i, t, e_opt) ->
        let (fnames1, ifuncs, i') = func_transform_expr fnames locals i in
        let (fnames2, tfuncs, t') = func_transform_expr fnames1 locals t in
        (match e_opt with
        | Some(e) ->
            let (fnames3, efuncs, e') = func_transform_expr fnames2 locals e in
            (fnames3, ifuncs @ tfuncs @ efuncs, Texp_ifthenelse(i', t', Some(e')))
        | None ->
            (fnames2, ifuncs @ tfuncs, Texp_ifthenelse(i', t', None)))
    | Texp_while(cond, inner) ->
        let (fnames1, cfuncs, cond') = func_transform_expr fnames locals cond in
        let (fnames2, ifuncs, inner') = func_transform_expr fnames1 locals inner in
        (fnames2, cfuncs @ ifuncs, Texp_while(cond', inner'))
    | Texp_for(var_opt, min, max, dir, inner) ->
        let (fnames1, min_funcs, min') = func_transform_expr fnames locals min in
        let (fnames2, max_funcs, max') = func_transform_expr fnames1 locals max in
        let (fnames3, inner_funcs, inner') = func_transform_expr fnames2 locals inner in
        (fnames3, min_funcs @ max_funcs @ inner_funcs, Texp_for(var_opt, min', max', dir, inner'))
    | Texp_sequence(a, b) ->
        let (fnames1, afuncs, a') = func_transform_expr fnames locals a in
        let (fnames2, bfuncs, b') = func_transform_expr fnames1 locals b in
        (fnames2, afuncs @ bfuncs, Texp_sequence(a', b'))
  in (fnames', funcs, {expr with texp_desc = desc})

and func_transform_value_bindings fnames locals rf tvb_list =
  let vars = List.concat (List.map tvb_list ~f:(fun tvb -> tvb.tvb_pat.tpat_vars)) in
  let locals' = List.fold ~init:locals ~f:(fun a (v, t) -> Map.Poly.set a ~key:v ~data:t) vars in
  let inner_locals =
    (match rf with
    | Asttypes.Nonrecursive -> locals
    | Asttypes.Recursive -> locals')
  in
  let (fnames1, tvb_funcs, tvb_list') = transform_list fnames inner_locals tvb_list ~f:(fun fn _ tvb ->
    let next_name =
      match tvb.tvb_pat.tpat_desc with
      | Tpat_var(name) -> Some(name)
      | _ -> None
    in
    let (fn1, fcs, e') = func_transform_expr ~next_name:next_name fn inner_locals tvb.tvb_expr in
    (fn1, fcs, {tvb with tvb_expr = e'}))
  in
  (fnames1, tvb_funcs, locals', tvb_list')

and func_transform_let fnames locals rf tvb_list e =
  let (fnames1, tvb_funcs, locals', tvb_list') = func_transform_value_bindings fnames locals rf tvb_list in
  let (fnames2, e_funcs, e') = func_transform_expr fnames1 locals' e in
  (fnames2, e_funcs @ tvb_funcs, Texp_let(rf, tvb_list', e'))

and func_transform_func next_name fnames locals typ pat expr =
  let (fnames1, fname, app_name) =
    match next_name with
    | Some(name) -> add_named_func fnames name
    | None -> add_anon_func fnames
  in
  let locals' = List.fold ~init:locals ~f:(fun a (t, v) -> Map.Poly.set a ~key:t ~data:v) pat.tpat_vars in
  let next_name' = Some(app_name) in
  let (fnames2, funcs, expr_trans) = func_transform_expr ~next_name:next_name' fnames1 locals' expr in
  let vars_used = texpression_free_vars expr in
  let closure_vars = Map.Poly.filter_keys vars_used ~f:(Map.Poly.mem locals) in
  let closure_list = Map.to_alist closure_vars in
  let fdata = {
    fd_pat = pat;
    fd_expr = expr_trans;
    fd_cvars = closure_list;
    fd_type = typ;
    fd_name = fname;
    fd_export_name = None
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
  in (fnames2, fdata :: funcs, Texp_apply(fident, [tuple]))

and func_transform_structure_item fnames (si: tstructure_item) =
  let (fnames', funcs, desc) =
    match si.tstr_desc with
    | Tstr_eval(e) ->
        let (fnames1, funcs, e') = func_transform_expr fnames Map.Poly.empty e in
        (fnames1, funcs, Tstr_eval(e'))
    | Tstr_value (rf, tvb_list) ->
        let (fnames1, funcs, _, tvb_list') = func_transform_value_bindings fnames Map.Poly.empty rf tvb_list in
        (fnames1, funcs, Tstr_value(rf, tvb_list'))
    | Tstr_type -> (fnames, [], si.tstr_desc)
  in (fnames', funcs, {si with tstr_desc = desc})

and func_transform_match fnames locals e cases =
  let (fnames1, efuncs, e') = func_transform_expr fnames locals e in
  let (fnames2, funcs, cases') = transform_list fnames1 locals cases ~f:(fun fn _ case ->
    let locals' = List.fold ~init:locals ~f:(fun a (v, t) -> Map.Poly.set a ~key:v ~data:t) case.tc_lhs.tpat_vars in
    let (fn', cfuncs, rhs') = func_transform_expr fn locals' case.tc_rhs in
    (fn', cfuncs, {case with tc_rhs = rhs'})
  )
  in
  (fnames2, efuncs @ funcs, Texp_match(e', cases'))

and func_transform_structure (struc: tstructure) =
  let fnames = {
    temp_count = 0;
    names = Set.Poly.empty
  }
  in
  let (fnames', funcs, si_list) = transform_list fnames 0 struc ~f:(fun fn _ item ->
    func_transform_structure_item fn item)
  in
  let funcs' = select_export_functions fnames' funcs in
  (funcs', si_list)


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
