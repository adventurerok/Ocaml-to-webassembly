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

type trav_state = {
  mutable fnames : func_names;
  mutable funcs : func_data list;
  traverser: ((trav_state, trav_input, unit) Traverse_ast.traverser)
}

and trav_input = {
  next_name: string option;
  locals: type_map;
}

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

(* So on an expression, we'll need the modified expression, and the map of id to function *)
(* Globals: Not in closure (global variables or arguments), Locals: In closure *)

and func_transform_func state input typ pat expr =
  let locals = input.locals in
  let next_name = input.next_name in
  let (fnames1, fname, app_name) =
    match next_name with
    | Some(name) -> add_named_func state.fnames name
    | None -> add_anon_func state.fnames
  in
  let () = state.fnames <- fnames1 in
  let locals' = List.fold ~init:locals ~f:(fun a (t, v) -> Map.Poly.set a ~key:t ~data:v) pat.tpat_vars in
  let next_name' = Some(app_name) in
  let input1 = {
    next_name = next_name';
    locals = locals'
  }
  in
  let (_, expr_trans) = Traverse_ast.traverse_expr state.traverser state input1 expr in
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
  in
  let () = state.funcs <- fdata :: state.funcs in
  (Texp_apply(fident, [tuple]))



let trav_step_input _ input = {
  input with
  next_name = None
}

let trav_pre_expr state input expr =
  match expr.texp_desc with
  | Texp_fun(pat, inner) ->
      let desc' = func_transform_func state input expr.texp_type pat inner in
      (input, {expr with texp_desc = desc'})
  | _ -> (input, expr)

let trav_pre_let _ input (rf, tvb_lst, _) =
  let vars = List.concat (List.map tvb_lst ~f:(fun tvb -> tvb.tvb_pat.tpat_vars)) in
  let locals = input.locals in
  let locals' = List.fold ~init:locals ~f:(fun a (v, t) -> Map.Poly.set a ~key:v ~data:t) vars in
  let inner_locals =
    (match rf with
    | Asttypes.Nonrecursive -> locals
    | Asttypes.Recursive -> locals')
  in
  ({input with locals = inner_locals}, {input with locals = locals'}, tvb_lst)

let trav_mid_value_binding _ input _ tvb =
    let next_name =
      match tvb.tvb_pat.tpat_desc with
      | Tpat_var(name) -> Some(name)
      | _ -> None
    in
    let input1 = {
      input with
      next_name = next_name
    }
    in
    (input1, tvb)

let trav_mid_case _ input _ case =
  let locals = input.locals in
  let locals' = List.fold ~init:locals ~f:(fun a (v, t) -> Map.Poly.set a ~key:v ~data:t) case.tc_lhs.tpat_vars in
  let input1 = {
    input with
    locals = locals'
  }
  in
  (input1, case)

let func_transform_traverse : (trav_state, trav_input, unit) Traverse_ast.traverser =
  {
    (Traverse_ast.no_output_traverser trav_step_input) with
    pre_let = trav_pre_let;
    mid_value_binding = trav_mid_value_binding;
    pre_expr = trav_pre_expr;
    mid_case = trav_mid_case
  }

let func_transform_structure (struc: tstructure) =
  let state = {
    fnames = {
      temp_count = 0;
      names = Set.Poly.empty
    };
    funcs = [];
    traverser = func_transform_traverse;
  }
  in
  let input = {
    next_name = None;
    locals = Map.Poly.empty;
  }
  in
  let (_, si_list) = Traverse_ast.traverse_structure state.traverser state input struc in
  let funcs' = select_export_functions state.fnames state.funcs in
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
