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
  fd_cvars: (tident * scheme_type) list;
  fd_type: scheme_type;
  fd_name: string;
  fd_export_name: string option;
}

type type_map = (tident, scheme_type) Map.Poly.t

let add_vars map vars =
  List.fold ~init:map ~f:(fun m (tv, t) -> Map.Poly.set m ~key:tv ~data:t) vars

let rec remove_apps name count =
  if String.is_suffix name ~suffix:"-app" then
    remove_apps (String.chop_suffix_exn name ~suffix:"-app") (count + 1)
  else (name, count)

type state = {
  mutable fnames : func_names;
  mutable funcs : func_data list;
  mutable next_var : int;
}

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


let rec generate_let_bindings expr match_args =
  match match_args with
  | [] -> expr
  | (arg_name, pat) :: match_args' ->
      let tvb =
        {
          tvb_pat = pat;
          tvb_expr = {
            texp_desc = Texp_ident(arg_name);
            texp_loc = Location.none;
            texp_type = pat.tpat_type;
          };
          tvb_vars = List.map pat.tpat_vars ~f:(fun (vname, vtyp) -> (vname, Forall(Set.Poly.empty, vtyp)));
        }
      in
      let inner_expr = generate_let_bindings expr match_args' in
      {expr with
        texp_desc = Texp_let(Asttypes.Nonrecursive, [tvb], inner_expr);
      }

let rec func_transform_expr ?next_name:(next_name=None) ?match_args:(match_args=[])
                            (state: state) (locals: type_map) (in_expr: texpression) =
  let expr =
    match in_expr.texp_desc with
    | Texp_fun _ -> in_expr
    | _ -> generate_let_bindings in_expr (List.rev match_args)
  in
  let desc =
    match expr.texp_desc with
    | Texp_ident(x) -> Texp_ident(x)
    | Texp_constant(c) -> Texp_constant(c)
    | Texp_let (rf, tvb_list, e) -> func_transform_let state locals rf tvb_list e
    | Texp_fun (p, e) -> func_transform_func next_name match_args state locals expr.texp_type p e
    | Texp_apply (a, blist) ->
        let a' = func_transform_expr state locals a in
        let blist' = List.map blist ~f:(func_transform_expr state locals) in
        (Texp_apply(a', blist'))
    | Texp_special(_, _, _) -> expr.texp_desc
    | Texp_match (e, cases) -> func_transform_match state locals e cases
    | Texp_tuple(ls) ->
        let ls' = List.map ls ~f:(func_transform_expr state locals) in
        (Texp_tuple(ls'))
    | Texp_construct (name, ls) ->
        let ls' = List.map ls ~f:(func_transform_expr state locals) in
        (Texp_construct(name, ls'))
    | Texp_ifthenelse (i, t, e_opt) ->
        let i' = func_transform_expr state locals i in
        let t' = func_transform_expr state locals t in
        (match e_opt with
        | Some(e) ->
            let e' = func_transform_expr state locals e in
            (Texp_ifthenelse(i', t', Some(e')))
        | None ->
            (Texp_ifthenelse(i', t', None)))
    | Texp_while(cond, inner) ->
        let cond' = func_transform_expr state locals cond in
        let inner' = func_transform_expr state locals inner in
        (Texp_while(cond', inner'))
    | Texp_for(var_opt, min, max, dir, inner) ->
        let min' = func_transform_expr state locals min in
        let max' = func_transform_expr state locals max in
        let inner' = func_transform_expr state locals inner in
        (Texp_for(var_opt, min', max', dir, inner'))
    | Texp_sequence(a, b) ->
        let a' = func_transform_expr state locals a in
        let b' = func_transform_expr state locals b in
        (Texp_sequence(a', b'))
  in
  {expr with texp_desc = desc}


and func_transform_value_bindings state locals rf tvb_list =
  let vars = List.concat (List.map tvb_list ~f:(fun tvb -> tvb.tvb_pat.tpat_vars)) in
  let locals' = List.fold ~init:locals ~f:(fun a (v, t) -> Map.Poly.set a ~key:v ~data:t) vars in
  let inner_locals =
    (match rf with
    | Asttypes.Nonrecursive -> locals
    | Asttypes.Recursive -> locals')
  in
  let tvb_list' = List.map tvb_list ~f:(fun tvb ->
    let next_name =
      match tvb.tvb_pat.tpat_desc with
      | Tpat_var((name, _)) -> Some(name)
      | _ -> None
    in
    let e' = func_transform_expr ~next_name:next_name state inner_locals tvb.tvb_expr in
    {tvb with tvb_expr = e'})
  in
  (locals', tvb_list')

and func_transform_let state locals rf tvb_list e =
  let (locals', tvb_list') = func_transform_value_bindings state locals rf tvb_list in
  let e' = func_transform_expr state locals' e in
  (Texp_let(rf, tvb_list', e'))

and func_transform_func next_name match_args state locals typ pat expr =
  let (fnames1, fname, app_name) =
    match next_name with
    | Some(name) -> add_named_func state.fnames name
    | None -> add_anon_func state.fnames
  in
  let () = state.fnames <- fnames1 in
  let arg_name = "arg_" ^ (String.chop_prefix_exn ~prefix:"$$f_" fname) in
  let arg_id = state.next_var in
  state.next_var <- arg_id + 1;
  let arg_ident = (arg_name, arg_id) in
  let new_pat = {
    tpat_desc = Tpat_var(arg_ident);
    tpat_loc = Location.none;
    tpat_type = pat.tpat_type;
    tpat_vars = [(arg_ident, pat.tpat_type)]
  }
  in
  let locals' = Map.set locals ~key:arg_ident ~data:pat.tpat_type in
  let next_name' = Some(app_name) in
  let match_args' = (arg_ident, pat) :: match_args in
  let expr_trans = func_transform_expr ~next_name:next_name' ~match_args:match_args' state locals' expr in
  let vars_used = texpression_free_vars expr_trans in
  let closure_vars = Map.Poly.filter_keys vars_used ~f:(Map.Poly.mem locals) in
  let closure_list = Map.to_alist closure_vars in
  let fdata = {
    fd_pat = new_pat;
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
  let () = state.funcs <- fdata :: state.funcs in
  (Texp_special(Tspec_mkclosure, fname, [tuple]))

and func_transform_structure_item state (si: tstructure_item) =
  let desc =
    match si.tstr_desc with
    | Tstr_eval(e) ->
        let e' = func_transform_expr state Map.Poly.empty e in
        (Tstr_eval(e'))
    | Tstr_value (rf, tvb_list) ->
        let (_, tvb_list') = func_transform_value_bindings state Map.Poly.empty rf tvb_list in
        (Tstr_value(rf, tvb_list'))
    | Tstr_type -> (si.tstr_desc)
  in {si with tstr_desc = desc}

and func_transform_match state locals e cases =
  let e' = func_transform_expr state locals e in
  let cases' = List.map cases ~f:(fun case ->
    let locals' = List.fold ~init:locals ~f:(fun a (v, t) -> Map.Poly.set a ~key:v ~data:t) case.tc_lhs.tpat_vars in
    let rhs' = func_transform_expr state locals' case.tc_rhs in
    {case with tc_rhs = rhs'}
  )
  in
  (Texp_match(e', cases'))

and func_transform_structure next_var (struc: tstructure) =
  let fnames = {
    temp_count = 0;
    names = Set.Poly.empty
  }
  in
  let state = {
    fnames = fnames;
    funcs = [];
    next_var = next_var;
  }
  in
  let si_list = List.map struc ~f:(func_transform_structure_item state) in
  let funcs' = select_export_functions state.fnames state.funcs in
  (funcs', si_list, state.next_var)


let func_data_to_string fdata =
  let pstr = tpattern_to_string fdata.fd_pat in
  let estr = texpression_to_string fdata.fd_expr in
  let tstr = string_of_scheme_type fdata.fd_type in
  let cvstr = String.concat ~sep:", " (List.map fdata.fd_cvars ~f:(fun (v,t) ->
    ((tident_to_string v) ^ " : " ^ (string_of_scheme_type t))))
  in fdata.fd_name ^ "{\n  pat = " ^ pstr ^ "\n  expr = " ^ estr ^ "\n  type = " ^ tstr ^ "\n  vars = " ^ cvstr ^ "\n}"


let print_func_datas fdlist =
  List.iter fdlist ~f:(fun fd ->
    let str = func_data_to_string fd in
    Stdio.print_endline str)


(* let function_transform (ctx : Context.context) (ast : tstructure) = *)
