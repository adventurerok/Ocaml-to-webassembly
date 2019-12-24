open Core_kernel
open Intermediate_ast

type vars = {
  count: int;
  scope: iscope;
  data: ((string * string * itype) list);
  temp_count: int;
  var_names: string Set.Poly.t;
  blocks: int;
  temp_prefix: string;
  named_prefix: string;
}

let base_empty_vars = {
  count = 0;
  scope = Local;
  data = [];
  temp_count = 0;
  var_names = Set.Poly.empty;
  blocks = 0;
  temp_prefix = "$temp_";
  named_prefix = "$";
}

let empty_global_vars = {
  base_empty_vars with
  scope = Global
}

let add_var_mapping (vrs : vars) (n : string) (vn : string) (t : itype) =
  {
    vrs with
    count = vrs.count + 1;
    data = (n, vn, t) :: vrs.data;
    var_names = Set.Poly.add vrs.var_names vn
  }


let add_temp_var (vrs : vars) (t : itype) =
  let name = vrs.temp_prefix ^ (Int.to_string vrs.temp_count) in
  let vrs' = {
    vrs with
    temp_count = vrs.temp_count + 1;
  }
  in
  (add_var_mapping vrs' name name t, (vrs.scope, name))

let add_named_var (vrs : vars) (n : string) (t : itype) =
  let rec find_free_name test_name cnt =
    let extension = if cnt = 0 then "" else "-" ^ (Int.to_string cnt) in
    let full_name = test_name ^ extension in
    if Set.Poly.mem vrs.var_names full_name then
      find_free_name test_name (cnt + 1)
    else
      full_name
  in
  let var_name = find_free_name (vrs.named_prefix ^ n) 0 in
  (add_var_mapping vrs n var_name t, (vrs.scope, var_name))

let add_block (vrs : vars) =
  let block_name = "$block_" ^ (Int.to_string vrs.blocks) in
  let vrs' = {
    vrs with
    blocks = vrs.blocks + 1
  } in
  (vrs', block_name)

let lookup_var (vrs : vars) (n : string) =
  let rec loop data =
    match data with
    | [] -> None
    | (code_name, var_name, _) :: data' ->
        if (String.equal n code_name) || (String.equal n var_name) then
          Some((vrs.scope, var_name))
        else loop data'
  in
  loop vrs.data

let lookup_var_or_global (vrs : vars) (n : string) =
  match (lookup_var vrs n) with
  | Some(var) -> var
  | None -> (Global, n)

let function_arg_name = "$arg"
let function_arg = (Local, function_arg_name)

let make_local_vars (fdata : Functions.func_data) =
  let empty = {
    base_empty_vars with
    scope = Local
  } in
  let with_cvars = List.fold fdata.fd_cvars ~init:empty ~f:(fun vars (name,st) ->
    let ityp = stoitype st in
    let (vars', _) = add_named_var vars name ityp in
    vars')
  in
  let with_arg = add_var_mapping with_cvars function_arg_name function_arg_name (stoitype fdata.fd_pat.tpat_type) in
  with_arg

let make_init_vars global_vars =
  {
    base_empty_vars with
    count = 1;
    scope = Local;
    data = [("$init_arg", "$init_arg", It_none)];
    var_names = Set.Poly.singleton "$init_arg";
    blocks = global_vars.blocks
  }

let vars_to_string vars =
  let dstr = List.map vars.data ~f:(fun (name, var_name, typ) ->
    name ^ " -> " ^ var_name ^ " (" ^ (itype_to_string typ) ^ ")"
  )
  in
  String.concat ~sep:"\n" dstr

(* Gets the ordered list of var name and type *)
let get_vars vars =
  List.rev (List.map vars.data ~f:(fun (_, var_name, typ) -> (var_name, typ)))
