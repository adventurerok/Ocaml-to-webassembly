open Core_kernel
open Intermediate_ast

type vars = {
  count: int;
  global: bool;
  data: ((string * string * itype) list)
}

let empty_global_vars = {
  count = 0;
  global = true;
  data = []
}

let add_var_mapping (vrs : vars) (n : string) (vn : string) (t : itype) =
  {
    vrs with
    count = vrs.count + 1;
    data = (n, vn, t) :: vrs.data
  }


let add_temp_var (vrs : vars) (t : itype) =
  let name = "@temp_" ^ (Int.to_string vrs.count) in
  (add_var_mapping vrs name name t, name)

let add_named_var (vrs : vars) (n : string) (t : itype) =
  let var_name = "@var_" ^ (Int.to_string vrs.count) ^ "_" ^ n in
  (add_var_mapping vrs n var_name t, var_name)

let lookup_var (vrs : vars) (n : string) =
  let rec loop data =
    match data with
    | [] -> None
    | (code_name, var_name, _) :: data' ->
        if (String.equal n code_name) || (String.equal n var_name) then
          Some(var_name)
        else loop data'
  in
  loop vrs.data

let lookup_var_or_global (vrs : vars) (n : string) =
  match (lookup_var vrs n) with
  | Some(var_name) -> var_name
  | None -> "@global_" ^ n

let function_arg = "@arg"

let make_local_vars (fdata : Functions.func_data) =
  let empty = {
    count = 0;
    global = false;
    data = []
  } in
  let with_cvars = List.fold fdata.fd_cvars ~init:empty ~f:(fun vars (name,st) ->
    let ityp = stoitype st in
    let (vars', _) = add_named_var vars name ityp in
    vars')
  in
  let with_arg = add_var_mapping with_cvars function_arg function_arg (stoitype fdata.fd_pat.tpat_type) in
  with_arg
