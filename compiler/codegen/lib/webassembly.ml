open Core_kernel
open Otwa_transform
open Intermediate_ast
open Intermediate_program

(* Malloc will take an int number of bytes to allocate, and return a pointer to the new memory *)
let malloc_id = "$malloc"

exception CodegenFailure of string

let itype_to_watype it =
  match it with
  | It_bool -> "i32"
  | It_int -> "i32"
  | It_pointer -> "i32"
  | It_float -> "f32"
  | It_unit -> "i32"
  | It_none -> raise (CodegenFailure "It_none cannot be converted directly to wasm")

let itype_to_waresult it =
  match it with
  | It_none -> ""
  | _ -> "(result " ^ (itype_to_watype it) ^ ")"

let itype_size it =
  match it with
  | It_bool -> 4
  | It_int -> 4
  | It_pointer -> 4
  | It_float -> 4
  | It_unit -> 4
  | It_none -> 0

let ituptype_size itt =
  Option.value ~default:0 (List.reduce (List.map itt ~f:itype_size) ~f:(+))


let codegen_local_vars vars ret_typ cvar_count =
  let var_list = Vars.get_vars vars in
  let wa_result = itype_to_waresult ret_typ in
  let strs = List.mapi var_list ~f:(fun index (var_name, ityp) ->
    let watyp = itype_to_watype ityp in
    if index <= cvar_count then
      let param = "(param " ^ var_name ^ " " ^ watyp ^ ")" in
      if index = cvar_count then
        param ^ "\n" ^ wa_result
      else param
    else "(local " ^ var_name ^ " " ^ watyp ^ ")"
  )
  in
  String.concat ~sep:"\n" strs

let rec codegen_iexpr_list lst =
  let codes = List.map lst ~f:codegen_iexpr in
  String.concat ~sep:"\n" codes

and codegen_iexpr (expr : iexpression) =
  let none = "NONE" in
  match expr with
  | Iexp_newvar (_, (scope, name)) -> (iscope_to_string scope) ^ ".set " ^ name
  | Iexp_pushvar (_, (scope, name)) -> (iscope_to_string scope) ^ ".get " ^ name
  | Iexp_binop (ityp, binop) -> codegen_binop ityp binop
  | Iexp_pushconst (ityp, str_rep) -> codegen_const ityp str_rep
  | Iexp_newclosure (_, _, _, _) -> none
  | Iexp_fillclosure _ -> none
  | Iexp_callclosure _ -> none
  | Iexp_block (name, typ, lst) -> codegen_block name typ lst
  | Iexp_exitblock(name) -> "br " ^ name
  | Iexp_exitblockif(name) -> "br_if " ^ name
  | Iexp_ifthenelse (name, ityp, tcode, ecode_opt) -> codegen_ifthenelse name ityp tcode ecode_opt
  | Iexp_pushtuple(itt, name, tuple_codelst) -> codegen_pushtuple itt name tuple_codelst
  | Iexp_loadtupleindex (itt, index) -> codegen_tupleindex itt index 0
  | Iexp_pushconstruct (itt, name, id, tuple_codelst) ->
      codegen_pushtuple (It_int :: itt) name ([Iexp_pushconst(It_int, Int.to_string id)] :: tuple_codelst)
  | Iexp_loadconstructindex (itt, index) -> codegen_tupleindex (It_int :: itt) (index + 1) 0
  | Iexp_loadconstructid -> codegen_tupleindex [It_int] 0 0
  | Iexp_fail -> "unreachable"
  | Iexp_drop _ -> "drop"

and codegen_binop ityp binop =
  let opname =
    match binop with
    | Ibin_add -> "add"
    | Ibin_sub -> "sub"
    | Ibin_mul -> "mul"
    | Ibin_div -> "div_s"
    | Ibin_rem -> "rem_s"
    | Ibin_and -> "and"
    | Ibin_or -> "or"
    | Ibin_eq -> "eq"
    | Ibin_ne -> "ne"
    | Ibin_lt -> "lt_s"
    | Ibin_le -> "le_s"
    | Ibin_gt -> "gt_s"
    | Ibin_ge -> "ge_s"
  in
  let watyp = itype_to_watype ityp in
  watyp ^ "." ^ opname

and codegen_const ityp str_rep =
  match ityp with
  | It_bool ->
      let booltyp = itype_to_watype It_bool in
      (match str_rep with
      | "true" -> booltyp ^ ".const 1"
      | "false" -> booltyp ^ ".const 0"
      | _ -> raise (CodegenFailure "Boolean is not true or false"))
  | It_unit ->
      (itype_to_watype It_unit) ^ ".const 0"
  | _ ->
      let watyp = itype_to_watype ityp in
      watyp ^ ".const " ^ str_rep

and codegen_block name ityp code_lst =
  let wa_lst = codegen_iexpr_list code_lst in
  let wa_result = itype_to_waresult ityp in
  "block " ^ name ^ " " ^ wa_result ^ "\n" ^
  wa_lst ^ "\n" ^
  "end " ^ name

and codegen_ifthenelse name ityp tcode ecode_opt =
  let wa_tcode = codegen_iexpr_list tcode in
  "if " ^ name ^ " " ^ (itype_to_watype ityp) ^ "\n" ^
  wa_tcode ^ "\n" ^
  (match ecode_opt with
  | Some(ecode) ->
      let wa_ecode = codegen_iexpr_list ecode in
      "else\n" ^ wa_ecode ^ "\n"
  | None -> "") ^
  "end"

and codegen_pushtuple itt (scope_enum, name) tuple_codelst =
  let tup_size = ituptype_size itt in
  let scope = iscope_to_string scope_enum in
  "i32.const " ^ (Int.to_string tup_size) ^ "\n" ^
  "call " ^ malloc_id ^ "\n" ^
  scope ^ ".set " ^ name ^ "\n" ^
  (
    let zipped_lst = List.zip_exn itt tuple_codelst in
    let (_, code_list_rev) = List.fold zipped_lst ~init:(0, []) ~f:(fun (offset, out_lst) (it, item_code) ->
      let item_wa =
        scope ^ ".get " ^ name ^ "\n" ^
        (codegen_iexpr_list item_code) ^ "\n" ^
        (itype_to_watype it) ^ ".store offset=" ^ (Int.to_string offset)
      in
      (offset + (itype_size it), item_wa :: out_lst)
  )
  in
  String.concat ~sep:"\n" (List.rev code_list_rev)) ^ "\n" ^
  scope ^ ".get " ^ name

and codegen_tupleindex itt index offset =
  (* Only types that occur before the one we want *)
  let itt_trim = List.take itt index in
  let final_offset = List.fold itt_trim ~init:offset ~f:(fun o ityp -> o + (itype_size ityp)) in
  let watyp = itype_to_watype (List.nth_exn itt index) in
  watyp ^ ".load offset=" ^ (Int.to_string final_offset)

let codegen_globals (globals : Vars.vars) =
  let global_list = Vars.get_vars globals in
  let global_wa_list = List.map global_list ~f:(fun (var_name, ityp) ->
    let watyp = itype_to_watype ityp in
    let export_name = (String.chop_prefix_exn var_name ~prefix:"$") in
    "(global " ^ var_name ^
    " (export \"" ^ export_name ^ "\")" ^
    " (mut " ^ watyp ^ ") (" ^ watyp ^ ".const 0))")
  in
  String.concat ~sep:"\n" global_wa_list

let codegen_ifunction (func : ifunction) =
  let (_, ret_typ) = func.pf_type in
  let cvar_count = List.length func.pf_cvars in
  let export_name = String.chop_prefix_exn func.pf_name ~prefix:"$" in
  "(func " ^ func.pf_name ^ " (export \"" ^ export_name ^ "\")\n"
  ^ (codegen_local_vars func.pf_vars ret_typ cvar_count) ^ "\n"
  ^ (codegen_iexpr_list func.pf_code) ^ "\n"
  ^ ")"

let pretty_indent str =
  let lines = String.split_lines str in
  let fixed_lines = List.folding_map lines ~init:0 ~f:(fun indent line ->
    let lbracket_count = String.count line ~f:(fun c -> c = '(') in
    let rbracket_count = String.count line ~f:(fun c -> c = ')') in
    let new_indent = indent + lbracket_count - rbracket_count in
    let line_indent = if String.is_prefix line ~prefix:")" then new_indent else indent in
    (new_indent, (String.make (2 * line_indent) ' ') ^ line))
  in
  String.concat ~sep:"\n" fixed_lines

let iprogram_to_module (prog : iprogram) =
  let ugly_code =
    "(module\n" ^
    (codegen_globals prog.prog_globals) ^ "\n" ^
    (let (_, func_list) = List.unzip (Map.Poly.to_alist prog.prog_functions) in
    let func_codes = List.map func_list ~f:codegen_ifunction in
    String.concat ~sep:"\n" func_codes) ^ "\n" ^
    ")"
  in
  pretty_indent ugly_code
