open Core_kernel
open Otwa_transform
open Intermediate_ast
open Intermediate_program

type string_int_map = (string, int) Map.Poly.t

(* Malloc will take an int number of bytes to allocate, and return a pointer to the new memory *)
let malloc_id = "$malloc"

let runtime =
  "(memory (export \"memory\") 1)\n" ^
  "(global $mem_idx (export \"mem_idx\") (mut i32) (i32.const 4))\n" ^
  "(func " ^ malloc_id ^ " (export \"malloc\") (param $size i32) (result i32)\n" ^
  "global.get $mem_idx\n" ^
  "global.get $mem_idx\n" ^
  "local.get $size\n" ^
  "i32.add\n" ^
  "global.set $mem_idx\n" ^
  ")"

let closure_call_export =
  "(func $call_closure_i32_i32 (export \"call_closure_i32_i32\") (param $closure i32) (param $arg i32) (result i32)\n" ^
  "local.get $closure\n" ^
  "local.get $arg\n" ^
  "local.get $closure\n" ^
  "i32.load offset=0\n" ^
  "call_indirect (type $type-i32-i32-i32)\n" ^
  ")"

exception CodegenFailure of string

let itype_to_watype it =
  match it with
  | It_poly -> "i32"
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
  | It_poly -> 4
  | It_bool -> 4
  | It_int -> 4
  | It_pointer -> 4
  | It_float -> 4
  | It_unit -> 4
  | It_none -> 0

let poly_size = itype_size It_poly
let poly_watype = itype_to_watype It_poly

let ituptype_size itt =
  Option.value ~default:0 (List.reduce (List.map itt ~f:itype_size) ~f:(+))


let closure_type_name ((iarg, iret) : iftype) =
  "$type-" ^ (itype_to_watype It_pointer) ^ "-" ^
  (itype_to_watype iarg) ^ "-" ^
  (match iret with
  | It_none -> "none"
  | _ -> itype_to_watype iret)

let wrapper_func_name func_name =
  "$wrap-" ^ (String.chop_prefix_exn func_name ~prefix:"$")

let codegen_local_vars vars ret_typ cvar_count =
  let var_list = Vars.get_vars vars in
  let wa_result = itype_to_waresult ret_typ in
  let strs = List.mapi var_list ~f:(fun index (var_name, ityp) ->
    if index <= cvar_count then
      let param =
        match ityp with
        | It_none -> ""
        | _ -> "(param " ^ var_name ^ " " ^ (itype_to_watype ityp) ^ ")"
      in
      if index = cvar_count then
        param ^ "\n" ^ wa_result
      else param
    else "(local " ^ var_name ^ " " ^ (itype_to_watype ityp) ^ ")"
  )
  in
  String.concat ~sep:"\n" strs

let rec codegen_iexpr_list (wrap_table : string_int_map) lst =
  let codes = List.map lst ~f:(codegen_iexpr wrap_table) in
  String.concat ~sep:"\n" codes

and codegen_iexpr (wrap_table : string_int_map) (expr : iexpression) =
  match expr with
  | Iexp_newvar (_, (scope, name)) -> (iscope_to_string scope) ^ ".set " ^ name
  | Iexp_pushvar (_, (scope, name)) -> (iscope_to_string scope) ^ ".get " ^ name
  | Iexp_binop (ityp, binop) -> codegen_binop ityp binop
  | Iexp_pushconst (ityp, str_rep) -> codegen_const ityp str_rep
  | Iexp_newclosure (ift, func_name, itt, var) -> codegen_newclosure wrap_table ift func_name itt var
  | Iexp_fillclosure(itt, var, tuple_codelst) -> codegen_fillclosure wrap_table itt var tuple_codelst
  | Iexp_callclosure(_, var, arg_code) -> codegen_callclosure wrap_table var arg_code
  | Iexp_block (name, typ, lst) -> codegen_block wrap_table name typ lst
  | Iexp_exitblock(name) -> "br " ^ name
  | Iexp_exitblockif(name) -> "br_if " ^ name
  | Iexp_ifthenelse (name, ityp, tcode, ecode_opt) -> codegen_ifthenelse wrap_table name ityp tcode ecode_opt
  | Iexp_pushtuple(itt, name, tuple_codelst) -> codegen_pushtuple wrap_table itt name tuple_codelst
  | Iexp_loadtupleindex (itt, index) -> codegen_tupleindex ~wrapped:true itt index 0
  | Iexp_pushconstruct (itt, name, id, tuple_codelst) ->
      codegen_pushtuple wrap_table (It_int :: itt) name ([Iexp_pushconst(It_int, Int.to_string id)] :: tuple_codelst)
  | Iexp_loadconstructindex (itt, index) -> codegen_tupleindex ~wrapped:true (It_int :: itt) (index + 1) 0
  | Iexp_loadconstructid -> codegen_tupleindex ~wrapped:false [It_int] 0 0
  | Iexp_wrap(ityp, unwrap, wrap) -> codegen_wrap ityp unwrap wrap
  | Iexp_unwrap(ityp, wrap, unwrap) -> codegen_unwrap ityp wrap unwrap
  | Iexp_fail -> "unreachable"
  | Iexp_drop _ -> "drop"

and codegen_binop ityp binop =
  let signed_ext =
    match ityp with
    | It_int -> "_s"
    | _ -> ""
  in
  let opname =
    match binop with
    | Ibin_add -> "add"
    | Ibin_sub -> "sub"
    | Ibin_mul -> "mul"
    | Ibin_div -> "div" ^ signed_ext
    | Ibin_rem -> "rem" ^ signed_ext
    | Ibin_and -> "and"
    | Ibin_or -> "or"
    | Ibin_eq -> "eq"
    | Ibin_ne -> "ne"
    | Ibin_lt -> "lt" ^ signed_ext
    | Ibin_le -> "le" ^ signed_ext
    | Ibin_gt -> "gt" ^ signed_ext
    | Ibin_ge -> "ge" ^ signed_ext
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

and codegen_newclosure wrap_table _ift func_name itt (vscope, vname) =
  let closure_tuple = It_int :: itt in
  let tup_size = ituptype_size closure_tuple in
  let scope = iscope_to_string vscope in
  let func_id = Map.Poly.find_exn wrap_table func_name in
  "i32.const " ^ (Int.to_string tup_size) ^ "\n" ^
  "call " ^ malloc_id ^ "\n" ^
  scope ^ ".set " ^ vname ^ "\n" ^
  scope ^ ".get " ^ vname ^ "\n" ^
  (itype_to_watype It_int) ^ ".const " ^ (Int.to_string func_id) ^ "\n" ^
  (itype_to_watype It_int) ^ ".store offset=0"

and codegen_fillclosure wrap_table itt var tuple_codelst =
  codegen_filltuple ~wrapped:false wrap_table itt var tuple_codelst (itype_size It_int)

and codegen_callclosure wrap_table (vscope, vname) arg_code =
  let scope = iscope_to_string vscope in
  scope ^ ".get " ^ vname ^ "\n" ^
  (codegen_iexpr_list wrap_table arg_code) ^ "\n" ^
  scope ^ ".get " ^ vname ^ "\n" ^
  (itype_to_watype It_int) ^ ".load offset=0\n" ^
  "call_indirect (type $type-i32-i32-i32)"

and codegen_block wrap_table name ityp code_lst =
  let wa_lst = codegen_iexpr_list wrap_table code_lst in
  let wa_result = itype_to_waresult ityp in
  "block " ^ name ^ " " ^ wa_result ^ "\n" ^
  wa_lst ^ "\n" ^
  "end " ^ name

and codegen_ifthenelse wrap_table name ityp tcode ecode_opt =
  let wa_tcode = codegen_iexpr_list wrap_table tcode in
  "if " ^ name ^ " " ^ (itype_to_waresult ityp) ^ "\n" ^
  wa_tcode ^ "\n" ^
  (match ecode_opt with
  | Some(ecode) ->
      let wa_ecode = codegen_iexpr_list wrap_table ecode in
      "else\n" ^ wa_ecode ^ "\n"
  | None -> "") ^
  "end"

and codegen_pushtuple wrap_table itt (scope_enum, name) tuple_codelst =
  let tup_size = ituptype_size itt in
  let scope = iscope_to_string scope_enum in
  "i32.const " ^ (Int.to_string tup_size) ^ "\n" ^
  "call " ^ malloc_id ^ "\n" ^
  scope ^ ".set " ^ name ^ "\n" ^
  (codegen_filltuple ~wrapped:true wrap_table itt (scope_enum, name) tuple_codelst 0) ^ "\n" ^
  scope ^ ".get " ^ name

and codegen_filltuple ~wrapped:wrapped wrap_table itt (scope_enum, name) tuple_codelst start_offset =
  let scope = iscope_to_string scope_enum in
  (
    let zipped_lst = List.zip_exn itt tuple_codelst in
    let (_, code_list_rev) = List.fold zipped_lst ~init:(start_offset, []) ~f:(fun (offset, out_lst) (it, item_code) ->
      let item_wa =
        scope ^ ".get " ^ name ^ "\n" ^
        (codegen_iexpr_list wrap_table item_code) ^ "\n" ^
        (if wrapped then poly_watype else (itype_to_watype it)) ^ ".store offset=" ^ (Int.to_string offset)
      in
      (offset + (if wrapped then poly_size else (itype_size it)), item_wa :: out_lst)
  )
  in
  String.concat ~sep:"\n" (List.rev code_list_rev))

and codegen_tupleindex ~wrapped:wrapped itt index offset =
  (* Only types that occur before the one we want *)
  let itt_trim = List.take itt index in
  let final_offset = List.fold itt_trim ~init:offset ~f:(fun o ityp ->
    o + (if wrapped then poly_size else (itype_size ityp)))
  in
  let watyp = itype_to_watype (List.nth_exn itt index) in
  (if wrapped then poly_watype else watyp) ^ ".load offset=" ^ (Int.to_string final_offset)

and codegen_wrap ityp (unwrap_scope_enum, unwrap_name) (wrap_scope_enum, wrap_name) =
  let wrap_size = itype_size ityp in
  let unwrap_scope = iscope_to_string unwrap_scope_enum in
  let wrap_scope = iscope_to_string wrap_scope_enum in
  "i32.const " ^ (Int.to_string wrap_size) ^ "\n" ^
  "call " ^ malloc_id ^ "\n" ^
  wrap_scope ^ ".set " ^ wrap_name ^ "\n" ^
  (match ityp with
  | It_float ->
      wrap_scope ^ ".get " ^ wrap_name ^ "\n" ^
      unwrap_scope ^ ".get " ^ unwrap_name ^ "\n" ^
      (itype_to_watype It_float) ^ ".store offset=0"
  | _ -> raise (CodegenFailure ("The type " ^ (itype_to_string ityp) ^ " cannot be wrapped")))

and codegen_unwrap ityp (wrap_scope_enum, wrap_name) (unwrap_scope_enum, unwrap_name) =
  let unwrap_scope = iscope_to_string unwrap_scope_enum in
  let wrap_scope = iscope_to_string wrap_scope_enum in
  let watyp = itype_to_watype ityp in
  match ityp with
  | It_float ->
    wrap_scope ^ ".get " ^ wrap_name ^ "\n" ^
    watyp ^ ".load offset=0\n" ^
    unwrap_scope ^ ".set " ^ unwrap_name
  | _ -> raise (CodegenFailure ("The type " ^ (itype_to_string ityp) ^ " cannot be unwrapped"))


(* Generate all closure types avoiding duplicates *)
let codegen_types () =
  let type_map = List.fold all_of_iftype ~init:Map.Poly.empty ~f:(fun map (iarg, iret) ->
    match iarg with
    | It_none -> map
    | _ ->
      let type_name = closure_type_name (iarg, iret) in
      let wa_sig =
        "(func (param " ^
        (itype_to_watype It_pointer) ^ " " ^
        (itype_to_watype iarg) ^ ") " ^
        (itype_to_waresult iret) ^ ")"
      in
      Map.Poly.set map ~key:type_name ~data:wa_sig)
  in
  let type_list = Map.Poly.to_alist type_map in
  let module_types = List.map type_list ~f:(fun (name, wa_sig) ->
    "(type " ^ name ^ " " ^ wa_sig ^ ")")
  in
  String.concat ~sep:"\n" module_types

let codegen_wrapper_table iprog =
  let func_names = Map.Poly.keys (Map.Poly.remove iprog.prog_functions iprog.prog_initfunc) in
  let wrap_names = List.map func_names ~f:wrapper_func_name in
  let wrap_table = List.foldi func_names ~init:Map.Poly.empty ~f:(fun index map name ->
    Map.Poly.set map ~key:name ~data:index)
  in
  let wrap_code =
    "(table (export \"wrapper_functions\") funcref\n" ^
    "(elem\n" ^
    (String.concat ~sep:"\n" wrap_names) ^ "\n" ^
    ")\n" ^
    ")"
  in (wrap_table, wrap_code)

let codegen_globals (globals : Vars.vars) =
  let global_list = Vars.get_vars globals in
  let global_wa_list = List.map global_list ~f:(fun (var_name, ityp) ->
    let watyp = itype_to_watype ityp in
    let export_name = "global_" ^ (String.chop_prefix_exn var_name ~prefix:"$") in
    "(global " ^ var_name ^
    " (export \"" ^ export_name ^ "\")" ^
    " (mut " ^ watyp ^ ") (" ^ watyp ^ ".const 0))")
  in
  String.concat ~sep:"\n" global_wa_list

let codegen_ifunction_core (wrap_table : string_int_map) (func : ifunction) =
  let (_, ret_typ) = func.pf_type in
  let cvar_count = List.length func.pf_cvars in
  let export =
    match func.pf_export_name with
    | Some(export_name) -> " (export \"" ^ export_name ^ "\")"
    | None -> ""
  in
  "(func " ^ func.pf_name ^ export ^ "\n"
  ^ (codegen_local_vars func.pf_vars ret_typ cvar_count) ^ "\n"
  ^ (codegen_iexpr_list wrap_table func.pf_code) ^ "\n"
  ^ ")"

(* Wrapper function takes two arguments: closure and function argument *)
let codegen_ifunction_wrapper (func : ifunction) =
  let wrapper_name = wrapper_func_name func.pf_name in
  let (iarg, iret) = func.pf_type in
  let wa_arg_type = itype_to_watype iarg in
  let wa_result_type = itype_to_watype iret in
  let arg_needs_unwrap = itype_needs_wrap iarg in
  let result_needs_wrap = itype_needs_wrap iret in
  "(func " ^ wrapper_name ^ "\n" ^
  "(param $closure " ^ (itype_to_watype It_pointer) ^ ")\n" ^
  "(param $arg " ^ poly_watype ^ ")\n" ^
  "(result " ^ poly_watype ^ ")\n" ^
  (if arg_needs_unwrap then
    "(local $arg_unwrap " ^ wa_arg_type ^ ")\n"
  else "") ^
  (if result_needs_wrap then
    "(local $result_unwrap " ^ wa_result_type ^ ")\n" ^
    "(local $result_wrap " ^ poly_watype ^ ")\n"
  else "") ^
  (
    let (_, itt) = List.unzip func.pf_cvars in
    let load_cvar_codes = List.folding_map itt ~init:(itype_size It_int) ~f:(fun offset ityp ->
      let next_offset = offset + (itype_size ityp) in
      let code =
        "local.get $closure\n" ^
        (itype_to_watype ityp) ^ ".load offset=" ^ (Int.to_string offset)
      in
      (next_offset, code))
    in
    String.concat ~sep:"\n" load_cvar_codes
  ) ^ "\n" ^
  (if arg_needs_unwrap then
    (codegen_unwrap iarg (Local, "$arg") (Local, "$arg_unwrap")) ^ "\n" ^
    "local.get $arg_unwrap\n"
  else
    "local.get $arg\n") ^
  "call " ^ func.pf_name ^ "\n" ^
  (if result_needs_wrap then
    "local.set $result_unwrap\n" ^
    (codegen_wrap iret (Local, "$result_unwrap") (Local, "$result_wrap")) ^ "\n" ^
    "local.get $result_wrap\n"
  else "") ^
  ")"

let codegen_ifunction (wrap_table : string_int_map) init_func (func : ifunction) =
  (if not (String.equal init_func func.pf_name) then
    (codegen_ifunction_wrapper func) ^ "\n"
   else "") ^
  (codegen_ifunction_core wrap_table func)

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
  let (wrap_table, wrap_code) = codegen_wrapper_table prog in
  let ugly_code =
    "(module\n" ^
    runtime ^ "\n" ^
    (if not (Map.Poly.is_empty wrap_table) then
      closure_call_export ^ "\n"
    else "") ^
    (codegen_types ()) ^ "\n" ^
    wrap_code ^ "\n" ^
    (codegen_globals prog.prog_globals) ^ "\n" ^
    (let (_, func_list) = List.unzip (Map.Poly.to_alist prog.prog_functions) in
    let func_codes = List.map func_list ~f:(codegen_ifunction wrap_table prog.prog_initfunc) in
    String.concat ~sep:"\n" func_codes) ^ "\n" ^
    "(start " ^ prog.prog_initfunc ^ ")\n" ^
    ")"
  in
  pretty_indent ugly_code
