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
  "(global $mem_max (export \"mem_max\") (mut i32) (i32.const 65535))\n" ^
  "(func " ^ malloc_id ^ " (export \"malloc\") (param $size i32) (result i32)\n" ^
  "global.get $mem_idx\n" ^
  "global.get $mem_idx\n" ^
  "local.get $size\n" ^
  "i32.add\n" ^
  "global.set $mem_idx\n" ^
  "global.get $mem_idx\n" ^
  "global.get $mem_max\n" ^
  "i32.ge_u\n" ^
  "if\n" ^
  "i32.const 1\n" ^
  "memory.grow\n" ^
  "i32.const 0\n" ^
  "i32.le_s\n" ^
  "if\n" ^
  "unreachable\n" ^
  "end\n" ^
  "i32.const 65536\n" ^
  "global.get $mem_max\n" ^
  "i32.add\n" ^
  "global.set $mem_max\n" ^
  "end\n" ^
  ")"

let closure_call_export =
  "(func $call_closure (export \"call_closure\") (param $closure i32) (param $arg i32) (result i32)\n" ^
  "local.get $closure\n" ^
  "local.get $arg\n" ^
  "local.get $closure\n" ^
  "i32.load offset=0\n" ^
  "call_indirect (param i32 i32) (result i32)\n" ^
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

type state = {
  wrap_table: string_int_map;
  mutable vars: Vars.vars
}

(* Helper function for updating vars *)
let update_vars (state : state) (vars, thing) =
  state.vars <- vars;
  thing

let codegen_setvar (scope, name) =
  (iscope_to_string scope) ^ ".set " ^ name

let codegen_getvar (scope, name) =
  (iscope_to_string scope) ^ ".get " ^ name

let rec codegen_iexpr_list (state : state) lst =
  let codes = List.map lst ~f:(codegen_iexpr state) in
  String.concat ~sep:"\n" codes

and codegen_iexpr (state : state) (expr : iexpression) =
  match expr with
  | Iexp_setvar (ityp, var, str_rep) ->
      (codegen_const ityp str_rep) ^ "\n" ^
      (codegen_setvar var)
  | Iexp_copyvar(_, res, arg) ->
      (codegen_getvar arg) ^ "\n" ^
      (codegen_setvar res)
  | Iexp_return(_, arg) ->
      (codegen_getvar arg)
  | Iexp_unop (ityp, unop, res, arg) -> codegen_unop ityp unop res arg
  | Iexp_binop (ityp, binop, res, arg1, arg2) -> codegen_binop ityp binop res arg1 arg2
  | Iexp_newclosure (ift, func_name, itt, var) -> codegen_newclosure state ift func_name itt var
  | Iexp_fillclosure(itt, var, arg_lst) -> codegen_fillclosure state itt var arg_lst
  | Iexp_callclosure(_, res, clo, arg) -> codegen_callclosure res clo arg
  | Iexp_startblock (name) ->
      "block " ^ name
  | Iexp_endblock(name) ->
      "end " ^ name
  | Iexp_exitblock(name) -> "br " ^ name
  | Iexp_exitblockif(name, cond) ->
      (codegen_getvar cond) ^ "\n" ^
      "br_if " ^ name
  | Iexp_startif(name, cond) ->
      (codegen_getvar cond) ^ "\n" ^
      "if " ^ name
  | Iexp_else(name) ->
      "else " ^ name
  | Iexp_endif(name) ->
      "end " ^ name
  | Iexp_startloop(break, continue) -> codegen_startloop state break continue
  | Iexp_endloop(break, continue) -> codegen_endloop state break continue
  | Iexp_pushtuple(itt, res, args) -> codegen_pushtuple state itt res args
  | Iexp_loadtupleindex (itt, index, res, arg) -> codegen_tupleindex ~boxed:true itt index 0 res arg
  | Iexp_pushconstruct (itt, res, id, arg_vars) ->
      codegen_construct state itt res id arg_vars
  | Iexp_loadconstructindex (itt, index, res, arg) -> codegen_tupleindex ~boxed:true (It_int :: itt) (index + 1) 0 res arg
  | Iexp_loadconstructid(res, arg) -> codegen_tupleindex ~boxed:false [It_int] 0 0 res arg
  | Iexp_newbox(ityp, unbox, box) -> codegen_box ityp unbox box
  | Iexp_updatebox(ityp, unbox, box) -> codegen_updatebox ityp unbox box
  | Iexp_unbox(ityp, box, unbox) -> codegen_unbox ityp box unbox
  | Iexp_fail -> "unreachable"

and codegen_unop ityp unop res arg =
  let watyp = itype_to_watype ityp in
  (* TODO neg isn't allowed on integers *)
  let opname =
    match unop with
    | Iun_eqz -> "eqz"
    | Iun_neg -> "neg"
  in
  (codegen_getvar arg) ^ "\n" ^
  watyp ^ "." ^ opname ^ "\n" ^
  (codegen_setvar res)

and codegen_binop ityp binop res arg1 arg2 =
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
  (codegen_getvar arg1) ^ "\n" ^
  (codegen_getvar arg2) ^ "\n" ^
  watyp ^ "." ^ opname ^ "\n" ^
  (codegen_setvar res)

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

and codegen_newclosure state _ift func_name itt clo =
  let closure_tuple = It_int :: itt in
  let tup_size = ituptype_size closure_tuple in
  let func_id = Map.Poly.find_exn state.wrap_table func_name in
  "i32.const " ^ (Int.to_string tup_size) ^ "\n" ^
  "call " ^ malloc_id ^ "\n" ^
  (codegen_setvar clo) ^ "\n" ^
  (codegen_getvar clo) ^ "\n" ^
  (itype_to_watype It_int) ^ ".const " ^ (Int.to_string func_id) ^ "\n" ^
  (itype_to_watype It_int) ^ ".store offset=0"

and codegen_fillclosure state itt var var_lst =
  codegen_filltuple ~boxed:false state itt var var_lst (itype_size It_int)

and codegen_callclosure res clo arg =
  (codegen_getvar clo) ^ "\n" ^
  (codegen_getvar arg) ^ "\n" ^
  (codegen_getvar clo) ^ "\n" ^
  (itype_to_watype It_int) ^ ".load offset=0\n" ^
  "call_indirect (param i32 i32) (result i32)\n" ^
  (codegen_setvar res)

and codegen_block state name code_lst =
  let wa_lst = codegen_iexpr_list state code_lst in
  "block " ^ name ^ "\n" ^
  wa_lst ^ "\n" ^
  "end " ^ name

and codegen_ifthenelse state name cond tcode ecode_opt =
  let wa_tcode = codegen_iexpr_list state tcode in
  (codegen_getvar cond) ^ "\n" ^
  "if " ^ name ^ "\n" ^
  wa_tcode ^ "\n" ^
  (match ecode_opt with
  | Some(ecode) ->
      let wa_ecode = codegen_iexpr_list state ecode in
      "else\n" ^ wa_ecode ^ "\n"
  | None -> "") ^
  "end"

and codegen_startloop _state break continue =
  "block " ^ break ^ "\n" ^
  "loop " ^ continue

and codegen_endloop _state break continue =
  "br " ^ continue ^ "\n" ^
  "end " ^ continue ^ "\n" ^
  "end " ^ break

and codegen_pushtuple state itt res args =
  let tup_size = ituptype_size itt in
  "i32.const " ^ (Int.to_string tup_size) ^ "\n" ^
  "call " ^ malloc_id ^ "\n" ^
  (codegen_setvar res) ^ "\n" ^
  (codegen_filltuple ~boxed:true state itt res args 0)

and codegen_construct state itt res id args =
  let tup_size = ituptype_size itt + (itype_size It_int) in
  "i32.const " ^ (Int.to_string tup_size) ^ "\n" ^
  "call " ^ malloc_id ^ "\n" ^
  (codegen_setvar res) ^ "\n" ^
  (codegen_getvar res) ^ "\n" ^
  "i32.const " ^ (Int.to_string id) ^ "\n" ^
  "i32.store offset=0\n" ^
  (codegen_filltuple ~boxed:true state itt res args (itype_size It_int))


and codegen_filltuple ~boxed:boxed _state itt var arg_lst start_offset =
  let zipped_lst = List.zip_exn itt arg_lst in
  let (_, code_list_rev) = List.fold zipped_lst ~init:(start_offset, []) ~f:(fun (offset, out_lst) (it, arg) ->
    let item_wa =
      (codegen_getvar var) ^ "\n" ^
      (codegen_getvar arg) ^ "\n" ^
      (if boxed then poly_watype else (itype_to_watype it)) ^ ".store offset=" ^ (Int.to_string offset)
    in
    (offset + (if boxed then poly_size else (itype_size it)), item_wa :: out_lst)
  )
  in
  String.concat ~sep:"\n" (List.rev code_list_rev)

and codegen_tupleindex ~boxed:boxed itt index offset res arg =
  (* Only types that occur before the one we want *)
  let itt_trim = List.take itt index in
  let final_offset = List.fold itt_trim ~init:offset ~f:(fun o ityp ->
    o + (if boxed then poly_size else (itype_size ityp)))
  in
  let watyp = itype_to_watype (List.nth_exn itt index) in
  (codegen_getvar arg) ^ "\n" ^
  (if boxed then poly_watype else watyp) ^ ".load offset=" ^ (Int.to_string final_offset) ^ "\n" ^
  (codegen_setvar res)

and codegen_box ityp unbox_var (box_scope_enum, box_name) =
  let box_size = itype_size ityp in
  let box_scope = iscope_to_string box_scope_enum in
  "i32.const " ^ (Int.to_string box_size) ^ "\n" ^
  "call " ^ malloc_id ^ "\n" ^
  box_scope ^ ".set " ^ box_name ^ "\n" ^
  (codegen_updatebox ityp unbox_var (box_scope_enum, box_name))

and codegen_updatebox ityp (unbox_scope_enum, unbox_name) (box_scope_enum, box_name) =
  let unbox_scope = iscope_to_string unbox_scope_enum in
  let box_scope = iscope_to_string box_scope_enum in
  (match ityp with
  | It_float ->
      box_scope ^ ".get " ^ box_name ^ "\n" ^
      unbox_scope ^ ".get " ^ unbox_name ^ "\n" ^
      (itype_to_watype It_float) ^ ".store offset=0"
  | It_poly ->
      box_scope ^ ".get " ^ box_name ^ "\n" ^
      unbox_scope ^ ".get " ^ unbox_name ^ "\n" ^
      poly_watype ^ ".store offset=0"
  | _ -> raise (CodegenFailure ("The type " ^ (itype_to_string ityp) ^ " cannot be boxed")))

and codegen_unbox ityp (box_scope_enum, box_name) (unbox_scope_enum, unbox_name) =
  let unbox_scope = iscope_to_string unbox_scope_enum in
  let box_scope = iscope_to_string box_scope_enum in
  let watyp = itype_to_watype ityp in
  match ityp with
  | It_float
  | It_poly ->
      box_scope ^ ".get " ^ box_name ^ "\n" ^
      watyp ^ ".load offset=0\n" ^
      unbox_scope ^ ".set " ^ unbox_name
  | _ -> raise (CodegenFailure ("The type " ^ (itype_to_string ityp) ^ " cannot be unboxed"))


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
  let state = {
    wrap_table = wrap_table;
    vars = func.pf_vars
  }
  in
  let func_code = codegen_iexpr_list state func.pf_code in
  let cvar_count = List.length func.pf_cvars in
  let export =
    match func.pf_export_name with
    | Some(export_name) -> " (export \"" ^ export_name ^ "\")"
    | None -> ""
  in
  "(func " ^ func.pf_name ^ export ^ "\n"
  ^ (codegen_local_vars state.vars ret_typ cvar_count) ^ "\n"
  ^ func_code ^ "\n"
  ^ ")"

(* Wrapper function takes two arguments: closure and function argument *)
let codegen_ifunction_wrapper (func : ifunction) =
  let wrapper_name = wrapper_func_name func.pf_name in
  let (iarg, iret) = func.pf_type in
  let wa_arg_type = itype_to_watype iarg in
  let wa_result_type = itype_to_watype iret in
  let arg_needs_unbox = itype_needs_box iarg in
  let result_needs_box = itype_needs_box iret in
  "(func " ^ wrapper_name ^ "\n" ^
  "(param $closure " ^ (itype_to_watype It_pointer) ^ ")\n" ^
  "(param $arg " ^ poly_watype ^ ")\n" ^
  "(result " ^ poly_watype ^ ")\n" ^
  (if arg_needs_unbox then
    "(local $arg_unbox " ^ wa_arg_type ^ ")\n"
  else "") ^
  (if result_needs_box then
    "(local $result_unbox " ^ wa_result_type ^ ")\n" ^
    "(local $result_box " ^ poly_watype ^ ")\n"
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
  (if arg_needs_unbox then
    (codegen_unbox iarg (Local, "$arg") (Local, "$arg_unbox")) ^ "\n" ^
    "local.get $arg_unbox\n"
  else
    "local.get $arg\n") ^
  "call " ^ func.pf_name ^ "\n" ^
  (if result_needs_box then
    "local.set $result_unbox\n" ^
    (codegen_box iret (Local, "$result_unbox") (Local, "$result_box")) ^ "\n" ^
    "local.get $result_box\n"
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
    wrap_code ^ "\n" ^
    (codegen_globals prog.prog_globals) ^ "\n" ^
    (let (_, func_list) = List.unzip (Map.Poly.to_alist prog.prog_functions) in
    let func_codes = List.map func_list ~f:(codegen_ifunction wrap_table prog.prog_initfunc) in
    String.concat ~sep:"\n" func_codes) ^ "\n" ^
    "(start " ^ prog.prog_initfunc ^ ")\n" ^
    ")"
  in
  pretty_indent ugly_code
