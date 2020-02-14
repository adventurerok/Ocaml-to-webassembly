open Core_kernel
open Otwa_transform
open Intermediate_ast
open Intermediate_program
open Wa_base
(* open Basic_strategy *)
open Stack_strategy

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

let codegen_ifunction_core (wrap_table : string_int_map) (globals : Vars.vars) (func : ifunction) =
  let (_, ret_typ) = func.pf_type in
  let (vars1, func_code) = codegen_ifunction_code wrap_table globals func in
  let cvar_count = List.length func.pf_cvars in
  let export =
    match func.pf_export_name with
    | Some(export_name) -> " (export \"" ^ export_name ^ "\")"
    | None -> ""
  in
  "(func " ^ func.pf_name ^ export ^ "\n"
  ^ (codegen_local_vars vars1 ret_typ cvar_count) ^ "\n"
  ^ func_code ^ "\n"
  ^ ")"

(* Wrapper function takes two arguments: closure and function argument *)
let codegen_ifunction_wrapper (func : ifunction) =
  let wrapper_name = wrapper_func_name func.pf_name in
  let (iarg, iret) = func.pf_type in
  let wa_result_type = itype_to_watype iret in
  let arg_needs_unbox = itype_needs_box iarg in
  let result_needs_box = itype_needs_box iret in
  let declaration =
    "(func " ^ wrapper_name ^ "\n" ^
    "(param $closure " ^ (itype_to_watype It_pointer) ^ ")\n" ^
    "(param $arg " ^ poly_watype ^ ")\n" ^
    "(result " ^ poly_watype ^ ")\n" ^
    (if result_needs_box then
      "(local $result_box " ^ poly_watype ^ ")\n"
    else "")
  in
  let get_cvars =
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
      String.concat ~sep:"\n" load_cvar_codes)
  in
  let load_arg =
    (if arg_needs_unbox then
      (* (codegen_unbox iarg (Local, "$arg") (Local, "$arg_unbox")) ^ "\n" ^
      "local.get $arg_unbox\n" *)
      "local.get $arg\n" ^
      (itype_to_watype iarg) ^ ".load offset=0\n"
    else
      "local.get $arg\n")
  in
  let invoke_function =
    get_cvars ^ "\n" ^
    load_arg ^
    "call " ^ func.pf_name ^ "\n"
  in
  declaration ^
  (if result_needs_box then
    "i32.const " ^ (Int.to_string (itype_size iret)) ^ "\n" ^
    "call " ^ malloc_id ^ "\n" ^
    "local.tee $result_box\n" ^
    invoke_function ^
    wa_result_type ^ ".store offset=0\n" ^
    "local.get $result_box"
  else
    invoke_function
  ) ^
  ")"

let codegen_ifunction (wrap_table : string_int_map) globals init_func (func : ifunction) =
  (if not (String.equal init_func func.pf_name) then
    (codegen_ifunction_wrapper func) ^ "\n"
   else "") ^
  (codegen_ifunction_core wrap_table globals func)

let pretty_indent str =
  let lines = String.split_lines str in
  let no_empty = List.filter lines ~f:(fun s -> not (String.is_empty s)) in
  let fixed_lines = List.folding_map no_empty ~init:0 ~f:(fun indent line ->
    let lbracket_count = String.count line ~f:(fun c -> Char.equal c '(') in
    let rbracket_count = String.count line ~f:(fun c -> Char.equal c ')') in
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
    let func_codes = List.map func_list ~f:(codegen_ifunction wrap_table prog.prog_globals prog.prog_initfunc) in
    String.concat ~sep:"\n" func_codes) ^ "\n" ^
    "(start " ^ prog.prog_initfunc ^ ")\n" ^
    ")"
  in
  pretty_indent ugly_code
