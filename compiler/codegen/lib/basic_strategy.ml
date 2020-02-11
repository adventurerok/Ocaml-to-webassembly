open Core_kernel
open Otwa_transform
open Intermediate_ast
open Intermediate_program
open Wa_base


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

and codegen_box ityp unbox_var box_var =
  let box_size = itype_size ityp in
  "i32.const " ^ (Int.to_string box_size) ^ "\n" ^
  "call " ^ malloc_id ^ "\n" ^
  (codegen_setvar box_var) ^ "\n" ^
  (codegen_updatebox ityp unbox_var box_var)

and codegen_updatebox ityp unbox_var box_var =
  match ityp with
  | It_float ->
      (codegen_getvar box_var) ^ "\n" ^
      (codegen_getvar unbox_var) ^ "\n" ^
      (itype_to_watype It_float) ^ ".store offset=0"
  | It_poly ->
      (codegen_getvar box_var) ^ "\n" ^
      (codegen_getvar unbox_var) ^ "\n" ^
      poly_watype ^ ".store offset=0"
  | _ -> raise (CodegenFailure ("The type " ^ (itype_to_string ityp) ^ " cannot be boxed"))

and codegen_unbox ityp box_var unbox_var =
  let watyp = itype_to_watype ityp in
  match ityp with
  | It_float
  | It_poly ->
      (codegen_getvar box_var) ^ "\n" ^
      watyp ^ ".load offset=0\n" ^
      (codegen_setvar unbox_var) ^ "\n"
  | _ -> raise (CodegenFailure ("The type " ^ (itype_to_string ityp) ^ " cannot be unboxed"))


let codegen_ifunction_code (wrap_table : string_int_map) (func : ifunction) =
  let state = {
    wrap_table = wrap_table;
    vars = func.pf_vars
  }
  in
  let func_code = codegen_iexpr_list state func.pf_code in
  (state.vars, func_code)
