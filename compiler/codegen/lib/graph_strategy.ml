open Core_kernel
open Otwa_transform
open Intermediate_ast
open Intermediate_program
open Wa_base

type state = {
  wrap_table: string_int_map;
  vars: Vars.vars
}

type load_variable_dest =
  |  Lv_stack of ivariable
  |  Lv_var of ivariable

let concat_lines lst =
  (String.concat ~sep:"\n" lst)

(* Order to load variables, and whether to ensure var is ready, or put them on the stack *)
let load_variable_order (iexpr : iexpression) =
  let lv_stack_list lst = List.map ~f:(fun a -> Lv_stack(a)) lst in
  match iexpr with
  | Iexp_setvar (_, _, _) -> []
  | Iexp_copyvar (_, _, arg) -> [Lv_stack(arg)]
  | Iexp_return (_, arg) -> [Lv_stack(arg)]
  | Iexp_unop (_, _, _, arg) -> [Lv_stack(arg)]
  | Iexp_binop (_, _, _, arg1, arg2) -> [Lv_stack(arg1); Lv_stack(arg2)]
  | Iexp_newclosure (_, _, _, _) -> []
  | Iexp_fillclosure (_, clo, arg_lst) -> (Lv_var(clo)) :: (lv_stack_list arg_lst)
  | Iexp_callclosure (_, _, clo, arg) -> [Lv_var(clo); Lv_stack(arg)]
  | Iexp_startblock _ -> []
  | Iexp_endblock _ -> []
  | Iexp_exitblock _ -> []
  | Iexp_exitblockif (_, cond) -> [Lv_stack(cond)]
  | Iexp_startif (_, cond) -> [Lv_stack(cond)]
  | Iexp_else _ -> []
  | Iexp_endif _ -> []
  | Iexp_startloop (_, _) -> []
  | Iexp_endloop (_, _) -> []
  | Iexp_pushtuple (_, _, args) -> lv_stack_list args
  | Iexp_loadtupleindex (_, _, _, arg) -> [Lv_stack(arg)]
  | Iexp_pushconstruct (_, _, _, args) -> lv_stack_list args
  | Iexp_loadconstructindex (_, _, _, arg) -> [Lv_stack(arg)]
  | Iexp_loadconstructid (_, arg) -> [Lv_stack(arg)]
  | Iexp_newbox (_, arg, _) -> [Lv_stack(arg)]
  | Iexp_updatebox (_, arg, box) -> [Lv_stack(box); Lv_stack(arg)]
  | Iexp_unbox (_, box, _) -> [Lv_stack(box)]
  | Iexp_fail -> []


let variable_result (iexpr : iexpression) =
  match iexpr with
  | Iexp_setvar (_, res, _) -> Some(Lv_stack(res))
  | Iexp_copyvar (_, res, _) -> Some(Lv_stack(res))
  | Iexp_return (_, _) -> None
  | Iexp_unop (_, _, res, _) -> Some(Lv_stack(res))
  | Iexp_binop (_, _, res, _, _) -> Some(Lv_stack(res))
  | Iexp_newclosure (_, _, _, res) -> Some(Lv_var(res))
  | Iexp_fillclosure (_, res, _) -> Some(Lv_var(res))
  | Iexp_callclosure (_, res, _, _) -> Some(Lv_stack(res))
  | Iexp_startblock _ -> None
  | Iexp_endblock _ -> None
  | Iexp_exitblock _ -> None
  | Iexp_exitblockif (_, _) -> None
  | Iexp_startif (_, _) -> None
  | Iexp_else _ -> None
  | Iexp_endif _ -> None
  | Iexp_startloop (_, _) -> None
  | Iexp_endloop (_, _) -> None
  | Iexp_pushtuple (_, res, _) -> Some(Lv_var(res))
  | Iexp_loadtupleindex (_, _, res, _) -> Some(Lv_stack(res))
  | Iexp_pushconstruct (_, res, _, _) -> Some(Lv_var(res))
  | Iexp_loadconstructindex (_, _, res, _) -> Some(Lv_stack(res))
  | Iexp_loadconstructid (res, _) -> Some(Lv_stack(res))
  | Iexp_newbox (_, _, box) -> Some(Lv_var(box))
  | Iexp_updatebox (_, _, box) -> Some(Lv_var(box))
  | Iexp_unbox (_, _, unbox) -> Some(Lv_stack(unbox))
  | Iexp_fail -> None

let codegen_setvar _state (scope, name) =
  (iscope_to_string scope) ^ ".set " ^ name

let codegen_getvar _state (scope, name) =
  (iscope_to_string scope) ^ ".get " ^ name

let codegen_teevar state (scope, name) =
  match scope with
  | Global ->
      (codegen_setvar state (scope, name)) ^ "\n" ^
      (codegen_getvar state (scope, name))
  | Local ->
      (iscope_to_string scope) ^ ".tee " ^ name

let rec codegen_iexpression_core (state : state) lvo (expr : iexpression) =
  (* If vout is Lv_stack, then that is top of the stack *)
  (* If vout is Lv_var, the var was saved but it isn't top of stack *)
  (* If vout is None, no variable *)
  match expr with
  | Iexp_setvar (ityp, _, str_rep) ->
      (concat_lines lvo) ^ "\n" ^
      (codegen_const ityp str_rep) ^ "\n"
  | Iexp_copyvar(_, _, _) ->
      (concat_lines lvo) ^ "\n"
  | Iexp_return(_, _) ->
      (concat_lines lvo) ^ "\n"
  | Iexp_unop (ityp, unop, _, _) ->
      (concat_lines lvo) ^ "\n" ^
      (codegen_unop ityp unop)
  | Iexp_binop (ityp, binop, _, _, _) ->
      (concat_lines lvo) ^ "\n" ^
      (codegen_binop ityp binop)
  | Iexp_newclosure (ift, func_name, itt, var) -> codegen_newclosure state ift func_name itt var
  | Iexp_fillclosure(itt, var, _) -> codegen_fillclosure state lvo itt var
  | Iexp_callclosure(_, _, clo, _) -> codegen_callclosure state lvo clo
  | Iexp_startblock (name) ->
      "block " ^ name ^ "\n"
  | Iexp_endblock(name) ->
      "end " ^ name ^ "\n"
  | Iexp_exitblock(name) -> "br " ^ name ^ "\n"
  | Iexp_exitblockif(name, _) ->
      let get_arg =
        match lvo with
        | [ga] -> ga
        | _ -> raise (CodegenFailure "LVO Mismatch")
      in
      get_arg ^ "\n" ^
      "br_if " ^ name ^ "\n"
  | Iexp_startif(name, _) ->
      let get_arg =
        match lvo with
        | [ga] -> ga
        | _ -> raise (CodegenFailure "LVO Mismatch")
      in
      get_arg ^ "\n" ^
      "if " ^ name ^ "\n"
  | Iexp_else(name) ->
      "else " ^ name ^ "\n"
  | Iexp_endif(name) ->
      "end " ^ name ^ "\n"
  | Iexp_startloop(break, continue) ->
      "block " ^ break ^ "\n" ^
      "loop " ^ continue ^ "\n"
  | Iexp_endloop(break, continue) ->
      "br " ^ continue ^ "\n" ^
      "end " ^ continue ^ "\n" ^
      "end " ^ break
  | Iexp_pushtuple(itt, res, _) -> codegen_pushtuple state lvo itt res
  | Iexp_loadtupleindex (itt, index, _, _) -> codegen_tupleindex ~boxed:true state lvo itt index 0
  | Iexp_pushconstruct (itt, res, id, _) ->
      codegen_construct state lvo itt res id
  | Iexp_loadconstructindex (itt, index, _, _) ->
      codegen_tupleindex ~boxed:true state lvo (It_int :: itt) (index + 1) 0
  | Iexp_loadconstructid(_, _) -> codegen_tupleindex ~boxed:false state lvo [It_int] 0 0
  | Iexp_newbox(ityp, _, box) -> codegen_box state lvo ityp box
  | Iexp_updatebox(ityp, _, _) -> codegen_updatebox state lvo ityp
  | Iexp_unbox(ityp, _, _) -> codegen_unbox state lvo ityp
  | Iexp_fail -> "unreachable"

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

and codegen_unop ityp unop =
  let watyp = itype_to_watype ityp in
  (* TODO neg isn't allowed on integers *)
  let opname =
    match unop with
    | Iun_eqz -> "eqz"
    | Iun_neg -> "neg"
  in
  watyp ^ "." ^ opname ^ "\n"

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
  watyp ^ "." ^ opname ^ "\n"

and codegen_newclosure state _ift func_name itt clo =
  let closure_tuple = It_int :: itt in
  let tup_size = ituptype_size closure_tuple in
  let func_id = Map.Poly.find_exn state.wrap_table func_name in
  "i32.const " ^ (Int.to_string tup_size) ^ "\n" ^
  "call " ^ malloc_id ^ "\n" ^
  (codegen_setvar state clo) ^ "\n" ^
  (codegen_getvar state clo) ^ "\n" ^
  (itype_to_watype It_int) ^ ".const " ^ (Int.to_string func_id) ^ "\n" ^
  (itype_to_watype It_int) ^ ".store offset=0"


and codegen_fillclosure state lvo itt var =
  let gen_var_code = List.hd_exn lvo in
  let fill_lvo = List.tl_exn lvo in
  let fill_code = codegen_filltuple ~boxed:false state itt var fill_lvo (itype_size It_int) in
  gen_var_code ^ "\n" ^
  fill_code ^ "\n"

and codegen_callclosure state lvo clo =
  let (load_clo, load_arg) =
    match lvo with
    | [lc; la] -> (lc, la)
    | _ -> raise (CodegenFailure "Incorrect LVO arguments")
  in
  load_clo ^ "\n" ^
  (codegen_getvar state clo) ^ "\n" ^
  load_arg ^ "\n" ^
  (codegen_getvar state clo) ^ "\n" ^
  (itype_to_watype It_int) ^ ".load offset=0\n" ^
  "call_indirect (param i32 i32) (result i32)\n"


and codegen_pushtuple state lvo itt res =
  let tup_size = ituptype_size itt in
  "i32.const " ^ (Int.to_string tup_size) ^ "\n" ^
  "call " ^ malloc_id ^ "\n" ^
  (codegen_setvar state res) ^ "\n" ^
  (codegen_filltuple ~boxed:true state itt res lvo 0)


and codegen_construct state lvo itt res id =
  let tup_size = ituptype_size itt + (itype_size It_int) in
  "i32.const " ^ (Int.to_string tup_size) ^ "\n" ^
  "call " ^ malloc_id ^ "\n" ^
  (codegen_teevar state res) ^ "\n" ^
  "i32.const " ^ (Int.to_string id) ^ "\n" ^
  "i32.store offset=0\n" ^
  (codegen_filltuple ~boxed:true state itt res lvo (itype_size It_int))


and codegen_tupleindex ~boxed:boxed _state lvo itt index offset =
  let get_arg =
    match lvo with
    | [ga] -> ga
    | _ -> raise (CodegenFailure "Mismatched LVO")
  in
  (* Only types that occur before the one we want *)
  let itt_trim = List.take itt index in
  let final_offset = List.fold itt_trim ~init:offset ~f:(fun o ityp ->
    o + (if boxed then poly_size else (itype_size ityp)))
  in
  let watyp = itype_to_watype (List.nth_exn itt index) in
  get_arg ^ "\n" ^
  (if boxed then poly_watype else watyp) ^ ".load offset=" ^ (Int.to_string final_offset) ^ "\n"


and codegen_filltuple ~boxed:boxed state itt var lvo start_offset =
  let zipped_lst = List.zip_exn itt lvo in
  let (_, code_list_rev) = List.fold zipped_lst ~init:(start_offset, [])
                             ~f:(fun (offset, out_lst) (it, lv_arg) ->
    let item_wa =
      (codegen_getvar state var) ^ "\n" ^
      (lv_arg) ^ "\n" ^
      (if boxed then poly_watype else (itype_to_watype it)) ^ ".store offset=" ^ (Int.to_string offset)
    in
    (offset + (if boxed then poly_size else (itype_size it)), item_wa :: out_lst)
  )
  in
  String.concat ~sep:"\n" (List.rev code_list_rev)


and codegen_box state lvo ityp box_var =
  let get_arg =
    match lvo with
    | [ga] -> ga
    | _ -> raise (CodegenFailure "LVO Mismatch")
  in
  let box_size = itype_size ityp in
  "i32.const " ^ (Int.to_string box_size) ^ "\n" ^
  "call " ^ malloc_id ^ "\n" ^
  (codegen_teevar state box_var) ^ "\n" ^
  get_arg ^ "\n" ^
  (itype_to_watype ityp) ^ ".store offset=0\n"

and codegen_updatebox _state lvo ityp =
  let (get_box, get_arg) =
    match lvo with
    | [gb; ga] -> (gb, ga)
    | _ -> raise (CodegenFailure "LVO Mismatch")
  in
  get_box ^ "\n" ^
  get_arg ^ "\n" ^
  (itype_to_watype ityp) ^ ".store offset=0\n"

and codegen_unbox _state lvo ityp =
  let get_arg =
    match lvo with
    | [ga] -> ga
    | _ -> raise (CodegenFailure "LVO Mismatch")
  in
  let watyp = itype_to_watype ityp in
  get_arg ^ "\n" ^
  watyp ^ ".load offset=0\n"


let codegen_iexpression_simple state iexpr =
  let lvo_req = load_variable_order iexpr in
  let lvo = List.map lvo_req ~f:(fun req ->
    match req with
    | Lv_var(_) -> ""
    | Lv_stack(var) -> codegen_getvar state var)
  in
  let main_code = codegen_iexpression_core state lvo iexpr in
  let expected_output = variable_result iexpr in
  match expected_output with
  | Some(Lv_stack(var)) ->
      main_code ^
      (codegen_setvar state var)
  | _ -> main_code

let codegen_basic_block state _fa (bb : Analysis.basic_block) =
  let lines = Array.to_list bb.bb_code in
  let line_codes = List.map ~f:(codegen_iexpression_simple state) lines in
  String.concat ~sep:"\n" line_codes

let codegen_ifunction_code wrap_table func =
  let fa = Analysis.analyse_function func in
  let state = {
    wrap_table = wrap_table;
    vars = func.pf_vars
  }
  in
  let unmapped = Map.Poly.data fa.fa_basic_blocks in
  let bb_codes = List.map ~f:(codegen_basic_block state fa) unmapped in
  let full_code = String.concat ~sep:"\n" bb_codes in
  (state.vars, full_code)
