open Core_kernel
open Otwa_base
open Otwa_transform
open Intermediate_ast
open Intermediate_program
open Wa_base

type state = {
  wrap_table: string_int_map;
  mutable vars: Vars.vars;
  fa: Analysis.func_analysis;
  mutable used_vars: (ivariable, IVariable.comparator_witness) Set.t;
}

type load_variable_dest =
  |  Lv_stack of ivariable
  |  Lv_var of ivariable

let lvd_var lvd =
  match lvd with
  | Lv_stack(v) -> v
  | Lv_var(v) -> v

let concat_lines lst =
  (String.concat ~sep:"\n" lst)

(* Order to load variables, and whether to ensure var is ready, or put them on the stack *)
let load_variable_order (iins : iinstruction) =
  let lv_stack_list lst = List.map ~f:(fun a -> Lv_stack(a)) lst in
  match iins with
  | Iins_setvar (_, _, _) -> []
  | Iins_copyvar (_, _, arg) -> [Lv_stack(arg)]
  | Iins_return (_, arg) -> [Lv_stack(arg)]
  | Iins_unop (_, _, _, arg) -> [Lv_stack(arg)]
  | Iins_binop (_, _, _, arg1, arg2) -> [Lv_stack(arg1); Lv_stack(arg2)]
  | Iins_newclosure (_, _, _, _) -> []
  | Iins_fillclosure (_, clo, arg_lst) -> (Lv_var(clo)) :: (lv_stack_list arg_lst)
  | Iins_callclosure (_, _, clo, arg) -> [Lv_stack(clo); Lv_stack(arg)]
  | Iins_calldirect(_, _, _, arg_lst) -> (lv_stack_list arg_lst)
  | Iins_startblock _ -> []
  | Iins_endblock _ -> []
  | Iins_exitblock _ -> []
  | Iins_exitblockif (_, cond) -> [Lv_stack(cond)]
  | Iins_startif (_, cond) -> [Lv_stack(cond)]
  | Iins_else _ -> []
  | Iins_endif _ -> []
  | Iins_startloop (_, _) -> []
  | Iins_endloop (_, _) -> []
  | Iins_pushtuple (_, _, args) -> lv_stack_list args
  | Iins_loadtupleindex (_, _, _, arg) -> [Lv_stack(arg)]
  | Iins_pushconstruct (_, _, _, args) -> lv_stack_list args
  | Iins_loadconstructindex (_, _, _, arg) -> [Lv_stack(arg)]
  | Iins_loadconstructid (_, arg) -> [Lv_stack(arg)]
  | Iins_newbox (_, arg, _) -> [Lv_stack(arg)]
  | Iins_updatebox (_, arg, box) -> [Lv_stack(box); Lv_stack(arg)]
  | Iins_unbox (_, box, _) -> [Lv_stack(box)]
  | Iins_fail -> []


let variable_result (iins : iinstruction) =
  match iins with
  | Iins_setvar (_, res, _) -> Some(Lv_stack(res))
  | Iins_copyvar (_, res, _) -> Some(Lv_stack(res))
  | Iins_return (_, _) -> None
  | Iins_unop (_, _, res, _) -> Some(Lv_stack(res))
  | Iins_binop (_, _, res, _, _) -> Some(Lv_stack(res))
  | Iins_newclosure (_, _, _, res) -> Some(Lv_var(res))
  | Iins_fillclosure (_, res, _) -> Some(Lv_var(res))
  | Iins_callclosure (_, res, _, _) -> Some(Lv_stack(res))
  | Iins_calldirect (res, _, _, _) -> Some(Lv_stack(res))
  | Iins_startblock _ -> None
  | Iins_endblock _ -> None
  | Iins_exitblock _ -> None
  | Iins_exitblockif (_, _) -> None
  | Iins_startif (_, _) -> None
  | Iins_else _ -> None
  | Iins_endif _ -> None
  | Iins_startloop (_, _) -> None
  | Iins_endloop (_, _) -> None
  | Iins_pushtuple (_, res, _) -> Some(Lv_var(res))
  | Iins_loadtupleindex (_, _, res, _) -> Some(Lv_stack(res))
  | Iins_pushconstruct (_, res, _, _) -> Some(Lv_var(res))
  | Iins_loadconstructindex (_, _, res, _) -> Some(Lv_stack(res))
  | Iins_loadconstructid (res, _) -> Some(Lv_stack(res))
  | Iins_newbox (_, _, box) -> Some(Lv_var(box))
  | Iins_updatebox (_, _, box) -> Some(Lv_var(box))
  | Iins_unbox (_, _, unbox) -> Some(Lv_stack(unbox))
  | Iins_fail -> None

let needs_clear_stack (iins : iinstruction) =
  match iins with
  | Iins_startblock _ -> true
  | Iins_endblock _ -> true
  | Iins_startif _ -> true
  | Iins_endif _ -> true
  | Iins_else _ -> true
  | Iins_startloop _ -> true
  | Iins_endloop _ -> true
  | _ -> false

let codegen_setvar state (scope, name) =
  state.used_vars <- Set.add state.used_vars (scope, name);
  (iscope_to_string scope) ^ ".set " ^ name

let codegen_getvar state (scope, name) =
  state.used_vars <- Set.add state.used_vars (scope, name);
  (iscope_to_string scope) ^ ".get " ^ name

let codegen_teevar state (scope, name) =
  state.used_vars <- Set.add state.used_vars (scope, name);
  match scope with
  | Global ->
      (codegen_setvar state (scope, name)) ^ "\n" ^
      (codegen_getvar state (scope, name))
  | Local ->
      (iscope_to_string scope) ^ ".tee " ^ name

let rec codegen_iinstruction_core (state : state) saved_vars lvo (expr : iinstruction) =
  (* If vout is Lv_stack, then that is top of the stack *)
  (* If vout is Lv_var, the var was saved but it isn't top of stack *)
  (* If vout is None, no variable *)
  match expr with
  | Iins_setvar (ityp, _, str_rep) ->
      (concat_lines lvo) ^ "\n" ^
      (codegen_const ityp str_rep) ^ "\n"
  | Iins_copyvar(_, _, _) ->
      (concat_lines lvo) ^ "\n"
  | Iins_return(_, _) ->
      (concat_lines lvo) ^ "\n"
  | Iins_unop (ityp, unop, _, _) ->
      (concat_lines lvo) ^ "\n" ^
      (codegen_unop ityp unop)
  | Iins_binop (ityp, binop, _, _, _) ->
      (concat_lines lvo) ^ "\n" ^
      (codegen_binop ityp binop)
  | Iins_newclosure (ift, func_name, itt, var) -> codegen_newclosure state ift func_name itt var
  | Iins_fillclosure(itt, var, _) -> codegen_fillclosure state lvo itt var
  | Iins_callclosure(_, _, clo, _) -> codegen_callclosure state saved_vars lvo clo
  | Iins_calldirect(_, name, _, _) -> codegen_calldirect state name lvo
  | Iins_startblock (name) ->
      "block " ^ name ^ "\n"
  | Iins_endblock(name) ->
      "end " ^ name ^ "\n"
  | Iins_exitblock(name) -> "br " ^ name ^ "\n"
  | Iins_exitblockif(name, _) ->
      let get_arg =
        match lvo with
        | [ga] -> ga
        | _ -> raise (CodegenFailure "LVO Mismatch")
      in
      get_arg ^ "\n" ^
      "br_if " ^ name ^ "\n"
  | Iins_startif(name, _) ->
      let get_arg =
        match lvo with
        | [ga] -> ga
        | _ -> raise (CodegenFailure "LVO Mismatch")
      in
      get_arg ^ "\n" ^
      "if " ^ name ^ "\n"
  | Iins_else(name) ->
      "else " ^ name ^ "\n"
  | Iins_endif(name) ->
      "end " ^ name ^ "\n"
  | Iins_startloop(break, continue) ->
      "block " ^ break ^ "\n" ^
      "loop " ^ continue ^ "\n"
  | Iins_endloop(break, continue) ->
      "br " ^ continue ^ "\n" ^
      "end " ^ continue ^ "\n" ^
      "end " ^ break
  | Iins_pushtuple(itt, res, _) -> codegen_pushtuple state lvo itt res
  | Iins_loadtupleindex (itt, index, _, _) -> codegen_tupleindex ~boxed:true state lvo itt index 0
  | Iins_pushconstruct (itt, res, id, _) ->
      codegen_construct state lvo itt res id
  | Iins_loadconstructindex (itt, index, _, _) ->
      codegen_tupleindex ~boxed:true state lvo (It_int :: itt) (index + 1) 0
  | Iins_loadconstructid(_, _) -> codegen_tupleindex ~boxed:true state lvo [It_int] 0 0
  | Iins_newbox(ityp, _, box) -> codegen_box state lvo ityp box
  | Iins_updatebox(ityp, _, _) -> codegen_updatebox state lvo ityp
  | Iins_unbox(ityp, _, _) -> codegen_unbox state lvo ityp
  | Iins_fail -> "unreachable"

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
    | It_poly -> "_s"
    | It_int -> "_s"
    | It_bool -> "_s"
    | It_unit -> "_s"
    | It_float -> ""
    | _ -> raise (CodegenFailure ("Can't do binop on " ^ (itype_to_string ityp)))
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
  (codegen_teevar state clo) ^ "\n" ^
  (itype_to_watype It_int) ^ ".const " ^ (Int.to_string func_id) ^ "\n" ^
  (itype_to_watype It_int) ^ ".store offset=0"


and codegen_fillclosure state lvo itt var =
  let gen_var_code = List.hd_exn lvo in
  let fill_lvo = List.tl_exn lvo in
  let fill_code = codegen_filltuple ~boxed:false state itt var fill_lvo (itype_size It_int) in
  gen_var_code ^ "\n" ^
  fill_code ^ "\n"

and codegen_callclosure state saved_vars lvo clo =
  let (load_clo, load_arg) =
    match lvo with
    | [lc; la] -> (lc, la)
    | _ -> raise (CodegenFailure "Incorrect LVO arguments")
  in
  load_clo ^ "\n" ^
  (if Set.mem saved_vars clo then
    ""
  else
    (codegen_teevar state clo) ^ "\n") ^
  load_arg ^ "\n" ^
  (codegen_getvar state clo) ^ "\n" ^
  (itype_to_watype It_int) ^ ".load offset=0\n" ^
  "call_indirect (param i32 i32) (result i32)\n"

and codegen_calldirect _state name lvo =
  let load_args = String.concat ~sep:"\n" lvo in
  load_args ^ "\n" ^
  "call " ^ name ^ "\n"

and codegen_pushtuple state lvo itt res =
  let tup_size = ituptype_size itt in
  "i32.const " ^ (Int.to_string tup_size) ^ "\n" ^
  "call " ^ malloc_id ^ "\n" ^
  (if tup_size = 0 then
    (codegen_setvar state res) ^ "\n"
  else
  (codegen_teevar state res) ^ "\n" ^
  (codegen_filltuple ~boxed:true ~teed:true state itt res lvo 0))


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


and codegen_filltuple ~boxed:boxed ?teed:(teed = false) state itt var lvo start_offset =
  let zipped_lst = List.zip_exn itt lvo in
  let (_, code_list_rev) = List.foldi zipped_lst ~init:(start_offset, [])
                             ~f:(fun index (offset, out_lst) (it, lv_arg) ->
    let get_or_teed =
      if teed && (index = 0) then
        ""
      else
        (codegen_getvar state var) ^ "\n"
    in
    let item_wa =
      get_or_teed ^
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


let codegen_iinstruction_simple state iins =
  let lvo_req = load_variable_order iins in
  let lvo = List.map lvo_req ~f:(fun req ->
    match req with
    | Lv_var(_) -> ""
    | Lv_stack(var) -> codegen_getvar state var)
  in
  let main_code = codegen_iinstruction_core state (Set.empty (module IVariable)) lvo iins in
  let expected_output = variable_result iins in
  match expected_output with
  | Some(Lv_stack(var)) ->
      main_code ^
      (codegen_setvar state var)
  | _ -> main_code


(* Make stack wanted an option, or make it a list *)

type gen_block = {
  start_line: int;
  code: string;
  out_stack: ivariable option;
  assigned: (ivariable, IVariable.comparator_witness) Set.t;
  teed: bool
}

let gen_block_to_string gb =
  "{ gen_block " ^ "\n" ^
  "start_line = " ^ (Int.to_string gb.start_line) ^ "\n" ^
  "code = \n" ^ gb.code ^ "\n" ^
  "out_stack = " ^ (Option.value ~default: "NA" (Option.map ~f:ivariable_to_string gb.out_stack)) ^ "\n" ^
  "assigned = " ^
  (String.concat ~sep:" " (List.map ~f:ivariable_to_string (Set.to_list gb.assigned))) ^ "\n" ^
  "teed = " ^ (Bool.to_string gb.teed) ^ "\n } \n"

let print_state msg gb_stack stack_avail saved_vars =
  Stdio.print_endline msg;
  Stdio.print_endline (String.concat ~sep:"\n" (List.map gb_stack ~f:gen_block_to_string));
  Stdio.print_endline "Avail on stack:";
  Stdio.print_endline (String.concat ~sep:" " (List.map (Set.to_list stack_avail) ~f:ivariable_to_string));
  Stdio.print_endline "\nSaved vars:";
  Stdio.print_endline (String.concat ~sep:" " (List.map (Set.to_list saved_vars) ~f:ivariable_to_string))

(* Chance a gen block so it writes to it's var instead of putting the result on top of the stack *)
let unstack_gen_block state gb saved_vars =
  match gb.out_stack with
  | Some(var) ->
      let end_code =
        codegen_setvar state var
      in
      ({
        gb with
        code = gb.code ^ "\n" ^ end_code ^ "\n";
        assigned = Set.add gb.assigned var;
        out_stack = None;
      }, Set.add saved_vars var)
  | None -> (gb, saved_vars)

(* Find a stack entry that will generate the variable we want, removing unwanted entries along the way
 * by having their results be saved to their variable.
 * target_var = var we want
 * gen_stack = the stack
 * stack_avail = variables known to be available on the stack
 * saved_vars = variables known to be saved
 * no_bypass = variables that we cannot go past writes to *)
let rec unwind_gen_stack state target_var gen_stack stack_avail saved_vars no_bypass =
  match gen_stack with
  | [] -> raise (CodegenFailure ("Var not on gen stack: " ^ ivariable_to_string target_var))
  | (gb :: gen_stack') ->
      (* Check top gen stack entry doesn't write to a variable in no_bypass *)
      if Option.is_some (Set.find (Map.key_set no_bypass) ~f:(Set.mem gb.assigned)) then
        None
      else
        (match gb.out_stack with
        (* Top gen stack entry puts other var on top of stack *)
        | Some(other_var) ->
            let stack_avail' = Set.remove stack_avail other_var in
            (* Check this var also isn't in no_bypass *)
            if Map.mem no_bypass other_var then
              None
            else if equal_ivariable other_var target_var then
              (* We found our var *)
              let save_needed =
                gb.teed || (match target_var with
                | (Global, _) -> true
                | (Local, _) ->
                    (* If the variable is used more than once, assume we should tee it *)
                    let vs = Hashtbl.find_exn state.fa.fa_var_stats target_var in
                    vs.vs_use_count > 1
                )
              in
              let tee_extra =
                if save_needed then
                  "\n" ^ (codegen_teevar state other_var)
                else ""
              in
              Some((gb.start_line, [gb.code ^ tee_extra], gb.assigned, gen_stack', stack_avail', saved_vars))
            else
              (* Not our var, so this gen block needs to write it's result to the var
               * instead of keeping it on top of the stack *)
              let (gb', saved_vars') = unstack_gen_block state gb saved_vars in
              let deeper_option =
                unwind_gen_stack state target_var gen_stack' stack_avail' saved_vars' no_bypass
              in
              (match deeper_option with
              | Some ((start_line, c_lst, assigned_vars1, out_gen_stack, out_stack_avail, saved_vars2)) ->
                  let assigned_vars2 = Set.union assigned_vars1 gb'.assigned in
                  Some((start_line, gb'.code :: c_lst, assigned_vars2, out_gen_stack, out_stack_avail, saved_vars2))
              | None -> None)
        (* Top gen stack entry doesn't put a var on top of stack *)
        | None ->
            let deeper_option =
              unwind_gen_stack state target_var gen_stack' stack_avail saved_vars no_bypass
            in
            (match deeper_option with
            | Some ((start_line, c_lst, assigned_vars1, out_gen_stack, out_stack_avail, saved_vars')) ->
                let assigned_vars2 = Set.union assigned_vars1 gb.assigned in
                Some((start_line, gb.code :: c_lst, assigned_vars2, out_gen_stack, out_stack_avail, saved_vars'))
            | None -> None)
        )

(* Ensures that a var is written to it's variable *)
(* TODO might be redundant to do this *)
let savevar_gen_stack _state target_var gen_stack stack_avail saved_vars =
  let stack_avail' = Set.remove stack_avail target_var in
  let rec loop gs acc =
    match gs with
    | [] -> raise (CodegenFailure "Var not on gen stack")
    | (gb :: gs') ->
        (match gb.out_stack with
        | Some(other_var) ->
            if equal_ivariable other_var target_var then
              let gb' = {
                gb with
                assigned = Set.add gb.assigned other_var;
                teed = true;
              }
              in List.rev_append (gb' :: acc) gs'
            else loop gs' (gb :: acc)
        | None ->
            loop gs' (gb :: acc)
        )
  in (loop gen_stack [], stack_avail', Set.add saved_vars target_var)


(* Unwinds the gen block stack to produce code for each Load Variable Order *)
let rec codegen_unwind_lvos state start_line lvo_stack gen_stack stack_avail saved_vars no_bypass =
  match lvo_stack with
  | [] -> (start_line, [], Set.empty (module IVariable), gen_stack, stack_avail, saved_vars)
  | (lvd :: lvo_lst') ->
      let var = lvd_var lvd in
      let no_bypass' = Map.change no_bypass var ~f:(fun old ->
        let count = (Option.value old ~default:1) - 1 in
        if count = 0 then None else Some(count))
      in
      (match lvd with
      | Lv_var(_) ->
          if Set.mem saved_vars var || not (Set.mem stack_avail var) then
            let (sl1, prev_lst, assigned_vars, gen_stack', stack_avail', saved_vars') =
              codegen_unwind_lvos state start_line lvo_lst' gen_stack stack_avail saved_vars no_bypass'
            in (sl1, "" :: prev_lst, assigned_vars, gen_stack', stack_avail', saved_vars')
          else
            let (gen_stack1, stack_avail1, saved_vars1) =
              savevar_gen_stack state var gen_stack stack_avail saved_vars
            in
            let (sl2, prev_lst, assigned_vars, gen_stack2, stack_avail2, saved_vars2) =
              codegen_unwind_lvos state start_line lvo_lst' gen_stack1 stack_avail1 saved_vars1 no_bypass'
            in
            (sl2, "" :: prev_lst, assigned_vars, gen_stack2, stack_avail2, saved_vars2)
            (* Unwind the stack *)
      | Lv_stack(_) ->
          let ignore_stack () =
            let code = codegen_getvar state var in
            let (sl1, prev_lst, assigned_vars, gen_stack', stack_avail', saved_vars') =
              codegen_unwind_lvos state start_line lvo_lst' gen_stack stack_avail saved_vars no_bypass'
            in (sl1, code :: prev_lst, assigned_vars, gen_stack', stack_avail', saved_vars')
          in
          if Set.mem stack_avail var then
            let unwind_option =
              unwind_gen_stack state var gen_stack stack_avail saved_vars no_bypass'
            in
            (match unwind_option with
            | Some ((sl1, c_lst, assigned_vars1, gen_stack1, stack_avail1, saved_vars1)) ->
                let (sl2, prev_lst, assigned_vars2, gen_stack2, stack_avail2, saved_vars2) =
                  codegen_unwind_lvos state sl1 lvo_lst' gen_stack1 stack_avail1 saved_vars1 no_bypass'
                in
                let code = String.concat ~sep:"\n" (List.rev c_lst) in
                let assigned_vars3 = Set.union assigned_vars1 assigned_vars2 in
                (sl2, code :: prev_lst, assigned_vars3, gen_stack2, stack_avail2, saved_vars2)
            | None ->
                ignore_stack ()
            )
            (* Unwind the stack *)
          else
            ignore_stack ()
      )

(* Empty the stack, saving variables instead *)
let empty_stack state gen_stack saved_vars =
  let rec loop gs sv acc sl =
    match gs with
    | [] -> (acc, sv, sl)
    | (gb :: gs') ->
        let (gb', sv') = unstack_gen_block state gb sv in
        loop gs' sv' (gb'.code :: acc) gb'.start_line
  in
  let (c_lst, saved_vars', start_line) = loop gen_stack saved_vars [] (-1) in
  if start_line = -1 then
    (None, saved_vars')
  else
    let gb = {
      start_line = start_line;
      code = String.concat ~sep:"\n" c_lst;
      out_stack = None;
      assigned = Set.empty (module IVariable);
      teed = false;
    }
    in
    (Some(gb), saved_vars')



(* Gives a list of gen blocks, and set of available vars on stack *)
(* Prev gens is backwards *)
let codegen_add_line state prev_gens avail_vars saved_vars line iins =
  let lvo_req = load_variable_order iins in
  let lvo_stack = List.rev lvo_req in
  let lvo_count_map = List.fold lvo_stack ~init:(Map.empty (module IVariable)) ~f:(fun map lvd ->
    let var = lvd_var lvd in
    Map.update map var ~f:(fun iopt -> 1 + (Option.value iopt ~default:0)))
  in
  let (start_line, lvo_code_stack, assigned_vars, prev_gens1, avail_vars1, saved_vars1) =
    codegen_unwind_lvos state line lvo_stack prev_gens avail_vars saved_vars lvo_count_map
  in
  let lvo_code = List.rev lvo_code_stack in
  (*let () = List.iteri lvo_code ~f:(fun id code ->
    Stdio.print_endline ("LVO " ^ (Int.to_string id) ^ ":\n" ^ code ^ "\n")
  ) in *)
  let full_code = codegen_iinstruction_core state saved_vars1 lvo_code iins in
  let (prev_gens2, avail_vars2, saved_vars2) =
    if needs_clear_stack iins then
      let (gs_opt, sv') = empty_stack state prev_gens1 saved_vars1 in
      (match gs_opt with
      | Some(gs) -> ([gs], Set.empty (module IVariable), sv')
      | None -> ([], Set.empty (module IVariable), sv'))
    else (prev_gens1, avail_vars1, saved_vars1)
  in
  let result = variable_result iins in
  let (gb, avail_vars3, saved_vars3) =
    match result with
    | None ->
        ({
          start_line = start_line;
          code = full_code;
          out_stack = None;
          assigned = assigned_vars;
          teed = false;
        }, avail_vars2, saved_vars2)
    | Some(Lv_var(res)) ->
        ({
          start_line = start_line;
          code = full_code;
          out_stack = None;
          assigned = Set.add assigned_vars res;
          teed = false;
        }, avail_vars2, Set.add saved_vars2 res)
    | Some(Lv_stack(res)) ->
        ({
          start_line = start_line;
          code = full_code;
          out_stack = Some(res);
          assigned = Set.add assigned_vars res;
          teed = false;
        }, Set.add avail_vars2 res, Set.remove saved_vars2 res)
  in (gb :: prev_gens2, avail_vars3, saved_vars3)

let codegen_basic_block state func (bb : Analysis.basic_block) =
  let all_lines = Array.to_list bb.bb_code in
  let rec loop gen_blocks avail_vars saved_vars line_num lines =
    match lines with
    | [] ->
          let codes = List.map gen_blocks ~f:(fun gb ->
            let (gb', _) = unstack_gen_block state gb (Set.empty (module IVariable))
            in gb'.code)
          in
          String.concat ~sep:"\n" (List.rev codes)
    | (line :: lines') ->
          let (gen_blocks', avail_vars', saved_vars') =
            codegen_add_line state gen_blocks avail_vars saved_vars line_num line
          in
          (* let () = print_state ("After line " ^ (Int.to_string line_num)) gen_blocks' avail_vars' saved_vars' in *)
          loop gen_blocks' avail_vars' saved_vars' (line_num + 1) lines'
  in
  let all_vars = Vars.get_ivariables func.pf_vars in
  let cvar_count = List.length func.pf_cvars in
  let arg_vars = List.take all_vars (cvar_count + 1) in
  let initial_saved_vars = Set.of_list (module IVariable) arg_vars in
  loop [] (Set.empty (module IVariable)) initial_saved_vars bb.bb_start_line all_lines


let codegen_basic_block_nostack state (bb : Analysis.basic_block) =
  let lines = Array.to_list bb.bb_code in
  let line_codes = List.map ~f:(codegen_iinstruction_simple state) lines in
  String.concat ~sep:"\n" line_codes

let remove_unused_vars state func =
  let all_vars = Vars.get_vars state.vars in
  let cvar_count = List.length func.pf_cvars in
  let local_vars = List.drop all_vars (cvar_count + 1) in
  let () = List.iter local_vars ~f:(fun (name, _) ->
    let var = (Local, name) in
    if not (Set.mem state.used_vars var) then
      state.vars <- Vars.remove_var state.vars name
  )
  in
  state.vars

let codegen_ifunction_code wrap_table globals func =
  let fa = Analysis.analyse_function globals func in
  let state = {
    wrap_table = wrap_table;
    vars = func.pf_vars;
    fa = fa;
    used_vars = Set.empty (module IVariable);
  }
  in
  let unmapped = Map.data fa.fa_basic_blocks in
  let bb_codes =
    if Config.global.optimise_stack_codegen then
      List.map ~f:(codegen_basic_block state func) unmapped
    else
      List.map ~f:(codegen_basic_block_nostack state) unmapped
  in
  let full_code = String.concat ~sep:"\n" bb_codes in
  let reduced_vars = remove_unused_vars state func in
  (reduced_vars, full_code)
