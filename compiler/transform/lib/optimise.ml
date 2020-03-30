open Core_kernel
open Otwa_base
open Intermediate_ast
open Intermediate_program

let replace_var oldvar newvar code =
  let check_var var =
    if equal_ivariable oldvar var then
      newvar
    else
      var
  in
  iexpression_list_map_vars ~f:check_var code


let eliminate_redundant_copies code =
  List.filter_map code ~f:(fun iexpr ->
    match iexpr with
    | Iexp_copyvar(_, res, arg) ->
        if equal_ivariable res arg then
          None
        else
          Some(iexpr)
    | _ -> Some(iexpr))

(* This is the shitty old version that uses variable statistics *)
let rec eliminate_temp_to_named globals func =
  if not Config.global.optimise_alias_elimination then
    func
  else
    let fa = Analysis.analyse_function globals func in
    let map = Analysis.temp_to_named func fa in
    if List.is_empty map then
      func
    else
      let vars1 = List.fold map ~init:func.pf_vars ~f:(fun vrs ((_, ovar), _) ->
        Vars.remove_var vrs ovar)
      in
      let code1 = List.fold map ~init:func.pf_code ~f:(fun code (ovar, nvar) ->
        Stdio.print_endline ("Elim var " ^ (ivariable_to_string ovar) ^ " " ^ (ivariable_to_string nvar));
        replace_var ovar nvar code)
      in
      let code2 = eliminate_redundant_copies code1
      in
      let func1 = {
        func with
        pf_vars = vars1;
        pf_code = code2
      }
      in
      eliminate_temp_to_named globals func1

(* And the shiny new version that uses reaching definitions *)
(* Finds variables that have been copied, and replaces them with uncopied version *)
let rec eliminate_copies globals func =
  if not Config.global.optimise_alias_elimination then
    func
  else
    let fa = Analysis.analyse_function globals func in
    let rds = Analysis.reaching_definitions fa in
    let acs = Analysis.active_copies fa in
    let copy_defs = Hashtbl.create (module Int) in
    List.iteri func.pf_code ~f:(fun line iexpr ->
      (match iexpr with
      | Iexp_copyvar(_, _, arg) ->
          Hashtbl.set copy_defs ~key:line ~data:arg
      | _ -> ())
    );
    let changed = ref false in
    (* We can map a variable if all of it's definitions are copying the same variable *)
    let map_variable line var =
      if ivariable_is_global var then
        var
      else
        let line_defs = Hashtbl.find_exn rds line in
        let var_defs_opt = Map.find line_defs var in
        let target =
          match var_defs_opt with
          | Some(var_defs) ->
              let vd_lst = Set.to_list var_defs in
              let vd_copies = List.map vd_lst ~f:(Hashtbl.find copy_defs) in
              let vd_filter = List.filter_opt vd_copies in
              if List.length vd_copies <> List.length vd_filter then
                (* There are some definitions which are not copies *)
                var
              else
                let vd_unique = List.remove_consecutive_duplicates vd_filter ~equal:equal_ivariable in
                (* Now we see if there is only 1 definition variable *)
                (match vd_unique with
                | [uni] -> uni
                | _ -> var)
          | None -> var
        in
        if equal_ivariable target var then
          var
        else
          let active_copy_defs = Hashtbl.find_exn acs line in
          let target_copies = Option.value ~default:(Set.empty (module IVariable)) (Map.find active_copy_defs target) in
          if Set.mem target_copies var then
            (changed := true;
            target)
          else
            var

    in
    let map_variables line vars =
      List.map vars ~f:(map_variable line)
    in
    let new_code = List.mapi func.pf_code ~f:(fun line iexpr ->
      (match iexpr with
      | Iexp_setvar (_, _, _) -> iexpr
      | Iexp_copyvar (it, res, arg) -> Iexp_copyvar(it, res, map_variable line arg)
      | Iexp_return (it, arg) -> Iexp_return(it, map_variable line arg)
      | Iexp_unop (it, unop, res, arg) -> Iexp_unop(it, unop, res, map_variable line arg)
      | Iexp_binop (it, binop, res, arg1, arg2) -> Iexp_binop(it, binop, res, map_variable line arg1, map_variable line arg2)
      | Iexp_newclosure (_, _, _, _) -> iexpr
      | Iexp_fillclosure (itt, res, args) -> Iexp_fillclosure(itt, res, map_variables line args)
      | Iexp_callclosure (ift, out, clo, arg) -> Iexp_callclosure(ift, out, map_variable line clo, map_variable line arg)
      | Iexp_calldirect (out, name, itt, args) -> Iexp_calldirect(out, name, itt, map_variables line args)
      | Iexp_startblock _ -> iexpr
      | Iexp_endblock _ -> iexpr
      | Iexp_exitblock _ -> iexpr
      | Iexp_exitblockif (block, arg) -> Iexp_exitblockif(block, map_variable line arg)
      | Iexp_startif (block, arg) -> Iexp_startif(block, map_variable line arg)
      | Iexp_else _ -> iexpr
      | Iexp_endif _ -> iexpr
      | Iexp_startloop (_, _) -> iexpr
      | Iexp_endloop (_, _) -> iexpr
      | Iexp_pushtuple (itt, res, args) -> Iexp_pushtuple(itt, res, map_variables line args)
      | Iexp_loadtupleindex (itt, id, res, tup) -> Iexp_loadtupleindex(itt, id, res, map_variable line tup)
      | Iexp_pushconstruct (itt, res, id, args) -> Iexp_pushconstruct(itt, res, id, map_variables line args)
      | Iexp_loadconstructindex (itt, id, res, tup) -> Iexp_loadconstructindex(itt, id, res, map_variable line tup)
      | Iexp_loadconstructid (res, tup) -> Iexp_loadconstructid(res, map_variable line tup)
      | Iexp_newbox (it, unbox, box) -> Iexp_newbox(it, map_variable line unbox, box)
      | Iexp_updatebox (it, unbox, box) -> Iexp_updatebox(it, map_variable line unbox, map_variable line box)
      | Iexp_unbox (it, box, unbox) -> Iexp_unbox(it, map_variable line box, unbox)
      | Iexp_fail -> iexpr)
    )
    in let new_func = {
      func with
      pf_code = new_code
    }
    in
    if !changed then
      eliminate_copies globals new_func
    else
      new_func

(* Eliminate from the function vars those vars which are not used anywhere anymore *)
let eliminate_unused_vars globals (func : ifunction) =
  let fa = Analysis.analyse_function globals func in
  let arg_set = Hash_set.of_list (module IVariable) fa.fa_args in
  let vars_ref = ref func.pf_vars in
  Hashtbl.iter fa.fa_var_stats ~f:(fun vs ->
    let var = (vs.vs_scope, vs.vs_name) in
    if equal_iscope vs.vs_scope Local && vs.vs_use_count = 0 && vs.vs_assign_count = 0 && not (Hash_set.mem arg_set var) then
      (let vars = !vars_ref in
      let vars1 = Vars.remove_var vars vs.vs_name in
      vars_ref := vars1)
      (* We can eliminate *)
    else ()
  );
  {
    func with
    pf_vars = !vars_ref
  }



(* If we know which variables make up a tuple / construct, we can use them instead of loadtupleindex *)

let rec eliminate_tuple_loads globals func =
  if not Config.global.optimise_tuple_loads then
    func
  else
    let fa = Analysis.analyse_function globals func in
    let tup_map = Hashtbl.create (module Int) in
    let construct_map = Hashtbl.create (module Int) in
    List.iteri func.pf_code ~f:(fun line iexpr ->
      (match iexpr with
      | Iexp_pushtuple (_, _, vars) ->
          Hashtbl.set tup_map ~key:line ~data:(Array.of_list vars)
      | Iexp_pushconstruct (_, _, id, vars) ->
          Hashtbl.set construct_map ~key:line ~data:((id, Array.of_list vars))
      | _ -> ())
    );
    let rds = Analysis.reaching_definitions fa in
    let changed = ref false in
    let new_code = List.mapi func.pf_code ~f:(fun line iexpr ->
      let line_defs = Hashtbl.find_exn rds line in
      (match iexpr with
      | Iexp_loadtupleindex (itt, index, dest, tup) ->
          let tup_def_opt = Analysis.unique_reaching_definition line_defs tup in
          (match tup_def_opt with
          | Some(def_line) ->
              let tup_vars_opt = Hashtbl.find tup_map def_line in
              (match tup_vars_opt with
              | Some(tup_vars) ->
                  let source_var = Array.get tup_vars index in
                  let var_typ = List.nth_exn itt index in
                  changed := true;
                  (Iexp_copyvar(var_typ, dest, source_var))
              | None -> iexpr)
          | None -> iexpr)
      | Iexp_loadconstructindex (itt, index, dest, construct) ->
          let construct_def_opt = Analysis.unique_reaching_definition line_defs construct in
          (match construct_def_opt with
          | Some(def_line) ->
              let construct_data_opt = Hashtbl.find construct_map def_line in
              (match construct_data_opt with
              | Some((_, construct_vars)) ->
                  let source_var = Array.get construct_vars index in
                  let var_typ = List.nth_exn itt index in
                  changed := true;
                  (Iexp_copyvar(var_typ, dest, source_var))
              | None -> iexpr)
          | None -> iexpr)
      | Iexp_loadconstructid (dest, construct) ->
          let construct_def_opt = Analysis.unique_reaching_definition line_defs construct in
          (match construct_def_opt with
          | Some(def_line) ->
              let construct_data_opt = Hashtbl.find construct_map def_line in
              (match construct_data_opt with
              | Some((construct_id, _)) ->
                  changed := true;
                  (Iexp_setvar(It_int, dest, Int.to_string construct_id))
              | None -> iexpr)
          | None -> iexpr)
      | _ -> iexpr)
    )
    in
    let result_func = { func with pf_code = new_code } in
    if !changed then
      eliminate_tuple_loads globals result_func
    else
      result_func


let rec eliminate_dead_code globals func =
  if not Config.global.optimise_dead_code then
    func
  else
    let fa = Analysis.analyse_function globals func in
    let (_, lva_out) = Analysis.live_variables fa in
    let changed = ref false in
    let new_code = List.filter_mapi func.pf_code ~f:(fun line iexpr ->
      let live_vars = Hashtbl.find_exn lva_out line in
      let assign_var_opt, _ = Analysis.instr_vars iexpr in
      match assign_var_opt with
      | Some(assign) ->
          if (ivariable_is_local assign) && (not (Set.mem live_vars assign)) && (not (Analysis.can_side_effect iexpr)) then
            (changed := true;
            None)
          else
            Some(iexpr)
      | None -> Some(iexpr))
    in
    let result_func = { func with pf_code = new_code } in
    if !changed then
      eliminate_dead_code globals result_func
    else
      result_func


let rec eliminate_redundant_refs globals func =
  if not Config.global.optimise_refs then
    func
  else
    let fa = Analysis.analyse_function globals func in
    let target_vars = Hash_set.of_list (module IVariable) (Vars.get_ivariables func.pf_vars) in
    (* Remove argument variables as if these are refs, they allow external side effects *)
    List.iter fa.fa_args ~f:(Hash_set.remove target_vars);
    List.iter func.pf_code ~f:(fun iexpr ->
      match iexpr with
      | Iexp_newbox(_, unboxed, _) ->
          Hash_set.remove target_vars unboxed
      | Iexp_updatebox(_, unboxed, _) ->
          Hash_set.remove target_vars unboxed
      | Iexp_unbox(_, _, unboxed) ->
          Hash_set.remove target_vars unboxed
      | _ ->
          let assign_opt, used = Analysis.instr_vars iexpr in
          List.iter ((Option.to_list assign_opt) @ used) ~f:(Hash_set.remove target_vars)
    );
    let changed = ref false in
    let vars_ref = ref func.pf_vars in
    let new_code = List.map func.pf_code ~f:(fun iexpr ->
      match iexpr with
      | Iexp_newbox(it, unboxed, ((_, bname) as boxed)) ->
          if Hash_set.mem target_vars boxed then
            (changed := true;
            let vars = !vars_ref in
            let vars1 = Vars.change_var_type vars bname it in
            vars_ref := vars1;
            (Iexp_copyvar(it, boxed, unboxed)))
          else
            iexpr
      | Iexp_updatebox(it, unboxed, boxed) ->
          if Hash_set.mem target_vars boxed then
            (changed := true;
            (Iexp_copyvar(it, boxed, unboxed)))
          else
            iexpr
      | Iexp_unbox(it, boxed, unboxed) ->
          if Hash_set.mem target_vars boxed then
            (changed := true;
            (Iexp_copyvar(it, unboxed, boxed)))
          else
            iexpr
      | _ -> iexpr
    )
    in
    let result_func = {
      func with
      pf_code = new_code;
      pf_vars = !vars_ref;
    }
    in
    if !changed then
      eliminate_redundant_refs globals result_func
    else
      result_func


let optimise_function (prog : iprogram) (func : ifunction) =
  (if Config.global.debug then
    (Stdio.print_endline ("Function " ^ func.pf_name);
    let fa = Analysis.analyse_function prog.prog_globals func in
    let rd = Analysis.reaching_definitions fa in
    Analysis.print_reaching_definitions rd;
    let (_, lva) = Analysis.live_variables fa in
    Analysis.print_live_variables lva));
  let final_func =
      func
      (* |> eliminate_temp_to_named prog.prog_globals *)
      (* |> eliminate_redundant_refs prog.prog_globals *)
      |> eliminate_copies prog.prog_globals
      |> eliminate_tuple_loads prog.prog_globals
      |> eliminate_copies prog.prog_globals
      |> eliminate_dead_code prog.prog_globals
      |> eliminate_redundant_refs prog.prog_globals
      |> eliminate_dead_code prog.prog_globals
      |> eliminate_copies prog.prog_globals
      |> eliminate_dead_code prog.prog_globals
      |> eliminate_unused_vars prog.prog_globals
      (* |> eliminate_temp_to_named prog.prog_globals *)
  in
  final_func

let optimise (prog : iprogram) =
  {
    prog with
    prog_functions = Map.Poly.map ~f:(optimise_function prog) prog.prog_functions
  }
