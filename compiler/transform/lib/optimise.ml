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
  iinstruction_list_map_vars ~f:check_var code

let print_function (func : ifunction) =
  if not Config.global.trace then
    func
  else begin
    Stdio.print_endline ("\nFunction code for " ^ func.pf_name);
    List.iteri func.pf_code ~f:(fun line iins -> Stdio.print_endline ((Int.to_string line) ^ " :  " ^ (iinstruction_to_string iins)));
    Stdio.print_endline ("/End of function\n");
    func
  end

let print_analysis globals (func : ifunction) =
  if not Config.global.trace then
    func
  else begin
    let fa = Analysis.analyse_function globals func in
    let str = Analysis.func_analysis_to_string fa in
    Stdio.print_endline str;
    let (_, lva) = Analysis.live_variables fa in
    Analysis.print_live_variables func lva;
    func
  end


let eliminate_redundant_copies code =
  List.filter_map code ~f:(fun iins ->
    match iins with
    | Iins_copyvar(_, res, arg) ->
        if equal_ivariable res arg then
          None
        else
          Some(iins)
    | _ -> Some(iins))

(* This is the shitty old version that uses variable statistics *)
let rec eliminate_temp_to_named globals func =
  if not Config.global.optimise_alias_elimination then
    func
  else
    let () = if Config.global.debug then
      Stdio.print_endline ("Old eliminate temp to named for " ^ func.pf_name)
    in
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
let rec propagate_copies globals func =
  if not Config.global.optimise_alias_elimination then
    func
  else
    let () = if Config.global.debug then
      (Stdio.print_endline ("Propagate copies for " ^ func.pf_name);
      let _ : ifunction = print_analysis globals func in ())
    in
    let fa = Analysis.analyse_function globals func in
    let rds = Analysis.reaching_definitions fa in
    let () = if Config.global.trace then Analysis.print_reaching_definitions rds in
    let acs = Analysis.active_copies fa in
    let copy_defs = Hashtbl.create (module Int) in
    (* Safety net set of copy statements we have already used, to prevent modifying them *)
    let copies_used = Hash_set.create (module Int) in
    List.iteri func.pf_code ~f:(fun line iins ->
      (match iins with
      | Iins_copyvar(_, _, arg) ->
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
        let defs_lst, target =
          match var_defs_opt with
          | Some(var_defs) ->
              let vd_lst = Set.to_list var_defs in
              let vd_copies = List.map vd_lst ~f:(Hashtbl.find copy_defs) in
              let vd_filter = List.filter_opt vd_copies in
              if List.length vd_copies <> List.length vd_filter then
                (* There are some definitions which are not copies *)
                [], var
              else
                let vd_unique = List.remove_consecutive_duplicates vd_filter ~equal:equal_ivariable in
                (* Now we see if there is only 1 definition variable *)
                (match vd_unique with
                | [uni] -> vd_lst, uni
                | _ -> [], var)
                | None -> [], var
        in
        if equal_ivariable target var then
          var
        else
          let active_copy_defs = Hashtbl.find_exn acs line in
          let target_copies = Option.value ~default:Analysis.vns_empty (Map.find active_copy_defs target) in
          if Analysis.vns_mem target_copies var then
            (changed := true;
            List.iter defs_lst ~f:(fun def_line -> Hash_set.add copies_used def_line);
            target)
          else
            var

    in
    let map_variables line vars =
      List.map vars ~f:(map_variable line)
    in
    let new_code = List.mapi func.pf_code ~f:(fun line iins ->
      (match iins with
      | Iins_setvar (_, _, _) -> iins
      | Iins_copyvar (it, res, arg) ->
          let new_arg = map_variable line arg in
          if not (Hash_set.mem copies_used line) && not (equal_ivariable arg new_arg) then
            (* Invalidate the copydef. We loop this whole analysis to give this copydef a chance to be useful later *)
            (Hashtbl.remove copy_defs line;
            Iins_copyvar(it, res, map_variable line arg))
          else
            iins
      | Iins_return (it, arg) -> Iins_return(it, map_variable line arg)
      | Iins_unop (it, unop, res, arg) -> Iins_unop(it, unop, res, map_variable line arg)
      | Iins_binop (it, binop, res, arg1, arg2) -> Iins_binop(it, binop, res, map_variable line arg1, map_variable line arg2)
      | Iins_newclosure (_, _, _, _) -> iins
      | Iins_fillclosure (itt, res, args) -> Iins_fillclosure(itt, res, map_variables line args)
      | Iins_callclosure (ift, out, clo, arg) -> Iins_callclosure(ift, out, map_variable line clo, map_variable line arg)
      | Iins_calldirect (out, name, itt, args) -> Iins_calldirect(out, name, itt, map_variables line args)
      | Iins_startblock _ -> iins
      | Iins_endblock _ -> iins
      | Iins_exitblock _ -> iins
      | Iins_exitblockif (block, arg) -> Iins_exitblockif(block, map_variable line arg)
      | Iins_startif (block, arg) -> Iins_startif(block, map_variable line arg)
      | Iins_else _ -> iins
      | Iins_endif _ -> iins
      | Iins_startloop (_, _) -> iins
      | Iins_endloop (_, _) -> iins
      | Iins_pushtuple (itt, res, args) -> Iins_pushtuple(itt, res, map_variables line args)
      | Iins_loadtupleindex (itt, id, res, tup) -> Iins_loadtupleindex(itt, id, res, map_variable line tup)
      | Iins_pushconstruct (itt, res, id, args) -> Iins_pushconstruct(itt, res, id, map_variables line args)
      | Iins_loadconstructindex (itt, id, res, tup) -> Iins_loadconstructindex(itt, id, res, map_variable line tup)
      | Iins_loadconstructid (res, tup) -> Iins_loadconstructid(res, map_variable line tup)
      | Iins_newbox (it, unbox, box) -> Iins_newbox(it, map_variable line unbox, box)
      | Iins_updatebox (it, unbox, box) -> Iins_updatebox(it, map_variable line unbox, map_variable line box)
      | Iins_unbox (it, box, unbox) -> Iins_unbox(it, map_variable line box, unbox)
      | Iins_fail -> iins)
    )
    in let new_func = {
      func with
      pf_code = eliminate_redundant_copies new_code
    }
    in
    if !changed then
      propagate_copies globals new_func
    else
      new_func


(* let eliminate_copies globals (func : ifunction) =
  let fa = Analysis.analyse_function globals func in
  let rd = Analysis.reaching_definitions fa in
  let invert_rd = Analysis.invert_reaching_definitions fa rd in
  *)


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
    let () = if Config.global.debug then
      Stdio.print_endline ("Eliminate tuple loads for " ^ func.pf_name)
    in
    let fa = Analysis.analyse_function globals func in
    let tup_map = Hashtbl.create (module Int) in
    let construct_map = Hashtbl.create (module Int) in
    List.iteri func.pf_code ~f:(fun line iins ->
      (match iins with
      | Iins_pushtuple (_, _, vars) ->
          Hashtbl.set tup_map ~key:line ~data:(Array.of_list vars)
      | Iins_pushconstruct (_, _, id, vars) ->
          Hashtbl.set construct_map ~key:line ~data:((id, Array.of_list vars))
      | _ -> ())
    );
    let rds = Analysis.reaching_definitions fa in
    let changed = ref false in
    let new_code = List.mapi func.pf_code ~f:(fun line iins ->
      let line_defs = Hashtbl.find_exn rds line in
      (match iins with
      | Iins_loadtupleindex (itt, index, dest, tup) ->
          let tup_def_opt = Analysis.unique_reaching_definition line_defs tup in
          (match tup_def_opt with
          | Some(def_line) ->
              let tup_vars_opt = Hashtbl.find tup_map def_line in
              (match tup_vars_opt with
              | Some(tup_vars) ->
                  let source_var = Array.get tup_vars index in
                  let var_typ = List.nth_exn itt index in
                  changed := true;
                  (Iins_copyvar(var_typ, dest, source_var))
              | None -> iins)
          | None -> iins)
      | Iins_loadconstructindex (itt, index, dest, construct) ->
          let construct_def_opt = Analysis.unique_reaching_definition line_defs construct in
          (match construct_def_opt with
          | Some(def_line) ->
              let construct_data_opt = Hashtbl.find construct_map def_line in
              (match construct_data_opt with
              | Some((_, construct_vars)) ->
                  let source_var = Array.get construct_vars index in
                  let var_typ = List.nth_exn itt index in
                  changed := true;
                  (Iins_copyvar(var_typ, dest, source_var))
              | None -> iins)
          | None -> iins)
      | Iins_loadconstructid (dest, construct) ->
          let construct_def_opt = Analysis.unique_reaching_definition line_defs construct in
          (match construct_def_opt with
          | Some(def_line) ->
              let construct_data_opt = Hashtbl.find construct_map def_line in
              (match construct_data_opt with
              | Some((construct_id, _)) ->
                  changed := true;
                  (Iins_setvar(It_int, dest, Int.to_string construct_id))
              | None -> iins)
          | None -> iins)
      | _ -> iins)
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
    let () = if Config.global.debug then
      Stdio.print_endline ("Eliminate dead code for " ^ func.pf_name)
    in
    let fa = Analysis.analyse_function globals func in
    let (_, lva_out) = Analysis.live_variables fa in
    let changed = ref false in
    let new_code = List.filter_mapi func.pf_code ~f:(fun line iins ->
      let live_vars = Hashtbl.find_exn lva_out line in
      let assign_var_opt, _ = Analysis.instr_vars iins in
      match assign_var_opt with
      | Some(assign) ->
          if (ivariable_is_local assign) && (not (Set.mem live_vars assign)) && (not (Analysis.can_side_effect iins)) then
            (changed := true;
            None)
          else
            Some(iins)
      | None -> Some(iins))
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
    let () = if Config.global.debug then
      Stdio.print_endline ("Eliminate redundant refs for " ^ func.pf_name)
    in
    let fa = Analysis.analyse_function globals func in
    let target_vars = Hash_set.of_list (module IVariable) (Vars.get_ivariables func.pf_vars) in
    (* Remove argument variables as if these are refs, they allow external side effects *)
    List.iter fa.fa_args ~f:(Hash_set.remove target_vars);
    List.iter func.pf_code ~f:(fun iins ->
      match iins with
      | Iins_newbox(_, unboxed, _) ->
          Hash_set.remove target_vars unboxed
      | Iins_updatebox(_, unboxed, _) ->
          Hash_set.remove target_vars unboxed
      | Iins_unbox(_, _, unboxed) ->
          Hash_set.remove target_vars unboxed
      | _ ->
          let assign_opt, used = Analysis.instr_vars iins in
          List.iter ((Option.to_list assign_opt) @ used) ~f:(Hash_set.remove target_vars)
    );
    let changed = ref false in
    let vars_ref = ref func.pf_vars in
    let new_code = List.map func.pf_code ~f:(fun iins ->
      match iins with
      | Iins_newbox(it, unboxed, ((_, bname) as boxed)) ->
          if Hash_set.mem target_vars boxed then
            (changed := true;
            let vars = !vars_ref in
            let vars1 = Vars.change_var_type vars bname it in
            vars_ref := vars1;
            (Iins_copyvar(it, boxed, unboxed)))
          else
            iins
      | Iins_updatebox(it, unboxed, boxed) ->
          if Hash_set.mem target_vars boxed then
            (changed := true;
            (Iins_copyvar(it, boxed, unboxed)))
          else
            iins
      | Iins_unbox(it, boxed, unboxed) ->
          if Hash_set.mem target_vars boxed then
            (changed := true;
            (Iins_copyvar(it, unboxed, boxed)))
          else
            iins
      | _ -> iins
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


let eliminate_unreachable_blocks globals (func : ifunction) =
  let fa = Analysis.analyse_function globals func in
  (* The blocks will be in order thanks to the map's tree structure *)
  let bbs = Map.data fa.fa_basic_blocks in
  let block_codes =
    List.map bbs ~f:(fun bb ->
      if bb.bb_start_line = 0 || (List.length bb.bb_pred) > 0 then
        Array.to_list bb.bb_code
      else
        List.filter_map (Array.to_list bb.bb_code) ~f:(fun iins ->
          (* It is still possible for an unreachable basic block to have essential control structure markers in it *)
          match iins with
          | Iins_startloop _ -> Some(iins)
          | Iins_endloop _ -> Some(iins)
          | Iins_startif _ -> Some(iins)
          | Iins_else _ -> Some(iins)
          | Iins_endif _ -> Some(iins)
          | Iins_startblock _ -> Some(iins)
          | Iins_endblock _ -> Some(iins)
          | _ -> None
        )
    )
  in
  let new_code = List.concat block_codes in
  {
    func with
    pf_code = new_code
  }


let optimise_function (prog : iprogram) (func : ifunction) =
  (if Config.global.debug then
    (Stdio.print_endline ("Function " ^ func.pf_name);
    let fa = Analysis.analyse_function prog.prog_globals func in
    let rd = Analysis.reaching_definitions fa in
    Analysis.print_reaching_definitions rd;
    let (_, lva) = Analysis.live_variables fa in
    Analysis.print_live_variables func lva));
  let final_func =
      func
      (* Eliminating unreachable blocks is essential as tail call optimisation can generate broken unreachable blocks *)
      |> eliminate_unreachable_blocks prog.prog_globals
      |> propagate_copies prog.prog_globals
      |> eliminate_tuple_loads prog.prog_globals
      |> propagate_copies prog.prog_globals
      |> print_function
      |> eliminate_dead_code prog.prog_globals
      |> print_function
      |> eliminate_redundant_refs prog.prog_globals
      |> print_function
      |> eliminate_dead_code prog.prog_globals
      |> print_function
      |> print_analysis prog.prog_globals
      |> propagate_copies prog.prog_globals
      |> print_function
      |> print_analysis prog.prog_globals
      |> eliminate_dead_code prog.prog_globals
      |> print_function
      |> eliminate_unused_vars prog.prog_globals
  in
  final_func

let optimise (prog : iprogram) =
  {
    prog with
    prog_functions = Map.Poly.map ~f:(optimise_function prog) prog.prog_functions
  }
