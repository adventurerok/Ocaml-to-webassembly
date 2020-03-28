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
      (* TODO constructs *)
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


let optimise_function (prog : iprogram) (func : ifunction) =
  let fa = Analysis.analyse_function prog.prog_globals func in
  (* let rd = Analysis.reaching_definitions fa in
  Hashtbl.iteri rd ~f:(fun ~key:k ~data:d ->
    let var_strs =
      Map.to_alist d
      |> List.map ~f:(fun (vr, dfs) ->
          (ivariable_to_string vr) ^ ": " ^ (String.concat ~sep:"," (List.map (Set.to_list dfs) ~f:Int.to_string)))
    in
    let out = (Int.to_string k) ^ " --> " ^ (String.concat ~sep:"; " var_strs) in
    Stdio.print_endline out
  ); *)
  let (_, lva) = Analysis.live_variables fa in
  let lva_map = Map.of_alist_exn (module Int) (Hashtbl.to_alist lva) in
  Map.iteri lva_map ~f:(fun ~key:line ~data:live ->
    let var_strs = List.map ~f:ivariable_to_string (Set.to_list live) in
    let out = (Int.to_string line) ^ " --> " ^ (String.concat ~sep:", " var_strs) in
    Stdio.print_endline out
  );
  let f1 = eliminate_temp_to_named prog.prog_globals func in
  let f2 = eliminate_tuple_loads prog.prog_globals f1 in
  let f3 = eliminate_temp_to_named prog.prog_globals f2 in
  let f4 = eliminate_dead_code prog.prog_globals f3 in
  f4

let optimise (prog : iprogram) =
  {
    prog with
    prog_functions = Map.Poly.map ~f:(optimise_function prog) prog.prog_functions
  }
