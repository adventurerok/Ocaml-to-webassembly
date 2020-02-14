open Core_kernel
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

let optimise_function (prog : iprogram) (func : ifunction) =
  eliminate_temp_to_named prog.prog_globals func

let optimise (prog : iprogram) =
  {
    prog with
    prog_functions = Map.Poly.map ~f:(optimise_function prog) prog.prog_functions
  }
