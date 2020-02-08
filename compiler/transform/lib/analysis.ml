open Core_kernel
open Intermediate_ast
open Intermediate_program

type func_analysis = {
  fa_name: string;
  fa_var_stats: (string, var_stats) Hashtbl.t;
}

and var_stats = {
  vs_name: string;
  vs_type: itype;
  vs_temp: bool;
  mutable vs_use_count: int;
  mutable vs_assign_count: int;
  mutable vs_first_assign: int;
  mutable vs_last_assign: int;
  mutable vs_first_use: int;
  mutable vs_last_use: int;
  mutable vs_assign_locs: int list;
  mutable vs_use_locs: int list;
}

let var_stats_to_string vs =
  "{ var name = " ^ vs.vs_name ^ "\n" ^
  "type = " ^ (itype_to_string vs.vs_type) ^ "\n" ^
  "temp = " ^ (Bool.to_string vs.vs_temp) ^ "\n" ^
  "use_count = " ^ (Int.to_string vs.vs_use_count) ^ "\n" ^
  "assign_count = " ^ (Int.to_string vs.vs_assign_count) ^ "\n" ^
  "first_assign = " ^ (Int.to_string vs.vs_first_assign) ^ "\n" ^
  "last_assign = " ^ (Int.to_string vs.vs_last_assign) ^ "\n" ^
  "first_use = " ^ (Int.to_string vs.vs_first_use) ^ "\n" ^
  "last_use = " ^ (Int.to_string vs.vs_last_use) ^ "\n" ^
  "assign_locs = " ^ (String.concat ~sep:"," (List.map ~f:Int.to_string vs.vs_assign_locs)) ^ "\n" ^
  "use_locs = " ^ (String.concat ~sep:"," (List.map ~f:Int.to_string vs.vs_use_locs)) ^ " }\n"

let func_analysis_to_string fa =
  "Function Analysis for " ^ fa.fa_name ^ "\n" ^
  "Variables: \n" ^
  (String.concat (List.map ~f:var_stats_to_string (Hashtbl.data fa.fa_var_stats))) ^ "\n"

let new_var_stats name typ temp () =
  {
    vs_name = name;
    vs_type = typ;
    vs_temp = temp;
    vs_use_count = 0;
    vs_assign_count = 0;
    vs_first_assign = -1;
    vs_last_assign = -1;
    vs_first_use = -1;
    vs_last_use = -1;
    vs_assign_locs = [];
    vs_use_locs = [];
  }

let var_assigned func state line name =
  let vi = Option.value_exn (Vars.lookup_var_info func.pf_vars name) in
  let vs = Hashtbl.find_or_add state.fa_var_stats name ~default:(new_var_stats name vi.vi_itype vi.vi_temp) in
  vs.vs_assign_count <- vs.vs_assign_count + 1;
  (if vs.vs_first_assign = -1 then vs.vs_first_assign <- line);
  vs.vs_last_assign <- line;
  vs.vs_assign_locs <- line :: vs.vs_assign_locs

let var_used func state line name =
  let vi = Option.value_exn (Vars.lookup_var_info func.pf_vars name) in
  let vs = Hashtbl.find_or_add state.fa_var_stats name ~default:(new_var_stats name vi.vi_itype vi.vi_temp) in
  vs.vs_use_count <- vs.vs_use_count + 1;
  (if vs.vs_first_use = -1 then vs.vs_first_use <- line);
  vs.vs_last_use <- line;
  vs.vs_use_locs <- line :: vs.vs_use_locs

let update_line_vars func state line assigned used =
  let local_only (scope,name) =
    match scope with
    | Local -> Some(name)
    | Global -> None
  in
  let assigned_names = List.filter_map ~f:local_only assigned in
  let used_names = List.filter_map ~f:local_only used in
  List.iter ~f:(var_assigned func state line) assigned_names;
  List.iter ~f:(var_used func state line) used_names

let analyse_instr func state line (iexpr : iexpression) =
  let ulv_filled = update_line_vars func state line in
  match iexpr with
  | Iexp_setvar (_, res, _) -> ulv_filled [res] []
  | Iexp_copyvar (_, res, arg) -> ulv_filled [res] [arg]
  | Iexp_return (_, arg) -> ulv_filled [] [arg]
  | Iexp_unop (_, _, res, arg) -> ulv_filled [res] [arg]
  | Iexp_binop (_, _, res, arg1, arg2) -> ulv_filled [res] [arg1; arg2]
  | Iexp_newclosure (_, _, _, res) -> ulv_filled [res] []
  | Iexp_fillclosure (_, a1, alst) -> ulv_filled [] (a1 :: alst)
  | Iexp_callclosure (_, res, clo, arg) -> ulv_filled [res] [clo; arg]
  | Iexp_startblock _ -> ()
  | Iexp_endblock _ -> ()
  | Iexp_exitblock _ -> ()
  | Iexp_exitblockif (_, arg) -> ulv_filled [] [arg]
  | Iexp_startif (_, arg) -> ulv_filled [] [arg]
  | Iexp_else _ -> ()
  | Iexp_endif _ -> ()
  | Iexp_startloop (_, _) -> ()
  | Iexp_endloop (_, _) -> ()
  | Iexp_pushtuple (_, res, args) -> ulv_filled [res] args
  | Iexp_loadtupleindex (_, _, res, arg) -> ulv_filled [res] [arg]
  | Iexp_pushconstruct (_, res, _, args) -> ulv_filled [res] args
  | Iexp_loadconstructindex (_, _, res, arg) -> ulv_filled [res] [arg]
  | Iexp_loadconstructid (res, arg) -> ulv_filled [res] [arg]
  | Iexp_newbox (_, arg, res) -> ulv_filled [res] [arg]
  | Iexp_updatebox (_, arg, box) -> ulv_filled [] [arg; box]
  | Iexp_unbox (_, arg, res) -> ulv_filled [res] [arg]
  | Iexp_fail -> ()

let analyse_function (func : ifunction) =
  let fa = {
    fa_name = func.pf_name;
    fa_var_stats = Hashtbl.create (module String);
  }
  in
  List.iteri ~f:(analyse_instr func fa) func.pf_code;
  fa


let temp_to_named (func : ifunction) (fa : func_analysis) =
  (* We are assuming that no variable is used before it is assigned *)
  List.filter_mapi func.pf_code ~f:(fun _ iexpr ->
    match iexpr with
    | Iexp_copyvar (_, (Local, rname), (Local, aname)) ->
        let rstats = Hashtbl.find_exn fa.fa_var_stats rname in
        let astats = Hashtbl.find_exn fa.fa_var_stats aname in
        (* Both assigned once *)
        if rstats.vs_assign_count = 1 && astats.vs_assign_count = 1 then
          if astats.vs_temp then
            Some((aname, rname))
          else
            Some((rname, aname))
        else if astats.vs_assign_count = 1 && astats.vs_use_count = 1 then
          Some((aname, rname))
        (* Function arguments (never assigned *)
        else if astats.vs_assign_count = 0 && rstats.vs_assign_count = 1 then
          Some((rname, aname))
        else if astats.vs_assign_count = 0 && astats.vs_use_count = 1 then
          Some((rname, aname))
        else
          None
    | _ -> None)
