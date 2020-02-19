open Core_kernel
open Intermediate_ast
open Intermediate_program

type func_analysis = {
  fa_name: string;
  fa_var_stats: (ivariable, var_stats) Hashtbl.t;

  (* from line, to lines (including next line if possible) *)
  fa_jump_table: (int, int list) Hashtbl.t;

  (* start line number -> code for block *)
  mutable fa_basic_blocks: (int, basic_block) Map.Poly.t
}

and basic_block = {
  bb_start_line: int;
  bb_end_line: int;
  bb_code: iexpression array;
  mutable bb_next: int list;
  mutable bb_pred: int list;
}

and var_stats = {
  vs_name: string;
  vs_scope: iscope;
  vs_var: ivariable;
  vs_type: itype;
  vs_temp: bool;
  mutable vs_use_count: int;
  mutable vs_assign_count: int;
  mutable vs_first_assign: int;
  mutable vs_last_assign: int;
  mutable vs_first_use: int;
  mutable vs_last_use: int;
  mutable vs_assign_locs: Int.Set.t;
  mutable vs_use_locs: Int.Set.t;
}

let variable_next_use fa name line =
  match Hashtbl.find fa.fa_var_stats name with
  | Some(vs) ->
      Set.binary_search vs.vs_use_locs ~compare:Int.compare `First_strictly_greater_than line
  | None -> None

let variable_previous_use fa name line =
  match Hashtbl.find fa.fa_var_stats name with
  | Some(vs) ->
      Set.binary_search vs.vs_use_locs ~compare:Int.compare `Last_strictly_less_than line
  | None -> None

let variable_next_assign fa name line =
  match Hashtbl.find fa.fa_var_stats name with
  | Some(vs) ->
      Set.binary_search vs.vs_assign_locs ~compare:Int.compare `First_strictly_greater_than line
  | None -> None

let variable_previous_assign fa name line =
  match Hashtbl.find fa.fa_var_stats name with
  | Some(vs) ->
      Set.binary_search vs.vs_assign_locs ~compare:Int.compare `Last_strictly_less_than line
  | None -> None


exception AnalysisFailure of string

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
  "assign_locs = " ^ (String.concat ~sep:"," (List.map ~f:Int.to_string (Set.to_list vs.vs_assign_locs))) ^ "\n" ^
  "use_locs = " ^ (String.concat ~sep:"," (List.map ~f:Int.to_string (Set.to_list vs.vs_use_locs))) ^ " }\n"

let basic_block_to_string bb =
  "{ bb\n" ^
  "start_line = " ^ (Int.to_string bb.bb_start_line) ^ "\n" ^
  "end_line = " ^ (Int.to_string bb.bb_end_line) ^ "\n" ^
  "next = " ^ (String.concat ~sep:"," (List.map ~f:Int.to_string bb.bb_next)) ^ "\n" ^
  "pred = " ^ (String.concat ~sep:"," (List.map ~f:Int.to_string bb.bb_pred)) ^ "\n" ^
  "code = \n" ^
  (iexpression_list_to_string (Array.to_list bb.bb_code)) ^ "\n}\n\n"

let func_analysis_to_string fa =
  "Function Analysis for " ^ fa.fa_name ^ "\n" ^
  "Variables: \n" ^
  (String.concat (List.map ~f:var_stats_to_string (Hashtbl.data fa.fa_var_stats))) ^ "\n" ^
  "Basic Blocks: \n" ^
  (String.concat (List.map ~f:basic_block_to_string (Map.Poly.data fa.fa_basic_blocks))) ^ "\n"

let new_var_stats (scope, name) typ temp () =
  {
    vs_name = name;
    vs_scope = scope;
    vs_var = (scope, name);
    vs_type = typ;
    vs_temp = temp;
    vs_use_count = 0;
    vs_assign_count = 0;
    vs_first_assign = -1;
    vs_last_assign = -1;
    vs_first_use = -1;
    vs_last_use = -1;
    vs_assign_locs = Int.Set.empty;
    vs_use_locs = Int.Set.empty;
  }

let lookup_var_info func globals (scope, name) =
  match scope with
  | Global -> Vars.lookup_var_info globals name
  | Local -> Vars.lookup_var_info func.pf_vars name

let var_assigned func globals state line var =
  let vi = Option.value_exn ~message:("Unknown var " ^ (ivariable_to_string var)) (lookup_var_info func globals var) in
  let vs = Hashtbl.find_or_add state.fa_var_stats var ~default:(new_var_stats var vi.vi_itype vi.vi_temp) in
  vs.vs_assign_count <- vs.vs_assign_count + 1;
  (if vs.vs_first_assign = -1 then vs.vs_first_assign <- line);
  vs.vs_last_assign <- line;
  vs.vs_assign_locs <- Set.add vs.vs_assign_locs line

let var_used func globals state line var =
  let vi = Option.value_exn (lookup_var_info func globals var) in
  let vs = Hashtbl.find_or_add state.fa_var_stats var ~default:(new_var_stats var vi.vi_itype vi.vi_temp) in
  vs.vs_use_count <- vs.vs_use_count + 1;
  (if vs.vs_first_use = -1 then vs.vs_first_use <- line);
  vs.vs_last_use <- line;
  vs.vs_use_locs <- Set.add vs.vs_use_locs line

let update_line_vars func globals state line assigned used =
  List.iter ~f:(var_assigned func globals state line) assigned;
  List.iter ~f:(var_used func globals state line) used


(* Variable analysis on instructions *)
let analyse_instr func globals state line (iexpr : iexpression) =
  let ulv_filled = update_line_vars func globals state line in
  match iexpr with
  | Iexp_setvar (_, res, _) -> ulv_filled [res] []
  | Iexp_copyvar (_, res, arg) -> ulv_filled [res] [arg]
  | Iexp_return (_, arg) -> ulv_filled [] [arg]
  | Iexp_unop (_, _, res, arg) -> ulv_filled [res] [arg]
  | Iexp_binop (_, _, res, arg1, arg2) -> ulv_filled [res] [arg1; arg2]
  | Iexp_newclosure (_, _, _, res) -> ulv_filled [res] []
  | Iexp_fillclosure (_, a1, alst) -> ulv_filled [] (a1 :: alst)
  | Iexp_callclosure (_, res, clo, arg) -> ulv_filled [res] [clo; arg]
  | Iexp_calldirect(res, _, _, args) -> ulv_filled [res] args
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


let analyse_function_block func globals code =
  let fa = {
    fa_name = func.pf_name;
    fa_var_stats = Hashtbl.create (module IVariable);
    fa_jump_table = Hashtbl.create (module Int);
    fa_basic_blocks = Map.Poly.empty;
  }
  in
  List.iteri ~f:(analyse_instr func globals fa) code;
  fa


let find_block_end name code =
  let opt = List.findi code ~f:(fun _ instr ->
    match instr with
    | Iexp_else(n) -> String.equal name n
    | Iexp_endif(n) -> String.equal name n
    | Iexp_endblock(n) -> String.equal name n
    | Iexp_endloop(n, _) -> String.equal name n
    | _ -> false)
  in
  match opt with
  | Some(id, _) -> id
  | None -> raise (AnalysisFailure ("Can't find end of " ^ name ^ " block"))

let compute_jump_table func fa =
  let rec loop line code =
    match code with
    | [] -> ()
    | instr :: code' ->
        let () =
          (match instr with
          | Iexp_startif(block, _) ->
              let offset = find_block_end block code' in
              Hashtbl.set fa.fa_jump_table ~key:line ~data:[line + 1; line + offset + 2]
          | Iexp_else(block) ->
              let offset = find_block_end block code' in
              Hashtbl.add_multi fa.fa_jump_table ~key:line ~data:(line + offset + 2)
          | Iexp_startloop(break, _) ->
              let offset = find_block_end break code' in
              Hashtbl.add_multi fa.fa_jump_table ~key:(line + offset + 1) ~data:line
          | Iexp_exitblock(block) ->
              let offset = find_block_end block code' in
              Hashtbl.add_multi fa.fa_jump_table ~key:line ~data:(line + offset + 2)
          | Iexp_exitblockif(block, _) ->
            let offset = find_block_end block code' in
            Hashtbl.set fa.fa_jump_table ~key:line ~data:[line + 1; line + offset + 2]
          | _ -> ()
          )
        in loop (line + 1) code'
  in loop 0 func.pf_code

let compute_basic_blocks func fa =
  compute_jump_table func fa;
  let jump_offsets = Set.Poly.of_list (List.map ~f:(fun x -> x + 1) (Hashtbl.keys fa.fa_jump_table)) in
  let receive_offsets = Set.Poly.of_list (List.concat (Hashtbl.data fa.fa_jump_table)) in
  let block_offsets = Set.Poly.union jump_offsets receive_offsets in
  let pred_table = Hashtbl.create (module Int) in
  let add_basic_block start code_rev =
    let end_line = start + (List.length code_rev) - 1 in
    let bb = {
      bb_start_line = start;
      bb_end_line = end_line;
      bb_code = Array.of_list (List.rev code_rev);
      bb_next = Option.value (Hashtbl.find fa.fa_jump_table end_line) ~default:[end_line + 1];
      bb_pred = []
    }
    in
    fa.fa_basic_blocks <- Map.Poly.set fa.fa_basic_blocks ~key:start ~data:bb
  in
  let rec loop line code block_start block_rev =
    match code with
    | [] ->
        add_basic_block block_start block_rev
    | instr :: code' ->
        let () =
          (if Hashtbl.mem fa.fa_jump_table line then
            List.iter (Hashtbl.find_multi fa.fa_jump_table line) ~f:(fun target ->
              Hashtbl.add_multi pred_table ~key:target ~data:block_start))
        in
        if Set.Poly.mem block_offsets line then
          let () = add_basic_block block_start block_rev in
          loop (line + 1) code' line [instr]
        else
          loop (line + 1) code' block_start (instr :: block_rev)
  in
  loop 1 (List.tl_exn func.pf_code) 0 [List.hd_exn func.pf_code];
  fa.fa_basic_blocks <- Map.Poly.map fa.fa_basic_blocks ~f:(fun no_pred ->
    {
      no_pred with
      bb_pred = Hashtbl.find_multi pred_table no_pred.bb_start_line
    }
  );
  fa

let analyse_function (globals : Vars.vars) (func : ifunction) =
  let fa = analyse_function_block func globals func.pf_code in
  compute_basic_blocks func fa


let temp_to_named (func : ifunction) (fa : func_analysis) =
  (* We are assuming that no variable is used before it is assigned *)
  (* Only map each variable once, so multi cycle if we want more *)
  let already_mapped = Hash_set.create (module IVariable) in
  List.filter_mapi func.pf_code ~f:(fun _ iexpr ->
    let mapping =
      match iexpr with
      | Iexp_copyvar (_, ((Local, _) as rvar), ((Local, _) as avar)) ->
          let rstats = Hashtbl.find_exn fa.fa_var_stats rvar in
          let astats = Hashtbl.find_exn fa.fa_var_stats avar in
          if Hash_set.mem already_mapped rvar || Hash_set.mem already_mapped avar then
            None
          else if rstats.vs_assign_count = 1 && astats.vs_assign_count = 1 then
          (* Both assigned once *)
            if astats.vs_temp then
              Some((avar, rvar))
            else
              Some((rvar, avar))
          else if astats.vs_assign_count = 1 && astats.vs_use_count = 1 then
            Some((avar, rvar))
          (* Function arguments (never assigned *)
          else if astats.vs_assign_count = 0 && rstats.vs_assign_count = 1 then
            Some((rvar, avar))
          else if astats.vs_assign_count = 0 && astats.vs_use_count = 1 then
            Some((rvar, avar))
          else
            None
      | Iexp_copyvar (_, ((Global, _) as gvar), ((Local, _) as avar)) ->
          let gstats = Hashtbl.find_exn fa.fa_var_stats gvar in
          let astats = Hashtbl.find_exn fa.fa_var_stats avar in
          if Hash_set.mem already_mapped avar then
            None
          else if gstats.vs_assign_count = 1 && astats.vs_assign_count = 1 then
            Some((avar, gvar))
          else None
      | _ -> None
    in
    let () =
      match mapping with
      | Some(o, n) ->
          Hash_set.add already_mapped o;
          Hash_set.add already_mapped n
      | None -> ()
    in
    mapping
  )
