open Core_kernel
open Intermediate_ast
open Intermediate_program

type func_analysis = {
  fa_name: string;
  fa_var_stats: (ivariable, var_stats) Hashtbl.t;

  (* from line, to lines (including next line if possible) *)
  fa_jump_table: (int, int list) Hashtbl.t;

  (* The arguments to the function, in order *)
  fa_args: ivariable list;

  (* start line number -> code for block *)
  mutable fa_basic_blocks: basic_block Int.Map.t
}

and basic_block = {
  bb_start_line: int;
  bb_end_line: int;
  bb_code: iinstruction array;
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
  (iinstruction_list_to_string (Array.to_list bb.bb_code)) ^ "\n}\n\n"

let func_analysis_to_string fa =
  "Function Analysis for " ^ fa.fa_name ^ "\n" ^
  (* "Variables: \n" ^
  (String.concat (List.map ~f:var_stats_to_string (Hashtbl.data fa.fa_var_stats))) ^ "\n" ^ *)
  "Basic Blocks: \n" ^
  (String.concat (List.map ~f:basic_block_to_string (Map.data fa.fa_basic_blocks))) ^ "\n"

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

(* Result and argument vars of an iinstruction *)
let instr_vars ?fill_closure_is_assign:(fcia = false) (iins : iinstruction) =
  match iins with
  | Iins_setvar (_, res, _) -> (Some(res), [])
  | Iins_copyvar (_, res, arg) -> (Some(res), [arg])
  | Iins_return (_, arg) -> (None, [arg])
  | Iins_unop (_, _, res, arg) -> (Some(res), [arg])
  | Iins_binop (_, _, res, arg1, arg2) -> (Some(res), [arg1; arg2])
  | Iins_newclosure (_, _, _, res) -> (Some(res), [])
  | Iins_fillclosure (_, a1, alst) ->
      if fcia then
        (Some(a1), a1 :: alst)
      else
        (None, (a1 :: alst))
  | Iins_callclosure (_, res, clo, arg) -> (Some(res), [clo; arg])
  | Iins_calldirect(res, _, _, args) -> (Some(res), args)
  | Iins_startblock _ -> (None, [])
  | Iins_endblock _ -> (None, [])
  | Iins_exitblock _ -> (None, [])
  | Iins_exitblockif (_, arg) -> (None, [arg])
  | Iins_startif (_, arg) -> (None, [arg])
  | Iins_else _ -> (None, [])
  | Iins_endif _ -> (None, [])
  | Iins_startloop (_, _) -> (None, [])
  | Iins_endloop (_, _) -> (None, [])
  | Iins_pushtuple (_, res, args) -> (Some(res), args)
  | Iins_loadtupleindex (_, _, res, arg) -> (Some(res), [arg])
  | Iins_pushconstruct (_, res, _, args) -> (Some(res), args)
  | Iins_loadconstructindex (_, _, res, arg) -> (Some(res), [arg])
  | Iins_loadconstructid (res, arg) -> (Some(res), [arg])
  | Iins_newbox (_, arg, res) -> (Some(res), [arg])
  | Iins_updatebox (_, arg, box) -> (None, [arg; box])
  | Iins_unbox (_, arg, res) -> (Some(res), [arg])
  | Iins_fail -> (None, [])

let can_side_effect (iins : iinstruction) =
  match iins with
  | Iins_setvar (_, _, _) -> false
  | Iins_copyvar (_, _, _) -> false
  | Iins_return (_, _) -> true
  | Iins_unop (_, _, _, _) -> false
  | Iins_binop (_, _, _, _, _) -> false
  | Iins_newclosure (_, _, _, _) -> false
  | Iins_fillclosure (_, _, _) -> false
  | Iins_callclosure (_, _, _, _) -> true
  | Iins_calldirect (_, _, _, _) -> true
  | Iins_startblock _ -> false
  | Iins_endblock _ -> false
  | Iins_exitblock _ -> false
  | Iins_exitblockif (_, _) -> false
  | Iins_startif (_, _) -> false
  | Iins_else _ -> false
  | Iins_endif _ -> false
  | Iins_startloop (_, _) -> false
  | Iins_endloop (_, _) -> false
  | Iins_pushtuple (_, _, _) -> false
  | Iins_loadtupleindex (_, _, _, _) -> false
  | Iins_pushconstruct (_, _, _, _) -> false
  | Iins_loadconstructindex (_, _, _, _) -> false
  | Iins_loadconstructid (_, _) -> false
  | Iins_newbox (_, _, _) -> false
  | Iins_updatebox (_, _, _) -> true
  | Iins_unbox (_, _, _) -> false
  | Iins_fail -> true

(* Variable analysis on instructions *)
let analyse_instr func globals state line (iins : iinstruction) =
  let res_opt, args = instr_vars iins in
  update_line_vars func globals state line (Option.to_list res_opt) args


let analyse_function_block func globals code =
  let all_vars = Vars.get_ivariables func.pf_vars in
  let cvar_count = List.length func.pf_cvars in
  let arg_vars = List.take all_vars (cvar_count + 1) in
  let fa = {
    fa_name = func.pf_name;
    fa_var_stats = Hashtbl.create (module IVariable);
    fa_jump_table = Hashtbl.create (module Int);
    fa_args = arg_vars;
    fa_basic_blocks = Int.Map.empty;
  }
  in
  (* Create a var stats for each var, to account for completely unused vars that don't show up later *)
  List.iter all_vars ~f:(fun var ->
    let vi = Option.value_exn (lookup_var_info func globals var) in
    Hashtbl.set fa.fa_var_stats ~key:var ~data:(new_var_stats var vi.vi_itype vi.vi_temp ())
  );
  (* Give each argument an assign at -1 *)
  List.iter arg_vars ~f:(fun var ->
    var_assigned func globals fa (-1) var
  );
  List.iteri ~f:(analyse_instr func globals fa) code;
  fa


let find_block_end name code =
  let opt = List.findi code ~f:(fun _ instr ->
    match instr with
    | Iins_else(n) -> String.equal name n
    | Iins_endif(n) -> String.equal name n
    | Iins_endblock(n) -> String.equal name n
    | Iins_endloop(n, c) -> (String.equal name n) || (String.equal name c)
    | _ -> false)
  in
  match opt with
  | Some(id, instr) ->
      (match instr with
      | Iins_endloop(_, c) ->
          if String.equal name c then
            (id, true)
          else
            (id, false)
      | _ -> (id, false))
  | None -> raise (AnalysisFailure ("Can't find end of " ^ name ^ " block"))

let compute_jump_table func fa =
  let rec loop line code =
    match code with
    | [] -> ()
    | instr :: code' ->
        let () =
          (match instr with
          | Iins_startif(block, _) ->
              let offset, _ = find_block_end block code' in
              Hashtbl.set fa.fa_jump_table ~key:line ~data:[line + 1; line + offset + 2]
          | Iins_endif(_) ->
              Hashtbl.set fa.fa_jump_table ~key:line ~data:[line + 1]
          | Iins_endblock(_) ->
              Hashtbl.set fa.fa_jump_table ~key:line ~data:[line + 1]
          | Iins_else(block) ->
              let offset, _ = find_block_end block code' in
              Hashtbl.add_multi fa.fa_jump_table ~key:line ~data:(line + offset + 2)
          | Iins_startloop(break, _) ->
              let offset, _ = find_block_end break code' in
              (if line > 1 then
                Hashtbl.add_multi fa.fa_jump_table ~key:(line - 1) ~data:line);
              Hashtbl.add_multi fa.fa_jump_table ~key:(line + offset + 1) ~data:line
          | Iins_exitblock(block) ->
              let offset, is_loop = find_block_end block code' in
              let true_line =
                if is_loop then
                  List.hd_exn (Hashtbl.find_exn fa.fa_jump_table (line + offset + 1))
                else
                  line + offset + 2
              in
              Hashtbl.add_multi fa.fa_jump_table ~key:line ~data:true_line
          | Iins_exitblockif(block, _) ->
              let offset, is_loop = find_block_end block code' in
              let true_line =
                if is_loop then
                  List.hd_exn (Hashtbl.find_exn fa.fa_jump_table (line + offset + 1))
                else
                  line + offset + 2
              in
              Hashtbl.set fa.fa_jump_table ~key:line ~data:[line + 1; true_line]
          | _ -> ()
          )
        in loop (line + 1) code'
  in loop 0 func.pf_code

let compute_basic_blocks func fa =
  compute_jump_table func fa;
  let jump_offsets = Int.Set.of_list (List.map ~f:(fun x -> x + 1) (Hashtbl.keys fa.fa_jump_table)) in
  let receive_offsets = Int.Set.of_list (List.concat (Hashtbl.data fa.fa_jump_table)) in
  let block_offsets = Set.union jump_offsets receive_offsets in
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
    fa.fa_basic_blocks <- Map.set fa.fa_basic_blocks ~key:start ~data:bb
  in
  let rec loop line code block_start block_rev =
    match code with
    | [] ->
        add_basic_block block_start block_rev
    | instr :: code' ->
        (* To account for the pred table computation next, we need to give it the right target line *)
        let true_start =
          if Set.mem block_offsets line then
            line
          else
            block_start
        in
        let () =
          (if Hashtbl.mem fa.fa_jump_table line then
            List.iter (Hashtbl.find_multi fa.fa_jump_table line) ~f:(fun target ->
              Hashtbl.add_multi pred_table ~key:target ~data:true_start))
        in
        if Set.mem block_offsets line then
          let () = add_basic_block block_start block_rev in
          loop (line + 1) code' line [instr]
        else
          loop (line + 1) code' block_start (instr :: block_rev)
  in
  loop 1 (List.tl_exn func.pf_code) 0 [List.hd_exn func.pf_code];
  fa.fa_basic_blocks <- Map.map fa.fa_basic_blocks ~f:(fun no_pred ->
    {
      no_pred with
      bb_pred = Hashtbl.find_multi pred_table no_pred.bb_start_line
    }
  );
  fa

let analyse_function (globals : Vars.vars) (func : ifunction) =
  let fa = analyse_function_block func globals func.pf_code in
  compute_basic_blocks func fa

let reaching_definitions fa =
  (* Each argument variable has a -1 definition corresponding to "from an argument" *)
  let start_func_defs =
    List.map fa.fa_args ~f:(fun iv -> (iv, (Int.Set.singleton (-1))))
    |> Map.of_alist_exn (module IVariable)
  in
  (* Hashtbl of line number to Map of ivariable -> Set of possible definition lines *)
  let in_defs = Hashtbl.create (module Int) in
  let out_defs = Hashtbl.create (module Int) in
  let modified = ref true in
  while !modified do
    modified := false;
    Map.iter fa.fa_basic_blocks ~f:(fun bb ->
      let pred_defs = List.filter_map bb.bb_pred ~f:(fun pred_line ->
        let pred_bb = Map.find_exn fa.fa_basic_blocks pred_line in
        Hashtbl.find out_defs pred_bb.bb_end_line)
      in
      (* A map so we always have 1 predecessor map.
       * For the first basic block this is set to the start of function definitons *)
      let base_map =
        if bb.bb_start_line = 0 then
          start_func_defs
        else
          (Map.empty (module IVariable))
      in
      let merged = List.reduce_exn (base_map :: pred_defs) ~f:(fun a b ->
        Map.merge_skewed a b ~combine:(fun ~key:_ s1 s2 -> Set.union s1 s2))
      in
      let old_defs_opt = Hashtbl.find in_defs bb.bb_start_line in
      let changed =
        match old_defs_opt with
        | Some(old_defs) ->
            not (Map.equal Set.equal old_defs merged)
        | None -> true
      in
      if changed then
        modified := true;
        Hashtbl.set in_defs ~key:bb.bb_start_line ~data:merged;
        for index = 0 to (Array.length bb.bb_code) - 1 do
          let line = bb.bb_start_line + index in
          let start_def = Hashtbl.find_exn in_defs line in
          let assign_opt, _ = instr_vars (Array.get bb.bb_code index) in
          let end_def =
            match assign_opt with
            | Some(assign) ->
                Map.set start_def ~key:assign ~data:(Int.Set.singleton line)
            | None ->
                start_def
          in
          Hashtbl.set out_defs ~key:line ~data:end_def;
          (if index < Array.length bb.bb_code - 1 then
            Hashtbl.set in_defs ~key:(line + 1) ~data:end_def)

        done
    )
  done;
  in_defs

(* Finds a unique reaching definition for a variable, or none *)
(* line_defs = Map of reaching definitions for a specific line *)
let unique_reaching_definition line_defs var =
  if ivariable_is_global var then
    (* No guarantees for global variables *)
    None
  else
    let var_defs_opt = Map.find line_defs var in
    match var_defs_opt with
    | Some(var_defs) ->
        if Set.length var_defs = 1 then
          Set.choose var_defs
        else None
    | None -> None


let invert_reaching_definitions fa rd =
  (* Maps definition line to set of possible used lines *)
  let du = Hashtbl.create (module Int) in
  Map.iter fa.fa_basic_blocks ~f:(fun bb ->
    for index = 0 to (Array.length bb.bb_code) - 1 do
      (* Looping over each line in the function *)
      let line = bb.bb_start_line + index in
      (if not (Hashtbl.mem du line) then
        Hashtbl.set du ~key:line ~data:Int.Set.empty);
      let line_defs = Hashtbl.find_exn rd line in
      (* Find the variables used on this line (not those defined) *)
      let _, used = instr_vars (Array.get bb.bb_code index) in
      List.iter used ~f:(fun used_var ->
        (* For each used variable, find where it could have been defined *)
        let defs = Map.find_exn line_defs used_var in
        List.iter defs ~f:(fun def ->
          (* Give our current line a usage from that definition site *)
          let prev_usages = Option.value ~default:Int.Set.empty (Hashtbl.find du def) in
          let new_usages = Set.add prev_usages line in
          Hashtbl.set du ~key:def ~data:new_usages
        )
      )
    done
  );
  du

(* We have three options, we don't have X, we have a positive X or a negative X *)
type var_negate_set = {
  pos: (ivariable, IVariable.comparator_witness) Set.t;
  neg: (ivariable, IVariable.comparator_witness) Set.t
}

let vns_empty = {
  pos = Set.empty (module IVariable);
  neg = Set.empty (module IVariable);
}

(* AC: we have a new definition after the copy *)
let vns_negate_positive vns =
  let neg_new = Set.union vns.neg vns.pos in
  {
    pos = vns_empty.pos;
    neg = neg_new
  }

let vns_add_positive vns item =
  let pos_new = Set.add vns.pos item in
  let neg_new = Set.remove vns.neg item in
  {
    pos = pos_new;
    neg = neg_new;
  }

let vns_mem vns item =
  Set.mem vns.pos item


let vns_merge vns1 vns2 =
  let neg_new = Set.union vns1.neg vns2.neg in
  let pos_new = Set.union vns1.pos vns2.pos in
  {
    pos = Set.diff pos_new neg_new;
    neg = neg_new
  }

let vns_equal vns1 vns2 =
  (Set.equal vns1.pos vns2.pos) && (Set.equal vns1.neg vns2.neg)

(* For each line and variable, the set of copy instruction targets known to have copied the current version of the variable *)
(* A reaching definitions analysis is required for the target as well to determine if the copy is still valid *)
let active_copies fa =
  (* Hashtbl of line number to Map of ivariable -> VNS *)
  let in_defs = Hashtbl.create (module Int) in
  let out_defs = Hashtbl.create (module Int) in
  let modified = ref true in
  while !modified do
    modified := false;
    Map.iter fa.fa_basic_blocks ~f:(fun bb ->
      let pred_defs = List.filter_map bb.bb_pred ~f:(fun pred_line ->
        let pred_bb = Map.find_exn fa.fa_basic_blocks pred_line in
        Hashtbl.find out_defs pred_bb.bb_end_line)
      in
      let merged =
        (* Now we intersect *)
        if List.length pred_defs > 0 then
          List.reduce_exn pred_defs ~f:(fun a b ->
            (* Intersection requires removing keys only present in one *)
            Map.merge_skewed a b ~combine:(fun ~key:_ vns1 vns2 ->
              vns_merge vns1 vns2
            )

          )
        else
          Map.empty (module IVariable)
      in
      let old_defs_opt = Hashtbl.find in_defs bb.bb_start_line in
      let changed =
        match old_defs_opt with
        | Some(old_defs) ->
            not (Map.equal vns_equal old_defs merged)
        | None -> true
      in
      if changed then
        modified := true;
        Hashtbl.set in_defs ~key:bb.bb_start_line ~data:merged;
        for index = 0 to (Array.length bb.bb_code) - 1 do
          let line = bb.bb_start_line + index in
          let start_def = Hashtbl.find_exn in_defs line in
          let assign_opt, _ = instr_vars (Array.get bb.bb_code index) in
          let copied_opt =
            match Array.get bb.bb_code index with
            | Iins_copyvar(_, target, arg) ->
                Some((target, arg))
            | _ -> None
          in
          let middle_def =
            match assign_opt with
            | Some(assign) ->
                let old_vns = Option.value ~default:(vns_empty) (Map.find start_def assign) in
                let new_vns = vns_negate_positive old_vns in
                Map.set start_def ~key:assign ~data:new_vns
            | None ->
                start_def
          in let end_def =
            match copied_opt with
            | Some((target, copy)) ->
                let old_locs = Option.value ~default:(vns_empty) (Map.find middle_def copy) in
                let new_locs = vns_add_positive old_locs target in
                Map.set middle_def ~key:copy ~data:new_locs
            | None ->
                middle_def
          in
          Hashtbl.set out_defs ~key:line ~data:end_def;
          (if index < Array.length bb.bb_code - 1 then
            Hashtbl.set in_defs ~key:(line + 1) ~data:end_def)

        done
    )
  done;
  in_defs


let live_variables fa =
  (* Hashtbl of line number to Set of live ivariables *)
  let in_live = Hashtbl.create (module Int) in
  let out_live = Hashtbl.create (module Int) in
  let modified = ref true in
  while !modified do
    modified := false;
    Map.iter fa.fa_basic_blocks ~f:(fun bb ->
      let next_live = List.filter_map bb.bb_next ~f:(fun next_line ->
        let next_bb_opt = Map.find fa.fa_basic_blocks next_line in
        match next_bb_opt with
        | Some(next_bb) ->
            Hashtbl.find in_live next_bb.bb_start_line
        | None -> None)
      in
      (* A map so we always have 1 predecessor map.
       * For the first basic block this is set to the start of function definitons *)
      let base_set = (Set.empty (module IVariable)) in
      let merged = List.reduce_exn (base_set :: next_live) ~f:Set.union in
      let old_live_opt = Hashtbl.find out_live bb.bb_end_line in
      let changed =
        match old_live_opt with
        | Some(old_live) ->
            not (Set.equal old_live merged)
        | None -> true
      in
      if changed then
        modified := true;
        Hashtbl.set out_live ~key:bb.bb_end_line ~data:merged;
        for back_index = 0 to (Array.length bb.bb_code) - 1 do
          let index = (Array.length bb.bb_code - 1) - back_index in
          let line = bb.bb_start_line + index in
          let end_line_live = Hashtbl.find_exn out_live line in
          let assign_opt, used_vars = instr_vars (Array.get bb.bb_code index) in
          let inter_live =
            match assign_opt with
            | Some(assign) ->
                Set.remove end_line_live assign
            | None ->
                end_line_live
          in
          let start_line_live =
            Set.union inter_live (Set.of_list (module IVariable) used_vars)
          in
          Hashtbl.set in_live ~key:line ~data:start_line_live;
          (if index > 0 then
            Hashtbl.set out_live ~key:(line - 1) ~data:start_line_live)

        done
    )
  done;
  (in_live, out_live)


let print_reaching_definitions rd =
  let rd_map = Map.of_alist_exn (module Int) (Hashtbl.to_alist rd) in
  Stdio.print_endline ("\nReaching definitions:\n");
  Map.iteri rd_map ~f:(fun ~key:k ~data:d ->
    let var_strs =
      Map.to_alist d
      |> List.map ~f:(fun (vr, dfs) ->
          (ivariable_to_string vr) ^ ": " ^ (String.concat ~sep:"," (List.map (Set.to_list dfs) ~f:Int.to_string)))
    in
    let out = (Int.to_string k) ^ " --> " ^ (String.concat ~sep:"; " var_strs) in
    Stdio.print_endline out
  )


let print_live_variables (func : ifunction) lva =
  Stdio.print_endline ("\nLive variables:\n");
  List.iteri func.pf_code ~f:(fun line iins ->
    let live = Hashtbl.find_exn lva line in
    let var_strs = List.map ~f:ivariable_to_string (Set.to_list live) in
    let out = (Int.to_string line) ^ " :  " ^ (iinstruction_to_string iins) ^ " --> " ^ (String.concat ~sep:", " var_strs) in
    Stdio.print_endline out
  )



let temp_to_named (func : ifunction) (fa : func_analysis) =
  (* We are assuming that no variable is used before it is assigned *)
  (* Only map each variable once, so multi cycle if we want more *)
  let already_mapped = Hash_set.create (module IVariable) in
  List.filter_mapi func.pf_code ~f:(fun _ iins ->
    let mapping =
      match iins with
      | Iins_copyvar (_, ((Local, _) as rvar), ((Local, _) as avar)) ->
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
      | Iins_copyvar (_, ((Global, _) as gvar), ((Local, _) as avar)) ->
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
