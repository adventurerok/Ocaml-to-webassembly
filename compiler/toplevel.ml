open Core_kernel
open Otwa_base
open Otwa_types
open Otwa_transform
open Otwa_codegen

let parsestring str =
  let buf = Lexing.from_string str in
  Parse.implementation buf

let openfile name debug output =
  let alltext = In_channel.with_file name ~f:In_channel.input_all in
  let parsed = parsestring alltext in
  let tresult = Type_expr.type_structure Context.empty_lists_refs parsed in
  if debug then (
    Context.print tresult.tres_context;
    Stdio.print_endline (Typed_ast.tstructure_to_string tresult.tres_structure));
  let iprog = Intermediate.transform_program ~debug:debug
                      tresult.tres_context tresult.tres_next_var tresult.tres_structure
  in
  if debug then (
    let pstr = Intermediate_program.iprogram_to_string iprog in
    Stdio.print_endline pstr);
  let wa_code = Webassembly.iprogram_to_module iprog in
  (if debug then Stdio.print_endline "\n\n");
  match output with
  | "" -> Stdio.print_endline wa_code
  | _ ->
      Out_channel.with_file output ~f:(fun chan ->
        Out_channel.output_string chan wa_code)

let () =
  let debug_ref = ref false in
  let trace_ref = ref false in
  let optimise_stack_codegen_ref = ref true in
  let optimise_direct_call_gen_ref = ref true in
  let optimise_alias_elimination_ref = ref true in
  let optimise_tuple_loads_ref = ref true in
  let optimise_dead_code_ref = ref true in
  let output_ref = ref "" in
  let input_ref = ref "" in
  let cmd_spec =
    [("-debug", Arg.Set(debug_ref), "Enable debug mode");
     ("-trace", Arg.Set(trace_ref), "Enable debug and trace mode");
     ("-no_stack_codegen", Arg.Clear(optimise_stack_codegen_ref), "Disable stack codegen");
     ("-no_direct_calls", Arg.Clear(optimise_direct_call_gen_ref), "Disable direct call optimisations");
     ("-no_alias_elimination", Arg.Clear(optimise_alias_elimination_ref), "Disable alias elimination");
     ("-no_tuple_loads", Arg.Clear(optimise_tuple_loads_ref), "Disable tuple load optimisation");
     ("-no_dead_code", Arg.Clear(optimise_dead_code_ref), "Disable dead code elimination");
     ("-output", Arg.Set_string(output_ref), "Output to named file instead of standard out")]
  in
  let anon_fun str =
    input_ref := str
  in
  Arg.parse cmd_spec anon_fun "Usage: [options] input_file";
  Config.global.debug <- !debug_ref || !trace_ref;
  Config.global.trace <- !trace_ref;
  Config.global.optimise_stack_codegen <- !optimise_stack_codegen_ref;
  Config.global.optimise_direct_call_gen <- !optimise_direct_call_gen_ref;
  Config.global.optimise_alias_elimination <- !optimise_alias_elimination_ref;
  Config.global.optimise_tuple_loads <- !optimise_tuple_loads_ref;
  Config.global.optimise_dead_code <- !optimise_dead_code_ref;
  openfile !input_ref (!debug_ref || !trace_ref) !output_ref
