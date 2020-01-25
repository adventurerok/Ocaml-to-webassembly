open Core_kernel
open Otwa_types
open Otwa_transform
open Otwa_codegen

let parsestring str =
  let buf = Lexing.from_string str in
  Parse.implementation buf

let openfile name debug output =
  let alltext = In_channel.with_file name ~f:In_channel.input_all in
  let parsed = parsestring alltext in
  let (ctx, tast) = Type_expr.type_structure Context.empty_lists_refs parsed in
  if debug then (
    Context.print ctx;
    Stdio.print_endline (Typed_ast.tstructure_to_string tast));
  let iprog = Intermediate.transform_program ~debug:debug ctx tast in
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
  let output_ref = ref "" in
  let input_ref = ref "" in
  let cmd_spec =
    [("-debug", Arg.Set(debug_ref), "Enable debug mode");
     ("-output", Arg.Set_string(output_ref), "Output to named file instead of standard out")]
  in
  let anon_fun str =
    input_ref := str
  in
  Arg.parse cmd_spec anon_fun "Usage: [options] input_file";
  openfile !input_ref !debug_ref !output_ref
