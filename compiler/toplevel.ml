open Core_kernel
open Otwa_types
open Otwa_transform

let parsestring str =
  let buf = Lexing.from_string str in
  Parse.implementation buf

let parseexpr str =
  let buf = Lexing.from_string str in
  Parse.expression buf

let structype ctx str =
  let parsed = parsestring str in
  let (nctx, ast) = Type_expr.type_structure ctx parsed in
  Context.print nctx;
  Stdio.print_endline (Typed_ast.tstructure_to_string ast);
  nctx

let rec topLoop ctx =
  let line = In_channel.input_line In_channel.stdin in
  let ctx' =
    match line with
    | Some(str) -> structype ctx str
    | None -> (print_endline "Oh no"; ctx)
  in topLoop ctx'

let openfile name =
  let alltext = In_channel.with_file name ~f:In_channel.input_all in
  let parsed = parsestring alltext in
  let (ctx, tast) = Type_expr.type_structure Context.empty_with_lists parsed in
  Context.print ctx;
  Stdio.print_endline (Typed_ast.tstructure_to_string tast);
  let iprog = Intermediate.transform_program ~debug:true ctx tast in
  let pstr = Intermediate_program.iprogram_to_string iprog in
  Stdio.print_endline pstr

let () =
  if (Array.length Sys.argv) = 2 then
    openfile Sys.argv.(1)
  else
    topLoop Context.empty_with_lists
