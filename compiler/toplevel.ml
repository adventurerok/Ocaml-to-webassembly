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
  let (funcs, fast) = Functions.func_transform_structure tast in
  Stdio.print_endline (Typed_ast.tstructure_to_string fast);
  Functions.print_func_datas funcs;
  let code_list = Intermediate.transform_structure (Map.Poly.empty) fast in
  let str = Intermediate_ast.iexpression_list_to_string code_list in
  Stdio.print_endline str;
  List.iter funcs ~f:(fun fd ->
    Stdio.print_endline ("\nFunction " ^ fd.fd_name ^ " code:");
    let codes = Intermediate.transform_expr (Map.Poly.empty) fd.fd_expr in
    let cstr = Intermediate_ast.iexpression_list_to_string codes in
    Stdio.print_endline cstr)

let () =
  if (Array.length Sys.argv) = 2 then
    openfile Sys.argv.(1)
  else
    topLoop Context.empty_with_lists
