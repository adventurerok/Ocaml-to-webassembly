open Core_kernel
open Otwa_types

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

let _ = topLoop Context.empty_with_lists
