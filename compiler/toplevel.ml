open Core_kernel
open Otwa_types

let parsestring str =
  let buf = Lexing.from_string str in
  Parse.implementation buf

let parseexpr str =
  let buf = Lexing.from_string str in
  Parse.expression buf


let printinfer str =
  let parsed = parseexpr str in
  let ctx = Context.empty in
  let (unip, typ) = Type_expr.infer_expr ctx parsed in
  print_endline ((Types.string_of_uni_pair_list unip) ^ (Types.string_of_scheme_type typ))

let printtype str =
  let parsed = parseexpr str in
  let ctx = Context.empty in
  let typ = Type_expr.type_expr ctx parsed in
  Stdio.print_endline ((Types.string_of_scheme_type typ))

let structype ctx str =
  let parsed = parsestring str in
  let nctx = Type_expr.type_structure ctx parsed in
  (Context.print nctx; nctx)

let rec topLoop ctx =
  let line = In_channel.input_line In_channel.stdin in
  let ctx' =
    match line with
    | Some(str) -> structype ctx str
    | None -> (print_endline "Oh no"; ctx)
  in topLoop ctx'

let _ = topLoop Context.empty_with_lists
