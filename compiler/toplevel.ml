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

let structype str =
  let parsed = parsestring str in
  let ctx = Context.empty in
  let nctx = Type_expr.type_structure ctx parsed in
  let varlist = Context.get_var_list nctx in
  let printvar (v,t) =
    let tstr = Types.string_of_scheme t in
    print_endline (v ^ ": " ^ tstr)
  in (List.iter varlist ~f:printvar)

let rec topLoop _ =
  let line = In_channel.input_line In_channel.stdin in
  begin
  (match line with
  | Some(str) -> structype str
  | None -> print_endline "Oh no");
  topLoop ()
  end

let _ = topLoop ()
