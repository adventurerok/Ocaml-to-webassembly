open Core_kernel
open Otwa_types

let parsestring str =
  let buf = Lexing.from_string str in
  Parse.implementation buf

let parseexpr str =
  let buf = Lexing.from_string str in
  Parse.expression buf


let printtype str =
  let parsed = parseexpr str in
  let typ = Type_expr.type_expr parsed in
  print_endline (Types.print typ)


let rec topLoop _ =
  let line = In_channel.input_line In_channel.stdin in
  begin
  (match line with
  | Some(str) -> printtype str
  | None -> print_endline "Oh no");
  topLoop ()
  end

let _ = topLoop ()
