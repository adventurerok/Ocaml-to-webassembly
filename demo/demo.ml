open Core_kernel
open Proj_inc_nums

let parsestring str =
  let buf = Lexing.from_string str in
  Parse.implementation buf

let ppf = Format.err_formatter


let printstring str =
  let parsed = parsestring str in
  let parsed' = Inc_nums.inc_nums parsed in
  let text = Pprintast.string_of_structure parsed' in
  print_endline text


let rec topLoop _ =
  let line = In_channel.input_line In_channel.stdin in
  begin
  (match line with
  | Some(str) -> printstring str
  | None -> print_endline "Oh no");
  topLoop ()
  end

let _ = topLoop ()
