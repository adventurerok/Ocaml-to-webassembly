open Core_kernel
open Otwa_transform
open Intermediate_ast

type string_int_map = (string, int) Map.Poly.t

(* Malloc will take an int number of bytes to allocate, and return a pointer to the new memory *)
let malloc_id = "$malloc"

exception CodegenFailure of string

let itype_to_watype it =
  match it with
  | It_poly -> "i32"
  | It_bool -> "i32"
  | It_int -> "i32"
  | It_pointer -> "i32"
  | It_float -> "f32"
  | It_unit -> "i32"
  | It_none -> raise (CodegenFailure "It_none cannot be converted directly to wasm")

let itype_to_waresult it =
  match it with
  | It_none -> ""
  | _ -> "(result " ^ (itype_to_watype it) ^ ")"


let itype_size it =
  match it with
  | It_poly -> 4
  | It_bool -> 4
  | It_int -> 4
  | It_pointer -> 4
  | It_float -> 4
  | It_unit -> 4
  | It_none -> 0

let poly_size = itype_size It_poly
let poly_watype = itype_to_watype It_poly

let ituptype_size itt =
  Option.value ~default:0 (List.reduce (List.map itt ~f:itype_size) ~f:(+))


let wrapper_func_name func_name =
  "$wrap-" ^ (String.chop_prefix_exn func_name ~prefix:"$")

