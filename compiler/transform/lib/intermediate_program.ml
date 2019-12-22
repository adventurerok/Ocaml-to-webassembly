open Core_kernel
open Intermediate_ast

(* Because this depends on Vars, and vars depends on intermediate_ast *)
(* Hence this has it's own file and not Intermediate_ast *)
(* TODO if the itype stuff had it's own file instead that might be neater! *)

type iprogram = {
  (* Map of function name to function data *)
  prog_functions: (string, ifunction) Map.Poly.t;

  (* All global variables *)
  prog_globals: Vars.vars;

  (* Name of initialization function *)
  prog_initfunc: string
}

and ifunction = {
  (* Name of function *)
  pf_name: string;

  (* All variables of function *)
  pf_vars: Vars.vars;

  (* Code of function *)
  pf_code: iexpression list;

  (* Type of function *)
  pf_type: iftype;

  (* Closure variables in order with types *)
  pf_cvars: (string * itype) list
}


let ifunction_to_string ifunc =
  "Function " ^ ifunc.pf_name ^ ":\n" ^
  "-type: " ^ (iftype_to_string ifunc.pf_type) ^ "\n" ^
  "-vars:\n" ^ (Vars.vars_to_string ifunc.pf_vars) ^ "\n" ^
  "-code:\n" ^ (iexpression_list_to_string ifunc.pf_code)

let iprogram_to_string iprog =
  "Program\n" ^
  "-global_vars:\n" ^ (Vars.vars_to_string iprog.prog_globals) ^ "\n" ^
  "-init: " ^ iprog.prog_initfunc ^ "\n" ^
  "-functions:\n\n" ^
  (let (_, func_list) = List.unzip (Map.Poly.to_alist iprog.prog_functions) in
  String.concat ~sep:"\n\n" (List.map func_list ~f:ifunction_to_string))
