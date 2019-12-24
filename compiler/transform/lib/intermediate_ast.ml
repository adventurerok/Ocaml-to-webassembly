open Core_kernel
open Otwa_types
open Types

type itype =
  | It_bool
  | It_int
  | It_float
  | It_pointer
  | It_unit
  | It_none
  [@@deriving sexp_of, equal, enumerate]

let itype_to_string (it : itype) =
  match it with
  | It_bool -> "bool"
  | It_int -> "int"
  | It_float -> "float"
  | It_pointer -> "pointer"
  | It_unit -> "unit"
  | It_none -> "none"

type iftype = itype * itype
[@@deriving sexp_of, equal, enumerate]

let iftype_to_string (a,b) =
  (itype_to_string a) ^ " -> " ^ (itype_to_string b)

type ituptype = itype list
[@@deriving sexp_of, equal]

let ituptype_to_string tt =
  "(" ^ (String.concat ~sep:", " (List.map tt ~f:itype_to_string)) ^ ")"

exception BadType of string

let stoitype (typ : scheme_type) =
  match typ with
  | T_var(_) -> raise (BadType "Cannot convert type variable into inter type")
  | T_val(V_unit) -> It_unit
  | T_val(V_int) -> It_int
  | T_val(V_bool) -> It_bool
  | T_tuple _ -> It_pointer
  | T_constr (_, _) -> It_pointer
  | T_func (_, _) -> It_pointer (* Closure pointer *)

let functoitype (typ : scheme_type) =
  match typ with
  | T_func(a,b) -> (stoitype a, stoitype b)
  | _ -> raise (BadType "Expecting function type")

let tupletoitype (typ : scheme_type) =
  match typ with
  | T_tuple(ls) -> List.map ls ~f:stoitype
  | _ -> raise (BadType "Expecting tuple type")

type ibinop =
  Ibin_add
| Ibin_sub
| Ibin_mul
| Ibin_div
| Ibin_rem
| Ibin_and
| Ibin_or
| Ibin_eq
| Ibin_ne
| Ibin_lt
| Ibin_le
| Ibin_gt
| Ibin_ge
[@@deriving sexp_of, equal]

let ibinop_to_string (ib : ibinop) =
  match ib with
  | Ibin_add -> "add"
  | Ibin_sub -> "sub"
  | Ibin_mul -> "mul"
  | Ibin_div -> "div"
  | Ibin_rem -> "rem"
  | Ibin_and -> "add"
  | Ibin_or -> "or"
  | Ibin_eq -> "eq"
  | Ibin_ne -> "ne"
  | Ibin_lt -> "lt"
  | Ibin_le -> "le"
  | Ibin_gt -> "gt"
  | Ibin_ge -> "ge"

type iscope =
| Local
| Global
[@@deriving sexp_of]

let iscope_to_string (is : iscope) =
  match is with
  | Local -> "local"
  | Global -> "global"

(* name, is global *)
type ivariable = iscope * string
[@@deriving sexp_of]

let ivariable_to_string ((scope, name) : ivariable) =
  (iscope_to_string scope) ^ "." ^ name

type iexpression =
(* Create a new var, and pop to it from top of stack *)
(* type of variable, name of variable *)
| Iexp_newvar of itype * ivariable
(* Push var's value to the stack *)
(* type of variable, name of variable *)
| Iexp_pushvar of itype * ivariable
(* Binary operation using two stack values *)
(* type of operands, binary operation *)
| Iexp_binop of itype * ibinop
(* Push a constant to the stack *)
(* type of constant, string rep of constant *)
| Iexp_pushconst of itype * string
(* Make a new closure for specified function and tuple type, and put it in given variable *)
(* type of function, name of function, type of closure variables, variable to put closure in *)
| Iexp_newclosure of iftype * string * ituptype * ivariable
(* Fill a closure in the named variable using the code to generate those values *)
(* type of closure variables, name of variable *)
| Iexp_fillclosure of ituptype * ivariable * (iexpression list) list
(* Call closure in variable using argument generated from code *)
(* type of function, variable to use to help call, code to generate argument *)
| Iexp_callclosure of iftype * ivariable * (iexpression list)
(* A block of instructions, locally scoped *)
(* name of block, result type, list of instructions *)
| Iexp_block of string * itype * iexpression list
(* Exit from the named block *)
(* name of block *)
| Iexp_exitblock of string
(* Exit from the named block if top of stack is true *)
(* name of block *)
| Iexp_exitblockif of string
(* If then else *)
(* name of block, result type (on stack top), if case code, optional else code *)
| Iexp_ifthenelse of string * itype * iexpression list * iexpression list option
(* Create a tuple from the given code, push pointer to stack and put it in that variable *)
(* type of tuple, name of variable, code to generate each part of tuple *)
| Iexp_pushtuple of ituptype * ivariable * (iexpression list) list
(* Pop tuple, push its value at index i to the stack *)
(* type of tuple, index in tuple *)
| Iexp_loadtupleindex of ituptype * int
(* Create a construct from the given code, push pointer to stack and put it in variable *)
(* type of construct arguments, name of variable, id of construct, code to generate each part of construct *)
| Iexp_pushconstruct of ituptype * ivariable * int * (iexpression list) list
(* Pop construct, push its value at index i to the stack *)
(* type of construct arguments, index in arguments *)
| Iexp_loadconstructindex of ituptype * int
(* Pop construct, push its id to the stack *)
(* No parameters *)
| Iexp_loadconstructid
(* Fail *)
(* No parameters *)
| Iexp_fail
(* Drop top of stack *)
(* type of thing on top of stack *)
| Iexp_drop of itype
[@@deriving sexp_of]

let rec iexpression_to_string (iexp : iexpression) =
  match iexp with
  | Iexp_newvar (t, name) -> "newvar " ^ (itype_to_string t) ^ " " ^ (ivariable_to_string name)
  | Iexp_pushvar (t, name) -> "pushvar " ^ (itype_to_string t) ^ " " ^ (ivariable_to_string name)
  | Iexp_binop (t, op) -> "binop " ^ (itype_to_string t) ^ " " ^ (ibinop_to_string op)
  | Iexp_pushconst (t, v) -> "pushconst " ^ (itype_to_string t) ^ " " ^ v
  | Iexp_newclosure (ift, name, itt, var_name) ->
      "newclosure " ^ (iftype_to_string ift) ^ " " ^ name ^ " " ^ (ituptype_to_string itt) ^ " " ^
      (ivariable_to_string var_name)
  | Iexp_fillclosure(itt, name, codes) ->
      "fillclosure " ^ (ituptype_to_string itt) ^ " " ^ (ivariable_to_string name) ^ " " ^
      tuple_codes_to_string codes
  | Iexp_callclosure(ift, var, code) ->
      "callclosure " ^ (iftype_to_string ift) ^ " " ^ (ivariable_to_string var) ^ "(\n" ^
      (iexpression_list_to_string code) ^ "\n" ^
      ")"
  | Iexp_block(name, t, ls) ->
      "block " ^ name ^ " " ^ (itype_to_string t) ^ " {\n" ^
      (String.concat ~sep:"\n" (List.map ls ~f:iexpression_to_string)) ^
      "\n}"
  | Iexp_exitblock(name) -> "exitblock " ^ name
  | Iexp_exitblockif(name) -> "exitblockif " ^ name
  | Iexp_ifthenelse (name, t, ifl, ell) -> "ifthenelse " ^ name ^ " " ^ (itype_to_string t) ^ " if{\n" ^
      (String.concat ~sep:"\n" (List.map ifl ~f:iexpression_to_string)) ^ "\n}" ^
      Option.value (Option.map ell ~f:(fun ell_list -> " else {\n" ^ (String.concat ~sep:"\n" (List.map ell_list ~f:iexpression_to_string)) ^ "\n}")) ~default:""
  | Iexp_pushtuple(itt, name, codes) ->
      "pushtuple " ^ (ituptype_to_string itt) ^ " " ^ (ivariable_to_string name) ^ " " ^
      tuple_codes_to_string codes
  | Iexp_loadtupleindex (itt, id) -> "loadtupleindex " ^ (ituptype_to_string itt) ^ " " ^ (Int.to_string id)
  | Iexp_pushconstruct(itt, name, id, codes) ->
      "pushconstruct " ^ (ituptype_to_string itt) ^ " " ^ (ivariable_to_string name) ^ " " ^ (Int.to_string id) ^ " " ^
      tuple_codes_to_string codes
  | Iexp_loadconstructindex(itt, id) -> "loadconstructindex " ^ (ituptype_to_string itt) ^ " " ^ (Int.to_string id)
  | Iexp_loadconstructid -> "loadconstructid"
  | Iexp_fail -> "fail"
  | Iexp_drop(t) -> "drop " ^ (itype_to_string t)


and iexpression_list_to_string ls =
  String.concat ~sep:"\n" (List.map ls ~f:iexpression_to_string)

and tuple_codes_to_string codes =
  let str_parts = List.map codes ~f:(fun c -> "(" ^ (iexpression_list_to_string c) ^ ")") in
  "(\n" ^ (String.concat ~sep:"\n" str_parts) ^ "\n)"
