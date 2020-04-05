open Core_kernel
open Otwa_types
open Types

type itype =
  | It_poly
  | It_bool
  | It_int
  | It_float
  | It_pointer
  | It_unit
  | It_none
  [@@deriving sexp_of, equal, enumerate]

let itype_to_string (it : itype) =
  match it with
  | It_poly -> "poly"
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

let itype_needs_box (it : itype) =
  match it with
  | It_float -> true
  | _ -> false

let stoitype (typ : scheme_type) =
  match typ with
  | T_var(_) -> It_poly
  | T_val(V_unit) -> It_unit
  | T_val(V_int) -> It_int
  | T_val(V_bool) -> It_bool
  | T_val(V_float) -> It_float
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

type iunop =
  Iun_neg
| Iun_eqz
[@@deriving sexp_of, equal]

let iunop_to_string (iu : iunop) =
  match iu with
  | Iun_neg -> "neg"
  | Iun_eqz -> "eqz"

type iscope =
| Local
| Global
[@@deriving sexp_of, equal, hash, compare, sexp]

let iscope_to_string (is : iscope) =
  match is with
  | Local -> "local"
  | Global -> "global"

(* name, is global *)
type ivariable = iscope * string
[@@deriving sexp_of, equal, hash, compare, sexp]

let ivariable_to_string ((scope, name) : ivariable) =
  (iscope_to_string scope) ^ "." ^ name

module IVariable = struct
  module T = struct
    type t = ivariable
    let compare = compare_ivariable
    let sexp_of_t = sexp_of_ivariable
    let t_of_sexp = ivariable_of_sexp
    let hash = hash_ivariable
  end

  include T
  include Comparable.Make(T)
end

let ivariable_is_local ((is, _) : ivariable) =
  match is with
  | Local -> true
  | Global -> false

let ivariable_is_global ((is, _) : ivariable) =
  match is with
  | Global -> true
  | Local -> false

type iinstruction =
(* Create a new var from a constant *)
(* type of variable, name of variable *)
| Iins_setvar of itype * ivariable * string
(* Copy a variable into another *)
(* type of variable, name of new variable, name of old variable *)
| Iins_copyvar of itype * ivariable * ivariable
(* Return var *)
(* type of variable, name of variable *)
| Iins_return of itype * ivariable
(* Unary operation using one argument value *)
(* type of operand, unary operation, result var, input var *)
| Iins_unop of itype * iunop * ivariable * ivariable
(* Binary operation using two argument values *)
(* type of operands, binary operation *)
| Iins_binop of itype * ibinop * ivariable * ivariable * ivariable
(* Make a new closure for specified function and tuple type *)
(* type of function, name of function, type of closure variables, result variable *)
| Iins_newclosure of iftype * string * ituptype * ivariable
(* Fill a closure with a list of variables *)
(* type of closure variables, name of variable, list of variables to copy in *)
| Iins_fillclosure of ituptype * ivariable * ivariable list
(* Call closure in variable, passing in an argument *)
(* type of function, output variable, closure variable, variable for argument *)
| Iins_callclosure of iftype * ivariable * ivariable * ivariable
(* Directly call a function, passing multiple arguments *)
(* output variable, name of function, type of args, arg vars *)
| Iins_calldirect of ivariable * string * ituptype * (ivariable list)
(* Start a block *)
(* name of block *)
| Iins_startblock of string
(* End a block *)
(* name of block *)
| Iins_endblock of string
(* Exit from the named block *)
(* name of block *)
| Iins_exitblock of string
(* Exit from the named block if variable is true *)
(* name of block *)
| Iins_exitblockif of string * ivariable
(* Start an if statement *)
(* name of block, condition var *)
| Iins_startif of string * ivariable
(* Else clause of an if statement *)
(* name of block *)
| Iins_else of string
(* End an if statement *)
(* name of block *)
| Iins_endif of string
(* Starts a loop, loops until an exitblock or exitblockif *)
(* Name of escape block (to break to), name of loop block (to continue to) *)
| Iins_startloop of string * string
(* Ends a loop *)
(* Name of break block, name of continue block *)
| Iins_endloop of string * string
(* Create a tuple of the given variables *)
(* type of tuple, result variable, argument variables *)
| Iins_newtuple of ituptype * ivariable * ivariable list
(* Load tuple's value at index i *)
(* type of tuple, index in tuple, output var, tuple var *)
| Iins_loadtupleindex of ituptype * int * ivariable * ivariable
(* Create a construct of the given id and variables *)
(* type of construct arguments, result variable, id of construct, argument variables *)
| Iins_newconstruct of ituptype * ivariable * int * ivariable list
(* Load construct's value at index i *)
(* type of construct arguments, index in arguments, output variable, construct variable *)
| Iins_loadconstructindex of ituptype * int * ivariable * ivariable
(* Load construct's ID *)
(* output variable, construct variable *)
| Iins_loadconstructid of ivariable * ivariable
(* Create a mutable memory box for a value *)
(* unboxed type, result variable, variable to box *)
| Iins_newbox of itype * ivariable * ivariable
(* Update a mutable memory box with a new value *)
(* unboxed type, boxed variable, unboxed variable *)
| Iins_updatebox of itype * ivariable * ivariable
(* Load a value from a mutable memory box *)
(* unboxed type, target variable, boxed variable *)
| Iins_unbox of itype * ivariable * ivariable
(* Fail, suspending execution *)
(* No parameters *)
| Iins_fail
[@@deriving sexp_of]

let rec iinstruction_to_string (iins : iinstruction) =
  match iins with
  | Iins_setvar (t, name, con) ->
      "setvar " ^ (itype_to_string t) ^ " " ^ (ivariable_to_string name) ^ " " ^ con
  | Iins_copyvar(t, res, arg) ->
      "copyvar " ^ (itype_to_string t) ^ " " ^ (ivariable_to_string res) ^ " " ^
      (ivariable_to_string arg)
  | Iins_return (t, name) -> "return " ^ (itype_to_string t) ^ " " ^ (ivariable_to_string name)
  | Iins_unop (t, op, res, arg) ->
      "unop " ^ (itype_to_string t) ^ " " ^ (iunop_to_string op) ^
      " " ^ (ivariable_to_string res) ^ " " ^ (ivariable_to_string arg)
  | Iins_binop (t, op, res, arg1, arg2) ->
      "binop " ^ (itype_to_string t) ^ " " ^ (ibinop_to_string op) ^
      " " ^ (ivariable_to_string res) ^ " " ^ (ivariable_to_string arg1) ^
      " " ^ (ivariable_to_string arg2)
  | Iins_newclosure (ift, name, itt, var_name) ->
      "newclosure " ^ (iftype_to_string ift) ^ " " ^ name ^ " " ^ (ituptype_to_string itt) ^ " " ^
      (ivariable_to_string var_name)
  | Iins_fillclosure(itt, name, vars) ->
      "fillclosure " ^ (ituptype_to_string itt) ^ " " ^ (ivariable_to_string name) ^ " " ^
      vars_to_string vars
  | Iins_callclosure(ift, res, clo, arg) ->
      "callclosure " ^ (iftype_to_string ift) ^ " " ^ (ivariable_to_string res) ^
      " " ^ (ivariable_to_string clo) ^ " " ^ (ivariable_to_string arg)
  | Iins_calldirect(res, name, itt, arg_lst) ->
      "calldirect " ^ (ivariable_to_string res) ^ " " ^ name ^ " " ^
      (ituptype_to_string itt) ^ " " ^ (vars_to_string arg_lst)
  | Iins_startblock(name) ->
      "startblock " ^ name
  | Iins_endblock(name) ->
      "endblock " ^ name
  | Iins_exitblock(name) -> "exitblock " ^ name
  | Iins_exitblockif(name, var) -> "exitblockif " ^ name ^ " " ^ (ivariable_to_string var)
  | Iins_startif(name, cond) -> "startif " ^ name ^ " " ^ (ivariable_to_string cond)
  | Iins_else(name) -> "else " ^ name
  | Iins_endif(name) -> "endif " ^ name
  | Iins_startloop(break, cont) -> "startloop " ^ break ^ " " ^ cont
  | Iins_endloop(break, cont) -> "endloop " ^ break ^ " " ^ cont
  | Iins_newtuple(itt, name, vars) ->
      "pushtuple " ^ (ituptype_to_string itt) ^ " " ^ (ivariable_to_string name) ^ " " ^
      vars_to_string vars
  | Iins_loadtupleindex (itt, id, res, arg) ->
      "loadtupleindex " ^ (ituptype_to_string itt) ^ " " ^ (Int.to_string id) ^
      " " ^ (ivariable_to_string res) ^ " " ^ (ivariable_to_string arg)
  | Iins_newconstruct(itt, name, id, vars) ->
      "pushconstruct " ^ (ituptype_to_string itt) ^ " " ^ (ivariable_to_string name) ^
      " " ^ (Int.to_string id) ^ " " ^
      vars_to_string vars
  | Iins_loadconstructindex(itt, id, res, arg) ->
      "loadconstructindex " ^ (ituptype_to_string itt) ^ " " ^ (Int.to_string id) ^
      " " ^ (ivariable_to_string res) ^ " " ^ (ivariable_to_string arg)
  | Iins_loadconstructid(res, arg) ->
      "loadconstructid " ^ (ivariable_to_string res) ^ (ivariable_to_string arg)
  | Iins_newbox(typ, res, arg) ->
      "newbox " ^ (itype_to_string typ) ^ " " ^ (ivariable_to_string res) ^ " " ^ (ivariable_to_string arg)
  | Iins_updatebox(typ, box, arg) ->
      "updatebox " ^ (itype_to_string typ) ^ " " ^ (ivariable_to_string box) ^ " " ^ (ivariable_to_string arg)
  | Iins_unbox(typ, res, box) ->
      "unbox " ^ (itype_to_string typ) ^ " " ^ (ivariable_to_string res) ^ " " ^ (ivariable_to_string box)
  | Iins_fail -> "fail"


and iinstruction_list_to_string ls =
  String.concat ~sep:"\n" (List.map ls ~f:iinstruction_to_string)

and vars_to_string vars =
  let parts = List.map vars ~f:ivariable_to_string in
  "(" ^ (String.concat ~sep:" " parts) ^ ")"


let iinstruction_map_vars ~f:map_var (iins : iinstruction) =
  match iins with
  | Iins_setvar(t, name, str) ->
      Iins_setvar(t, map_var name, str)
  | Iins_copyvar(t, res, arg) ->
      Iins_copyvar(t, map_var res, map_var arg)
  | Iins_return(t, res) ->
      Iins_return(t, map_var res)
  | Iins_unop(t, un, res, arg) ->
      Iins_unop(t, un, map_var res, map_var arg)
  | Iins_binop(t, un, res, arg1, arg2) ->
      Iins_binop(t, un, map_var res, map_var arg1, map_var arg2)
  | Iins_newclosure(ift, fname, itt, var) ->
      Iins_newclosure(ift, fname, itt, map_var var)
  | Iins_fillclosure(itt, name, var_lst) ->
      Iins_fillclosure(itt, map_var name, List.map ~f:map_var var_lst)
  | Iins_callclosure(ift, res, clo, arg) ->
      Iins_callclosure(ift, map_var res, map_var clo, map_var arg)
  | Iins_calldirect(res, name, itt, arg_lst) ->
      Iins_calldirect(map_var res, name, itt, List.map ~f:map_var arg_lst)
  | Iins_startblock(name) ->
      Iins_startblock(name)
  | Iins_endblock(name) ->
      Iins_endblock(name)
  | Iins_exitblock(str) ->
      Iins_exitblock(str)
  | Iins_exitblockif(str, cond) ->
      Iins_exitblockif(str, map_var cond)
  | Iins_startif(name, cond) ->
      Iins_startif(name, map_var cond)
  | Iins_else(name) ->
      Iins_else(name)
  | Iins_endif(name) ->
      Iins_endif(name)
  | Iins_startloop(break, cont) ->
      Iins_startloop(break, cont)
  | Iins_endloop(break, cont) ->
      Iins_endloop(break, cont)
  | Iins_newtuple(itt, name, var_lst) ->
      Iins_newtuple(itt, map_var name, List.map ~f:map_var var_lst)
  | Iins_loadtupleindex(itt, id, res, tup) ->
      Iins_loadtupleindex(itt, id, map_var res, map_var tup)
  | Iins_newconstruct(itt, name, id, var_lst) ->
      Iins_newconstruct(itt, map_var name, id, List.map ~f:map_var var_lst)
  | Iins_loadconstructindex(itt, id, res, con) ->
      Iins_loadconstructindex(itt, id, map_var res, map_var con)
  | Iins_loadconstructid(res, con) ->
      Iins_loadconstructid(map_var res, map_var con)
  | Iins_newbox(t, res, arg) ->
      Iins_newbox(t, map_var res, map_var arg)
  | Iins_updatebox(t, box, arg) ->
      Iins_updatebox(t, map_var box, map_var arg)
  | Iins_unbox(t, res, box) ->
      Iins_unbox(t, map_var res, map_var box)
  | Iins_fail ->
      Iins_fail


let iinstruction_list_map_vars ~f:map_vars lst =
  List.map ~f:(iinstruction_map_vars ~f:map_vars) lst
