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

type iexpression =
(* Create a new var from a constant *)
(* type of variable, name of variable *)
| Iexp_setvar of itype * ivariable * string
(* Copy a variable into another *)
(* type of variable, name of new variable, name of old variable *)
| Iexp_copyvar of itype * ivariable * ivariable
(* Return var *)
(* type of variable, name of variable *)
| Iexp_return of itype * ivariable
(* Unary operation using one stack value *)
(* type of operand, unary operation, result var, input var *)
| Iexp_unop of itype * iunop * ivariable * ivariable
(* Binary operation using two stack values *)
(* type of operands, binary operation *)
| Iexp_binop of itype * ibinop * ivariable * ivariable * ivariable
(* Make a new closure for specified function and tuple type, and put it in given variable *)
(* type of function, name of function, type of closure variables, variable to put closure in *)
| Iexp_newclosure of iftype * string * ituptype * ivariable
(* Fill a closure in the named variable using the code to generate those values *)
(* type of closure variables, name of variable, list of variables to copy in *)
| Iexp_fillclosure of ituptype * ivariable * ivariable list
(* Call closure in variable using argument generated from code *)
(* type of function, output variable, closure variable, variable for argument *)
| Iexp_callclosure of iftype * ivariable * ivariable * ivariable
(* Start a block *)
(* name of block *)
| Iexp_startblock of string
(* End a block *)
(* name of block *)
| Iexp_endblock of string
(* Exit from the named block *)
(* name of block *)
| Iexp_exitblock of string
(* Exit from the named block if variable is true *)
(* name of block *)
| Iexp_exitblockif of string * ivariable
(* Start an if statement *)
(* name of block, condition var *)
| Iexp_startif of string * ivariable
(* Else clause of an if statement *)
(* name of block *)
| Iexp_else of string
(* End an if statement *)
(* name of block *)
| Iexp_endif of string
(* Starts a loop, loops until an exitblock or exitblockif *)
(* Name of escape block (to break to), name of loop block (to continue to) *)
| Iexp_startloop of string * string
(* Ends a loop *)
(* Name of break block, name of continue block *)
| Iexp_endloop of string * string
(* Create a tuple from the given code, push pointer to stack and put it in that variable *)
(* type of tuple, name of variable, code to generate each part of tuple *)
| Iexp_pushtuple of ituptype * ivariable * ivariable list
(* Pop tuple, push its value at index i to the stack *)
(* type of tuple, index in tuple, output var, tuple var *)
| Iexp_loadtupleindex of ituptype * int * ivariable * ivariable
(* Create a construct from the given code, push pointer to stack and put it in variable *)
(* type of construct arguments, name of variable, id of construct, code to generate each part of construct *)
| Iexp_pushconstruct of ituptype * ivariable * int * ivariable list
(* Pop construct, push its value at index i to the stack *)
(* type of construct arguments, index in arguments, output variable, tuple variable *)
| Iexp_loadconstructindex of ituptype * int * ivariable * ivariable
(* Pop construct, push its id to the stack *)
(* output variable, construct variable *)
| Iexp_loadconstructid of ivariable * ivariable
(* Box a value (on stack) of a type that needs boxing, or for a ref *)
(* unboxed type, unboxped variable, variable to store boxed result *)
| Iexp_newbox of itype * ivariable * ivariable
(* Update a boxed value, useful for refs *)
(* unboxed type, unboxped variable, boxed variable *)
| Iexp_updatebox of itype * ivariable * ivariable
(* Unbox a value / dereference a ref *)
(* unboxped type, wrapped variable, unboxped target variable *)
| Iexp_unbox of itype * ivariable * ivariable
(* Fail *)
(* No parameters *)
| Iexp_fail
[@@deriving sexp_of]

let rec iexpression_to_string (iexp : iexpression) =
  match iexp with
  | Iexp_setvar (t, name, con) ->
      "setvar " ^ (itype_to_string t) ^ " " ^ (ivariable_to_string name) ^ " " ^ con
  | Iexp_copyvar(t, res, arg) ->
      "copyvar " ^ (itype_to_string t) ^ " " ^ (ivariable_to_string res) ^ " " ^
      (ivariable_to_string arg)
  | Iexp_return (t, name) -> "return " ^ (itype_to_string t) ^ " " ^ (ivariable_to_string name)
  | Iexp_unop (t, op, res, arg) ->
      "unop " ^ (itype_to_string t) ^ " " ^ (iunop_to_string op) ^
      " " ^ (ivariable_to_string res) ^ " " ^ (ivariable_to_string arg)
  | Iexp_binop (t, op, res, arg1, arg2) ->
      "binop " ^ (itype_to_string t) ^ " " ^ (ibinop_to_string op) ^
      " " ^ (ivariable_to_string res) ^ " " ^ (ivariable_to_string arg1) ^
      " " ^ (ivariable_to_string arg2)
  | Iexp_newclosure (ift, name, itt, var_name) ->
      "newclosure " ^ (iftype_to_string ift) ^ " " ^ name ^ " " ^ (ituptype_to_string itt) ^ " " ^
      (ivariable_to_string var_name)
  | Iexp_fillclosure(itt, name, vars) ->
      "fillclosure " ^ (ituptype_to_string itt) ^ " " ^ (ivariable_to_string name) ^ " " ^
      vars_to_string vars
  | Iexp_callclosure(ift, res, clo, arg) ->
      "callclosure " ^ (iftype_to_string ift) ^ " " ^ (ivariable_to_string res) ^
      " " ^ (ivariable_to_string clo) ^ " " ^ (ivariable_to_string arg)
  | Iexp_startblock(name) ->
      "startblock " ^ name
  | Iexp_endblock(name) ->
      "endblock " ^ name
  | Iexp_exitblock(name) -> "exitblock " ^ name
  | Iexp_exitblockif(name, var) -> "exitblockif " ^ name ^ " " ^ (ivariable_to_string var)
  | Iexp_startif(name, cond) -> "startif " ^ name ^ " " ^ (ivariable_to_string cond)
  | Iexp_else(name) -> "else " ^ name
  | Iexp_endif(name) -> "endif " ^ name
  | Iexp_startloop(break, cont) -> "startloop " ^ break ^ " " ^ cont
  | Iexp_endloop(break, cont) -> "endloop " ^ break ^ " " ^ cont
  | Iexp_pushtuple(itt, name, vars) ->
      "pushtuple " ^ (ituptype_to_string itt) ^ " " ^ (ivariable_to_string name) ^ " " ^
      vars_to_string vars
  | Iexp_loadtupleindex (itt, id, res, arg) ->
      "loadtupleindex " ^ (ituptype_to_string itt) ^ " " ^ (Int.to_string id) ^
      " " ^ (ivariable_to_string res) ^ " " ^ (ivariable_to_string arg)
  | Iexp_pushconstruct(itt, name, id, vars) ->
      "pushconstruct " ^ (ituptype_to_string itt) ^ " " ^ (ivariable_to_string name) ^
      " " ^ (Int.to_string id) ^ " " ^
      vars_to_string vars
  | Iexp_loadconstructindex(itt, id, res, arg) ->
      "loadconstructindex " ^ (ituptype_to_string itt) ^ " " ^ (Int.to_string id) ^
      " " ^ (ivariable_to_string res) ^ " " ^ (ivariable_to_string arg)
  | Iexp_loadconstructid(res, arg) ->
      "loadconstructid " ^ (ivariable_to_string res) ^ (ivariable_to_string arg)
  | Iexp_newbox(typ, unbox, wrap) ->
      "newbox " ^ (itype_to_string typ) ^ " " ^ (ivariable_to_string unbox) ^ " " ^ (ivariable_to_string wrap)
  | Iexp_updatebox(typ, unbox, wrap) ->
      "updatebox " ^ (itype_to_string typ) ^ " " ^ (ivariable_to_string unbox) ^ " " ^ (ivariable_to_string wrap)
  | Iexp_unbox(typ, wrap, unbox) ->
      "unbox " ^ (itype_to_string typ) ^ " " ^ (ivariable_to_string wrap) ^ " " ^ (ivariable_to_string unbox)
  | Iexp_fail -> "fail"


and iexpression_list_to_string ls =
  String.concat ~sep:"\n" (List.map ls ~f:iexpression_to_string)

and vars_to_string vars =
  let parts = List.map vars ~f:ivariable_to_string in
  "(" ^ (String.concat ~sep:" " parts) ^ ")"


let iexpression_map_vars ~f:map_var (iexp : iexpression) =
  match iexp with
  | Iexp_setvar(t, name, str) ->
      Iexp_setvar(t, map_var name, str)
  | Iexp_copyvar(t, res, arg) ->
      Iexp_copyvar(t, map_var res, map_var arg)
  | Iexp_return(t, res) ->
      Iexp_return(t, map_var res)
  | Iexp_unop(t, un, res, arg) ->
      Iexp_unop(t, un, map_var res, map_var arg)
  | Iexp_binop(t, un, res, arg1, arg2) ->
      Iexp_binop(t, un, map_var res, map_var arg1, map_var arg2)
  | Iexp_newclosure(ift, fname, itt, var) ->
      Iexp_newclosure(ift, fname, itt, map_var var)
  | Iexp_fillclosure(itt, name, var_lst) ->
      Iexp_fillclosure(itt, map_var name, List.map ~f:map_var var_lst)
  | Iexp_callclosure(ift, res, clo, arg) ->
      Iexp_callclosure(ift, map_var res, map_var clo, map_var arg)
  | Iexp_startblock(name) ->
      Iexp_startblock(name)
  | Iexp_endblock(name) ->
      Iexp_endblock(name)
  | Iexp_exitblock(str) ->
      Iexp_exitblock(str)
  | Iexp_exitblockif(str, cond) ->
      Iexp_exitblockif(str, map_var cond)
  | Iexp_startif(name, cond) ->
      Iexp_startif(name, map_var cond)
  | Iexp_else(name) ->
      Iexp_else(name)
  | Iexp_endif(name) ->
      Iexp_endif(name)
  | Iexp_startloop(break, cont) ->
      Iexp_startloop(break, cont)
  | Iexp_endloop(break, cont) ->
      Iexp_endloop(break, cont)
  | Iexp_pushtuple(itt, name, var_lst) ->
      Iexp_pushtuple(itt, map_var name, List.map ~f:map_var var_lst)
  | Iexp_loadtupleindex(itt, id, res, tup) ->
      Iexp_loadtupleindex(itt, id, map_var res, map_var tup)
  | Iexp_pushconstruct(itt, name, id, var_lst) ->
      Iexp_pushconstruct(itt, map_var name, id, List.map ~f:map_var var_lst)
  | Iexp_loadconstructindex(itt, id, res, con) ->
      Iexp_loadconstructindex(itt, id, map_var res, map_var con)
  | Iexp_loadconstructid(res, con) ->
      Iexp_loadconstructid(map_var res, map_var con)
  | Iexp_newbox(t, unbox, box) ->
      Iexp_newbox(t, map_var unbox, map_var box)
  | Iexp_updatebox(t, unbox, box) ->
      Iexp_updatebox(t, map_var unbox, map_var box)
  | Iexp_unbox(t, boxed, unboxed) ->
      Iexp_unbox(t, map_var boxed, map_var unboxed)
  | Iexp_fail ->
      Iexp_fail


let iexpression_list_map_vars ~f:map_vars lst =
  List.map ~f:(iexpression_map_vars ~f:map_vars) lst
