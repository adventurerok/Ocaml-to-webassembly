open Core_kernel
open Otwa_base

type tvalue =
  | V_unit
  | V_int
  | V_bool
  | V_float
  [@@deriving sexp_of, equal]

type tvar_set = string Set.Poly.t

let sexp_of_tvar_set (tvs : tvar_set) =
  List.sexp_of_t String.sexp_of_t (Set.to_list tvs)

type scheme_type =
  | T_var of string
  | T_val of tvalue
  | T_tuple of scheme_type list
  | T_constr of string * scheme_type list
  | T_func of scheme_type * scheme_type
  [@@deriving sexp_of, equal]

type scheme = Forall of tvar_set * scheme_type
[@@deriving sexp_of]

type uni_pair = Uni of scheme_type * scheme_type * Location.t

let loc_to_string (loc : Location.t) =
  if loc.loc_ghost then
    "none"
  else
    let start_pos = loc.loc_start in
    let pos_in_line = start_pos.pos_cnum - start_pos.pos_bol in
    start_pos.pos_fname ^ " line " ^ (Int.to_string start_pos.pos_lnum) ^ ":" ^ (Int.to_string pos_in_line)

(* Converting things into strings *)
let rec string_of_scheme_type typ =
  match typ with
  | T_var(vr) -> "'" ^ vr
  | T_tuple(ls) -> "(" ^ (String.concat ~sep:" * " (List.map ls ~f:string_of_scheme_type)) ^ ")"
  | T_constr(str, ls) ->
      (match ls with
      | [] -> str
      | (x::[]) -> (string_of_scheme_type x) ^ " " ^ str
      | _ -> (string_of_scheme_type (T_tuple(ls))) ^ " " ^ str)
  | T_val(V_int) -> "int"
  | T_val(V_bool) -> "bool"
  | T_val(V_unit) -> "unit"
  | T_val(V_float) -> "float"
  | T_func(a,b) -> "(" ^ (string_of_scheme_type a) ^ " -> " ^ (string_of_scheme_type b) ^ ")"

let string_of_scheme (Forall(vars, typ)) =
  if Set.is_empty vars then
    string_of_scheme_type typ
  else
    "forall " ^ (String.concat ~sep:"," (Set.to_list vars)) ^ ". " ^ (string_of_scheme_type typ)

let string_of_uni_pair (Uni(s1, s2, _)) =
  "uni(" ^ (string_of_scheme_type s1) ^ ", " ^ (string_of_scheme_type s2) ^ ")"

let rec string_of_uni_pair_list = function
  | [] -> ""
  | (pr::lst) -> (string_of_uni_pair pr) ^ ", " ^ (string_of_uni_pair_list lst)


let rec ftv typ =
  match typ with
  | (T_var(tv)) -> Set.Poly.singleton tv
  | (T_val(_)) -> Set.Poly.empty
  | (T_tuple(ls)) -> Set.Poly.union_list (List.map ls ~f:ftv)
  | (T_constr(_, ls)) -> Set.Poly.union_list (List.map ls ~f:ftv)
  | (T_func(a, b)) -> Set.Poly.union (ftv a) (ftv b)

let ftv_scheme (Forall(s, t)) =
  Set.Poly.diff (ftv t) s

(* Substitute tv for styp in typ *)
let rec substitute tv styp typ =
  match typ with
  | (T_var(tvo)) -> if (String.equal tv tvo) then styp else typ
  | (T_val(_)) -> typ
  | (T_tuple(ls)) -> (T_tuple(List.map ls ~f:(substitute tv styp)))
  | (T_constr(str, ls)) -> (T_constr(str, List.map ls ~f:(substitute tv styp)))
  | (T_func(a, b)) -> (T_func(substitute tv styp a, substitute tv styp b))

(* Substitute a list of (tvar,styp) into typ IN ORDER *)
(* TODO use maps for substitutions *)
let rec substitute_list ls typ =
  match ls with
  | [] -> typ
  | ((tv,styp)::xs) -> substitute_list xs (substitute tv styp typ)

(* Substitute tv for styp in both types in Uni *)
let substitute_uni tv styp (Uni(a, b, loc)) =
  (Uni(substitute tv styp a, substitute tv styp b, loc))

let rec substitute_uni_list ls uni =
  match ls with
  | [] -> uni
  | ((tv,styp)::xs) -> substitute_uni_list xs (substitute_uni tv styp uni)

let substitute_scheme tv styp (Forall(s, t)) =
  if Set.mem s tv then
    (Forall(s, t))
  else
    (Forall(s, substitute tv styp t))

let substitute_scheme_list ls (Forall(s,t)) =
  let reduced = List.filter ls ~f:(fun (a,_) -> not (Set.mem s a)) in
  (Forall(s, substitute_list reduced t))

(* message, left type, right type *)
exception UnifyFail of string * string * string
let unify_fail_exn msg a_in b_in loc =
  raise (UnifyFail(msg ^ " at " ^ (loc_to_string loc), string_of_scheme_type a_in, string_of_scheme_type b_in))

(* type variable name, type *)
exception OccursFail of string * string

(* Ensure that tv doesn't occur in typ *)
let occurs_check tv typ =
  (if Config.global.trace then
    Stdio.print_endline ("Occurs check " ^ tv ^ " in " ^ (string_of_scheme_type typ))
  );
  let rec inner typ' =
    match typ' with
    | T_val(_) -> ()
    | T_var(ov) ->
        if (String.equal tv ov) then
          raise (OccursFail(tv, string_of_scheme_type typ))
        else
          ()
    | T_tuple(ls) -> List.iter ls ~f:inner
    | T_constr(_, ls) -> List.iter ls ~f:inner
    | T_func(a, b) ->
        let () = inner a in
        inner b
  in inner typ

let find_unify (Uni(a_in, b_in, loc)) =
  (if Config.global.trace then
    Stdio.print_endline ("Find unify " ^ (string_of_scheme_type a_in) ^ " " ^ (string_of_scheme_type b_in))
  );
  let rec inner a b =
    match (a, b) with
    | (T_val(va), T_val(vb)) ->
        if equal_tvalue va vb then []
        else unify_fail_exn "Different value types" a_in b_in loc
    | (T_tuple([]), T_tuple([])) -> []
    | (T_tuple(x::xs), T_tuple(y::ys)) -> inner (T_func(x, T_tuple(xs))) (T_func(y, T_tuple(ys)))
    | (T_constr(s1, l1), T_constr(s2, l2)) ->
        if String.equal s1 s2 then
          inner (T_tuple(l1)) (T_tuple(l2))
        else
          unify_fail_exn "Different constructs" a_in b_in loc
    | (T_var(ta), T_var(_)) -> [(ta, b)] (* To avoid self-unification failing the occurs check *)
    | (T_var(tv), _) ->
        let () = occurs_check tv b in
        [(tv, b)]
    | (_, T_var(tv)) ->
        let () = occurs_check tv a in
        [(tv, a)]
    | (T_func(p, q), T_func(x, y)) ->
        let upx = inner p x in
        let uqy = inner (substitute_list upx q) (substitute_list upx y) in
        (upx @ uqy)
    | _ -> unify_fail_exn "Unequal types" a_in b_in loc
  in inner a_in b_in

(* Shorthand if you don't want to make a Uni yourself *)
let unify a b = find_unify (Uni(a,b, Location.none))

(* Unify a whole list of constraints *)
let rec unify_many lst =
  match lst with
  | [] -> []
  | (up :: lst') ->
      let u1 = find_unify up in
      let lst'' = List.map lst' ~f:(substitute_uni_list u1) in
      let u2 = unify_many lst'' in
      (u1 @ u2)

