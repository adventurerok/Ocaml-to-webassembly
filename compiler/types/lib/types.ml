open Base

type tvalue =
  | V_unit
  | V_int
  | V_bool

(* TODO why? *)
type tvar = string

type tvar_set = (string, String.comparator_witness) Set.t

let empty_tvar_set = Set.empty (module String)

type scheme_type =
  | T_var of tvar
  | T_val of tvalue
  | T_tuple of scheme_type list
  | T_constr of string * scheme_type list
  | T_func of scheme_type * scheme_type

type scheme = Forall of tvar_set * scheme_type

type uni_pair = Uni of scheme_type * scheme_type

let rec ftv typ =
  match typ with
  | (T_var(tv)) -> Set.singleton (module String) tv
  | (T_val(_)) -> empty_tvar_set
  | (T_tuple(ls)) -> Set.union_list (module String) (List.map ls ~f:ftv)
  | (T_constr(_, ls)) -> Set.union_list (module String) (List.map ls ~f:ftv)
  | (T_func(a, b)) -> Set.union (ftv a) (ftv b)

let ftv_scheme (Forall(s, t)) =
  Set.diff (ftv t) s

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
let substitute_uni tv styp (Uni(a, b)) =
  (Uni(substitute tv styp a, substitute tv styp b))

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

exception UnifyFail of string * uni_pair
exception OccursFail

(* Ensure that tv doesn't occur in typ *)
let rec occurs_check tv typ =
  match typ with
  | T_val(_) -> ()
  | T_var(ov) ->
      if (String.equal tv ov) then
        raise (OccursFail)
      else
        ()
  | T_tuple(ls) -> List.iter ls ~f:(occurs_check tv)
  | T_constr(_, ls) -> List.iter ls ~f:(occurs_check tv)
  | T_func(a, b) ->
      let () = occurs_check tv a in
      occurs_check tv b

let unify_val va vb =
  match(va, vb) with
  | (V_int, V_int) -> []
  | (V_bool, V_bool) -> []
  | (V_unit, V_unit) -> []
  | _ -> raise (UnifyFail ("Different value types", (Uni(T_val(va), T_val(vb)))))

let rec find_unify (Uni(a, b)) =
  match (a, b) with
  | (T_val(va), T_val(vb)) -> unify_val va vb
  | (T_tuple([]), T_tuple([])) -> []
  | (T_tuple(x::xs), T_tuple(y::ys)) -> find_unify (Uni(T_func(x, T_tuple(xs)), T_func(y, T_tuple(ys))))
  | (T_constr(s1, l1), T_constr(s2, l2)) ->
      if String.equal s1 s2 then
        find_unify (Uni(T_tuple(l1), T_tuple(l2)))
      else
        raise (UnifyFail ("Different constructs '" ^ s1 ^ "' and '" ^ s2 ^ "'", (Uni(a,b))))
  | (T_var(ta), T_var(_)) -> [(ta, b)] (* To avoid self-unification failing the occurs check *)
  | (T_var(tv), _) ->
      let () = occurs_check tv b in
      [(tv, b)]
  | (_, T_var(tv)) ->
      let () = occurs_check tv a in
      [(tv, a)]
  | (T_func(p, q), T_func(x, y)) ->
      let upx = find_unify (Uni(p,x)) in
      let uqy = find_unify (Uni(substitute_list upx q, substitute_list upx y)) in
      (upx @ uqy)
  | _ -> raise (UnifyFail ("Unequal types", (Uni(a, b))))

(* Shorthand if you don't want to make a Uni yourself *)
let unify a b = find_unify (Uni(a,b))

(* Unify a whole list of constraints *)
let rec unify_many lst =
  match lst with
  | [] -> []
  | (up :: lst') ->
      let u1 = find_unify up in
      let lst'' = List.map lst' ~f:(substitute_uni_list u1) in
      let u2 = unify_many lst'' in
      (u1 @ u2)

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
  | T_func(a,b) -> "(" ^ (string_of_scheme_type a) ^ " -> " ^ (string_of_scheme_type b) ^ ")"

let string_of_scheme (Forall(vars, typ)) =
  if Set.is_empty vars then
    string_of_scheme_type typ
  else
    "forall " ^ (String.concat ~sep:"," (Set.to_list vars)) ^ ". " ^ (string_of_scheme_type typ)

let string_of_uni_pair (Uni(s1, s2)) =
  "uni(" ^ (string_of_scheme_type s1) ^ ", " ^ (string_of_scheme_type s2) ^ ")"

let rec string_of_uni_pair_list = function
  | [] -> ""
  | (pr::lst) -> (string_of_uni_pair pr) ^ ", " ^ (string_of_uni_pair_list lst)
