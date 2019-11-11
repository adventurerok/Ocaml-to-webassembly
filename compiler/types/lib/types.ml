open Base

type tvalue =
  | V_int
  | V_bool

type tvar = string

type scheme_type =
  | T_var of tvar
  | T_val of tvalue
  | T_func of scheme_type * scheme_type

type scheme = Forall of tvar list * scheme_type

type uni_pair = Uni of scheme_type * scheme_type

let rec substitute tv styp typ =
  match typ with
  | (T_var(tvo)) -> if (String.equal tv tvo) then styp else typ
  | (T_val(_)) -> typ
  | (T_func(a, b)) -> (T_func(substitute tv styp a, substitute tv styp b))

let rec substitute_list ls typ =
  match ls with
  | [] -> typ
  | ((tv,styp)::xs) -> substitute_list xs (substitute tv styp typ)

let substitute_uni tv styp (Uni(a, b)) =
  (Uni(substitute tv styp a, substitute tv styp b))

let rec substitute_uni_list ls uni =
  match ls with
  | [] -> uni
  | ((tv,styp)::xs) -> substitute_uni_list xs (substitute_uni tv styp uni)

exception UnifyFail of uni_pair

let unify_val va vb =
  match(va, vb) with
  | (V_int, V_int) -> []
  | (V_bool, V_bool) -> []
  | _ -> raise (UnifyFail (Uni(T_val(va), T_val(vb))))

let rec find_unify (Uni(a, b)) =
  match (a, b) with
  | (T_val(va), T_val(vb)) -> unify_val va vb
  | (T_var(tv), _) -> [(tv, b)]
  | (_, T_var(tv)) -> [(tv, a)]
  | (T_func(p, q), T_func(x, y)) ->
      let upx = find_unify (Uni(p,x)) in
      let uqy = find_unify (Uni(q,y)) in
      (upx @ uqy)
  | _ -> raise (UnifyFail (Uni(a, b)))

let rec unify_many lst =
  match lst with
  | [] -> []
  | (up :: lst') ->
      let u1 = find_unify up in
      let lst'' = List.map lst' ~f:(substitute_uni_list u1) in
      let u2 = unify_many lst'' in
      (u1 @ u2)

let rec string_of_scheme_type typ =
  match typ with
  | T_var(vr) -> "'" ^ vr
  | T_val(V_int) -> "int"
  | T_val(V_bool) -> "bool"
  | T_func(a,b) -> "(" ^ (string_of_scheme_type a) ^ " -> " ^ (string_of_scheme_type b) ^ ")"

let string_of_scheme sch =
  match sch with
  | Forall([], typ) -> string_of_scheme_type typ
  | Forall(vars, typ) -> "forall " ^ (String.concat ~sep:"," vars) ^ ". " ^ (string_of_scheme_type typ)

let string_of_uni_pair (Uni(s1, s2)) =
  "uni(" ^ (string_of_scheme_type s1) ^ ", " ^ (string_of_scheme_type s2) ^ ")"

let rec string_of_uni_pair_list = function
  | [] -> ""
  | (pr::lst) -> (string_of_uni_pair pr) ^ ", " ^ (string_of_uni_pair_list lst)
