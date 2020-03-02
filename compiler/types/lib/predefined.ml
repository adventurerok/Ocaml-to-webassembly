open Core_kernel
open Types

let v_int = T_val(V_int)
let v_bool = T_val(V_bool)
let v_unit = T_val(V_unit)
let v_float = T_val(V_float)

let f_ii = Forall(Set.Poly.empty, T_func(v_int, v_int))
let f_bb = Forall(Set.Poly.empty, T_func(v_bool, v_bool))
let f_iii = Forall(Set.Poly.empty, T_func(v_int, T_func(v_int, v_int)))
let f_iib = Forall(Set.Poly.empty, T_func(v_int, T_func(v_int, v_bool)))
let f_bbb = Forall(Set.Poly.empty, T_func(v_bool, T_func(v_bool, v_bool)))
let f_ff = Forall(Set.Poly.empty, T_func(v_float, v_float))
let f_fff = Forall(Set.Poly.empty, T_func(v_float, T_func(v_float, v_float)))
let f_ffb = Forall(Set.Poly.empty, T_func(v_float, T_func(v_float, v_bool)))

let f_aaa = Forall(Set.Poly.of_list ["a"; "b"; "c"], T_func(T_var("a"), T_func(T_var("b"), T_var("c"))))
let f_aab = Forall(Set.Poly.of_list ["a"; "b"], T_func(T_var("a"), T_func(T_var("b"), v_bool)))

let ref_a = T_constr("ref", [T_var("a")])

let ident_map = Map.Poly.of_alist_exn
  [
    ("+", f_iii);
    ("-", f_iii);
    ("*", f_iii);
    ("/", f_iii);
    ("mod", f_iii);
    ("<", f_aab);
    (">", f_aab);
    ("<=", f_aab);
    (">=", f_aab);
    ("=", f_aab);
    ("!=", f_aab);
    ("&&", f_bbb);
    ("||", f_bbb);
    ("~-", f_ii);
    ("+.", f_fff);
    ("-.", f_fff);
    ("*.", f_fff);
    ("/.", f_fff);
    ("~-.", f_ff);
    ("not", f_bb);
    ("ref", Forall(Set.Poly.singleton "a", T_func(T_var("a"), ref_a)));
    (":=", Forall(Set.Poly.singleton "a", T_func(ref_a, T_func(T_var("a"), v_unit))));
    ("!", Forall(Set.Poly.singleton "a", T_func(ref_a, T_var("a"))))
  ]

let lookup_ident = Map.find ident_map
