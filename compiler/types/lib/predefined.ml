open Base
open Types

let v_int = T_val(V_int)
let v_bool = T_val(V_bool)
let v_unit = T_val(V_unit)

let f_ii = T_func(v_int, v_int)
let f_bb = T_func(v_bool, v_bool)
let f_iii = T_func(v_int, f_ii)
let f_iib = T_func(v_int, T_func(v_int, v_bool))
let f_bbb = T_func(v_bool, f_bb)

let ident_map = Map.of_alist_exn (module String)
  [
    ("+", f_iii);
    ("-", f_iii);
    ("*", f_iii);
    ("/", f_iii);
    ("<", f_iib);
    (">", f_iib);
    ("<=", f_iib);
    (">=", f_iib);
    ("=", f_iib);
    ("&&", f_bbb);
    ("||", f_bbb);
    ("~-", f_ii)
  ]

let lookup_ident = Map.find ident_map
