open Core_kernel
open Parsetree
open Types

type texpression = {
  texp_desc : texpression_desc;
  texp_loc: Location.t;
  texp_type: scheme_type
}

and texpression_desc =
  Texp_ident of string
| Texp_constant of constant
| Texp_let of Asttypes.rec_flag * tvalue_binding list * texpression
| Texp_fun of tpattern * texpression
| Texp_apply of texpression * texpression list
| Texp_match of texpression * tcase list
| Texp_tuple of texpression list
| Texp_construct of string * texpression option
| Texp_ifthenelse of texpression * texpression * texpression option
(* No need for Texp_constraint *)

and tvalue_binding = {
  tvb_pat : tpattern;
  tvb_expr: texpression;
  tvb_vars: (string * scheme) list
}

and tcase = {
  tc_lhs: tpattern;
  tc_rhs: texpression;
}

and tpattern = {
  tpat_desc: tpattern_desc;
  tpat_loc: Location.t;
  tpat_type: scheme_type;
  tpat_vars: (string * scheme_type) list
}

and tpattern_desc =
  Tpat_var of string
| Tpat_constant of constant
| Tpat_tuple of tpattern list
| Tpat_construct of string * tpattern option

and tstructure = tstructure_item list

and tstructure_item = {
  tstr_desc: tstructure_item_desc;
  tstr_loc: Location.t;
  tstr_type: scheme_type
}

and tstructure_item_desc =
  Tstr_eval of texpression
| Tstr_value of Asttypes.rec_flag * tvalue_binding list
| Tstr_type

let rec tstructure_to_string tstr =
  String.concat ~sep:";;" (List.map tstr ~f:tstructure_item_to_string)

and tstructure_item_to_string si =
  match si.tstr_desc with
  | Tstr_eval(expr) -> texpression_to_string expr
  | Tstr_value(rf, vb) -> tvalue_bindings_to_string rf vb
  | Tstr_type -> "type"

and texpression_to_string (texpr : texpression) =
  "(" ^
  (match texpr.texp_desc with
  | Texp_ident(str) -> str
  | Texp_constant(const) -> constant_to_string const
  | Texp_let (rf, vb, texpr') -> (tvalue_bindings_to_string rf vb) ^ " in " ^ (texpression_to_string texpr')
  | Texp_fun (p, e) -> "fun " ^ (tpattern_to_string p) ^ " -> " ^ (texpression_to_string e)
  | Texp_apply (a, b) -> String.concat ~sep:" " (List.map (a :: b) ~f:texpression_to_string)
  | Texp_match (e, m) -> "match " ^ (texpression_to_string e) ^ " with " ^ (tcases_to_string m)
  | Texp_tuple (ls) -> "(" ^ (String.concat ~sep:", " (List.map ls ~f:texpression_to_string)) ^ ")"
  | Texp_construct (name, expropt) -> name ^ (Option.value_map expropt ~default:"" ~f:texpression_to_string)
  | Texp_ifthenelse (i, t, e_opt) ->
      "if " ^ (texpression_to_string i) ^
      " then " ^ (texpression_to_string t) ^
      (Option.value_map e_opt ~default:"" ~f:(fun e -> " else " ^ (texpression_to_string e))))
  ^ " : " ^ (string_of_scheme_type texpr.texp_type) ^ ")"

and tvalue_bindings_to_string rf vbl =
  "let " ^ (match rf with | Asttypes.Nonrecursive -> "" | Asttypes.Recursive -> "rec ")
  ^ (String.concat ~sep:" and " (List.map vbl ~f:tvalue_binding_to_string))

and tvalue_binding_to_string vb =
  (tpattern_to_string vb.tvb_pat) ^ " = " ^ (texpression_to_string vb.tvb_expr)

and tpattern_to_string pat =
  (match pat.tpat_desc with
  | Tpat_var(str) -> str
  | Tpat_constant(const) -> constant_to_string const
  | Tpat_tuple(ls) -> "(" ^ (String.concat ~sep:", " (List.map ls ~f:tpattern_to_string)) ^ ")"
  | Tpat_construct(name, patopt) -> name ^ (Option.value_map patopt ~default:"" ~f:tpattern_to_string))

and tcases_to_string cases =
  String.concat ~sep:" | " (List.map cases ~f:tcase_to_string)

and tcase_to_string case =
  (tpattern_to_string case.tc_lhs) ^ " -> " ^ (texpression_to_string case.tc_rhs)

and constant_to_string const =
  (match const with
  | Pconst_integer (str, _) -> str
  | Pconst_char(c) -> Char.to_string c
  | Pconst_string (str, _) -> str
  | Pconst_float (str, _) -> str)

let rec texpression_map_types sf stf texp =
  let desc =
    match texp.texp_desc with
    | Texp_let (recflag, tvb_lst, lexp) ->
        let tvb_lst' = tvalue_bindings_map_types sf stf tvb_lst in
        let lexp' = texpression_map_types sf stf lexp in
        Texp_let(recflag, tvb_lst', lexp')
    | Texp_fun (a, b) -> Texp_fun(tpattern_map_types sf stf a, texpression_map_types sf stf b)
    | Texp_apply (fexp, exp_lst) ->
        let fexp' = texpression_map_types sf stf fexp in
        let exp_lst' = List.map exp_lst ~f:(texpression_map_types sf stf) in
        Texp_apply(fexp', exp_lst')
    | Texp_match (mexp, c_lst) ->
        let mexp' = texpression_map_types sf stf mexp in
        let c_lst' = tcases_map_types sf stf c_lst in
        Texp_match(mexp', c_lst')
    | Texp_tuple (ls) -> Texp_tuple(List.map ls ~f:(texpression_map_types sf stf))
    | Texp_construct (name, exp_opt) ->
        let exp_opt' = Option.map exp_opt ~f:(texpression_map_types sf stf) in
        Texp_construct(name, exp_opt')
    | Texp_ifthenelse (iexp, texp, eexp_opt) ->
        let iexp' = texpression_map_types sf stf iexp in
        let texp' = texpression_map_types sf stf texp in
        let eexp_opt' = Option.map eexp_opt ~f:(texpression_map_types sf stf) in
        Texp_ifthenelse(iexp', texp', eexp_opt')
    | d -> d
  in {
    texp with
    texp_desc = desc;
    texp_type = (stf texp.texp_type)
  }

and tpattern_map_types sf stf tpat =
  let desc =
    match tpat.tpat_desc with
    | Tpat_tuple (ls) -> Tpat_tuple(List.map ls ~f:(tpattern_map_types sf stf))
    | Tpat_construct (name, pat_opt) ->
        let pat_opt' = Option.map pat_opt ~f:(tpattern_map_types sf stf) in
        Tpat_construct(name, pat_opt')
    | d -> d
  in {
    tpat with
    tpat_desc = desc;
    tpat_type = (stf tpat.tpat_type);
    tpat_vars = List.map tpat.tpat_vars ~f:(fun (v,t) -> (v, stf t))
  }

and tvalue_bindings_map_types sf stf tvb_lst =
  List.map tvb_lst ~f:(tvalue_binding_map_types sf stf)

and tvalue_binding_map_types sf stf tvb =
  {
    tvb_pat = tpattern_map_types sf stf tvb.tvb_pat;
    tvb_expr = texpression_map_types sf stf tvb.tvb_expr;
    tvb_vars = List.map tvb.tvb_vars ~f:(fun (v,s) -> (v, sf s))
  }

and tcases_map_types sf stf cases =
  List.map cases ~f:(tcase_map_types sf stf)

and tcase_map_types sf stf case =
  {
    tc_lhs = tpattern_map_types sf stf case.tc_lhs;
    tc_rhs = texpression_map_types sf stf case.tc_rhs
  }
