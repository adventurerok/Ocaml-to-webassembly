open Core_kernel
open Parsetree
open Types

let sexp_of_constant (c : constant) =
  let str = match c with
  | Pconst_integer (str, _) -> str
  | Pconst_char c -> Char.to_string c
  | Pconst_string (str, _) -> str
  | Pconst_float (str, _) -> str
  in String.sexp_of_t str

(* The typed AST definition *)
type texpression = {
  texp_desc : texpression_desc;
  texp_loc: Location.t [@sexp.opaque];
  texp_type: scheme_type
}

and texpression_desc =
  Texp_ident of string
| Texp_constant of string
| Texp_let of (Asttypes.rec_flag [@sexp.opaque]) * tvalue_binding list * texpression
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
  tpat_loc: Location.t [@sexp.opaque];
  tpat_type: scheme_type;
  tpat_vars: (string * scheme_type) list
}

and tpattern_desc =
  Tpat_var of string
| Tpat_constant of string
| Tpat_tuple of tpattern list
| Tpat_construct of string * tpattern option

and tstructure = tstructure_item list

and tstructure_item = {
  tstr_desc: tstructure_item_desc;
  tstr_loc: (Location.t [@sexp.opaque]);
  tstr_type: scheme_type
}

and tstructure_item_desc =
  Tstr_eval of texpression
| Tstr_value of Asttypes.rec_flag * tvalue_binding list
| Tstr_type

(* Functions to convert each to string *)
let rec tstructure_to_string tstr =
  String.concat ~sep:";;\n" (List.map tstr ~f:tstructure_item_to_string)

and tstructure_item_to_string si =
  match si.tstr_desc with
  | Tstr_eval(expr) -> texpression_to_string expr
  | Tstr_value(rf, vb) -> tvalue_bindings_to_string rf vb
  | Tstr_type -> "type"

and texpression_to_string (texpr : texpression) =
  "(" ^
  (match texpr.texp_desc with
  | Texp_ident(str) -> str
  | Texp_constant(const) -> const
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
  "(" ^
  (match pat.tpat_desc with
  | Tpat_var(str) -> str
  | Tpat_constant(const) -> const
  | Tpat_tuple(ls) -> "(" ^ (String.concat ~sep:", " (List.map ls ~f:tpattern_to_string)) ^ ")"
  | Tpat_construct(name, patopt) -> name ^ (Option.value_map patopt ~default:"" ~f:tpattern_to_string))
  ^ " : " ^ (string_of_scheme_type pat.tpat_type) ^ ")"

and tcases_to_string cases =
  String.concat ~sep:" | " (List.map cases ~f:tcase_to_string)

and tcase_to_string case =
  (tpattern_to_string case.tc_lhs) ^ " -> " ^ (texpression_to_string case.tc_rhs)


(* Functions to map all schemes and scheme_types in the tree *)
(* sf = scheme function: scheme -> scheme
 * stf = scheme type function: scheme_type -> scheme_type *)
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

(* Uses the map_types function to substitute *)
let texpression_substitute subs texp =
  texpression_map_types (substitute_scheme_list subs) (substitute_list subs) texp

let tpattern_substitute subs tpat =
  tpattern_map_types (substitute_scheme_list subs) (substitute_list subs) tpat

let merge_maps a b =
  Map.Poly.merge a b ~f:(fun ~key:_ p ->
    match p with
    | `Left(v) -> Some(v)
    | `Right(v) -> Some (v)
    | `Both(_, v) -> Some(v))

let merge_map_list mlist =
  List.fold ~init:(Map.Poly.empty) ~f:merge_maps mlist


(* Gets a map from var name to type, containing free vars in exp *)
let rec texpression_free_vars (exp : texpression) =
  match exp.texp_desc with
  | Texp_ident(id) -> Map.Poly.singleton id exp.texp_type
  | Texp_constant _ -> Map.Poly.empty
  | Texp_let (rf, tvb_list, e) ->
      let tvb_map = merge_map_list (List.map tvb_list ~f:(fun tvb -> texpression_free_vars tvb.tvb_expr)) in
      let vars = List.concat (List.map tvb_list ~f:(fun tvb ->
        let (names, _) = List.unzip tvb.tvb_vars in
        names))
      in
      let tvb_map' =
        (match rf with
        | Asttypes.Nonrecursive -> tvb_map
        | Asttypes.Recursive -> List.fold ~init:tvb_map ~f:(fun a v -> Map.Poly.remove a v) vars)
      in let emap = texpression_free_vars e in
      let emap' = List.fold ~init:emap ~f:(fun a v -> Map.Poly.remove a v) vars in
      merge_maps emap' tvb_map'
  | Texp_fun (p, e) ->
      let e_vars = texpression_free_vars e in
      List.fold ~init:e_vars ~f:(fun a (v, _) -> Map.Poly.remove a v) p.tpat_vars
  | Texp_apply (a, blist) -> merge_map_list ((texpression_free_vars a) :: (List.map blist ~f:texpression_free_vars))
  | Texp_match (e, cases) ->
      let emap = texpression_free_vars e in
      let cmaps = List.map cases ~f:(fun case ->
        let cexp_vars = texpression_free_vars case.tc_rhs in
        List.fold ~init:cexp_vars ~f:(fun a (v, _) -> Map.Poly.remove a v) case.tc_lhs.tpat_vars)
      in merge_map_list (emap :: cmaps)
  | Texp_tuple(ls) -> merge_map_list (List.map ls ~f:texpression_free_vars)
  | Texp_construct (_, expr_opt) ->
      (match expr_opt with
      | Some(e) -> texpression_free_vars e
      | None -> Map.Poly.empty)
  | Texp_ifthenelse (i, t, e_opt) ->
      let it_map = merge_maps (texpression_free_vars i) (texpression_free_vars t) in
      (match e_opt with
      | Some(e) -> merge_maps it_map (texpression_free_vars e)
      | None -> it_map)
