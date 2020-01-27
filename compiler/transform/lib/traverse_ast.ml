open Core_kernel
open Otwa_types
open Typed_ast


type let_binding = Asttypes.rec_flag * tvalue_binding list * texpression option;;

(* 'a is the state object
 * 'b is the input object
 * 'c is the output object *)
type ('a, 'b, 'c) traverser = {

  (* Turns state and input into an output if no child nodes available *)
  leaf: 'a -> 'b -> 'c;

  (* Traversal *)
  pre_expr : 'a -> 'b -> texpression -> ('b * texpression);
  post_expr: 'a -> 'c list -> texpression -> ('c * texpression);
  pre_value_binding: 'a -> 'b -> tvalue_binding -> ('b * tvalue_binding);
  mid_value_binding: 'a -> 'b -> 'c -> tvalue_binding -> ('b * tvalue_binding);
  post_value_binding: 'a -> 'c list -> tvalue_binding -> ('c * tvalue_binding);

  (* Another let special case, allows two different inputs to be computed for bindings and the resulting expression *)
  (* state input let_expr -> tvb_input inner_input let_expr *)
  pre_let: 'a -> 'b -> let_binding -> ('b * 'b * tvalue_binding list);

  (* Special case that allows different input to be computed for let expression based on the output of the values *)
  (* state tvb_input inner_input tvb_output let_expr -> inner_input let_expr *)
  mid_let: 'a -> 'b -> 'b -> 'c list -> let_binding -> ('b * tvalue_binding list);

  pre_case: 'a -> 'b -> tcase -> ('b * tcase);
  mid_case: 'a -> 'b -> 'c -> tcase -> ('b * tcase);
  post_case: 'a -> 'c list -> tcase -> ('c * tcase);
  pre_pattern: 'a -> 'b -> tpattern -> ('b * tpattern);
  post_pattern: 'a -> 'c list -> tpattern -> ('c * tpattern);
  pre_structure_item: 'a -> 'b -> tstructure_item -> ('b * tstructure_item);
  post_structure_item: 'a -> 'c list -> tstructure_item -> ('c * tstructure_item);
  pre_structure: 'a -> 'b -> tstructure -> ('b * tstructure);
  post_structure: 'a -> 'c list -> tstructure -> ('c * tstructure);
}


(* Leaf gives an output from a state and input *)
(* Merge merges outputs (only used if no implementation available for a function) *)
(* Step inputs changes the input (only used if no implementation available for a function) *)
let base_traverser leaf merge step_input =
  {
    leaf = leaf;
    pre_expr = (fun state input expr ->
      (step_input state input, expr));
    post_expr = (fun state outputs expr ->
      (merge state outputs, expr));
    pre_value_binding = (fun state input value_binding ->
      (step_input state input, value_binding));
    mid_value_binding = (fun _ input _ value_binding -> (input, value_binding));
    post_value_binding = (fun state outputs value_binding ->
      (merge state outputs, value_binding));
    pre_let = (fun _ input (_,l,_) -> (input, input, l));
    mid_let = (fun _ _ input _ (_,l,_) -> (input, l));
    pre_case = (fun state input case ->
      (step_input state input, case));
    mid_case = (fun _ input _ case -> (input, case));
    post_case = (fun state outputs case ->
      (merge state outputs, case));
    pre_pattern = (fun state input pattern ->
      (step_input state input, pattern));
    post_pattern = (fun state outputs pattern ->
      (merge state outputs, pattern));
    pre_structure_item = (fun state input structure_item ->
      (step_input state input, structure_item));
    post_structure_item = (fun state outputs structure_item ->
      (merge state outputs, structure_item));
    pre_structure = (fun state input structure ->
      (step_input state input, structure));
    post_structure = (fun state outputs structure ->
      (merge state outputs, structure));
  }

let no_output_traverser step_input =
  let leaf _ _ = () in
  let merge _ _ = () in
  base_traverser leaf merge step_input

let rec traverse_expr trav state input expr =
  let (input', expr1) = trav.pre_expr state input expr in
  let (outputs, expr2_desc) =
    match expr1.texp_desc with
    | Texp_ident(_)
    | Texp_constant(_) -> ([trav.leaf state input'], expr1.texp_desc)
    | Texp_let(rf, tvb_lst, inner) ->
        let (tvb_in, inner_in, tvb_lst1) = trav.pre_let state input' (rf, tvb_lst, Some(inner)) in
        let (tvb_outs, tvb_lst2) = List.unzip (List.map tvb_lst1 ~f:(traverse_value_binding trav state tvb_in)) in
        let (inner_in1, tvb_lst3) = trav.mid_let state tvb_in inner_in tvb_outs (rf, tvb_lst2, Some(inner)) in
        let (inner_out, inner2) = traverse_expr trav state inner_in1 inner in
        (tvb_outs @ [inner_out], Texp_let(rf, tvb_lst3, inner2))
    | Texp_fun (p, e) ->
        let (o1, p') = traverse_pat trav state input' p in
        let (o2, e') = traverse_expr trav state input' e in
        ([o1; o2], Texp_fun(p', e'))
    | Texp_apply (f, ls) ->
        let (o1, f') = traverse_expr trav state input' f in
        let (outs, ls') = List.unzip (List.map ls ~f:(traverse_expr trav state input')) in
        (o1 :: outs, Texp_apply(f', ls'))
    | Texp_match (e, cases) ->
        let (o1, e') = traverse_expr trav state input' e in
        let (outs, cases') = List.unzip (List.map cases ~f:(traverse_case trav state input')) in
        (o1 :: outs, Texp_match(e', cases'))
    | Texp_tuple(ls) ->
        let (outs, ls') = List.unzip (List.map ls ~f:(traverse_expr trav state input')) in
        (outs, Texp_tuple(ls'))
    | Texp_construct (name, ls) ->
        let (outs, ls') = List.unzip (List.map ls ~f:(traverse_expr trav state input')) in
        (outs, Texp_construct(name, ls'))
    | Texp_ifthenelse (i, t, e_opt) ->
        let (o1, i') = traverse_expr trav state input' i in
        let (o2, t') = traverse_expr trav state input' t in
        (match e_opt with
        | Some(e) ->
            let (o3, e') = traverse_expr trav state input' e in
            ([o1; o2; o3], Texp_ifthenelse(i', t', Some(e')))
        | None ->
            ([o1; o2], Texp_ifthenelse(i', t', None)))
    | Texp_while (c, i) ->
        let (o1, c') = traverse_expr trav state input' c in
        let (o2, i') = traverse_expr trav state input' i in
        ([o1; o2], Texp_while(c', i'))
    | Texp_for (v, min, max, dir, inner) ->
        let (o1, min') = traverse_expr trav state input' min in
        let (o2, max') = traverse_expr trav state input' max in
        let (o3, inner') = traverse_expr trav state input' inner in
        ([o1; o2; o3], Texp_for(v, min', max', dir, inner'))
    | Texp_sequence (a, b) ->
        let (o1, a') = traverse_expr trav state input' a in
        let (o2, b') = traverse_expr trav state input' b in
        ([o1; o2], Texp_sequence(a', b'))
  in
  trav.post_expr state outputs {expr1 with texp_desc = expr2_desc}

and traverse_value_binding trav state input tvb =
  let (input', tvb1) = trav.pre_value_binding state input tvb in
  let (o1, pat') = traverse_pat trav state input' tvb1.tvb_pat in
  let (input2, tvb2) = trav.mid_value_binding state input' o1 tvb1 in
  let (o2, expr') = traverse_expr trav state input2 tvb2.tvb_expr in
  let tvb3 = {
    tvb1 with
    tvb_pat = pat';
    tvb_expr = expr';
  }
  in
  trav.post_value_binding state [o1; o2] tvb3

and traverse_case trav state input case =
  let (input', case1) = trav.pre_case state input case in
  let (o1, pat') = traverse_pat trav state input' case1.tc_lhs in
  let (input2, case2) = trav.mid_case state input' o1 case in
  let (o2, expr') = traverse_expr trav state input2 case2.tc_rhs in
  let case3 = {
    tc_lhs = pat';
    tc_rhs = expr';
  }
  in
  trav.post_case state [o1; o2] case3

and traverse_pat trav state input pat =
  let (input', pat1) = trav.pre_pattern state input pat in
  let(outputs, pat2_desc) =
    match pat1.tpat_desc with
    | Tpat_any
    | Tpat_var(_)
    | Tpat_constant _ -> ([trav.leaf state input'], pat.tpat_desc)
    | Tpat_tuple(ls) ->
        let (outputs, ls') = List.unzip (List.map ls ~f:(traverse_pat trav state input')) in
        (outputs, Tpat_tuple(ls'))
    | Tpat_construct (name, ls) ->
        let (outputs, ls') = List.unzip (List.map ls ~f:(traverse_pat trav state input')) in
        (outputs, Tpat_construct(name, ls'))
  in
  let pat2 = {pat1 with tpat_desc = pat2_desc } in
  trav.post_pattern state outputs pat2

let traverse_structure_item trav state input item =
  let (input', item1) = trav.pre_structure_item state input item in
  let (outputs, item2_desc) =
    match item1.tstr_desc with
    | Tstr_eval(e) ->
        let (o1, e') = traverse_expr trav state input' e in
        ([o1], Tstr_eval(e'))
    | Tstr_value (rf, tvb_lst) ->
        let (tvb_in, inner_in, tvb_lst1) = trav.pre_let state input' (rf, tvb_lst, None) in
        let (outputs, tvb_lst2) = List.unzip (List.map tvb_lst1 ~f:(traverse_value_binding trav state tvb_in)) in
        let (_, tvb_lst3) = trav.mid_let state tvb_in inner_in outputs (rf, tvb_lst2, None) in
        (outputs, Tstr_value(rf, tvb_lst3))
    | Tstr_type -> ([trav.leaf state input'], item1.tstr_desc)
  in
  let item2 = {item1 with tstr_desc = item2_desc} in
  trav.post_structure_item state outputs item2

let traverse_structure trav state input struc =
  let (input', struc1) = trav.pre_structure state input struc in
  let (outputs, struc2) = List.unzip (List.map struc1 ~f:(traverse_structure_item trav state input')) in
  trav.post_structure state outputs struc2
