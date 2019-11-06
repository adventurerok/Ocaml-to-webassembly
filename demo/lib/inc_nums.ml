open Core_kernel
open Parsetree

let rec update_const (const : constant) = match const with
  | Pconst_integer(str, _) ->
      let i = Int.of_string str in
      let added = i + 1 in
      let str' = Int.to_string added in
      (Pconst_integer(str', None))
  | _ -> const

and update_args (args : (Asttypes.arg_label * expression) list) = match args with
  | [] -> []
  | ((label,expr)::args') -> ((label, update_expr expr) :: (update_args args'))

and update_pat_desc (desc : pattern_desc) = match desc with
  | Ppat_constant(const) -> Ppat_constant(update_const const)
  | _ -> desc

and update_pat (pat : pattern) =
  {pat with ppat_desc = update_pat_desc pat.ppat_desc}

and update_cases (args : case list) = match args with
  | [] -> []
  | (case::cases') ->
      (({ case with
          pc_rhs = update_expr case.pc_rhs;
          pc_lhs = update_pat case.pc_lhs
      }) :: (update_cases cases'))

and update_expr_desc (desc : expression_desc) = match desc with
  | Pexp_constant(const) -> Pexp_constant(update_const const)
  | Pexp_apply(expr, lst) -> Pexp_apply(update_expr expr, update_args lst)
  | Pexp_function(cases) -> Pexp_function(update_cases cases)
  | Pexp_fun(label, optexpr, pat, expr) -> Pexp_fun(label, optexpr, pat, update_expr expr)
  | Pexp_tuple(exprs) -> Pexp_tuple(List.map exprs ~f:update_expr)
  | Pexp_ifthenelse(iexpr, texpr, eexpropt) ->
      Pexp_ifthenelse(update_expr iexpr, update_expr texpr, Option.map ~f:update_expr eexpropt)
  | Pexp_let(rflag, bindings, expr) -> Pexp_let(rflag, update_bindings bindings, update_expr expr)
  | Pexp_match(expr, cases) -> Pexp_match(update_expr expr, update_cases cases)
  | Pexp_try(expr, cases) -> Pexp_try(update_expr expr, update_cases cases)
  | Pexp_array(exprs) -> Pexp_array(List.map ~f:update_expr exprs)
  | Pexp_construct(loc, expropt) -> Pexp_construct(loc, Option.map ~f:update_expr expropt)
  | _ -> desc

and update_expr (expr : expression) =
  {expr with pexp_desc = update_expr_desc expr.pexp_desc}

and update_bindings (bindings : value_binding list) = match bindings with
  | [] -> []
  | (bind::bindings) -> ({bind with pvb_expr = update_expr bind.pvb_expr}) :: bindings


and handle_desc (desc : structure_item_desc) = match desc with
  | Pstr_value(a,bindings) -> Pstr_value(a,update_bindings bindings)
  | Pstr_eval(expr, attrib) -> Pstr_eval(update_expr expr, attrib)
  | _ -> desc

and inc_nums (struc : structure) = match struc with
  | [] -> []
  | (struc_item::more) ->
      (({struc_item with pstr_desc = handle_desc struc_item.pstr_desc}) :: (inc_nums more))
