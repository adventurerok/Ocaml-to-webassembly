open Core_kernel
open Otwa_base
open Otwa_types
open Typed_ast
open Types


type func_rectype =
| Frt_simple (* No recursive calls *)
| Frt_tailrec (* Tail recursive calls only *)
| Frt_rec (* Some fully recursive calls *)

let func_rectype_to_string rectype =
  match rectype with
  | Frt_simple -> "simple"
  | Frt_tailrec -> "tailrec"
  | Frt_rec -> "rec"

type state = {
  func_name: string;
  mutable next_var: int;
}

type transform_state = {
  state: state;
  (* from var, ref var, from type *)
  copy_vars: (tident * tident * scheme_type) list;

  loop_name: string;
}


exception TailrecFailure of string

let add_var state =
  let var_id = state.next_var in
  state.next_var <- var_id + 1;
  var_id


let worst_rectype types =
  List.fold types ~init:Frt_simple ~f:(fun acc typ ->
    match acc, typ with
    | Frt_rec, _ -> Frt_rec
    | _, Frt_rec -> Frt_rec
    | Frt_tailrec, _ -> Frt_tailrec
    | _, Frt_tailrec -> Frt_tailrec
    | _ -> Frt_simple
  )


let rec get_rectype state (expr : texpression) =
  match expr.texp_desc with
  | Texp_ident _ -> Frt_simple
  | Texp_constant _ -> Frt_simple
  | Texp_let (_, tvb_list, inner) ->
      if are_exprs_recursive state (List.map tvb_list ~f:(fun tvb -> tvb.tvb_expr)) then
        Frt_rec
      else
        get_rectype state inner
  | Texp_fun (_, _) -> Frt_simple
  | Texp_apply (a, blist) -> get_rectype_apply state a blist
  | Texp_special (mode, name, args) -> get_rectype_special state mode name args
  | Texp_match (e, cases) ->
      if are_exprs_recursive state [e] then
        Frt_rec
      else
        worst_rectype (List.map cases ~f:(fun case -> get_rectype state case.tc_rhs))
  | Texp_tuple(args) ->
      if are_exprs_recursive state args then
        Frt_rec
      else
        Frt_simple
  | Texp_construct (_, args) ->
      if are_exprs_recursive state args then
        Frt_rec
      else
        Frt_simple
  | Texp_ifthenelse (i, t, e_opt) ->
      if are_exprs_recursive state [i] then
        Frt_rec
      else
        worst_rectype (List.map (t :: (Option.to_list e_opt)) ~f:(get_rectype state))
  | Texp_while (cond, inner) ->
      if are_exprs_recursive state [cond; inner] then
        Frt_rec
      else
        Frt_simple
  | Texp_for (_, min, max, _, inner) ->
      if are_exprs_recursive state [min; max; inner] then
        Frt_rec
      else
        Frt_simple
  | Texp_sequence (a, b) ->
      if are_exprs_recursive state [a] then
        Frt_rec
      else
        get_rectype state b


and are_exprs_recursive state args =
  List.exists args ~f:(fun arg ->
    let arg_rectype = get_rectype state arg in
    match arg_rectype with
    | Frt_simple -> false
    | _ -> true)


and get_rectype_apply state _fexpr args =
  if are_exprs_recursive state args then
    Frt_rec
  else
    Frt_simple


and get_rectype_special state mode name args =
  if are_exprs_recursive state args then
    Frt_rec
  else
    match mode with
    | Tspec_mkclosure -> Frt_simple
    | Tspec_directapply ->
        if String.equal state.func_name name then
          Frt_tailrec
        else
          Frt_simple (* We can keep calls to other functions in our loop *)
    | Tspec_namedloop -> Frt_simple
    | Tspec_breakloop -> Frt_simple
    | Tspec_continueloop -> Frt_simple


(* An expression to make a ref of tid of type st *)
let make_ref expr st =
  let ref_typ = T_constr("ref", [st]) in
  let ref_ident = {
    texp_loc = Location.none;
    texp_type = T_func(st, ref_typ);
    texp_desc = Texp_ident(("ref", -1))
  }
  in
  {
    texp_loc = Location.none;
    texp_type = ref_typ;
    texp_desc = Texp_apply(ref_ident, [expr])
  }


let make_deref ref_id st =
  let ref_typ = T_constr("ref", [st]) in
  let ident = {
    texp_loc = Location.none;
    texp_type = ref_typ;
    texp_desc = Texp_ident(ref_id)
  }
  in
  let deref_ident = {
    texp_loc = Location.none;
    texp_type = T_func(ref_typ, st);
    texp_desc = Texp_ident(("!", -1))
  }
  in
  {
    texp_loc = Location.none;
    texp_type = st;
    texp_desc = Texp_apply(deref_ident, [ident])
  }

let make_assign expr ref_id st =
  let ref_typ = T_constr("ref", [st]) in
  let ref_ident = {
    texp_loc = Location.none;
    texp_type = ref_typ;
    texp_desc = Texp_ident(ref_id)
  }
  in
  let assign_ident = {
    texp_loc = Location.none;
    texp_type = T_func(ref_typ, T_func(st, Predefined.v_unit));
    texp_desc = Texp_ident((":=", -1))
  }
  in
  {
    texp_loc = Location.none;
    texp_type = Predefined.v_unit;
    texp_desc = Texp_apply(assign_ident, [ref_ident; expr])
  }



let make_ref_tvbs copylst =
  List.map copylst ~f:(fun (from, to_ref, st) ->
    let from_expr = {
      texp_loc = Location.none;
      texp_type = st;
      texp_desc = Texp_ident(from);
    }
    in
    let expr = make_ref from_expr st in
    let pat = {
      tpat_loc = Location.none;
      tpat_type = T_constr("ref", [st]);
      tpat_desc = Tpat_var(to_ref);
      tpat_vars = [(to_ref, T_constr("ref", [st]))]
    }
    in
    {
      tvb_pat = pat;
      tvb_expr = expr;
      tvb_vars = [(to_ref, Forall(Set.Poly.empty, T_constr("ref", [st])))]
    }
  )


let rec tailrec_expr tstate expr =
  let desc =
    match expr.texp_desc with
    | Texp_ident _ -> expr.texp_desc
    | Texp_constant _ -> expr.texp_desc
    | Texp_let (rf, tvbs, inner) ->
        Texp_let(rf, tvbs, tailrec_expr tstate inner)
    | Texp_fun (_, _) -> expr.texp_desc
    | Texp_apply (_, _) -> expr.texp_desc
    | Texp_special (mode, name, args) -> tailrec_expr_special tstate mode name args
    | Texp_match (e, cases) ->
        let cases' = List.map cases ~f:(fun case ->
          let expr' = tailrec_expr tstate case.tc_rhs in
          {case with tc_rhs = expr'})
        in
        Texp_match(e, cases')
    | Texp_tuple _ -> expr.texp_desc
    | Texp_construct (_, _) -> expr.texp_desc
    | Texp_ifthenelse (i, t, e_opt) ->
        let t' = tailrec_expr tstate t in
        let e_opt' = Option.map e_opt ~f:(tailrec_expr tstate) in
        Texp_ifthenelse(i, t', e_opt')
    | Texp_while (_, _) -> expr.texp_desc
    | Texp_for (_, _, _, _, _) -> expr.texp_desc
    | Texp_sequence (a, b) ->
        Texp_sequence(a, tailrec_expr tstate b)
  in {expr with texp_desc = desc}


and tailrec_expr_special tstate mode name args =
  match mode with
  | Tspec_mkclosure -> Texp_special(mode, name, args)
  | Tspec_directapply ->
      if String.equal tstate.state.func_name name then
        (* A tailrecursive call *)
        let arg_tuple = List.hd_exn args in
        let inner_args =
          match arg_tuple.texp_desc with
          | Texp_tuple(inargs) -> inargs
          | _ -> raise (TailrecFailure("Expected tuple of arguments"))
        in
        let copy_exprs = List.map2_exn tstate.copy_vars inner_args ~f:(fun (_, ref_id, st) arg ->
          make_assign arg ref_id st)
        in
        let continue_expr = {
          texp_loc = Location.none;
          texp_type = Predefined.v_unit;
          texp_desc = Texp_special(Tspec_continueloop, tstate.loop_name, [])
        }
        in
        let seq_expr = List.fold_right copy_exprs ~init:continue_expr ~f:(fun x prev ->
          {
            texp_loc = Location.none;
            texp_type = Predefined.v_unit;
            texp_desc = Texp_sequence(x, prev)
          }
        )
        in
        seq_expr.texp_desc
      else
        Texp_special(mode, name, args)
  | Tspec_namedloop -> Texp_special(mode, name, args)
  | Tspec_continueloop -> Texp_special(mode, name, args)
  | Tspec_breakloop -> Texp_special(mode, name, args)


let tailrec_function state (func : Functions.func_data) =
  let old_arg, new_arg, new_pat =
    match func.fd_pat.tpat_desc with
    | Tpat_var((name, uid)) ->
        let new_arg = (name ^ "_in", add_var state) in
        ((name, uid), new_arg, { func.fd_pat with tpat_desc = Tpat_var(new_arg) })
    | _ ->
        raise (TailrecFailure("Function argument must be single var"))
  in
  let new_cvars = List.map func.fd_cvars ~f:(fun ((name, _), st) ->
    ((name ^ "_in", add_var state), st))
  in
  let arg_ref =
    match old_arg with
    | (name, _) -> (name ^ "_ref", add_var state)
  in
  let cvar_refs =
    List.map func.fd_cvars ~f:(fun ((name, _), _) ->
      (name ^ "_ref", add_var state))
  in
  let copy_vars =
    (List.map2_exn func.fd_cvars cvar_refs ~f:(fun (old_cvar, st) cvar_ref ->
      (old_cvar, cvar_ref, st)))
    @
    [(old_arg, arg_ref, new_pat.tpat_type)]
  in
  let transform_state = {
    state = state;
    copy_vars = copy_vars;
    loop_name = "tailrec_loop"
  }
  in
  (* The inside of the loop *)
  let inner = tailrec_expr transform_state func.fd_expr in
  let initial_copy_vars =
    (List.map2_exn new_cvars cvar_refs ~f:(fun (old_cvar, st) cvar_ref ->
      (old_cvar, cvar_ref, st)))
    @
    [(new_arg, arg_ref, new_pat.tpat_type)]
  in
  let result_ref = ("result", add_var state) in
  let result_type = func.fd_expr.texp_type in
  let inner_assign = make_assign inner result_ref result_type in
  let inner_tvbs = List.map transform_state.copy_vars ~f:(fun (old, ref_id, st) ->
    let expr = make_deref ref_id st in
    let pat = {
      tpat_loc = Location.none;
      tpat_type = st;
      tpat_vars = [(old, st)];
      tpat_desc = Tpat_var(old)
    }
    in {
      tvb_pat = pat;
      tvb_expr = expr;
      tvb_vars = [(old, Forall(Set.Poly.empty, st))]
    }
  )
  in
  let inner_with_bindings = List.fold_right inner_tvbs ~init:inner_assign ~f:(fun tvb expr ->
    {
      texp_loc = Location.none;
      texp_type = expr.texp_type;
      texp_desc = Texp_let(Asttypes.Nonrecursive, [tvb], expr)
    }
  )
  in
  let inner_escape = {
    texp_loc = Location.none;
    texp_type = Predefined.v_unit;
    texp_desc = Texp_special(Tspec_breakloop, transform_state.loop_name, []);
  }
  in
  let inner_with_escape = {
    texp_loc = Location.none;
    texp_type = Predefined.v_unit;
    texp_desc = Texp_sequence(inner_with_bindings, inner_escape)
  }
  in
  let inner_loop = {
    texp_loc = Location.none;
    texp_type = Predefined.v_unit;
    texp_desc = Texp_special(Tspec_namedloop, transform_state.loop_name, [inner_with_escape])
  }
  in
  let initial_tvbs = make_ref_tvbs initial_copy_vars in
  let loop_and_deref = {
    texp_loc = Location.none;
    texp_type = result_type;
    texp_desc = Texp_sequence(inner_loop, make_deref result_ref result_type)
  }
  in
  let result_pat = {
    tpat_loc = Location.none;
    tpat_type = T_constr("ref", [result_type]);
    tpat_vars = [(result_ref, T_constr("ref", [result_type]))];
    tpat_desc = Tpat_var(result_ref);
  }
  in
  let unit_expr = {
    texp_loc = Location.none;
    texp_type = Predefined.v_unit;
    texp_desc = Texp_constant("()");
  }
  in
  let result_expr = make_ref unit_expr result_type in
  let result_tvb = {
    tvb_pat = result_pat;
    tvb_expr = result_expr;
    tvb_vars = [(result_ref, Forall(Set.Poly.empty, T_constr("ref", [result_type])))]
  }
  in
  let outer_with_bindings = List.fold_right (initial_tvbs @ [result_tvb]) ~init:loop_and_deref ~f:(fun tvb expr ->
    {
      texp_loc = Location.none;
      texp_type = expr.texp_type;
      texp_desc = Texp_let(Asttypes.Nonrecursive, [tvb], expr)
    }
  )
  in
  {
    func with
    fd_pat = new_pat;
    fd_cvars = new_cvars;
    fd_expr = outer_with_bindings
  }


let tail_recursion_transform (funcs : Functions.func_data list) next_var =
  if not Config.global.optimise_tail_calls then
    (funcs, next_var)
  else
    let next_var_ref = ref next_var in
    (List.map funcs ~f:(fun func ->
      let state = {
        func_name = func.fd_name;
        next_var = !next_var_ref
      }
      in
      let rectype = get_rectype state func.fd_expr in
      let result =
        match rectype with
        | Frt_tailrec -> tailrec_function state func
        | _ -> func
      in
      next_var_ref := state.next_var;
      result
    ), !next_var_ref)
