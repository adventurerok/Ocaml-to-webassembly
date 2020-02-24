open Core_kernel
open Otwa_types
open Typed_ast

type state = {
  (* Maps function name to data *)
  funcs: (string, Functions.func_data) Hashtbl.t;

  (* Maps unique ID to function closure name *)
  func_vars: (int, string) Hashtbl.t;


  (* Vars available at this point in time *)
  avail_vars: (string * int) Hash_set.t
}


exception DirectTransformException of string

let pat_id_or_exn pat =
  match pat.tpat_desc with
  | Tpat_var(id) -> id
  | _ -> raise (DirectTransformException "Expecting identifier pattern")

(* Recurse: should go into functions? *)
let rec dct_expr ?recurse:(recurse = true) state expr =
  let (desc, func) =
    match expr.texp_desc with
    | Texp_ident((name, vid)) ->
        (Texp_ident((name, vid)), Hashtbl.find state.func_vars vid)
    | Texp_constant _ ->
        (expr.texp_desc, None)
    | Texp_let (rf, tvb_list, e) ->
        let (tvb_list', clear) = dct_value_bindings state rf tvb_list in
        let (e', f) = dct_expr state e in
        clear ();
        (Texp_let(rf, tvb_list', e'), f)
    | Texp_fun (_, _) ->
        raise (DirectTransformException "Functions should be removed")
    | Texp_apply (a, blist) -> dct_apply ~recurse:recurse state a blist
    | Texp_special (mode, name, args) -> dct_special ~recurse:recurse state mode name args
    | Texp_match (e, cases) -> (dct_match state e cases, None)
    | Texp_tuple(lst) ->
        let (lst', _) = List.unzip (List.map lst ~f:(dct_expr state)) in
        (Texp_tuple(lst'), None)
    | Texp_construct (name, lst) ->
        let (lst', _) = List.unzip (List.map lst ~f:(dct_expr state)) in
        (Texp_construct(name, lst'), None)
    | Texp_ifthenelse (i, t, e_opt) ->
        let (i', _) = dct_expr state i in
        let (t', _) = dct_expr state t in
        let e' = Option.map e_opt ~f:(dct_expr_nofunc state) in
        (Texp_ifthenelse(i', t', e'), None)
    | Texp_while (cond, inner) ->
        let cond' = dct_expr_nofunc state cond in
        let inner' = dct_expr_nofunc state inner in
        (Texp_while(cond', inner'), None)
    | Texp_for (var_opt, min, max, dir, inner) ->
        let min' = dct_expr_nofunc state min in
        let max' = dct_expr_nofunc state max in
        let inner' = dct_expr_nofunc state inner in
        (Texp_for(var_opt, min', max', dir, inner'), None)
    | Texp_sequence (a, b) ->
        let a' = dct_expr_nofunc state a in
        let (b', f) = dct_expr state b in
        (Texp_sequence(a', b'), f)
  in ({expr with texp_desc = desc}, func)

and dct_expr_nofunc ?recurse:(recurse = false) state expr =
  let (expr', _) = dct_expr ~recurse:recurse state expr in
  expr'

and dct_apply ~recurse:recurse state fexpr args =
  let args' = List.map args ~f:(dct_expr_nofunc ~recurse:recurse state) in
  match fexpr.texp_desc with
  | Texp_ident((name, _)) ->
      let lookup = Predefined.lookup_ident name in
      (match lookup with
      | Some(_) -> (Texp_apply(fexpr, args'), None)
      | None ->
          dct_apply_closure state fexpr args
      )
  | _ -> dct_apply_closure state fexpr args

and dct_special ~recurse:recurse state mode name args =
  match mode with
  | Tspec_mkclosure ->
      dct_mk_closure ~recurse:recurse state name args
  | Tspec_directapply ->
      (* Our work is already done *)
      (Texp_special(Tspec_directapply, name, args), None)

and dct_mk_closure ~recurse:recurse state name args =
  if recurse then begin
    let fd = Hashtbl.find_exn state.funcs name in
    (* No need to change closure variables, because they have the same inside and outside at this point *)
    (* Actually we do need to change the function arguments only *)
    let (pat_vars, _) = List.unzip fd.fd_pat.tpat_vars in
    let (clo_vars, _) = List.unzip fd.fd_cvars in
    let new_avail_vars = Hash_set.of_list (module TIdent) (pat_vars @ clo_vars) in
    let inner_state = {
      state with
      avail_vars = new_avail_vars;
    }
    in
    let (expr', _) = dct_expr inner_state fd.fd_expr in
    let fd' = {fd with fd_expr = expr'} in
    Hashtbl.set state.funcs ~key:name ~data:fd'
  end;
  (Texp_special(Tspec_mkclosure, name, args), Some(name))


and dct_apply_closure state fexpr args =
  let (fexpr', fname_opt) = dct_expr state fexpr in
  match fname_opt with
  | Some(fname) ->
      let _fd = Hashtbl.find_exn state.funcs fname in
      (Texp_apply(fexpr', args), None)
  | None -> (Texp_apply(fexpr', args), None)


and dct_value_bindings state rf tvb_list =
  let dct_vb_inner recurse =
    let (tvl, mapping_opts) = List.unzip (List.map tvb_list ~f:(fun tvb ->
      let (expr, func) = dct_expr ~recurse:recurse state tvb.tvb_expr in
      match func with
      | Some(fd) ->
          let (_, pat_id) = pat_id_or_exn tvb.tvb_pat in
          ({tvb with tvb_expr = expr}, Some(pat_id, fd))
      | None -> ({tvb with tvb_expr = expr}, None)
    ))
    in
    (* Function mappings can stay forever, as they map unique variables to function names *)
    let mappings = List.filter_opt mapping_opts in
    List.iter mappings ~f:(fun (id,fname) -> Hashtbl.set state.func_vars ~key:id ~data:fname);
    let pat_vars =
      List.map tvb_list ~f:(fun tvb -> let (vars, _) = List.unzip tvb.tvb_vars in vars)
      |> List.concat
    in
    (* Here we are tracking which vars are in scope, so we need to make sure we can remove them *)
    List.iter pat_vars ~f:(Hash_set.add state.avail_vars);
    let clear () =
      List.iter pat_vars ~f:(Hash_set.remove state.avail_vars)
    in (tvl, clear)
  in
  let (tvb_list', clear) =
    match rf with
    | Asttypes.Nonrecursive ->
        dct_vb_inner true
    | Asttypes.Recursive ->
        let (_, clear) = dct_vb_inner false in
        let tvl = List.map tvb_list ~f:(fun tvb ->
          let (expr, _) = dct_expr ~recurse:true state tvb.tvb_expr in
          {tvb with tvb_expr = expr}
        )
        in (tvl, clear)

  in (tvb_list', clear)

and dct_match state e cases =
  let (e', _) = dct_expr state e in
  let cases' = List.map cases ~f:(fun case ->
    let (pat_vars, _) = List.unzip case.tc_lhs.tpat_vars in
    List.iter pat_vars ~f:(Hash_set.add state.avail_vars);
    let (rhs', _) = dct_expr state case.tc_rhs in
    List.iter pat_vars ~f:(Hash_set.remove state.avail_vars);
    {case with tc_rhs = rhs'}
  )
  in
  Texp_match(e', cases')

let dct_structure_item state si =
  let desc =
    match si.tstr_desc with
    | Tstr_eval(e) ->
        let (e', _func) = dct_expr state e
        in Tstr_eval(e')
    | Tstr_value(rf, tvb_list) ->
        let (tvb_list', _clear) = dct_value_bindings state rf tvb_list
        in Tstr_value(rf, tvb_list')
    | Tstr_type -> (si.tstr_desc)
  in {si with tstr_desc = desc}


let dct_structure state struc =
  List.map struc ~f:(dct_structure_item state)

let direct_call_transform (funcs : Functions.func_data list) (toplevel : tstructure) =
  let func_map =
    funcs
    |> List.map ~f:(fun func -> (func.fd_name, func))
    |> Hashtbl.of_alist_exn (module String)
  in
  let state = {
    funcs = func_map;
    func_vars = Hashtbl.create (module Int);
    avail_vars = Hash_set.create (module TIdent);
  }
  in
  let toplevel' = dct_structure state toplevel in
  (Hashtbl.data state.funcs, toplevel')
