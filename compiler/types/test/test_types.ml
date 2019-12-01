open Core_kernel
open OUnit2

open Otwa_types
open Types
open Predefined

let param_test ~comp:comp test params  =
  List.map params ~f:(fun (title,arg1,res) ->
    title >:: (fun _test_ctx ->
      match res with
      | Some(x) ->
          assert_bool "Not equal" (comp x (test arg1))
      | None ->
          (try
            let _ = test arg1 in
            assert_bool "Expecting an exception" false
          with _ -> ())))

let param_test2 ~comp:comp test params  =
  List.map params ~f:(fun (title,arg1,arg2,res) ->
    title >:: (fun _test_ctx ->
      match res with
      | Some(x) ->
          assert_bool "Not equal" (comp x (test arg1 arg2))
      | None ->
          (try
            let _ = test arg1 arg2 in
            assert_bool "Expecting an exception" false
          with _ -> ())))

let suite =
  "suite">:::
    ["ftv">:::(
      param_test ~comp:Set.equal
        (* Function we are testing *)
        ftv
        (* test name, input, output *)
        [
          ("value", T_val(V_unit), Some(empty_tvar_set));
          ("tvar", T_var("a"), Some(Set.of_list (module String) ["a"]))
        ]);
     "unify">:::(
       param_test2 ~comp:(List.equal (fun (v1,t1) (v2,t2) -> (String.equal v1 v2) && equal_scheme_type t1 t2))
       unify
       [
         ("same values", v_unit, v_unit, Some([]));
         ("diff values", v_unit, v_unit, None);
         ("tvar with value", T_var("a"), v_int, Some([("a",v_int)]));
         ("func with tvar", T_var("c"), f_iib, Some([("c", f_iib)]));
         ("diff funcs", f_iii, f_iib, None);
         ("tvar left to right", T_var("a"), T_var("b"), Some([("a", T_var("b"))]));
         ("occurs check", T_var("a"), T_func(T_var("a"), v_int), None)
       ]);
    ]

let () =
  run_test_tt_main suite
