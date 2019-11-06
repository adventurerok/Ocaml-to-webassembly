open OUnit2


let test_basic _ =

  assert_equal 0 (List.length [])

let suite =
  "ExampleTestList" >::: [
    "test_basic" >:: test_basic
  ]

let () = run_test_tt_main suite
