(* Intended to test the entire core subset *)

(* Values: int, bool and float, defined using let and let in *)

let v_a = 10

let v_b = true

let v_c = 11.4

let v_d =
  let x = 2 in
  let y = 10 in
  x + y

let v_e =
  let x = 10.25 in
  let y = 2.0 in
  x *. y

(* Functions: let and let rec with multiple curried arguments,
 * with an expression for the function body, and inline functions with fun *)
(* if then else *)

let a_plus_b_times_c a b c =
  (a + b) * c

let v_twenty = a_plus_b_times_c 2 3 4

let rec fact_plus a b =
  if a = 0 then
    1 + b
  else
    (a + b) * (fact_plus (a - 1) b)

let v_720 = fact_plus 6 0

let add4 x = x + 4

let then_add x next y =
  (next (x + 0)) + y

let v_34 = then_add 10 add4 20

let v_50 = (then_add 2 (a_plus_b_times_c 5 0) 2) + 38

let inline_func = fun x -> 8 * x

let v_16 = inline_func 2

(* Types: Non-polymorphic defined using type, and tuples *)
(* (not-so-)basic pattern matching *)

type tree =
  | Leaf
  | Branch of int * tree * tree

let v_leaf = Leaf

let v_branch = Branch(108, v_leaf, v_leaf)

let v_108 =
  match v_branch with
  | Leaf -> -1
  | Branch(num, _, _) -> num

let v_tup = (3, 7.2, 9, 11.1, true)

let v_12 =
  match v_tup with
  | (4, _, 9, _, true) -> -1
  | (i1, _, i2, _, false) -> -2 - i1 - i2
  | (i1, _, 9, _, true) -> i1 + 9
  | _ -> -100

