(* List append *)
(*
let rec append xs ys =
  match xs with
  | [] -> ys
  | x :: xs' -> x :: (append xs' ys) *)

(* Lazy list *)
type 'a llist =
  Seq of 'a * (unit -> 'a llist)


let rec nth (Seq(item,next)) n =
  match n with
  | 0 -> item
  | _ -> nth (next()) (n - 1)

let rec filter test (Seq(item,next)) =
  if test item then
    (Seq(item, fun () -> filter test (next())))
  else
    filter test (next())

let rec from n =
  Seq(n, fun () -> from (n + 1))

(* Quite a slow recursive sequence algorithm *)
let rec is_prime n =
  let rec test_div (Seq(item,next)) =
    if n mod item = 0 then
      false
    else if item * 2 > n then
      true
    else
      test_div (next())
  in test_div (gen_primes())
and gen_primes () =
  Seq(2, fun () -> filter is_prime (from 3))

let primes = gen_primes();;

let v31 = nth primes 10;;

let slow_benchmark () =
  let v547 = nth primes 100 in
  v547 = 547
