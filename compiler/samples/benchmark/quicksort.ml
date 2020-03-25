
(* Could this append be improved with a native one? *)
let rec append xs ys =
  match xs with
  | [] -> ys
  | x :: xs' -> x :: (append xs' ys)


let rec partition piv unsorted sm bg =
  match unsorted with
  | [] -> sm, bg
  | x :: xs ->
      if x <= piv then
        partition piv xs (x :: sm) bg
      else
        partition piv xs sm (x :: bg)

let rec quicksort xs =
  match xs with
  | [] -> []
  | x :: xs' ->
      let sm, bg = partition x xs' [] [] in
      append (quicksort sm) (x :: (quicksort bg))


(* Doesn't have to be perfect, just give non sorted numbers *)
let lcg seed =
  ((8121 * seed) + 28411) mod 134456

let rec random_list seed len acc =
  if len = 0 then
    seed, acc
  else
    let seed' = lcg seed in
    random_list seed' (len - 1) (seed' :: acc)


let rec check_sorted min lst =
  match lst with
  | [] -> true
  | (x :: xs) ->
      if x < min then
        false
      else
        check_sorted x xs

let _, test_list = random_list 101 20 []
let v_true = check_sorted 0 (quicksort test_list)

let sort_n seed n =
  let _, lst = random_list seed n [] in
  let sorted = quicksort lst in
  check_sorted 0 sorted

let sort_1000 () =
  sort_n 34217 1000

let sort_100 () =
  sort_n 67231 100

let sort_10000 () =
  sort_n 31415 10000
