let double n = 2 * n

let sum x y = x + y

let rec fact n = if n = 0 then 1 else n * (fact (n - 1))

let add3 n =
  let add1 n = sum n 1 in
  add1 (add1 (add1 n))

let mult m n =
  let rec addm t a =
    if t = 0 then a
    else addm (t-1) (a + m) in
  addm n 0


let v12 = sum 10 2

let v20 = (sum 8) v12

let v7 = add3 4

let v50 = mult 10 5

let v720 = fact 6
