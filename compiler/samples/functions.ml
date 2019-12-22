let double n = 2 * n

let sum x y = x + y

let rec fib n = if n = 0 then 1 else fib (n - 1)

let add3 n =
  let add1 n = sum n 1 in
  add1 (add1 (add1 n))

let mult m n =
  let rec addm t a =
    if t = 0 then a
    else addm (t-1) (a + m) in
  addm n 0
