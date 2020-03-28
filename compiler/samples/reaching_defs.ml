

let myfunc x y z =
  let a = x + y in
  let b = y + z in
  let c = a + b in
  let d = 4 in
  let e = b + d in
  let q =
    if d = 4 then
      b
    else
      a
  in
  q
