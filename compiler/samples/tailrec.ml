

let rec fact_tail n acc =
  if n = 1 then
    acc
  else
    fact_tail (n - 1) (n * acc)
