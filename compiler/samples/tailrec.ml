

let rec fact_tail n acc =
  if n = 1 then
    acc
  else
    fact_tail (n - 1) (n * acc)


let v5040 = fact_tail 7 1


let rec float_fact_tail n acc =
  if n <= 1.1 then
    acc
  else
    float_fact_tail (n -. 1.0) (n *. acc)

let vf362880 = float_fact_tail 9.0 1.0
