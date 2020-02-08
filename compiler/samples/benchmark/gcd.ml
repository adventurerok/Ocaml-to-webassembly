

let rec gcd a b =
  match (a, b) with
  | (0, y) -> y
  | (x, 0) -> x
  | _ ->
      if a > b then
        gcd (a - b) b
      else
        gcd (b - a) a

let rv_3 = gcd 15 27

let imp_gcd a b =
  let xr = ref a in
  let yr = ref b in
  while (!xr != 0) && (!yr != 0) do
    if (!xr) > (!yr) then
      xr := !xr - !yr
    else
      yr := !yr - !xr
  done;
  if (!xr) = 0 then
    !yr
  else
    !xr

let iv_3 = imp_gcd 15 27

let benchmark () =
  let one = gcd 83643 27 in
  one = 1

let loop_benchmark () =
  for i = 1 to 1000 do
    let _ = benchmark () in
    ()
  done;
  true

let imp_benchmark () =
  let one = imp_gcd 83643 27 in
  one = 1
