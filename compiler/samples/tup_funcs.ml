

let add (x,y) = x + y

(* Mostly for studying how this compiles *)
(* At the time this was written, x and y would be
 * stored in the closure separately.
 * I will investigate storing the tuple in the closure
 * instead *)
let add_mult (x,y) (z,w) = (x + y) * (z + w)

let add_mult_triple (a,b) (c,d) (e,f) = (a + b) * (c + d) * (e + f)


let test =
  let a = 11 in
  let ff x =
    let q = a in
    q + x
  in ff

let v5 = add (2,3)

let v40 = add_mult (2,3) (7,1)

let mult5_add = add_mult (4,1)

let v100 = mult5_add (18, 2)
