
let tup_map (f,g) (x,y) = (f x, g y)

let int_double x = 2 * x

let float_double x = 2.0 *. x

let int_tup = tup_map (int_double, int_double) (2,3)

let float_tup = tup_map (float_double, float_double) (1.5, 3.5)

let mixed_tup = tup_map (float_double, int_double) (1.5, 3)

let id x = x

let mixed_tup2 = tup_map (id float_double, id) (10.5, true)
