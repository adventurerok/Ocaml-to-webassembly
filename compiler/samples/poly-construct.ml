
(* Let's make sure that we can still pattern match ints and floats *)

type basic =
  | Int of int
  | Float of float

let test1 =
  match Int(4) with
  | Float(_) -> false
  | Int(4) -> true
  | Int(_) -> true

let test2 =
  match Float(2.1) with
  | Int(_) -> false
  | Float(2.1) -> true
  | Float(_) -> false

type 'a box =
  | Null
  | Here of 'a

let mynull = Null

let int_here = Here(4)

let float_here = Here(4.1)

let test3 =
  match float_here with
  | Null -> false
  | Here(4.1) -> true
  | Here(_) -> false

let here_be_tuple (Here(x)) = Here((x,x))

let test4 =
  match (here_be_tuple int_here) with
  | Null -> false
  | Here((0,0)) -> false
  | Here((4,4)) -> true
  | _ -> false

let test5 =
  match (here_be_tuple float_here) with
  | Null -> false
  | Here((4.1,4.1)) -> true
  | _ -> false

let map_here map (Here(x)) = (Here(map x))

let double_f x = x *. 2.0

let v_8_2 =
  match (map_here double_f (Here(4.1))) with
  | Null -> 0.0
  | Here(x) -> x
