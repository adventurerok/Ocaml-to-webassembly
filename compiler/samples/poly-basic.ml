(* Identitify function *)
let id x = x

(* Test id *)
let v_3 = id 3
let v_true = id true
let v_4_5 = id 4.5

(* Application function *)
let app f x = f x

(* A non-polymorphic function to test it on *)
let double n = 2 * n

(* Test app *)
let v_10 = app double 5
let v_2 = app id 2
let v_8_1 = app id 8.1
