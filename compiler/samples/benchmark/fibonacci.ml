

type 'a llist =
  Seq of 'a * (unit -> 'a llist)


let rec fib_func prev cur =
  Seq(cur, fun () -> fib_func cur (prev + cur))

let fib_seq = Seq(0, fun () -> Seq(1, fun () -> fib_func 1 1))

let rec nth (Seq(item,next)) n =
  match n with
  | 0 -> item
  | _ -> nth (next()) (n - 1)


(* Should be 102334155 *)
let n40 = nth fib_seq 40


let loop1000 () =
  for i = 1 to 1000 do
    let _n50 = nth fib_seq 50 in ()
  done;
  true
