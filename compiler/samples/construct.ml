
type thing =
| Item
| Spinner of int
| Numbers of int * int * int
| Box of thing
| Float of float

let my_item = Item

let my_spinner = Spinner(3)

let my_numbers = Numbers(8, 9, 10)

let my_box = Box(my_numbers)

let my_float = Float(7.1)

let x =
  match my_item with
  | Item -> 12
  | _ -> 1

let y =
  match my_spinner with
  | Item -> 77777
  | Spinner(num) -> num
  | _ -> 1

let z =
  match my_numbers with
  | Spinner(num) -> num
  | Item -> 77777
  | Numbers(n1, n2, n3) -> n1 + n2 + n3
  | _ -> 1

let w =
  match my_box with
  | Box(Item) -> 777
  | Box(Spinner(_)) -> 888
  | Box(Numbers(n1, n2, n3)) -> n1 * n2 * n3
  | _ -> 1

let v =
  match my_float with
  | Item -> -1.1
  | Box(_) -> -1.2
  | Float(n1) -> n1
  | _ -> -1.9
