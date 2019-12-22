
type thing =
  | Item
  | Count of int
  | Box of thing
  | Possibility of bool

let thingid th =
  match th with
  | Item -> 0
  | Count _ -> 1
  | Box _ -> 2
  | Possibility _ -> 3

let countcompare th =
  match th with
  | Count(0) -> 0
  | Count(10) -> 1
  | Count(32) -> 2

let boxcompare th =
  match th with
  | Box(Item) -> 0
  | Box(Count(2)) -> 1
  | Box(Box(Item)) -> 2

let tupcompare tup =
  match tup with
  | (0, Item) -> 0
  | (x, Box(Item)) -> x
  | (32, y) -> 2
  | (_, Count(n)) -> n
