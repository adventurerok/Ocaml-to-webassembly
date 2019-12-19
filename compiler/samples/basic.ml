let double n = 2 * n

let sum x y = x + y

let q = sum 2 3

type tree =
  | Leaf
  | Branch of int * tree * tree

let mytree = Branch(4, Branch(2, Leaf, Leaf), Leaf)
