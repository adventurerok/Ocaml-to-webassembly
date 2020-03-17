
let rec append xs ys =
  match xs with
  | [] -> ys
  | lh :: lt -> lh :: (append lt ys)

(* WHYY is this broken and WHYY DID I NEVER TEST THIS BEFORE? *)
