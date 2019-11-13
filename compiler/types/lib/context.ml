open Base
open Types

type context = (string * scheme_type) list

let empty : context = []

let extend (ctx : context) vr typ = (vr, typ) :: ctx

let rec search (ctx : context) name =
  match ctx with
  | [] -> None
  | ((vr, typ) :: ctx') -> if (String.equal vr name) then Some(typ) else (search ctx' name)
