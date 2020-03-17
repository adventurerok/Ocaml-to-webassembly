type t = {
  mutable debug: bool;
  mutable trace: bool; (* More fine grained debug *)
  mutable optimise_stack_codegen: bool;
  mutable optimise_direct_call_gen: bool;
  mutable optimise_alias_elimination: bool;
}


let global = {
  debug = false;
  trace = false;
  optimise_stack_codegen = true;
  optimise_direct_call_gen = true;
  optimise_alias_elimination = true;
}
