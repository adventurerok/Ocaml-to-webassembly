# Disable exit on non 0
set +e

echo "Full benchmarks"
node testing/end2end.js samples/benchmark/ -benchmult 10 -benchstat 50 -only gcd
node testing/end2end.js samples/benchmark/ -benchmult 2 -benchstat 50 -only primes
node testing/end2end.js samples/benchmark/ -benchmult 5 -benchstat 50 -only fibonacci
node testing/end2end.js samples/benchmark/ -benchmult 5 -benchstat 50 -only quicksort

echo "OTWA no-ref-elim"
node testing/end2end.js samples/benchmark/ -benchmult 10 -benchstat 50 -otwaonly -only gcd -no_ref_elimination
node testing/end2end.js samples/benchmark/ -benchmult 2 -benchstat 50 -otwaonly -only primes -no_ref_elimination
node testing/end2end.js samples/benchmark/ -benchmult 5 -benchstat 50 -otwaonly -only fibonacci -no_ref_elimination
node testing/end2end.js samples/benchmark/ -benchmult 5 -benchstat 50 -otwaonly -only quicksort -no_ref_elimination

echo "OTWA no-tail_calls"
node testing/end2end.js samples/benchmark/ -benchmult 10 -benchstat 50 -otwaonly -only gcd -no_tail_calls -no_ref_elimination
node testing/end2end.js samples/benchmark/ -benchmult 2 -benchstat 50 -otwaonly -only primes -no_tail_calls -no_ref_elimination
node testing/end2end.js samples/benchmark/ -benchmult 5 -benchstat 50 -otwaonly -only fibonacci -no_tail_calls -no_ref_elimination
node testing/end2end.js samples/benchmark/ -benchmult 5 -benchstat 50 -otwaonly -only quicksort -no_tail_calls -no_ref_elimination

echo "otwa no ref/tail/dead code"
node testing/end2end.js samples/benchmark/ -benchmult 10 -benchstat 50 -otwaonly -only gcd -no_ref_elimination -no_tail_calls -no_dead_code
node testing/end2end.js samples/benchmark/ -benchmult 2 -benchstat 50 -otwaonly -only primes -no_ref_elimination -no_tail_calls -no_dead_code
node testing/end2end.js samples/benchmark/ -benchmult 5 -benchstat 50 -otwaonly -only fibonacci -no_ref_elimination -no_tail_calls -no_dead_code
node testing/end2end.js samples/benchmark/ -benchmult 5 -benchstat 50 -otwaonly -only quicksort -no_ref_elimination -no_tail_calls -no_dead_code

echo "otwa no ref/tail/dead/tuple loads"
node testing/end2end.js samples/benchmark/ -benchmult 10 -benchstat 50 -otwaonly -only gcd -no_ref_elimination -no_tail_calls -no_dead_code -no_tuple_loads
node testing/end2end.js samples/benchmark/ -benchmult 2 -benchstat 50 -otwaonly -only primes -no_ref_elimination -no_tail_calls -no_dead_code -no_tuple_loads
node testing/end2end.js samples/benchmark/ -benchmult 5 -benchstat 50 -otwaonly -only fibonacci -no_ref_elimination -no_tail_calls -no_dead_code -no_tuple_loads
node testing/end2end.js samples/benchmark/ -benchmult 5 -benchstat 50 -otwaonly -only quicksort -no_ref_elimination -no_tail_calls -no_dead_code -no_tuple_loads

echo "otwa no ref/tail/dead/tuple/alias/direct"
node testing/end2end.js samples/benchmark/ -benchmult 4 -benchstat 50 -otwaonly -only gcd -no_ref_elimination -no_tail_calls -no_dead_code -no_tuple_loads -no_alias_elimination -no_direct_calls
node testing/end2end.js samples/benchmark/ -benchmult 1 -benchstat 50 -otwaonly -only primes -no_ref_elimination -no_tail_calls -no_dead_code -no_tuple_loads -no_alias_elimination -no_direct_calls
node testing/end2end.js samples/benchmark/ -benchmult 2 -benchstat 50 -otwaonly -only fibonacci -no_ref_elimination -no_tail_calls -no_dead_code -no_tuple_loads -no_alias_elimination -no_direct_calls
node testing/end2end.js samples/benchmark/ -benchmult 2 -benchstat 50 -otwaonly -only quicksort -no_ref_elimination -no_tail_calls -no_dead_code -no_tuple_loads -no_alias_elimination -no_direct_calls

echo "otwa no alias elimination"
node testing/end2end.js samples/benchmark/ -benchmult 10 -benchstat 50 -otwaonly -only gcd -no_tail_calls -no_ref_elimination -no_alias_elimination
node testing/end2end.js samples/benchmark/ -benchmult 2 -benchstat 50 -otwaonly -only primes -no_tail_calls -no_ref_elimination -no_alias_elimination
node testing/end2end.js samples/benchmark/ -benchmult 5 -benchstat 50 -otwaonly -only fibonacci -no_tail_calls -no_ref_elimination -no_alias_elimination
node testing/end2end.js samples/benchmark/ -benchmult 5 -benchstat 50 -otwaonly -only quicksort -no_tail_calls -no_ref_elimination -no_alias_elimination

echo "otwa no ref/tail/dead/tuple/alias/direct/scg"
node testing/end2end.js samples/benchmark/ -benchmult 2 -benchstat 50 -otwaonly -only gcd -no_ref_elimination -no_tail_calls -no_dead_code -no_tuple_loads -no_alias_elimination -no_direct_calls -no_stack_codegen
node testing/end2end.js samples/benchmark/ -benchmult 1 -benchstat 50 -otwaonly -only primes -no_ref_elimination -no_tail_calls -no_dead_code -no_tuple_loads -no_alias_elimination -no_direct_calls -no_stack_codegen
node testing/end2end.js samples/benchmark/ -benchmult 1 -benchstat 50 -otwaonly -only fibonacci -no_ref_elimination -no_tail_calls -no_dead_code -no_tuple_loads -no_alias_elimination -no_direct_calls -no_stack_codegen
node testing/end2end.js samples/benchmark/ -benchmult 1 -benchstat 50 -otwaonly -only quicksort -no_ref_elimination -no_tail_calls -no_dead_code -no_tuple_loads -no_alias_elimination -no_direct_calls -no_stack_codegen

echo "All benchmarks have finished!!!!"
echo "Yay, we are done!!!!"
