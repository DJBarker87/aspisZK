# 5. `sparse_eq_weights`

File: `crates/aspis-statement/src/constraints_v4.rs`. This module has no `cfg`
gate, so it is compiled into every program that uses `aspis-statement`. Whether
any program keeps the function is answered by gate A (an unchanged ELF), not by
this note.

Old shape. Inside the loop over prefixes, `for (coordinate, value) in
point[..prefix_len].iter().enumerate()` with the body `weight = weight.mul(if bit
== 0 { QM31::ONE.sub(*value) } else { *value })`.

New shape. The function still counts the trailing Boolean coordinates with the
same iterator chain and builds the suffix with the same loop; it then returns
`sparse_eq_weight_rows(point, prefix_len, trailing_boolean, suffix)`. That new
private function is the former outer loop as a counted `while` loop over `prefix`
from 0 to `(1 << prefix_len) - 1`: same row formula, weight from
`sparse_eq_prefix_weight(point, prefix, prefix_len)`, same push. The second new
function is the former inner loop as a counted loop over `coordinate` from 0 to
`prefix_len - 1`, whose body is `weight = sparse_eq_weight_step(weight, prefix,
prefix_len, coordinate, point[coordinate])`; the step function computes the same
`bit` and returns the same `weight.mul(..)` expression. So there are three small
functions, none with a nested loop and none with a branch inside a loop.

How it got there. Two earlier forms did not translate: the inner loop written as
a counted loop in place ("Could not match the contexts" at that loop), and the
inner loop as a function with the outer `for` loop left in place (the same
message at the outer loop). The form above translates.

Why the behaviour is the same. `point[..prefix_len]` has `prefix_len` elements,
element `coordinate` of it is `point[coordinate]`, and `prefix_len` is at most 10,
the length of `point`, so the indices are in range. The coordinates are visited in
the same order and each multiplies the running weight by the same factor, chosen
by the same bit of the same prefix. The shift amount `prefix_len - 1 - coordinate`
is the same expression evaluated for the same values (`coordinate < prefix_len`),
so it cannot underflow in either form. The bound of the outer loop, `1 <<
prefix_len`, was evaluated once by the pin's range and is evaluated once into
`count` here. The output vector has the same capacity request and receives the
same pairs in the same order.

Test added: `pv_aspis_rw_sparse_eq_weights_matches_pin_body` (every count of
trailing Boolean coordinates from 0 to 10, every zero/one pattern of a short tail,
Boolean values inside the prefix, generated and edge field values).
