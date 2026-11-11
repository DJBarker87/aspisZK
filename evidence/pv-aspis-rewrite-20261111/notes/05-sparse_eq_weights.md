# 5. `sparse_eq_weights`

File: `crates/aspis-statement/src/constraints_v4.rs`. This module has no `cfg`
gate, so it is compiled into every program that uses `aspis-statement`. Whether
any program keeps the function is answered by gate A (an unchanged ELF), not by
this note.

Old shape. Inside the loop over prefixes, `for (coordinate, value) in
point[..prefix_len].iter().enumerate()` with the body `weight = weight.mul(if bit
== 0 { QM31::ONE.sub(*value) } else { *value })`.

New shape. A counted loop `coordinate` from 0 to `prefix_len - 1` whose body is
`weight = sparse_eq_weight_step(weight, prefix, prefix_len, coordinate,
point[coordinate])`; the step function computes the same `bit` and returns the
same `weight.mul(..)` expression. The count of trailing Boolean coordinates, the
suffix loop, the outer loop, the row formula and the pushes are unchanged.

Why the behaviour is the same. `point[..prefix_len]` has `prefix_len` elements,
element `coordinate` of it is `point[coordinate]`, and `prefix_len` is at most 10,
the length of `point`, so the indices are in range. The coordinates are visited in
the same order and each multiplies the running weight by the same factor, chosen
by the same bit of the same prefix. The shift amount `prefix_len - 1 - coordinate`
is the same expression evaluated for the same values (`coordinate < prefix_len`),
so it cannot underflow in either form. The output vector has the same capacity
request and receives the same pairs in the same order.

Test added: `pv_aspis_rw_sparse_eq_weights_matches_pin_body` (every count of
trailing Boolean coordinates from 0 to 10, every zero/one pattern of a short tail,
Boolean values inside the prefix, generated and edge field values).
