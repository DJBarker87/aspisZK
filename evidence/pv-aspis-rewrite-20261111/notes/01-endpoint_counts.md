# 1. `endpoint_counts` (two copies)

Files: `crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs` and
`crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs` (both modules are
`#[cfg(not(target_os = "solana"))]`). The two functions have the same text.

Old shape. For every link, the function built an array of two pairs,
`(producer row, &mut producers)` and `(consumer row, &mut consumers)`, and ran one
inner loop over that array: test the row, return the error or add one to the count.

New shape. The outer loop over the links is unchanged. The inner loop is written
out as its two iterations, producer first and consumer second, each with the same
test, the same error value and the same `+= 1`. No reference is stored in a value.

Why the behaviour is the same. The pin's array had exactly two elements in that
order, so its inner loop ran exactly those two steps. The two row numbers are
computed by `usize::from` of a `u16`, which has no effect and cannot fail, so it
does not matter that the pin computed both before the first test. The test
`row >= POOL_V1_PAIR_TRACE_ROWS || counts[row] >= 2` is the same expression with
the same short-circuit, so the array is indexed only when the row is inside the
trace (the arrays have 1024 entries and the bound is 1024). The count is a `u8`
that is incremented only when it is below 2, with the same `+=` operator. The
first failing endpoint in link order, producer before consumer, returns the same
`EndpointCapacity { row }`; on success the two arrays are returned by value as
before.

Test added: `pv_aspis_rw_endpoint_counts_matches_pin_body` in each file compares
the function with the pin body (kept under `#[cfg(test)]` as `endpoint_counts_pin`)
on the real schedule, all its prefixes and 20,000 generated link lists that reach
success and both error causes.
