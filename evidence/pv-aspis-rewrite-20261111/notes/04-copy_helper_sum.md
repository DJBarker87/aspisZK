# 4. `state_only_copy_helper_sum`

File: `crates/aspis-statement/src/state_only_semantic.rs` (module is
`#[cfg(not(target_os = "solana"))]`).

Old shape. `(h1.len() == TRACE_ROWS).then(|| h1.iter().copied().fold(QM31::ZERO,
QM31::add))`: a closure given to `bool::then`, which folds with the function item
`QM31::add`.

New shape. `if h1.len() != TRACE_ROWS { return None; }`, then a counted loop
`sum = sum.add(h1[row])` for `row` from 0 to `TRACE_ROWS - 1`, then `Some(sum)`.

Why the behaviour is the same. `bool::then` returns `None` without calling the
closure when the lengths differ, and `Some` of the closure's value otherwise.
`fold` starts from `QM31::ZERO` and applies `acc.add(value)` to the elements in
index order, which is what the loop does. The length test guarantees every index
is in range. There is no error path and no allocation in either form.

Test added: `pv_aspis_rw_copy_helper_sum_matches_pin_body` (zeros, ones, `P - 1`
in every limb, a single non-zero row at four positions, 200 generated tables, and
five wrong lengths).
