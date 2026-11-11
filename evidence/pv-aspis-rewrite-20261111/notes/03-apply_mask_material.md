# 3. `apply_mask_material_for_layout` and its callee `balance_m31_copy_inactive`

File: `crates/aspis-prover/src/state_only_hiding.rs` (crate `aspis-prover`, which
no program depends on).

## `apply_mask_material_for_layout`

Old shape. After the shape checks and the search for one inactive row per column
(both unchanged), two loops: `for (cell, mask) in cells.iter().copied().zip(
core::mem::take(&mut material.c1))`, adding each mask to its trace cell through a
mutable reference; then `for (column, dependent) in trace.c1.iter_mut().zip(
inactive_dependents)`, calling `balance_m31_copy_inactive(column,
dependent.unwrap(), active)?`.

New shape. The mask vector is taken out of `material` by the same
`core::mem::take` into a local inside a block; a counted loop over
`index < cells.len()` does `trace.c1[column][row] = trace.c1[column][row].add(
masks[index])` with `column` and `row` read from `cells[index]`; the block ends,
releasing the vector. A second counted loop over `column <
STATE_ONLY_HIDING_C1_COLUMNS` calls `balance_m31_copy_inactive(&mut
trace.c1[column], inactive_dependents[column].unwrap(), active)?`. No iterator
adaptor and no borrow is alive from one iteration to the next, so every path
reaches the head of each loop with the same borrows.

Why the behaviour is the same.
* Number of steps of the first loop. The earlier check returns `TraceShape` unless
  `material.c1.len() == cells.len()`, so the zip had exactly `cells.len()` items
  and `masks[index]` is always in range.
* Order and values. Cell `index` is paired with mask `index` in both forms. The
  pin indexed the column and then the row; the new form indexes the column and
  then the row to read, and again to write, so a cell outside the trace panics at
  the same cell with the same kind of panic, before any later cell is touched.
  The value written is `old.add(mask)` in both forms.
* The taken mask vector. In the pin it was moved into the loop's iterator and
  freed, without being cleared, when the loop ended. In the new form it is a
  local of a block that ends when the loop ends, so it is freed at the same place,
  also without being cleared. `material.c1` is left empty in both forms, so the
  `Drop` of `material` clears the same (empty) vector and the same other fields.
* Number of steps of the second loop. `trace.c1` is an array of
  `STATE_ONLY_C1_COLUMNS` vectors and `inactive_dependents` an array of
  `STATE_ONLY_HIDING_C1_COLUMNS` options; both constants are 16, and a `const`
  assertion next to the function now fails the build if they ever differ. So the
  zip had exactly that many items.
* Errors. The `?` is in the same place: the first column whose balancing fails
  returns its error, with the columns before it already balanced, as before. The
  `unwrap` cannot fail in either form because the function has already returned
  `Layout` if any entry is `None`.
* The returned value is built by the same four expressions.

## `balance_m31_copy_inactive`

Old shape. After the same length and activity check, `(0..ROWS).filter(|row|
!active[*row] && *row != dependent).fold(M31::ZERO, |sum, row|
sum.add(table[row]))`, then `table[dependent] = M31::ZERO.sub(sum)`.

New shape. The sum is `inactive_m31_sum_except(table, active, dependent)`: a
counted loop over the rows in increasing order whose body calls a step function;
the step function returns `sum.add(table[row])` when the row is inactive and is
not the dependent row, and `sum` otherwise. The write of the dependent row is
unchanged.

Why the behaviour is the same. The rows are visited in the same order, the same
rows contribute, and each contributes by the same `add` on the same running sum,
so the sum is the same field element (the order matters only in that the pin's
order is kept). `table` has exactly `ROWS` entries at that point and `active` is
an array of `ROWS` entries, so no index can fail in either form. The check before
the sum, with its possible panic on `active[dependent]` for a dependent row
outside the array, is the same expression.

## Tests

The existing test `pv_rw_a_mask_material_build_and_apply_match_pin_bodies`
compares `apply_mask_material_for_layout` with the pin body (which now calls the
pin body of the balancing function, so the oracle does not share the rewritten
code) on five layouts, random traces and material, and a shape error. Added:
`pv_aspis_rw_balance_m31_matches_pin_body`, the balancing function against its
pin body on the five layouts' active rows, random and all-inactive row sets,
random tables with field edge values, every kind of dependent row, and wrong
lengths.

## Other evidence touched

`balance_m31_copy_inactive` is the subject of the Kani harness
`prover_commit_balance7::balance_m31_caller` in the same file. The harness text is
unchanged and was not run in this job; its earlier result was obtained on the pin
body and does not carry over to the new body until it is run again.
