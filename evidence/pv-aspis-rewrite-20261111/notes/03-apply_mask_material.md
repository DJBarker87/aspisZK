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

New shape. The function body has no loop. The shape checks and the two
`iter().any(..)` tests are unchanged. The three loops are three private functions,
each one counted `while` loop:
* `inactive_dependent_rows(cells, active)` returns the array of per-column
  dependent rows; its step function reads the cell's row and column, tests
  `active[row]` and writes `Some(row)` for an inactive row (the pin's `for cell in
  cells` loop, which was already in the pin and is now moved, not altered);
* `add_cell_masks(trace, cells, masks)` takes the mask vector by value (the caller
  passes `core::mem::take(&mut material.c1)`, as the pin passed it to `zip`) and
  for `index` from 0 to `cells.len() - 1` calls `add_cell_mask(trace, cells[index],
  masks[index])`, which does `trace.c1[column][row] = trace.c1[column][row].add(
  mask)`; the vector is released when the function returns;
* `balance_trace_columns(trace, &inactive_dependents, active)` calls
  `balance_m31_copy_inactive(&mut trace.c1[column], dependents[column].unwrap(),
  active)?` for `column` from 0 to `STATE_ONLY_HIDING_C1_COLUMNS - 1` and returns
  `Ok(())`; the caller applies `?` to it.

How it got there. Three earlier forms did not translate: the two later loops as
counted loops in place ("Unimplemented" at the first of them); the same with the
cell update in a helper ("Could not match the contexts" at that loop); and those
two loops as functions with the pin's first loop left in place (the same message
at that loop). With no loop left in the function that holds the iterator tests,
it translates.

Why the behaviour is the same.
* Number of steps of the first loop. The earlier check returns `TraceShape` unless
  `material.c1.len() == cells.len()`, so the zip had exactly `cells.len()` items
  and `masks[index]` is always in range.
* Order and values. Cell `index` is paired with mask `index` in both forms. The
  pin indexed the column and then the row; the new form indexes the column and
  then the row to read, and again to write, so a cell outside the trace panics at
  the same cell with the same kind of panic, before any later cell is touched.
  The value written is `old.add(mask)` in both forms.
* The dependent rows. The cells are visited in the same order, and for each the
  same reads and the same conditional write happen in the same order, so the
  array is the same and a cell outside the trace or the column range panics at
  the same cell.
* The taken mask vector. In the pin it was moved into the loop's iterator and
  freed, without being cleared, when the loop ended. In the new form it is an
  argument of `add_cell_masks`, which returns when the loop ends, so it is freed
  at the same place, also without being cleared. `material.c1` is left empty in both forms, so the
  `Drop` of `material` clears the same (empty) vector and the same other fields.
* Number of steps of the second loop. `trace.c1` is an array of
  `STATE_ONLY_C1_COLUMNS` vectors and `inactive_dependents` an array of
  `STATE_ONLY_HIDING_C1_COLUMNS` options; both constants are 16, and a `const`
  assertion next to the function now fails the build if they ever differ. So the
  zip had exactly that many items.
* Errors. The first column whose balancing fails returns its error out of
  `balance_trace_columns` and, through the caller's `?`, out of the function,
  with the columns before it already balanced, as before. The
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
unchanged and was not run in this job.

Correction, 12 November: the only earlier run of this harness (receipt
`balance-m31-focused-v1` under
`docs/research/100bit-spend-path-20261013/evidence/prover-commit7-20261021/receipts/`)
ended at its 600 second limit with no verdict, so there was no earlier result to
carry over. It was run again on 94e06159f32 with the same command and limits and
again reached the limit with no verdict (record in
`evidence/pv-prefreeze2-20261112/` on branch `codex/pv-prefreeze-20261111`).
There is no Kani verdict for this harness on either body. The evidence for the
new body is the differential test `pv_aspis_rw_balance_m31_matches_pin_body`.
