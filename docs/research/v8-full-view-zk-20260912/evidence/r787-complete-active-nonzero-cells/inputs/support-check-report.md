# R787 selected active-block support preflight

This is a metadata/index comparison only. It performs no field arithmetic, elimination, proof, or claim that the saved matrix is the evaluation of the Lean source matrix.

Inputs and pins:

- Saved R769 raw matrix: SHA-256 `91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af`.
- R769 raw selected-column map: SHA-256 `8b8506e8c85975f798d566d07ceeaff586b5eb12ad76aeaa58c554dc9902fa04`.
- R778 row-code/shape summary: SHA-256 `182915860a04793e56a50cf9b8352c411840877015ff46cc480a4801b00ffeb2`.
- `AspisV8R17.IndexSchedule.indexLoop`: SHA-256 `363b0eb4491d3cb40ad5d097e5e7f0242677f43808a1839bafe80add2356cfcf`.
- `AspisV8R17.WeightedScatter` support definitions: SHA-256 `5a33cf1c7f5fa122bf3f2bc94ac6c2d4f51a25446f565faf8e3d6e20da413e0c`.
- Existing generic zero consumer `R787PairSupportZero.lean`: SHA-256 `b17902d251355267290c8bb5fb7e6cff7a01d2e3a1f6844a41a7881290ba7b37`.
- Existing schedule inventory `R761_FINITE_GATHER_SCHEDULES.md`: SHA-256 `42e40530f3a1e8bc90fb51993073ca93b6fba8ca65dce607c92ac7f7e5339923`.

The checker is `compute.py` (SHA-256 `ee66b56b6f88ce805a44fb9879aabe51c82ad9281f355b8570c20039904dfab3`). Its full checkable output, including every support-positive coordinate, is `support-check.json` (SHA-256 `4ddaff34fc112bc64cb5484b81c7af7e96f10301326ce3a686b39ca4f641b592`). The checker reproduces the pinned `indexLoop` recursion at fuel 10 and computes `indexTargets`, `evenUnitSupport`, `oddUnitSupport`, and R787's `pairSupport` directly as integer/list predicates. It uses raw TSV column headers `(d, raw_slot)`, with `s=raw_slot-1`, and the active source row codes from the R778 summary.

For the 214×222 block, all 700 support-positive positions are exactly the 700 literal nonzero TSV cells. There are zero support-positive literal zeros (no observed cancellation), zero literal nonzeros outside support, and 46,808 literal zeros outside support. This is strong agreement between the schedule support and saved table sparsity, but remains a diagnostic comparison.

A bounded first theorem candidate is the row with source code 114: its support-positive selected-column positions are exactly `[0, 220]`. A source-formula-only mask theorem could introduce a finite `dOfSelectedPosition` / `sOfSelectedPosition` table from the 222 TSV headers, prove for every other position `¬ R787PairSupportZero.pairSupport d s 114` by finite index computation, then apply `R787PairSupportZero.direction_sourceChord_zero_of_not_pairSupport` (the row code satisfies `96 ≤ 114`). Keep positions 0 and 220 as the explicit allowed support. Existing R786's isolated row-114 zero is a reusable cell-level precedent, not this complete row mask.

The crucial unresolved boundary is unchanged: these table-header `(d,s)` values and source row codes have not been formally bound, for every cell, to `R746SelectedJointMinor.selectedColumns` and the `J`/row-code indexing of `chosenSourceMatrix`. Thus this preflight does not prove any raw matrix cell equals its Lean source-chord value. The row mask should be compiled as a small next source-formula target only after the lead chooses/validates the finite header mapping; no full 46,808-cell proof is started here.
