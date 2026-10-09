# R645 TwoSwap high directions — scratch evidence

Final focused target: `AspisV8R19/R645TwoSwapHighDirections.lean`.

Final success: `1791110939556601000`, exit 0, wall 0:00.90, peak Lean RSS
2,323,836 KiB, swap 0. The four printed declarations each report only
`[propext, Classical.choice, Quot.sound]`.

The exact final source proves:

* `actualMask` is `inverseTransport` with the actual `TwoSwapSourceTable`
  inactive set and permutation, applied to the pre-existing source chord code;
* `actualCoin` reads `TwoSwapSourceTable.order (TwoSwapSourceG.coinIndex i)`;
* its value is the code at that raw coin index, its transport is the code, and
  its inactive balance is zero; and
* `SourceCircleBoundary.column t alpha j` has zero at every such TwoSwap
  sparse coin, using the pre-existing order-independent
  `R514DegenerateGCore.source_selected_g_zero`.

This closes only this field/table routing gap for the existing 13-column
family. It does not connect that family to `AugmentedQuotient` or the residual
determinant, prove direction coverage, refine Rust execution, or establish a
privacy/security claim.

Failed mechanical drafts and their logs/receipts are retained in `attempts/`:
initial missing/ambiguous namespace forms (`1791110889380771000`,
`1791110901049684000`, `1791110910182892000`), followed by two green drafts
with unused-instance warnings (`1791110922411699000`,
`1791110931554780000`). The final run removes those warnings. No source or
runtime test was run.
