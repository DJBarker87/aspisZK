# R382 selected mask polynomial degree evidence

This bundle records the promoted research source and its focused Lean compilation, together with every R382 target attempt discovered in the scratch receipts. The target proves a degree bound for a direct polynomial model of the selected mask expression. In that model the C1 terms and mask-only terms both use the ordinary point-0 claim polynomial, as selected by the source composition shape in the included R379 inventory. It also proves the stated cancellation identity for the wrapper polynomial.

The green R382 attempt `1790953727904895000` is retained as **superseded**: its mask-only terms used point 2 (the xor opening), so it does not prove the selected-mask model. The final green attempt is `1790953849208662000`; the four earlier failed focused attempts are retained verbatim. The checker validates every run's saved source, receipt, full log metrics and axiom report; it separately checks the superseded source shape and final point-0 shape. No failed or superseded run is counted as evidence for the final theorem.

The proof uses the R374 line-degree model and the R376 degree bound for ordinary claim polynomials, with the source exponents bounded by small arithmetic proofs. It makes no premise about output-polynomial degree. The R379 inventory provides the source-expression and source-hash basis for the selected schedules. Remaining obligations include proving the coefficient assignment schedules, mutable `selected_mask_linears` computation, reverse Horner evaluation, and tower-basis word execution correspond to this direct-sum model. Actual source execution correspondence, coefficient assignment/execution, cryptographic/security properties, and complete terminal-output claims remain open.

All compilation evidence is the focused target run through the included pinned runner, with `-j1 -M4500` under `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. The successful run records exit 0, 23.01 seconds, 3,692,264 KiB GNU-time Lean-child peak RSS, and zero swaps. Its source revision is recorded in its receipt; the dependency source and runner are copied here with hashes in `formal.json`.

Run the offline checker from any directory with:

```sh
python3 docs/research/v8-full-view-zk-20260912/evidence/r382-selected-mask-degree/verify_evidence.py
```

The checker needs only this repository's promoted target and saved bundle; it does not read `.r21-scratch`, invoke Lean, or access the build host.
