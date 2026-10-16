# Extracted selector expansion reaches the existing product theorem

`SelectorExpansionOldAdapter.expand_model_product` proves the extracted candidate's actual mutable-array `Selectors.expand` succeeds on canonical coordinates when capacity suffices, preserves canonicality, and decodes to the exact tensor-product selector in every in-range position. The inner and outer generated loops are connected to the old descending update recurrence.

The product mathematics is reused from the earlier `SelectedSelectorExpansion.lean`: `SelectedSelectorExpansionCore` retains the relevant pure definitions and proved lemmas without importing the unrelated large V7 certificate chain. The shared generated QM31 subtraction is imported from `EqualityValueSlice`; the obsolete slice that redefined it is not used. These are candidate source proofs, not a claim that the production verifier has been fully refined. Actual at_point/row composition and the wider source-to-semantic bridge remain separate tasks.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. SelectorSourceSlice is definitions only and has zero theorem reports. Exact source/import pins, cap, wall time, RSS and axiom outputs are retained per target.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `SelectorSourceSlice` | 1.448 | 2611436 | 0 |
| `SelectorExpansionCorrectness` | 2.185 | 3015792 | 4 |
| `SelectorExpansionOuter` | 2.186 | 3015936 | 2 |
| `SelectedSelectorExpansionCore` | 2.149 | 3343288 | 4 |
| `SelectorExpansionOldAdapter` | 2.064 | 3814580 | 7 |
