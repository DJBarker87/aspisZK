# Trace spend witness and base descent focused Lean evidence

This bundle contains the green focused targets `R1SpendBaseDescent` and `R1TraceSpendWitness`, their direct import source snapshots, and all four attempt receipts/logs/source snapshots. `TraceSpendWitness` attempts a and b failed on local proof elaboration; attempt c is the final green source.

The `fromTrace` record mirrors the existing production witness field selection. `base_coordinates` proves only membership of the selected field coordinates in the embedded base subfield from `BaseTyped`. The witness constructor is noncomputable because the existing `tracePath` selector is noncomputable. This evidence does not prove that the trace is spend-valid, provide an efficient extractor, or refine current Rust parsing.

Final targets compiled with `compile-snapshot.sh` in the pinned NUC workspace under `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. Exact attempt metrics and axiom reports are in the receipts and logs. The object archive contains the two target objects and four direct import objects; there are no loose `.olean` files.
