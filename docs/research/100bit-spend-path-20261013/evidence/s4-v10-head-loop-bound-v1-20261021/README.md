# V10 typed seven-batch head-loop bound

This packet proves a typed source-model connection for the transparent V10 head loop. `v10HeadBody_eq_fixedBody` transports the V10 head body to the existing fixed-v6 body after replacing only its nested V10 term-loop call with the checked typed adapter. `v10HeadLoop_eq_fixedLoop` lifts that exact body equality through `Aeneas.Std.loop`. `v10HeadLoop_success_seven_bound` then reuses the fixed-v6 seven-batch theorem on the same mapped coefficient array, iterator, initial limbs, and successful output.

The output bound is `cell output i ≤ 7 * Cap` for all eight cells, under mapped-coordinate bounds and successful execution from `StepSchedule.startBy`. Lean 4.32 reports only `propext`, `Classical.choice`, and `Quot.sound` for all three declarations. The focused compile took 9.39 seconds, 2,267,922,432 bytes peak RSS, and zero swap. The launch revision and compiler hash are in `receipts/receipt.json`; generated and dependency source snapshots are pinned in the manifest.

This packet does not establish concrete source-operation installation, the full V10 helper/callback equivalence, outer `from_fn` correspondence, or the Rust/P6 standard-library boundary. The V10 implementation remains a candidate model. No production source changed.
