# S4 tx1 exact-gamma batch composition

`S4Tx1ExactGammaBatchesRootV1.same_prepare_and_loop_exact_batches` composes the exact returned gamma/scratch facts from the same successful installed preparation with the ten-query original-port batch theorem. Its proof applies the ten-query theorem in stages (base arguments, then canonicality, powers, carrier map, scan, initial cursor, and loop success); this avoids a costly single dependent application.

`S4Tx1WholeExactBatchesRootV1.accepted_tx1_exact_gamma_batches` derives `k = 10` and a `PreparedBatches` witness, including all ten `ExactTenBatches`, from one successful installed `sourceCaller` tx1 run. The same `p` and `g` returned by that run flow into the gamma bridge and loop theorem.

The result is within the installed caller/source-cut model. Scanner/leaf operation bindings remain explicit; it does not establish frozen Rust dispatcher or standard-library `from_fn` correspondence. Both focused Lean 4.32 runs exited 0 with 0 swaps and standard axioms `[propext, Classical.choice, Quot.sound]`. The complete commands, profiles, resource logs, and producer source/object pins are in `receipt/`; compiled binaries are intentionally not included.


Attempts 1–4 of the small join are preserved with raw source and failure logs. Attempt 5 source is retained, but the original raw receipt/log was overwritten by the subsequent successful run; its reported timeout is marked as parent-reported in `receipt/failed-join-attempt5.json`, not reconstructed. Whole-consumer failed drafts are retained alongside the accepted attempt.
