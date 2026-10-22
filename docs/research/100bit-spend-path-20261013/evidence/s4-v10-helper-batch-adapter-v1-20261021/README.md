# S4 v10 helper-to-batch adapter

This source-only focused packet proves a same-batch result for the explicit `FourDotsOps` model. If the parameterized v6 body succeeds, it transfers through the retained eight-step product and eight-step fold/update proofs and yields the same actual batch witnesses: selected batch range, bounded `ActualTermTrace` contributions, per-product caps, and exact per-limb update by the fold of those contributions. The theorem derives `wideLimbCount = ok 8` by `rfl`; it does not re-prove the coordinate arithmetic.

The checked theorem is `AspisR1FastDotsV10FixedBodyBatchExact.v10_fixed_body_success_actual_batch_exact` in `sources/S4V10FixedBodyBatchExact.lean`. Its premise is successful `FunsOpsFixedV6.fast_dots.four_dots_one_loop0.body` under the actual-batch operation record. The source-chain checker compares the five emitted v10 helper definitions against the corresponding v6 emitted definitions, runs the exact v10 extraction checker, and runs the v6 generated-to-`FourDotsOps` adapter checker. This pins the explicit operation adapter at the source level; it does not make raw external Funs an axiom-free Lean owner or prove that adapter relation in Lean.

The target compiled with Lean 4.32, `-j1 -M4400`, using the retained 5,946-object warm cache; no dependencies were built. The final receipt records source revision, command, wall time, process/aggregate RSS, zero swaps, object hash, and standard axiom audit. The earlier first-pass logs are kept under `diagnostics/` and are superseded by the final green receipt. No `.olean` binaries are included.

For the five selected prerequisite objects, source hashes and successful compile receipts are retained, but their selected-object receipts do not include swap metrics. Older receipts report zero swap for the same source with different object hashes, so this packet does not infer or transfer those values. The final wrapper run itself records zero swaps; prerequisite swap usage is unknown.

Rust `array::from_fn`/Try-trait semantics and the P6 model correspondence remain open. Frozen-source equivalence and adoption remain open; this is a candidate-specific checked composition only.
