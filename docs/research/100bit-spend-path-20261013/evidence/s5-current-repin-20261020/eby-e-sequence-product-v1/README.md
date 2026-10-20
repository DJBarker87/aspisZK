# EbyE finite sequence product bridge

`AspisR1EbyESequenceDecodedProductV1.successful_trace_decoded_product_sum` proves the algebraic result for a finite list of EbyE operand pairs: if each trace step is a successful selected generated push and has the required count-bound/canonical-input premises, then the decoded final accumulator equals the decoded initial accumulator plus the list of operand products.

The theorem consumes the frozen one-step decoded product update. `SuccessfulPushTrace` is an explicit certificate relation; this packet does not show that the outer Rust caller generates that relation. Initial-state construction, source-loop refinement, and global R22 range discharge remain open.

The target compiled with Lean 4.32.0, `-M4400 -j1`, in a 1GiB/2GiB/zero-swap scope. Exit status 0, wall time 2.108s, process RSS 3,928,664 KiB, scope peak 381,177,856 bytes, swap 0. The axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`. Exact config, admission, reservation, preflight, command, logs, and receipt are under `evidence/AspisR1EbyESequenceDecodedProductV1/`.
