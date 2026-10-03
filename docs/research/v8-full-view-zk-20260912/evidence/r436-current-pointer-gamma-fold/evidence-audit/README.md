# R436 saved compilation custody audit

This read-only audit checks the saved attempt B source, receipt, Lean log, GNU time output, launcher status, before/after cgroup snapshots, and artifact-copy receipts. The root `R436PointerGammaFold.UNVERIFIED.lean` is byte-identical to B's compiled input.

B compiled the target `AspisV8R19/R436PointerGammaFold.lean` successfully. Its single complete axiom report matches the receipt and lists only `propext`, `Classical.choice`, and `Quot.sound`. The source revision and Lean 4.32.0 pin match. GNU time reports 1.52 seconds, 3,709,252 KiB peak RSS, and zero swaps; cgroup peak and GNU RSS are recorded separately. Effective cgroup limits are 5/7 GiB, 0 swap, 128 tasks, with no high/max/OOM events. All six copied-artifact receipts pass.

Attempt A remains as rejected history: an extra `rfl` after the rewrite had closed the goal and Lean reported “No goals to be solved.” A's standard-only axiom print does not make its nonzero-exit run successful.

This is a model-composition custody audit only; it asserts no actual Rust source correspondence or native execution closure. Run `python3 verify_attempt_b.py` from this directory for a fresh read-only report. `SHA256SUMS` covers the audit files.
