# R435 saved compilation custody audit

This read-only audit checks attempt B's root source copy, receipt, Lean log, GNU time output, cgroup snapshots, launcher status, and artifact copy receipts. The root `R435HelperGuards.UNVERIFIED.lean` is byte-identical to the compiled B source.

Attempt B compiled successfully for `AspisV8R19/R435HelperGuards.lean` with four complete axiom reports. Each report contains only `propext`, `Classical.choice`, and `Quot.sound`; none contains `sorryAx`. The source revision and Lean 4.32.0 pin match the receipt. GNU time records 1.09 seconds, 2,540,672 KiB peak RSS, and zero swaps. Effective cgroup limits and event counters are checked independently, and the cgroup peak is reported separately from GNU RSS. All six copy-status records pass.

Attempt A remains preserved as a failed platform-size simplification proof; its `sorryAx` output is rejected history. B uses `System.Platform.numBits_eq`. The audited result is a generic Lean scalar/helper fragment only, with no native execution-closure or Rust source-correspondence claim.

Run `python3 verify_attempt_b.py` from this directory to print a fresh read-only report. `SHA256SUMS` covers the audit files.
