# S9 actual wide-by-M31 totality

`qm_mul_m31_total` constructs the actual current QM31-by-M31 call's successful result from four existing total `current_mul_mod` contracts. `wide_mul_m31_total` composes the checked remainder and both actual coordinate calls. Both statements cover arbitrary stored U32 inputs, with no canonicality or successful-call antecedent.

`concrete_wideMulM31_total` installs that success in the exact concrete helper operation record. `concrete_wideMulM31_total_exact` then derives canonical output and the decoded scalar-product equality from that same constructed result, under canonical input. The old success-conditional theorem is reused; operation success is now proved rather than hypothesized. This is an actual operation-level improvement, not a whole-helper theorem.

Focused Lean 4.32, `-j1 -M4400`, exit 0, 19.737 s, process RSS 3,153,149,952 bytes, aggregate process-tree RSS 3,140,780,032 bytes, observed swaps 0. All four exported theorem audits contain standard axioms only. Exact source/import/object pins, argv/profile, raw logs, watchdog and receipt retained. No objects/binaries included; no cold dependency build or unchanged replay.

The runner acquired its atomic lock, wrote PID/inode metadata and checked no other Lean before launch. A sibling reported stale empty-lock cleanup with incomplete historical inode evidence around this period. We do not assert continuous cross-session lock ownership from that evidence; the process-tree measurements and successful proof remain valid. The earlier mutex-wait timeout launched no Lean. No rerun was made to manufacture stronger historical lock evidence.

Complete S9 still requires its helper loop/value composition, original array-library correspondence, caller/source binding and global composition. No shipped source or security target changed.

## Reuse correction

The arbitrary-input primitive QM/wide totality lemmas already existed in `AspisR1S3PowersLowTotalV1`; this packet duplicated those proofs. They are not new primitive arithmetic results. The preferred integration consumer is now `s9-focused-mulm31-reuse-root-v2-20261022`, which imports that existing theorem directly and supplies the concrete S9 record's totality/exactness. This historical compile remains mathematically valid; its source and logs are preserved.
