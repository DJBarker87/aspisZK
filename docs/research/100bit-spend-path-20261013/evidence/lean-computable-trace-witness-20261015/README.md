# Computable trace witness focused proof

`R1ComputableTraceWitness` compiled in the pinned NUC workspace at 4 GiB memory-high / 6 GiB max / 0 swap / 128 tasks. Attempts a-c failed on the path-function equality proof; their exact source snapshots, source hashes, receipts, logs and time records are retained. Attempt d succeeds.

The module defines `pathFromTrace` using a decidable M31 zero comparison after explicit coordinate projection, and a literal computable `fromTrace` witness. Under the existing `BaseTyped` premise, `pathFromTrace_eq` identifies the path with `SpendDataMap.path project (tracePath A)`, and `fromTrace_eq_projected_existing` identifies the full witness with the projection of `TraceSpendWitness.fromTrace`. Both public audits report `[propext, Classical.choice, Quot.sound]`; neither selector definition uses `noncomputable` or `Classical.choose`. The result constructs data only and does not prove `Rspend` or another validity condition.

Source revision `c7b5a949e2274b15ac91a6299fbbc3da691aeb3c`; source SHA-256 `2025bc75176168fcfb738453effcad4a506e561e97c27b9105ffd302dc00e0e1`; object SHA-256 `b42ead4a64af7d22fcf67df3151659753e7f6fae4acd3b91cbe428fff5e8c3f3`.
