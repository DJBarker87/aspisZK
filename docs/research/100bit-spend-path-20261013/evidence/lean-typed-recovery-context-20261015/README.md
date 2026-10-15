# Typed recovery context evidence

This focused module constructs the existing `R0P.SemSource.TypedContext` from the strict total typed-word representation. It fixes the context word using C1-only recovery with invalid or missing C2 leaves mapped to zero, then proves that supplying the C2 lanes 26 and 27 reconstructs the full word and satisfies the corresponding typed base predicate. This is a representation bridge only; it does not connect recovered bytes to protocol source paths or make a causal, acceptance, probability, or security claim.

Final green target: `R1TypedRecoveryContext`, attempt `typed-recovery-context-e`, exit 0, 1.92 s, peak RSS 3,542,228 KiB, zero swap; cgroup `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. Both public theorem audits report `[propext, Classical.choice, Quot.sound]`. Attempts a–d failed and are retained with exact snapshots, receipts, logs, and timing.

Final source SHA-256: `2996554b29c722580cb6f105015803bbb1ac1f0847532f6aef32366e1496f0bb`. The pinned NUC workspace and runner/import source and object hashes are recorded in `source-manifest.json`.
