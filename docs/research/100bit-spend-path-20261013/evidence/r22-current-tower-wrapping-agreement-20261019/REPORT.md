# R22: current extension-field checked/wrapping agreement

The new CM31 and QM31 modules lift the checked M31 agreement results through the actual current extension-field source bodies. On canonical inputs the current CM31 add/sub/mul, multiplication by r, and QM31 add/mul are total, equal their explicit wrapping-primitive bodies, and preserve canonicality. In particular the extra U64 sums and cross-product in current CM31 multiplication are covered; they are not silently treated as M31 operations.

The proof reuses the existing current-source canonicality and source-shaped cross-product results, followed by compositional rewrites. It introduces no replacement arithmetic runtime, Rust modification or verifier artifact. This addresses these core field kernels; it does not prove the distinct optimized fast-pairing implementation or canonicality of every caller's inputs.

| Checked target | Exit | Wall | Peak process RSS KiB | Cgroup peak bytes | Swap bytes |
| --- | --- | --- | --- | --- | --- |
| Canonical current CM31 agreement | 0 | 1.906 s | 2,630,872 | 307,920,896 | 0 |
| Canonical current QM31 agreement | 0 | 1.805 s | 2,626,712 | 305,205,248 | 0 |

All eleven printed theorem reports contain only `propext`, `Classical.choice`, `Quot.sound`. Focused NUC scopes used MemoryHigh=512 MiB, MemoryMax=1 GiB, MemorySwapMax=0. Exact revision/source/object/import/compiler hashes, ordered roots, commands, admissions, reservations, GNU-time and receipts are retained. No OOM, cap increase, or full manifest replay occurred.

Publication checked all 63 payload hashes and both accepted source hashes. Archive SHA256: `7d41d6885d16a8f9908145a1e810a499dbf7ec46eedd2c4c58a8bafc3bdc6671`. Readable sources are under `lean-candidates/r22-current-field-wrapping-20261019`.

The failed CM31 v1/v2 proof snapshots are retained: both were local alias/monadic-body rewrite mismatches. The final proof exposes the exact source-shaped bind sequence and uses the same checked sum/product facts; v3 passes. R22 still needs admitted-path source range propagation, optimized fast-pairing arithmetic, control/index arithmetic, and the final deployed-acceptance-to-model theorem. No held commitment-layer work is included.
