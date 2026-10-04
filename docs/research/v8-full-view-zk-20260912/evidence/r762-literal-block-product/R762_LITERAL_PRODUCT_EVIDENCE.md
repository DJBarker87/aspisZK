# R762 explicit literal determinant product: evidence index

Final target: `AspisV8R19/R762LiteralBlockProduct.lean` (source SHA-256 `0f2457f9a743aaaa6fa21e2fb7979663cd58972c182ddb006d23c3bce7a4e368`).

The final theorem proves `IsUnit` for the explicitly constructed product of 41 literal block-determinant factors in SCC order. It uses 11 named chunks of at most four factors, the 40 cached R752 inverse theorems, and the cached R751 left-inverse fact for SCC 6. The expression is not a `Fin 41`-indexed determinant family and has no source-global determinant binding.

The final focused run was `1791146752944767000`: exit 0, wall 1.85 s, peak RSS 3,416,860 KiB, swap 0, cgroup `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, Lean flags `-j1 -M4500`. Its 53 complete `#print axioms` reports contain only `[propext, Classical.choice, Quot.sound]`.

A prior probe reproducing the single branch conversion from the original `Fin 41`-indexed `blockDet` failed at the `unit_00` declaration with kernel excessive memory use (run `1791146530047492000`, exit 1). The five earlier R762 family attempts are also retained. The changed explicit product shape succeeded without raising caps or recursion depth.

The two smaller direct-product preflights compiled first: the 2-factor shape at run `1791146659404802000` and the 4-factor chunk at `1791146680416220000`; both exited 0 with only the three standard axioms.

The evidence manifest includes all nine R762/R763 attempt sources, receipts, logs, complete axioms, source revisions, checksums, wall times, RSS and swap. It also pins 42 direct imported Lean sources and cached oleans: 40 R752 inverse modules plus R751 and R747. For these imports, local and NUC source hashes match.

No verifier-source correspondence, determinant of a verifier-global matrix, or privacy/security conclusion follows from this literal-product theorem.

Artifacts:

- `manifest.json` — structured exact attempt and direct-import inventory.
- `attempts/<run-id>/` — exact source snapshot, log, and JSON receipt for each attempt.
- `../R762_DIRECT_IMPORT_REMOTE_SHA256SUMS.txt` — raw NUC source/olean hash command output.
- `../R752_SUCCESS_INVENTORY.json` — all 139 successful R752 modules and their cached `.olean` hashes.
