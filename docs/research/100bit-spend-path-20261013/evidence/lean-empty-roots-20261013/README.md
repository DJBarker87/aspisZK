# Empty-root certificate focused compilation evidence

This directory records the authorized NUC check of empty-root nodes 0 through 20. The source base is `3a73ee4bb67558ffbc608abfea81d74b4d2fa2a4`; each attempt has its exact source snapshot and runner receipt, stdout log, resource log, and SHA sidecar under `attempts/`.

The generator `--check` passed before compilation, confirming generated Lean/Rust literal tables, all frozen roots, and split independent round states. The final set contains 43 green targets: zero data/preflight/check plus data/check for rows 01–20. The checker targets report only standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. All successful receipts record swap 0 under MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0.

One dependency-ordering failure is retained: `R1EmptyRoot06Check-a` started before `R1EmptyRoot06Data` had produced its object, so Lean reported an unknown module prefix. After verifying the data object and its successful receipt, the checker passed as attempt `b`; the failed `a` artifacts and source remain intact.

`target-objects.tar.gz` contains the 43 final successful `.olean` objects. Members are sorted and normalized (uid/gid/time zero; gzip mtime zero); member hashes and all attempt classifications are in `manifest.json`. The pinned runner inputs and environment snapshot are under `runner/`. `empty-root-data.json` and the exact generator snapshot are included for provenance. `SHA256SUMS` covers every file except itself.
