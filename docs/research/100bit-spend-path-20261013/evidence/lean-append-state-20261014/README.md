# Append-state Lean evidence

This directory collects existing focused NUC attempt evidence for the frontier-preservation chain. It contains 23 attempts: 8 successful and 15 failed. Every attempt has its exact receipt, stdout log, time log, SHA256 sidecar, and source snapshot; source hashes match their receipts. The eight final source snapshots and object hashes are listed in `source-manifest.json`.

`R1AppendTreeState-a` failed because its import used the wrong module prefix (`R1AppendCarryIndexed`); this was an import-name failure, not a theorem failure. Source base: `fd4aff50d1c5d977b6dda12e01356e3a1f0d258a`. Pinned workspace: `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` on `dombarker@100.108.41.90`. Runner and environment snapshots are under `environment/`. The eight final `.olean` files are packed in `target-objects.tar.gz`, with normalized tar metadata and gzip timestamp. No package-wide replay was run for this collection.
