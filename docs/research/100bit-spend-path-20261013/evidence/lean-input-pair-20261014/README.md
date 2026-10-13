# Input-pair Lean evidence

This directory collects 14 existing focused attempts: 5 successful and 9 failed. Each attempt includes the pinned NUC receipt, output log, time log, SHA256 sidecar, and a source snapshot whose hash matches the receipt. The five final source snapshots and the five final object-member hash records are listed in `source-manifest.json`.

The final source base is `7c740172da25ec986373b7c996a513b9d1c0ec11`. The copy-links source was compiled unchanged on historical base `fd4aff50d1c5d977b6dda12e01356e3a1f0d258a` and matches its final source hash. Runner/environment snapshots are under `environment/`. Final `.olean` objects are retained only in the deterministic `target-objects.tar.gz` archive; member hashes appear in the manifest. No build was run during this evidence collection.
