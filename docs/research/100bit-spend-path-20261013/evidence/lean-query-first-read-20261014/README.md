# Query first-read focused Lean evidence

This bundle records 35 capped focused attempts for the twelve final targets listed in `source-manifest.json`, pinned to source base `52023cce56db49914ea5dc6980d859ec8786360d`. All attempt receipts, logs, resource time logs, source-hash sidecars, and attempt source snapshots are included. Every source snapshot hashes exactly to both the receipt and its sidecar.

The attempt record includes failures and intermediate successful compiles. A missing NUC attempt snapshot was replaced only where an exact local task snapshot existed or the current NUC source hash exactly matched that attempt receipt; provenance is recorded per attempt. No attempt was rerun for collection.

The twelve final source snapshots and their twelve object files are listed in the manifest. Object files are retained only inside the deterministic gzip/tar archive; there are no loose `.olean` files. `runner/` contains the pinned `compile-one.sh`, `run2.py`, and `environment-base.json`. `SHA256SUMS` covers every bundle file other than itself.
