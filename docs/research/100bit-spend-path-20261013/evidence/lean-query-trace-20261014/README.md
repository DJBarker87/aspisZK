# Query trace focused Lean evidence

This bundle captures 22 capped focused attempts for ten final targets, pinned to source base `84de41db1c7a26101183efa8bd4fe2b06a31bb40`. It preserves 12 failed attempts and ten final successful targets. Every attempt source snapshot matches the receipt source hash and sidecar. Five final attempt snapshots missing from the NUC evidence directory were copied from current NUC sources only after exact hash comparison; that provenance is recorded in the manifest.

The final checkpoint `R1QueryTraceCheckpoint-a` passed in 1.36s at 3,525,648 KiB peak RSS with zero swap and 18 axiom reports. Its source hash is `e7ff92dc22e051917b1d89a49a7dbc751b02faf63a770247a05cafb95506d184`.

`final-sources/` contains the ten final source snapshots. `objects/query-trace-objects.tar.gz` contains the ten final Lean objects with normalized timestamps and ownership; no loose `.olean` files remain. `runner/` contains the pinned runner and environment snapshot. `SHA256SUMS` covers every bundle file other than itself.

The lead's independent `ROOT-VALIDATION.json` audit confirms all attempt hashes, resource receipts against time logs, ten current sources against final snapshots, ten archived object hashes, and all 36 successful axiom reports. Those reports use only `propext`, `Classical.choice`, and/or `Quot.sound`. This is evidence for the local bridge, not a full protocol security certificate.
