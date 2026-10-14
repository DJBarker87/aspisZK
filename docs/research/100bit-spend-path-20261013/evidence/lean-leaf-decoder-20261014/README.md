# Fixed-width leaf decoder focused evidence

This bundle records the focused Lean evidence for fixed-width list slicing, decoding, and the mixed C1/C2 leaf wrapper. It makes no parser-to-Rust or security claim.

Source base: `8b62ca762b89b5af8f131d1c97a5c6d400df2a6b`.

The manifest records 22 receipt-backed attempts: 8 final green targets and 14 failed attempts, with no superseded green attempts. Every attempt retains its exact source snapshot, receipt, source and target SHA sidecars, stdout log, and time log. The eight final `.olean` files are in `objects/leaf-decoder-objects.tar.gz`; the manifest records the archive hash and each member hash. The runner directory contains `compile-snapshot.sh`, `compile-one.sh`, `run2.py`, and `environment-base.json` with their hashes.

Self-validation confirmed all snapshot hashes against receipts and sidecars, all final source hashes against their final receipts, all four runner hashes, all eight archived object-member hashes, and 48 final axiom-audit reports. The per-target exit, elapsed time, peak RSS, swap, and cgroup values are in `source-manifest.json` and the raw receipts.
