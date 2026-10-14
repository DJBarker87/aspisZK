# FS reuse focused Lean evidence

This bundle collects 17 capped focused attempts for the six final targets listed in `source-manifest.json`. It is pinned to source base `e8b1a73c6e3fd764ca01701c9c936cd705ce74b1`. Attempt receipts retain their per-target exit status, elapsed time, peak RSS, swap, cap, and exact source hash. Every attempt source snapshot is present and hash-matches its receipt.

`R1QueryContinuation-b.source.lean` was recovered from edit history by `fs_reuse_inventory`; its SHA256 matches the original attempt receipt. The source was not recompiled. Other query-continuation snapshots came from the NUC attempt evidence. The one-attempt prefix, recovery, and checkpoint snapshots were copied from their current NUC sources after verifying the attempt receipt hashes. SemanticContext and DuplexRewind snapshots came from their task evidence directories and were similarly hash-checked.

The six final source files and six Lean objects are indexed in the manifest. The object files are retained only as members of the deterministic gzip/tar archive; no loose `.olean` files are included. `runner/` contains the exact pinned `compile-one.sh`, `run2.py`, and `environment-base.json` snapshots.
