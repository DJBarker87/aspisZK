# Frozen Lean reuse checkpoint evidence

This evidence-only manifest contains 24 successful predecessor targets with local staged source snapshots, exact source hashes/imports, compile receipts/logs/time logs/sidecars, complete `#print axioms` declarations, and a deterministic archive of target and available transitive dependency object bytes. Five failed attempts are retained separately under `failed-attempts/`; they are not green targets.

Slash-separated receipt target identifiers are retained in `targets`; dependency-source keys and Lean import names retain dotted module notation. The validator is copied from the prior checkpoint with its docstring adjusted only. This inventory is not a release-gate conclusion.

The lead independently validated all 24 green target records, 31 source/object
entries, 98 standard-only axiom audits and the captured checksum inventory.
The final combined `R1ReuseCheckpoint` attempt b passed in 1.35 s with peak
RSS 3,501,880 KiB and zero swap under MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0. It loads both the new bridges and the refactored older
opening modules. The base source revision is
`0dbaf0c8d576a8da71e031b89cef2c9083c67cca`; dirty source hashes identify the
exact new content. Objects use the pinned cache, so this is not a complete
from-scratch historical manifest replay. Full semantic, Rust, shared-oracle
Fiat–Shamir and privacy obligations remain open.

Loose `.olean` files are git-ignored and excluded from the tracked-file
checksums. Their bytes and hashes are preserved in the compiled-object
archive and verified directly by `validate_manifest.py`.
