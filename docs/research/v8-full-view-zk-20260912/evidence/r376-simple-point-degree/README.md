# R376 simple point degree evidence

This saved evidence records a focused Lean compile of `AspisV8R19/R376SimplePointDegree.lean`; no compile was repeated during evidence preparation. The promoted research source at `../../lean/AspisV8R19/R376SimplePointDegree.lean` is byte-identical to the successful compiler input. Both attempted source snapshots, complete logs, and receipts are preserved under `runs/`; the earlier failed attempt is retained with its `sorryAx` reports and nonzero exit. The runner copy matches the successful receipt's SHA-256. The direct R374 import is archived under `dependencies/` and matches the successful receipt hash.

The green run was `1790951275309097000`, exit 0, 1.04 s, peak Lean-child RSS 2,291,652 KiB, swap 0, under MemoryHigh 5G / MemoryMax 7G / MemorySwapMax 0 / TasksMax 128 with `-j1 -M4500`. The three complete axiom reports are recorded verbatim in `formal.json`; each reports only `propext`, `Classical.choice`, and `Quot.sound`.

The result is bounded to the ordinary/xor R374 model table: the claim polynomial has degree at most 1 when `which.val != 1`. The R374 successor-degree bound is not weakened. This does not establish actual Rust execution correspondence, full terminal degree, or privacy.

Run `python3 verify_evidence.py` from any working directory to check the saved target/import copies, source/log/receipt hashes, runner identity, status/metrics/axioms, and root-only checksum index. This checker does not invoke Lean.
