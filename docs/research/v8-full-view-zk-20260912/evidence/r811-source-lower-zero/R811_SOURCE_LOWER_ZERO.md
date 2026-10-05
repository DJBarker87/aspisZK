# R811 source lower-zero lemma package

This evidence package contains the focused proof runs for the 213 remaining active-row lower-zero facts, plus the previously compiled `rowFlat35_lower_zero` prototype. These are symbolic support facts for the 222-by-222 reordered source matrix. They do not prove the full determinant, a privacy theorem, or end-to-end security.

The chunk generator maps active source row IDs through the pinned active-code list and row-order inverse, then closes each lower-position zero using exact support exclusions against the captured sparse source row. Coverage validation found 213 distinct chunk rows and, with the reused prototype at flat row 35, 214 active rows total. The eight uncovered flat positions are the non-active rows `{0, 1, 2, 3, 4, 5, 72, 73}`.

All 54 chunks have an exit-zero run whose source hash equals the packaged current chunk source. All four failed attempts are retained: the initial prototype compile, two initial chunk-01 attempts, and the first chunk-23 attempt. Chunk 23 was regenerated after its singleton support exclusion incorrectly projected `.1`; the corrected theorem uses the proposition directly. The previous failed source and exact log remain archived.

Each green chunk used the pinned focused Lean runner with `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; all green axiom reports are `[propext, Classical.choice, Quot.sound]`. Per-run source revision, source hash, direct import hashes, exit status, wall time, RSS, swap, and complete axiom output are in each receipt. Logs and exact source snapshots are alongside each receipt.

The next permissible formal step is a dependent aggregation theorem importing these exact chunk modules and the prototype and proving the indexed lower-zero property for all active rows by dispatching through the row-to-flat mapping. It must preserve the eight non-active rows outside the claim. This package does not assert any determinant/source execution/cryptographic conclusion.
