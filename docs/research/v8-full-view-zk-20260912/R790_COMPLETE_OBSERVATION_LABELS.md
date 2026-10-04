# R790 full literal observation ordering coverage

This expands the first-eight prototype using the real two-swap table and R746 definitions. It establishes literal membership/row-code/selected-column facts for the remaining 205 high observations, the top unit row, and all eight supplementary observation constructors. It does not establish matrix-entry values or rank.

The deterministic generator and preflight are:

- `generate.py` (SHA-256 `58bf882d7a47e5d64c4e5fb7a6e0cb0c348c08486d0876ba867c7262f7399d82`), run as `python3 .r21-scratch/r790-literal-observation-order/generate.py --check` (passed). It fails closed on source/table hash changes, exact raw row labels, all selected raw headers, constructor coverage, and unexpected/missing generated chunks.
- Generated chunks: `generator-output/R790LiteralObservationChunk00.lean` through `Chunk13.lean`. Every chunk contains at most 16 new observation constructors. All are linked by imports, with Chunk00 importing the already-green first-eight R790 prototype.
- The complete run/source/axiom manifest is `manifest.json` (SHA-256 `ecf1e094ef4403e9c26abce37d4c82a6388f733749adc5cf1ce66ee0eca1e821`). Each target receipt records target, source revision/checksum, exact direct local imports, resources, status, GNU time, RSS and swap; each complete `#print axioms` output is in its log/receipt.

All 14 new chunks compiled green in the pinned Lean 4.32 cached workspace, with `-j1 -M4500`, systemd limits `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. Maximum Lean-child RSS was 3,497,956 KiB, maximum wall time 55.65 seconds, swap remained zero. Every theorem has only `[propext, Classical.choice, Quot.sound]`; no `sorryAx` appears. The first-eight prototype was reused from its earlier successful run (5.14 seconds, 3,335,268 KiB, zero swap); its earlier ambiguous-`I` failed compile remains separately recorded.

The saved raw table has 222 row labels. Slots 0–212 are exactly `active_chord_<source_rowcode>` for the 213 `High` values; slot 213 is `active_chord_1022`, represented by the `Unit` constructor; slots 214–216 are `point_0` through `point_2`; slots 217–221 are `ordinary_relation_1`, `_2`, `_3`, `_5`, `_6`, represented by the five `Fin` constructors. The generated theorems establish actual `highActive` membership and `R707.rowCode` for every high row, and exact `R746.selectedColumns` against the raw selected header `(d, raw_slot-1)` for all 222 observations. The top `Unit` row code is 1022. Supplementary selected pairs are `(23,0..2)`, `(24,0..2)`, `(27,2)`, `(47,2)`.

This resolves the literal observation-order mapping at the constructor/label/header level. It does not equate any saved raw TSV numeric matrix cell with `chosenSourceMatrix`, and it does not assert determinant, rank, privacy, or security. The first remaining matrix obligation is a separate source-to-saved-cell equality bridge; no full matrix or field arithmetic was run here.

## Reproducibility bundle

The standalone evidence bundle is in `evidence/`: it contains exact run source snapshots, receipts, complete logs, generated chunks, input files, imported Lean source copies, complete axiom reports, and a post-run remote source/cache hash listing. `evidence/evidence-manifest.json` records all 16 attempts (15 successful module targets plus the single failed first-eight prototype attempt), checksums, imports, resource measurements, and axiom classification. Its observation index map is `evidence/observation-index-map.json` and lists each definition for observation indices 0–221. The remote sources and cache oleans were read-only hash-checked at 2026-10-04 22:34:23 UTC; the remote source staging tree has no Git metadata, so the run receipts' local source revision plus exact per-file checksums identify the compiled inputs.


First remaining proposition: assemble the complete source observation bijection and prove literal numerical cell equality for the selected source matrix, then derive its nonzero determinant. These mapping facts alone do not prove rank or privacy. Verifier 999,790 / 999,532 CU and all security parameters are unchanged.
