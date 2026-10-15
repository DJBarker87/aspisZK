# Unified opening-row density evidence

This focused bundle records the rowwise density bound for the four opening challenge rows and its direct composition with the existing causal first-hit adapter. It does not establish a concrete transcript-to-decoder bridge, acceptance-to-hit, or extraction.

The final target `R1UnifiedOpeningDensity` compiled from source SHA-256 `da14425c9d497daaeffccba3921d0a0283f015a43215b60bbcbd1ebda26d6648` on pinned base revision `6459d24bcd83bf12441b606d8031b6c9301bc320`. Attempt `opening-density-k` exited 0 in 2.81 seconds at 3,588,244 KiB peak RSS with zero swap under `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. Both public results use only `propext`, `Classical.choice`, and `Quot.sound`.

The density theorem is uniform over an explicitly supplied decoded context and uses the row-specific sampler equalities at rows 27–30. The first-hit theorem applies `UnifiedCausalBound.first_hit_bound` with that density bound and nonnegativity of `openingCap`. It adds no acceptance condition.

All eleven attempts are preserved, including nine failed source revisions, the superseded green density-only attempt `i`, and final attempt `k`. Receipts, source snapshots, source sidecars, logs, and runner inputs are kept under `attempts/`, with the untouched remote evidence copies retained under `evidence/`. The final `.olean` appears only inside the normalized archive at `objects/R1UnifiedOpeningDensity.tar.gz`.
