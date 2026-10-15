# Folded WideExact leaf codec evidence

This bundle preserves the focused `R1FoldedLeafCodec` compile and all four attempts: `folded-leaf-a` and `-b` failed during proof development, `-c` compiled but was superseded when the named per-slot lemma was added, and `-d` is the final source. No target was rerun during collection.

The final module defines a strict list codec for one `WideExact` as two canonical 16-byte QM31 encodings, then a four-slot folded value `Fin 4 → WideExact`. It proves per-wide round trips, 32-byte single-value length, 128-byte folded length, successful-decode reconstruction, an exact per-slot characterization, and per-slot extraction. The output audits list only `propext`, `Classical.choice`, and `Quot.sound`.

This is a mathematical byte-model codec. It does not identify the folded representation with C2, establish Rust parser or call-site correspondence, or prove protocol/security properties. `source-manifest.json` records exact source, runner, import-source/object pins, attempt receipts, and the normalized object archive.

The final attempt used the pinned NUC workspace `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013`, target `R1FoldedLeafCodec`, suffix `folded-leaf-d`: exit 0, 1.50 seconds, peak RSS 3,320,012 KiB, swap 0, `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`.
