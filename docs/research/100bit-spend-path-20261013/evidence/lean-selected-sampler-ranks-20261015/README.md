# Selected sampler rank equivalences

This bundle records two focused attempts for `R1SelectedSamplerRanks`: failed attempt a and final successful attempt b. The final theorem `stateRank` identifies the selected positional encoding with `R0C.ModuloField.blockRank` via `finCongr`; `ordinary_eq`, `gamma_eq`, and `qm31_eq` are definitional/projection equalities to the existing modulo sampler models. The four successful axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

This is a selected model-level rank/equality result. It does not establish that current Rust transcript sampling implements this rank map, nor a current R1 sampling probability law. Direct import sources and compiled objects are pinned in `source-manifest.json`; the object archive contains the target and the two direct-import `.olean` files.

The focused NUC run used the pinned workspace `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`, Lean threshold 5000 MB. Attempt b exited 0 in 1.55 s with peak RSS 3,557,844 KiB and zero swap. The initial attempt a failed on stale names/proof plumbing; its exact source, receipt, log, sidecar, and timing record are retained.
