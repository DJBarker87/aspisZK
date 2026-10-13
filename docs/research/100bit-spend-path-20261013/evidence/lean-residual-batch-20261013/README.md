# Residual batch Lean target

`lean/ResidualBatch.lean` formalizes finite algebraic residual-polynomial facts for 22 coordinates, plus the generic 22-by-64 accumulation identity. It makes no probability, Fiat–Shamir, protocol-security, or source-correspondence claim.

The focused target `R1ResidualBatch` compiled successfully on the pinned NUC workspace `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` with `./compile-one.sh R1ResidualBatch f`. The scope was capped at `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`; Lean used `-M5000`. The receipt records exit 0, wall time 1.25 s, peak RSS 2,081,804 KiB, and zero swaps. The source SHA-256 was `a352af8c22bb0bcced49e7de74abce39aea9eaee7e868dc195688ca2ca30405f`.

All printed theorem axioms were `[propext, Classical.choice, Quot.sound]`; no `sorryAx` was reported. Earlier source-revision attempts `a` through `e` and their outputs, timings, hashes, and receipts are retained in `remote-evidence/` to preserve the compile history.

The root-count bound was imported from cached module `R1SubfieldBatchStage2` in that NUC workspace. Its earlier recorded focused compile used source SHA-256 `bca6aaef7b658424ca8f7f3c6d85b12fbaa9299a9321ece3258ff59151580630` (see `../lean-subfield-batch-20261013/receipt.json`). The similarly named local source is `lean/SubfieldBatch.lean`; the checked cached module’s name includes `Stage2`.
