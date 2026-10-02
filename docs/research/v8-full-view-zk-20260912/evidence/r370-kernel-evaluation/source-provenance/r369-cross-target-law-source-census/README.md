# R369 cfg and cross-target coefficient-law census

Read-only mechanical source/provenance inventory. It resolves the R117 `v8_positive_transfer` cfg from the exact staged profile, then records nearby Lean coefficient/polynomial results. No build, Lean compile, test, elimination, source edit, or theorem synthesis was performed.

The exact R117 staged `r17-stage.json` was fetched read-only from the frozen R117 root. Its SHA256 (`5efe649e…077e`) matches the hash pinned in saved R117 `r18-stage.json`; it includes `--cfg v8_positive_transfer`. The wrapper chain `run_r117_full → run_r107_full → run_r106_full → run_r84_full` sets host-build `RUSTFLAGS` from this profile. R118 uses the same profile-field assignment.

No direct existing theorem was located for the requested arbitrary-q,w sourceKernel polynomial/dot-product law. Closest named results and limits are in `inventory.json`; excerpts and hashes are in `excerpts.md`. `coefficient_blocks` gives the kernel sum with quarter and reversed slots, while `lift_coefficient` handles a specific alpha-dependent vector; neither states the combined identity requested.

`SHA256SUMS` covers the copied sources and report files.
