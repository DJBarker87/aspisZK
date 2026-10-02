# R366 dependency cache replay

Only the 11 missing local dependency modules listed below were compiled, in order, serially; the loop stopped on the first failure and reached all 11 successfully. Each exact Lean source snapshot, runner receipt, and complete log is copied into this directory. Original scratch records remain in `.r21-scratch/`. The R366 theorem file was not compiled. Every job used Lean 4.32.0 with `-j1 -M4500` under its own systemd user scope (5 GiB high, 7 GiB max, zero swap, 128 tasks). Actual compiler time/RSS and swap are listed per target in `replay-summary.json`; remote source hashes and resulting `.olean` hashes are also included.

Dependency order: StructuredRound, CausalRounds, StructuredCube, SourceMaskLoop, TerminalG, SourceZeroBoundary, MaskWeightBlocks, Mixing, SourceMixing, SourceMixingWeights, MaskWeightVector.

The previously failed R366 attempt is preserved and remains a cache-missing diagnostic; it was not overwritten. No source edits, premise changes, theorem changes, or R366 compile occurred.
