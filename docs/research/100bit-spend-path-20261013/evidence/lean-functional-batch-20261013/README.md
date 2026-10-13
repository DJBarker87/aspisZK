# FunctionalBatch focused Lean receipt

The final source is `R1FunctionalBatchClean.lean`; the initial attempt is
preserved with its unused-section-variable warnings. Both attempts compiled
successfully. No package build or other Lean target was run.

- Source target: `docs/research/100bit-spend-path-20261013/lean/FunctionalBatch.lean`
- Source revision: `7742957648c33cf045eb6a672e7c7cc796b61087`
- Final source SHA-256 (base revision plus this uncommitted source):
  `b21ac7058403ffaa617b3d1507a54c5de09767be5c664fd3e16ad619327fad7d`
- Pinned host/toolchain: NUC `dombarker@100.108.41.90`, cached workspace
  `/home/dombarker/project-offloads/aspis-fs-generic-20261006`, Lean 4.32.0
  (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`), using `objects2` and the
  existing `LEAN_PATH`.
- Reservation before the final attempt: populated caps 24 GiB + 6 GiB; the
  existing `aspis-z8b-full.scope` was MemoryHigh 3 GiB, MemoryMax 4 GiB,
  MemorySwapMax 0. `run2.sh` enforces the 55 GiB aggregate-cap check.
- Final command: `./run2.sh functional-batch-r1-20261013b R1FunctionalBatchClean 5000 6`
- Final target: `objects2/R1FunctionalBatchClean.olean`; Lean exit 0,
  `run2.sh` exit 0, wall 1.32 s, maximum RSS 2,081,180 KiB, swaps 0.
- Final `#print axioms` for all four theorems:
  `propext`, `Classical.choice`, `Quot.sound`.

Attempt A used the same run limits and passed in 1.31 s (2,081,040 KiB peak
RSS, zero swaps). Its source SHA was
`169c7bf417b0841f873c56eff704e206a6d58737a13ff7fbcb16fb856f381e2c`; it had
two warnings that `[DecidableEq T]` was unused. The unnecessary family-index
instance was removed for attempt B; no theorem premise or result changed.

The two archived source-hash files, source snapshots, stdout/axiom logs and
`/usr/bin/time -v` logs are retained here as `*20261013a*` and `*20261013b*`.
