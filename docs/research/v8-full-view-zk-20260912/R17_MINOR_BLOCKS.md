# R17 small-block certificate route

## Frozen block artifact

Base `00cc7a1e` plus this changeset. The source test now asserts exact
equality with `evidence/r17-minor-blocks.jsonl`, containing all 133 blocks.
Each record gives reachable-set `order`, `rows` as zero-based positions
in the original 214-active-row list, `columns` as zero-based positions
in the frozen 214-column minor, and `values` in row-major order. Values
are canonical M31 residues at alpha=2,u=3,v=4; each value is checked to
embed back into QM31 exactly, excluding a silently discarded extension
component. Columns refer to `r17-active-minor-columns.txt`, not directly
to the 699-column map. Sorting blocks by decreasing order gives the
checked triangular order. Equal-order distinct blocks have no connecting
support edge.

The 133 records contain 29 distinct evaluated matrices, allowing repeated
tiny determinant proofs to share named lemmas. This is frozen exact source
evidence, not yet a generated Lean certificate. Next: compile determinant
nonzero leaves for those 29 cases and formally bind their reuse and the
block permutation/structural zero pattern. A nonzero determinant at this
algebraic witness remains distinct from a source-sampler probability law.

Focused command is the same named offline/locked/release/jobs=1 test below.
Initial export compilation failed on a field-member typo and JSON format
brace: exit 101, 2.52s, RSS 416792576 bytes. Correcting the member left
the format error: exit 101, 1.81s, RSS 404979712 bytes. Both were fixed.
Export test then passed: exit 0, 23.85s, RSS 566951936 bytes. All zero
swaps. Logs under `/tmp/aspis-r15-host.drHYn9/` are
`r17-minor-block-data.log`, `r17-minor-block-data-v2.log` and
`r17-minor-block-data-v3.log`. The artifact was populated from the passing
output, then added as an exact assertion to the source test.
Final frozen-artifact assertion passed: exit 0, 24.43s, RSS 566099968
bytes, zero swaps; `r17-minor-block-frozen.log` in the same log directory.

Base `c54fedc8` plus this changeset, 2026-09-21.

The fixed 214-column minor has only 599 potentially nonzero polynomial
entries under the six-constant representation. The support calculation
uses whether ANY of the six field constants is nonzero. It does not use
entries that happen to vanish at alpha=2,u=3,v=4. This is an overapproximate
symbolic support, so additional polynomial cancellations cannot invalidate
its zero pattern.

A perfect matching of this support identifies rows with columns. Mutual
reachability partitions the resulting directed graph into diagonal blocks.
The test checks that every edge between different blocks strictly decreases
reachable-set cardinality, yielding a block-triangular order. It separately
checks each diagonal block at the fixed evaluation using the existing
independent inverse-product rank check. The expected partition is 60
one-by-one, 65 two-by-two and 8 three-by-three blocks, totaling 214.

This changes the planned formal certificate: use the block permutation,
structural zeros and 133 tiny determinant witnesses, not a dense 214-square
inverse or expansion. No generated Lean certificate or formal determinant
factorization is claimed yet. The next required artifact is a frozen block
layout and source-bound small-block coefficient certificate, then generic
block-triangular determinant composition. This is a resource preflight and
exact executable certificate analysis, not a full privacy or soundness
result. All source/adaptive/shared-oracle/retry/publication obligations
remain separate.

## Focused evidence

Command from the privacy worktree: `/usr/bin/time -l cargo test --offline
--locked --release --jobs 1 -p aspis-prover --lib
r17_active_minor_polynomial_witness -- --nocapture`.
Initial support decomposition passed: exit 0, wall 24.74s, peak RSS
566640640 bytes, zero swaps. Log:
`/tmp/aspis-r15-host.drHYn9/r17-minor-support.log`.
The existing full minor rank, fixed pivot list and 149586 entry comparisons
remain checked. No Lean source changed or axioms audit ran in this step.
The strengthened test checking the exact block histogram, strict triangular
ordering and every diagonal block passed: exit 0, wall 24.41s, peak RSS
568066048 bytes, zero swaps; log
`/tmp/aspis-r15-host.drHYn9/r17-minor-blocks.log`.
