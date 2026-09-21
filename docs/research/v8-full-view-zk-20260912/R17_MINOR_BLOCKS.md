# R17 small-block certificate route

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
