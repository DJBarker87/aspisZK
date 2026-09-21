# Fixed active-minor nonvanishing witness

Base `291f0623` plus this changeset, 2026-09-21.

The research-only `r17_active_minor_polynomial_witness` constructs the
214-by-699 direct active map using the immutable source transport and
chord multiplication. Columns are ordered by degree 22..254 and then
channel B,C,D. Each column has that channel coefficient one and A equal
to minus alpha, alpha squared, or alpha cubed respectively. It uses
normalized chord `[1+uv,uv-1,-(u+v)]`.

At the single fixed algebraic evaluation alpha=2,u=3,v=4 in M31, rank is
214. The reduction routine independently checks its computed left inverse
times the original selected square matrix equals identity. The exact
214 zero-based column indices are frozen in
`evidence/r17-active-minor-columns.txt`; the test requires equality with
this fixed minor, rather than allowing a different selection silently.

These parameters lie in CM31 and are NOT accepted OOD parameters. That
does not invalidate a polynomial nonvanishing witness: a polynomial with
any nonzero evaluation is not identically zero. No synthetic execution
or claim about the sampler's support is being made here.

## Degree argument and remaining refinement

Regard alpha,u,v as indeterminates over QM31. Quotient entries have alpha
degree at most 3 and no u/v dependence. Chord entries have degree at most
one in each of u,v and total degree at most 2. `times_x` and inverse
transport are fixed linear maps with field-constant coefficients.
Therefore direct matrix entries have separate degree bounds (3,1,1)
and total degree at most 5. Each determinant term is a product of 214
entries. The fixed determinant consequently has separate degree bounds
(642,214,214), and total degree at most 1070. Summation cannot increase
these upper bounds. Its nonzero evaluation above is an executable exact
field certificate, not yet a kernel-checked determinant certificate.

This is an explicit mathematical degree argument based on the inspected
linear routines, not a compiled Rust-to-polynomial correspondence theorem.
The next formal obligation is to represent that polynomial matrix and
certify the fixed minor/degree bridge. Probability accounting additionally
requires a justified source challenge law, including adaptive shared-oracle
conditioning and rejected/repeated draws. No numerical source loss is
claimed yet. H1 point rows, G residual rows, C1 coverage, commitments,
seed expansion, retries/publication and soundness remain separate gates.

## Focused evidence

Only the named Rust test ran, offline/locked/release/jobs=1, package
aspis-prover, --lib, --nocapture, timed with `/usr/bin/time -l`.
Initial compile failed because QM31 has no `from_m31` constructor: exit
101, wall 2.60s, RSS 416645120 bytes, swaps 0. Replaced those three calls
with the existing `ONE.mul_m31` API. The corrected test passed: exit 0,
wall 23.57s, RSS 561201152 bytes, swaps 0. Logs are respectively
`/tmp/aspis-r15-host.drHYn9/r17-active-minor.log` and
`/tmp/aspis-r15-host.drHYn9/r17-active-minor-v2.log`.
No Lean source changed in this step; no new axioms audit is claimed.
After freezing the column artifact, the changed test passed again: exit
0, wall 23.83s, RSS 562708480 bytes, swaps 0; log
`/tmp/aspis-r15-host.drHYn9/r17-active-minor-v3.log`.
