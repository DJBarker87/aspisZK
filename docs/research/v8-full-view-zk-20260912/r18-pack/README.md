# Aspis R18 — structural CU reset

**Pinned source:** privacy branch at `6677d5f1310ff7373301fbd79f186278f772e68a`.
**Current measured source endpoint:** R43 primary checkpoint 16,456,519 CU;
not a complete accepted transaction. R44 compact geometric G is slower.
**This package:** new mathematical design, executable finite-field screening,
operator identities, Rust integration drafts, and a staged source/SBF task.
**Not established here:** actual Rust compilation, SBF savings, full-view
privacy, malicious-prover soundness, or a below-budget transaction.

## Primary change: remove Vandermonde G entirely

Keep the current R16 encoding transform T and both R17 opening channels.
Select 271 spaced code coefficients instead of computing 271 Vandermonde
functionals of G:

    u[i] = (T G)[128 + 3*i],  i = 0..270.

These are existing independent coordinates in the ideal balanced-mask model,
with an exact 752-coordinate complement. The structured ten-round mask is
unchanged as a polynomial of u. Its verifier functional is now sparse in CODE
coordinates. It requires no numerator tree, FFT, dense G vector, G dual
permutation correction, or dense G chord/fold pipeline.

The supplied sparse terminal uses the retained 16-by-64 chord geometry and
386 full-field products in its main contraction, excluding geometry, coin
weight construction, and optional four output scales. This is an operation
count, not a CU benchmark.

**This changes the protocol profile.** Do not accept R17 v2 proof bytes under
it, or treat the old full-view/Fiat–Shamir obligations as discharged.

## Separate second change: minimum-support completion of the repair map

Keep the exact same first 89 mask images and original balance pivot 1023,
but fix every coordinate not forced to move. This gives 163 moved entries
instead of 479. Its finite modeled G/H1 ranks pass; arbitrary-vector sparse
correction contractions pass. Stage it AFTER sparse G and under its own
version, not as an unreviewed extra edit to the first candidate.

A more aggressive bit-affine permutation also passed raw and G tests, but
lost 23 H1 dimensions. It is rejected and preserved as a negative control.

## Run the executed checks

Requires Python 3 and a C++17 g++ compiler, no external packages or network:

    python3 run_checks.py --build-dir /tmp/aspis-r18-checks-UNUSED

The output directory must not exist. Assertions cannot be disabled: the
C++ source rejects NDEBUG builds. The runner checks exact expected ranks,
including negative controls, rather than treating exit zero alone as proof.
The evidence supplied in this ZIP records the completed focused invocations.

## Files

- `design/MATHEMATICS.md`: constructions, inverses, contraction and sharing.
- `CODEX_TASK.md`: actual source integration and benchmark sequence.
- `design/RESOURCE_PLAN.md`: performance boundary and production/diagnostic split.
- `tests/structural_probe.cpp`: 624x1022 G and 562x1022 H1 finite models.
- `tests/operator_checks.cpp`: sparse operator vs independent chord adjoint,
  codec, dual, common-channel identities and 163-support correction checks.
- `src/sparse_coded_g.rs`: uncompiled Rust integration first pass.
- `src/minimal_support_transport.rs`: optional host map-generator draft.
- `src/source_inventory_gate.rs`: source legality draft for the REJECTED
  bit-affine candidate; retained to distinguish legality from joint coverage.
- `SOURCE_PINS.json`: exact inspected source revision and blob identities.
- `evidence/VERIFICATION.md`, `evidence/results.json`: scope and executed results.

No remote files were modified, no branch was pushed, and no protocol was
deployed by this review. The new profile is a candidate, not a release.
