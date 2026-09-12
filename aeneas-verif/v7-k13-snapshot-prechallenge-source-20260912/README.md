# V7 Tag-73 prechallenge snapshot source extraction

Pinned source revision: `ccc19c1cecfaf2526edd3d3a5277c7b54b0a77bf`.

This focused Aeneas extraction targets the default-off
`snapshot_prechallenge` helper used by the atomic Tag-73 observer.  It proves
only the concrete verifier calculation at the pre-query cut; it does **not**
claim arbitrary-prover random-oracle causality.

The translated helper computes the terminal discrepancy from the borrowed
weight accumulator and the first four final coefficients.  Its sole local
Aspis opaque dependency is `WeightAccumulator::weight_at`, whose separately
translated source artifact is frozen in
`aeneas-verif/v7-k13-weight-at-source-20260912`.

The generated Lean files require the pinned Aeneas Lean backend (Lean 4.31);
the V7 formal tree presently uses Lean 4.32, so this artifact is extraction
evidence rather than a completed integrated Lean replay.  The version gap is
recorded explicitly rather than bridged by an unchecked compatibility claim.

## Extraction evidence

- Charon 0.1.223
- Aeneas `d860ac47-tag73-variantfn-namespace-arrayfix-r1`
- Aeneas translation: exit 0, 187.40 s, peak RSS 1,776,892 KiB, zero swap
- Raw LLBC SHA-256:
  `c70b00a3e34d4cc99a7455d49d933ce2f4c3ec1a12cca0b4fcf4577edb6f2318`

The generated template deliberately remains a template until all external
library models and the separately translated `weight_at` namespace are linked
under the matching backend.
