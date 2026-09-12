# Replayable collector source through later relation coins — 2026-09-12

`lean/ExtractionCollectorReplayableSource.lean` replaces the collector's
previous `.pure (consume ...)` start with a compiled bounded script.  One
execution now constructs and returns the literal submitted body, both OOD
points, gamma, kappa, tau, alpha0, the q22 schedule, rho and the three later
relation challenges.  Gamma, alpha0 and alpha1–alpha3 are therefore record
projections, not labels supplied separately to the collector.

The script preserves canonical/source-work abort as V7
`controllerRefused`.  Prefix, middle and later sampler failures are returned
and classified as rejections; they are not discarded.  The same-execution
theorem decomposes a successful run at its actual post-gamma, post-rho and
post-alpha3 states.

Checker acceptance currently means only that this source script returned its
`Record` through the three later relation responses and challenges.  It does
**not** mean terminal relation acceptance, payment acceptance, successful
extraction, or `Progress`.  `SameBodyRelation.consume` still needs the actual
causal strategy, ordinary scalar and authenticated query-increment arithmetic;
none is manufactured here from a successful record.

## Focused evidence

- Base revision: `4455c1904eecd52dceaf495a9ac7ceac48139485`
- Toolchain: Lean 4.32.0, commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- Command: capped single-file Lean compilation on the NUC with
  `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`, `-j1 -M8192`
- Exit: 0
- Wall time: 3.20 seconds
- Peak RSS: 6,599,148 KiB
- Swap: 0
- Source SHA-256:
  `aedc7e695f7d83d15e6bb8126197566240f9e0a66f70f515c1ea8a7388587b01`
- Olean SHA-256:
  `c2e8b0f42ddea93d33487173b5f90bf5edb2e13043e8b11d3c7a88e6a07e851c`
- Axioms: `propext`, `Classical.choice`, `Quot.sound`

No protocol, wire-format, probability, CU, or production-acceptance claim is
made by this milestone.
