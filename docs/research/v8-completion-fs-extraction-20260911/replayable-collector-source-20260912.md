# Replayable collector source through rho — 2026-09-12

`lean/ExtractionCollectorReplayableSource.lean` replaces the collector's
previous `.pure (consume ...)` start with a compiled bounded script.  One
execution now constructs and returns the literal submitted body, both OOD
points, gamma, kappa, tau, alpha0, the q22 schedule and rho.  Gamma and alpha0
are therefore record projections, not labels supplied separately to the
collector.

The script preserves canonical/source-work abort as V7
`controllerRefused`.  Prefix and middle sampler failures are returned and
classified as rejections; they are not discarded.  The same-execution theorem
decomposes a successful run at its actual post-gamma and post-rho states.

Checker acceptance currently means only that this source script returned its
`Record` through rho.  It does **not** mean terminal relation acceptance,
payment acceptance, successful extraction, or `Progress`.  The live source
model does not yet contain response1–response3 and their sequential alphas.
Consequently `SameBodyRelation.consume` cannot yet be invoked without taking
future coins from outside the execution.  That continuation and the terminal
relation/payment checker remain open.

## Focused evidence

- Base revision: `64ebf012c5371d1c6c29c057b4c149d6c1d58fbb`
- Toolchain: Lean 4.32.0, commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- Command: capped single-file Lean compilation on the NUC with
  `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`, `-j1 -M8192`
- Exit: 0
- Wall time: 3.36 seconds
- Peak RSS: 6,603,648 KiB
- Swap: 0
- Source SHA-256:
  `fae1b97cd0325470ed4a27451bb40dbab47af3bfe5a7e5e6ec99b87a32dcf018`
- Olean SHA-256:
  `a4ce27987058d854246862fb5537c8a2e058a1b88527d563ae770e652b43eaf6`
- Axioms: `propext`, `Classical.choice`, `Quot.sound`

No protocol, wire-format, probability, CU, or production-acceptance claim is
made by this milestone.
