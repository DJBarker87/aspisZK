# Chronological authentication to Prepared scalar — 2026-09-12

`lean/SameBodyChronologicalPreparedScalar.lean` completes the deferred small
composition above `SameBodyChronologicalAuthentication`.

For one successful chronological C1/C2, replayable source, q22 schedule and
selected same-body Merkle run, it executes the real `prepare` function.  Its
result is total at this interface:

- `.error .openedPipeline` is retained as an explicit preparation failure; or
- the returned `Prepared` value is proved to contain the same body, typed q22
  schedule, data, alpha0 and rho, and its parsed wire and Merkle trace are
  proved equal to the same successful chronological Merkle run.

In the success branch, `ScalarOutcome` stores the two constructed prefix
answer facts, the two chronological prefix inclusions and the prepared
leaf/node-call inclusion. `ScalarOutcome.result` invokes the existing
`authenticated_scalar_or_failure` theorem, so it yields the exact shifted
authenticated scalar equation or the already defined authentication failure.
No opening equality or authentication premise is taken from the caller.

This does not construct OOD `Data`, execute `SameBodyRelation.consume`, prove
terminal/payment acceptance, refine literal Rust, or supply freshness,
probability or adversarial-ROM coupling.

## Focused evidence

- Base revision: `66400a885c8426897200d74aa396b15385717086`
- Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- Command: focused `lean -j1 -M8192` under `MemoryHigh=8G`,
  `MemoryMax=9G`, `MemorySwapMax=0`, `RuntimeMaxSec=600`
- Exit: 0
- Wall time: 2.85 seconds
- Peak RSS: 6,747,892 KiB
- Swap: 0
- Source SHA-256:
  `38f0b7edeca2eb2939796e89d41cacdd4c0efb029089244e68b990dabd80428b`
- Olean SHA-256:
  `a53582a7fd72dc2bde256a0e31b44b044d4b4b471a31ed2a630a03e09aa0b00a`
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
