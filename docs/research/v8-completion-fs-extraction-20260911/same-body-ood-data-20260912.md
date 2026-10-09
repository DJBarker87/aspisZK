# Same-body OOD data construction — 2026-09-12

`lean/SameBodyOODData.lean` removes a caller-supplied algebraic interface from
the repaired relation path.  Given one sampled OOD pair, the live gamma value,
and one submitted body, `fromSampled` now:

1. canonically decodes both circle-point coordinates;
2. parses the body's 697 canonical fixed QM31 fields once;
3. selects fixed-field indices 359 through 416, intended to be the two
   sequential 29-lane OOD answer rows;
4. chooses the same nonconstant chord coordinate as `OODInterpolant.Data`;
5. computes its inverse through `qm31TryInv`; and
6. returns `none` on every coordinate, body, or inverse failure.

The checked theorem proves that every successful result satisfies the actual
interpolant inverse equation.  Separate theorems expose canonical body parsing,
the exact answer-row producer, and preservation of the live gamma.  No caller
supplies `Data.Checked`, the answer rows, or an inverse.

This is a deterministic source-shaped constructor, not yet the complete
chronological connection.  The sampler-to-decodable-coordinate bridge, a
source/Rust proof of the row offsets and unreachable `getD` fallback, the live
gamma challenge coupling, literal Rust parser/inversion refinement, relation
terminal, payment extraction, and Fiat–Shamir probability theorem remain open.

## Focused evidence

- Base revision: `66400a885c8426897200d74aa396b15385717086`
- Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- Command: focused `lean -j1 -M8192 -o /tmp/SameBodyOODData.olean`
  under `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`,
  `RuntimeMaxSec=600`
- Exit: 0
- Wall time: 3.32 seconds
- Peak RSS: 6,571,900 KiB
- Swap: 0
- Source SHA-256:
  `09953f353a89367773f9d3f2906c7a27faf20180ec53b85a388fa96be57df192`
- Olean SHA-256:
  `db0f6a97564848b7f03409e3c54c07e5a3b074bb63e73a2a7a813f0b813056a9`
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
