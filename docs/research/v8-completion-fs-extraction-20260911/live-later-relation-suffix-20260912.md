# Live later-relation suffix — 2026-09-12

`lean/FSLiveLaterRelationSuffix.lean` extends the chronological selected
source trace from rho through the three later relation responses and their
three sequential, zero-permitted alpha challenges.  Each response is read
from the same canonical fixed-field body range before its corresponding
challenge is sampled.  A successful trace constructs the exact `Fin 3` coin
vector consumed by the algebraic relation model; no later coin is supplied by
the caller.

The verifier-derived query increment is retained as an explicit
`IncrementProducer` boundary.  Its type makes it depend on the authenticated
OOD result, gamma, completed query/rho record and body, but this milestone does
not prove that its bytes equal the pinned Rust arithmetic.  Candidate failure
and exhaustion at alpha1, alpha2 or alpha3 remain represented, with exact
final transcript state.

This leaf ends at the complete terminal *input* boundary.  It does not call
`SameBodyRelation.consume`, assume `terminalZero`, or establish terminal
relation/payment acceptance, probability, freshness, or literal Rust
refinement.

## Focused evidence

- Base revision: `64ebf012c5371d1c6c29c057b4c149d6c1d58fbb`
- Toolchain: Lean 4.32.0, commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- Command: capped single-file Lean compilation on the NUC with
  `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`, `-j1 -M8192`
- Exit: 0
- Wall time: 4.02 seconds
- Peak RSS: 6,599,352 KiB
- Swap: 0
- Source SHA-256:
  `c2a64e09622d629d2fefe36256e37bf96ca5e7ac5d72d16d906d70380ec773f9`
- Olean SHA-256:
  `e95081ebdd5863c61912d787bb1c5cf1c879610e579735072eacd829d2508f28`
- Axioms: `propext`, `Classical.choice`, `Quot.sound`

No protocol, wire-format, security, CU, or production-acceptance change is
made by this milestone.
