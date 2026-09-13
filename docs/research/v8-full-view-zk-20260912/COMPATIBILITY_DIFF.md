# R6 compatibility diff

Date: 2026-09-13.

This branch does not change the production V8 prover, verifier, proof format,
or public statement. It adds research-only diagnostics, exact algebraic gates,
generic formal results, and a fail-closed publication-boundary prototype.

## Unchanged protocol surface

- Verifier acceptance language and verifier entry points.
- Proof grammar, serialized proof bytes, transcript framing, hash domains and
  Fiat--Shamir sampling.
- Public statement, account inputs, commitments and emitted public events.
- Existing mask inventory, balancing relation, seed derivation and shared C1/C2
  leaf-salt convention.
- The 40,282-byte proof-account cap.
- Production retry, publication and proof-account write paths. No new gate is
  wired into a generated prover or a deployment target.

No deployment, transaction, wallet/key operation, SBF build, Aeneas replay or
generated-certificate aggregation was performed.

## Research surface added

- Source-locked Rust regressions for the q4/q6 raw separator and a same-public
  duplicate-input witness pair with actual mask application.
- An exact finite-field certifier returning either a simultaneous correction
  or a checked left-kernel separator. The fixed spread schedule passes raw
  coverage; the scattered schedule containing fibres 4 and 6 fails it.
- A fixed-affine public-coset representative and witness-free simulator, with
  fail-closed checks for a missing or invalid public quotient.
- A research-only immutable candidate/review/publication API. Its production
  review function never issues a permit because complete full-view coverage is
  unsupported. It therefore demonstrates enforcement shape, not a useful
  adapter and not a production repair.
- Lean results for the affine public-coset construction, release-event
  transport, and a non-IID conditional retry-failure bound.
- Research-only source regressions deriving the literal 136-edge H1 incidence
  layout, the full 1024-row duplicate-selection helper delta, the actual-encoder
  fixed-observation corrections, coordinatewise C2 lift, and exact 84/87 point
  projection.
- Lean results for finite transport, graph incidence, nonlinear-coefficient
  fresh padding, triangular reuse of one pad, point projection, and the
  conditional source-shaped fixed helper observation.
- A staged evidence ledger that keeps raw diagnostics, joint-view coverage,
  simulator construction, and retry/publication proof separate.

## Consequence

The compatibility surface is preserved because the branch changes no
production protocol path. That also means it does not repair the live q22
path. Wiring the current reject-all prototype would preserve confidentiality
by publishing nothing, but would have release probability zero and is not an
acceptable operational repair.
