# R6 final handoff

Date: 2026-09-13.

Outcome: **(b) exact irreducible missing theorem isolated; no full-view privacy
repair or release claim**.

The branch supplies source-locked negative regressions, an exact raw affine
certifier, a fixed-affine public-coset simulator, a fail-closed publication
prototype, and generic stopping/retry theorems. These are deliberately
separate layers. Passing raw joint linear coverage for one schedule is not a
full chronological coupling; the affine simulator is not a V8 simulator; the
publication prototype is reject-all; and the retry theorem has no positive
source-specific release premise.

## Exact obstruction

The first irreducible source obligation is a public causal law or coupling for
H1/C2 and its semantic messages conditioned on the already committed C1
history. In the selected path H1 is derived from the unmasked semantic trace
and transcript challenges after C1; the copy-logup helper includes inversions
and rational witness dependence; C2 then commits that result. The existing
affine C1 correction certificate neither supplies this nonlinear conditional
law nor a public quotient for it.

Without that theorem there is no complete joint source adapter, no
statement/history-only simulator, no useful full-view permit, and no positive
per-history release lower bound. Assigning any corresponding loss term zero
would be unsupported. The current publication prototype correctly returns
`CompleteFullViewCoverageUnsupported`, giving release probability zero and
exhaustion probability one for every finite retry cap.

## R6 focused validation

Validation revision: `7235d022d2d84c9dd06e7867f52fcc03cd9f3b6a`.

- `cargo test --offline -p aspis-prover --release --lib v8_privacy -- --nocapture`:
  exit 0; 11 passed; test time 0.15 s; wall 0.60 s; peak RSS 74,956,800
  bytes; swap 0.
- `cargo test --offline -p aspis-prover --release --lib diagnostic_same_public_duplicate_input_selection_pair -- --nocapture`:
  exit 0; 1 passed; test time 0.10 s; wall 0.40 s; peak RSS 74,891,264
  bytes; swap 0.
- The latest changed Lean leaves and aggregate passed at R5. Aggregate exit 0;
  wall 3.40 s; peak RSS 1,658,732,544 bytes; swap 0; `#print axioms`
  reported only `propext`, `Classical.choice`, and `Quot.sound`, with no
  `sorryAx`. They were not rerun unchanged at R6.

The exact next experiment and alternative protocol-level repair are specified
in `REMAINING_OBLIGATIONS.md`. `COMPATIBILITY_DIFF.md` records that no
production proof, verifier, transcript, public statement, byte cap, retry or
publication path changed.
