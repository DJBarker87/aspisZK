# R15 actual-terminal R12 inverse bridge

Date: 2026-09-19. Branch: `research/v8-privacy-repair-20260913`.

## Result

The retained fixed R12 inverses now run against the actual compiled
pair-forest selected terminal, rather than only its extracted G factor.
For both cut 1 and cut 2, the test:

- derives eta after the actual initial claim;
- uses the actual compiler fixture, copy helper, and selected-terminal
  evaluator;
- checks that the lifted G correction preserves that initial claim and hence
  eta;
- checks every earlier selected-terminal round is unchanged;
- realizes both a compact basis target and a non-base arbitrary 27-coordinate
  target at the selected cut.

Command:

```sh
CARGO_BUILD_JOBS=1 cargo test --offline --release -p aspis-prover \
  --features insecure-spend-fixture --test r10_semantic_cut \
  r15_r12_inverse_hits_arbitrary_compact_targets_at_actual_selected_terminal \
  -- --nocapture
```

Exit status: 0. The focused test ran in 15.84 s after a 6.70 s optimized
incremental compile; no production paths were changed.

## Boundary

The test deliberately uses R14's named diagnostic public transcript entry.
It neither constructs C1/C2 roots nor applies the inverse through an actual
shared-oracle commitment history, actual q22 opening schedule, retry/stopping
path, or publication sink. It therefore proves a source-terminal algebraic
transport for this deterministic fixture, not a public-only simulator,
commitment hop, or full privacy statement.

The first remaining proposition on this positive path is to bind this
actual-terminal inverse to the source's complete paired C1/C2 commitment and
shared oracle chronology, including the real C2 entry bytes and later q22
queries. The R15 source-slice audit independently shows that the archived
q22 performance source is not yet a coherent transformed source closure.
