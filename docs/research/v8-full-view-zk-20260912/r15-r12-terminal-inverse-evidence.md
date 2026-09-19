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
- checks all 27 scaled compact basis directions and one non-base target
  with separately varied values in all four QM31 limbs at each selected cut
  (56 target checks in total). This is not a universal arbitrary-target proof.

Command:

```sh
CARGO_BUILD_JOBS=1 cargo test --offline --release -p aspis-prover \
  --features insecure-spend-fixture --test r10_semantic_cut \
  r15_r12_inverse_hits_arbitrary_compact_targets_at_actual_selected_terminal \
  -- --nocapture
```

Initial two-target-per-cut run: exit 0, 15.84 s test plus 6.70 s compile.
Expanded all-basis run on starting revision
`0107b6531018948499703f740397d4fa18adfa06` plus this test change: exit 0,
51.57 s test, 56.47 s total wall, peak RSS 167,821,312 bytes, swaps 0,
measured with `/usr/bin/time -l`. Fixed G-zero offsets are cached once per
round; no production paths changed. No Lean compilation/axioms claim is made
for this Rust fixture check.

## Boundary

The test deliberately uses R14's named diagnostic public transcript entry.
It neither constructs C1/C2 roots nor applies the inverse through an actual
shared-oracle commitment history, actual q22 opening schedule, retry/stopping
path, or publication sink. It therefore tests a source-terminal algebraic
transport for this deterministic fixture, not a universal transport theorem, public-only simulator,
commitment hop, or full privacy statement.

The first remaining proposition on this positive path is to bind this
actual-terminal inverse to the source's complete paired C1/C2 commitment and
shared oracle chronology, including the real C2 entry bytes and later q22
queries. The R15 source-slice audit now reconstructs the exact pinned q22
performance source; the complete generated closure and entropy-backed adapter
remain separate obligations.
