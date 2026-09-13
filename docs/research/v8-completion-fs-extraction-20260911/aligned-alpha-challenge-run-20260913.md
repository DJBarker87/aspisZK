# Complete aligned ordinary-alpha challenge run

Date: 2026-09-13

This milestone closes the deterministic fresh/cache history bridge for one
successful live ordinary `alpha0` challenge.  It does not close the exact-root
or probability coupling.

## Constructed execution

The five focused leaves are:

- `lean/FSV8AlphaHistoryPhasePrefix.lean`;
- `lean/FSV8CandidateOriginTrace.lean`;
- `lean/FSV8AlignedAlphaSqueezeStep.lean`;
- `lean/FSV8AlphaChallengeDecoderBridge.lean`;
- `lean/FSV8AlignedAlphaChallengeRun.lean`.

`successful_live_challenge_constructs_aligned_run` starts from an actual live
`challenge tape start` success, its source `SqueezePath`, a V7 state aligned at
the already-constructed marker cut, and worst-case room for four two-query
pairs.  It constructs the complete one-to-four-pair V7 run.  Every proper
candidate prefix is rejected by the deployed decoder using prefix minimality;
the last candidate is accepted; and the literal V7 history recognizer reaches
`inactive` after the final advance query.

Each pair contains both actual `queryOracle` equations, exact two-record
history appends, successor-state alignment, and a constructed fresh-or-cached
classification.  The advance runs from the post-output state while retaining
the pre-pair digest, matching the source `squeeze` convention.  No transcript,
candidate block, answer, or alternate body is selected retrospectively.

The finite projected log cannot supply this result by inversion because it
erases actor identity and conflates cached/programmed provenance.  The proof
therefore executes the V7 queries forward.  A superseded draft attempting the
lossy inverse route was deleted rather than retained as evidence.

## Evidence

The focused Lean 4.32.0 runs are recorded in
`../../../results/v8-completion-fs-extraction-20260911/aligned-alpha-challenge-run-v1/report.json`.
All five leaves compiled with exit status zero.  The promoted endpoint's axiom
list is exactly `propext`, `Classical.choice`, and `Quot.sound`; there is no
`sorryAx` or custom axiom.

A hostile theorem review found the endpoint substantive and non-circular for
this deterministic scope.  In particular, the successful endpoint derives
proper-prefix rejection from the actual successful decoder path rather than
taking it as a top-level conclusion-shaped assumption.

## Boundaries that remain open

- The initial `StateAligned` and marker prefix must still be constructed at
  the exact whole-verifier/root cut, including the parsed body nonce.
- The `+8` total/fresh/tape room conditions are conservative.  Total coverage
  needs a source cap invariant or a disposition-sensitive relaxation.
- `StateAligned` excludes programmed entries.  Restored/programmed extraction
  runs require their own alignment construction.
- Preferred scheduler coordinates, target occurrence, and the exact-root
  controller are not connected by this theorem.
- It proves no random-oracle law, sampler probability, Fiat--Shamir bound,
  literal Rust refinement, or global soundness claim.

The next source theorem should construct the aligned marker start from the
same parsed body and executable pre-alpha factorization, then connect the
resulting full challenge run to the exact root scheduler/controller.
