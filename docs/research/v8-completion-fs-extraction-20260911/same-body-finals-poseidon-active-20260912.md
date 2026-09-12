# Same-body chronology, replay finals, and active Poseidon rows

Status: focused deterministic milestone; global soundness remains open.

## What is now constructed

`FSAuthenticatedInterleavedPrefixMiddle` composes the source/OOD/gamma
prefix, the fail-closed functional middle, and the authenticated q22 suffix
without fabricating an intermediate digest.  A successful staged run exposes
the exact prefix-middle and suffix executions.  Its new
`successful_suffixContinuation_components` theorem derives the valid q22
schedule and the actual successful interleaved suffix; it does not accept an
independent suffix execution.

`ExtractionCollectorSuccessfulReplay.parsed_body_roots_equal_cuts` now starts
from one successful staged replay and initial log consistency.  It follows
that same run through the schedule, selected q22 Merkle calls, parser and both
root checks.  The older draft accepted independent positions, suffix tape,
suffix oracle, trace and suffix-success premises; hostile review rejected that
interface and those premises are absent from the retained theorem.

`ExtractionCollectorFinalMatrix` parses each supplied `.checked` replay
record's own submitted body and derives its final-256 values from fixed fields
441 through 696.  It
does not accept a caller-supplied final polynomial, witness, full oracle, or
`RecoveredHigh` object.

Each replay deliberately carries its own full body.  Forks must share the
authenticated commitment prefix but may contain challenge-dependent suffix
messages.  An earlier draft incorrectly indexed all 116 records by one whole
body; that interface was rejected before commit.  The current matrix bridge
does not yet construct the shared-prefix property or the replay records.

The matrix now also constructs the value-keyed four-alpha nodes and the
29-gamma interpolation nodes, with exact one-hot lookup and nodal
reconstruction lemmas.  These are deterministic interpolation adapters only:
`CompleteMatrix` still does not prove that its supplied `.checked` records were
produced by the permitted replay collector, and verifier acceptance has not
yet been shown to imply the per-cell fold-correctness premise needed to recover
the true quotient.

The Poseidon leaves and source callback composition establish:

- generic width-16 polynomial degree propagation and the selected degree-27
  weighted residual ceiling;
- exact Boolean restriction of block, selector, and three trace views;
- the eleven active selector classes and their leading/full/internal weights;
- exact source-evaluator predictions for the active classes; and
- `baseCoordinate_active`, equating every active Boolean callback coordinate
  with the literal selected `pairResidual`; and
- zero classification for inactive blocks and selector rows, followed by the
  exact selected four-coordinate tower packing on every Boolean row.
- a combined callback whose Poseidon, semantic and Copy lanes are evaluated by
  their actual chronological source expressions, with exact Boolean
  restriction and masked assembly identities.

These are mathematical/source-evaluator identities.  They deliberately do not
identify the source evaluators with the old off-domain Boolean-table MLEs.
Complete terminal-success classification and literal optimized Rust/Aeneas
refinement remain open.

## Permitted-extraction boundary found by hostile review

The canonical injective-label adapters are now constructed.  The next missing
implication is substantive rather than indexing: each selected successful
replay must either supply the exact fold of one shared quotient at its alpha
node or enter an explicitly charged relation/query failure event.  Only then
can `SelectedMiddleFourAlpha.Generic.reconstruct_folds` identify each gamma
row, followed by 29-gamma reconstruction of the tuple.

The collector must additionally construct all records from legal replays
sharing the chronological commitment prefix while allowing later body bytes
to vary.  `CompleteMatrix` alone does not establish this, and a mathematical
matrix does not establish a resource-bounded rewind strategy.

No interpolation, payment witness, extraction-success probability, or global
soundness conclusion is claimed by this checkpoint.

## Focused evidence

The Poseidon prerequisites were checked on the NUC under the recorded cgroup
limits.  The new callback, replay, suffix and interpolation leaves were checked
with Lean 4.32.0 on the laptop against the pinned dependency union after
rebuilding the smallest incompatible first-party dependencies from source.
Printed promoted declarations use only `propext`, `Classical.choice`, and
`Quot.sound`.

The exact hashes and measurements are recorded in
`results/v8-completion-fs-extraction-20260911/same-body-finals-poseidon-active-v1/report.json`.
The pinned union cache is not a clean first-party dependency rebuild.

## Security implication

This checkpoint removes three conclusion-shaped inputs: a free replay-final
projection, a generic active Poseidon callback, and an independently supplied
authentication suffix for the same-body root theorem.  It does not yet prove
that the permitted replay strategy supplies a complete fold-correct
reconstruction matrix, that the recovered coefficients yield a checked
payment witness, or that the adaptive Fiat-Shamir execution realizes the ideal
laws.  Consequently the global failure term and global security bits remain
unestablished.
