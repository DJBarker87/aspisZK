# Operational provenance through the extraction matrix

Status: checked deterministic provenance milestone; matrix availability,
shared-prefix causality, extraction and global Fiat--Shamir soundness remain
open.

## Result

`lean/ExtractionCollectorVerifiedMatrix.lean` prevents the generic matrix
collector from erasing why a selected cell exists.  A `CheckedCell` contains:

- its exact `OriginReplayConfiguration`;
- the body returned by the replay;
- the dependent record accepted from that body; and
- the equality showing that `verifiedSourceAttempt` produced that checked
  outcome.

`verifiedAttempt` constructs the cell by dependent matching on the actual
attempt result.  Replay failure, verifier oracle abort, verifier timeout,
source rejection and source resource failure remain distinct outcomes.

Consequently `matrix_cell_constructs_functional_run` proves that every cell
selected by a `CompleteMatrix` constructs its own operational replay and the
same-body functional rerun from the preceding milestone.  It does not recover
that provenance by trusting a bare parsed record or a separately supplied
semantic program.

## Boundary

This theorem does not prove that a bounded attempt list contains all 116
requested cells.  It also does not prove that the four cells in one row share
one chronological pre-alpha history.  In particular, equality of parsed
`kappa`, `tau` or response0 values would not establish that history property.
Fold correctness, terminal acceptance and checked payment extraction are
unchanged open gates.

The functional rerun still takes the transcript's `initialDigest` explicitly.
This work does not add a digest-to-oracle-state invariant; the digest is an
external verifier input at this boundary.

## Focused evidence

Lean 4.32.0 with the pinned union cache, `-j1 -M7500`:

- target: `ExtractionCollectorVerifiedMatrix.lean`;
- exit code: 0;
- wall time: 4.61 seconds;
- peak RSS: 5,833,392,128 bytes;
- swaps: 0;
- printed axioms: `propext`, `Classical.choice`, `Quot.sound` only.

This was a focused cached compile, not a clean first-party dependency rebuild.
Global security bits remain unset and grinding contributes zero.
