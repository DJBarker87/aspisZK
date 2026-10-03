# R537: preserved privacy-construction negatives

This evidence package preserves two restricted synthetic-prefix diagnostics.
It is not a privacy proof, a published-view incompatibility result, a witness
leak, or a probability statement.

## 1. Sequential C1/H1/G construction

The first diagnostic used a synthetic input with `z=0`, alpha zero,
gamma/kappa/tau one, two accepted OOD parameters, query indices 0 through 21,
and beta retained from an unrelated honest run. It was intentionally not a
consistent Fiat--Shamir transcript. It first found C1 affine compatibility for
all 16 columns and then compatibility for the extended H1 system. Its later
626-row G solve had two nonzero residual rows. The recorded left-kernel
certificate has coefficients -1 at semantic row 0 and +1 at point row 361,
and the recorded certificate RHS is nonzero.

This establishes only that the sequential C1/H1/G correction construction did
not supply a full correction for that synthetic prefix. The H1 step adds
ordinary-relation and per-channel final constraints before G, so it can be
stronger than the combined published constraints. The exact sequential source
snapshots are missing; the accompanying `MISSING_SNAPSHOTS.md` records why this is not an exact-source verified milestone.

## 2. Per-column initial-mask-preserving C1 construction

The follow-up changed only C1 by appending four initial-mask equations per
column and forcing each column's initial-mask contribution to zero. In the
same synthetic prefix, column 0 has 112 equations, 221 variables, rank 96,
and one incompatible residual: added row 108 is an all-zero row with RHS
`p-1`. Its exact C1 source snapshots are present and checksummed.

This establishes incompatibility only for that selected per-column support and
stronger per-column zero target. It does not rule out cancellation between
columns or any full joint correction.

## Evidence and history

The package retains all locally saved setup/build logs and negative run logs,
the C1 and G certificates, format descriptions, and the original status note.
The initial output-path and missing-audit-variable invocations are described in
the status note, but no separate local raw logs for them were found. Exact
source/receipt gaps are not filled by inference.

No verifier source, security parameter, CU result, privacy theorem, or
security claim changed. The next task is a faithful full published-view joint
model with shared oracle, seed/retry/stopping/publication behavior and a
universal compatibility or incompatibility argument.

Source context: frozen R117 revision `6677d5f1310ff7373301fbd79f186278f772e68a`; campaign parent `5dff53d0e8f7e52289d21c4f0749d8cd0f17c14b`. Evidence is under `evidence/r537-privacy-construction-negatives/`. Complete Lean axiom output is not applicable: these are Rust diagnostics and finite matrix certificates, not Lean theorems. The recorded status and raw logs are preserved verbatim, including the documented missing sequential source snapshots.

The next focused experiment chooses jointly among the original 108-row C1 solutions to preserve the total initial claim, then runs the existing H1/G checks. A successful example would still not prove universal compatibility or whole-view privacy.

Receipt recovery: the matching NUC final build logs were recovered after the first archival commit. They agree with the status-recorded resource figures; the initially packaged build3/build4 logs were earlier builds. No diagnostic was rerun.
