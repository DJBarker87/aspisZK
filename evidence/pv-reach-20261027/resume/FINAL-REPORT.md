# pv-reach resume final report

Branch `codex/pv-reach-20261027`; resume base `eb627aa1d8`.
Worktree exactly `/Users/dominic/ZK/.worktrees/pv-reach`.
**Target not yet established. V404 OPEN → OPEN; V405 OPEN → OPEN.**
Neither row is claimed closed. No endpoint premise or deployment condition
is removed, added, weakened or changed. T retains its three existing fields.

## Exact proved result

`PV_RE_ContinuationRetry.whole_client` composes the proof-account client,
its actual op233 call with every outcome, all eight possible retry positions,
and the actual op226 call followed by the named full attempt continuation.
`PV_RE_ShapeControl.transfer` and `.withdrawal` specialize this Result
identity to each public constructor. They have no added Prop hypotheses.
All entropy, attempt, failure, divergence, rejection and exhausted-cap branches
remain in the expression. Source bodies are symbolic; no whole-run kernel
normalization is used.

`PV_RE_RetryCongruence.congr_at` proves continuation locality at the incremented
counter. All of its increment/continuation hypotheses are instantiated in
`PV_RE_FiniteRetry.at0` through `.at8`. The formerly failing irreducible cap
proof is replaced by `PV_RE_CapValue.cap_value`; the eight tiny counter
increments are proved with named bitvector identities. The older failed
candidates and every new failed candidate remain as evidence.

The named source suffixes and their guarded success/failure/divergence
transitions are listed in `continuation-manifest.json`. These are source
control equations, not native source refinement or execution witnesses.
`PV_RE_RetryOutcomes` exposes exact local terminal and
rejection transitions; their guards are not instantiated on native fixtures.

## Requested obligations and native boundary

1. Complete dictionary callback-membership theorem for each fixture shape:
   **not proved**. The complete outer control equation is proved, but the
   actual invocation-trace refinement through every attempt suffix is missing.
2. Exclusion for each dictionary entry outside the reached set:
   **not proved**. Reached sets remain unresolved for both fixtures;
   universally excluded dictionary entries: **none proved**.
3. Native fixture non-vacuity: **not proved**. No arbitrary abstract Input,
   public constructor, dictionary or compiler result is used as a native
   fixture witness.

`native-boundary.md` states all boundaries. Compiler success, actual returned
public/records association, external and records association, native ordered
effects and deployed-caller association remain V163/V167 P obligations.
The optional local outcome guards are ordinary source hypotheses, not named
native associations; they earn no row closure. No fact is moved into T.

## Validation and stop

Receipts, final audit results and stop accounting will be populated after the
remaining sequential focused checks and three reserved audit attempts.
