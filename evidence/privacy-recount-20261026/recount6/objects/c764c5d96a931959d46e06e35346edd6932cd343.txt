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

Fresh budget **100/100 Lean**: **85 passed / 15 failed**; **0 Kani**.
IDs **44200–44299**, unique; no admission refusals and no unchanged failing
source/environment replay. Each failed candidate is retained in its numbered
source snapshot and receipt. The Option-returning validation suffix shape is
now recognized by the generator and proved by symbolic Result/Option cases,
without unfolding either recursive validation loop.

`receipt-index.json` records every exact target, exit status, wall time, peak
RSS, swap, source revision/hash, dependency fingerprint and full axioms output.
All scopes were sequential, 6G/8G/swap0, TasksMax64, Lean -M7000.

Final audit revision: `f3e613f7f86ca8515bd22d7182617ead947aaa8f`.
Target prefix `R1Z/PV_RE_`:

| Target / ID | Exit | Wall | Peak RSS KiB | Swap | Axioms reports |
|---|---:|---|---:|---:|---:|
| ResumeAuditA / 44297 | 0 | 0:01.24 | 2633244 | 0 | 226 |
| ResumeAuditB / 44298 | 0 | 0:01.20 | 2582632 | 0 | 175 |
| ResumeCombinedAudit / 44299 | 0 | 0:01.91 | 4235568 | 0 | 402 |

All 401 retained resume declarations plus the existing headline have only
standard axioms. The combined log also prints the full outer-control theorem
signatures. This is a focused audit against retained objects, **not a clean
release manifest replay**. All retained source bytes have a matching green
receipt; source hashes and audit receipts are frozen in `new-source-pins.json`,
`pre-audit-source-check.json` and `final-audits.json`. Generator checks pass. `whitespace-check.json` records trailing spaces in two
checked declaration lines and retained historical transcripts; their exact
bytes are preserved.

The uncompiled `PV_RE_Continue063`, `PV_RE_Continue064`, and
`PV_RE_RetryTerminal` drafts remain under the job's tools directory and are
excluded from the audited theory. No credit is taken for them.

No shipped code, endpoint/simE/observer source, shared env-J source, sibling
worktree, wallet or key was changed. The four extracted candidate source
hashes remain equal to the inherited pins. Private object scratch was hashed
and removed after auditing; sources and all receipts remain. No push/merge.

Stopped on **fresh Lean budget exhaustion**, not a failed candidate or checked
source counterexample. The next concrete deliverable is a callback-invocation
trace semantics/refinement through the retained attempt suffixes, including
failure/divergence prefixes, composed with `whole_client`; then finite-set
membership and per-entry exclusion for each fixture, with actual native
association non-vacuity. See `next-obligation.md`.

Resume commit log before the final evidence commit: `commits-before-final.txt`.
The prior report is retained in `prior-final-report.md`.
