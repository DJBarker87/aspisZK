# pv-reach final report

Branch `codex/pv-reach-20261027`; base `aa27e73f99`. Worktree unchanged.
**Target not yet established. V404 OPEN → OPEN; V405 OPEN → OPEN.**
No endpoint premise or deployment condition was removed, added, weakened or
changed. T retains exactly its existing three fields.

For transfer and withdrawal, **complete reached sets remain unresolved;
universally excluded callback entries: none proved**. No static dependency
path or first-bind equality is credited as a complete execution witness.

Proved over the extracted ProverRwFull definitions: symbolic first-bind
identities for the proof-account op233 entry and entered-attempt op226 entry;
38 direct-callback boundaries, 36 callee boundaries, ten exact named branch
decompositions, and the retry cap/entropy split. The source bodies remain
symbolic. These are local extracted equations, not native source refinement,
fixture admission, trace completeness, or whole-caller privacy.

`PV_RE_AttemptEntry.failure` proves truncation after a failing op226. Its
hypothesis is not instantiated on either selected native fixture, so it earns
no universal fixture exclusion. No other new Prop hypothesis is introduced
by the retained equations. The exact compiler-success/native-public
association types and unmet fixture non-vacuity obligations are in
`native-boundary.md`. V163/V167 remain unchanged; no native fact is moved to T.
Two numeral-specific retry proofs failed to unfold the irreducible cap and
remain only in `tools/pv-reach-20261027/drafts/`, outside the audited theory.

Lean **100/100**, **90 passed / 10 failed**; Kani **0**. Allocated IDs
44000–44100; 44002 was refused before compilation. All scopes were sequential,
6G/8G/swap0, TasksMax64, Lean -M7000. Occupied pv-canon IDs were avoided.
`receipt-index.json` contains every target, exit, exact source hash/revision
qualification, wall, RSS, swap and complete axioms report. Attempt 44005 was
an erroneous unchanged import-failure repeat; `process-deviation.json`
records it without credit.

Final audits (revision `fcd0358000`; target names have prefix `R1Z/PV_RE_`):

| Target / ID | Exit | Wall | Peak RSS KiB | Swap | Axioms reports |
|---|---:|---|---:|---:|---:|
| AuditA / 44098 | 0 | 0:01.06 | 2628332 | 0 | 42 |
| AuditB / 44099 | 0 | 0:01.12 | 2630336 | 0 | 67 |
| CombinedAudit / 44100 | 0 | 0:01.71 | 4225912 | 0 | 110 |

All 109 retained declarations plus the existing headline print standard
axioms only. This reuses retained objects; it is not a clean release replay.
Generators pass `--check`. No shipped code, endpoint/simE/observer source,
shared env-J source, sibling worktree or key was changed. Owned object scratch
was removed after hashing; receipts and sources remain.

Stopped on budget exhaustion. Next deliverable: a control-flow/trace
refinement composing the continuations across all eight retry positions,
then complete fixture membership/exclusion theorems with the actual native
compiler/public association instantiated on both fixtures.

Pre-final commit log: `commits-before-final.txt`.
