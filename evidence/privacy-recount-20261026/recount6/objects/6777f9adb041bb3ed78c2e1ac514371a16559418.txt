# pv-reach2 continuation report (LOG D309)

Branch `codex/pv-reach-20261027`; worktree exactly
`/Users/dominic/ZK/.worktrees/pv-reach`; base `aee46ed9c5`.
**Target not yet established. V404 OPEN → OPEN; V405 OPEN → OPEN.**
No endpoint premise/deployment condition was removed, added, weakened or changed.
No T field was added. No shipped source, shared source/object, sibling worktree,
wallet or key changed. No push or merge.

## Definition comparison, completed before proofs

The requested exact Lean row definitions are absent: recount5 has null theorem,
closure_theorem and closure_route, and empty definition_witnesses/definition_witnesses5
for both rows. `row-definitions.json` preserves both complete records. The ledger,
ROWS5 and join4/join5 reports require actual execution reachability/exclusion.
Result dictionary congruence is **weaker**: invoked callbacks may leave no influence
on the returned Result. Invocation, minimality, ordering and native-effect/source
fidelity do not follow. `row-definition-match.md` was committed before proof work.
No instrumented trace semantics was introduced.

## What was checked, and its limits

`PV_RE_DictGenerator` constructs symbolic Eq proofs compositionally from immediate
callee congruences. Fixed-point functionals use congruence; monotonicity certificates
use proof irrelevance. It never evaluates recursive equations or complete runs.
An erased Payload type required a type-only definitional equality check. All six
failed candidates remain in numbered source snapshots and receipts.

`PV_RE_DictSuffix000`–`020` prove congruence of byte-preserving copies of each
named source suffix and of its original full source function, using an explicit
list of dictionary-field equality hypotheses. These plus their callees give
318 named congruences. `congruence-supports.json` records the support list for
every checked function/suffix; `suffix-manifest.json` connects all 74 prepared
targets to the original continuation manifest. Generator --check passes.
The support lists are semantic overapproximations, not actual invocation sets.

**S_transfer: not established. S_withdrawal: not established.**
Whole-client/shape congruence: not proved. Per-entry whole-shape exclusions: none.
Actual fixture admitted-input non-vacuity: not proved. V163/V167 compile_call,
public/records/external associations and native ordered effects remain open.
No arbitrary abstract input was presented as the actual native fixture.

`PV_RE_RetryRestored` repackages the ten retained retry/control sources with only
import lines removed; it and suffixes 021–073 are UNCOMPILED. The next composition
source is explicitly a draft under tools/.../drafts/resume2/. No credit is taken.

## Mandatory provenance stop

After attempt 36932, verification found **18/236 authoritative library objects
mismatch**, including a direct import used by every receipt:

- AeneasMeta.Extensions expected
  `d4c7b9386b70ced61f8444bfba438bd29b20ce89ccd29edad3d32fb2c095e343`;
- observed `f582f735bdd4f965977df7350789248c45665874aa3c510699b9238732dff113`.

The selected path is
`/home/dombarker/project-offloads/codex-cx-import-union-20261022/objects/AeneasMeta/Extensions.olean`.
Current research has the same authoritative expected hash. All 18 expected/actual
pairs, paths and private-provider checks are in `library-object-verification.json`,
`library-pins-research.json`, `private-library-verification.json` and
`provenance-stop.json`. Ruling (h''') forbids library substitution/rebuild; this
worker did neither. The 27 passing checks describe the observed kernel environment,
**not a replay under the authoritative frozen library**. No release or row credit.
The pin check should have preceded compilation; this sequencing error is recorded.

This is a provenance gate, not a failed-candidate stop or a checked source
counterexample. Further compiles require the lead to reconcile the authorized
library pins/objects. All independent compile-free source preparation and handoff
work is complete. No launcher/build-infrastructure repair was attempted.

## Validation and receipts

**33/100 Lean charged: 27 passed, 6 failed; 67 unspent. 0 Kani.**
IDs 36900–36932 only; 36997–36999 reserved and unused. No refusal or unchanged
failed-input rerun. All scopes sequential, MemoryHigh6G/MemoryMax8G/swap0,
TasksMax64, Lean -M7000. Observed max RSS 2,736,852 KiB; swaps zero.
`receipt-index.json` contains each target, exit, wall, peak RSS, swap, revision,
source snapshot/hash, dependencies/fingerprint and full printed axioms. The 43
printed accepted-target axiom reports contain only standard axioms. The individual
318-helper audit and final three audit targets were NOT run after the provenance
stop. No final manifest replay is claimed.

The next deliverable is the lead's library-pin reconciliation, followed by
suffixes 021–073, retry/whole-client composition, both explicit finite support sets,
per-entry replacement corollaries, actual fixture hypothesis instantiation and the
reserved axioms audits. Detailed steps are in `next-deliverable.md`.
