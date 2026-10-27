from pathlib import Path
import json,collections
P=Path(__file__).resolve().parent;root=P.parents[2];ledger=root/'design/PRIVACY-LEDGER-20261026.md';rows=json.loads((P/'rows3.json').read_text());t=json.loads((P/'totals3.json').read_text())['recount3_all'];old=json.loads((P.parent/'recount2/totals2.json').read_text())['recount2_all']
s='''

## Recount 3 2026-10-27 (B)

**Target not yet established.** This statement/dependency audit removes no
endpoint premise. The original ledger rows and both previous recounts remain
intact. [Every row, dependency and import disposition](../evidence/privacy-recount-20261026/ROWS3.md),
[method and corrections to D209–D235](../evidence/privacy-recount-20261026/recount3/METHOD3.md),
[immutable branch pins](../evidence/privacy-recount-20261026/recount3/pins.json),
[machine-readable rows](../evidence/privacy-recount-20261026/recount3/rows3.json),
[import chains](../evidence/privacy-recount-20261026/recount3/import-closures.json),
and [20 statement-check receipts](../evidence/privacy-recount-20261026/recount3/receipts.json)
are the evidence of record. No proof, theorem, implementation, observer,
simulator, bad-event definition or release pin was changed.

The denominator grows by four explicitly tracked P rows: V403 canonical M31
domain at op121 callers, V404 transfer reachability, V405 withdrawal
reachability, V406 owner adoption of the proposed three-field T. These are
slices/decisions with recorded overlaps, not four independent security gates.
**V240/op223 is V164's remaining P_source_p6; it is linked, never counted twice.**
The proposed T is not accepted trust: the original T/P/C classes stay intact.

| Inventory / status | Recount 1 | Recount 2 | Recount 3 |
|---|---:|---:|---:|
| Rows | 400 | 403 | 407 |
| T | 26 | 26 | 26 |
| P | 370 | 372 | 376 |
| C | 4 | 5 | 5 |
| OPEN | 138 | 110 | 103 |
| REDUCED | 152 | 154 | 176 |
| EVIDENCED | 10 | 12 | 14 |
| CLOSED-ON-RESEARCH | 87 | 87 | 87 |
| CLOSED-ON-CANDIDATE | 13 | 40 | 27 |

On the **same inherited 403 rows**, recount 3 is OPEN 99, REDUCED 176,
EVIDENCED 14, CLOSED-ON-RESEARCH 87, CLOSED-ON-CANDIDATE 27, with T/P/C
26/372/5. The four new OPEN P rows bring OPEN to 103 and P to 376.
The decrease in candidate closure labels is a correction under the requested
strict source criterion, not regression of the underlying proved equations.

There are **26 exact operation source closures**: 23 from the callback branch
and three unique CB3 rows (op120, op225, op246). op229/V246 appears on both
branches and counts once. The scoped Formatter-axiom diagnostic V270 adds
one candidate closure, giving 27. V269's original native Formatter type,
value, options, sink, failure/state/world row remains OPEN; types stay 26/28.
The original 87 research closures are model-scoped and retain their guards.

For a V169–V267 candidate source closure, the complete extracted Result
equation must be supplied: an installed equation or bounded Kani gate alone
is insufficient. Seventeen former installed/value closures and the older
op81/V203 selected heap interpretation therefore return to REDUCED.
The stronger fresh Exact equations replace several partial source labels
already counted in recount 2, so they are not five additional ledger rows.

| CLOSED-ON-CANDIDATE import disposition | Count |
|---|---:|
| In research headline closure | 0 |
| In candidate refinement_of_data consumer closure | 17 |
| In neither | 10 |

The ten in neither are V197, V206, V209, V210, V212, V213, V214, V218, V219
and V270. Nine are source laws whose exact current theorem is absent from the
consumer import paths; V270 is an axiom-audit property with no imported
closure theorem. Among the 26 operation source rows alone: 0 research,
17 candidate, 9 neither. Import membership is not a proof of the caller's
whole-data premise. All 407 row dispositions are separately listed as
research 160 / candidate 133 / neither 114; for non-closure rows this records
only defining-source membership, not discharge.

The consumer roots are PV_Join_AggregateCaller, PV_Join_PublicCaller,
ProverRw19CanonicalAuditRefinement and ProverRw18ContextData. Paths and exact
source bindings are retained; older imported partial names do not confer
credit on newer Exact laws. Missing candidate dictionary source files are
resolved explicitly from the pinned dictionary branch for graph analysis;
this is not a coherent object/source replay certificate. No audit module is
used as a root to create membership.

Per-row changes since recount 2 (every other inherited status is unchanged;
all inherited rows are individually re-derived in ROWS3.md):

| Row | Recount 2 → recount 3 | Evidence / retained limit |
|---|---|---|
'''
for r in rows:
 if r['recount2_status']!=r['recount3_status']:
  why=r['recount3_basis']
  if len(why)>540:why=why[:537]+'…'
  s+='| '+r['id']+' | '+r['recount2_status']+' → '+r['recount3_status']+' | '+why.replace('|','\\|')+' |\n'
s+='''
V163 remains OPEN but moves from (a) to (b): the independent mathematical
serializer is published, while the concrete deployed-input-to-model instance
and full proof-byte/data equations are still missing. V164 is REDUCED to
P_source_p6 / V240; rw20's concrete context identity is checked. Source-ID
families words/publicCorr/admission/row_call are REDUCED, compile_call OPEN;
V152–V154 are REDUCED, never deployed closures. The merge gate remains blocked
by the stale-object/provenance issue; newer resume6 records a rejected protected
source replay failure as well. No protected source is edited here.

| OPEN dependency | Recount 2 | Recount 3, same 403 | Recount 3, all 407 | Change, all rows |
|---|---:|---:|---:|---:|
| (a) independent source obligation | 51 | 41 | 44 | -7 |
| (b) native interpretation / concrete model instance | 50 | 51 | 51 | +1 |
| (c) owner decision | 9 | 7 | 8 | -1 |
| Total OPEN | 110 | 99 | 103 | -7 |

Bucket (a) loses V152–V154, V164, V270, four unique new source closures
(V219/V242/V246/V254), and V163's native-dependent completion; it gains the
three new source/reachability families. Bucket (b) gains V163. Bucket (c)
loses timing rows V344/V345 after D216 and gains proposed-T adoption V406.
Owner-first rows are V370 compiler preservation, V371 DOITM/CPU latency,
V373 and V380-inversion inversion boundary, V374 Docker-cap/quiet-host dudect,
V396 client bundle pin, V400 OS-entropy-failure repair A/B, V406 exact T list.
All five L1 and eighteen inherited L2 rows remain native-dependent OPEN.
REDUCED/EVIDENCED residuals are not disguised as completed native gates.

Corrections and supported lead claims, stated plainly:

- D211/recount 2 over-credited installed/value interpretations as extracted
  source closures. The 18 affected rows are explicitly downgraded above.
- D219 closes the candidate Formatter-axiom blocker only. It does not close
  V269's full native interpretation; V270 gets the scoped diagnostic closure.
- D223 is correct: refinement_of_data has no callback-hypothesis list. Its
  ExternalFuns value, reservation and whole proof/audit data equation remain.
  The source callback inventory is **30**, not 31; selected-entry source
  correspondence is not another inventory decrement. Both fixture reached
  sets remain unresolved; universally excluded entries are **none proved**.
- D226 counts op229/V246 twice across cb/cb3: only three unique additions,
  not four. Its 40→44 / 110→106 arithmetic is unsupported as unique-row
  arithmetic; cb5 inherits that duplicated baseline.
- D235's operation-to-row labels are incorrect: op84 is V206, op105 V211,
  op107 V212, op109 V213, op118 V218. The source table's 23/73 is supported;
  these strengthen five older partial equations already counted in recount 2.
- Op51/V195 remains OPEN as requested. The newer cb5 final report claims
  arbitrary-carrier P6 coverage and a checked reference-selector wrapper;
  that claim is retained explicitly, without silently reversing the withdrawal.
- D232 supplies constructed-candidate initial/causal, while **deployed P is
  unchanged: 2→2 / 8→8 / 6→6**. T stays exactly three proposed fields:
  entropy_law, entropy_kernel, observation. Neither owner adoption nor A/B
  OS-failure repair nor deployed (P ∧ T) fixture inhabitance is supplied.
- D234's noncanonical M31 reference disagreement is retained and is **not a
  row counterexample**. The canonical-domain proof is V403; no assumption,
  raw carrier restriction on source self-equality, or shipped fix is added.
- D216's timing pass supports V344/V345 EVIDENCED (5 samples per fixture and
  binary; transfer 13.742 s, withdrawal 13.499 s candidate medians). It is not
  a universal side-channel theorem. pv-envfix repairs the environment only.

**Single most valuable independent next row: V240/op223**, exact complete
shipped/extracted-source correspondence for arbitrary slices and Result
outcomes. It is V164's last P_source_p6 and feeds V163; a reference-only
extraction or another selector equation does not finish it.

Validation: **20/20 Lean statement-check invocations**, Env-J38600–38619;
19 exit 0, one exit 1 (38608, exact missing
R1Z/PDict_OwnedCorrect262.olean). Every run records target, exit, wall, peak RSS,
swap, revision/source hash, dependency fingerprint and full axioms/errors.
All accepted axiom reports are standard only. No retry or cap/range change;
current launcher TasksMax=64, -M7000, MemoryHigh 6G, MemoryMax 8G,
MemorySwapMax=0, one scope at a time. Missing helper object is not reported
passing or confused with D219's separately reused audit. Zero Kani, new proofs,
runtime suites, Aeneas/SBF/Rust builds or full manifest replay. No sibling/root
worktree edit, merge, push, or key/account/fund operation. Premises
removed/added/weakened: **0/0/0**. Stop: all rows re-derived, statement budget
exhausted. **Target not yet established.**
'''
assert '## Recount 3 2026-10-27 (B)' not in ledger.read_text()
with ledger.open('a') as f:f.write(s)
print('Appended',len(s.splitlines()),'lines')
