from pathlib import Path
import json
P=Path(__file__).resolve().parent;root=P.parents[2];ledger=root/'design/PRIVACY-LEDGER-20261026.md';s=ledger.read_text();t=json.loads((P/'totals.json').read_text())
assert '## Recount 12 2026-11-04 (B)' not in s
start=s.index('| Inventory / status | Recount 1 |',s.index('## Recount 11 2026-11-04 (B)'));end=s.index('\n\n',start);table=s[start:end].splitlines();values={'Rows':407,'T':3,'P':400,'C':4,**t['statuses']}
new=[]
for i,line in enumerate(table):
 if i==0:v='Recount 12'
 elif i==1:v='---:'
 else:v=str(values[line.split('|')[1].strip()])
 new.append(line.rstrip()+' '+v+' |')
body='''

## Recount 12 2026-11-04 (B)

Independent source/statement/receipt recount from research d6b809c9e8a. All407
rows re-derived with immutable pins in
[evidence/privacy-recount-20261026/recount12/pins.json](../evidence/privacy-recount-20261026/recount12/pins.json).
The shared candidate ref origin/codex/cx-prover-rw-20261023 is d4ed1ba89f;
the local same-named ref is stale8e450dab558 (October29), recorded separately
and not used to claim adopted-client association. Nine live worker heads are
captured once; later commits and uncommitted work are excluded. Same historical
meanings, scopes, columns and dependency buckets as Recount11; current fields
supersede historical reporting. Import membership is not discharge.

'''+ '\n'.join(new)+'''

Explicit row status changes:

- **V177 and V180: CLOSED-ON-CANDIDATE → OPEN a.** Their current bounded
  PathBuf source scopes depend on C044. Its retained control output fails
  `len != r.len()` but contains no complete execution/pointer trace. Under the
  conservative k4 review, full-width input queries require retained control
  evidence; no rerun was allowed. Historical source/model laws remain. This
  suspends evidence, not the truth of the theorem or native source correctness.
- No other row status/class changes. OPEN68 = a6/b58/c3/d1. REDUCED176,
  EVIDENCED14, research closures87, candidate closures62. P400/C4/T3 remain.

Explicit credit changes under **D639/k4**:

- **C044, C084, C088, C089 → SUSPENDED**, missing retained full matched traces.
  C088/C089's output identifies only a generic formatted-panic placeholder;
  it does not identify the intended original assertion. C084's inverted
  `get(i)` equality and C044's inverted length equality are retained as terse
  assertion summaries, not full traces. These checked-get sources restrict
  actual dereferences to their small buffers; no aliasing is alleged. The
  review conservatively includes their unconstrained full-width input queries
  rather than substituting that source argument for the requested trace.
- **K93109, K93110, K93111 → SUSPENDED** for missing full matched traces.
  Their repaired logical-u128/two-slot projection is explicit and avoids the
  original physical-offset mechanism. Terse controls alone are not promoted
  to the requested trace evidence. Original ptr.add/allocation/OWNER binding
  remains OPEN. No parent or row closure depends on these packets.
- **K93100/K93108 remain uncredited model errors**, not native counterexamples:
  distinct offsets differing by2^62 alias modulo2^48 at offset2^48−4.
  Positive and both negative traces are retained at the pinned D637 packet;
  the failure was classified before subsequent work.
- The305-credit K-3 baseline remains26 RESTORED/81 UNAFFECTED/195 SUSPENDED/
  3 WITHDRAWN. After the k4 overlay: **24 RESTORED/79 UNAFFECTED/199 SUSPENDED/
  3 WITHDRAWN**. New K9 gates are a separate inventory, never added to305.
  C051/C053/C163/C164 stay K-3 RESTORED within their original bounded scopes;
  C156 stays SUSPENDED for the missing full-raw multiplication child/frame/G
  bridge. Local memo/caller diagnostics do not restore it. K92679's reported
  scope overlap earns no credit; its changed sequential replacement is separate.
- C044 was current support for V177/V180, so both rows reopen. C084 is not
  current support for V179's structural closure; C088/C089 are not current
  support for V233's independent typed structural restoration. V233/V236/V197
  retain Recount11's exact scoped restorations. V244 uses C155/C157, never
  C156. No current credited closure consumes a newly suspended credit.

Explicit qualifications and status-note changes:

- **D602/V183:** retain the qualified source closure
  `R1Z.PV_FXM_ReserveSelected.complete`, with Result/failure/divergence and
  native association uninstalled. The adopted diagnostics.rs global allocator
  calls System then aborts on null for alloc/alloc_zeroed/realloc. The generic
  returning-model denial law supplies NO native returned-denial credit.
  Native association must map null to abort terminal/divergence, preserving
  libc post-world/errno, timing and named rdea-1/rdea-2/V370 obligations.
  [Every identified consumer is dispositioned](../evidence/privacy-recount-20261026/recount12/v183-consumers12.json).
- **D630:** `PV_B3P_OriginalSelection29177_29182_29187.first_package` is ONE
  conditional hybrid theorem, consuming OWNER by name and
  NativePendingSelection623, NativeFaultSelection623,
  NativeEffectsSelection623, ResourceTimingIndependenceSelection623.
  Provider raw92894 passes183 roots. **D636:** the three CombinedLift630227,
  CombinedComponent630227 and CombinedArithmetic630227 package theorems retain
  their corresponding four named hypotheses; raw92895 passes220 roots.
  They cover10 sites;217 caller functions/1494 sites remain. They do not
  close V241/V244/V245, the original-ops equation, opaque associations or
  DeployedWrapper557. Hybrid/reclassification within existing tool trust,
  not endpoint premise removal.
- **D624/D625:** P_pthread_create_transfer, P_pthread_join_quiescence,
  P_scope_atomic_lifetime and P_thread_prefix_frame are OPEN named P premises
  pending the owner. Neither source-control fragments nor arbitrary port
  replies discharge them. No row/credit installs them as a proved fact or T
  field. The full ordered_families_spawn_prefix_linear and v263 pair/descriptor
  instance remain OPEN. Unsupported TLS/capture controls earn no native credit.
- **D589/l3-2:** native events/fileTrace/countTrace/timeTrace/oraclePrefix stay
  source-level effects of one advancing world run. source_entry_world is now
  defined over Machine.run with named executable parameters; its concrete
  installation and five RuntimeBinding equations remain OPEN. D623's
  pending-free Executes overstatement is corrected; source_entry_world uses
  Machine.run directly, and FIRST has pending-inclusive adequacy. The named
  ActualEntropyEntryPrefix source-to-machine pairing remains a V370/L3
  residual, not a row or a premise consumed by any row/projection. Older
  da36d6aa physical evidence still requires adopted-fc8808eb binding/refresh.
- **D597/92080:** the corrected single authorized agg16 run passes all three
  steps: consumer compilation,16539-module zero-dangling/matching-import scan,
  and32-root unchanged NEP raw walk with zero unresolved constants, standard
  axioms and raw/summary equality. Scoped coherent fixture composition is
  confirmed, conditional on FixturePdaRuntime base. The run's retained
  authorization is14G/16G/swap0; exit0,wall160.604783654s,peak12424428KiB,
  swap0,source74ac46dbcac0643157cf9c90b1fcb212212513cb. No new run or cap
  change occurred here. This supersedes Recount11's failed92060 raw-driver
  status, not actual event acquisition or joint-simulation obligations.
- RuntimeReturnData is not consumed by privacy and adds no T item. Final
  user-client adoption remains scoped to fc8808eb/uc8897074612 and shared
  candidate d4ed1ba89f; V396 native integration remains OPEN. D640's statement
  that timing awaits a quiet window is a pending rerun/status note, not a
  withdrawal of the retained completed N91120 evidence independently checked
  in Recount11. No new timing measurement is claimed.

[ROWS12](../evidence/privacy-recount-20261026/ROWS12.md),
[method](../evidence/privacy-recount-20261026/recount12/METHOD12.md),
[k4 per-credit check](../evidence/privacy-recount-20261026/recount12/k4-credit-check.json),
[status/receipt audit](../evidence/privacy-recount-20261026/recount12/status-audit12.json)
and [totals](../evidence/privacy-recount-20261026/recount12/totals.json) retain
source pins, exact hypotheses, support changes and resource/axiom receipts.
Every #print axioms is SUMMARY-BASED; raw NEP results are separately labelled.

Validation here is inspection-only: Lean0/40,Kani0/0,Env-J93400–93439 unused.
No proof, full replay, unchanged regression, Stream A edit, key action, merge
or push. Endpoint premises removed/added/weakened0/0/0. T remains exactly
entropy_law,entropy_kernel,observation; simE, full D159 observer, domain, bound
and bad event unchanged. Actual source/OWNER/world association, op227/op257,
E1/E2, native integration, L1/diag/L3 links, acquisition/joint simulation and
the complete actual release obligations remain.
**Target not yet established.**
'''
ledger.write_text(s+body)
