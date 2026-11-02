import json,re,collections
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent
rows=json.loads((P/'rows10.json').read_text());by={r['id']:r for r in rows}
for id in ['V178','V181']:
 by[id]['recount10_basis']='OPEN b. D502 adopts fixed diagnostic bundle and D537 ships da36d6aa; the prior pending D474 decision is resolved. Literal-message/backtrace/panic-hook controls are partial source evidence. Native I/O/format/capture/cleanup, occurrence/operand/frame laws and actual event projections remain. No deployed diagnostic link is inferred from the three DIAG model witnesses.'
by['V239']['recount10_basis']='OPEN b/PARTIAL. SourceDense and source-stage ActualInput remain distinct from actual native input/resource/trace association. D494 PV_SKWC_OWNM.satisfiable verifies the five-link conjunction on a non-degenerate MODEL instance, not a deployed run. No real V239 closure. Ownp line remains parked; later model witness supersedes its old undetermined-consistency label.'
by['V346']['recount10_basis']='OPEN b. Historical manifest checks artifact/source associations at their recorded pins; stale-record review D495-D505 checked76 credited closures and leaves31 provenance/consumer cases to final replay. D537 adopted bundle changes client pin to da36d6aa and requires refreshed manifest, as would later user-client adoption. Current target/source/artifact and whole reached-cone binding, coherent release replay and NEP audit remain absent. Historical pin equality is not a current full release certificate.'
by['V380-inversion']['recount10_basis']='OPEN native inversion proof obligation at the retained row status. The owner adopted inversion zero-boundary as proof work; no further mathematical approval is needed. Conditional same-coin pole/guard and mask/slot algebra remain, actual reached-call slots, native operands and full observation need binding. K-3 suspended C056 provides no current support. D484/D487 connect17 calls/two zero branches only at qualified binary/source evidence, not all inlined copies or the adopted new binary.'
for r in rows:
 if r['id'] in ['V347','V348','V349','V350','V351','V353','V355','V356','V358','V359','V361','V362','V363','V364','V365','V367']:
  r['recount10_basis']+=' CURRENT: D490/D494 give three DIAG and L1_COUNT_TRACE joint MODEL witnesses. They verify model consistency, not native links. L1 count and L2 lines are PARKED on native/world/D163 association; binary L3 work requires the adopted-client refresh. No closure from parked status.'
membership=[]
for r in rows:
 membership.append({'id':r['id'],'historical_consumer_roots':r['import_witnesses10'],'adopted_event_endpoint':r['event_endpoint_import_witnesses10']})
 r['import_witnesses10']='import-membership10.json#'+r['id'];r['event_endpoint_import_witnesses10']='import-membership10.json#'+r['id']
(P/'import-membership10.json').write_text(json.dumps(membership,separators=(',',':'))+'\n')
(P/'rows10.json').write_text('[\n'+',\n'.join(json.dumps(r,separators=(',',':')) for r in rows)+'\n]\n')
t=json.loads((P/'totals.json').read_text());t['candidate_closure_imports']=dict(collections.Counter(r['in_headline_closure10'] for r in rows if r['recount10_status']=='CLOSED-ON-CANDIDATE'));(P/'totals.json').write_text(json.dumps(t,indent=2)+'\n')
ls=['# Recount 10 2026-11-02 (B)','','All407 historical rows; current recount10 columns supersede dated dispositions. Full historical fields, exact source snapshots, qualifiers and evidence are in recount10/rows10.json. Membership is not discharge. Target not yet established.','','| Row / class9 →10 / name | Status9 →10 | OPEN bucket | in headline closure? | Tool trust | Derivation, residual and evidence |','|---|---|---|---|---|---|']
for r in rows:
 detail=r['recount10_basis']+' Residual: '+r['residual10']+' Evidence: recount10/rows10.json#'+r['id']
 ls.append('|'+r['id']+' / '+r['recount9_class']+' → '+r['recount10_class']+' / '+r['name'].replace('|','\\|')+'|'+r['recount9_status']+' → '+r['recount10_status']+'|'+(r['dependency_bucket'] or '—')+'|'+r['in_headline_closure10']+'|'+r['tool_trust10']+'|'+detail.replace('|','\\|').replace('\n',' ')+'|')
(B/'ROWS10.md').write_text('\n'.join(ls)+'\n')
ledger=Path('design/PRIVACY-LEDGER-20261026.md');s=ledger.read_text();assert '## Recount 10 2026-11-02 (B)' not in s
old=s[s.index('## Recount 9 2026-10-29 (B)'):];a=old.index('| Inventory / status |');z=old.index('\n\n',a);table=old[a:z]
vals={'Rows':407,'T':3,'P':400,'C':4,**t['statuses']}
new=[]
for i,l in enumerate(table.splitlines()):
 if i==0:new.append(l+' Recount 10 |')
 elif i==1:new.append(l+' ---: |')
 else:
  label=l.split('|')[1].strip();new.append(l+' '+str(vals[label])+' |')
text="""

## Recount 10 2026-11-02 (B)

All407 rows are re-derived at the [immutable pins](../evidence/privacy-recount-20261026/recount10/pins.json):
research base a6138b93b9, fixed prover candidate ba1fa07d9e, and nine live heads
captured at03:40:16 UTC. These are point-in-time snapshots; pv-v263 was absent
then and later work earns no credit. LOG D480–D565 is read at the base; D566
is retained at supplemental LOG revision5128519ff8. Full same-column row table:
[ROWS10.md](../evidence/privacy-recount-20261026/ROWS10.md). Machine-readable
[rows](../evidence/privacy-recount-20261026/recount10/rows10.json),
[totals](../evidence/privacy-recount-20261026/recount10/totals.json),
[method](../evidence/privacy-recount-20261026/recount10/METHOD10.md),
[independent checks](../evidence/privacy-recount-20261026/recount10/independent-audit10.json).

"""+ '\n'.join(new)+"""

Status changes, all OPEN → CLOSED-ON-CANDIDATE at a qualified source boundary:

- **V201:** rdcd4 complete original generic CodeField/q1024/Point Result law;
  145 records dispositioned, concrete iterator/memory/writeback bindings.
  Native producer and full physical observation remain separate.
- **V220:** complete original28-coefficient radix-four source equals the
  loop-free reference for every typed input/challenge, retaining errors and
  divergence. Structural binding earns the credit; the unrecovered historical
  checker is not called passing. No new polynomial-meaning theorem.
- **V237:** complete generic Core::default Result and original moved-core
  reference. ONLY the fixed64-byte default subcall is input-free, with the
  45-node influence census, named zero literal, exact native bytes and deployed
  configuration harness. No arbitrary new default callback or Core singleton.
- **V242:** D502 explicitly adopts lowering-only compiler-cohort credit under
  V370. The whole-row class-A audit identifies four unchanged pure project
  bodies; the existing all-Public Result theorem is retained. Compiler
  preservation remains a boundary, not a discharged endpoint premise.

Thus OPEN73→69 and candidate closures57→61. REDUCED176, EVIDENCED14,
research closures87 and P400/C4/T3 are unchanged. Tool-semantic transport is
reclassification within existing trust, never endpoint premise removal.

OPEN bucket changes and reasons (exclusive d/c/b/a precedence):

- **V197 d→a:** live rdcd5 proves an empty-input whole-Result mismatch:
  existing parser fail.panic versus owned parser fail.arrayOutOfBounds.
  This checked equality failure supersedes escaping-reference extraction as
  the immediate blocker. V197 remains OPEN; no privacy leak is inferred.
- **V373 c→a:** owner recipe/timing choices are resolved; compiled-kernel audit
  must be refreshed on adopted da36d6aa. Prior audit did not identify every
  inlined copy. **V374 c→a:** actual-binary statistical leakage evidence remains;
  throughput medians and decoder traces are not whole-client dudect.
- **V396 c→b:** D524 resolves user-client scope; concrete native integration,
  faithful external operations, timing and full-entry checking remain.

Buckets are **a5/b60/c3/d1**. Remaining owner bucket is V231,V232 (SHA backend)
and V371 (CPU/DOITM operational boundary). V233/V236 remain OPEN on exact typed
carrier/buffer transport; rdcd5's partial work does not restore them.

**K-3:** independently recomputed final totals are **22 RESTORED,81 UNAFFECTED,
199 SUSPENDED,3 WITHDRAWN** over305 observations. The
[per-credit/row check](../evidence/privacy-recount-20261026/recount10/k3-audit10.json)
checks controlled rerun receipts and all34 current support lists. No CURRENT
qualified credited scope depends on a still-SUSPENDED credit. V183's historical
flag is cleared only for its independent world-indexed structural family;
C018/C019 remain suspended. C051 (native Drop log), C053 (Core default log),
C156/C163/C164 (shared memo) remain SUSPENDED. No local mock, missing original
input or passing rerun overrides inherited K-1/K-2 restrictions. UNAFFECTED is
only K-3 on recorded inputs; std parity/k''' structural arguments, compiler,
native/world/domain conditions remain. These credit counts are not row totals.

**Measured headline D540:** statement inspection confirms the same full
Signal×Observation carrier, adaptive observer, simE/completion, bad event,
PV_EVH_Core.bound, strict threshold and capped T (entropy_law,entropy_kernel,
observation). The measured runtime permits arbitrary probability laws with
measurability/exact joint ConditionalLaw as ordinary P; the adapter forwards
all22 former runtime fields unchanged. Its finite-uniform corollary recovers
the entire old rational inequality and numerical envelope from the measured
endpoint. This removes finite representability, not a native row obligation.
The Result-only headline is historical; the D159 observer is not weakened.

**Publication consumers D541/D548:** QueryAppend and FinishContext are
constructed internally. Required links fall9→8→7, with the exact same actual
RUNJOIN_PUBLISH_COMPACT conclusion and runtime/world/store binders. These are
CONSUMER improvements, not counted row closures or endpoint removals. Remaining
links are R24Sampler,CommonSample,BackendInput,QueryContext,QueryRange,
NodeAppend,PublishOrder. Skeleton consistency: reduced to non-emptiness;
actual Nonempty P is unproved, including the independent op257 obligation.
Model witnesses for V239/DIAG/L1 are not deployed-run witnesses. L1/L2/older
binary L3 lines remain parked pending their named native/binary work.

**V244 D559:**36/36 local associations (4 direct extraction,2 Kani,30
Lean/structural) compose jointly, but the exact original runjoin callback
consumer still requires **PV_B3P_Closure557227.DeployedWrapper557 base ops**.
Formatting unreachability,16 opaque helper instances and pointer/drop/
initializer/caller associations are missing. The live pin retains this binder.
**V244/op227 remains OPEN**, and selected ports or a model installation cannot
be substituted for that deployed residual.

**D565 correction:** the joint non-vacuity witness is **NOT established on a
coherent build**.90000's successful elaboration used the incoherent NDR cohort;
90001 and NEP_R900 fail at undeclared stage2_owned.match_3. The NDR authority,
evhc overlay/bridge joint-coherence claim and D562 witness credit are excluded.
Source-level privacy unification is unaffected. Every #print axioms output is
labelled **SUMMARY-BASED**; standard summaries do not cure a missing constant.
NEP_Driver uses importAll/private loading and hard errors; its planted-case
coverage and actual failure are retained, never filtered. No new raw release
audit or repaired NER cohort is claimed.

**Client D537/D561:** combined bundle da36d6aa is ADOPTED pending the user
client, with unchanged three ELFs and D359(A) paired throttled timing
(transfer14.834947s,+3.3167%; withdrawal14.310064s,−1.3159%). V346 manifest and
V373 binary audit must be refreshed. The user-client scope is approved, but
candidate9310ca5e is not an all-gates-pass adopted executable:1000/1000 pairs
(2000 real calls) and31/31 checksums are finite positive evidence; N75149 has
zero accepted timing pairs. Full-entry emission is not full-entry Lean
compilation: faithful25-type/119-op externals, operand-losing formatting and
the decoder I32/U32 shift mismatch remain blockers at the captured pin. The
three-root audit covers only those compiled roots. The adopted linux_raw
getrandom backend removes the old dlsym path; native error/cleanup/event and
witness-independent-failure laws remain obligations, never extra T fields.

Validation is inspection-only: **0/40 Lean,0 Kani**, Env-J90300–90399 unused,
no proofs or new Lean modules. Historical exact targets, exits, wall/RSS/swap,
revisions, admission records and summary axiom lines are retained in
[receipt-audit10.json](../evidence/privacy-recount-20261026/recount10/receipt-audit10.json)
and the content-addressed manifest. No whole replay or unchanged suite rerun,
Stream A edit, key action, merge or push. Endpoint premises removed/added/
weakened0/0/0. Remaining work includes deployed op227/op257 and Nonempty P,
actual event acquisition/joint D163/D166/V400, client gates, E1/E2 and the
coherent final replay with complete NEP audit. **Target not yet established.**
"""
ledger.write_text(s+text)
print('Final rows/table/ledger written')
