from pathlib import Path
import json,re
P=Path(__file__).resolve().parent;B=P.parent;f=Path('design/PRIVACY-LEDGER-20261026.md');s=f.read_text();t=json.loads((P/'totals9.json').read_text());prior=s[s.index('## Recount 8 2026-10-28 (B)'):] if '## Recount 8 2026-10-28 (B)' in s else s[s.index('Recount 8 2026-10-28 (B)'):]
vals={'Rows':407,**t['classes'],**t['statuses']}
a=prior.index('| Inventory / status');b=prior.index('\n\n',a);table=[]
for line in prior[a:b].splitlines():
 label=line.split('|')[1].strip()
 val='Recount 9' if label=='Inventory / status' else '---:' if label.startswith('---') else vals[label]
 table.append(line+' '+str(val)+' |')
a=prior.index('| OPEN dependency');b=prior.index('\n\n',a);deps=[]
for line in prior[a:b].splitlines():
 label=line.split('|')[1].strip()
 val='Recount 9' if label=='OPEN dependency' else '---:' if label.startswith('---') else t['open_dependencies'][label[1]]
 deps.append(line+' '+str(val)+' |')
a=prior.index('| in headline closure?');b=prior.index('\n\n',a);membership=[]
for line in prior[a:b].splitlines():
 label=line.split('|')[1].strip()
 val='Recount 9 all / candidate closures' if label=='in headline closure?' else '---:' if label.startswith('---') else str(t['all_row_imports'].get(label,0))+' / '+str(t['candidate_closure_imports'].get(label,0))
 membership.append(line+' '+val+' |')
text='''

## Recount 9 2026-10-29 (B)

All407 rows are re-derived at [immutable recount9 pins](../evidence/privacy-recount-20261026/recount9/pins.json):
research6474027f52, fixed prover candidate42760700cb and the five live heads
captured as snapshots. The full same-column row table is [ROWS9.md](../evidence/privacy-recount-20261026/ROWS9.md);
[rows9.json](../evidence/privacy-recount-20261026/recount9/rows9.json) retains
all historical fields with explicit recount9 dispositions. Full defining and
closing sources, source hashes, import paths and receipts are indexed in the
manifest. Byte-identical defining sources reuse the prior scoped derivation;
no LOG summary substitutes for a statement. Membership is not discharge.

'''+ '\n'.join(table)+'\n\n'+'\n'.join(deps)+'''

OPEN81→73 and selected candidate closures49→57 are eight scoped restorations:
V229,V230,V256,V257,V260,V265,V217,V213. REDUCED176, EVIDENCED14 and research87
are unchanged. No endpoint premise was removed, added or weakened. V231 moves
b→c for the unresolved owner SHA-NI/backend decision; buckets follow d/c/b/a
precedence, so a2/b62/c7/d2. No extra counted row is invented for the observation
carrier or deployed-verifier checklist. Tool-semantic transfers remain
RECLASSIFICATION within existing trust, never premise removal. T remains
exactly entropy_law, entropy_kernel, observation.

| Row | Exact statement/scope and independent disposition | Evidence class |
|---|---|---|
| V229 | PV_OWNH_Literals.v229_result; constant214-word rows,437 canonical Result bytes. Ordinary cone influence/address/channel(iii) reviewed;85 crate-source files independently match the pinned candidate; actual native stdout compared to Lean literal in every byte. | exhaustive over a singleton input domain, deployed-configuration harness |
| V230 | PV_OWNH_Literals.v230_result; constant64-word masks,137 bytes; original row dependency, fixed shifts/array and expanded masks agree. | exhaustive over a singleton input domain, deployed-configuration harness |
| V256 | PV_RDB2F_SamplerCalls.gamma_callback; original iterator/FnMut/current-array, returned quotient, first and optional second carry and verifier continuation. Exact original-path88-target replay completes the suspended gate. | structural (K-1 substitute), own-1 |
| V257 | PV_RDB2F_SamplerCalls.ordinary_callback; original from_fn, all eight writes and final current quotient before decode/caller. Same exact-path replay, zero object differences. | structural (K-1 substitute), own-1 |
| V260 | PV_RDCD3_V260Complete.complete; both original253 and selected251 APIs, all weights/kinds/indices, full errors/divergence and range/fold/index source binding. | structural (K-1 substitute), own-1 |
| V265 | PV_RDCD3_V265.complete; static circle control and concrete M31 inverse including zero assertion; no arbitrary inverse or success premise. Pointer-form Kani stays quarantined. | structural (K-1 substitute), own-1 |
| V217 | PV_RDCD3_V217.complete; all typed c1/mask/g/point, complete source/owned Result with every array write; original unrecovered checker not relabelled. | structural (K-1 substitute), own-1 |
| V213 | PV_RDCD_Op109Audit.source; all raw WideExact, complete Result/Option, ExternalTypes/ExternalFuns retained. Compliant62012–14/62112 and focused62113 replace void41466.17 aggregate consumers remain unfinished. | extraction with deployed source-law transport; reclassification |

V213 differs from D425's worker classification. The scoped row law is freshly
rebuilt and audited through compliant objects; uncompiled aggregate consumers
block a coherent final release replay, not the row-specific source association.
This uses recount8's row-specific treatment of the other rdcd restorations.
41466 remains void under(t), and no historical aggregate importing it is credited.
Rdeac62002 also repairs the old final-replay name error; V178/V181 stay OPEN
because the deployed diagnostic/effect association is still missing.

The own-2 triple-prime evidence label is accurate in its full harness form and only for
the constant successful value domain. The harness is not the shipped ELF and
one execution does not exhaust allocator states, failure hooks or timing.
Memory primitives are confined to supplied regions under V370; ordinary-cone
external reads are excluded, relative-pointer bases cancel, and allocator-written
state is not subsequently read. Fixed1016→2032/544-byte requests and every failure
prefix retain rdea-1 and public failure independence. Source/codegen V370 and
D381/D386 remain. Calling these source-binding proofs or full-observation
closures would be incorrect.

Ruling b3p6-1 supports36 raw-body reclassifications, not V244 closure. Independent
re-tokenization re-hashes actual committed postmacro expansions and exact raw
extraction blocks.43 identities pass; seven lack exact model-span provenance:
fields, frontier, private_public, semantic, terminal_qm31, transition and
withdrawal_public. The reproduced Funs/Types/translation hashes agree; LLBC
identity is not claimed.79 is a conservative candidate universe, not certified
exact deployed reachability.36 nonidentical candidates also remain unbound.
Dependency/name resolution, compiled ports, D188 matrix/writeback, slices and
library bindings remain. Exact tool trust justifies the reclassification label;
it does not establish Rust correctness. The generated extraction Cargo.lock is
hash-recorded but absent from the tracked snapshot; its bytes were not independently
re-hashed here. All14 other recorded extractor input files match.

Ruling h5'' is satisfied for PrivacyR1HeadlineV2. The entire old/new delta removes
one redundant rfl, with every statement and all other bytes unchanged. Explanatory
commite030a78a73, research/candidate byte identity and fresh65000–65010 V2/ten-consumer
receipts support the supersession. Stale4321909f→tracked0bb8dcc7 repairs source
cohort authority only. It does not resolve the separate observation finding.

The headline currently proves a conditional Result-only theorem. D476/D478 expose
why its Runtime.disclosed/observerOracle cannot express D159's ordered bytes,
side channels, partial failed/divergent prefixes and timing. plan.rs starts
Instant at84 and inserts prove_wall_seconds at129 after the core prover and
file writes. A finite pause can change that observation with the same core
Output/public data/coins/charged events/option-B signal. The Lean obstruction
is conditional on a good completed path; no paired native non-bad run was
certified, and this is not a witness-leak finding. D166 simulatable timing is
a distributional route, not Result-fibre functional recovery. External timing
would remain even if the printed field were removed. Full D159 joint privacy
is not established. Owner D478 recommends an event-retaining interface and
model-level recomposition; EVHD remains experimental and unadopted.

| PARTIAL decomposition | Named links and present boundary |
|---|---|
| PV_OWNM_V239.restore | ActualInput, SourceDense, Transcript879, Transcript890, OwnedPublicPlan. SourceDense proved; ActualInput source-stage composition only. Four deployed links remain open. V239 parked after ownp. |
| PV_DIAG10.DIAG_FILE_TRACE / DIAG_JSON_STDOUT_TRACE / DIAG_ERROR_STDERR_TRACE | Init, Step, Readout, EventOrder per channel; Entropy, MaskedAttempt, ReachedAttempt; Operands, Sites, Frames, Levels, Request, WorldBlind, ExecutionHistory, ChargedBad. Fifteen named-link families; no full deployed producer link discharged through diag12. |
| PV_L1E_OriginalCountSkeleton.original_count_trace; PV_L1G_Statements.combined | CountAcquisition partial; BodyWrapper open; OriginalRetry partial; NativeD163 and Sites open. L1G adds full-world/source prefix criteria, not native instances or joint simE coupling. ORACLE_PREFIX, TIME_TRACE and RETAINED_SIDECHANNELS remain open. |
| PV_RunJoin_PublishSkeleton54.complete | RUNJOIN_PUBLISH_COMPACT source-slice equation. R24Sampler discharged; CommonSample, BackendInput, FinishContext, QueryAppend, NodeAppend, PublishOrder open in the recorded54 result; full native/toRP composition remains. |
| op227 selected_callback bridge | Statement/decomposition in progress on pinned b3p6; unconditional consumed hypothesis not discharged. V244 reference/installed nonvacuity residual(a) is settled at emitted/original-carrier scope, not full native closure. |

D456's byte-pinned typed caller equality and V047 fibre consumption without
that equality hypothesis are accepted. Live native record/handle binding,
FixturePdaRuntime, E1/E2, actual RunJoin and world association remain. JHx_Joint
remains historical-forest evidence only. V152–V154 retain reduced raw-family
meaning with separate successful canonical honest-family coverage; positive
change is necessary for both spend kinds and the owner domain choice is pending.

The diagnostic line is PAUSED after diag12 pending D474. Std I/O/format/capture/
cleanup, actual operand/frame/site laws and V400 remain despite reusable syscall,
buffering and option-B conditional models. No checked honest witness-dependent
diagnostic is found and no universal native publicness is established. V178/V181
and V239 are parked; rjdec/rj4idb are parked with their component laws retained.
V231 awaits SHA-NI owner action; V197 retains its exact loan-validation obstruction.
Rdcd4, runjoin, b3p6 and L2E remain partial at their snapshots. No live-head promise
or new closure is inferred from later work.

D474 recommends a reviewed client diagnostic redesign with ELF checks, repin
and timing re-run. D478 recommends an event-retaining observer. Neither is adopted
at these pins; their owner-packet texts are unchanged. Other pending choices
are successful-user/zero-change scope, paired throttled timing, V242 compiler
cohort, release features/CT decoding, N7 custody, SHA-NI, DOITM and client scope.
The release checklist still requires deployed verifier equals pinned release
ELF; historical devnetfb2fc048 is not release63ad3e9c/defaultf8c0ec72.

'''+ '\n'.join(membership)+'''

[CORRECTIONS9.md](../evidence/privacy-recount-20261026/recount9/CORRECTIONS9.md)
records D418–D479 dispositions, label/scope corrections and failed/void exclusions.
The independent raw receipts include exact targets, statuses, wall/RSS/swap,
source revisions and complete standard-axiom outputs. Failed sorryAx records
are retained and uncredited; refusals60630/60643 wait before compliant launches.
Validation is source/statement/receipt inspection only: Lean0/40, Kani0;
Env-J68000–68099 unused, no new proofs, host scopes or unchanged release replay.
No Stream A/soundness file, implementation, observer, simulator, wallet or key
is edited. Coherent final dependency replay, native/deployment bindings and full
D159 observation composition remain. **Target not yet established.**
'''
assert '## Recount 9 2026-10-29 (B)' not in s
f.write_text(s+text)
