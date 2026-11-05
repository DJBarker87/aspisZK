from pathlib import Path
import json,re,hashlib,subprocess,collections
E=Path(__file__).resolve().parent
read=lambda n:json.loads((E/n).read_text())
receipts=[]
for kind,count in [('K',100),('L',70),('E',3)]:
 for i in range(1,count+1):
  a=f'NGM_{kind}{i:03}';r=read(a+'/receipt.json');assert r['attempt']==a;receipts.append(r)
assert len({r['attempt']for r in receipts})==173
excluded=['NGM_K083','NGM_K086','NGM_K087'];kani=[r for r in receipts if r['kind']=='kani']
expected_pairs=[(i,i+1)for i in range(1,83,2)]+[(84,85)]+[(i,i+1)for i in range(88,100,2)]
for p,n in expected_pairs:
 for number,status in [(p,0),(n,1)]:
  a=f'NGM_K{number:03}';r=read(a+'/receipt.json');raw=(E/a/'stdout.log').read_text();assert r['exit_status']==status
  assert ('VERIFICATION:- SUCCESSFUL'if status==0 else'VERIFICATION:- FAILED')in raw
  assert not re.search(r'timed out|memory limit exceeded|SIGKILL',raw,re.I)
for a in excluded:assert 'timed out'in(E/a/'stdout.log').read_text()
assert read('NGM_K100/receipt.json')['exit_status']==0
summary=dict(status='budget exhausted; target not established',used=dict(kani=100,lean_audit=70,extraction=3),limit=dict(kani=100,lean_audit=70,extraction=3),kani=dict(positive=49,matched_negative=48,timeout=3,unpaired_positive='K100 reverse control trace; no standalone native credit',excluded=excluded),max_rss_kib=max(int(r['peak_rss_kib'])for r in receipts),swaps=sum(int(r['swaps'])for r in receipts),new_closed_rows=['TX2:132','TX2:145'],tail_roots_closed=0,source_revision_at_last_launch=read('NGM_K100/receipt.json')['source_revision'],final_audit=read('NGM_AUDIT.json'),scopes='one own scope at a time; every launch admitted exit0 AND allowed:true;6G/8G/0/64 unchanged',extraction_failures=['E003 Aeneas internal borrow-context failure; no credit/no retry'],lean_failures=[r['attempt']for r in receipts if r['kind']not in ['kani','extract']and r['exit_status']!=0])
(E/'NGM_BUDGET.json').write_text(json.dumps(summary,indent=2)+'\n')
closed={row for f in read('NGM_CLOSED.json')['functions']for row in f['rows']};remaining=[r for r in read('NGM_REMAINING.json')if r['row']not in closed]
updates={
'TX2:115':('Native full Result pair K084/085 passes, but general-domain event length/order and call/frame association remain OPEN after K083/K086/K087 timeouts. Extracted-reference complete Result/acceptance and source-body equality are separate checked laws; their SAME-call source/cohort interpretation, all Weights::new/pair/round/dot callee packets, and NFW Prepared/view producer domains are still needed.','Kani: split event/capture/frame obligations; do not repeat timed-out whole-record shape. Lean: complete reference/source/cohort association and SAME-call callee/domain composition.'),
'TX2:114':('Fourteen one-iteration native observations and all matched corruptions pass K055..082. Typed projection and decoded-item partial-Result induction compile. Still need nine-word/count parser ABI association to those observations, canonical field-window/index propagation, exact new/finish Q-packet use, byte-source loop/error-prefix association, and equality to the adopted SAG dot function. No source/cohort loop closure is inferred from generic induction.','Lean-only work remains with the existing native candidates;70 Lean/audit slots exhausted. Further Kani only if exact ABI/frame association exposes an uncovered observation;100 native slots exhausted.'),
'TX2:116':('K098/099 test the exact native Relation/Ok Result against a safe reference with full opaque scale/polynomial replies. NGM_RoundScale.total supplies the emitted quarter product value/canonicality. Missing native call/frame captures, field-window/source association, reference extraction/cohort association (E003 failed), and CLOSED polynomial composition on SAME arguments.','Kani: scale/polynomial call arguments/order/frame with matched controls. Lean/extraction: full source/model Result and field/callee domain association; budgets exhausted.'),
'TX2:119':('K088..097 five single-iteration observation pairs pass; K100 reverse-fold control trace is an unpaired diagnostic. The emitted WideExact.mul natural value law exists; source-step erasure has mutation controls. Missing safe-reference extraction (E003 failed), emitted/reference coefficient-add association, seven-iteration source/model induction, domain/frame propagation and matched reverse-control corruption.','Lean-only Horner/field association work remains;70 slots exhausted. Kani: matched reverse-control corruption and any uncovered per-window frame;100 slots exhausted.'),
'TX2:022':('Ledger8 OPEN; later committed NGH square packet must be imported read-only with source/cohort pins and revalidated on the SAME canonical receiver before this ledger row changes. No duplicated proof or unvalidated external credit.','No new Kani necessarily required: provenance/domain import plus coherent Lean replay/audit required;70 slots exhausted.'),
'TX2:138':('NFW owns powers/caller preparation. Import only its committed CLOSED canonical packet with provenance, revalidate and prove SAME call domain; no sibling worktree access or duplicate candidate.','Owner/import boundary. Existing native evidence may suffice after validation; coherent Lean and domain replay required; budgets exhausted.')}
for r in remaining:
 if r['row']in updates:r['obligation'],r['remaining_work_kind']=updates[r['row']]
 else:r['remaining_work_kind']='Kani: exact source-ordered local-record or one-iteration Result/error/frame packet and matched controls. Lean: emitted/reference/cohort equality, loop induction where applicable and SAME-call domains. Use CLOSED children only;100/70/3 budgets exhausted.'
 r['status']='OPEN'
(E/'NGM_REMAINING.json').write_text(json.dumps(remaining,indent=2)+'\n')
text='# NGM remaining obligations\n\nBudget exhausted:100/100 Kani,70/70 Lean/audit,3/3 extraction. This is not a Kani-only stop: all allocated Lean-only slots were used. No entry-to-accepted-spend path is CLOSED. Each remaining row and the exact type of work are below.\n'
for r in remaining:text+=f"\n## {r['row']} {r['function'].split('::')[-1]} — OPEN\n\n{r['obligation']}\n\n{r['remaining_work_kind']}\n"
(E/'NGM_REMAINING.md').write_text(text)
byrow={r['row']:r for r in remaining};graph=read('NGM_TAIL_GRAPH.json');tail='# NGM TX2 acceptance tail\n\n**Target not established.** Two supporting helper rows CLOSED relative to NGJ ledger8; all four acceptance-tail rows remain OPEN. NGM_DOMAIN.md states the exact caller predicate and its remaining NFW boundary. NGM_REMAINING.md gives member-by-member native versus Lean work.\n\n'
for g in graph:
 if g['status']!='OPEN':continue
 row=g['row'];name=g['function'].split('::')[-1]
 if row in closed:
  theorem='NGM_DoubleProduct.cohort; K041..054; E002; canonical input'if row=='TX2:132'else'NGM_GuardRawModel.cohort; K001..004; arbitrary raw full record'
  tail+=f'## {row} {name} — CLOSED\n\n{theorem}. No caller or parent promotion.\n\n'
 else:tail+=f"## {row} {name} — OPEN\n\n{byrow[row]['obligation']}\n\n"
tail+='Inherited CLOSED callees and exact call graph: NGM_TAIL_GRAPH.json (Q/NFQ/NFM/NFS provenance retained). This delta does not reclassify sibling results or retire any headline premise. RuntimeReturnData/RuntimeMemcmp and P6/D188 option A remain accepted trust rows. Source association is the retained hybrid certificate, not a new monolithic Rust semantics theorem.\n'
(E/'NGM_TX2_TAIL.md').write_text(tail)
p=E/'NGM_CALLER_DOMAIN_REPAIR.json';x=read(p.name);x.update(status='OPEN control composition',passing_general_result=['K084','K085'],excluded=excluded,unreached_after_exclusion='groups1..7 full-domain caller observations; no credit from unlaunched K088..100 in prior scripts',actual_remaining_allocation='K088..097 polynomial5 pairs; K098/099 round Result pair; K100 unpaired reverse-control diagnostic');p.write_text(json.dumps(x,indent=2)+'\n')
p=E/'NGM_DOMAIN.md';s=p.read_text().replace('K084..099 isolate','K084/085 isolate').replace('Results remain pending until their individual receipts are checked.','The full Result pass and matched corruption fail are checked. K086 and K087 event-length observations time out and are excluded; other full-domain capture/order checks remain OPEN.').replace('canonical E inputs/replies','canonical E inputs/replies');p.write_text(s)
(E/'NGM_BRIDGES.md').write_text('''# NGM bridge status

Only TX2:132 double and TX2:145 shared_two_point_guard are CLOSED. Their precise native pairs, reference/extraction pins, theorem domains and retained trust are in NGM_CLOSED.json. No tail root or caller is promoted. NGM_LEDGER_DELTA.json is additive relative to NGJ ledger8.

The SAME TX2 query-loop/flush/reconstruction domain is derived by NGM_QueryExit.tx2 and NGM_FinishDomain.tx2_writeback from the committed NGC laws, imported read-only with NGM_NGC_PROVENANCE.json. This is a model caller boundary, not native tx2_common closure. Prepared/view provenance and callee domains remain NFW/parent obligations in NGM_DOMAIN.md.

Finish control: exact source-body erasure and four rejected mutations; full general-domain Result K084/085 pass/fail. E001's safe reference has a complete two-fold Result theorem and acceptance iff (L059/L061), all eight deployed error codes are injectively preserved (L067), and NGM_FinishControl.source is exact emitted branching-body equality. The source/ref/cohort installation is OPEN. K005..040 were narrower scaffolds (zero weights/adjacent windows), never a general caller certificate. K083/K086/K087 time out; all are excluded. No renamed harness or increased limit changes a verdict.

Dot: K055..082 fourteen native one-iteration observations with targeted failing corruptions, exact KMX patch and frozen graph/lock each run. NGM_DotABI gives typed field projection, update and index/error fragments; NGM_RawWords gives exact eight-word representation/injectivity; NGM_DotInduction proves decoded-item partial-Result source iteration by induction over the CLOSED public-push model body. Byte parser, arbitrary-prestate native association, new/finish calls and adopted SAG dot composition remain OPEN.

Polynomial/round: K088..097 five native single-iteration observation pairs; K098/099 exact round Relation/Ok Result pair; K100 reverse-control trace passes without a matched failing control and earns no standalone native credit. Source erasure and six mutations pass. E003 fails inside Aeneas borrow-context collapse, so its helper reference is not an admitted extraction. NGM_RoundScale.total is a checked total quarter product/canonical value law; the existing LPi_TowerValues.wide_mul supplies the canonical tower product law. Parent source/ref/cohort and loop/domain/frame association remain OPEN. No field product is evaluated in Kani.

Final combined L068 includes NGJ_VERIFIER_IMPORT and AspisR1.RPx_Deployed.deployed. L069 raw-walks22 new roots,109 unique across retained batches; all standard axioms and no collectAxioms disagreement. The exact same optimized binary passed all8 fixtures in L021; NGM_AX2_PROVENANCE retains its source/binary pins. L070 scans13417 modules with zero dangling references, incompatible owners or import mismatches. This is focused cached evidence, not a cold frozen-manifest release replay. Failed elaborations/extraction/timeouts are diagnostic only; no source admission is used.
''')
(E/'NGM_LPh_STUBS.md').write_text('''# Lean-discharged opaque product calls

| Native local opaque call | Named emitted value law | Domain | Parent status |
|---|---|---|---|
| NGM_weights::opaque_product(x,x), two calls in source_double | NGM_DoubleProduct.total; NGM_DoubleProduct.cohort substitutes the SAME deterministic reply | SAME canonical four limbs; exact natural LPi_FieldValues.mulQ and canonical output | CLOSED double only |
| NGM_helpers::product(a,x,log), one polynomial iteration | AspisR1.LPi_TowerValues.wide_mul | SAME canonical eight-limb a/x; actual emitted WideExact.mul is ok with canonical output and exact natural mulE | OPEN reference/cohort and native call association |
| NGM_helpers::scale(claim,QUARTER,log) | AspisR1.NGM_RoundScale.total | SAME emitted E claim; factor exactly536870912; actual emitted WideExact.mul_m31 returns ok, eight canonical limbs, each input limb*536870912 modulo2147483647 | OPEN round call/frame/reference/cohort composition |
| NGM_dot::recorded_push (whole child, not a product stub) | CLOSED NFG_PushRoot public/private packets; associated NFM new/finish packets in NGJ closure | Exact canonical E, scalar validity/rejection, count/receiver and raw observation domains must be established at each SAME call | OPEN caller association; no whole-child output premise earns a closure |

Every native field product is opaque; no multiplication circuit or SHA implementation is unwound. These are (y) local-record call logs, not new field implementations or private copy stubs. Only double has complete paired value/native/cohort substitution. An existing law does not itself close a caller. Exact KMX patch remains the sole copy mitigation; no stub_verified/function contract composition was introduced for these helper candidates. P6/D188 option A is retained/reclassified, never removed.
''')
(E/'NGM_HANDOFF.md').write_text('''# NGM final handoff

Branch codex/cx-slice-d-finish-20261105; no push. **TX2 acceptance path not established.** CLOSED delta: TX2:132 double and TX2:145 shared_two_point_guard. All four tail rows and NFW caller boundary remain OPEN; see NGM_TX2_TAIL.md and NGM_REMAINING.md. Exact incoming predicate and producer obligations: NGM_DOMAIN.md. Source/cohort trust is retained hybrid P6/D188 option A, not a premise retirement.

Budget fully used:100 Kani,70 Lean/audit,3 extraction. Native outcomes49 positive,48 matched negative,3 excluded timeouts (K083/K086/K087); K100 is an unpaired diagnostic. E003 fails Aeneas loop borrow-context collapse. Failed source/model candidates and logs are retained without credit; NGM_FINDINGS.md records replacements. All standard-axiom top theorems have #print axioms. No unchanged timeout/memory failure was retried and no cap/timeout raised.

Final combined L068 passes beside the deployed headline; raw22 new roots L069,109 unique across batches; same compiled walker/driver passed8 fixtures; scan L07013417 modules,zero defects. Exact attempts include target/status/wall/RSS/swap/revision/axioms; NGM_AUDIT.json and NGM_AX2_PROVENANCE.json pin scope. Cached coherent verification only, not a new cold release replay.

Host/cache: prefix-owned workspace and cache; original coherent seed7,586,865,704 bytes/29,968 files,hash-pinned in NGM_CACHE_IMPORTS.json.xz. Own compiled exports and final resource/source checks: NGM_RETENTION.json and NGM_HYGIENE.json. Retain the own cache. Every host proof/build scope admitted with exit0 AND allowed:true,6G/8G/no swap/64 tasks,one own scope at a time. Never touch shared infrastructure or sibling/session A worktrees.

All harnesses live outside the repository in a frozen scratch tree; only patch, scripts, references and receipts are committed. Before each Kani run the offline resolved graph matches the frozen lock,afterward the lock hash is unchanged,and deployed features/KMX hashes are checked. The job changes no shipped source. ELF rebuild trigger did not fire; default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 are inherited pins,not fresh rebuilds. No wallet/key action.
''')
p=E/'NGM_EDGES.json';x=read(p.name);x['open_edges']=[dict(caller=g['function'],callee=c,status='OPEN parent composition',reason='SAME-call source/model/domain composition not established by fragments')for g in graph if g['row']in ['TX2:114','TX2:115','TX2:116','TX2:119']for c in g['callees']];x['no_parent_promotion']=True;p.write_text(json.dumps(x,indent=2)+'\n')
p=E/'NGM_LEDGER_DELTA.json';x=read(p.name);x['validator_checks_added']+=['all173 charged attempts and fixed budgets','timeouts excluded without native credit','full reference Result/acceptance and eight-error codec','typed arbitrary-prestate dot observations and induction remain OPEN pending adopted-model association','source inputs retained once by SHA256','no shipped changes / no ELF rebuild trigger'];p.write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(status='packet finalized',remaining=len(remaining),new_closed_rows=sorted(closed),attempts=len(receipts))))
