#!/usr/bin/env python3
"""Audit receipt/source integrity and write the final measured handoff; no builds."""
import csv,hashlib,json,pathlib,re,subprocess
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-runjoin10-20261027'
rows=sorted([json.loads(p.read_text()) for p in e.glob('receipt-*.json')],key=lambda r:r['attempt'])
accepted=[r for r in rows if r['accepted']];used=sorted(int(p.stem.split('-')[1]) for p in e.glob('used-*.json'))
assert len(used)==len(set(used)) and all(39000<=i<=39299 for i in used)
assert sum(r.get('exit') is not None for r in rows)==100
assert all(r.get('swaps')==0 for r in rows if r.get('exit') is not None)
assert all('TrustAudit10' in r['target'] for r in rows[-3:])
assert all(r['accepted'] for r in rows[-3:]),'Focused audit failed; report retained error, never claim it passed'
bad=[]
for r in accepted:
 assert hashlib.sha256((e/r['source_snapshot']).read_bytes()).hexdigest()==r['source_sha256']
 for line in r['axioms']:
  m=re.search(r'depends on axioms: \[([\s\S]*?)\]',line)
  if m and not {x.strip() for x in m[1].split(',')} <= {'propext','Classical.choice','Quot.sound'}:bad.append([r['attempt'],line])
assert not bad,bad
active=[]
for p in sorted((root/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RunJoin_*.lean')):
 old=subprocess.run(['git','cat-file','-e','ab9f1bfb8f:'+str(p.relative_to(root))],capture_output=True)
 if old.returncode==0:continue
 sha=hashlib.sha256(p.read_bytes()).hexdigest();good=[r['attempt'] for r in accepted if r['target']=='R1Z/'+p.stem and r['source_sha256']==sha]
 assert good,(p,'no accepted matching source')
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b|set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text()),p
 active.append(dict(path=str(p.relative_to(root)),sha256=sha,accepted_receipts=good))
unchanged=[]
for name in ['PV_RunJoin_TrustItems','PV_RunJoin_TrustEndpoint','PV_RunJoin_TrustLedger','PV_RunJoin_Deployed','PV_RunJoin_Boundary','PV_RunJoin_JoinedCausalHeadline']:
 p=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'/(name+'.lean');prior=subprocess.check_output(['git','show','ab9f1bfb8f:'+str(p.relative_to(root))])
 assert p.read_bytes()==prior,p
 unchanged.append(dict(path=str(p.relative_to(root)),sha256=hashlib.sha256(prior).hexdigest()))
changed=subprocess.check_output(['git','diff','--name-only','ab9f1bfb8f','HEAD','--','crates','programs'],text=True).splitlines()
assert changed==['crates/aspis-statement/src/pool_v1/pair_trace_pv_runjoin8_roots.rs'],changed
kani=json.loads((e/'kani-summary.json').read_text());assert len(kani)==6 and all(r['exit']==0 and r['successful'] and r['swaps']==0 for r in kani)
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
audit=dict(base='ab9f1bfb8fe9b976ad84169b2c10777439b098a7',checked_revision=revision,active_sources=active,unchanged_records_and_headline=unchanged,changed_crates_or_programs=changed,accepted_axiom_violations=bad,T_fields=['entropy_law','entropy_kernel','observation'],record_counts=dict(runtime_boundary=[2,2],fields=[8,8],residuals=[6,6]))
(e/'final-source-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
refs=json.loads((e/'sibling-pins.json').read_text());original={x['module'].replace('.','/'):x for x in json.loads((e/'original25-plan.json').read_text())}
origins=[]
for r in rows:
 origin=original.get(r['target'],{}).get('source_revision')
 if origin is None:origin=refs['codex/pv-l2-sim-20261026'] if r['target'].startswith('R1Z/PV_L2_') else r['source_revision'] if r['target'].startswith('R1Z/PV_RunJoin_') else refs['research']
 snapshot=(e/r['source_snapshot']).read_bytes()
 candidates=list(dict.fromkeys([origin,r['source_revision'],revision]))
 verified=None
 for candidate in candidates:
  if candidate is None:continue
  result=subprocess.run(['git','show',candidate+':docs/research/v8-r0-zk-20261009/lean/'+r['target']+'.lean'],capture_output=True)
  if result.returncode==0 and result.stdout==snapshot:verified=candidate;break
 origins.append(dict(attempt=r['attempt'],target=r['target'],worker_revision=r['source_revision'],source_origin_revision=verified,source_sha256=r['source_sha256'],source_was_uncommitted=r['source_was_uncommitted'],accepted=r['accepted'],origin_verified_by_git_bytes=verified is not None))
(e/'source-origins.json').write_text(json.dumps(origins,indent=2)+'\n')
summary=dict(lean_charged=len(rows),lean_accepted=len(accepted),lean_rejected=len(rows)-len(accepted),refusals=len(list(e.glob('refusal-*.json'))),kani_runs=len(kani),kani_successes=len(kani),lean_wall_seconds=sum(r.get('wall_seconds',0) for r in rows),lean_peak_rss_bytes=max(r['peak_rss_bytes'] for r in rows),kani_wall_seconds=sum(r['wall_seconds'] for r in kani),kani_peak_aggregate_rss_bytes=max(r['peak_rss_bytes'] for r in kani),swaps=0,used_ids=used,next_id=max(used)+1,original_missing_objects_before=25,original_missing_objects_after=0,whole_deployed_rows_removed=0,proof_source_revision=revision)
(e/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
logs=subprocess.check_output(['git','log','--oneline','ab9f1bfb8f..HEAD'],text=True);(e/'COMMITS.txt').write_text(logs)
body=f'''# pv-runjoin10 final status — budget exhausted

Branch `codex/pv-runjoin-20261026`, entry `ab9f1bfb8f`. **Target not yet established.** Proof/audit source revision `{revision}`; the final evidence-only commit follows it. No push.

PackedPublic proves full source public-projection preservation under canonical normalization/path packing. PackedRecords identifies the exact same private record and gives reference-record admission under semantic public association. PackedBinding supplies a sufficient canonical-reference association, explicitly not installed as an actual returned transition. PackedDynamic consumes srcid6 admission through the dynamic dictionary, retaining shipped dictionary equality and public association. CompilerPayload proves that the compiler call ignores the supplied Input.compiled field and that two successful same-source return associations force equal payloads. These are source/interface results, not actual deployed selection/compiler-success proofs.

Constructed-candidate P remains **{{source public binding, trace}} → {{source public binding, trace}}**. Deployed compiler success, actual dictionary/selection/public association, admission installation, runtime/callback/store/initializer/complete-observer installation, complete outside-bad-event extracted trace, and source/artifact/coherent-release identity remain OPEN. **Zero whole deployed endpoint rows removed; no endpoint premise added, renamed or weakened.** Exact before/after statements: P-before-after.json and stage1-obstruction.md. Ledger accounting retains V038/V045/V047, V152–V154, V165–V167, V336–V339 and release/OS-failure rows unchanged; see ledger-accounting.json. Runtime/boundary **2→2**, fields **8→8**, residuals **6→6**. T is unchanged, with exactly entropy_law, entropy_kernel, observation. A/B remain unadopted.

Transfer **P ∧ T non-vacuity OPEN**; withdrawal **P ∧ T non-vacuity OPEN**, with T hypothetical. Stage2-obstruction.md retains every runtime/observer checklist item. Actual caller source inspection locates the supplied public/compiled arguments in RealR1_client and their test construction in r0_fixture::prepare; source hashes are in actual-fixture-source-pins.json. No convenient model is presented as the deployed fixture.

All **25 original missing F5/multiproof objects → 0**, compiled from pinned research HEAD into the shared launcher output and retained in the assigned own objects directory with preimage backups. The available L2 replay checks source-linked F3 retry/entropy/control, the exact-endpoint F5 model legs, joint-row bound, structural multiproof and partial recorded arithmetic/checker subroutine objects through F6IdentityRow. The complete checker is not claimed replayed. It does not construct native event producers or establish trace. Remaining source objects are inventoried in l2-final-cache.json. No coherent frozen-release manifest replay is claimed.

Validation: **100/100 Lean attempts: {len(accepted)} accepted, {len(rows)-len(accepted)} rejected; 6/6 Kani successful**. IDs **{used[0]}–{used[-1]}** consumed once; **{summary['refusals']}** uncharged reservation refusals observed required waits and fresh IDs. Final three charged attempts are the focused trust audit. Lean wall total **{summary['lean_wall_seconds']:.2f}s**, peak RSS **{summary['lean_peak_rss_bytes']}B**; Kani wall total **{summary['kani_wall_seconds']:.4f}s**, aggregate peak RSS **{summary['kani_peak_aggregate_rss_bytes']}B**; **swap 0 throughout**. Accepted axiom lists are subsets of `[propext, Classical.choice, Quot.sound]`. The rejected draft's recovery output is not accepted.

Six new source parent cells 11,12,14,15,16,17 passed using the retained unchanged Kani configuration: **19/21** combined cells; 18 and 19 remain. These checks are not full compiler success or shipped dynamic-mapper equality. The prior srcid6 handoff's timed-out mapper checks are not credited.

| Final focused target | ID | Exit | Wall | Peak RSS bytes | Swap |
|---|---:|---:|---:|---:|---:|
'''
for r in rows[-3:]:body+=f"| {r['target'].split('/')[-1]} | {r['attempt']} | {r['exit']} | {r['wall_seconds']:.2f}s | {r['peak_rss_bytes']} | {r['swaps']} |\n"
body+='''
Every target/exit/wall/RSS/swap/revision/source-hash/full-axioms result is retained in receipt-index.tsv, receipt JSONs and raw logs. Source origins distinguish pinned read-only source revisions from the worker revision and source snapshots. final-source-audit.json verifies accepted current proof hashes and unchanged original records/headline. Own-object hashes are in own-object-index.json. The only crate change is the existing cfg(kani) child; production bodies and ELF pins are unchanged. Kani compiler target cache and identifiable owned solver scratch were removed after receipts. No wallet/account key was created or destroyed.

Stopped only because both allocations are exhausted. No checked ROW counterexample was found. Next deliverable: prove actual source dictionary/mapper correspondence and actual SAME selected compiler success with the returned transition/public association at r0_fixture::prepare / the D162 proof-account caller, then install the real Runtime/Boundary and complete native/extracted event producers for each fixture. Complete remaining source objects, root cells 18/19 and coherent release provenance/replay afterward. Branch commits are in COMMITS.txt.
'''
(e/'REPORT.md').write_text(body)
print(json.dumps(summary))
