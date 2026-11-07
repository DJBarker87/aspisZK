from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
load=lambda p:json.loads(p.read_text())
a=[json.loads(l)for l in(E/'NLQ_ATTEMPTS.jsonl').read_text().splitlines()]
manifest=load(E/'NLQ_AUDIT_ROOTS.json');required=set(manifest['roots']);results=[];children=[]
for p in sorted((E/'NLQ_audit').glob('batch*/proof*.json')):
 d=load(p);children.append(dict(path=str(p.relative_to(E)),**{k:d[k]for k in ['target','exit_status','wall_seconds','peak_rss_kib','swaps']}));results.extend(d['results'])
byroot={r['root']:r for r in results};missing=sorted(required-set(byroot));allowed={'Classical.choice','Quot.sound','propext'}
nonstandard=[r for r in results if set(r['walked_axioms'])-allowed];differences=[r for r in results if not r['equal']]
scanpath=E/'NLQ_LOADED_scan.jsonl';scan=[json.loads(l)for l in scanpath.read_text().splitlines()]if scanpath.exists()else[]
issues=[r for r in scan if r['dangling'] or r.get('duplicate_owners')or not r['imports_match']]
fixtures=load(E/'NLQ_audit/fixtures/fixtures.json')if (E/'NLQ_audit/fixtures/fixtures.json').exists()else{}
f=fixtures.get('results',[])
fixtures_good=len(f)==8 and all(bool(r['walked_axioms'])==r['root'].startswith('NEP_Planted.')for r in f)
combined=[r for r in a if r.get('module')=='NLQ_COMBINED_IMPORT'];scopes=[r for r in a if r.get('kind')=='audit']
scan_receipts=[r for r in scopes if r.get('module')=='scan']
baseline_known={r['root']:(r['collect_axioms'],r['walked_axioms'])for r in load(E.parent/'ledger22-20261110/NLO_AUDIT.json')['collect_axioms_disagreements']}
retained_nonzero=[]
for c in children:
 if c['exit_status']==0:continue
 detail=load(E/c['path']);diff=[r for r in detail['results']if not r['equal']]
 log=(E/c['path']).with_suffix('.log').read_text()
 accepted=c['exit_status']==1 and bool(diff) and all(baseline_known.get(r['root'])==(r['collect_axioms'],r['walked_axioms'])for r in diff) and log.count('raw graph disagrees with collectAxioms')==len(diff)
 c['retained_known_collector_exit']=accepted
 retained_nonzero.append(dict(target=c['target'],exit_status=c['exit_status'],accepted_under_ax2=accepted,differences=diff))
rawgood=bool(results)and not missing and not nonstandard and len(results)==len(byroot)and all(c['exit_status']==0 or c.get('retained_known_collector_exit',False)for c in children)
scan_good=bool(scan)and not issues and len(scan_receipts)==1 and scan_receipts[0]['exit_status']==0
combined_good=len(combined)==1 and combined[0]['exit_status']==0
pins=[load(E/r['attempt']/'NLQ_ProofDriver_BINARY_PIN.json')['sha256']for r in scopes if r.get('module','').startswith('batch')and(E/r['attempt']/'NLQ_ProofDriver_BINARY_PIN.json').exists()]
binary_coherent=bool(pins)and len(set(pins))==1
support_good=combined_good and rawgood and scan_good and fixtures_good and binary_coherent
baseline=load(E.parent/'ledger22-20261110/NLO_AUDIT.json')
d=dict(status='SUPPORT_CLOSURE_PASS'if support_good else'INCOMPLETE_OR_FAILED',security_target_established=False,full_composition_pass=False,support_closure_pass=support_good,combined='NLQ_COMBINED_IMPORT',combined_attempt=combined[0]['attempt']if combined else None,full_combined_audits_run=len(combined),headline='AspisR1.RPx_Deployed.deployed',required_roots=len(required),raw_root_count=len(results),all_required_raw_roots_present=not missing,missing_roots=missing,raw_standard_axioms_only=rawgood,nonstandard_roots=nonstandard,axioms=sorted(allowed),new_roots=load(E/'NLQ_AUDIT_PLAN.json')['new_roots'],collect_axioms_disagreements=differences,known_baseline_disagreements=baseline['collect_axioms_disagreements'],raw_authoritative_ruling='ax2; collector disagreements and original nonzero exits retained',retained_nonzero_audit_exits=retained_nonzero,scanner=dict(pass_=scan_good,modules=len(scan),dangling=sum(len(r['dangling'])for r in scan),duplicate_owners=sum(len(r.get('duplicate_owners',[]))for r in scan),import_mismatches=sum(not r['imports_match']for r in scan),cached_replicas=sum(len(r.get('cached_replicas',[]))for r in scan),receipt=scan_receipts[0]['attempt']if scan_receipts else None),fixtures=dict(passed=fixtures_good,results=f),same_optimized_proof_binary_sha256=sorted(set(pins)),proof_binary_coherent=binary_coherent,raw_children=children,resources=[{k:r.get(k)for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','limits','cgroup_memory_peak_bytes']}for r in a],cold_release_replay=False,inherited_baseline_audit='evidence/ledger22-20261110/NLO_AUDIT.json',inherited_raw_root_count=11174,closure_replay_reason='Full combined import and NFX module scan; fresh raw audit of added roots, headline and known collector disagreements; unchanged baseline raw audit retained by reference',row_promotions=[])
(E/'NLQ_AUDIT.json').write_text(json.dumps(d,indent=1)+'\n')
print(json.dumps(dict(status=d['status'],roots=len(results),missing=len(missing),nonstandard=len(nonstandard),collector_disagreements=len(differences),scan_pass=scan_good)))
