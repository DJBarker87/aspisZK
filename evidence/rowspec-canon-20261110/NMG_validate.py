from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).resolve().parent
attempts=[json.loads(l) for l in (E/'NMG_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({x['attempt'] for x in attempts})==len(attempts)
fields=['module','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms','deps_fingerprint']
for row in attempts:
 rc=json.loads((E/row['full_receipt']).read_text());assert all(k in rc for k in fields)
 assert rc['limits']==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64']))
 ad=json.loads((E/(rc['attempt']+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 for n,sha in rc['source_hashes'].items():assert hashlib.sha256((E/rc['attempt']/'sources'/n).read_bytes()).hexdigest()==sha,(rc['attempt'],n)
 for raw in rc['print_axioms'] if isinstance(rc['print_axioms'],list) else []:
  if rc['exit_status']==0:assert 'sorryAx' not in raw and all(a in ['propext','Classical.choice','Quot.sound'] for a in re.findall(r'\[([^]]*)\]',raw)[0].split(', ')) if '[' in raw else True
comparison=json.loads(lzma.decompress((E/'NMG_INHERITED_COMPARISON.json.xz').read_bytes()));assert not comparison['unmatched']
pairs=0
for p in E.rglob('*.xz'):
 dest=p.with_suffix('.sha256')
 raw=lzma.decompress(p.read_bytes());sha=hashlib.sha256(raw).hexdigest()
 if dest.exists():assert dest.read_text().strip().split()[0]==sha,str(p)
 else:dest.write_text(sha+'\n')
 pairs+=1
for row in json.loads((E/'NMG_FROZEN_INPUTS.json').read_text()):assert hashlib.sha256((E.parents[1]/row['snapshot']).read_bytes()).hexdigest()==row['sha256']
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000];assert not large,large
assert not list(E.rglob('__pycache__'))
queue=[json.loads(l) for l in (E/'NMG_QUEUE.jsonl').read_text().splitlines()] if (E/'NMG_QUEUE.jsonl').exists() else []
results=[json.loads((E/'NMG_audit'/q['mode']/'result.json').read_text()) for q in queue if q['has_result']]
flat=[x for r in results for x in r['results']];expected=json.loads((E/'NMG_AUDIT_ROOTS.json').read_text())['roots']
scan=json.loads((E/'NMG_audit/scan/result.json').read_text());fixtures=json.loads((E/'NMG_audit/fixtures/result.json').read_text())
fixture_expected={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[]}
assert {r['root']:r['walked_axioms'] for r in fixtures['results']}==fixture_expected
assert all(r['equal'] for r in fixtures['results'])
report=dict(status='INCOMPLETE: canonical full-strength RowSpecs and comparisons not established',gate='INCOMPLETE',security_target_established=False,row_credit=0,full_child_packets_approved=[],budget=dict(numbered_slots=max(int(x['attempt'][-3:]) for x in attempts),actual_capped_scopes=len(attempts),allowed_Lean=100,Kani=0,extraction=0,prelaunch='NMG_L002 not submitted'),support_gate=dict(combined_import='NMG_L015 exit0',coherence_scan='NMG_L024 exit0',modules=17778,scan_pass=scan['exit_status']==0,fixtures=len(fixtures['results']),fixtures_pass=fixtures['exit_status']==0,raw_expected=len(expected),raw_completed=len(flat),raw_all_standard=all(set(x['walked_axioms'])<=set(['propext','Classical.choice','Quot.sound']) for x in flat),raw_complete=set(expected)=={x['root'] for x in flat}),collector_disagreements=[x for x in flat if not x['equal']],failed_attempts=[dict(attempt=x['attempt'],target=x['module'],exit=x['exit_status']) for x in attempts if x['exit_status']!=0],scope_wall_seconds=sum(x['wall_seconds'] for x in attempts),peak_rss_kib=max(int(x['peak_rss_kib']) for x in attempts),peak_cgroup_bytes=max(int(json.loads((E/x['full_receipt']).read_text())['cgroup_memory_peak_bytes']) for x in attempts),swaps=sum(int(x['swaps']) for x in attempts),compressed_pairs=pairs,inherited_objects_matched=len(comparison['matched']),new_selected_own_objects=len(comparison['new_own_objects']),frozen_source_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',no_shipped_change=True,trust_change=False,retained_runtime_items='ledger24 inventory unchanged',validation='Receipt/source/hash/limits/admission/compression checks pass; focused cached forest only, not cold release replay')
(E/'NMG_AUDIT.json').write_text(json.dumps(report,indent=1)+'\n')
print(json.dumps(dict(scopes=len(attempts),roots=len(flat),raw_complete=report['support_gate']['raw_complete'],raw_standard=report['support_gate']['raw_all_standard'],pairs=pairs,job_gate='INCOMPLETE')))
