from pathlib import Path
import json,re,hashlib,subprocess,collections
E=Path(__file__).resolve().parent;root=E.parent.parent
rows=[json.loads(l) for l in (E/'NCJ_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({r['attempt'] for r in rows})==len(rows)
assert sum(r['kind']=='kani' for r in rows)==70
assert sum(r['kind']=='lean' for r in rows)==80
idx=json.loads((E/'NCJ_FINAL_INDEX.json').read_text());audit=json.loads((E/'NCJ_L080/receipt.json').read_text())
assert audit['exit_status']==0
idx['final_audit']={'receipt':'evidence/native-tx2w-20261028/NCJ_L080/receipt.json','source_sha256':hashlib.sha256((root/'lean/NCJ_FinalAudit.lean').read_bytes()).hexdigest(),'axioms':audit['print_axioms']}
idx['copy_laws_location']='lean/NCJ_FinalAudit.lean; checked L080; historical standalone source relocated to evidence'
for m,r in idx['green_modules'].items():assert hashlib.sha256((root/'lean'/(m+'.lean')).read_bytes()).hexdigest()==r['source_sha256']
for p in (root/'lean').glob('NCJ_*.lean'):
 s=p.read_text();assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth|allowUnsafeReducibility)',s),p
for r in rows:
 if r['kind']=='lean' and r['exit_status']==0:
  for a in r['print_axioms']:
   if 'depends on axioms:' in a:
    names=a.split('depends on axioms:')[1].strip().strip('[]').split(',')
    assert set(n.strip() for n in names)<=set(['propext','Classical.choice','Quot.sound'])
for i in range(1,71):
 g=json.loads((E/f'NCJ_K{i:03}-graph-check.json').read_text())
 assert g['exact_frozen_resolved_graph_match'] and g['lock_unchanged']
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
# Human-readable outcome classes preserve expected negative failures.
k=[]
for r in rows:
 if r['kind']!='kani':continue
 a=r['attempt'];s=(E/a/'stdout.log').read_text()
 kind='compile_error' if 'could not compile' in s else 'timeout' if 'timed out' in s.lower() or 'VERIFICATION:- TIMEOUT' in s else 'pass' if r['exit_status']==0 else 'negative_failed'
 k.append({'attempt':a,'outcome':kind,'exit_status':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':r['peak_rss_kib'],'swaps':r['swaps']})
(E/'NCJ_FINAL_INDEX.json').write_text(json.dumps(idx,indent=2)+'\n')
(E/'NCJ_FINAL_VALIDATION.json').write_text(json.dumps({'kani_attempts':70,'lean_attempts':80,'kani_outcomes':dict(collections.Counter(x['outcome'] for x in k)),'lean_green':sum(r['kind']=='lean' and r['exit_status']==0 for r in rows),'source_matched_green_modules':len(idx['green_modules']),'axioms_standard_only':True,'frozen_graph_checks':70,'unchanged_lock_checks':70,'no_oversized_files':True,'native_details':k},indent=2)+'\n')
print('Final validation passed',collections.Counter(x['outcome'] for x in k))
