from pathlib import Path
import json,hashlib,subprocess,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag8-20261029');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(D/'final-check.py'),'--post'],check=True)
rs=[json.loads(p.read_text()) for p in sorted(D.glob('lean*-receipt.json'))]
assert len(rs)==100 and {r['attempt'] for r in rs}==set(range(66000,66100))
for r in rs:
 assert r['admission_allowed'] is True and r['admission_exit']==0
 if r['exit']==0:
  assert 'sorryAx' not in r['print_axioms']
  for names in re.findall(r'depends on axioms: \[([^]]*)\]',r['print_axioms']):
   assert set(x.strip() for x in names.split(',')) <= {'propext','Classical.choice','Quot.sound'}
(D/'attempts.json').write_text(json.dumps(rs,indent=2)+'\n')
(D/'summary.json').write_text(json.dumps(dict(lean_attempts=len(rs),accepted=sum(r['exit']==0 for r in rs),rejected=[r['attempt'] for r in rs if r['exit']],native_scopes=6,kani=0,total_lean_wall_seconds=sum(r['wall_seconds'] for r in rs),peak_lean_rss_kib=max(int(r['peak_rss_kib']) for r in rs),swap=sum(int(r['swaps']) for r in rs),stop='100 Lean attempt budget exhausted; deployed target not established',endpoint_removed=0,endpoint_added=0,endpoint_weakened=0),indent=2)+'\n')
# Remove only this job's compiler products; keys and nonce/account state never
# existed in objects, and no source, shared object, receipt or cache is removed.
deleted=[]
for p in sorted((D/'objects').rglob('*')):
 if not p.is_file():continue
 assert not p.is_symlink()
 assert any(str(p).endswith(s) for s in ['.olean','.olean.server','.olean.private','.ir','.ilean'])
 deleted.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size));p.unlink()
(D/'cleanup.json').write_text(json.dumps(dict(deleted_compiler_products=deleted,keys_or_accounts_touched=False,shared_objects_touched=False),indent=2)+'\n')
print('attempts',len(rs),'accepted',sum(r['exit']==0 for r in rs),'compiler products removed',len(deleted))
