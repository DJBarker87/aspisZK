"""Remove only this job's rebuildable object files/links after final verification.
Sources, receipts, other jobs' targets, and all wallet/key material are untouched.
"""
from pathlib import Path
import json,subprocess,shlex,hashlib
E=Path('evidence/pv-l1d-20261029');H='/home/dombarker/project-offloads/codex-pv-l1d-20261029'
assert json.loads((E/'final-validation.json').read_text())['compiler_starts']==100
code=r'''import pathlib,json,hashlib,sys
p=pathlib.Path(sys.argv[1]);assert str(p)=='/home/dombarker/project-offloads/codex-pv-l1d-20261029'
removed=[];suffixes=('.olean','.olean.private','.olean.server','.ilean','.ir','.so','.o','.bc','.c')
for name in ['objects','external']:
 root=p/name
 for q in sorted(root.rglob('*')):
  if q.is_symlink():
   removed.append(dict(path=str(q),kind='own cache link',target=str(q.readlink())));q.unlink()
  elif q.is_file():
   assert q.name.endswith(suffixes),('unexpected non-cache file; retained',str(q))
   removed.append(dict(path=str(q),kind='own compiled scratch',sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size));q.unlink()
print(json.dumps(dict(removed=removed,only_own_cache=True,shared_targets_written=False,wallet_or_key_operations=False,sources_and_receipts_retained=True)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)+' '+shlex.quote(H)],text=True,capture_output=True)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);x['final_validation_sha256']=hashlib.sha256((E/'final-validation.json').read_bytes()).hexdigest();(E/'cache-cleanup.json').write_text(json.dumps(x,indent=2)+'\n')
p=Path('/tmp/pv-l1d-chunk-host.py')
if p.exists():p.unlink()
print('Removed own cache artifacts/links:',len(x['removed']))
