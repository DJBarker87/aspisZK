#!/usr/bin/env python3
"""Compile one owned proof through the retained, range-guarded J launcher."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,time
module,attempt,revision=sys.argv[1:]
assert re.fullmatch(r'[A-Za-z0-9_.]+',module)
assert 10600<=int(attempt)<=10699
W=Path(__file__).resolve().parent
root=W.parent
src=root/'sources'/(module.replace('.','/')+'.lean')
env=json.loads((W/'J.json').read_text())
paths=[root/'objects']+[Path(p) for p in env['LEAN_PATH'].split(':')]
def obj(m):
 return next((r/(m.replace('.','/')+'.olean') for r in paths if (r/(m.replace('.','/')+'.olean')).is_file()),None)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
imports=[]
for line in src.read_text().splitlines():
 hit=re.match(r'^\s*import\s+(.+)',line)
 if hit:imports.extend(hit[1].split('--')[0].split())
deps=[]
for m in imports:
 p=obj(m);assert p is not None,'missing dependency '+m
 deps.append((m,str(p),sha(p)))
# Lean 4.32 consumes split core artifacts too. The first attempt demonstrated
# that these were missing; fingerprint their presence/content, not a retry nonce.
core=[]
for n in ['Init.olean','Init.olean.server','Init.olean.private']:
 p=root/'objects'/n
 core.append((n,sha(p) if p.is_file() else None))
fp=hashlib.sha256(json.dumps(dict(imports=deps,core_artifacts=core),sort_keys=True).encode()).hexdigest()
output=root/'objects'/(module.replace('.','/')+'.olean')
assert not output.is_symlink(),'refuse to overwrite shared cache link'
cmd=['sh',str(W/'proof-launcher.sh'),attempt,module.replace('.','/'),'J','7000','8',fp]
start=time.monotonic();p=subprocess.run(cmd,text=True,capture_output=True)
evidence=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
receipt={'module':module,'attempt':'J'+attempt,'source_sha256':sha(src),'source_revision':revision,'dependencies':deps,'core_artifacts':core,'deps_fingerprint':fp,'command':cmd,'controller_exit':p.returncode,'controller_wall_seconds':time.monotonic()-start,'stdout':p.stdout,'stderr':p.stderr}
for stem,suffix in [('out','.log'),('time','.log'),('sha','.txt')]:
 f=evidence/(stem+'-'+attempt+suffix)
 if f.exists():receipt[stem]=f.read_text()
receipt['exit']=int(re.search(r'^exit=(\d+)$',receipt.get('out',''),re.M)[1]) if re.search(r'^exit=(\d+)$',receipt.get('out',''),re.M) else None
(root/'proof-evidence').mkdir(exist_ok=True)
(root/'proof-evidence'/('J'+attempt+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
(root/'proof-evidence'/('J'+attempt+'.lean.txt')).write_bytes(src.read_bytes())
print(p.stdout,p.stderr,flush=True)
sys.exit(0 if receipt['exit']==0 else 1)
