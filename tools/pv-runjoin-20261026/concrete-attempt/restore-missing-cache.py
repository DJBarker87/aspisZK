# Reuse the predecessor's retained exact cache. Never overwrite an object.
from pathlib import Path
import hashlib,json,shutil
root=Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026')
src=root/'objects-final-9297a12175/R1Z'
dst=Path('/home/dombarker/project-offloads/aspis-joint-20261019/objects/R1Z')
rows=[]
for name in ['PV_RunJoin_UnifiedRetry','PV_RunJoin_SourceBinding','PV_RunJoin_CallerWorld','PV_RunJoin_KernelCompletion']:
    p=src/(name+'.olean');q=dst/p.name
    if q.exists():
        rows.append(dict(module=name,action='retained existing',sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
    else:
        shutil.copyfile(p,q)
        rows.append(dict(module=name,action='restored missing predecessor cache',sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
(root/'evidence/cache-23401.json').write_text(json.dumps(rows,indent=2)+'\n')
