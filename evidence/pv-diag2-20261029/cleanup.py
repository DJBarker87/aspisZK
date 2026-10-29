"""Record own compiled artifact hashes, then remove only own rebuildable scratch.
No wallet, account, nonce-store or key files are created or removed.
"""
from pathlib import Path
import hashlib,json,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');assert D.name=='codex-pv-diag2-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for name in ['PV_DIAG2_Effects','PV_DIAG2_Retry','PV_DIAG2_Exit','PV_DIAG2_Process']:
 o=D/'objects'/(name+'.olean')
 if o.is_file():rows.append(dict(module=name,object_sha256=sha(o),object_bytes=o.stat().st_size,credit='independent core' if name.endswith('Effects') else 'development model only; h7 cone blocked'))
audit=D.parent/'aspis-joint-20261019/objects/PV_DIAG2_CoreAudit.olean';assert audit.is_file();rows.append(dict(module='PV_DIAG2_CoreAudit',object_sha256=sha(audit),object_bytes=audit.stat().st_size,credit='independent Init-only audit 62797'))
exe=D/'error-exit';removed=[]
if exe.is_file():
 removed.append(dict(path=str(exe),sha256=sha(exe),bytes=exe.stat().st_size,kind='own finite-probe executable'));exe.unlink()
obj=D/'objects'
if obj.is_dir():shutil.rmtree(obj);removed.append(dict(path=str(obj),kind='own compiled scratch and symlinks only; symlink targets retained'))
(D/'cleanup.json').write_text(json.dumps(dict(artifact_pins=rows,removed=removed,shared_objects_removed=False,key_operations=0),indent=2)+'\n');print('retained',len(rows),'artifact pins; own executable and private object scratch removed')
