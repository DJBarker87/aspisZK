"""Remove only this job's rebuildable outputs after verified proof export."""
from pathlib import Path
import json,hashlib,subprocess,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-carriers-bind-20261105')
C=Path('/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104')
exports=json.loads((B/'NGS_EXPORT.json').read_text());assert len(exports)==6
for row in exports:
 p=Path(row['path']);assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
processes=subprocess.check_output(['ps','-u','dombarker','-o','pid=,args='],text=True)
active=[l for l in processes.splitlines() if str(B) in l and any(x in l for x in ['/bin/lean ','/bin/leanc ','NGS_native/NGS_'])];assert not active,active
inventory=[]
for n in ['NGS_objects','NGS_native','NGS_tmp']:
 p=B/n;files=[x for x in p.rglob('*') if x.is_file()]
 inventory.append(dict(directory=str(p),files=len(files),bytes=sum(x.stat().st_size for x in files)))
 if p.is_dir():shutil.rmtree(p)
cache=[x for x in C.rglob('*') if x.is_file()]
out=dict(removed_owned_rebuildable_outputs=inventory,cache_retained=str(C),cache_files=len(cache),cache_bytes=sum(x.stat().st_size for x in cache),exports_verified=len(exports),active_owned_provers=active,disk=subprocess.check_output(['df','-h','/'],text=True))
(B/'NGS_CLEANUP.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
