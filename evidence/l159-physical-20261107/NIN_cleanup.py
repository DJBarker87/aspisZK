"""Delete only owned rebuildable artifacts AFTER export retention verification."""
from pathlib import Path
import json,shutil,subprocess
B=Path.cwd();assert B.name=='codex-cx-l159-physical-20261107'
r=json.loads((B/'NIN_RETENTION.json').read_text());assert r['status']=='VERIFIED_BEFORE_CLEANUP'
cache=Path(r['cache_retained']);assert cache.is_dir()and cache.parent.name=='codex-cx-carriers-bind-cache-20261104'
removed=[]
for n in ['NIN_objects','NIN_native','NIN_tmp']:
 p=B/n
 if p.exists():
  size=sum(q.stat().st_size for q in p.rglob('*')if q.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
assert cache.is_dir()and (cache/'NIN_exports_20261107').is_dir()
x=dict(status='OWN_REBUILDABLE_OUTPUTS_REMOVED_CACHE_RETAINED',removed=removed,cache_retained=str(cache),disk=subprocess.check_output(['df','-h',str(B)],text=True),print_axioms='N/A: retention-verified cleanup; no prover replay or key/account operation')
(B/'NIN_HOST_END.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x))
