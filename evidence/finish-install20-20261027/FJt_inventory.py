"""Read-only source/object inventory of this task and inherited terminal modules."""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
files=sorted([*R.glob('lean/FJt_*.lean'),*R.glob('lean/FJq_*.lean'),*R.glob('lean/FJn_*.lean'),R/'lean/IDa_Deployed.lean',R/'lean/ARX_Root.lean'])
mods=[p.stem for p in files]
code="""from pathlib import Path
import hashlib,json
B=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
mods="""+repr(mods)+"""
out={}
for m in mods:
 row={}
 for suffix in ['.lean','.olean']:
  p=B/(m+suffix)
  row[suffix]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) if p.exists() else None
 out[m]=row
print(json.dumps(out))
"""
r=subprocess.run(['ssh','dombarker@100.108.41.90',"python3 - <<'PY'\n"+code+"PY"],check=True,text=True,capture_output=True)
remote=json.loads(r.stdout)
for p in files:
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 assert remote[p.stem]['.lean'] is not None,p
 assert remote[p.stem]['.lean']['sha256']==h,p
 remote[p.stem]['local_path']=str(p.relative_to(R))
 remote[p.stem]['source_match']=True
 if p.stem.startswith('FJt_'):assert remote[p.stem]['.olean'] is not None,p
(E/'FJt_SOURCE-OBJECT-MANIFEST.json').write_text(json.dumps(remote,indent=2)+'\n')
print(json.dumps(dict(source_count=len(files),own_source_count=sum(p.stem.startswith('FJt_') for p in files),all_host_local_sources_match=True)))
