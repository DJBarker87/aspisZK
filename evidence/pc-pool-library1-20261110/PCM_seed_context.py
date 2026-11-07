"""Copy the non-quarantined retained closure into the PCM cache; never hardlink."""
from pathlib import Path
import json,lzma,subprocess,hashlib
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-pc-pool-library1-cache-20261110'
meta=json.loads(lzma.open(E.parent/'lib-20261111/LIB_BUNDLE_CLOSURE_PINS.json.xz').read())
selected=meta['objects']; blocked=[];allowed=[]
for r in selected:
 if 'codex-cx-tx2-entry5-20261110' in r['path']:blocked.append(r)
 else:allowed.append(r)
(E/'PCM_BLOCKED_CONTEXT.json').write_text(json.dumps(dict(reason='Explicit entry5 inheritance exclusion; clarification pending',objects=blocked),indent=1)+'\n')
# A root is selected only once; sidecar files are named from the pinned path.
rows=[]
for r in allowed:
 module=r['module'];suffix=r['path'].rsplit(module.replace('.','/'),1)
 assert len(suffix)==2,r
 rows.append(dict(source=r['path'],relative=module.replace('.','/')+suffix[1],sha256=r['sha256'],bytes=r['bytes']))
code='''from pathlib import Path
import shutil,hashlib,json,lzma
b=Path(B);assert shutil.disk_usage(b).free>=40_000_000_000
out=[]
for r in rows:
 src=Path(r['source']);dst=b/'PCM_context'/r['relative'];dst.parent.mkdir(parents=True,exist_ok=True)
 assert hashlib.sha256(src.read_bytes()).hexdigest()==r['sha256'],str(src)
 if dst.exists():assert hashlib.sha256(dst.read_bytes()).hexdigest()==r['sha256'],str(dst)
 else:shutil.copy2(src,dst)
 assert hashlib.sha256(dst.read_bytes()).hexdigest()==r['sha256']
 out.append(dict(r,destination=str(dst)))
p=b/'PCM_CONTEXT_IMPORTS.json.xz';p.write_bytes(lzma.compress(json.dumps(out).encode(),preset=1))
print(json.dumps(dict(files=len(out),bytes=sum(r['bytes'] for r in out),manifest_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),disk=shutil.disk_usage(b)._asdict())))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nrows='+repr(rows)+'\n'+code,text=True,capture_output=True)
(E/'PCM_CONTEXT_COPY.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stderr
(E/'PCM_CONTEXT_COPY.json').write_text(r.stdout)
print(r.stdout.strip())
