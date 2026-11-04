from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code=r'''from pathlib import Path
import hashlib,json,shutil
base=Path('/home/dombarker/project-offloads');dest=base/'codex-cx-pool-prefix-cache-20261104/NGG_headline'
existing=[dest,base/'codex-cx-pool-prefix-cache-20261104',base/'codex-cx-sound-int2-20261025',base/'codex-cx-sound-int2-20261025/objects']
source=base/'codex-cx-ledger7-cache-20261104/NFX_priority'
assert shutil.disk_usage(base).free>20*1024**3
rows=[]
for p in source.rglob('*'):
 if not p.is_file():continue
 rel=p.relative_to(source)
 # Retained cache fallbacks resolve unchanged dependencies; copy missing module artifacts.
 if any((r/rel).exists() for r in existing):continue
 q=dest/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 rows.append(dict(source=str(p),destination=str(q),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
print(json.dumps(dict(classification='additional retained NFX priority objects; copied read-only; no proof credit',imports=rows,bytes=sum(r['bytes'] for r in rows))))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'NGG_HEADLINE_CLOSURE_PINS.json').write_text(r.stdout)
d=json.loads(r.stdout);print(json.dumps(dict(files=len(d['imports']),bytes=d['bytes'])))
