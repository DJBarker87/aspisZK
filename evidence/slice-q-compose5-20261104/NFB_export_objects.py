from NFB_remote import *
import json,hashlib
assert not (E/'NFB_ACTIVE.json').exists()
latest={}
for p in sorted(E.glob('NFB_L*/receipt.json')):
 r=json.loads(p.read_text());latest[r['module']]=r
rows=[]
for m,r in latest.items():
 if r['exit_status']!=0:continue
 a=r['attempt'];o=json.loads((E/a/'object.json').read_text())
 generated=json.loads((E/'NFB_GENERATED.json').read_text())
 src=E/(generated[m]['path'] if m in generated else m.replace('.','/')+'.lean')
 if not src.exists() or hashlib.sha256(src.read_bytes()).hexdigest()!=o['source_sha256']:continue
 rows.append(o)
a='NFB_EXPORT_OBJECTS';admit(a)
r=ssh(a,'python3',f'''from pathlib import Path
import shutil,hashlib,json
root=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose5-cache-20261029/NFB_exports_20261104');out=[]
for r in {rows!r}:
 p=Path(r['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'];q=root/(r['module'].replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==r['sha256']
 else:shutil.copy2(p,q)
 out.append(dict(r,destination=str(q)))
print(json.dumps(dict(exports=out,cache_never_deleted=True)))
''');assert r.returncode==0,r.stderr
(E/'NFB_FINAL_CACHE.json').write_text(r.stdout)
