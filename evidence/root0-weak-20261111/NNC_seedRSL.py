from NNC_transport import *
import hashlib
admission('NNC_S002')
r=ssh('python3',f'''from pathlib import Path
import shutil,json,hashlib
b=Path({B!r});src=b.parent/'codex-cx-tx2-owned-20261111/NMS_RSL_objects';out=b/'NNC_seed/RSL';rows=[]
for p in sorted(src.rglob('*')):
 if not p.is_file():continue
 q=out/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:shutil.copy2(p,q)
 rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
print(json.dumps(dict(files=rows)))
''');assert r.returncode==0,r.stderr
(E/'NNC_RSL_SEED.json').write_text(r.stdout)
p=E/'NNC_ENV.json';x=json.loads(p.read_text());paths=x['LEAN_PATH'].split(':');paths.insert(1,B+'/NNC_seed/RSL');x['LEAN_PATH']=':'.join(dict.fromkeys(paths));p.write_text(json.dumps(x,indent=1)+'\n')
print(json.dumps(dict(files=len(json.loads(r.stdout)['files']))))
