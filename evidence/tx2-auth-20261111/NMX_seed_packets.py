from NMX_transport import *
import base64
admission('NMX_S002')
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});src=b.parent/'codex-cx-tx2-entry5-20261110/NMN_exports_20261110';rows=[]
for p in src.rglob('*'):
 if not p.is_file():continue
 q=b/'NMX_seed/NMN'/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:shutil.copy2(p,q)
 rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
print(json.dumps(rows))
''');assert r.returncode==0,r.stderr
(E/'NMX_PACKET_SEED.json').write_text(r.stdout)
env=json.loads((E/'NMX_ENV.json').read_text());parts=env['LEAN_PATH'].split(':');parts.insert(1,B+'/NMX_seed/NMN');env['LEAN_PATH']=':'.join(dict.fromkeys(parts));(E/'NMX_ENV.json').write_text(json.dumps(env,indent=1)+'\n')
