from PCC_formal import *
import base64,lzma
files={n:(E/n).read_text() for n in ['PCC_AUDIT_ROOTS.json','PCC_AUDIT_MODULES.json','PCC_EXPECTED_IMPORTS.jsonl','PCC_final_one.py']}
for i,mode in [(66,'fixtures'),(67,'proof0'),(68,'scan')]:
 a=f'PCC_L{i:03d}'
 r=run(a,'audit',mode,['python3','PCC_final_one.py',mode,a],files)
 rr=ssh('python3',f'''from pathlib import Path
import json,lzma,base64,hashlib
b=Path({B!r})/'PCC_final_audits'/{a!r};out=[]
for p in b.rglob('*'):
 if not p.is_file():continue
 raw=p.read_bytes();out.append(dict(name=p.name,sha256=hashlib.sha256(raw).hexdigest(),data=base64.b64encode(lzma.compress(raw)).decode()))
print(json.dumps(out))
''');assert rr.returncode==0,rr.stderr
 for x in json.loads(rr.stdout):
  raw=lzma.decompress(base64.b64decode(x['data']));assert sha(raw)==x['sha256']
  p=E/a/'PCC_audit_outputs'/x['name'];p.parent.mkdir(parents=True,exist_ok=True)
  if p.suffix=='.json':p.write_bytes(raw)
  else:p.with_name(p.name+'.xz').write_bytes(base64.b64decode(x['data']));p.with_name(p.name+'.sha256').write_text(x['sha256']+'\n')
 assert r['exit_status']==0,(a,'No unchanged rerun')
