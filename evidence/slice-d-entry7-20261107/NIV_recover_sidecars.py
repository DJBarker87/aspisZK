from NIV_transport import *
rs=list(map(json.loads,(E/'NIV_ATTEMPTS.jsonl').read_text().splitlines()));ids=[r['attempt']for r in rs if r['attempt'].startswith('NIV_K')]
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});out={{}}
for a in {ids!r}:
 for p in b.glob(a+'-*.json'):
  if p.is_file():out[p.name]=p.read_text()
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
new=0
for n,s in json.loads(r.stdout).items():
 p=E/n
 if p.exists():assert p.read_text()==s,n
 else:p.write_text(s);new+=1
print(json.dumps(dict(recovered_sidecars=new,attempts=len(ids))))
