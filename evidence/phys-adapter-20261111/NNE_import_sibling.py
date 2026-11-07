from NNE_transport import *
import hashlib
rev=subprocess.check_output(['git','rev-parse','codex/cx-stage-wrap-20261107'],text=True).strip()
mods=['NMV_RslLaws','NMV_RslSnapshots','NMV_RslDomain','NMV_RslFold']
rows=[]
for m in mods:
 raw=subprocess.check_output(['git','show',rev+':evidence/stage-wrap-20261111/'+m+'.lean'])
 p=E/('NNE_IMPORTED_'+m+'.lean.txt');p.write_bytes(raw)
 rows.append(dict(module=m,source_revision=rev,sha256=hashlib.sha256(raw).hexdigest(),archive=p.name))
admission('NNE_S003')
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});rows=json.loads({json.dumps(rows)!r});src=b.parent/'codex-cx-stage-wrap-20261111'
for x in rows:
 p=src/'NMV_generated'/(x['module']+'.lean');assert hashlib.sha256(p.read_bytes()).hexdigest()==x['sha256'],x
 for z in (src/'NMV_objects').glob(x['module']+'.*'):
  q=b/'NNE_seed/RSL'/z.name;shutil.copy2(z,q);x.setdefault('objects',[]).append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
print(json.dumps(rows))
''');assert r.returncode==0,r.stderr
(E/'NNE_SIBLING_IMPORTS.json').write_text(r.stdout)
print('imported',len(rows),'committed sibling modules')
