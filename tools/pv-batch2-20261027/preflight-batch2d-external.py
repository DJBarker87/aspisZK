from pathlib import Path
import subprocess,json,hashlib
E=Path('evidence/pv-batch2-20261027/batch2d')
b=subprocess.check_output(['git','show','research:evidence/pv-replay-20261027/receipts/external-object-manifest.json'])
rows=json.loads(b)
code='''import json,sys,hashlib,time
from pathlib import Path
rows=json.load(sys.stdin);bad=[]
for a in rows:
 p=Path(a['path']);sha=hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
 if sha!=a['object_sha256']:bad.append(dict(module=a['module'],path=str(p),expected=a['object_sha256'],actual=sha))
print(json.dumps(dict(checked=len(rows),mismatches=bad,epoch=time.time())))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+__import__('shlex').quote(code)],input=b,capture_output=True,check=True)
j=json.loads(r.stdout);j['authority']='research:evidence/pv-replay-20261027/receipts/external-object-manifest.json';j['manifest_sha256']=hashlib.sha256(b).hexdigest()
(E/'H4-library-verification.json').write_text(json.dumps(j,indent=2)+'\n');print(j);assert not j['mismatches']
