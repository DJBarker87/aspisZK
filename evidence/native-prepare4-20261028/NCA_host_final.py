"""Read-only final inherited-object verification; never rewrites the retained cache."""
from pathlib import Path
import subprocess,json,shlex,time
E=Path(__file__).resolve().parent
assert not (E/'NCA_ACTIVE.json').exists()
baseline=json.loads((E/'NCA_CACHE_IMPORTED.json').read_text())
library=json.loads((E/'NCA_LIBRARY_PIN.json').read_text())
code='''from pathlib import Path
import json,hashlib
x=json.loads(INPUT)
def pin(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(8*1024*1024):h.update(b)
 return dict(sha256=h.hexdigest(),bytes=p.stat().st_size)
c=Path(x['baseline']['cache']);errors=[]
for name,old in x['baseline']['objects'].items():
 p=c/name
 if not p.is_file() or pin(p)!=old:errors.append(name)
lerrors=[]
for name,old in x['library'].items():
 p=Path(name)
 if not p.is_file() or pin(p)!=old:lerrors.append(name)
print(json.dumps(dict(cache=str(c),inherited_count=len(x['baseline']['objects']),inherited_errors=errors,library_count=len(x['library']),library_errors=lerrors,own_objects={p.name:pin(p) for p in c.glob('NCA_*.olean')},cache_retained=True,read_only=True),indent=2))
assert not errors and not lerrors
'''.replace('INPUT',repr(json.dumps(dict(baseline=baseline,library=library))))
argv=['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','-o','ControlMaster=auto','-o','ControlPersist=600','-o','ControlPath=/private/tmp/NCA_ssh_%C','dombarker@100.108.41.90','python3']
for i in range(11):
 r=subprocess.run(argv,input=code,capture_output=True,text=True)
 (E/f'NCA_HOST_FINAL-{i}.log').write_text(r.stdout+r.stderr)
 if r.returncode!=255:break
 if i<10:time.sleep(60)
assert r.returncode==0,r.stderr
(E/'NCA_HOST_FINAL.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
print('Inherited objects and resolved Aeneas objects unchanged; own cache retained')
