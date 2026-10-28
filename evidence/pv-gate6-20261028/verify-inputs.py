"""Post-run byte integrity check against pre-build exact Git input manifests."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
sources={w:json.loads((E/name).read_text()) for w,name in [('candidate','source-identity.json'),('control','control-source-identity.json')]}
code='''from pathlib import Path
import json,hashlib,time
D=Path('/home/dombarker/project-offloads/codex-pv-gate6-20261028')
sources=SOURCES
roots={'candidate':D/'source','control':D/'combined/baseline/source'}
rows=[]
for w,s in sources.items():
 bad=[]
 for n,h in s['files'].items():
  p=roots[w]/n
  actual=hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
  if actual!=h:bad.append(dict(path=n,expected=h,actual=actual))
 rows.append(dict(side=w,revision=s['revision'],checked_files=len(s['files']),disagreements=bad,passed=not bad))
r=dict(utc=time.time(),rows=rows,passed=all(x['passed'] for x in rows),scope='Read-only comparison of every exported input against pre-build Git-verified hashes; generated output additions are not build inputs')
(D/'post-run-source-integrity.json').write_text(json.dumps(r,indent=2)+'\\n')
print(json.dumps(r))
'''.replace('SOURCES',repr(sources))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True)
print(r.stdout,r.stderr);r.check_returncode();x=json.loads(r.stdout);(E/'post-run-source-integrity.json').write_text(json.dumps(x,indent=2)+'\n');assert x['passed']
