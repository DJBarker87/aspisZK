from pathlib import Path
import subprocess,json,re,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxio-20261028'
n=int(sys.argv[1]);assert 35800<=n<=35899
code='''from pathlib import Path
import json,re,os
b=Path('/home/dombarker/project-offloads');n=ATTEMPT;rx=re.compile(r'(?<![0-9])'+n+r'(?![0-9])');matches=[]
p=b/'r1-privacy-build-integration-20261019/evidence/sent.txt'
sent=[s for s in p.read_text().splitlines() if re.search(r' J '+n+r' ',s)]
roots=[b/'aspis-fs-generic-20261006/evidence']+list(b.glob('codex-pv-*'))
for root in roots:
 for d,dirs,files in os.walk(root):
  depth=len(Path(d).relative_to(root).parts)
  dirs[:]=[x for x in dirs if x not in ['target','.git','lean-objects','objects','lean-sources','sources','node_modules'] and depth<4]
  for name in dirs+files:
   if rx.search(name):matches.append(str(Path(d)/name))
print(json.dumps(dict(id=int(n),host_roots=list(map(str,roots)),sent=sent,receipt_name_matches=matches,unused=not sent and not matches)))
'''.replace('ATTEMPT',repr(str(n)))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
j=json.loads(r.stdout)
files=subprocess.check_output(['rg','--files','evidence'],cwd=R,text=True).splitlines()
j['local_prior_receipts']=[p for p in files if re.search(r'(?<!\d)'+str(n)+r'(?!\d)',p)]
j['unused']=j['unused'] and not j['local_prior_receipts']
(E/f'{n}-id-preflight.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j))
assert j['unused']
