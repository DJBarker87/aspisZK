from pathlib import Path
import json,hashlib,os,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag11-20261029');P=D.parent/'codex-pv-diag10-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Read-only reuse: diag10's recursively checked runjoin/decoder cohort; no b3p cohort.
env=json.loads((P/'env-J.json').read_text());env['LEAN_PATH']=str(D/'objects')+':'+env['LEAN_PATH'];(D/'env-J.json').write_text(json.dumps(env,indent=2)+'\n')
rows=[]
for r in json.loads((P/'reuse.json').read_text())['rows'].values():
 assert sha(Path(r['path']))==r['sha256'];assert sha(Path(r['source']))==r['source_sha256'];rows.append(r)
for p in (P/'sources').glob('PV*.lean'):
 if p.stem.startswith('PV_DIAG10_Op227'):continue
 hits=[]
 for q in P.glob('lean*-receipt.json'):
  r=json.loads(q.read_text())
  if r.get('module')==p.stem and r['exit']==0 and r['source_sha256']==sha(p):hits.append(r)
 if hits:
  r=hits[-1];o=P/'objects'/(p.stem+'.olean');assert sha(o)==r['object_sha256']
  for dep,files in r['dependency_objects'].items():
   for f,h in files.items():assert sha(Path(f))==h,(p,dep)
  rows.append(dict(path=str(o),sha256=sha(o),source=str(p),source_sha256=sha(p),receipt=str(P/('lean'+str(r['attempt'])+'-receipt.json'))))
(D/'reuse.json').write_text(json.dumps(dict(rows=rows,checked=len(rows),authority='diag10 accepted read-only cohort; inherited recursive authority retained; no b3p imports'),indent=2)+'\n')
hits=[]
for root,dirs,files in os.walk(D.parent):
 p=Path(root)
 if p==D:dirs[:]=[];continue
 if len(p.relative_to(D.parent).parts)>=5:dirs[:]=[]
 dirs[:]=[d for d in dirs if d not in {'target','client-target','objects','lean-objects','actual-objects','sources','actual-sources','source','src','node_modules','.git','.lake','native-source','repo','frozen'}]
 for name in dirs+files:
  if re.search(r'(?<![A-Za-z0-9])670\d\d(?![A-Za-z0-9])',name):hits.append(str(p/name))
 for name in files:
  if name=='sent.txt':
   for line in (p/name).read_text().splitlines():
    fs=line.split()
    if len(fs)>2 and fs[2].isdigit() and 67000<=int(fs[2])<=67099:hits.append(str(p/name)+':'+line)
(D/'id-preflight.json').write_text(json.dumps(dict(range=[67000,67099],collisions=hits),indent=2)+'\n');assert not hits
print('reused',len(rows),'ID collisions',len(hits))
