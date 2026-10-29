from pathlib import Path
import json,hashlib,os,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdeac-20261028')
P=D.parent/'codex-pv-rdea-20261028'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=[]
for n in ['actual-closure-final.json','physical-closure-final.json']:
 for r in json.loads((P/n).read_text()):
  assert sha(r['source'])==r['source_sha256'],r['module']
  assert sha(r['object'])==r['object_sha256'],r['module']
  rows.append(r)
# Both inherited cohorts must agree on shared names.
seen={}
for r in rows:
 if r['module'] in seen:assert seen[r['module']]['object_sha256']==r['object_sha256'],r['module']
 seen[r['module']]=r
E=json.loads((P/'private-env-J.json').read_text())
E['LEAN_PATH']=str(P/'actual-objects')+':'+E['LEAN_PATH']
roots=list(map(Path,E['LEAN_PATH'].split(':')))
external=json.loads((D.parent/'codex-pv-rdb1-20261028/external-object-manifest.json').read_text())
checks=[]
for r in external:
 rel=r['module'].replace('.','/')+'.olean'
 p=next((p/rel for p in roots if (p/rel).is_file()),None)
 assert p and sha(p)==r['object_sha256'],(r['module'],p)
 checks.append(dict(module=r['module'],path=str(p),sha256=sha(p)))
# Ensure resolution of every inherited project object is the recorded cohort.
for m,r in seen.items():
 rel=m.replace('.','/')+'.olean';p=next((p/rel for p in roots if (p/rel).is_file()),None)
 assert p and sha(p)==r['object_sha256'],(m,p)
(D/'env-J.json').write_text(json.dumps(E,indent=2)+'\n')
(D/'preflight.json').write_text(json.dumps(dict(external=checks,project=list(seen.values()),ok=True,void_inherited_attempt=60309,void_module='R1Z.PV_RDEA_CloneExecution',remedy='Recompile exact source privately under valid admission before consuming dependent laws.'),indent=2)+'\n')
# Read-only cross-job receipt scan of newly assigned ID block.
pat=re.compile(r'(?:^|[-_])(611\d\d)(?:[-_.]|$)');hits=[]
for job in D.parent.glob('codex-pv-*'):
 if job==D:continue
 for root,dirs,files in os.walk(job):
  dirs[:]=[x for x in dirs if x not in ['target','client-target','objects','lean-objects','actual-objects','sources','actual-sources','source','src','node_modules','.git','.lake','native-source','repo']]
  for n in files:
   if pat.search(n):hits.append(str(Path(root)/n))
G=D.parent/'aspis-fs-generic-20261006/evidence'
for i in range(61100,61200):
 if (G/f'out-{i}.log').exists():hits.append(str(G/f'out-{i}.log'))
(D/'id-scan.json').write_text(json.dumps(dict(range=[61100,61199],matches=hits),indent=2)+'\n')
assert not hits,hits
print('verified',len(checks),'external and',len(seen),'project objects; IDs unused')
