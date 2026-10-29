"""Read-only cohort audit and private staging. Never writes predecessor directories."""
from pathlib import Path
import json,hashlib,shutil,re,time,subprocess,struct,os
B=Path('/home/dombarker/project-offloads/codex-pv-evhc2-20261029');R=B.parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
plan=json.load(open(B/'plan.json'));ident=json.load(open(B/'source-identity.json'))
start=time.monotonic();checks=[]
ndr=json.load(open(B/'NDR_FINAL_COHORT_PINS.json'))
for v in ndr['entries']:
 p=Path(v['object_path']);actual=sha(p);assert actual==v['object_sha256'],v
 checks.append(dict(module=v['module'],path=str(p),sha256=actual))
# Also pin NDR_CombinedAudit, which is the output rather than an entry in its closure.
for name,v in json.load(open(B/'NDR_FINAL_OUTPUT_PINS.json')).items():
 p=R/'codex-cx-reconcile-cache-20261028'/name;assert sha(p)==v['sha256'],name
checks.append(dict(module='NDR_CombinedAudit',path=str(R/'codex-cx-reconcile-cache-20261028/objects/NDR_CombinedAudit.olean'),sha256=sha(R/'codex-cx-reconcile-cache-20261028/objects/NDR_CombinedAudit.olean')))
formal=R/'ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal'
for row in ident['modules']:
 if row['kind']!='external':continue
 m=row['module'];rel=m.replace('.','/')+'.lean'
 candidates=[formal/'.lake/packages/mathlib'/rel,R/'aspis-joint-20261019/sources'/rel]
 candidates += [R/'codex-cx-import-union-20261022'/rel]
 p=next((q for q in candidates if q.is_file()),None);assert p,('external source missing',m)
 digest=sha(p);snapshots=row['snapshots'];assert any(v['sha256']==digest for v in snapshots),('external source differs from common revision snapshots',m,str(p),digest)
 row.update(host_source_path=str(p),host_source_sha256=digest,host_matches_common_source=True)
# Read actual object import headers, using the existing s126 binary parser.
def imports(path):
 b=path.read_bytes(); assert b[:5]==b'olean',str(path)
 base,root=struct.unpack_from('<QQ',b,80)
 def u(o): return struct.unpack_from('<Q',b,o)[0]
 def name(p):
  if p&1: assert p==1; return ''
  o=p-base; tag=b[o+7]; prefix=name(u(o+8)); assert tag in [1,2]
  if tag==1:
   q=u(o+16)-base; t=b[q+32:b.index(0,q+32)].decode()
  else: t=str(u(o+16))
  return prefix+'.'+t if prefix else t
 arr=u(root-base+8)-base
 return list(dict.fromkeys(name(u(u(arr+24+8*i)-base+8)) for i in range(u(arr+8))))

graph={};source_pins={}
for m,v in plan['all_event_pins'].items():
 p=Path(v['path']);assert sha(p)==v['sha256'],('event fingerprint',m)
 graph[m]=imports(p)
# FinEnum is the sole external event-only module; only needed if the binary graph marks it affected.
m='Mathlib.Data.FinEnum';p=formal/'.lake/packages/mathlib/Mathlib/Data/FinEnum.lean'
source_pins[m]=dict(path=str(p),sha256=sha(p))
# Always include implicit Init; it is common and unchanged.
graph['NDR_CombinedAudit']=[]
ndrmap={v['module']:v for v in ndr['entries']}
conflicts=set(plan['conflicts']);affected={};visiting=set()
def hit(m):
 if m in affected:return affected[m]
 if m in conflicts:affected[m]=True;return True
 assert m not in visiting,('import cycle',m)
 visiting.add(m)
 if m not in graph and m in ndrmap:graph[m]=imports(Path(ndrmap[m]['object_path']))
 assert m in graph,('graph gap',m)
 h=False
 for d in graph[m]:h=hit(d) or h
 visiting.remove(m);affected[m]=h;return h
order=[];visited=set();ndrnames={v['module'] for v in ndr['entries']}|{'NDR_CombinedAudit'}
def visit(m):
 if m in visited:return
 visited.add(m)
 if m in ndrnames:return
 assert m in plan['events'],('event pin missing',m)
 for d in graph[m]:visit(d)
 order.append(m)
for m in plan['roots']:visit(m)
plan['rebuild']=[m for m in order if hit(m)];plan['reuse']=[m for m in order if not hit(m)]
plan['edges']={m:graph[m] for m in order}
plan['graph_source_pins']=source_pins
plan['full_graph']=graph
for m in plan['rebuild']:
 if m in plan['sources']:continue
 p=Path(source_pins[m]['path']);plan['sources'][m]=dict(path=str(p),revision='identical external package pin at b51b1040f2 and 06f74c902f',sha256=sha(p),text=p.read_text())
ndrmap={v['module']:v for v in ndr['entries']}
old_roots=json.load(open(R/'codex-pv-evh-20261029/J.json'))['LEAN_PATH'].split(':')
reuse=[]
for m in plan['reuse']:
 v=plan['events'][m];assert sha(v['path'])==v['sha256'],m
 deps=[]
 for d in plan['edges'][m]:
  old=next(Path(q)/(d.replace('.','/')+'.olean') for q in old_roots if (Path(q)/(d.replace('.','/')+'.olean')).is_file())
  new=Path(ndrmap[d]['object_path']) if d in ndrmap else Path(plan['events'][d]['path'])
  assert sha(old)==sha(new),(m,d,'reuse dependency fingerprint changed')
  deps.append(dict(module=d,old_path=str(old),new_path=str(new),sha256=sha(new)))
 reuse.append(dict(module=m,object_sha256=v['sha256'],dependencies=deps))
 dst=B/'objects'/Path(m.replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True)
 for suffix in ['', '.server','.private']:
  src=Path(v['path']+suffix)
  if src.exists():shutil.copyfile(src,Path(str(dst)+suffix))
 src=Path(v['path']).with_suffix('.ir')
 if src.exists():shutil.copyfile(src,dst.with_suffix('.ir'))
for m,s in plan['sources'].items():
 if m not in plan['rebuild']:continue
 p=B/'sources'/Path(m.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s['text']);assert sha(p)==s['sha256']
for name in ['S2W_lean_host.py','S2W_run_host.py']:
 shutil.copyfile(R/'codex-cx-fixture-cache-20261027'/name,B/name)
(B/'source-identity-host.json').write_text(json.dumps(ident,indent=2)+'\n')
(B/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
# Read-only ID collision scan across all jobs; no launcher is invoked.
used={};pat=re.compile(r'(?<![0-9])(7[01][0-9]{3})(?![0-9])')
for job in R.glob('codex-*'):
 # Receipt trees and top-level runner output only; never traverse source/dependency caches.
 candidates=list(job.glob('*'))
 if (job/'evidence').exists():candidates+=list((job/'evidence').rglob('*'))
 for q in job.glob('lean-*'):
  if q.is_dir():candidates+=list(q.glob('*'))
 for p in candidates:
  if p.is_dir():continue
  if not any(t in p.name for t in ['receipt','submission','attempt','modules-','out-','lean-','admission','time-']):continue
  for a in pat.findall(str(p.relative_to(job))):used.setdefault(a,[]).append(str(p))
sent=R/'r1-privacy-build-integration-20261019/evidence/sent.txt'
if sent.exists():
 for line in sent.read_text().splitlines():
  for a in pat.findall(line):used.setdefault(a,[]).append('sent.txt: '+line)
(B/'id-audit.json').write_text(json.dumps(used,indent=2)+'\n')
(B/'source-identity-host.json').write_text(json.dumps(ident,indent=2)+'\n')
(B/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
(B/'preflight.json').write_text(json.dumps(dict(status='PASS',wall_seconds=time.monotonic()-start,ndr_objects=checks,reuse=reuse,runners={name:sha(B/name) for name in ['S2W_lean_host.py','S2W_run_host.py']}),indent=2)+'\n')
print(json.dumps(dict(status='PASS',wall_seconds=time.monotonic()-start,rebuild=len(plan['rebuild']),reuse=len(reuse),ids_used=sorted(used))))
