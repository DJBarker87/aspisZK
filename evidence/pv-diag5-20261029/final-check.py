from pathlib import Path
import hashlib,json,sys
D=Path('/home/dombarker/project-offloads/codex-pv-diag5-20261029');P=D.parent/'codex-pv-diag3-20261029';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((P/'resume-cache-preflight.json').read_text())['rows'];external={r['module'].replace('/','.'):r for r in json.loads((D/'external-authority.json').read_text())};records={}
for p in sorted(D.glob('lean*-receipt.json')):
 r=json.loads(p.read_text())
 if r['exit']==0:records[r['module']]=r
roots=['PV_DIAG5_Joint','PV_DIAG5_Endpoint','R1Z.PV_RunJoin_Deployed']
if '--post' in sys.argv:roots+=['PV_DIAG5_Audit','PV_DIAG5_CohortAudit','PV_DIAG5_FinalManifest']
seen={};bad=[]
def visit(m):
 if m in seen:return seen[m]
 p=D/'objects'/(m.replace('.','/')+'.olean')
 if m in records:
  r=records[m];s=D/'sources'/(m.replace('.','/')+'.lean');d=dict(module=m,path=str(p),sha256=sha(p),source_sha256=sha(s),expected_source=r['source_sha256'],expected_object=r['object_sha256'],authority='fresh compile',attempt=r['attempt'],dependencies=r['dependency_objects'])
  if sha(s)!=r['source_sha256'] or sha(p)!=r['object_sha256']:bad.append(d)
  deps={dep:next(v for k,v in values.items() if k.endswith('.olean')) for dep,values in r['dependency_objects'].items()}
 elif m in external:
  r=external[m];p=Path(r['path']);d=dict(module=m,path=str(p),sha256=sha(p),expected_object=r['object_sha256'],authority='pinned external');deps={}
  if sha(p)!=r['object_sha256']:bad.append(d)
 else:
  r=old[m];d=dict(module=m,path=str(p),sha256=sha(p),expected_object=r['sha256'],source_sha256=r.get('source_sha256'),authority='read-only h6/h7 cohort',dependencies=r.get('record_dependencies',{}))
  if sha(p)!=r['sha256']:bad.append(d)
  deps={m:v['sha256'] for m,v in r.get('record_dependencies',{}).items()}
 seen[m]=d
 for dep,expected in deps.items():
  actual=visit(dep)
  if actual['sha256']!=expected:bad.append(dict(module=m,dependency=dep,expected=expected,actual=actual['sha256']))
 d['sidecars']={str(q):sha(q) for q in [Path(str(p)+'.server'),Path(str(p)+'.private'),p.with_suffix('.ir')] if q.is_file()}
 return d
for root in roots:visit(root)
# Explicitly connect the reused sampler objects to diag4's recovered generation chain.
chain=json.loads((D.parent/'codex-pv-diag4-20261029/sampler-generation-chain.json').read_text())
for m,r in chain['sources'].items():
 if m in seen:assert seen[m]['source_sha256']==r['sha256'],m
(D/('final-post.json' if '--post' in sys.argv else 'final-pre.json')).write_text(json.dumps(dict(roots=roots,checked=len(seen),rows=seen,mismatches=bad,environment_sha256=sha(D/'env-J.json')),indent=2)+'\n')
print('coherent objects',len(seen),'mismatches',len(bad));print(json.dumps(bad[:3],indent=2));assert not bad
