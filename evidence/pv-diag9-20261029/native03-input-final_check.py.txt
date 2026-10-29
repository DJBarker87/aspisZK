from pathlib import Path
import json,hashlib,re,sys
D=Path('/home/dombarker/project-offloads/codex-pv-diag9-20261029');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
accepted={};attempts=[]
for p in sorted(D.glob('lean*-receipt.json')):
 r=json.loads(p.read_text());attempts.append(r)
 assert r['admission_allowed'] and r['admission_exit']==0
 assert r['resource_caps']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64)
 assert r['swaps']=='0'
 if r['exit']==0:
  assert 'sorryAx' not in r['print_axioms']
  accepted[r['module']]=r
ext={r['module'].replace('/','.'):r for r in json.loads((D.parent/'codex-pv-diag5-20261029/external-authority.json').read_text())}
reused=json.loads((D/'reuse.json').read_text())['rows'];dec=json.loads((D/'decoder-reuse.json').read_text())['rows'];seen={};bad=[]
def visit(m):
 if m in seen:return seen[m]
 if m in accepted:
  r=accepted[m];obj=D/'objects'/(m.replace('.','/')+'.olean');src=D/'sources'/(m.replace('.','/')+'.lean')
  deps={dep:next(v for p,v in vals.items() if p.endswith('.olean')) for dep,vals in r['dependency_objects'].items()}
  x=dict(module=m,path=str(obj),object_sha256=sha(obj),source_sha256=sha(src),expected_source=r['source_sha256'],expected_object=r['object_sha256'],dependencies=deps,attempt=r['attempt'])
 elif m in reused:
  r=reused[m];obj=Path(r['path']);src=Path(r['source_path']);deps={q['dependency']:q['expected'] for q in r['dependencies']}
  x=dict(module=m,path=str(obj),object_sha256=sha(obj),source_sha256=sha(src),expected_source=r['expected_source_sha256'],expected_object=r['expected_object_sha256'],dependencies=deps,authority='runjoin52 read-only coherent cohort')
 elif m in dec:
  r=dec[m];R=D.parent/'codex-pv-rj4idb-20261029';obj=R/'objects'/(m.replace('.','/')+'.olean');src=R/'sources'/(m.replace('.','/')+'.lean');deps={d:q['sha256'] for d,q in r['dependencies'].items()}
  x=dict(module=m,path=str(obj),object_sha256=sha(obj),source_sha256=sha(src),expected_source=r['source_sha256'],expected_object=r['object_sha256'],dependencies=deps,authority='rj4idb accepted exact candidate cohort')
 else:
  r=ext[m];obj=Path(r['path']);x=dict(module=m,path=str(obj),object_sha256=sha(obj),expected_object=r['object_sha256'],dependencies={},authority='h4 external')
 seen[m]=x
 if x['object_sha256']!=x['expected_object'] or x.get('source_sha256')!=x.get('expected_source'):bad.append(m)
 for dep,h in x['dependencies'].items():
  if visit(dep)['object_sha256']!=h:bad.append([m,dep])
 return x
roots=['PV_DIAG9_'+m for m in ['Result','Honest','Retry','Encoders','Frames','Operands','World','Handoff','Scope']]
if '--post' in sys.argv:roots+=['PV_DIAG9_Audit','PV_DIAG9_CohortAudit','PV_DIAG9_FinalManifest']
for m in roots:visit(m)
out=dict(roots=roots,checked=len(seen),rows=seen,mismatches=bad,attempt_count=len(attempts),accepted=sum(r['exit']==0 for r in attempts),rejected=[r['attempt'] for r in attempts if r['exit']!=0])
(D/('final-post.json' if '--post' in sys.argv else 'final-pre.json')).write_text(json.dumps(out,indent=2)+'\n')
print('checked',len(seen),'mismatches',bad);assert not bad
