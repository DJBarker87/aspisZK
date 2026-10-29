from pathlib import Path
import json,hashlib,re,sys
D=Path('/home/dombarker/project-offloads/codex-pv-diag6-20261029');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r={}
for p in sorted(D.glob('lean*-receipt.json')):
 q=json.loads(p.read_text())
 if q['exit']==0:r[q['module']]=q
old=json.loads((D/'law-preflight.json').read_text())['rows'];ext={q['module'].replace('/','.'):q for q in json.loads((D.parent/'codex-pv-diag5-20261029/external-authority.json').read_text())}
roots=['PV_DIAG6_Native','PV_DIAG6_Prefix','PV_DIAG6_Distribution']
if '--post' in sys.argv:roots+=['PV_DIAG6_Audit','PV_DIAG6_CohortAudit','PV_DIAG6_FinalManifest']
seen={};bad=[]
def visit(m):
 if m in seen:return seen[m]
 p=D/'objects'/(m.replace('.','/')+'.olean')
 if m in r:
  q=r[m];src=D/'sources'/(m.replace('.','/')+'.lean');x=dict(module=m,path=str(p),sha256=sha(p),source_sha256=sha(src),attempt=q['attempt'],authority='fresh private compile');deps={k:next(v for p,v in vals.items() if p.endswith('.olean')) for k,vals in q['dependency_objects'].items()}
  if sha(p)!=q['object_sha256'] or sha(src)!=q['source_sha256']:bad.append(m)
 elif m in old:
  q=old[m];p=Path(q['path']);x=dict(module=m,path=str(p),sha256=sha(p),source_sha256=q.get('source_sha256'),authority='h6 pinned read-only L1 law closure');deps={k:v['sha256'] for k,v in q.get('record_dependencies',{}).items()}
  if sha(p)!=q['sha256']:bad.append(m)
 else:
  q=ext[m];p=Path(q['path']);x=dict(module=m,path=str(p),sha256=sha(p),authority='h4 external manifest');deps={}
  if sha(p)!=q['object_sha256']:bad.append(m)
 seen[m]=x
 x['dependencies']=deps
 for dep,v in deps.items():
  y=visit(dep)
  if y['sha256']!=v:bad.append(dict(module=m,dependency=dep,actual=y['sha256'],expected=v))
 x['sidecars']={str(p):sha(p) for p in [Path(str(p)+'.server'),Path(str(p)+'.private'),p.with_suffix('.ir')] if p.is_file()}
 return x
for m in roots:visit(m)
(D/('final-post.json' if '--post' in sys.argv else 'final-pre.json')).write_text(json.dumps(dict(roots=roots,checked=len(seen),rows=seen,mismatches=bad,environment_sha256=sha(D/'env-J.json')),indent=2)+'\n');print('coherent',len(seen),'mismatches',len(bad));assert not bad
