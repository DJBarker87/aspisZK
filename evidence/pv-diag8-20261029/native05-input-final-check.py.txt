from pathlib import Path
import json,hashlib,sys,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag8-20261029');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
accepted={}
for p in sorted(D.glob('lean*-receipt.json')):
 q=json.loads(p.read_text())
 if q['exit']==0:accepted[q['module']]=q
ext={q['module'].replace('/','.'):q for q in json.loads((D.parent/'codex-pv-diag5-20261029/external-authority.json').read_text())}
roots=['PV_DIAG8_'+m for m in ['Cursor','Arrays','Round','Publication','Messages','World','Frames','AuditValue']]
if '--post' in sys.argv:roots+=['PV_DIAG8_Audit','PV_DIAG8_CohortAudit','PV_DIAG8_FinalManifest']
seen={};bad=[]
def visit(m):
 if m in seen:return seen[m]
 if m in accepted:
  q=accepted[m];p=D/'objects'/(m.replace('.','/')+'.olean');s=D/'sources'/(m.replace('.','/')+'.lean')
  deps={dep:next(v for path,v in vals.items() if path.endswith('.olean')) for dep,vals in q['dependency_objects'].items()}
  r=dict(module=m,path=str(p),sha256=sha(p),source_sha256=sha(s),attempt=q['attempt'],dependencies=deps)
  if sha(p)!=q['object_sha256'] or sha(s)!=q['source_sha256']:bad.append(m)
 else:
  q=ext[m];p=Path(q['path']);r=dict(module=m,path=str(p),sha256=sha(p),authority='h4 external',dependencies={})
  if sha(p)!=q['object_sha256']:bad.append(m)
 seen[m]=r
 for dep,h in r['dependencies'].items():
  if visit(dep)['sha256']!=h:bad.append([m,dep])
 return r
for m in roots:visit(m)
(D/('final-post.json' if '--post' in sys.argv else 'final-pre.json')).write_text(json.dumps(dict(checked=len(seen),rows=seen,mismatches=bad,environment_sha256=sha(D/'env-J.json')),indent=2)+'\n')
print('checked',len(seen),'mismatches',len(bad));assert not bad
