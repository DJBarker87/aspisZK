"""Read-only h6 reuse: retain each original environment prefix; verify closure."""
from pathlib import Path
import json,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-skw-20261029');P=D.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
D.mkdir(exist_ok=True);(D/'sources').mkdir(exist_ok=True);(D/'objects').mkdir(exist_ok=True)
cat=json.loads((D/'pins.json').read_text()); records={}
def add(m,r):records.setdefault(m.replace('/','.'),[]).append(r)
for r in cat['own']:
 add(r['module'],dict(source_sha256=r['source_sha256'],object_sha256=r['object_sha256'],source_path=r['source_path'],deps=r['dependency_objects']))
for m,r in cat['diag'].items():add(m,dict(source_sha256=r['source_sha256'],object_sha256=r['sha256'],source= r['source']))
T=P/'codex-pv-diag10-20261029'
for f in T.glob('lean*-receipt.json'):
 r=json.loads(f.read_text())
 if r['exit']==0:
  deps={m:next(h for p,h in v.items() if p.endswith('.olean')) for m,v in r['dependency_objects'].items()}
  add(r['module'],dict(source_sha256=r['source_sha256'],object_sha256=r['object_sha256'],source=str(T/'sources'/(r['module'].replace('.','/')+'.lean')),deps=deps))
L=P/'codex-pv-l1g-20261029'
for f in (L/'evidence').glob('results-*.json'):
 for r in json.loads(f.read_text()):
  if r['exit']==0:add(r['module'],dict(source_sha256=r['source_sha256'],object_sha256=r['object_sha256'],source=str(L/'sources'/(r['module'].replace('.','/')+'.lean')),deps={m:v['sha256'] for m,v in r['dependencies'].items()}))
ext=json.loads((P/'codex-pv-diag5-20261029/external-authority.json').read_text());external={r['module'].replace('/','.'):r for r in ext}
reports={}
for name,old,envname,roots in [('diag',T,'env-J.json',['PV_DIAG10_FILE','PV_DIAG10_JSON_STDOUT','PV_DIAG10_ERROR_STDERR']),('l1',L,'J.json',['PV_L1E_OriginalCountSkeleton'])]:
 env=json.loads((old/envname).read_text()); paths=[old/('lean-objects' if name=='own' else 'objects')]+[Path(p) for p in env['LEAN_PATH'].split(':')]
 def select(m):
  q=next((p/(m.replace('.','/')+'.olean') for p in paths if (p/(m.replace('.','/')+'.olean')).is_file()),None)
  assert q is not None,('missing object',name,m)
  return q
 rows={}
 def visit(m):
  if m in rows:return
  obj=select(m);h=sha(obj)
  if m in external:
   assert h==external[m]['object_sha256'],('external mismatch',m);rows[m]=dict(external=True,object=str(obj),sha256=h);return
  candidates=[r for r in records.get(m,[]) if r['object_sha256']==h]
  assert candidates,('missing matching project pin',name,m,str(obj),h)
  r=candidates[-1];src=Path(r['source']) if 'source' in r else old/'lean-sources'/(m.replace('.','/')+'.lean')
  if not src.is_file():
   src=next(p/(m.replace('.','/')+'.lean') for p in [P/'codex-pv-ownn-20261029/lean-sources',P/'codex-pv-ownc-20261029/lean-sources',P/'codex-pv-runjoin-20261026/runjoin32-lean/sources'] if (p/(m.replace('.','/')+'.lean')).is_file())
  assert sha(src)==r['source_sha256'],('source mismatch',m,str(src))
  imports=re.findall(r'^import (\S+)',re.sub(r'/\-.*?\-/','',src.read_text(),flags=re.S),re.M)
  rows[m]=dict(source=str(src),source_sha256=sha(src),object=str(obj),sha256=h,imports=imports)
  for dep,hdep in r.get('deps',{}).items():assert sha(select(dep))==hdep,('dependency mismatch',m,dep)
  for dep in imports:visit(dep)
 for m in roots:visit(m)
 # Validate every external object before first compile (h4), not only directly named imports.
 for m,r in external.items():assert sha(select(m))==r['object_sha256'],m
 reports[name]=dict(rows=rows,external_checked=len(external),original_environment_sha256=sha(old/envname),LEAN_GITHASH=env['LEAN_GITHASH'])
 # Preserve original prefix exactly; private additions are only at the end.
 env['LEAN_PATH']=':'.join(map(str,paths))+':'+str(D/'objects')
 (D/('env-own.json' if name=='own' else 'env-l1.json' if name=='l1' else 'env-J.json')).write_text(json.dumps(env,indent=2)+'\n')
(D/'reuse.json').write_text(json.dumps(reports,indent=2)+'\n')
print({k:len(v['rows']) for k,v in reports.items()})
