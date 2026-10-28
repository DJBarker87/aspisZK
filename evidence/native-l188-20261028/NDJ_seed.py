"""Task cache copying and provenance inspection only; no compiler/launcher."""
import json,hashlib,shutil
from pathlib import Path
B=Path(__file__).resolve().parent
x=json.loads((B/'NDJ_SEED_INPUT.json').read_text())
assert str(B)==x['base']
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def select(m,paths,suffix='.olean'):
 return next((p for r in paths if (p:=Path(r)/(m.replace('.','/')+suffix)).is_file()),None)
graph=x['graph'];fallback=x['fallback'];seen={};missing=[]
for m,v in json.loads(Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/object-source-manifest.json').read_text())['modules'].items():fallback.setdefault(m,v)
def visit(m,paths,cohort):
 if m in seen:return
 p=select(m,paths)
 if p is None:missing.append((cohort,m));return
 s=select(m,paths,'.lean')
 imports=graph.get(m)
 if cohort=='joint':
  imports=([n for l in s.read_text().splitlines() if l.startswith('import ') for n in l[7:].split()] if s else fallback.get(m,{}).get('imports',imports))
 if imports is None and s is None:
  lib=Path('/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/mathlib')/(m.replace('.','/')+'.lean')
  if lib.is_file():
   s=lib;imports=[n for l in s.read_text().splitlines() if l.startswith('import ') for n in l[7:].split()]
 if imports is None:missing.append(('imports',m));return
 seen[m]=dict(module=m,original=str(p),sha256=sha(p),bytes=p.stat().st_size,imports=imports,cohort=cohort,source=str(s) if s else None,source_sha256=sha(s) if s else None)
 for n in imports:visit(n,paths,cohort)
visit('RPx_Deployed',x['rpx_paths'],'headline')
headline=set(seen)
# Joint selection must use the coherent headline objects wherever they overlap.
visit('JHx_Joint',x['joint_paths'],'joint')
collisions=[]
for m in headline:
 q=select(m,x['joint_paths'])
 if q and (h:=sha(q))!=seen[m]['sha256']:
  collisions.append(dict(module=m,headline=seen[m]['original'],headline_sha256=seen[m]['sha256'],joint=str(q),joint_sha256=h))
assert not missing,missing[:30]
# Differences are not silently repaired. Record before any compile; lead review
# can distinguish root-unique names from a genuinely shared incompatible object.
rows=[]
for m,v in seen.items():
 p=Path(v['original']);rel=Path(m.replace('.','/'));dst=B/'objects'/rel.with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
 artifacts=[]
 for src,dest in [(p,dst),(Path(str(p)+'.server'),Path(str(dst)+'.server')),(Path(str(p)+'.private'),Path(str(dst)+'.private')),(p.with_suffix('.ir'),dst.with_suffix('.ir'))]:
  if not src.is_file():continue
  h=sha(src)
  if dest.exists():assert sha(dest)==h, str(dest)
  else:shutil.copyfile(src,dest)
  artifacts.append(dict(original=str(src),path=str(dest),sha256=h,bytes=dest.stat().st_size))
 v.update(path=str(dst),artifacts=artifacts);rows.append(v)
out=dict(roots=['RPx_Deployed','JHx_Joint'],headline_count=len(headline),union_count=len(rows),objects=rows,alternate_joint_path_differences=collisions,missing=missing)
(B/'NDJ_CACHE_PINS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(headline_count=len(headline),union_count=len(rows),alternate_joint_path_differences=len(collisions),missing=missing)))
# Copy unchanged existing lead-owned launchers.
for n in ['S2W_run_host.py','S2W_lean_host_agg16.py','S2W_run_host_agg16.py','reservation_agg16.py']:
 p=Path('/home/dombarker/project-offloads/codex-cx-sha453-cache-20261028')/n
 if p.is_file():shutil.copyfile(p,B/n)
