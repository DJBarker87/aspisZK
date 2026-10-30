"""Read-only receipt/source audit; compress retained inspection evidence in own directory."""
from pathlib import Path
import json,hashlib,os,re,lzma,time
B=Path(__file__).resolve().parent; H=B.parent
sha=lambda p:hashlib.file_digest(Path(p).open('rb'),'sha256').hexdigest()
mods={m for x in json.load(open(B/'collisions.json')) for m in x['modules']}
seeds=json.load(open(B/'source-seeds.json')); pred=json.load(open(B/'NDR-source-authorities.json'))['NDO_SEED_PINS.json']
results={};gaps=[]
for m in sorted(mods):
 x=seeds.get(m,{}).copy(); rel=m.replace('.','/')+'.lean'
 if not x:
  candidates=[]
  if m.split('.')[0] in ['Init','Lean','Std']:candidates=[Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean')/rel]
  else:
   roots=[H/'aspis-r1-j17-port-20261015/backend/.lake/packages/mathlib',H/'ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/mathlib']
   for root in roots:candidates.extend([root/rel,root/'.lake/packages/batteries'/rel])
   for root in pred['source_roots']:candidates.extend([Path(root)/rel,Path(root)/'sources'/rel,Path(root)/'historical_sources'/rel])
   candidates.extend([H/'codex-cx-reconcile-cache-20261028/historical_sources'/rel,H/'aspis-joint-20261019/sources'/rel])
  found=[p for p in candidates if p.is_file()]
  if found:x={'source':str(found[0]),'sha256':sha(found[0]),'basis':'frozen cohort source-root/module-path association; source existence/hash, not fresh compilation binding','candidate_matches':[str(p) for p in found]}
  else:gaps.append(m);continue
 if x['source'].startswith('/'):
  p=Path(x['source']);x['host_source_exists']=p.is_file()
  if p.is_file():
   actual=sha(p);x['actual_source_sha256']=actual
   if x.get('sha256'):assert actual==x['sha256'],(m,x,actual)
   else:x['sha256']=actual
 results[m]=x
(B/'SOURCES.json').write_text(json.dumps({'providers':results,'unresolved':gaps},indent=2)+'\n')
# Preserve large logs as xz plus the original hash, without changing original evidence.
artifacts=[]
for name in ['lean-70754/stdout.log','lean-70764/stdout.log','divergent-expressions.jsonl']:
 p=B/name;out=Path(str(p)+'.xz');digest=hashlib.sha256();size=0
 with p.open('rb') as src,lzma.open(out,'wb',preset=6) as dst:
  while block:=src.read(1024*1024):digest.update(block);size+=len(block);dst.write(block)
 Path(str(p)+'.sha256').write_text(digest.hexdigest()+'  '+p.name+'\n')
 artifacts.append(dict(path=name,size=size,sha256=digest.hexdigest(),xz_size=out.stat().st_size,xz_sha256=sha(out)))
(B/'retained-log-manifest.json').write_text(json.dumps(artifacts,indent=2)+'\n')
used=[]
for root,dirs,files in os.walk(H):
 dirs[:]=[d for d in dirs if not any(s in d.lower() for s in ['target','object','.git','.lake','node_modules','toolchain'])]
 for f in files:
  if re.search(r'(?<!\d)707(?:[5-8]\d|9[0-6])(?!\d)',f):used.append(str(Path(root)/f))
(B/'resume-id-audit.json').write_text(json.dumps(sorted(used),indent=2)+'\n')
print(json.dumps({'providers':len(results),'unresolved':gaps,'retained_logs':artifacts,'id_evidence_count':len(used)}))
