#!/usr/bin/env python3
"""Read committed A blobs only; preserve bytes in a job-owned dependency overlay."""
from pathlib import Path
import subprocess,json,hashlib,re,os
ROOT=Path(__file__).resolve().parents[2]; E=ROOT/'evidence/port17release-20261024'; O=E/'dependency-source'; O.mkdir(exist_ok=True)
REV='a4fa5c5ab357a4f6732a3e053965640c90a0df1e'; BASE='aab7c6fe684835c47c5495287ced886dbd83e903'; PREFIX='docs/research/100bit-spend-path-20261013/'
def blob(p):return subprocess.check_output(['git','show',REV+':'+p],cwd=ROOT)
def sha(b):return hashlib.sha256(b).hexdigest()
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',REV],cwd=ROOT,text=True).splitlines()
# Index immutable receipt objects without accessing the other worktree.
receiptpaths=[p for p in paths if p.endswith('/receipt.json') and '/s126-current-caller-20261021/' in p]
proc=subprocess.Popen(['git','cat-file','--batch'],cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
# Avoid pipe deadlock: use communicate with all requests.
out,_=proc.communicate((''.join(REV+':'+p+'\n' for p in receiptpaths)).encode());pos=0;receipts={}
for p in receiptpaths:
 end=out.index(b'\n',pos);size=int(out[pos:end].split()[-1]);data=out[end+1:end+1+size];pos=end+size+2
 try:r=json.loads(data)
 except (ValueError,UnicodeDecodeError):continue
 if r.get('exit_status')==0 and r.get('object_sha256') and r.get('target'):receipts[r['object_sha256']]=(p,r)
finalpins=json.loads(blob(PREFIX+'evidence/s126-current-caller-20261021/s1-prepare-count-import-pins.json')); final_byname={m['name']:m for m in finalpins['modules']}
top=PREFIX+'evidence/s126-current-caller-20261021/s1-top-prepare-budget-v2-final-imports/receipt.json';r=json.loads(blob(top));selected={};conflicts=[]
def visit(name,h,path):
 if name in final_byname:
  final=final_byname[name]
  if h!=final['sha256']:conflicts.append({'module':name,'historical_requested':h,'final_selected':final['sha256'],'assessment':'Final committed transitive import manifest selects the cache; historical receipt not reused as current dependency validation'})
  h=final['sha256'];path=final['path']
 if name in selected:
  if selected[name]['object_sha256']!=h:conflicts.append({'module':name,'first':selected[name]['object_sha256'],'second':h})
  return
 row={'object_sha256':h,'cached_path':path};selected[name]=row
 if h not in receipts:return
 rp,rr=receipts[h];row['receipt']=rp;row['receipt_sha256']=sha(blob(rp));row['source_sha256']=rr['source_sha256']
 # Require original current committed source bytes, not merely a historical receipt.
 candidates=[p for p in paths if p.endswith('/'+name+'.lean') and '/lean-candidates/s126-caller-boundary-20261021/' in p]
 if not candidates:candidates=[p for p in paths if p.endswith('/'+name.replace('.','/')+'.lean') and '/evidence/' not in p]
 exact=[p for p in candidates if sha(blob(p))==rr['source_sha256']]
 if not exact:
  candidates=[p for p in paths if p.endswith('/'+name.replace('.','/')+'.lean')]
  exact=[p for p in candidates if sha(blob(p))==rr['source_sha256']]
 if not exact:
  row['source_obstruction']='No committed source matching cached receipt';return
 source=exact[0];data=blob(source);dest=O/(name.replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);(dest.read_bytes()==data or (_ for _ in ()).throw(RuntimeError('immutable copy differs'))) if dest.exists() else dest.write_bytes(data);dest.chmod(0o444);row['source_path']=source
 local=ROOT/source
 row['base_source_assessment']='absent from assigned root' if not local.exists() else ('same bytes' if sha(local.read_bytes())==sha(data) else 'DIFFERENT: frozen dependency copy only')
 for dep,info in rr.get('direct_imports',{}).items():visit(dep,info['sha256'],info['path'])
visit('S1TopPrepareBudgetV1',r['object_sha256'],'/tmp/s126-current-caller-20261021-objects/S1TopPrepareBudgetV1.olean')
cache=[]
for n,row in selected.items():
 p=Path(row['cached_path']);actual=sha(p.read_bytes()) if p.exists() else None
 row['cache_matches']=actual==row['object_sha256'];row['cached_actual_sha256']=actual
 cache.append(row['cache_matches'])
report={'immutable_commit':REV,'assigned_base':BASE,'top_receipt':top,'top_receipt_sha256':sha(blob(top)),'lean_path':r['lean_path'],'selected':selected,'object_conflicts':conflicts,'all_selected_cache_match':all(cache),'source_obstructions':[n for n,v in selected.items() if 'source_obstruction' in v]}
(E/'dependency-inventory.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'selected':len(selected),'receipted_sources':sum('source_path' in v for v in selected.values()),'cache_mismatch':[n for n,v in selected.items() if not v['cache_matches']],'object_conflicts':conflicts,'source_obstructions':report['source_obstructions']}))
