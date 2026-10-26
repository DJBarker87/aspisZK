"""Hash every local git blob, including non-Lean filenames and unreachable blobs."""
import subprocess,hashlib,json,time
from pathlib import Path
O=Path(__file__).parent
inventories=['EJR_inventory.json','EJR_supplement-inventory.json'];xs=[json.loads((O/n).read_text()) for n in inventories];wanted={s for x in xs for s in x['missing_hashes']};found={};start=time.monotonic();count=0;size=0
p=subprocess.Popen(['git','cat-file','--batch-all-objects','--batch'],stdout=subprocess.PIPE)
while True:
 line=p.stdout.readline()
 if not line:break
 oid,kind,n=line.decode().split();n=int(n);remaining=n;h=hashlib.sha256()
 while remaining:
  b=p.stdout.read(min(remaining,1024*1024));remaining-=len(b)
  if kind=='blob':h.update(b)
 assert p.stdout.read(1)==b'\n'
 if kind!='blob':continue
 count+=1;size+=n;s=h.hexdigest()
 if s in wanted:
  found[s]={'blob':oid,'bytes':n};print('FOUND',s,oid,flush=True)
assert p.wait()==0
objects={}
if found:
 for l in subprocess.check_output(['git','rev-list','--objects','--all'],text=True).splitlines():
  oid,_,path=l.partition(' ')
  if oid in {r['blob'] for r in found.values()}:objects[oid]=path
 for s,r in found.items():
  path=objects.get(r['blob']);r['path']=path;r['revision']=None
  for rev in subprocess.check_output(['git','log','--all','--format=%H','--find-object='+r['blob']],text=True).splitlines():
   if not path:break
   tree=subprocess.check_output(['git','ls-tree',rev,'--',path],text=True)
   if r['blob'] in tree:r['revision']=rev;break
r=dict(blob_count=count,blob_bytes=size,wall_seconds=time.monotonic()-start,wanted_count=len(wanted),found=found,not_found=sorted(wanted-found.keys()),scope='every local git blob, all names, reachable and unreachable; source bytes never normalized',exit=0)
(O/'EJR_exhaustive-blob-scan.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k not in ['found','not_found']}),flush=True)
