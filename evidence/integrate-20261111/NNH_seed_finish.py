"""Copy only136's source import closure from its audited receipt pins."""
from pathlib import Path
import json,subprocess,re
E=Path(__file__).resolve().parent;D=Path('evidence/tx1-principal-20261111')
pins={}
for p in sorted(D.glob('NNG_L*/receipt.json')):
 try:n=int(p.parent.name[5:])
 except ValueError:continue
 if n>362:continue
 x=json.loads(p.read_text())
 if x.get('exit_status')!=0:continue
 for path,pin in x.get('deps_fingerprint',{}).get('selected_objects',{}).items():
  if '/NNG_objects/' in path:pins[path]=pin
seen=set();queue=['NNG_Candidate136'];sources=[]
while queue:
 m=queue.pop()
 if m in seen:continue
 seen.add(m)
 p=D/(m+'.lean')
 if p.exists():
  s=p.read_text();sources.append(str(p));queue.extend(re.findall(r'^import (NNG_[\w.]+)',s,re.M))
rows=[]
for m in sorted(seen):
 rel=m.replace('.','/')+'.olean';matches=[v for path,v in pins.items()if path.endswith('/NNG_objects/'+rel)]
 assert len(matches)==1,(m,len(matches));rows.append(dict(matches[0],relative=rel,module=m))
code='''from pathlib import Path
import shutil,json,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-integrate-20261111');out=[]
assert shutil.disk_usage(b).free>=40_000_000_000
for row in rows:
 p=Path(row['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
 rel=row['relative'];q=b/'NNH_seed'/rel
 if not q.exists():q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==row['sha256'],str(q)
 out.append(dict(source=str(p),destination=str(q),sha256=row['sha256']))
 for src,suffix in [(Path(str(p)+'.private'),'.private'),(Path(str(p)+'.server'),'.server'),(p.with_suffix('.ir'),'IR')]:
  if not src.is_file():continue
  dst=b/'NNH_seed'/(rel[:-6]+'.ir'if suffix=='IR'else rel+suffix)
  if not dst.exists():shutil.copy2(src,dst)
  h=hashlib.sha256(src.read_bytes()).hexdigest();assert hashlib.sha256(dst.read_bytes()).hexdigest()==h,str(dst)
  out.append(dict(source=str(src),destination=str(dst),sha256=h))
print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='rows='+repr(rows)+'\n'+code,capture_output=True,text=True);assert r.returncode==0,r.stderr
(E/'NNH_FINISH_IMPORTS.json').write_text(json.dumps(dict(objects=json.loads(r.stdout),source_closure=sources,modules=sorted(seen),supplier='NNG_Candidate136; complete audited candidate; ledger gate decides credit'),indent=2)+'\n');print('copied',len(json.loads(r.stdout)))
