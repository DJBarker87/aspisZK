"""Read-only manifest copy of217's mathematical reference/value transport.
No native row credit is imported; the ledger alone gates that candidate.
"""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
x=json.load(open('evidence/tx2-auth-20261111/NMX_R3_EXPORT.json'));rows=x['files']
code='''from pathlib import Path
import hashlib,json,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-integrate-20261111');roots=[b/'NNH_objects',b/'NNH_seed',b/'NNH_library_seed'];out=[]
assert shutil.disk_usage(b).free>=40_000_000_000
for row in rows:
 p=Path(row['path']);rel=row['module'].replace('.','/')+'.olean'
 if any((root/rel).exists()for root in roots):continue
 assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
 for src,suffix in [(p,''),(Path(str(p)+'.private'),'.private'),(Path(str(p)+'.server'),'.server'),(p.with_suffix('.ir'),'IR')]:
  if not src.is_file():continue
  q=roots[1]/(rel[:-6]+'.ir'if suffix=='IR'else rel+suffix);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,q)
  out.append(dict(source=str(src),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='rows='+repr(rows)+'\n'+code,capture_output=True,text=True);assert r.returncode==0,r.stderr
p=E/'NNH_LANE_IMPORTS.json';old=json.loads(p.read_text())if p.exists()else[];new=json.loads(r.stdout);p.write_text(json.dumps(old+new,indent=2)+'\n');print('copied',len(new))
