#!/usr/bin/env python3
"""Bounded source/log collection from one exact owned workspace. No builds."""
from pathlib import Path
import subprocess,json,base64,hashlib,time
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
code=r'''
from pathlib import Path
import json,base64,hashlib,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20));signal.alarm(30)
result={};total=0;count=0
for n in range(9,10):
 w=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021/s1-claims-safe-extract-run'+str(n)+'-20261025')
 files=sorted([p for p in w.iterdir()if p.suffix in ['.json','.log']or p.name=='run.py'])
 if (w/'generated').exists():files+=sorted(p for p in (w/'generated').rglob('*')if p.is_file()and p.suffix in ['.lean','.json'])
 out={}
 for p in files:
  assert not p.is_symlink();count+=1;assert count<=1024
  size=p.stat().st_size;assert size<=10*2**20;total+=size;assert total<=32*2**20
  data=p.read_bytes();out[str(p.relative_to(w))]=base64.b64encode(data).decode()
 llbc=w/'ClaimsSafe.llbc'
 if llbc.exists():
  assert llbc.stat().st_size<=32*2**20
  data=llbc.read_bytes();d=json.loads(data)
  out['llbc-info.json']=base64.b64encode((json.dumps(dict(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),has_errors=d.get('has_errors')),indent=2)+'\n').encode()).decode()
 result[str(n)]=out
print(json.dumps(result))
'''
cmd=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=8','dombarker@100.108.41.90','/usr/bin/python3 -I -S -B -']
start=time.monotonic();q=subprocess.run(cmd,input=code,text=True,capture_output=True,timeout=40);assert q.returncode==0,q.stderr
assert len(q.stdout)<48*2**20;d=json.loads(q.stdout)
for n,files in d.items():
 out=E/('s1-claims-nuc-extract-run'+n)
 for rel,encoded in files.items():
  p=out/rel;assert '..'not in Path(rel).parts and not Path(rel).is_absolute()
  data=base64.b64decode(encoded);p.parent.mkdir(parents=True,exist_ok=True)
  if p.exists():assert p.read_bytes()==data,str(p)
  else:p.write_bytes(data)
 p=out/'collection-receipt.json';p.write_text(json.dumps(dict(exit_status=q.returncode,wall_seconds=time.monotonic()-start,transport_sha256=hashlib.sha256(q.stdout.encode()).hexdigest(),files={rel:hashlib.sha256(base64.b64decode(v)).hexdigest()for rel,v in files.items()},collector_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),build_launched=False),indent=2)+'\n')
for n in d:
 w=E/('s1-claims-nuc-extract-run'+n)
 for name in ['charon-receipt.json','aeneas-receipt.json','terminal.json','terminal-error.json']:
  if (w/name).exists():print(n,name,(w/name).read_text()[:900])
print('Collected source/log files:',sum(len(v)for v in d.values()))
