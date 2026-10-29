from pathlib import Path
import json,hashlib,re
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029');records={};expected={};chain=[]
for p in H.glob('lean-*/receipt/receipt.json'):
 r=json.loads(p.read_text())
 if r.get('exit_status')==0:records.setdefault(r.get('module'),[]).append((p,r))
for i in range(15):
 m='PV_B3Q_D188Fixture'+str(i);raw=(H/'lean'/(m+'.lean')).read_bytes();sha=hashlib.sha256(raw).hexdigest();choices=[(p,r)for p,r in records[m]if r['source_sha256']==sha];assert len(choices)==1,(m,choices)
 p,r=choices[0];log=p.parent/'stdout.log'
 chain.append(dict(module=m,attempt=r['attempt'],source_sha256=sha,stdout_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),receipt=str(p)))
 for line in log.read_text().splitlines():
  if not line.startswith('"'):continue
  text=json.loads(line);match=re.fullmatch(r'([A-Za-z_0-9]+):(\d+)=(.*)',text,re.S);assert match,text
  values=json.loads(match[3]);assert isinstance(values,list)and all(isinstance(x,int)for x in values)
  key=match[1]+':'+match[2];assert key not in expected,key;expected[key]=values
assert len(expected)==96,len(expected)
(H/'d188-expected.json').write_text(json.dumps(expected,indent=1)+'\n');(H/'d188-expectation-chain.json').write_text(json.dumps(chain,indent=2)+'\n')
