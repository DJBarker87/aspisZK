from pathlib import Path
import subprocess,json,shlex
E=Path('evidence/pv-batch2-20261027/batch2c')
code=r'''from pathlib import Path
import os,re,json,time
B=Path('/home/dombarker/project-offloads');hits=[];used=set()
sent=B/'r1-privacy-build-integration-20261019/evidence/sent.txt'
for line in sent.read_text().splitlines():
 ids={int(x) for x in re.findall(r'(?<!\d)52\d{3}(?!\d)',line) if 52000<=int(x)<=52499}
 if ids:used.update(ids);hits.append(dict(path=str(sent),line=line,ids=sorted(ids)))
prune={'src','target','sources','lean-sources','lean-objects','artifacts','diagnostics','node_modules','.git','charon-target','native-target','sbf-target-verifier','sbf-target-pool','.lake','objects','objects2','retained-objects','lake-packages','vendor','toolchains','pinned-tools','node_modules','cargo-home'}
for root in list(B.glob('codex-*'))+[B/'aspis-fs-generic-20261006/evidence']:
 for parent,ds,fs in os.walk(root):
  ds[:]=[d for d in ds if d not in prune]
  for name in ds+fs:
   ids={int(x) for x in re.findall(r'(?<!\d)52\d{3}(?!\d)',name) if 52000<=int(x)<=52499}
   if ids:used.update(ids);hits.append(dict(path=str(Path(parent)/name),ids=sorted(ids)))
print(json.dumps(dict(checked_epoch=time.time(),used=sorted(used),hits=hits)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True,check=True)
j=json.loads(r.stdout);(E/'ID-PREFLIGHT.json').write_text(json.dumps(j,indent=2)+'\n');print('used',j['used']);print('audit candidates',[n for n in range(52499,51999,-1) if n not in j['used']][:3])
