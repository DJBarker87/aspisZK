"""Collect per-invocation textual freezes without launching or repeating any job."""
from pathlib import Path
import subprocess,json,time,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-kstub-20261028';H='dombarker@100.108.41.90'
code='''from pathlib import Path
import json
D=Path('/home/dombarker/project-offloads/codex-pv-kstub-20261028')
print(json.dumps({str(p.relative_to(D)):p.read_text() for d in sorted(D.glob('K[0-9][0-9]')) for p in d.iterdir() if p.is_file() and (p.name=='source-manifest.json' or p.name.endswith('.rs.txt'))}))
'''
for k in range(11):
 q=subprocess.run(['ssh',H,'python3 -'],input=code,text=True,capture_output=True)
 if q.returncode!=255:break
 with (E/'source-collection-transport.jsonl').open('a') as f:f.write(json.dumps(dict(exit=255,attempt=k,stderr=q.stderr,time=time.time()))+'\n')
 if k<10:time.sleep(60)
assert q.returncode==0,q.stderr
for rel,s in json.loads(q.stdout).items():
 p=E/rel
 if p.exists():assert p.read_text()==s,'Immutable source snapshot changed: '+rel
 else:p.write_text(s)
audit=[]
for p in sorted(E.glob('K??/KMX_stubs.rs.txt')):
 h=hashlib.sha256(p.read_bytes()).hexdigest();assert h=='c282a1272676cd56fd2702f60b17009bac9d252e495b1508459b01d6ed1cf9d9';audit.append(dict(run=p.parent.name,path=str(p.relative_to(R)),stub_sha256=h))
(E/'per-run-kmx-audit.json').write_text(json.dumps(dict(patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',runs=audit),indent=2)+'\n');print('Collected immutable source freezes for',len(audit),'runs')
