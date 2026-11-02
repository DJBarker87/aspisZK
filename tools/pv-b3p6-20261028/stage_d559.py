"""Stage only newly committed PV_B3P modules with h5 HEAD authority."""
from pathlib import Path
import subprocess,json,hashlib,re,sys
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
A={};S={}
for m in sys.argv[1:]:
 p=Path('evidence/pv-b3p6-20261028/lean')/(m+'.lean');b=p.read_bytes()
 assert subprocess.check_output(['git','show',rev+':'+str(p)])==b
 S[m]=b.decode();A[m]=dict(module=m,path=str(p),blob=subprocess.check_output(['git','rev-parse',rev+':'+str(p)],text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),authority='h5 HEAD',imports=re.findall(r'^import (\S+)',b.decode(),re.M),tracked_conflicts=[])
code="""from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-b3p6-20261028');A=AUTH;S=SOURCES;rev=REVISION
x=json.loads((H/'project-resolution-resume18.json').read_text())
for m,s in S.items():
 p=H/'lean'/(m+'.lean');assert not p.exists(),m;p.write_text(s)
x['revision']=rev;x['modules'].update(A);(H/'project-resolution-resume18.json').write_text(json.dumps(x,indent=2)+'\\n')
print('staged',len(S),'new modules')
""".replace('AUTH',repr(A)).replace('SOURCES',repr(S)).replace('REVISION',repr(rev))
print(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True),end='')
