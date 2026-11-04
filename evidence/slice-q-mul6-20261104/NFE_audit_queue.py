from pathlib import Path
import subprocess,json,lzma,hashlib
E=Path(__file__).resolve().parent
jobs=[(58,'fixtures'),(59,'scan')]+[(60+i,'proof'+str(i)) for i in range(41)]
for i,mode in jobs:
 a=f'NFE_L{i:03}'
 if (E/a/'receipt.json').exists():
  assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0
  continue
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NFE_run.py'),a,'auditbin',mode],stdout=f,stderr=subprocess.STDOUT)
 print(a,mode,r.returncode,flush=True)
 if r.returncode:break
 # Raw graphs are compressed immediately after each successful audit.
 for p in E.glob('NEP_'+mode+'_*_REACHABLE.txt'):
  raw=p.read_bytes();Path(str(p)+'.xz').write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');p.unlink()
