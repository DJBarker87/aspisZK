"""Resolve new private proof modules at the committed worktree HEAD (h5).
No shared source/object writes, and no fallback to similarly named sources.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
D=Path('evidence/pv-b3p6-20261028');O=D/'resume13';p=O/'project-resolution-resume13.json';x=json.loads(p.read_text())
x['revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
for m in sys.argv[1:]:
 q=D/'lean'/(m+'.lean');k='HEAD:'+str(q);raw=q.read_bytes()
 assert subprocess.check_output(['git','show',k])==raw
 x['modules'][m]=dict(module=m,path=str(q),blob=subprocess.check_output(['git','rev-parse',k],text=True).strip(),sha256=hashlib.sha256(raw).hexdigest(),authority='h5 HEAD',imports=[l.split()[1]for l in raw.decode().splitlines()if l.startswith('import ')],tracked_conflicts=[])
p.write_text(json.dumps(x,indent=2)+'\n')
