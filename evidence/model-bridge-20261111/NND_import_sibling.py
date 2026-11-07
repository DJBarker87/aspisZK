"""Copy immutable committed sibling sources, preserving their theorem owners."""
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
rev=subprocess.check_output(['git','rev-parse','codex/cx-root0-weak-20261107'],text=True).strip()
rows=json.loads((E/'NND_REUSE.json').read_text())
names=['NNC_SourceCuts','NNC_ByteCarriers','NNC_CommonWeak','NNC_ResumeHeader','NNC_064Weak','NNC_WeakSpec']
for n in names:
 path='evidence/root0-weak-20261111/'+n+'.lean'
 b=subprocess.check_output(['git','show',rev+':'+path]);p=E/'NND_reuse'/(n+'.lean')
 if p.exists():assert p.read_bytes()==b
 else:p.write_bytes(b)
 item=dict(module=n,revision=rev,path=path,sha256=hashlib.sha256(b).hexdigest(),use='unchanged private replay; no duplicated sibling proof')
 if item not in rows:rows.append(item)
(E/'NND_REUSE.json').write_text(json.dumps(rows,indent=1)+'\n')
print(rev)
