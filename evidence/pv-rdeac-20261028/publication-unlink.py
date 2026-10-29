from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdeac-20261028');removed=[]
for m in json.loads((D/'publication-rebuild-order.json').read_text()):
 p=D/'objects'/(m.replace('.','/')+'.olean')
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server')]:
  if q.is_symlink():
   removed.append(dict(path=str(q),target=str(q.readlink()),sha256=hashlib.sha256(q.read_bytes()).hexdigest()));q.unlink()
(D/'publication-unlink.json').write_text(json.dumps(dict(removed_own_cache_links=removed,reason='Rebuild ten-module dependent closure of current ProverRwFullExternalFuns; no shared object is modified'),indent=2)+'\n');print('removed own links',len(removed))
