from pathlib import Path
import json,hashlib
w=Path('/home/dombarker/project-offloads/pair-regular-trace-final-comparison-v1-20261024')
d=json.loads((w/'closure.json').read_text())
c=json.loads(Path('/home/dombarker/project-offloads/pair-regular-trace-final-model-v2-20261024/config.json').read_text())
roots=[Path(r) for r in c['lean_path']]
matched=[];missing={};different={}
for name,v in d['owners'].items():
 rel=Path(name.replace('.','/')).with_suffix('.olean')
 p=next((r/rel for r in roots if (r/rel).is_file()),None)
 if p is None:missing[name]=v;continue
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if h==v['sha256']:matched.append(name)
 else:different[name]={'expected':v,'remote_path':str(p),'remote_sha256':h}
out={'selected':len(d['owners']),'matched':len(matched),'missing':missing,'different':different,'config_sha256':hashlib.sha256(Path('/home/dombarker/project-offloads/pair-regular-trace-final-model-v2-20261024/config.json').read_bytes()).hexdigest(),'scope':'Read-only post-check selected object comparison; no proof replay'}
(w/'comparison.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
