from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');P=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028')
s=(P/'reached.py').read_text().split('\ndef root(')[0].replace('O.mkdir(exist_ok=True)','None')
ns={};exec(compile(s,str(P/'reached.py'),'exec'),ns)
out={}
for cohort,nodes in ns['nodes'].items():
 out[cohort]={m:[dict(key=k,body=nodes[k]) for k,t in ns['indexes'][cohort].get(m,[]) if ('core::' in k or m=='inv_with')] for m in ['index','eq','from_residual','into','next','inv_with']}
(D/'type-candidates.json').write_text(json.dumps(out,indent=2)+'\n')
print({c:{m:len(v) for m,v in a.items()} for c,a in out.items()})
