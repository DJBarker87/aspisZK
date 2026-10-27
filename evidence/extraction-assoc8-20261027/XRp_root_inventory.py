"""Read-only, one-shot root source-closure and RPv cache availability audit."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
remote=r'''
from pathlib import Path
import json,hashlib
C=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
R=Path('/home/dombarker/project-offloads/codex-cx-replay-dry-20261026')
cfg=json.loads((R/'RPv_0357.json').read_text())
cache=[C,C/'objects']; rp=[Path(x) for x in cfg['env']['LEAN_PATH'].split(':')]
sources=[C]+[R/x for x in ['RPz5_sources','RPz4_sources','RPz3_sources','RPz_sources','RPv_sources','RPu_sources','RPt_sources','RPz8_sources','RPz7_sources']]
seen={};missing=[];unresolved=[]
def visit(m):
 if m in seen:return
 rel=m.replace('.','/')
 obj=next((p/(rel+'.olean') for p in cache if (p/(rel+'.olean')).exists()),None)
 src=next((p/(rel+'.lean') for p in sources if (p/(rel+'.lean')).exists()),None)
 seen[m]={'source':str(src) if src else None,'coherent_object':str(obj) if obj else None}
 if obj is None:
  rpo=next((p/(rel+'.olean') for p in rp if (p/(rel+'.olean')).exists()),None)
  missing.append({'module':m,'rpv_object':str(rpo) if rpo else None,'source':str(src) if src else None})
 if src:
  seen[m]['sha256']=hashlib.sha256(src.read_bytes()).hexdigest()
  for l in src.read_text().splitlines():
   if l.startswith('import '):
    for dep in l[7:].split():visit(dep)
 elif obj is None:unresolved.append(m)
visit('FJv_Top')
print(json.dumps({'root':'FJv_Top','rpv_config':str(R/'RPv_0357.json'),'rpv_lean_path':cfg['env']['LEAN_PATH'],'visited':seen,'missing':missing,'unresolved_sources':unresolved,'complete_source_closure':not unresolved,'kernel_audit':False,'decision':'defer root; missing canonical objects unavailable on pinned RPv path; audit new small groups'}))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=remote,text=True,capture_output=True,check=True)
(E/'XRp_ROOT_INVENTORY.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
x=json.loads(r.stdout);print({k:len(x[k]) for k in ['visited','missing','unresolved_sources']})
