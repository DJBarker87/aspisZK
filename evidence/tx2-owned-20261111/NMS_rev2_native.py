"""Revision2 private recompilation of RSL-dependent native support.
No existing proved module is edited. The dependency/source mapping is retained.
"""
from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
seen=set();order=[]
def visit(n):
 if n in seen:return
 seen.add(n);p=E/(n+'.lean')
 if not p.exists():return
 for d in re.findall(r'^import (NMS_\w+)',p.read_text(),re.M):visit(d)
 order.append(n)
visit('NMS_Native242Children')
affected=set()
for n in order:
 deps=re.findall(r'^import (\w+)',(E/(n+'.lean')).read_text(),re.M)
 if any(d.startswith('RSL_') or d in affected for d in deps):affected.add(n)
renames={n:'NMS_R2N_'+n.removeprefix('NMS_') for n in affected}
renames.update(NMS_RSLRefine='NMS_R2Refine',NMS_RSLSuccess='NMS_R2Success',NMS_RSLStepFacts='NMS_R2StepFacts')
mods=[]
for n in order:
 if n not in affected or n in ['NMS_RSLRefine','NMS_RSLSuccess','NMS_RSLStepFacts']:continue
 t=(E/(n+'.lean')).read_text()
 for a,b in sorted(renames.items(),key=lambda x:-len(x[0])):t=t.replace(a,b)
 if n=='NMS_CloneReference':
  t=t.replace('RS.ofExcept account.data','RS.ofExcept account.bytes').replace('unfold data RS.ofExcept OwnedAccount.data','unfold data RS.ofExcept')
 (E/(renames[n]+'.lean')).write_text(t);mods.append(renames[n])
(E/'NMS_R2_NATIVE_PROVENANCE.json').write_text(json.dumps(dict(renames=renames,order=mods,change='NMS_CloneReference.snapshot_data now refers explicitly to stored bytes; new target is canonical rev2'),indent=2)+'\n')
if __name__=='__main__':
 from NMS_formal import run
 for i,m in enumerate(mods,308):
  r=run(f'NMS_L{i:03}','lean',m)
  if r['exit_status']:break
