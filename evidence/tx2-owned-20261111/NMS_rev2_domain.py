"""New-prefix revision2 carrier helpers, preserving the prior modules."""
from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
base=json.loads((E/'NMS_R2_NATIVE_PROVENANCE.json').read_text())['renames']
base['NMS_RSLDomains']='NMS_R2Domains'
seen=set();order=[]
def go(n):
 if n in seen:return
 seen.add(n);p=E/(n+'.lean')
 if not p.exists():return
 for d in re.findall(r'^import (NMS_\w+)',p.read_text(),re.M):go(d)
 order.append(n)
for n in ['NMS_InterpretedNativeDomain','NMS_RSLBindings','NMS_RSLScalarEq','NMS_RawTry','NMS_ScanRegular']:go(n)
affected=set(base)
for n in order:
 deps=re.findall(r'^import (\w+)',(E/(n+'.lean')).read_text(),re.M)
 if any(d.startswith('RSL_') or d in affected for d in deps):affected.add(n)
renames={n:'NMS_R2N_'+n.removeprefix('NMS_') for n in affected};renames.update(base)
mods=[]
for n in order:
 if n not in affected or n in base:continue
 t=(E/(n+'.lean')).read_text()
 for a,b in sorted(renames.items(),key=lambda x:-len(x[0])):t=t.replace(a,b)
 if n=='NMS_InterpretedNativeDomain':t=t.replace('RSL.verifierCheckpoint (account acc6) (b32 program) false = .ok ()','(account acc6).length = .ok RSL.CHECKPOINT_BYTES')
 (E/(renames[n]+'.lean')).write_text(t);mods.append(renames[n])
(E/'NMS_R2_DOMAIN_PROVENANCE.json').write_text(json.dumps(dict(renames=renames,order=mods),indent=2)+'\n')
if __name__=='__main__':
 from NMS_formal import run
 for i,m in enumerate(mods,328):
  r=run(f'NMS_L{i:03}','lean',m)
  if r['exit_status']:break
