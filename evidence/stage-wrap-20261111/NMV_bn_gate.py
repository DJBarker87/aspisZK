"""Only new NMV tops; existing raw walker and launcher remain unchanged."""
from NMV_formal import *
import re
mods=['NMV_WindowEval','NMV_WindowClock','NMV_WindowStage','NMV_WindowRoots','NMV_NoWrite','NMV_NoWriteSdk','NMV_NoWritePool','NMV_NoWriteOwned','NMV_NoWrite241','NMV_SdkExec','NMV_SnapshotExec','NMV_CopyExec','NMV_ConcreteWindows','NMV_G2Reference','NMV_TasRoots']
def manifests():
 roots=[];owners={}
 for m in mods:
  s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1]
  names=re.findall(r'^theorem (\w+)',s,re.M)+(['packet'] if m=='NMV_TasRoots' else [])
  prints=re.findall(r'^#print axioms (\w+)',s,re.M)
  assert set(names)==set(prints),(m,names,prints)
  for n in names:roots.append(ns+'.'+n);owners[ns+'.'+n]=m
 old=json.loads((E/'NMV_AUDIT_ROOTS.json').read_text());om=json.loads((E/'NMV_AUDIT_MODULES.json').read_text())
 groups=old['groups'][:12];om=om[:12]
 for i in range(0,len(roots),8):
  g=roots[i:i+8];groups.append(g);om.append(sorted({owners[n] for n in g}))
 (E/'NMV_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=groups,roots=[n for g in groups for n in g]),indent=1)+'\n')
 (E/'NMV_AUDIT_MODULES.json').write_text(json.dumps(om,indent=1)+'\n')
 (E/'NMV_BN_ROOTS.json').write_text(json.dumps(dict(modules=mods,roots=roots,owners=owners,groups=list(range(12,len(groups)))),indent=1)+'\n')
 return roots,list(range(12,len(groups)))
if __name__=='__main__':
 mode=sys.argv[1];roots,groups=manifests()
 if mode=='combined':
  (E/'NMV_BN_COMBINED_IMPORT.lean').write_text('import NMV_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)+'\n#print axioms NMV_TasRoots.packet\n#print axioms NMV_TasRoots.field240\n#print axioms NMV_TasRoots.field344\n#print axioms NMV_TasRoots.weakFrame\n')
  r=run('NMV_L112','lean','NMV_BN_COMBINED_IMPORT');sys.exit(r['exit_status'])
 elif mode=='audit':
  for i,g in enumerate(groups,113):
   a=f'NMV_L{i:03}'
   files={n:(E/n).read_text() for n in ['NMV_batch.py','NMV_AUDIT_ROOTS.json','NMV_AUDIT_MODULES.json']}
   r=run(a,'audit','proof'+str(g),['python3','NMV_batch.py','proof'+str(g)],files)
   if r['exit_status']:raise SystemExit(r['exit_status'])
 elif mode=='manifests':print(json.dumps(dict(roots=len(roots),groups=groups)))
 else:raise ValueError(mode)
