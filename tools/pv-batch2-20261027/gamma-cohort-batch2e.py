"""One private replay module for six unchanged, previously checked gamma proofs.
No proof term or tactic limit changes; dependency imports are topologically joined.
The unit restores a deleted private cache, not a new generic lemma candidate.
"""
from pathlib import Path
import re,json,hashlib,subprocess,sys
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');E=Path('evidence/pv-batch2-20261027/batch2e')
names=['PV_B2_C_AddSmallAgreement','PV_B2_C_GammaNumeric','PV_B2_C_GammaTotal','PV_B2_C_GammaHelpers','PV_B2_C_U32Arithmetic','PV_B2_C_GammaSource'];imports=[];bodies=[];pins=[]
for name in names:
 p=L/(name+'.lean');b=p.read_bytes();assert b==subprocess.check_output(['git','show','HEAD:'+str(p)])
 s=b.decode();pins.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest()))
 for imp in re.findall(r'^import (\S+)',s,re.M):
  if imp.replace('R1Z.','') not in names and imp not in imports:imports.append(imp)
 s=re.sub(r'^import [^\n]+\n','',s,flags=re.M)
 bodies.append('-- Unchanged previously checked component '+name+'\nsection\n'+s+'\nend\n')
out='\n'.join('import '+i for i in imports)+'\n'+''.join(bodies);p=L/'PV_B2_E_GammaCohort.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
(E/'GAMMA-COHORT-SOURCE-PINS.json').write_text(json.dumps(dict(components=pins,imports=imports,proof_changes=False,tactic_limit_changes=False,reason='restore own deleted cache with one new private module; prior focused generic proofs already checked in batch2c'),indent=2)+'\n')
print('gamma cohort',len(names),'unchanged checked components; no XR import')
