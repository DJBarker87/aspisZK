"""Generate one focused cached axioms audit; no compiler invocation."""
from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parents[3];d=r/'docs/research/v8-r0-zk-20261009/lean/R1Z';e=r/'evidence/pv-rw-step-20261026'
files=sorted(p for p in d.glob('PV_RW_*.lean') if p.stem!='PV_RW_Audit');imports=[];reports=[];pins=[]
for p in files:
 s=p.read_text();ns=re.search(r'^namespace (R1Z\.PV_RW_\w+)$',s,re.M).group(1)
 names=re.findall(r'^#print axioms ([\w.]+)$',s,re.M)
 declared=re.findall(r'^theorem (\w+)',s,re.M)
 assert set(declared)<=set(names),(p,declared,names)
 imports.append('import R1Z.'+p.stem)
 reports += ['#print axioms '+ns+'.'+name for name in names]
 pins.append(dict(path=str(p.relative_to(r)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),theorems=declared))
text='\n'.join(imports)+'''\nimport R1Z.PrivacyR1HeadlineDeployedReal
-- Focused cached closure audit, not a coherent frozen release replay.
'''+ '\n'.join(reports)+'''\n#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
'''
(d/'PV_RW_Audit.lean').write_text(text)
(e/'focused-source-manifest.json').write_text(json.dumps(dict(sources=pins,modules=len(pins),theorem_reports=len(reports),scope='One focused cached closure audit; no deployment or release replay inference.'),indent=2)+'\n')
print(len(pins),'modules',len(reports),'new theorem reports')
