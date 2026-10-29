"""Lean candidate copy identity only. This is NOT a native structural checker."""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-rdcd3-20261028'
mp=json.load(open(E/'v217-owned-candidates.json'))['mapping'];out=[]
def normalize(s):
 for a,b in sorted(mp.items(),key=lambda x:-len(x[0])):s=s.replace(a,b)
 s=re.sub(r'^import .*\n','',s,flags=re.M)
 s=re.sub(r'^set_option max(?:Heartbeats|RecDepth).*\n','',s,flags=re.M)
 return s
for old,new in [('ProverRwP7CurrentFieldSource','PV_RDCD3_FieldSource'),('PV_CB_MaskSource','PV_RDCD3_CB_MaskSource'),('PV_CB_OwnedMask','PV_RDCD3_CB_OwnedMask')]:
 a=L/(old+'.lean');b=L/(new+'.lean');assert normalize(a.read_text())==normalize(b.read_text()),(old,new)
 out.append(dict(original=str(a.relative_to(R)),original_sha256=hashlib.sha256(a.read_bytes()).hexdigest(),owned=str(b.relative_to(R)),owned_sha256=hashlib.sha256(b.read_bytes()).hexdigest()))
(E/'v217-program-copy-identity.json').write_text(json.dumps(dict(records=out,qualification='Lean program text preserved modulo namespace/import/resource-override changes. No Rust correspondence or whole-row credit; complete deployed structural binding remains required.'),indent=2)+'\n')
print('Three candidate program texts match; not native/source-row credit')
