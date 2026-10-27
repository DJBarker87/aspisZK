"""Three final audit targets, preserving all inherited accepted modules."""
from pathlib import Path
import json,hashlib,re
r=Path(__file__).resolve().parents[2];e=r/'evidence/pv-join-20261026/resume4';p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'
x=json.loads((e.parent/'resume3/combined-audit-manifest.json').read_text())
names=sorted(x['theorems']+['R1Z.PV_Join_PublicFailure4.fail_public']);head='R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed'
for suffix,ns in [('A',names[:64]),('B',names[64:])]:
 s='import R1Z.PV_Join_CombinedAudit\nimport R1Z.PV_Join_PublicFailure4\n\n'
 s+=''.join(f'#print {n}\n#print axioms {n}\n' for n in ns)
 (p/f'PV_Join_FinalAudit4{suffix}.lean').write_text(s)
s='import R1Z.PV_Join_FinalAudit4A\nimport R1Z.PV_Join_FinalAudit4B\n\n'+''.join(f'#print axioms {n}\n' for n in names+[head]);(p/'PV_Join_CombinedAudit4.lean').write_text(s)
sources=x['sources']+[dict(module='R1Z.PV_Join_PublicFailure4',sha256=hashlib.sha256((p/'PV_Join_PublicFailure4.lean').read_bytes()).hexdigest(),theorems=['fail_public'])]
(e/'combined-audit-manifest.json').write_text(json.dumps(dict(theorems=names,headline=head,sources=sources,final_targets=['R1Z.PV_Join_FinalAudit4A','R1Z.PV_Join_FinalAudit4B','R1Z.PV_Join_CombinedAudit4'],kind='reuse inherited green source closure; final new focused audit, not release replay'),indent=2)+'\n')
print(len(names),'PV_Join theorems plus headline')
