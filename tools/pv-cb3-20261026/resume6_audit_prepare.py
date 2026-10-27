"""Prepare the three reserved audit targets, without launching a compiler.
Run after the last focused source change, never as a repeated full replay.
"""
from pathlib import Path
import json,re,hashlib
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cb3-20261026'
lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
tally=json.loads((out/'RESUME6_TALLY.json').read_text())
assert len(tally['lean_charged'])==97, 'Freeze only after focused attempt97'
proofs=[]
for p in sorted(lean.glob('PV_CB3_*.lean')):
    if 'Resume6' in p.stem:continue
    text=p.read_text();h=hashlib.sha256(text.encode()).hexdigest()
    matches=[]
    for receipt in out.glob('*.json'):
        try:d=json.loads(receipt.read_text())
        except ValueError:continue
        if not isinstance(d,dict):continue
        if d.get('module')=='R1Z/'+p.stem and d.get('exit')==0 and d.get('source_sha256')==h:
            matches.append((receipt.name,d))
    if matches:
        proofs.append(dict(module='R1Z.'+p.stem,source_sha256=h,receipt=matches[-1][0],
            axioms=[name for line in matches[-1][1].get('axioms',[]) for name in re.findall(r"'([^']+)'",line)]))
# All new ordinary modules require a green exact-source receipt before aggregation.
changed=__import__('subprocess').check_output(['git','diff','--name-only','29297acd5c','--',str(lean)],text=True).splitlines()
covered={x['module'] for x in proofs}
missing=[p for p in changed if p.endswith('.lean') and 'Resume6' not in p and 'R1Z.'+Path(p).stem not in covered]
assert not missing,missing
(out/'RESUME6_FROZEN_MANIFEST.json').write_text(json.dumps(proofs,indent=2)+'\n')
rows='''import R1Z.PV_CB3_CallbackBundle
import R1Z.PV_CB3_Op51Arbitrary
#print axioms R1Z.PV_CB3_CallbackBundle.op246_source
#print axioms R1Z.PV_CB3_CallbackBundle.op229_source
#print axioms R1Z.PV_CB3_CallbackBundle.op225_source
#print axioms R1Z.PV_CB3_CallbackBundle.op120_source
#print axioms R1Z.PV_CB3_Op51Arbitrary.op51_source
'''
(lean/'PV_CB3_Resume6RowsAudit.lean').write_text(rows)
imports='\n'.join('import '+x['module'] for x in proofs)+'\n'
targets=sorted({name for x in proofs for name in x['axioms']})
(lean/'PV_CB3_Resume6ReferenceAudit.lean').write_text(imports+'\n'.join('#print axioms '+name for name in targets)+'\n')
(lean/'PV_CB3_Resume6FinalManifest.lean').write_text('import R1Z.PV_CB3_Resume6RowsAudit\nimport R1Z.PV_CB3_Resume6ReferenceAudit\n')
print('Prepared only; imports',len(proofs),'reserved compiles98–100 remain unlaunched')
