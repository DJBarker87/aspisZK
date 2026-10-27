"""Freeze checked focused sources, then run one full axioms audit and one manifest audit."""
from pathlib import Path
import json,hashlib,re
root=Path(__file__).resolve().parents[2];lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z';out=root/'evidence/pv-op134-20261027'
report=json.loads((out/'AUDIT.json').read_text())
assert not report['unchecked'],report['unchecked']
assert report['charged']==98,report['charged']
mods=sorted(lean.glob('PV_Op134_*.lean'))
closure=''.join('import R1Z.'+p.stem+'\n' for p in mods)
for p in mods:
 for n in re.findall(r'^theorem (\w+)',p.read_text(),re.M):
  closure+='#print axioms R1Z.'+p.stem+'.'+n+'\n'
manifest='''import R1Z.PV_Op134_AuditClosure
#check R1Z.PV_Op134_ReferenceBundle.op134_reference
#check R1Z.PV_Op134_ReferenceBundle.rows_reference
#check R1Z.PV_Op134_ReferenceBundle.cells_reference
#check R1Z.PV_Op134_Inventory.complete
#print axioms R1Z.PV_CBM_CallbackBundle.op134_reference
#print axioms R1Z.PV_CBM_CallbackBundle.op133_reference
#print axioms R1Z.PV_CBM_CallbackBundle.op132_reference
#print axioms R1Z.PV_CBM_InventoryCardinality.cardinal
'''
for name,s in [('AuditClosure',closure),('AuditManifest',manifest)]:
 p=lean/('PV_Op134_'+name+'.lean');assert not p.exists();p.write_text(s)
entries=[]
for p in sorted(lean.glob('PV_Op134_*.lean')):
 s=p.read_text();entries.append(dict(module='R1Z/'+p.stem,path=str(p.relative_to(root)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),imports=re.findall(r'^import (\S+)',s,re.M)))
(out/'FOCUSED-MANIFEST.json').write_text(json.dumps(dict(scope='New-module frozen manifest and import/axioms audit only; no deployment release claim.',modules=entries),indent=2)+'\n')
print('Frozen',len(entries),'modules; two audits use reserved ID pool 50297–50299')
