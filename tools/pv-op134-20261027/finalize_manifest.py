"""Freeze the focused source manifest after its targets are checked, before audits."""
from pathlib import Path
import json,hashlib,re,sys
root=Path(__file__).resolve().parents[2];lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z';out=root/'evidence/pv-op134-20261027'
report=json.loads((out/'AUDIT.json').read_text())
assert not report['unchecked'],report['unchecked']
assert report['charged']==97,report['charged']
mods=sorted(lean.glob('PV_Op134_*.lean'))
reference='''import R1Z.PV_Op134_ReferenceBundle
#print axioms R1Z.PV_Op134_ReferenceBundle.op134_reference
#print axioms R1Z.PV_Op134_ReferenceBundle.rows_reference
#print axioms R1Z.PV_Op134_InventoryCallback.callback
'''
closure=''.join('import R1Z.'+p.stem+'\n' for p in mods)
for p in mods:
 for n in re.findall(r'^theorem (\w+)',p.read_text(),re.M):
  if p.stem not in ['PV_Op134_ReferenceBundle','PV_Op134_InventoryCallback']:
   closure+='#print axioms R1Z.'+p.stem+'.'+n+'\n'
manifest='''import R1Z.PV_Op134_AuditReference
import R1Z.PV_Op134_AuditClosure
#check R1Z.PV_Op134_ReferenceBundle.op134_reference
#check R1Z.PV_Op134_ReferenceBundle.rows_reference
#check R1Z.PV_Op134_Inventory.complete
#print axioms R1Z.PV_CBM_CallbackBundle.op134_reference
#print axioms R1Z.PV_CBM_CallbackBundle.op133_reference
#print axioms R1Z.PV_CBM_CallbackBundle.op132_reference
#print axioms R1Z.PV_CBM_InventoryCardinality.cardinal
'''
for name,s in [('AuditReference',reference),('AuditClosure',closure),('AuditManifest',manifest)]:
 p=lean/('PV_Op134_'+name+'.lean');assert not p.exists();p.write_text(s)
entries=[]
for p in sorted(lean.glob('PV_Op134_*.lean')):
 s=p.read_text();entries.append(dict(module='R1Z/'+p.stem,path=str(p.relative_to(root)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),imports=re.findall(r'^import (\S+)',s,re.M)))
(out/'FOCUSED-MANIFEST.json').write_text(json.dumps(dict(scope='New-module frozen manifest and import/axioms audit only; no deployment release claim.',modules=entries),indent=2)+'\n')
print('Frozen',len(entries),'modules; audit IDs 50297–50299')
