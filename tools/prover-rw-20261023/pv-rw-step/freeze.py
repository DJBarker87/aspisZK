"""Freeze the final focused source manifest after every new leaf is green."""
from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parents[3];d=r/'docs/research/v8-r0-zk-20261009/lean/R1Z';e=r/'evidence/pv-rw-step-20261026';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
accepted={}
for p in [*e.glob('*-receipt.json'),*(e/'local').glob('*-receipt.json')]:
 x=json.loads(p.read_text())
 if x.get('exit_status')==0 and 'module' in x:accepted.setdefault(x['module'],set()).add(x['source_sha256'])
files=sorted(p for p in d.glob('PV_RW_*.lean') if p.stem not in ['PV_RW_FinalAudit','PV_RW_FrozenManifest']);imports=[];reports=[];pins=[]
for p in files:
 module='R1Z/'+p.stem;assert sha(p) in accepted.get(module,set()),('not green',module)
 s=p.read_text();imports.append('import R1Z.'+p.stem)
 ns=re.search(r'^namespace (R1Z\.PV_RW_\w+)$',s,re.M)
 declared=re.findall(r'^theorem (\w+)',s,re.M);names=re.findall(r'^#print axioms ([\w.]+)$',s,re.M)
 if ns:
  assert set(declared)<=set(names),(p,declared,names)
  reports += ['#print axioms '+(name if name.startswith('R1Z.') else ns[1]+'.'+name) for name in names]
 pins.append(dict(path=str(p.relative_to(r)),sha256=sha(p),theorems=declared))
assert not (d/'PV_RW_FinalAudit.lean').exists() and not (d/'PV_RW_FrozenManifest.lean').exists()
(d/'PV_RW_FinalAudit.lean').write_text('\n'.join(imports)+'''\nimport R1Z.PrivacyR1HeadlineDeployedReal
-- Final focused cached axioms audit; no full release/source replay claim.
'''+ '\n'.join(reports)+'''\n#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
''')
(d/'PV_RW_FrozenManifest.lean').write_text('''import R1Z.PV_RW_FinalAudit
-- One final frozen focused manifest check, reusing the pinned compiled cache.
-- Original-helper source association and whole model data equality stay open.
#print axioms R1Z.PV_RW_CombinedCompression.arity16
#print axioms R1Z.PV_RW_CombinedBodyData.refinement_of_data
#print axioms R1Z.PV_RW_DataPartsIff.exact_criterion
#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
''')
for name in ['PV_RW_FinalAudit','PV_RW_FrozenManifest']:
 p=d/(name+'.lean');pins.append(dict(path=str(p.relative_to(r)),sha256=sha(p),theorems=[]))
(e/'final-focused-source-manifest.json').write_text(json.dumps(dict(sources=pins,leaf_modules=len(files),theorem_reports=len(reports),scope='Final focused cached closure audit and one frozen focused manifest; no original whole-helper source association, source dependency rebuild, release or endpoint closure inferred.'),indent=2)+'\n')
print(len(files),'leaf modules',len(reports),'theorem reports')
