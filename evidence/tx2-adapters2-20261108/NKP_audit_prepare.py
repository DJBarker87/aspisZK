from pathlib import Path
import json,re,lzma,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent
mods=['NKP_BoxCuts','NKP_LaneCuts','NKP_LaneInduction','NKP_LaneCarrier','NKP_LaneCompletion','NKP_RegistryCuts']
roots=['AspisR1.RPx_Deployed.deployed']
roots+=json.loads((E.parent/'tx2-adapters-20261108/NKF_AUDIT_ROOTS.json').read_text())['groups'][0][1:]
for m in mods:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\w+)',s,re.M)[1]
 roots.extend(ns+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M))
assert len(roots)==len(set(roots))
s='import NKH_COMBINED_IMPORT\nimport NKF_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)
s+='\n'+''.join('#check '+r+'\n#print axioms '+r+'\n' for r in roots)
for n in ['NKP_BoxCuts.MasterCut','NKP_BoxCuts.CheckpointCut','NKP_BoxCuts.MasterReturned','NKP_BoxCuts.CheckpointReturned','NKP_LaneCuts.IterationCut','NKP_BoxCuts.master','NKP_BoxCuts.checkpoint']:
 s+='\nset_option pp.proofs false in\n#print '+n+'\n'
(E/'NKP_COMBINED_IMPORT.lean').write_text(s)
(E/'NKP_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots],scope='NKH+NKF combined, all new NKP top theorems, all NKF tops, deployed headline; inherited NKH raw audits retained with exact selected pins'),indent=1)+'\n')
expected={};variants=[]
for d,n in [('ledger18-20261108','NKH'),('tx2-adapters-20261108','NKF')]:
 for l in (E.parent/d/(n+'_EXPECTED_IMPORTS.jsonl')).read_text().splitlines():
  x=json.loads(l);name=x['module']
  if name in expected and expected[name]!=x['imports']:variants.append(dict(module=name,prior=expected[name],other=x['imports']))
  else:expected[name]=x['imports']
assert not variants,variants
for m in mods+['NKP_COMBINED_IMPORT']:
 expected[m]=['Init']+re.findall(r'^(?:public )?import(?: all)? (\S+)',(E/(m+'.lean')).read_text(),re.M)
(E/'NKP_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=v))+'\n' for n,v in sorted(expected.items())))
old=(E.parent/'tx2-adapters-20261108/NKF_ScanDriver.lean').read_text()
new=old.replace('NKF_COMBINED_IMPORT','NKP_COMBINED_IMPORT').replace('NKF_EXPECTED_IMPORTS','NKP_EXPECTED_IMPORTS').replace('NKF_LOADED_scan','NKP_LOADED_scan')
(E/'NKP_ScanDriver.lean').write_text(new)
(E/'NKP_ScanDriver.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='NKF_ScanDriver.lean',tofile='NKP_ScanDriver.lean')))
(E/'NKP_audit_one.py').write_text((E.parent/'tx2-adapters-20261108/NKF_audit_one.py').read_text().replace('NKF_binary_','NKP_binary_'))
# Pin all predecessor cohort objects/sidecars. Duplicate same-path pins must agree.
pins={}
for d,n in [('ledger18-20261108','NKH'),('tx2-adapters-20261108','NKF')]:
 x=json.loads(lzma.decompress((E.parent/d/(n+'_CLOSURE_PINS.json.xz')).read_bytes()))
 for row in x['selected_objects']:
  path=row['path'];prior=pins.get(path)
  if prior:assert prior['sha256']==row['sha256'],path
  pins[path]=row
(E/'NKP_PREDECESSOR_PINS.json').write_text(json.dumps(list(pins.values()),indent=1)+'\n')
print(json.dumps(dict(prepared_roots=len(roots),expected_modules=len(expected),predecessor_files=len(pins))))
