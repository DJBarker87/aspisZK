from pathlib import Path
import json,re,lzma,hashlib,difflib
E=Path(__file__).resolve().parent
mods=['NLA_RootPrefix','NLA_LaneStep','NLA_DataPrefix','NLA_OwnedData','NLA_AllocationPrefix','NLA_PdaStatus']
roots=['AspisR1.RPx_Deployed.deployed']
roots+=json.loads((E.parent/'tx2-adapters2-20261108/NKP_AUDIT_ROOTS.json').read_text())['groups'][0][1:]
new=[]
for m in mods:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\w+)',s,re.M)[1]
 new.extend(ns+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M))
roots+=new
assert len(roots)==len(set(roots))
s='import NKW_COMBINED_IMPORT\nimport NKP_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)
s+='\n'+''.join('#check '+r+'\n#print axioms '+r+'\n' for r in roots)
s+='\n'+''.join('set_option pp.proofs false in\n#print '+r+'\n' for r in new)
(E/'NLA_COMBINED_IMPORT.lean').write_text(s)
(E/'NLA_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots],scope='NKW+NKP canonical combined import, all new NLA support, deployed headline; no row closure asserted'),indent=1)+'\n')
expected={}
for d,n in [('ledger20-20261109','NKW'),('tx2-adapters2-20261108','NKP')]:
 for l in (E.parent/d/(n+'_EXPECTED_IMPORTS.jsonl')).read_text().splitlines():
  x=json.loads(l);name=x['module']
  if name in expected:assert expected[name]==x['imports'],name
  else:expected[name]=x['imports']
for m in mods+['NLA_COMBINED_IMPORT']:
 expected[m]=['Init']+re.findall(r'^(?:public )?import(?: all)? (\S+)',(E/(m+'.lean')).read_text(),re.M)
(E/'NLA_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=v))+'\n' for n,v in sorted(expected.items())))
old=(E.parent/'tx2-adapters2-20261108/NKP_ScanDriver.lean').read_text()
newdriver=old.replace('NKP_COMBINED_IMPORT','NLA_COMBINED_IMPORT').replace('NKP_EXPECTED_IMPORTS','NLA_EXPECTED_IMPORTS').replace('NKP_LOADED_scan','NLA_LOADED_scan')
(E/'NLA_ScanDriver.lean').write_text(newdriver)
(E/'NLA_ScanDriver.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),newdriver.splitlines(True),fromfile='NKP_ScanDriver.lean',tofile='NLA_ScanDriver.lean')))
(E/'NLA_audit_one.py').write_text((E.parent/'tx2-adapters2-20261108/NKP_audit_one.py').read_text().replace('NKP_binary_','NLA_binary_'))
pins={}
for d,n in [('ledger20-20261109','NKW'),('tx2-adapters2-20261108','NKP')]:
 x=json.loads(lzma.decompress((E.parent/d/(n+'_CLOSURE_PINS.json.xz')).read_bytes()))
 for row in x['selected_objects']:
  path=row['path'];prior=pins.get(path)
  if prior:assert prior['sha256']==row['sha256'],path
  pins[path]=row
(E/'NLA_PREDECESSOR_PINS.json').write_text(json.dumps(list(pins.values()),indent=1)+'\n')
print(json.dumps(dict(prepared_roots=len(roots),expected_modules=len(expected),predecessor_files=len(pins))))
