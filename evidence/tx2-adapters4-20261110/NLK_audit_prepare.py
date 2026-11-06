"""One extended combined gate; semantic modules chosen from current successful receipts."""
from pathlib import Path
import json,re,lzma,hashlib,difflib
E=Path(__file__).resolve().parent
skip={'NLK_Inspect','NLK_ModelInspect','NLK_OwnedInspect','NLK_COMBINED_IMPORT','NLK_ScanDriver'}
receipts=[json.loads(l) for l in (E/'NLK_ATTEMPTS.jsonl').read_text().splitlines()]
mods=[];new=[]
for p in sorted(E.glob('NLK_*.lean')):
 m=p.stem
 if m in skip:continue
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 assert any(r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values() for r in receipts),m
 mods.append(m);s=p.read_text();ns=re.search(r'^namespace (\w+)',s,re.M)[1]
 new += [ns+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
roots=json.loads((E.parent/'ledger21-20261110/NLG_AUDIT_ROOTS.json').read_text())['roots']
for d,n in [('tx2-adapters3-20261109','NLA'),('sdk-borrow-20261109','NLF')]:
 x=json.loads((E.parent/d/(n+'_AUDIT_ROOTS.json')).read_text())
 for g in x['groups']:
  roots+=g
roots=list(dict.fromkeys(roots+new));assert 'AspisR1.RPx_Deployed.deployed' in roots
# Preserve ledger group ordering and add only genuinely additional roots.
old=json.loads((E.parent/'ledger21-20261110/NLG_AUDIT_ROOTS.json').read_text())['groups']
oldset={r for g in old for r in g};additional=[r for r in roots if r not in oldset]
groups=old+[additional] if additional else old
(E/'NLK_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=groups,roots=roots,new_roots=new,scope='full ledger21 plus NLA/NLF and every current NLK support theorem; no proposed CLOSED root'),indent=1)+'\n')
s='import NLG_COMBINED_IMPORT\nimport NLA_COMBINED_IMPORT\nimport NLF_SdkBorrowLaw\n'+''.join('import '+m+'\n' for m in mods)
s+='\n#print AspisR1.RPx_Deployed.deployed\n#print axioms AspisR1.RPx_Deployed.deployed\n'
s+='\n'.join('#print '+r+'\n#print axioms '+r for r in new)+'\n'
(E/'NLK_COMBINED_IMPORT.lean').write_text(s)
expected={}
for d,n in [('ledger21-20261110','NLG'),('tx2-adapters3-20261109','NLA'),('sdk-borrow-20261109','NLF')]:
 for l in (E.parent/d/(n+'_EXPECTED_IMPORTS.jsonl')).read_text().splitlines():
  x=json.loads(l);name=x['module'];imp=x['imports']
  if name in expected:assert expected[name]==imp,name
  expected[name]=imp
for m in mods+['NLK_COMBINED_IMPORT']:
 expected[m]=['Init']+re.findall(r'^(?:public )?import(?: all)? (\S+)',(E/(m+'.lean')).read_text(),re.M)
(E/'NLK_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=v))+'\n' for n,v in sorted(expected.items())))
old=(E.parent/'tx2-adapters3-20261109/NLA_ScanDriver.lean').read_text()
newdriver=old.replace('NLA_COMBINED_IMPORT','NLK_COMBINED_IMPORT').replace('NLA_EXPECTED_IMPORTS','NLK_EXPECTED_IMPORTS').replace('NLA_LOADED_scan','NLK_LOADED_scan')
(E/'NLK_ScanDriver.lean').write_text(newdriver)
(E/'NLK_ScanDriver.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),newdriver.splitlines(True),fromfile='NLA_ScanDriver.lean',tofile='NLK_ScanDriver.lean')))
(E/'NLK_audit_one.py').write_text((E.parent/'tx2-adapters3-20261109/NLA_audit_one.py').read_text().replace('NLA_binary_','NLK_binary_'))
pins={}
for d,n in [('ledger21-20261110','NLG'),('tx2-adapters3-20261109','NLA'),('sdk-borrow-20261109','NLF')]:
 x=json.loads(lzma.decompress((E.parent/d/(n+'_CLOSURE_PINS.json.xz')).read_bytes()))
 for row in x.get('selected_objects',x.get('objects',[])):
  path=row['path'];prior=pins.get(path)
  if prior:assert prior['sha256']==row['sha256'],path
  pins[path]=row
(E/'NLK_PREDECESSOR_PINS.json.xz').write_bytes(lzma.compress(json.dumps(list(pins.values())).encode()))
(E/'NLK_SEMANTIC_MODULES.json').write_text(json.dumps(mods,indent=1)+'\n')
print(json.dumps(dict(modules=len(mods),roots=len(roots),new=len(new),groups=len(groups),predecessor_pins=len(pins))))
