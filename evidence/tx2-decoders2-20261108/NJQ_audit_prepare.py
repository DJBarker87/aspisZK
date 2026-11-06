"""Freeze the checked support import and unchanged-driver runtime inventories."""
from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
rs=[json.loads(l)for l in(E/'NJQ_ATTEMPTS.jsonl').read_text().splitlines()]
modules=[];roots=[]
for f in sorted(E.glob('NJQ_*.lean')):
 if f.stem in ['NJQ_COMBINED_IMPORT','NJQ_ScanDriver','NJQ_ProofDriver']:continue
 h=sha(f.read_bytes())
 assert any(r['module']==f.stem and r['exit_status']==0 and h in r['source_hashes'].values()for r in rs),'Unchecked current source '+f.stem
 modules.append(f.stem)
 s=f.read_text();ns=re.search(r'^namespace (NJQ_\w+)',s,re.M)[1]
 roots += [ns+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
roots+=['AspisR1.RPx_Deployed.deployed']
s='import NJO_COMBINED_IMPORT\nimport NJI_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in modules)
s+='\n'+''.join('#check '+r+'\n#print axioms '+r+'\n'for r in roots)
(E/'NJQ_COMBINED_IMPORT.lean').write_text(s)
(E/'NJQ_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots],scope='CHECKED_SUPPORT_ONLY_NO_ROW_CREDIT'),indent=1)+'\n')
expected={};conflicts=[]
for path in [E.parent/'ledger15-20261108/NJO_EXPECTED_IMPORTS.jsonl',E.parent/'tx2-decoders-20261108/NJI_EXPECTED_IMPORTS.jsonl']:
 for l in path.read_text().splitlines():
  x=json.loads(l);n=x['module'];v=x['imports']
  if n in expected and expected[n]!=v:conflicts.append(dict(module=n,old=expected[n],new=v))
  expected[n]=v
assert not conflicts,conflicts
for name in modules+['NJQ_COMBINED_IMPORT']:
 expected[name]=['Init']+re.findall(r'^(?:public )?import(?: all)? (\S+)',(E/(name+'.lean')).read_text(),re.M)
(E/'NJQ_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=v))+'\n'for n,v in sorted(expected.items())))
old=(E.parent/'tx2-decoders-20261108/NJI_ScanDriver.lean').read_text();new=old.replace('NJI_COMBINED_IMPORT','NJQ_COMBINED_IMPORT').replace('NJI_EXPECTED_IMPORTS','NJQ_EXPECTED_IMPORTS').replace('NJI_LOADED_scan','NJQ_LOADED_scan')
(E/'NJQ_ScanDriver.lean').write_text(new)
(E/'NJQ_ScanDriver.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='NJI_ScanDriver.lean',tofile='NJQ_ScanDriver.lean')))
print(json.dumps(dict(modules=len(modules),roots=len(roots),expected_modules=len(expected),status='prepared; no audit run')))
