"""Prepare a focused audit of source-matched new NNG roots only."""
from pathlib import Path
import json,hashlib,re,difflib
E=Path(__file__).resolve().parent
selected={}
for receipt in sorted(E.glob('NNG_L1[0-9][0-9][0-9]/receipt.json')):
 row=json.loads(receipt.read_text())
 if row['exit_status'] or row['kind']!='lean':continue
 for source,sha in row['source_hashes'].items():
  path=E/source
  if not source.startswith('NNG_generated/NNG_') or not path.is_file() or path.suffix!='.lean':continue
  if hashlib.sha256(path.read_bytes()).hexdigest()!=sha:continue
  own=E/path.name
  assert own.is_file() and hashlib.sha256(own.read_bytes()).hexdigest()==sha,path
  roots=[]
  for line in row['print_axioms']:
   assert 'sorryAx' not in line,line
   m=re.match(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",line)
   if m:roots.append(m[1])
  if roots:selected[path.stem]={'attempt':row['attempt'],'source':path.name,'sha256':sha,'roots':roots,'print_axioms':row['print_axioms']}
assert 'NNG_Candidate345' in selected and 'NNG_Candidate344' in selected
pairs=sorted((root,module) for module,item in selected.items() for root in item['roots'])
assert len(pairs)==len(set(root for root,module in pairs))
groups=[pairs[i:i+10] for i in range(0,len(pairs),10)]
(E/'NNG_Resume_AUDIT_ROOTS.json').write_text(json.dumps({'groups':[[root for root,module in g]for g in groups],'selected':selected,'reuse':'L363 unchanged raw-walker negative controls; no inherited root audit rerun'},indent=2))
(E/'NNG_Resume_AUDIT_MODULES.json').write_text(json.dumps([sorted(set(module for root,module in g)) for g in groups],indent=2))
combined='import NMQ_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in sorted(selected))
(E/'NNG_Resume_COMBINED.lean').write_text(combined)
old=(E/'NNG_R4Final_ProofDriver.lean').read_text();new=old.replace('NNG_R4Final','NNG_Resume')
(E/'NNG_Resume_ProofDriver.lean').write_text(new)
(E/'NNG_Resume_DRIVER.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='retained NNG_R4Final_ProofDriver.lean',tofile='NNG_Resume_ProofDriver.lean')))
for source,dest in [('NNG_R4Final_audit_batch.py','NNG_Resume_audit_batch.py'),('NNG_R4Final_link.py','NNG_Resume_link.py')]:
 (E/dest).write_text((E/source).read_text().replace('NNG_R4Final','NNG_Resume'))
pins={n:hashlib.sha256((E/n).read_bytes()).hexdigest()for n in ['NNG_Resume_AUDIT_ROOTS.json','NNG_Resume_AUDIT_MODULES.json']}
(E/'NNG_Resume_AUDIT_MANIFEST_PINS.json').write_text(json.dumps(pins,indent=2))
print(json.dumps({'roots':len(pairs),'modules':len(selected),'groups':len(groups)}))
