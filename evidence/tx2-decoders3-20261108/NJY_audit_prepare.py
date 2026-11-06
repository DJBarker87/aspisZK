from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent;Q=E.parent/'tx2-decoders2-20261108'
modules=['NJY_Identity','NJY_Checkpoint','NJY_Master','NJY_Entry','NJY_Registry','NJY_WindowStep','NJY_Roots']
roots=json.loads((Q/'NJQ_AUDIT_ROOTS.json').read_text())['groups'][0]
for m in modules:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\w+)',s,re.M)[1]
 roots += [ns+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
roots=list(dict.fromkeys(roots))
# Exactly one combined import, after all focused targets pass. Retain all NJQ support.
s='import NJW_COMBINED_IMPORT\nimport NJQ_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in modules)
s+='\n'+''.join('#check '+r+'\n#print axioms '+r+'\n' for r in roots)
s+='\nset_option pp.proofs false in\n#print NJQ_MasterTotal.Cut\nset_option pp.proofs false in\n#print NJQ_EntryTotal.Cut\nset_option pp.proofs false in\n#print NJQ_RegistryTotal.Cut\nset_option pp.proofs false in\n#print NJQ_CheckpointTotal.Cut\n'
(E/'NJY_COMBINED_IMPORT.lean').write_text(s)
(E/'NJY_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots],scope='NJW+NJQ+NJY+AspisR1.RPx_Deployed.deployed; audit all NJY and NJQ roots; baseline NJW raw audit retained'),indent=1)+'\n')
expected={}
for p in [E.parent/'ledger16-20261108/NJW_EXPECTED_IMPORTS.jsonl',Q/'NJQ_EXPECTED_IMPORTS.jsonl']:
 for l in p.read_text().splitlines():
  x=json.loads(l);n=x['module'];v=x['imports'];assert n not in expected or expected[n]==v, n;expected[n]=v
for m in modules+['NJY_COMBINED_IMPORT']:
 expected[m]=['Init']+re.findall(r'^(?:public )?import(?: all)? (\S+)',(E/(m+'.lean')).read_text(),re.M)
(E/'NJY_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=v))+'\n' for n,v in sorted(expected.items())))
old=(Q/'NJQ_ScanDriver.lean').read_text();new=old.replace('NJQ_COMBINED_IMPORT','NJY_COMBINED_IMPORT').replace('NJQ_EXPECTED_IMPORTS','NJY_EXPECTED_IMPORTS').replace('NJQ_LOADED_scan','NJY_LOADED_scan');(E/'NJY_ScanDriver.lean').write_text(new)
(E/'NJY_ScanDriver.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='NJQ_ScanDriver.lean',tofile='NJY_ScanDriver.lean')))
(E/'NJY_audit_one.py').write_text((Q/'NJQ_audit_one.py').read_text().replace('NJQ_binary_','NJY_binary_'))
print(json.dumps(dict(prepared_roots=len(roots),expected_modules=len(expected))))
