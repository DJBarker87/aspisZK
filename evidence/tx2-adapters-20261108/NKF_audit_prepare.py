from pathlib import Path
import json,re,difflib
E=Path(__file__).resolve().parent
modules=['NKF_BoxModel','NKF_MasterBox','NKF_CheckpointBox','NKF_BoxInstall','NKF_ArrayFrame','NKF_BoxFields','NKF_Windows','NKF_Roots','NKF_LaneTrace','NKF_PdaModel']
roots=['AspisR1.RPx_Deployed.deployed']
for m in modules:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\w+)',s,re.M)[1]
 roots.extend(ns+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M))
assert len(roots)==len(set(roots))
s='import NKC_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in modules)
s+='\n'+''.join('#check '+r+'\n#print axioms '+r+'\n' for r in roots)
for n in ['NKF_Roots.MasterCut','NKF_Roots.CheckpointCut','NKF_Roots.MasterTail','NKF_Roots.CheckpointTail','NKF_BoxFields.Master','NKF_BoxFields.Checkpoint','NKF_Windows.Master','NKF_Windows.Checkpoint','NKF_Roots.master','NKF_Roots.checkpoint']:
 s+='\nset_option pp.proofs false in\n#print '+n+'\n'
(E/'NKF_COMBINED_IMPORT.lean').write_text(s)
(E/'NKF_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots],scope='NKC combined + every current NKF top theorem + deployed headline; NKC raw audit retained under exact selected object pins'),indent=1)+'\n')
expected={}
for l in (E.parent/'ledger17-20261108/NKC_EXPECTED_IMPORTS.jsonl').read_text().splitlines():
 x=json.loads(l);expected[x['module']]=x['imports']
for m in modules+['NKF_COMBINED_IMPORT']:
 expected[m]=['Init']+re.findall(r'^(?:public )?import(?: all)? (\S+)',(E/(m+'.lean')).read_text(),re.M)
(E/'NKF_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=v))+'\n' for n,v in sorted(expected.items())))
old=(E.parent/'tx2-decoders3-20261108/NJY_ScanDriver.lean').read_text()
new=old.replace('NJY_COMBINED_IMPORT','NKF_COMBINED_IMPORT').replace('NJY_EXPECTED_IMPORTS','NKF_EXPECTED_IMPORTS').replace('NJY_LOADED_scan','NKF_LOADED_scan')
(E/'NKF_ScanDriver.lean').write_text(new)
(E/'NKF_ScanDriver.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='NJY_ScanDriver.lean',tofile='NKF_ScanDriver.lean')))
(E/'NKF_audit_one.py').write_text((E.parent/'tx2-decoders3-20261108/NJY_audit_one.py').read_text().replace('NJY_binary_','NKF_binary_'))
print(json.dumps(dict(prepared_roots=len(roots),expected_modules=len(expected))))
