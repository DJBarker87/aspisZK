from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ats=[json.loads(l) for l in (E/'PCD_ATTEMPTS.jsonl').read_text().splitlines()]
mods=sorted(p.stem for p in E.glob('PCD_*.lean') if p.stem not in ['PCD_COMBINED_IMPORT','PCD_ProofDriver'])
roots=['AspisR1.RPx_Deployed.deployed','PCD_PRODUCERS.P1','PCD_PRODUCERS.P2','PCD_PRODUCERS.P3']
pins=[]
for m in mods:
 p=E/(m+'.lean');h=sha(p);ok=[r for r in ats if r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values()]
 assert ok,('CURRENT_SOURCE_NOT_CHECKED',m)
 pins.append(dict(module=m,source_sha256=h,receipt=ok[-1]['attempt']))
 for line in ok[-1]['print_axioms']:
  assert 'sorryAx' not in line,line
  name=re.match("'([^']+)'",line)[1]
  if name not in roots:roots.append(name)
 for row in re.findall(r'def (RowSpec_POOL_\d+)',p.read_text()):roots.append('PCD.'+row)
(E/'PCD_COMBINED_IMPORT.lean').write_text('import NLS_COMBINED_IMPORT\nimport NLO_COMBINED_IMPORT\nimport NLF_SdkBorrowLaw\n'+''.join('import '+m+'\n' for m in mods)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
(E/'PCD_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots]),indent=1)+'\n')
(E/'PCD_AUDIT_MODULES.json').write_text(json.dumps([['PCD_COMBINED_IMPORT']])+'\n')
(E/'PCD_CURRENT_SOURCE_CHECK.json').write_text(json.dumps(pins,indent=1)+'\n')
expected={};variants=[]
for f in ['pool-settle-20261106/NIB_EXPECTED_IMPORTS.jsonl','sdk-borrow-20261109/NLF_EXPECTED_IMPORTS.jsonl','ledger23-20261110/NLS_EXPECTED_IMPORTS.jsonl']:
 for line in (E.parent/f).read_text().splitlines():
  x=json.loads(line);n=x['module']
  if n in expected and expected[n]!=x:variants.append(dict(module=n,earlier=expected[n],current=x,current_manifest=f))
  expected[n]=x
for m in mods+['PCD_COMBINED_IMPORT']:
 expected[m]=dict(module=m,imports=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',(E/(m+'.lean')).read_text(),re.M))))
(E/'PCD_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(expected[m])+'\n' for m in sorted(expected)))
(E/'PCD_EXPECTED_VARIANTS.json').write_text(json.dumps({'variants':variants,'selection':'Latest NLS manifest authoritative for shared current cohort; actual loaded scan must validate every selected header. No variant is claimed binary-identical.'},indent=1)+'\n')
print(f'Focused audit prepared: {len(mods)} current compiled modules, {len(roots)} roots, {len(variants)} retained expected-header variants.')
