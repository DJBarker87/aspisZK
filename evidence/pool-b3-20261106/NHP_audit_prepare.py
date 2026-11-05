"""Only allowed ax2 filename/import retargets of the admitted NHC audit drivers."""
from pathlib import Path
import json,re,difflib,hashlib
E=Path(__file__).resolve().parent;K=E.parent/'pool-leaves-20261105'
roots=['AspisR1.RPx_Deployed.deployed','NHP_StackRef.NHP_reference.transaction_level','NHC_ErrorConversion.result']
for p in E.glob('NHP_L*/stdout.log'):
 if json.loads((p.parent/'receipt.json').read_text())['exit_status']:continue
 for line in p.read_text().splitlines():
  m=re.match(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",line)
  if m and m[1].startswith('NHP_'):roots.append(m[1])
roots=sorted(set(roots));(E/'NHP_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots[i:i+200] for i in range(0,len(roots),200)]),indent=1)+'\n')
changes={'NHC_AUDIT_ROOTS':'NHP_AUDIT_ROOTS','NHC_COMBINED_IMPORT':'NHP_COMBINED_IMPORT','NHC_EXPECTED_IMPORTS':'NHP_EXPECTED_IMPORTS','NHC_LOADED_scan':'NHP_LOADED_scan'}
provenance=[]
for name in ['ProofDriver','Driver']:
 before=(K/('NHC_'+name+'.lean')).read_text();after=before
 for old,new in changes.items():after=after.replace(old,new)
 (E/('NHP_'+name+'.lean')).write_text(after)
 (E/('NHP_'+name+'.diff')).write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='NHC_'+name,tofile='NHP_'+name)))
 provenance.append(dict(source=str(K/('NHC_'+name+'.lean')),source_sha256=hashlib.sha256(before.encode()).hexdigest(),target='NHP_'+name+'.lean',sha256=hashlib.sha256(after.encode()).hexdigest(),allowed_replacements=changes,algorithm_unchanged=True))
(E/'NHP_AUDIT_DRIVER_PROVENANCE.json').write_text(json.dumps(provenance,indent=2)+'\n')
(E/'NHP_batch.py').write_text((K/'NHC_batch.py').read_text().replace('NHC_','NHP_'))
baselines={r['module']:r for r in map(json.loads,(K/'NHC_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for p in (p for p in E.rglob('*.lean') if 'sources' not in p.relative_to(E).parts):
 name=str(p.relative_to(E)).removesuffix('.lean').replace('/','.')
 baselines[name]=dict(module=name,imports=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M))))
(E/'NHP_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(row)+'\n' for name,row in sorted(baselines.items())))
print(json.dumps(dict(roots=len(roots),baselines=len(baselines),driver_algorithm_unchanged=True)))
