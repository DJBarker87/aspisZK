from pathlib import Path
import json,difflib,re,hashlib
E=Path(__file__).resolve().parent;I=E.parent/'pool-b3-20261106'
for name in ['ProofDriver.lean','Driver.lean','batch.py']:
 old=(I/('NHP_'+name)).read_text();new=old.replace('NHP_','NIE_');(E/('NIE_'+name)).write_text(new)
 (E/('NIE_'+name+'.diff')).write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='retained/NHP_'+name,tofile='NIE_'+name)))
roots=[]
for p in E.glob('NIE_*.lean'):
 if p.stem.endswith(('Driver','COMBINED_IMPORT')):continue
 ns=re.search(r'^namespace\s+(\S+)',p.read_text(),re.M)
 if ns:
  roots += [ns[1]+'.'+n for n in re.findall(r'^theorem\s+(\w+)',p.read_text(),re.M)]
roots+=['AspisR1.RPx_Deployed.deployed']
(E/'NIE_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots]),indent=2)+'\n')
base=(I/'NHP_EXPECTED_IMPORTS.jsonl').read_text();names=set(json.loads(s)['module'] for s in base.splitlines());added=[]
for p in E.glob('NIE_*.lean'):
 if p.stem.endswith('Driver'):continue
 imports=['Init']+re.findall(r'^import\s+(\S+)',p.read_text(),re.M)
 if p.stem not in names:added.append(json.dumps(dict(module=p.stem,imports=imports)))
(E/'NIE_EXPECTED_IMPORTS.jsonl').write_text(base.rstrip()+'\n'+'\n'.join(added)+'\n')
(E/'NIE_AUDIT_ADAPTATION.json').write_text(json.dumps(dict(method='Retained NHP driver with module/root manifest names changed only; unchanged NFA_WALKER and memory wrapper imports',driver_inputs={str(I/('NHP_'+n)):hashlib.sha256((I/('NHP_'+n)).read_bytes()).hexdigest() for n in ['ProofDriver.lean','Driver.lean','batch.py']},raw_fixture_run_required=True,fixtures=8),indent=2)+'\n')
print(json.dumps(dict(roots=len(roots),new_expected_modules=len(added))))
