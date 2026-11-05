"""Adapt only module/root lists and runtime names of the admitted NGN driver."""
from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent;S=E.parent/'slice-d-prepared-20261105'
(E/'NGT_native').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:(E/'NGT_native'/n).write_bytes((S/'NGN_native'/n).read_bytes())
for n in ['Driver','ProofDriver','batch.py']:
 old='NGN_'+n+('' if n.endswith('.py') else '.lean');new=old.replace('NGN','NGT');s=(S/old).read_text();t=s.replace('NGN','NGT');(E/new).write_text(t);(E/('NGT_'+n.replace('.py','')+'_ADAPTATION.diff')).write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile=old,tofile=new)))
base=[json.loads(l) for l in (S/'NGN_EXPECTED_IMPORTS.jsonl').read_text().splitlines()]
mods={r['module']:r['imports'] for r in base}
# New modules have exact source import lists. Unchanged prerequisites retain
# their original complete import list; Init is implicit in these Lean files.
for p in E.glob('NGT_*.lean'):
 if p.name in ['NGT_Driver.lean','NGT_ProofDriver.lean']:continue
 mods[p.stem]=['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)
for p in E.glob('NGT_PREREQ_*.lean.txt'):
 n=p.name[len('NGT_PREREQ_'):-len('.lean.txt')];mods[n]=['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)
# NGC was not in the NGN source selection. Reuse its own recorded import
# baseline rather than inventing data from an already loaded environment.
N=E.parent/'slice-d-checkpoint-20261104'
for p in [N/'NGC_EXPECTED_IMPORTS.jsonl']:
 if p.exists():
  for l in p.read_text().splitlines():
   r=json.loads(l);mods.setdefault(r['module'],r['imports'])
(E/'NGT_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=i))+'\n' for n,i in sorted(mods.items())))
roots={'AspisR1.RPx_Deployed.deployed'}
for line in (E/'NGT_ATTEMPTS.jsonl').read_text().splitlines():
 x=json.loads(line)
 if x['kind']=='lean' and x['exit_status']==0:
  for a in x['print_axioms']:roots.add(a.split("'")[1])
(E/'NGT_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[sorted(roots)]),indent=1))
walker=E.parent/'axaudit2-20261102/NEP_WALKER.lean'
# NGN used the identical NFA_WALKER module; its source identity is rechecked.
known='e93447db5a4c402d73e78259bb8c5f3ac09faf3e778250e889bcbcc94acf7344'
assert hashlib.sha256(walker.read_bytes()).hexdigest()==known
(E/'NGT_AUDIT_DRIVER_PINS.json').write_text(json.dumps(dict(walker_source=str(walker),walker_sha256=known,walker_c_sha256=hashlib.sha256((E/'NGT_native/NFA_WALKER.c').read_bytes()).hexdigest(),new_roots=len(roots),driver_origin='evidence/slice-d-prepared-20261105/NGN_Driver.lean',proof_driver_origin='evidence/slice-d-prepared-20261105/NGN_ProofDriver.lean'),indent=1))
print(len(roots),len(mods))
