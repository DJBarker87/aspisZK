"""Freeze receipt inventory after D542; no build or cache deletion."""
from pathlib import Path
import json,hashlib,subprocess
from run import H
R=H/'resume17';paths=[]
for ident in [73832,73833,73899]:
 p=H/f'lean-{ident}'
 if p.exists():paths.extend(q for q in p.rglob('*')if q.is_file())
for ident in [73949,73950]:
 for p in R.glob(f'K{ident}*'):
  if p.is_dir()and not p.name.endswith('-tmp'):paths.extend(q for q in p.rglob('*')if q.is_file())
  elif p.is_file():paths.append(p)
paths += [H/'TALLY-resume17.json',H/'project-resolution-resume17.json',H/'external-verification-resume17.json',H/'cache-verification-resume17.json',R/'ID-SCAN-D542.json']
paths=list(dict.fromkeys(paths));assert all(p.is_file()for p in paths)
x=dict(hashes={str(p.relative_to(H)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths},scopes=subprocess.check_output(['systemctl','--user','list-units','pv-b3p6-*','--no-pager'],text=True),lean_attempts=json.loads((H/'TALLY-resume17.json').read_text())['lean_attempts'],extraction_receipts=len(list(R.glob('N*/receipt/receipt.json'))),kani_receipts=len(list(R.glob('K*/receipt/receipt.json'))))
assert '0 loaded units listed'in x['scopes'],x['scopes']
(R/'D542-final-host-inventory.json').write_text(json.dumps(x,indent=2)+'\n')
(R/'D542-collect-paths.txt').write_text('\n'.join(str(p.relative_to(H))for p in paths)+'\nresume17/D542-final-host-inventory.json\n')
print(json.dumps({k:x[k]for k in ['lean_attempts','extraction_receipts','kani_receipts']}))
