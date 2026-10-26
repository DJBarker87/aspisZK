"""Copy owned text receipts only; no launcher, monitor or build mutation."""
from pathlib import Path
import json,hashlib,shutil
h=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023');r=h/'src';out=h/'native-install-export';out.mkdir(exist_ok=True)
manifest=[]
def copy(p,rel):
 q=out/rel;q.parent.mkdir(parents=True,exist_ok=True)
 assert p.suffix in ['.json','.log','.txt','.rs']
 if p.suffix=='.rs':q=q.with_suffix('.rs.txt')
 shutil.copyfile(p,q)
 manifest.append(dict(path=str(q.relative_to(out)),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
for pattern in ['entropy-native-*','elf-proverw116-*','elf-proverw118-*']:
 for d in sorted((r/'receipts').glob(pattern)):
  for p in sorted(d.glob('*')):
   if p.is_file() and p.suffix in ['.json','.log','.txt']:copy(p,Path('receipts')/d.name/p.name)
for p in sorted(r.glob('reservation-entropy-native-*.json')):copy(p,Path('admission')/p.name)
for p in sorted(r.glob('reservation-elf-proverw11*.json')):copy(p,Path('admission')/p.name)
p=r/'elf-identities.json'
if p.exists():copy(p,'current-source-elf-identities.json')
p=h/'native-install-before-source-sync'
if p.exists():
 for q in sorted(p.rglob('*')):
  if q.is_file():copy(q,Path('stale-host-input')/q.relative_to(p))
(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(len(manifest))
