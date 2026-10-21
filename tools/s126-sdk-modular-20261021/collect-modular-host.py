#!/usr/bin/env python3
"""Collect only text sources, pins and receipts, never compiled objects."""
from pathlib import Path
import hashlib,json,shutil,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'modular-export';O.mkdir(exist_ok=True)
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
for p in (H/'receipts').glob('*/*'):
 if p.suffix in ['.json','.log']:copy(p,p.relative_to(H))
for pat in ['*-admission.json','*-input.json']:
 for p in H.glob(pat):copy(p,p.name)
folders=[]
for f in H.iterdir():
 if not f.is_dir() or not (f/'src/lib.rs').is_file():continue
 folders.append(f.name)
 for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json']:
  if (f/rel).is_file():copy(f/rel,Path('sources')/f.name/rel)
 for p in f.glob('*-input.json'):copy(p,Path('sources')/f.name/p.name)
 if f.name in ['owned-tail-v5','owned-tail-v6','owned-tail-v8']:
  for p in (f/'generated').rglob('*.lean'):
   copy(p,Path('sources')/f.name/(str(p.relative_to(f))+'.txt'))
for p in (H/'kit').glob('*.py'):copy(p,Path('runner')/p.name)
std=H/'kani-rust-slice-iter-macros.rs'
if std.is_file():
 copy(std,Path('std')/std.name)
 (O/'std/pin.json').write_text(json.dumps(dict(url='https://raw.githubusercontent.com/rust-lang/rust/53732d5e0/library/core/src/slice/iter/macros.rs',compiler='rustc 1.93.0-nightly (53732d5e0 2025-11-20)',sha256=hashlib.sha256(std.read_bytes()).hexdigest(),qualification='Pinned upstream source for Kani compiler commit; stock Iter<u8>::any short circuit uses next. Kani executable/sysroot trust is part of the named P6 tool boundary.'),indent=2)+'\n')
(O/'llbc-pins.json').write_text(json.dumps([dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),has_errors=json.loads(p.read_text()).get('has_errors')) for f in folders for p in (H/f).glob('*.llbc')],indent=2)+'\n')
print('source-only export',O)
