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
 for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json','voluntary-stop.json']:
  if (f/rel).is_file():copy(f/rel,Path('sources')/f.name/rel)
 for p in f.glob('*-input.json'):copy(p,Path('sources')/f.name/p.name)
 if f.name in ['owned-tail-v5','owned-tail-v6','owned-tail-v8','owned-sdk-v1','owned-sdk-v2','owned-sdk-v3']:
  for p in (f/'generated').rglob('*.lean'):
   copy(p,Path('sources')/f.name/(str(p.relative_to(f))+'.txt'))
for folder in H.glob('sdk-*guard-context-v*'):
 if not folder.is_dir():continue
 for rel in ['step0.log','step1.log','cbmc-exit.json','properties-without-traces.json','voluntary-stop.json']:
  if (folder/rel).is_file():copy(folder/rel,Path('diagnostics')/folder.name/rel)
 raw=folder/'step2.log'
 if raw.is_file():
  dest=O/'diagnostics'/folder.name;dest.mkdir(parents=True,exist_ok=True)
  (dest/'raw-log-pin.json').write_text(json.dumps(dict(path=str(raw),sha256=hashlib.sha256(raw.read_bytes()).hexdigest(),bytes=raw.stat().st_size,qualification='Raw CBMC text retained on build host. Large counterexample trace omitted from packet; complete property/status projection retained when solver completed.'),indent=2)+'\n')
  if raw.stat().st_size<1024*1024:copy(raw,Path('diagnostics')/folder.name/raw.name)
for p in (H/'kit').glob('*.py'):copy(p,Path('runner')/p.name)
std=H/'kani-rust-slice-iter-macros.rs'
if std.is_file():
 copy(std,Path('std')/std.name)
 (O/'std/pin.json').write_text(json.dumps(dict(url='https://raw.githubusercontent.com/rust-lang/rust/53732d5e0/library/core/src/slice/iter/macros.rs',compiler='rustc 1.93.0-nightly (53732d5e0 2025-11-20)',sha256=hashlib.sha256(std.read_bytes()).hexdigest(),qualification='Pinned upstream source for Kani compiler commit; stock Iter<u8>::any short circuit uses next. Kani executable/sysroot trust is part of the named P6 tool boundary.'),indent=2)+'\n')
(O/'llbc-pins.json').write_text(json.dumps([dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),has_errors=json.loads(p.read_text()).get('has_errors')) for f in folders for p in (H/f).glob('*.llbc')],indent=2)+'\n')
print('source-only export',O)
