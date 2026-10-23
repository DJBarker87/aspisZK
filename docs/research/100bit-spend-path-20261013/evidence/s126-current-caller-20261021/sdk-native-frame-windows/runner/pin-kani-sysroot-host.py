#!/usr/bin/env python3
"""Pin installed Kani Rust/sysroot archives without exporting binary payloads."""
from pathlib import Path
import json,hashlib,subprocess,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
K=Path('/home/dombarker/.kani/kani-0.67.0');tag='sdk-kani-sysroot-pins-v1'
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while block:=f.read(1024*1024):h.update(block)
 return h.hexdigest()
if 'run' not in sys.argv:
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',runner_sha256=sha(Path(__file__)),qualification=__doc__),indent=2)+'\n')
 raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Stream hashes of installed standard-library/Kani archives; no compilation or solver replay','--','python3',__file__,'run']))
paths=sorted(set((K/'toolchain/lib/rustlib/x86_64-unknown-linux-gnu/lib').glob('*.rlib'))|set((K/'lib').rglob('*.rlib')))
assert paths and any(p.name.startswith('libstd-') for p in paths) and any(p.name.startswith('liballoc-') for p in paths)
rows=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in paths]
versions={name:(K/name).read_text().strip() for name in ['rustc-version','rust-toolchain-version']}
(H/'receipts'/tag/'sysroot-pins.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',versions=versions,archives=rows,qualification=__doc__+' Hashes identify installed payloads; this metadata inventory is not source refinement or a coherent rebuild.'),indent=2)+'\n')
print(json.dumps(dict(archives=len(rows),bytes=sum(r['bytes'] for r in rows),versions=versions)))
