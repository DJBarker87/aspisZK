#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,subprocess
H=Path('/home/dombarker/project-offloads/codex-cx-asq8-kani-20261021')
O=H/'export-final';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputs=json.loads((H/'source-inputs.json').read_text());bad=[p for p,s in inputs.items() if not (H/'src'/p).exists() or sha(H/'src'/p)!=s]
assert not bad,bad
(H/'source-validation.json').write_text(json.dumps(dict(total=len(inputs),mismatches=bad),indent=2)+'\n')
for p in (H/'receipts').glob('*/receipt.json'):
 d=O/'receipts'/p.parent.name;d.mkdir(parents=True)
 for q in p.parent.iterdir():
  if q.suffix in ['.json','.log']:shutil.copyfile(q,d/q.name)
for pattern in ['reservation*.json','source-validation.json','source-revision.txt','pool-elf.sha256','pool-elf.size']:
 for p in H.glob(pattern):shutil.copyfile(p,O/p.name)
artifacts={}
for d in H.glob('extraction-*'):
 for p in d.glob('*input.json'):
  q=O/d.name/p.name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
 for p in d.rglob('*'):
  if p.is_file() and p.suffix in ['.llbc','.lean']:
   artifacts[str(p.relative_to(H))]=dict(sha256=sha(p),bytes=p.stat().st_size)
 for p in d.rglob('translation.json'):
  q=O/d.name/'translation.json';shutil.copyfile(p,q)
assert (H/'receipts/pool-build-v2/receipt.json').exists()
assert (H/'pool-elf.sha256').read_text().split()[0]=='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'
(O/'artifact-pins.json').write_text(json.dumps(artifacts,indent=2)+'\n')
paths=[Path('/home/dombarker/.cargo/bin/cargo-kani')]+list(Path('/home/dombarker/.kani/kani-0.67.0/bin').glob('*'))
paths += [Path('/home/dombarker/.rustup/toolchains/nightly-2025-11-21-x86_64-unknown-linux-gnu/bin/rustc')]
tools={str(p):dict(sha256=sha(p),bytes=p.stat().st_size) for p in paths if p.is_file()}
versions={n:subprocess.check_output([str(p),'--version'],text=True).strip() for n,p in [('kissat',Path('/home/dombarker/.kani/kani-0.67.0/bin/kissat')),('cbmc',Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc'))]}
(O/'kani-tools.json').write_text(json.dumps(dict(kani='0.67.0',versions=versions,files=tools),indent=2)+'\n')
print(O)
