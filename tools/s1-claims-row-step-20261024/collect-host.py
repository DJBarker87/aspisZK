#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,shutil,os
W=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021/s1-claims-row-step-v1-20261024');P=W/'source-only-packet';P.mkdir(exist_ok=False)
for n in ['Cargo.toml','Cargo.lock','source-binding.json','proofs.rs','run-host.py','admit-host.py','HostAdmission.py','prepare-host.py']:
 shutil.copyfile(W/n,P/n)
shutil.copytree(W/'payload',P/'payload')
shutil.copytree(W/'results',P/'attempts')
for p in W.glob('*-admission.json'):shutil.copyfile(p,P/p.name)
# Retain every actual local crate source named in the successful Cargo graph;
# never include native libraries, compiled objects or target trees.
m=json.loads((W/'results/claims_row_write_preserves_initialized_prefix-v6/input.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for i,(manifest,pins) in enumerate(m['source_pins'].items()):
 root=Path(manifest).parent;dest=P/'dependencies'/str(i)
 for rel,h in pins.items():
  p=root/rel;assert sha(p)==h,(p,h)
  out=dest/rel;out.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,out)
 (dest/'source-root.json').write_text(json.dumps(dict(root=str(root),manifest=manifest),indent=2)+'\n')
log=(W/'results/claims_row_write_preserves_initialized_prefix-v6/stdout.log').read_text()
lines=[x for x in log.splitlines() if 'failed' in x or 'VERIFICATION:' in x or 'cover properties' in x]
(P/'result-summary.json').write_text(json.dumps(dict(summary=lines,preflight_failures={'v1':'Cargo metadata only: missing retained lockfile/workspace exclusion; compiler/SAT not launched','v2':'Cargo metadata only: retained lockfile copied, missing statement workspace exclusion still pulled in unused dev dependencies; compiler/SAT not launched'},rust_preflight_failures={'v3':'Four M31 raw-word constructor type errors; no SAT','v4':'Generic lifetime binding mismatch in Kani decoder stub; no SAT','v5':'Explicit lifetime remained late-bound; no SAT'},selected='v6',qualification=m['qualification']),indent=2)+'\n')
files={str(p.relative_to(P)):sha(p) for p in P.rglob('*') if p.is_file()}
assert not any(Path(n).suffix in ['.olean','.ir','.llbc','.rlib','.rmeta','.so','.o','.a','.pyc'] for n in files)
(P/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files),indent=2)+'\n')
print(json.dumps(dict(files=len(files),bytes=sum(p.stat().st_size for p in P.rglob('*') if p.is_file()),summary=lines)))
