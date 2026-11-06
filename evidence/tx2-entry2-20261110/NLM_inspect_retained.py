"""Bounded final identity/retention inspection; launches no proof or extraction."""
from pathlib import Path
import json,hashlib,shutil,os
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prior=json.loads((B/'NLM_PREDECESSOR_TOOL_PINS.json').read_text());tools=[]
for t in prior['tools']:
 p=Path(t['path']);r=p.resolve();h=sha(r)
 assert h==t['sha256'],('tool identity changed',t['name'])
 tools.append(dict(name=t['name'],path=str(p),resolved=str(r),sha256=h,version=t['version'],identity_matches_predecessor=True))
for p in [Path('/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler'),Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc')]:
 if p.exists():tools.append(dict(name=p.name,path=str(p),resolved=str(p.resolve()),sha256=sha(p.resolve())))
(B/'NLM_TOOL_PINS.json').write_text(json.dumps(dict(tools=tools,note='Final binary identity matches retained NLF pins; no verification/extraction run',CARGO_TARGET_DIR=str(B/'NLM_target')),indent=1)+'\n')
seed=json.loads((B/'NLM_SEED.json').read_text())
for r in seed['files']:assert sha(Path(r['destination']))==r['sha256'],r['destination']
size=sum(p.stat().st_size for p in B.rglob('*') if p.is_file() and not p.is_symlink())
assert size<30_000_000_000,('own write budget',size)
(B/'NLM_RETENTION.json').write_text(json.dumps(dict(workspace=str(B),own_bytes=size,host_free_bytes=shutil.disk_usage(B).free,source='NLM_src retained',target='NLM_target retained',temporary='NLM_tmp retained',seed_hashes_rechecked=len(seed['files']),deletions=[],wallets_or_keys_created=False),indent=1)+'\n')
print(json.dumps(dict(tool_pins=len(tools),own_bytes=size,retained=True)))
