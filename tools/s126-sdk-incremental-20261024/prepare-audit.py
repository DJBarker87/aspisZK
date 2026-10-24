#!/usr/bin/env python3
"""Prepare combined raw-data audit without trusting either data environment."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'sdk-current-incremental-20261024';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((E/'sdk-current-incremental-export-v2/receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
config=json.loads((P/'input-v2.json').read_text());W=Path(config['dest']).parent
old=json.loads((E/'sdk-current-export-20261024/release.json').read_text());base=Path(old['location']);manifest=json.loads((base/'manifest.json').read_text());assert sha(base/'manifest.json')==old['manifest_sha256']
transport=[]
for row in manifest['files']:
 if row['relative'].startswith('transport/'):
  path=base/row['relative'];assert path.is_file() and not path.is_symlink() and sha(path)==row['sha256']
  module=row['relative'][len('transport/'):-len('.olean')].replace('/','.')
  transport.append((module,str(path)))
newfiles=sorted((W/'transport').rglob('*.olean'));assert newfiles
for path in newfiles:
 module=str(path.relative_to(W/'transport'))[:-len('.olean')].replace('/','.')
 transport.append((module,str(path)))
refresh=json.loads((P/'accepted-proof-replay-source.json').read_text())
audit=dict(transport=transport,seeds=config['seeds'],proof_refresh=(refresh['old_object'],'/tmp/s126-current-caller-20261021-objects/AdapterRwAccepted.olean'))
(W/'audit-input.json').write_text(json.dumps(audit,indent=2)+'\n');(P/'audit-input.json').write_bytes((W/'audit-input.json').read_bytes())
# Mandatory whole selected input postcheck; no unchanged proof replay.
pins=json.loads((P/'input-pins-v2.json').read_text());checks=[]
for row in pins['inputs']:
 for f in row['files']:
  p=Path(f['path']);checks.append(dict(path=str(p),unchanged=p.is_file() and sha(p)==f['sha256']))
assert all(row['unchanged'] for row in checks)
(P/'post-export-inputs.json').write_text(json.dumps(dict(all_unchanged=True,files=checks),separators=(',',':'))+'\n')
(P/'overlay-files.json').write_text(json.dumps([dict(relative=str(p.relative_to(W)),sha256=sha(p),bytes=p.stat().st_size) for p in newfiles],indent=2)+'\n')
print(json.dumps(dict(base_modules=manifest['transport_modules'],new_modules=len(newfiles),combined_modules=len(transport))))
