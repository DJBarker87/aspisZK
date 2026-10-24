#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'sdk-selected-cut-export-20261025';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((E/'sdk-selected-cut-export-v1/receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
config=json.loads((P/'input.json').read_text());W=Path(config['dest']).parent;files=sorted((W/'transport').rglob('*.olean'));assert files
transport=[(str(p.relative_to(W/'transport'))[:-len('.olean')].replace('/','.'),str(p)) for p in files]
pins=json.loads((P/'input-pins.json').read_text())
audit=dict(transport=transport,seeds=config['seeds'],baseline_names=config['baseline_names'],baseline_transport=pins['base_transport'])
(W/'audit-input.json').write_text(json.dumps(audit,separators=(',',':'))+'\n');(P/'audit-input.json').write_bytes((W/'audit-input.json').read_bytes())
pins=json.loads((P/'input-pins.json').read_text());checks=[]
for row in pins['inputs']:
 for f in row['files']:
  p=Path(f['path']);checks.append(dict(path=str(p),unchanged=p.is_file() and sha(p)==f['sha256']))
assert all(r['unchanged'] for r in checks)
(P/'post-export-inputs.json').write_text(json.dumps(dict(all_unchanged=True,files=checks),separators=(',',':'))+'\n')
(P/'overlay-files.json').write_text(json.dumps([dict(relative=str(p.relative_to(W)),sha256=sha(p),bytes=p.stat().st_size) for p in files],indent=2)+'\n')
print(json.dumps(dict(new_fragments=len(files),baseline_constants=len(config['baseline_names']))))
