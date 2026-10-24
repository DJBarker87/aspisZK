#!/usr/bin/env python3
"""Retain failed exact attempt; select one explicit same-source proof replay."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'sdk-current-incremental-20261024';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((P/'input.json').read_text());pins=json.loads((P/'input-pins.json').read_text());r=json.loads((E/'sdk-current-accepted-proof-replay-v1/receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0 and len(r['print_axioms'])==2
base=Path(pins['baseline_location']);base_names={json.loads(line)['name'] for line in (base/'constants.jsonl').read_text().splitlines()};assert not any(n.startswith('AspisR1.AdapterRw.Accepted.') for n in base_names)
rows=[];changed=[]
for row in pins['inputs']:
 rel=Path(*row['module'].split('.')).with_suffix('.olean');path=next(Path(root)/rel for root in old['roots'] if (Path(root)/rel).is_file());files=[]
 for suffix in ['', '.server','.private']:
  f=Path(str(path)+suffix)
  if f.exists():files.append(dict(path=str(f),sha256=sha(f),bytes=f.stat().st_size))
 hashes=lambda fs:{Path(f['path']).name:f['sha256'] for f in fs}
 if hashes(files)!=hashes(row['files']):
  assert row['module']=='AdapterRwAccepted' and sha(path)==r['object_sha256']
  changed.append(dict(module=row['module'],old_files=row['files'],new_files=files,receipt='sdk-current-accepted-proof-replay-v1/receipt.json',baseline_contains_no_constants_from_this_module=True))
 rows.append(dict(module=row['module'],files=files))
assert len(changed)==1
w=Path('/private/tmp/s126-sdk-current-incremental-20261024-v2');w.mkdir(mode=0o700,exist_ok=False);(w/'transport').mkdir(mode=0o700)
new=dict(old,dest=str(w/'transport'));(P/'input-v2.json').write_text(json.dumps(new,indent=2)+'\n');(w/'input.json').write_bytes((P/'input-v2.json').read_bytes())
newpins=dict(pins,inputs=rows,changes=changed,scope='Explicit byte-identical published AdapterRwAccepted source replay, same-type comparison required. Base has no constants from this newly needed module, so all 1287 released base payloads remain unchanged. Raw data only, not kernel reconstruction.')
(P/'input-pins-v2.json').write_text(json.dumps(newpins,separators=(',',':'))+'\n')
print(json.dumps(dict(work=str(w),changed=changed)))
