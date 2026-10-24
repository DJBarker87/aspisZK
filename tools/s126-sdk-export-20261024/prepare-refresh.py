#!/usr/bin/env python3
"""Explicit proof-only import refresh; never relabel the failed exact 9acc export."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'sdk-current-export-20261024';W=Path('/private/tmp/s126-sdk-current-export-20261024-v2');W.mkdir(mode=0o700,exist_ok=False);(W/'transport').mkdir(mode=0o700)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();old=json.loads((P/'input.json').read_text());basis=json.loads((E/'s6-sdk-first-factor-import-pins.json').read_text());r=json.loads((E/'sdk-current-entry-privileges-replay-v1/receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms']
rows=[];changed=[]
for row in basis['modules']:
 rel=Path(*row['name'].split('.')).with_suffix('.olean');path=next(Path(root)/rel for root in old['roots'] if (Path(root)/rel).exists());h=sha(path)
 if h!=row['sha256']:
  assert row['name']=='S2W_EntryPrivileges' and h==r['object_sha256']
  changed.append(dict(module=row['name'],historical_path=row['path'],historical_sha256=row['sha256'],refreshed_path=str(path),refreshed_sha256=h,receipt='sdk-current-entry-privileges-replay-v1/receipt.json'))
 fs=[]
 for suffix in ['', '.server','.private']:
  p=Path(str(path)+suffix)
  if p.exists():fs.append(dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)))
 rows.append(dict(module=row['name'],files=fs))
assert len(changed)==1
config=dict(old,dest=str(W/'transport'));(W/'input.json').write_text(json.dumps(config,indent=2)+'\n');(P/'input-v2.json').write_bytes((W/'input.json').read_bytes())
(P/'input-pins-v2.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',primary_source_basis='9acc015544c36891712af984c0a9604a39425eeb',source_worktree_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),assessment='Primary source/object seeds unchanged; explicit proof-only dependency replay overlay. NOT an exact historical 9acc closure. All other selected input hashes match the historical basis.',changes=changed,inputs=rows,tools=json.loads((P/'input-pins.json').read_text())['tools']),indent=2)+'\n')
print(json.dumps(dict(work=str(W),changed=changed)))
