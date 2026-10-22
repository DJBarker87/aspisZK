#!/usr/bin/env python3
"""Retain excluded reversed-order pair evidence, source only; no proof credit."""
from pathlib import Path
import json,hashlib,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-reference-first-native-export-v1';O.mkdir(exist_ok=False);P=H/'sdk-shared-prefix-reference-first-native-pair-v1';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_text())
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json']:copy(P/rel,Path('source')/rel)
for tag in ['sdk-shared-prefix-codegen-reference-first-native-pair-v1','sdk-native-reference-first-native-pair-v1']:
 i=load(H/(tag+'-input.json'));r=load(H/'receipts'/tag/'receipt.json');assert i['source_sha256']==sha(P/'src/lib.rs') and r['swaps']==0 and r['limits']['memory.swap.max']=='0'
 for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:
  if (H/(tag+suffix)).exists():copy(H/(tag+suffix),tag+suffix)
 for p in (H/'receipts'/tag).iterdir():
  if p.suffix in ['.json','.log']:copy(p,Path('receipts')/tag/p.name)
 if (H/tag).is_dir():
  for p in (H/tag).iterdir():
   if p.is_file() and p.suffix in ['.json','.log','.py','.c']:copy(p,Path('case')/p.name)
for name in ['run-modular-host.py','run-sdk-shared-prefix-host.py','capped.py','reservation.py']:copy(H/'kit'/name,Path('runner')/name)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',accepted_kani_targets=0,qualification='Codegen succeeded; complete reversed-order pair timed out in SSA conversion and receives no proof credit. No unchanged retry or cap increase. Kernel reference reset/reuse theorem is checked separately; native fixed-input correspondence and enclosing S2 remain open.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file()}),indent=2)+'\n');print(str(O))
