#!/usr/bin/env python3
"""Collect actual guard-chain frame and excluded bound preflights, no binaries."""
from pathlib import Path
import json,hashlib,shutil,tomllib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-native-drop-chain-export-v1';O.mkdir(exist_ok=True)
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
rows={}
for v in [1,2,3]:
 tag=f'sdk-native-drop-chain-check-v{v}';P=H/f'sdk-native-drop-chain-v{v}'
 for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json']:copy(P/rel,Path('sources')/str(v)/rel)
 for p in (H/'receipts'/tag).iterdir():
  if p.suffix in ['.json','.log']:copy(p,Path('receipts')/tag/p.name)
 for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:copy(H/(tag+suffix),tag+suffix)
 i=load(H/(tag+'-input.json'));r=load(H/'receipts'/tag/'receipt.json')
 for package,pin in i['local_dependency_source_pins'].items():
  for rel,d in pin['files'].items():assert sha(Path(pin['root'])/rel)==d;copy(Path(pin['root'])/rel,Path('dependencies')/package/rel)
 row=dict(accepted=v==3,receipt=r,source_sha256=sha(P/'src/lib.rs'))
 if v==3:
  assert r['exit_status']==0 and r['swaps']==0
  crate=tomllib.loads((P/'Cargo.toml').read_text())['package']['name'].replace('-','_');matches=[]
  for p in (H/'target/kani').rglob(crate+'*.kani-metadata.json'):
   for h in load(p)['proof_harnesses']:
    if h['pretty_name']=='proofs::actual_sdk_drop_chain':matches.append((p,h))
  assert len(matches)==1;p,h=matches[0];copy(p,Path('metadata')/'harness-metadata.json');raw=Path(h['goto_file']);ready=Path(str(raw).replace('.symtab.out','.out'))
  row.update(raw_goto_sha256=sha(raw),prepared_goto_sha256=sha(ready))
 rows[tag]=row
for n in ['run-modular-host.py','capped.py','reservation.py']:copy(H/'kit'/n,Path('runner')/n)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=rows,scope='Counter-only combined frame for actual three std guards, all concrete acquisitions through original SDK. Real Drop executes; no SDK/Drop or verified stubs in selected harness. The native leaf-links cut supplies guard words/pointers and live counts at actual post-first continuation. Source/result/runtime joins and Box/Vec owner effects remain.',excluded='v1/v2 insufficient unwind bounds in fixture loop4 and key memcmp32. v3 uses33 covering fixed32-byte comparisons; unwinding assertions enabled. Failed runs have zero proof credit.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file() and p.name!='manifest.json'}),indent=2)+'\n')
print(O)
