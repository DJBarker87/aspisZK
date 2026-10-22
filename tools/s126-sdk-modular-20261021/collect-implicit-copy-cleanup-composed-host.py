#!/usr/bin/env python3
"""Collect every new attempt; accepted composition needs all checks/covers green."""
from pathlib import Path
import json,hashlib,shutil,tomllib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-implicit-copy-cleanup-composed-export-v1';O.mkdir(exist_ok=False)
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
rows={}
for v in [1,2]:
 tag=f'sdk-implicit-copy-cleanup-composed-check-v{v}';source=f'sdk-implicit-copy-cleanup-composed-v{v}';P=H/source
 r=load(H/'receipts'/tag/'receipt.json');i=load(H/(tag+'-input.json'));assert sha(P/'src/lib.rs')==i['source_sha256']
 for f in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json']:copy(P/f,Path('sources')/source/f)
 for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:copy(H/(tag+suffix),tag+suffix)
 for p in (H/'receipts'/tag).iterdir():
  if p.suffix in ['.json','.log']:copy(p,Path('receipts')/tag/p.name)
 row=dict(accepted=r['exit_status']==0,receipt=r,source=source,source_sha256=i['source_sha256'])
 if row['accepted']:
  assert v==2 and r['swaps']==0 and all(load(H/(tag+'-dependency-postcheck.json'))['unchanged'].values())
  log=(H/'receipts'/tag/'stdout.log').read_text();import re
  m=re.search(r'0 of (\d+) failed',log);assert m and '2 of 2 cover properties satisfied' in log;row.update(checks=int(m[1]),covers=2)
  crate=tomllib.loads((P/'Cargo.toml').read_text())['package']['name'].replace('-','_');matches=list((H/'target/kani').rglob(crate+'*.kani-metadata.json'));assert len(matches)==1;copy(matches[0],Path('metadata')/'harness-metadata.json')
  h=next(x for x in load(matches[0])['proof_harnesses'] if x['pretty_name']=='proofs::actual_sdk_ordered_cleanup');g=Path(h['goto_file']);row['raw_goto_sha256']=sha(g);row['prepared_goto_sha256']=sha(Path(str(g).replace('.symtab.out','.out')))
 rows[tag]=row
copy(H/'kit/run-modular-host.py','runner/run-modular-host.py');copy(H/'kit/capped.py','runner/capped.py');copy(H/'kit/reservation.py','runner/reservation.py')
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=rows,dependency_evidence='../sdk-release-allocator/dependencies',scope='EXCLUDED: v1 codegen failed missing same-crate callee proof harness; v2 added the verbatim existing harness but timed out in the combined frame check. No composition or equivalence credit.',remaining='Not whole native caller/source correspondence, arbitrary runtime/ABI/allocator validity, child/oracle interpretation, original-input join or TX2/S1/S6 closure. The source cut/typed move and native order/geometry must still be composed. Failed v1 is a missing same-crate proof harness preflight, not evidence.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file()}),indent=2)+'\n');print(str(O))
