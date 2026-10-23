#!/usr/bin/env python3
"""Collect source-only original std Drop counter-frame gates; no solver replay."""
from pathlib import Path
import json,hashlib,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-drop-frames-export';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
accepted={}
for mode,n in [('shared',760),('exclusive',740)]:
 P=H/f'sdk-drop-{mode}-v1';tag=f'sdk-drop-{mode}-frame-v1'
 for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json']:copy(P/rel,Path('sources')/mode/rel)
 for p in (H/'receipts'/tag).iterdir():
  if p.suffix in ['.json','.log']:copy(p,Path('receipts')/tag/p.name)
 for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:copy(H/(tag+suffix),tag+suffix)
 r=json.loads((H/'receipts'/tag/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
 log=(H/'receipts'/tag/'stdout.log').read_text();assert f'0 of {n} failed' in log and '3 of 3 cover properties satisfied' in log
 matches=[]
 for p in (H/'target/kani').rglob(f'aspis_s126_sdk_drop_{mode}_v1*.kani-metadata.json'):
  for row in json.loads(p.read_text()).get('proof_harnesses',[]):
   if row['crate_name']==f'aspis_s126_sdk_drop_{mode}_v1' and row['pretty_name']=='proofs::actual_sdk_live_contract':matches.append((p,row))
 assert len(matches)==1;metadata,row=matches[0];assert row['attributes']['kind']=={'ProofForContract':{'target_fn':'finish_guard'}} and not row['attributes']['stubs']
 copy(metadata,Path('metadata')/mode/'harness-metadata.json')
 accepted[mode]=dict(target=tag,checks=n,covers=3,raw_goto_sha256=sha(Path(row['goto_file'])),receipt_sha256=sha(H/'receipts'/tag/'receipt.json'))
for n in ['run-modular-host.py','capped.py','reservation.py']:copy(H/'kit'/n,Path('runner')/n)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',accepted=accepted,qualification=__doc__,remaining='Matching acquisition postcondition provides Drop pointer/count preconditions; actual typed guard. Host ABI/runtime embedding, method contextual transport and complete source/caller/oracle composition remain. Bounded helper result, not whole S2.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file()}),indent=2)+'\n')
print(O)
