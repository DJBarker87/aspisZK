#!/usr/bin/env python3
"""Source-only direct SDK/model pair evidence; original unary frames reused."""
from pathlib import Path
import json,hashlib,shutil,tomllib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
O=H/'sdk-live-pairs-export';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
selected={}
for mode,checks in [('length',707),('shared',811),('exclusive',811)]:
 P=H/f'sdk-live-pair-{mode}-v1';tag=f'sdk-live-pair-{mode}-check-v1'
 for rel in ['src/lib.rs','src/sdk_live_models.rs','Cargo.toml','Cargo.lock','source-cut.json']:copy(P/rel,Path('sources')/mode/rel)
 for p in (H/'receipts'/tag).iterdir():
  if p.is_file() and p.suffix in ['.json','.log']:copy(p,Path('receipts')/tag/p.name)
 for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:copy(H/(tag+suffix),tag+suffix)
 r=json.loads((H/'receipts'/tag/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
 log=(H/'receipts'/tag/'stdout.log').read_text();assert f'0 of {checks} failed' in log and '3 of 3 cover properties satisfied' in log
 matches=[]
 for p in (H/'target/kani').rglob(f'aspis_s126_sdk_live_pair_{mode}_v1*.kani-metadata.json'):
  for row in json.loads(p.read_text()).get('proof_harnesses',[]):
   if row['crate_name']==f'aspis_s126_sdk_live_pair_{mode}_v1' and row['pretty_name']=='proofs::actual_sdk_live_contract':matches.append((p,row))
 assert len(matches)==1,matches
 p,row=matches[0];assert not row['attributes'].get('stubs') and row['attributes']['kind']=='Proof'
 copy(p,Path('metadata')/mode/'harness-metadata.json')
 raw=Path(row['goto_file']);ready=Path(str(raw).replace('.symtab.out','.out'))
 selected[mode]=dict(target=tag,checks=checks,covers=3,raw_goto_sha256=sha(raw),prepared_goto_sha256=sha(ready),source_sha256=sha(P/'src/lib.rs'),model_sha256=sha(P/'src/sdk_live_models.rs'),receipt_sha256=sha(H/'receipts'/tag/'receipt.json'))
 sdk=[p for p in tomllib.loads((P/'Cargo.lock').read_text())['package'] if p['name']=='solana-account-info'];assert len(sdk)==1 and sdk[0]['version']=='2.3.0'
 selected[mode]['sdk_lock_package']=sdk[0]
registry=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/solana-account-info-2.3.0')
assert sha(registry/'src/lib.rs')=='6b59aba664bb70fda6e17bcc8cf6eb41fc0bc9d8bcbb797bd70c1b107809c29a'
for rel in ['src/lib.rs','src/debug_account_data.rs','Cargo.toml']:copy(registry/rel,Path('original-sdk')/rel)
for name in ['run-modular-host.py','capped.py','reservation.py']:copy(H/'kit'/name,Path('runner')/name)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',accepted=selected,qualification=__doc__,result='All three direct ordinary pairs pass on the original typed AccountInfo and actual std guard/error types. The paired result/guard words/live counter/drop restoration are checked together; no SDK stubs, custom Arbitrary or SDK carrier substitutes. Counter-only whole-heap write frames come from the separately verified matching actual/model unary contracts; these ordinary pairs are not new DFCC frame checks. Host ABI/domain, method contextual substitution, runtime embedding and enclosing caller/source child/oracle joins remain explicit. No whole S2, TOTAL source or soundness claim.'),indent=2)+'\n')
pins={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=pins),indent=2)+'\n')
print(O)
