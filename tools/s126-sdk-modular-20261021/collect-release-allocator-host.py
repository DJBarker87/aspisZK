#!/usr/bin/env python3
"""Source-only release allocator effects and excluded ownership experiments."""
from pathlib import Path
import json,hashlib,shutil,tomllib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-release-allocator-export-v1';O.mkdir(exist_ok=True)
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
accepted={};excluded={}
cases=[('sdk-release-dealloc-check-v1','sdk-release-dealloc-v1','actual_release_dealloc_frame',53,2),('sdk-release-owner-drop-check-v1','sdk-release-owner-drop-v1','proofs::actual_owner_drop_frame',455,1),('sdk-release-owner-empty-check-v1','sdk-release-owner-empty-v1','proofs::actual_owner_drop_frame',501,3)]
cases += [(f'sdk-native-owner-drop-check-v{v}',f'sdk-native-owner-drop-v{v}','proofs::actual_owner_drop_frame',None,None) for v in [1,2,3]]
cases += [('sdk-native-finish-drop-chain-check-v1','sdk-native-finish-drop-chain-v1','proofs::actual_sdk_finish_drop_chain',None,None),('sdk-release-accepted-tail-check-v1','sdk-release-accepted-tail-v1','proofs::native_tail_write_frame',None,None),('sdk-native-first-entry-pair-v5','sdk-shared-prefix-first-entry-pair-v5','proofs::native_owned_decoder_prefix',None,None),('sdk-shared-prefix-codegen-first-entry-pair-v5','sdk-shared-prefix-first-entry-pair-v5','proofs::native_owned_decoder_prefix',None,None)]
for tag,source,harness,checks,covers in cases:
 P=H/source;i=load(H/(tag+'-input.json'));r=load(H/'receipts'/tag/'receipt.json')
 for rel in ['src/lib.rs','src/sdk_live_models.rs','Cargo.toml','Cargo.lock','source-cut.json','release-allocator-selection.rs.txt']:
  if (P/rel).is_file():copy(P/rel,Path('sources')/source/rel)
 for p in (H/'receipts'/tag).iterdir():
  if p.is_file() and p.suffix in ['.json','.log']:copy(p,Path('receipts')/tag/p.name)
 for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:
  if (H/(tag+suffix)).is_file():copy(H/(tag+suffix),tag+suffix)
 if (H/tag).is_dir():
  for p in (H/tag).iterdir():
   if p.is_file() and p.suffix in ['.py','.json','.log','.c']:copy(p,Path('cases')/tag/p.name)
 for package,pin in i.get('local_dependency_source_pins',{}).items():
  for rel,d in pin['files'].items():assert sha(Path(pin['root'])/rel)==d;copy(Path(pin['root'])/rel,Path('dependencies')/package/rel)
 row=dict(source=source,harness=harness,source_sha256=sha(P/'src/lib.rs'),receipt_sha256=sha(H/'receipts'/tag/'receipt.json'),exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'])
 if checks is not None:
  assert r['exit_status']==0 and r['swaps']==0
  log=(H/'receipts'/tag/'stdout.log').read_text();assert f'0 of {checks} failed' in log and f'{covers} of {covers} cover properties satisfied' in log
  crate=tomllib.loads((P/'Cargo.toml').read_text())['package']['name'].replace('-','_');matches=[]
  for p in (H/'target/kani').rglob(crate+'*.kani-metadata.json'):
   for h in load(p).get('proof_harnesses',[]):
    if h['pretty_name']==harness:matches.append((p,h))
  assert len(matches)==1;p,h=matches[0];copy(p,Path('metadata')/tag/'harness-metadata.json');raw=Path(h['goto_file']);ready=Path(str(raw).replace('.symtab.out','.out'))
  row.update(checks=checks,covers=covers,raw_goto_sha256=sha(raw),prepared_goto_sha256=sha(ready))
  accepted[tag]=row
 else:excluded[tag]=row
for tag in ['sdk-native-owner-drop-v2-failure-inventory','sdk-native-owner-drop-v2-failure-trace']:
 for p in (H/'receipts'/tag).iterdir():
  if p.suffix in ['.json','.log']:copy(p,Path('receipts')/tag/p.name)
 for suffix in ['-input.json','-admission.json']:copy(H/(tag+suffix),tag+suffix)
for p in (H/'sdk-native-owner-drop-v2-failure-audit').iterdir():
 if p.suffix in ['.json','.log']:copy(p,Path('failure-audit')/p.name)
sdk=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/solana-program-entrypoint-2.3.0')
for rel in ['src/lib.rs','Cargo.toml']:
 copy(sdk/rel,Path('original-sdk-entrypoint')/rel)
for n in ['run-modular-host.py','run-sdk-shared-prefix-host.py','capped.py','reservation.py','audit-owner-drop-failure-host.py']:copy(H/'kit'/n,Path('runner')/n)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',accepted=accepted,excluded=excluded,scope='Actual SDK BumpAllocator dealloc body has empty write frame. Full actual statement Box/Vec<u8> Drop operations have empty byte-write footprint for all reply lengths0..1769 under explicitly supplied frozen release deallocation. Host System/free failed tests retained, not bypassed or claimed equivalent. Complete accepted-tail/native-prefix products still timed out and have no proof credit.',remaining='Check frozen target allocator dispatch, ABI and valid-owner/runtime mapping; compose concrete SDK acquisition/scan/gate/first/pure-child and copy/guard/owner source instances into the enclosing native-to-owned caller theorem. Source-only focused evidence, no whole S2/TOTAL-stage/soundness claim.',pins_qualification='SDK entrypoint registry snapshot collected after checks; actual compiler dependency versions captured in final Cargo.lock and metadata. Local-path source inventories are pinned before/after where present. No fabricated prelaunch registry hash.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file() and p.name!='manifest.json'}),indent=2)+'\n')
print(json.dumps(dict(output=str(O),accepted=len(accepted),excluded=len(excluded))))
