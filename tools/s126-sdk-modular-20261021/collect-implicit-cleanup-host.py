#!/usr/bin/env python3
"""Source-only focused implicit cleanup packet, with failed predecessor excluded."""
from pathlib import Path
import json,hashlib,shutil,tomllib,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-implicit-cleanup-export-v1';O.mkdir(exist_ok=False);load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
rows={}
for version,accept in [('implicit-cleanup-frame-v1',False),('implicit-cleanup-frame-v2',True),('implicit-copy-cleanup-frame-v1',False)]:
 tag='sdk-'+version.replace('-frame-','-frame-check-');P=H/('sdk-'+version);i=load(H/(tag+'-input.json'));r=load(H/'receipts'/tag/'receipt.json');assert sha(P/'src/lib.rs')==i['source_sha256']
 for p in P.rglob('*'):
  if p.is_file() and p.suffix in ['.rs','.toml','.lock','.json']:copy(p,Path('sources')/P.name/p.relative_to(P))
 for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:copy(H/(tag+suffix),tag+suffix)
 for p in (H/'receipts'/tag).iterdir():
  if p.suffix in ['.json','.log']:copy(p,Path('receipts')/tag/p.name)
 row=dict(accepted=accept,source=P.name,source_sha256=sha(P/'src/lib.rs'),receipt=r)
 if accept:
  assert r['exit_status']==0 and r['swaps']==0
  log=(H/'receipts'/tag/'stdout.log').read_text();n=re.search(r'0 of (\d+) failed',log);assert n and '2 of 2 cover properties satisfied' in log
  crate=tomllib.loads((P/'Cargo.toml').read_text())['package']['name'].replace('-','_');matches=list((H/'target/kani').rglob(crate+'*.kani-metadata.json'));assert len(matches)==1
  h=next(h for h in load(matches[0])['proof_harnesses'] if h['pretty_name']=='proofs::actual_sdk_ordered_cleanup');copy(matches[0],Path('metadata')/tag/'harness-metadata.json');raw=Path(h['goto_file']);prepared=Path(str(raw).replace('.symtab.out','.out'));row.update(checks=int(n[1]),covers=2,raw_goto_sha256=sha(raw),prepared_goto_sha256=sha(prepared))
  ordertag=P.name+'-order-v1';order=H/(ordertag+'-export')
  for p in order.iterdir():copy(p,Path('order')/tag/p.name)
  for suffix in ['-input.json','-admission.json']:copy(H/(ordertag+suffix),ordertag+suffix)
  for rel in ['receipt.json','stderr.log','time.log']:copy(H/'receipts'/ordertag/rel,Path('receipts')/ordertag/rel)
 for package,pin in i['local_dependency_source_pins'].items():
  for rel,d in pin['files'].items():assert sha(H/'sdk-release-allocator-export-v1/dependencies'/package/rel)==d
 rows[tag]=row
for name in ['run-modular-host.py','capped.py','reservation.py','inspect-implicit-cleanup-initial-parser.py','inspect-implicit-cleanup-host.py']:copy(H/'kit'/name,Path('runner')/name)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=rows,dependency_evidence='../sdk-release-allocator/dependencies',scope='Actual typed compiler implicit cleanup has counter-only write footprint and exact restored counters. The combined whole-copy/cleanup attempt timed out and has no proof credit; separate concrete copy and cleanup frames remain the composition route. Checked destructor role/type order matches the actual native source suffix. No explicit drop helper or verified/model callee stub in these checked bodies.',remaining='Explicit frozen-release deallocation dispatch, valid SDK memory class/runtime/ABI/allocator interpretation and native accepted-length/call-site/common-prefix composition remain. Concrete installed children/oracle, fixed-input whole caller and cross-TX transport, S1/S6 remain open. v1 postcondition probe precedes parameter destruction and is excluded, not a shipped defect. Combined copy/cleanup timed out; no unchanged retry or cap increase.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file()}),indent=2)+'\n');print(json.dumps(dict(output=str(O),accepted=1,excluded=2)))
