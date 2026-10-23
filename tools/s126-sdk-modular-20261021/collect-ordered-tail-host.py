#!/usr/bin/env python3
"""Collect exact ordered-tail link and leaf evidence, with failed probes excluded."""
from pathlib import Path
import json,hashlib,shutil,tomllib,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-ordered-tail-export-v1';O.mkdir(exist_ok=True)
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
cases=[('sdk-modular-owner-step-check-v1','sdk-modular-ordered-tail-v1',False),('sdk-modular-owner-step-check-v2','sdk-modular-ordered-tail-v2',False),('sdk-modular-owner-step-check-v3','sdk-modular-ordered-tail-v3',True),('sdk-modular-ordered-tail-check-v3','sdk-modular-ordered-tail-v3',False),('sdk-ordered-tail-links-check-v1','sdk-ordered-tail-links-v1',False),('sdk-raw-drop-shared-check-v1','sdk-ordered-tail-links-raw-v1',False),('sdk-raw-drop-shared-check-v2','sdk-ordered-tail-links-raw-v2',True),('sdk-raw-drop-exclusive-check-v2','sdk-ordered-tail-links-raw-v2',True),('sdk-ordered-tail-links-raw-check-v2','sdk-ordered-tail-links-raw-v2',True)]
rows={}
for tag,source,accept in cases:
 P=H/source;i=load(H/(tag+'-input.json'));r=load(H/'receipts'/tag/'receipt.json');assert sha(P/'src/lib.rs')==i['source_sha256']
 for rel in ['src/lib.rs','src/sdk_live_models.rs','Cargo.toml','Cargo.lock','source-cut.json']:
  if (P/rel).exists():copy(P/rel,Path('sources')/source/rel)
 for p in (H/'receipts'/tag).iterdir():
  if p.suffix in ['.json','.log']:copy(p,Path('receipts')/tag/p.name)
 for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:
  p=H/(tag+suffix)
  if p.exists():copy(p,tag+suffix)
 row=dict(accepted=accept,source=source,receipt=r,source_sha256=sha(P/'src/lib.rs'))
 if accept:
  assert r['exit_status']==0 and r['swaps']==0
  text=(H/'receipts'/tag/'stdout.log').read_text();m=re.search(r'0 of (\d+) failed',text);c=re.search(r'(\d+) of (\d+) cover properties satisfied',text);assert m and c
  row.update(noncover_successes=int(m[1]),reached_covers=int(c[1]),all_cover_locations=int(c[2]))
  harness=i['command'][i['command'].index('--harness')+1];crate=tomllib.loads((P/'Cargo.toml').read_text())['package']['name'].replace('-','_');matches=[]
  for p in (H/'target/kani').rglob(crate+'*.kani-metadata.json'):
   for h in load(p)['proof_harnesses']:
    if h['pretty_name']==harness:matches.append((p,h))
  assert len(matches)==1;p,h=matches[0];copy(p,Path('metadata')/tag/'harness-metadata.json');raw=Path(h['goto_file']);ready=Path(str(raw).replace('.symtab.out','.out'))
  row.update(harness=harness,raw_goto_sha256=sha(raw),prepared_goto_sha256=sha(ready))
 for package,pin in i['local_dependency_source_pins'].items():
  for rel,d in pin['files'].items():assert sha(H/'sdk-release-allocator-export-v1/dependencies'/package/rel)==d
 rows[tag]=row
for tag in ['sdk-ordered-tail-links-v1-failure-inventory','sdk-ordered-tail-links-v1-failure-trace']:
 for p in (H/'receipts'/tag).iterdir():
  if p.suffix in ['.json','.log']:copy(p,Path('receipts')/tag/p.name)
 for suffix in ['-input.json','-admission.json']:copy(H/(tag+suffix),tag+suffix)
for p in (H/'sdk-ordered-tail-links-v1-failure-audit').iterdir():
 if p.suffix in ['.json','.log']:copy(p,Path('failure-audit')/p.name)
for n in ['run-modular-host.py','capped.py','reservation.py','audit-ordered-tail-failure-host.py']:copy(H/'kit'/n,Path('runner')/n)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=rows,dependency_evidence='../sdk-release-allocator/dependencies',scope='Actual SDK caller instantiates typed copy/owner/raw-guard contracts in source-relative cleanup order, checks exact return codes, observed checkpoint byte, counters/Rc. Raw shared/exclusive guard Drop leaves and owner step are separately proved; copy reuses existing exact native finish certificate. No enclosing whole-memory DFCC frame is enforced or assumed by the accepted ordinary caller link.',excluded='v1 syntax splice; v2 missing proof harness declarations; v3 enclosing DFCC timeout. By-value verified guard link failed with extra cleanup after stub postcondition, trace retained. raw-drop-shared-v1 was an unintended unchanged by-value leaf replay after local generator preflight failed; no new proof credit. Subsequent source generation/upload is gated on success.',remaining='All exact leaf domains/tool/source pins must match. Compiler implicit-cleanup/explicit typed Drop candidate equivalence, footprint union/source composition, frozen allocator dispatch/valid owners/runtime/ABI, full native first/child/oracle and cross-TX transport remain. No full S2/TOTAL stage or soundness claim.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file() and p.name!='manifest.json'}),indent=2)+'\n')
print(json.dumps(dict(output=str(O),accepted=sum(r['accepted'] for r in rows.values()),excluded=sum(not r['accepted'] for r in rows.values()))))
