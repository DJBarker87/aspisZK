#!/usr/bin/env python3
"""Collect audited native constructor entry; source/text only, no new replay."""
from pathlib import Path
import json,hashlib,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-native-success-bytes-pair-export-v1';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_text())
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
v='success-bytes-pair-v1';tag='sdk-native-'+v;P=H/('sdk-shared-prefix-'+v);a=load(H/tag/'success-pair-audit.json');r=load(H/'receipts'/tag/'receipt.json');i=load(H/(tag+'-input.json'))
assert a['noncover_successes']==5513 and len(a['reached_covers'])==2
for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json']:copy(P/rel,Path('source')/rel)
for name in [tag,'sdk-shared-prefix-codegen-'+v]:
 for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:
  p=H/(name+suffix)
  if p.exists():copy(p,name+suffix)
 for p in (H/'receipts'/name).iterdir():
  if p.suffix in ['.json','.log']:copy(p,Path('receipts')/name/p.name)
for rel in ['runner-at-launch.py','source-cut.json','comparison-body.c','comparison-declaration.c','property-inventory.json','properties-complete.json','success-pair-audit.json','cbmc-exit.json']:
 p=H/tag/rel
 if p.exists():copy(p,Path('case')/rel)
copy(H/tag/('step'+str(len(i['commands'])-1)+'.log'),'case/all-properties.log')
cg=load(H/('sdk-shared-prefix-codegen-'+v+'-input.json'))
for package,pin in cg['local_dependency_source_pins'].items():
 for rel,d in pin['files'].items():
  p=H/'sdk-native-first-pair-export-v1/dependencies'/package/rel;assert sha(p)==d
for n in ['run-modular-host.py','run-sdk-shared-prefix-host.py','audit-native-success-bytes-pair-host.py','capped.py','reservation.py']:copy(H/'kit'/n,Path('runner')/n)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',tag=tag,source_sha256=sha(P/'src/lib.rs'),noncover_successes=5513,reached_covers=2,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],dependency_evidence='../sdk-native-first-pair/dependencies',scope='Both COMPLETE native and borrowed-reference callers execute with actual SDK, original proof/public allocations and full statement. With UNSEEDED original proof/prefix/tag/public/checkpoint bytes and only source-reached control conditions, native first entry with arbitrary common1768-byte output implies both complete caller successes and the SAME checkpoint bytes at every selected coordinate, with typed child order/projection/k/None and restored Rc/borrow metadata. The reference gets a real clone of the original checkpoint taken before the native write. Original native copy and implicit cleanup execute; no SDK/copy/Drop stub or explicit-cleanup candidate.',remaining='Compose the existing concrete native accepted-prefix/output-length cut (check-v13/source-v9), native constructor/iterator facts and exact common scan/comparison interpretation; identify reused proof/public bytes as original inputs using source effect/frame composition; install actual pure child/first/verifier interpretations and general valid runtime/heap/ABI/allocator/oracle/TX2 transport. The reference-success premise is derived in the paired unseeded-byte/source-control domain, not yet discharged for the enclosing actual source theorem. Not whole S2/TOTAL stage.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file()}),indent=2)+'\n')
print(json.dumps(dict(output=str(O),checks=5513,covers=2)))
