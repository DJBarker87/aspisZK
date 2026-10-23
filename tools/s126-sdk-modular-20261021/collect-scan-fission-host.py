#!/usr/bin/env python3
"""Collect source-only native scan probe frames; retain every enabled check."""
from pathlib import Path
import hashlib,json,shutil,tomllib,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-scan-fission-export-v1';O.mkdir(exist_ok=False);load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
rows={}
for mode,tag in [('enter','sdk-native-scan-fission-enter-v1'),('leave','sdk-scan-fission-leave-check-v1')]:
 P=H/('sdk-shared-prefix-scan-fission-'+mode+'-v1');i=load(H/(tag+'-input.json'));r=load(H/'receipts'/tag/'receipt.json');assert sha(P/'src/lib.rs')==i['source_sha256'] and r['swaps']==0
 for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json']:copy(P/rel,Path('sources')/mode/rel)
 for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:
  p=H/(tag+suffix)
  if p.exists():copy(p,tag+suffix)
 for p in (H/'receipts'/tag).iterdir():
  if p.suffix in ['.log','.json']:copy(p,Path('receipts')/tag/p.name)
 row=dict(mode=mode,source_sha256=i['source_sha256'],receipt=r)
 if mode=='enter':
  assert r['exit_status']==10;a=load(H/tag/'scan-enter-audit.json');row.update(checks=a['noncover_successes'],covers=len(a['reached_covers']),raw_goto_sha256=a['raw_goto_sha256'],prepared_goto_sha256=a['prepared_goto_sha256'])
  for p in (H/tag).iterdir():
   if p.is_file() and p.suffix in ['.json','.log','.py','.c']:copy(p,Path('case')/p.name)
  cg='sdk-shared-prefix-codegen-scan-fission-enter-v1'
  for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:copy(H/(cg+suffix),cg+suffix)
  for p in (H/'receipts'/cg).iterdir():
   if p.suffix in ['.log','.json']:copy(p,Path('receipts')/cg/p.name)
 else:
  assert r['exit_status']==0;log=(H/'receipts'/tag/'stdout.log').read_text();assert '0 of 110 failed' in log and '2 of 2 cover properties satisfied' in log;row.update(checks=110,covers=2)
 crate=tomllib.loads((P/'Cargo.toml').read_text())['package']['name'].replace('-','_');matches=list((H/'target/kani').rglob(crate+'*.kani-metadata.json'));assert len(matches)==1
 meta=load(matches[0]);name='proofs::native_owned_decoder_prefix' if mode=='enter' else 'proofs::scan_leave_contract';h=next(h for h in meta['proof_harnesses'] if h['pretty_name']==name);copy(matches[0],Path('metadata')/mode/'harness-metadata.json');raw=Path(h['goto_file']);row.update(raw_goto_sha256=sha(raw),harness=name)
 if mode=='leave':row['prepared_goto_sha256']=sha(Path(str(raw).replace('.symtab.out','.out')))
 rows[tag]=row
for name in ['run-modular-host.py','run-native-scan-fission-frame-host.py','audit-scan-fission-enter-host.py','capped.py','reservation.py']:copy(H/'kit'/name,Path('runner')/name)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=rows,dependency_evidence='../sdk-native-constructor/dependencies',scope='Actual unchanged enter probe is checked empty-write at its real original-SDK native scan site, on the existing constructor source class. Actual unchanged leave body is checked all-bool/all-old-Option ghost-only and exact Some(hit). Source let/any/probe order erasure and concrete extracted-scanner ghost erasure are checked separately.',remaining='No whole native SDK caller/SBF/runtime/ABI/oracle/TX2 closure. Existing native constructor and first-entry common execution, actual scan/child port interpretation and the forward original-input constructor still require joint concrete instantiation.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file()}),indent=2)+'\n');print(str(O))
