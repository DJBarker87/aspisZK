#!/usr/bin/env python3
"""Source-only actual typed SDK output-slot checks, including all failed attempts."""
from pathlib import Path
import json,hashlib,shutil,tomllib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-live-out-export-v3';O.mkdir(exist_ok=False);load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
cases=[('sdk-live-out-shared-contract-v1','sdk-live-out-shared-v1','review-stopped'),('sdk-live-out-shared-contract-v2','sdk-live-out-shared-v2','review-stopped'),('sdk-live-out-shared-bridge-codegen-v3','sdk-live-out-shared-v3','compile-error'),('sdk-live-out-shared-bridge-codegen-v4','sdk-live-out-shared-v4','codegen-only'),('sdk-live-out-shared-contract-v4','sdk-live-out-shared-v4','review-stopped'),('sdk-live-out-shared-contract-diagnostic-v4','sdk-live-out-shared-diagnostic-v4','diagnostic-review-stopped'),('sdk-live-out-shared-contract-v5','sdk-live-out-shared-v5','compile-error'),('sdk-live-out-shared-contract-v6','sdk-live-out-shared-v6','review-stopped'),('sdk-live-out-shared-contract-v7','sdk-live-out-shared-v7','review-stopped'),('sdk-live-out-shared-bridge-v7','sdk-live-out-shared-v7','failed-conditional-bridge')]
for tag,source,kind in list(cases):
 if kind=='contract' and load(H/'receipts'/tag/'receipt.json')['exit_status']==0:
  cases.append(('sdk-live-out-shared-bridge-v6',source,'bridge'))
rows={}
for tag,source,kind in cases:
 P=H/source;r=load(H/'receipts'/tag/'receipt.json');i=load(H/(tag+'-input.json'));assert sha(P/'src/lib.rs')==i['source_sha256'];assert r['swaps']==0
 for f in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json']:copy(P/f,Path('sources')/source/f)
 for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:copy(H/(tag+suffix),tag+suffix)
 for p in (H/'receipts'/tag).iterdir():
  if p.suffix in ['.json','.log']:copy(p,Path('receipts')/tag/p.name)
 row=dict(source=source,source_sha256=i['source_sha256'],kind=kind,receipt=r,semantic_accepted=kind in ['contract','bridge'] and r['exit_status']==0)
 if r['exit_status']==0:
  crate=tomllib.loads((P/'Cargo.toml').read_text())['package']['name'].replace('-','_');matches=list((H/'target/kani').rglob(crate+'*.kani-metadata.json'));assert matches
  row['metadata_candidates']={}
  for k,m in enumerate(matches):copy(m,Path('metadata')/tag/(str(k)+'-harness-metadata.json'));row['metadata_candidates'][str(k)]=sha(m)
  # Multiple codegen-mode fingerprints are retained as candidates, never
  # silently assigned one authoritative historical GOTO binary.
  if kind!='codegen-only':
   row['prepared_goto_sha256']=sha(Path(str(g).replace('.symtab.out','.out')))
   import re
   log=(H/'receipts'/tag/'stdout.log').read_text();m=re.search(r'0 of (\d+) failed',log);assert m and '3 of 3 cover properties satisfied' in log;row.update(checks=int(m[1]),covers=3)
 rows[tag]=row
for tag in ['sdk-live-out-shared-loops-v4','sdk-live-out-shared-goto-v4','sdk-live-out-shared-bridge-counterexample-v7']:
 for suffix in ['-input.json','-admission.json']:copy(H/(tag+suffix),tag+suffix)
 for p in (H/'receipts'/tag).iterdir():
  if p.suffix in ['.json','.log']:copy(p,Path('receipts')/tag/p.name)
copy(H/'sdk-live-out-shared-bridge-counterexample-v7/inventory.json','counterexample/inventory.json')
for name in ['s126-out-bridge-counterexample.py','s126-inspect-out-loops.py','s126-inspect-out-goto.py','run-modular-host.py','capped.py','reservation.py']:copy(H/'kit'/name,Path('runner')/name)
sdk=list(Path('/home/dombarker/.cargo/registry/src').glob('*/solana-account-info-2.3.0/src/lib.rs'));assert sdk and len({sha(p) for p in sdk})==1 and sha(sdk[0])=='6b59aba664bb70fda6e17bcc8cf6eb41fc0bc9d8bcbb797bd70c1b107809c29a';copy(sdk[0],'sdk-original-lib.rs')
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=rows,scope='Actual SDK guard/result types retained in a unit-return adapter. Codegen success alone is not a semantic or frame proof. Unit slot ABI, native source bridge installation, actual source/runtime/heap/child/oracle/TX2 and enclosing SDK caller remain required. Full10MiB domain applies only to explicitly marked full-bound candidates;58295 and1-byte cases are qualified restricted/diagnostic probes and cannot discharge that domain.',review='MaybeUninit contracts were stopped after large formula growth, even for one-byte backing: payload size is not the main cause. v3 was a lifetime-in-const compile error; v4 bridge codegen passed. v5 switched to the actual initialized Result error slot but needed immutable postcondition matching, repaired in v6. v6 and v7 unit contracts were also review-stopped. The conditional v7 bridge FAILED2/830 checks: shared BorrowRef Drop subtraction overflow and data-counter restoration;2/3 covers. A selected-property trace reproduces restoration failure. Its contract is not established, and the failed bridge is not a shipped-source counterexample. All stopped/failed/codegen cases are excluded from semantic acceptance.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file()}),indent=2)+'\n');print(str(O))
