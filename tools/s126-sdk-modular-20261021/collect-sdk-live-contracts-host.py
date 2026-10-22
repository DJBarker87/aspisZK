#!/usr/bin/env python3
"""Export source/text evidence only; failed joins never become certificates."""
from pathlib import Path
import hashlib,json,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
O=H/'sdk-live-contracts-export';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
modes=['length','shared','exclusive']
folders=[f'sdk-account-info-{m}-v1' for m in modes]+[f'sdk-live-{m}-v1' for m in modes]
folders += ['sdk-account-info-all-v1','sdk-account-info-all-v2']
folders += [f'sdk-shared-prefix-v{i}' for i in range(7,13)]
folders += [f'sdk-live-model-shared-v{i}' for i in range(1,4)]+['sdk-live-model-exclusive-v1','sdk-live-model-length-v1','sdk-live-model-length-v2']
receipts=[f'sdk-live-{m}-{kind}-v1' for m in modes for kind in ['codegen','join','properties']]
receipts += [f'sdk-shared-prefix-codegen-v{i}' for i in [7,8,10]]+['sdk-shared-prefix-check-v10']
receipts += [f'sdk-live-model-shared-{kind}-v{i}' for i in range(1,4) for kind in ['codegen','join']]
receipts += [f'sdk-live-model-length-{kind}-v{i}' for i in [1,2] for kind in ['codegen','join']]
receipts += ['sdk-live-alias-inspection-v1','sdk-live-function-inventory-v1']
receipts += ['sdk-shared-prefix-codegen-v11','sdk-native-prefix-frame-check-v1','sdk-shared-prefix-codegen-v12','sdk-native-point-frame-check-v1']
for name in folders:
 root=H/name;assert root.is_dir(),root
 for p in root.rglob('*'):
  rel=p.relative_to(root)
  if p.is_file() and ('src' in rel.parts or str(rel) in ['Cargo.toml','Cargo.toml.orig','Cargo.lock','source-cut.json','voluntary-stop.json']) and p.suffix in ['.rs','.toml','.orig','.lock','.json']:
   copy(p,Path('sources')/name/rel)
for tag in receipts:
 root=H/'receipts'/tag;assert (root/'receipt.json').is_file(),tag
 for p in root.iterdir():
  if p.suffix in ['.json','.log']:
   if p.stat().st_size<1024*1024:copy(p,Path('receipts')/tag/p.name)
   else:
    q=O/'receipts'/tag/(p.name+'-pin.json');q.parent.mkdir(parents=True,exist_ok=True)
    q.write_text(json.dumps(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size,qualification='Host-retained diagnostic; no proof follows from a timeout or inspection.'),indent=2)+'\n')
 for suffix in ['-input.json','-admission.json']:
  p=H/(tag+suffix)
  if p.is_file():copy(p,p.name)
 for p in (H/tag).glob('*.json'):copy(p,Path('diagnostics')/tag/p.name)
for mode in modes:
 root=H/f'sdk-live-{mode}-properties-v1-snapshot'
 copy(root/'harness-metadata.json',Path('metadata')/mode/'harness-metadata.json')
for p in (H/'kit').glob('*'):
 if p.is_file() and (p.suffix=='.py' and any(x in p.name for x in ['live-','shared-prefix','run-modular','reservation','capped']) or p.name=='sdk-live-models.rs'):
  copy(p,Path('runner')/p.name)
registry=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/solana-account-info-2.3.0')
for rel in ['src/lib.rs','src/debug_account_data.rs','Cargo.toml','Cargo.toml.orig']:
 copy(registry/rel,Path('original-sdk')/rel)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',accepted=[f'sdk-live-{m}-join-v1' for m in modes],qualification='Three actual unchanged SDK method bodies, annotation-only isolated SDK copies, explicitly bounded host-ABI heap domain. All paired model and parent composition attempts are excluded. No enclosing caller premise, arbitrary runtime heap, S2, TOTAL or soundness closure is asserted. Receipt source_revision is inherited host bookkeeping; exact source/tool/lock/annotation pins determine the checked target.'),indent=2)+'\n')
pins={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file() and p != O/'manifest.json'}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=pins),indent=2)+'\n')
print(O)
