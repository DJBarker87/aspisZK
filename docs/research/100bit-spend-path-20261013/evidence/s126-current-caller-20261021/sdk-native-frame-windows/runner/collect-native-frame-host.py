#!/usr/bin/env python3
"""Collect the native decoder-prefix partitions; export source/text only."""
from pathlib import Path
import hashlib,json,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
O=H/'sdk-native-frame-export';assert not O.exists();O.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,rel):
 q=O/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
sources=[f'sdk-shared-prefix-v{i}' for i in range(15,20)]
sources += [f'sdk-shared-prefix-window{i}-v1' for i in range(1,15)]
sources += ['sdk-shared-prefix-entry-facts-v1']
for name in sources:
 for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json']:
  p=H/name/rel;assert p.is_file(),p;copy(p,Path('sources')/name/rel)
tags=[f'sdk-shared-prefix-codegen-v{i}' for i in range(15,20)]
tags += ['sdk-native-root2-point-v1','sdk-native-root2-all-v1','sdk-native-root2-audit-v1',
 'sdk-native-root1-all-v1','sdk-native-root1-audit-v1','sdk-native-root0-all-v1',
 'sdk-native-pair-separated-frame-v1','sdk-native-frame-coverage-v1','sdk-native-frame-coverage-v2',
 'sdk-shared-prefix-codegen-entry-facts-v1','sdk-native-entry-facts-v1']
for i in range(15):
 tags += [f'sdk-native-proof-window{i}-all-v1',f'sdk-native-proof-window{i}-all-v1-audit']
 if i:tags += [f'sdk-shared-prefix-codegen-window{i}-v1']
for tag in tags:
 root=H/'receipts'/tag;assert (root/'receipt.json').is_file(),root
 for p in root.iterdir():
  if p.is_file() and p.suffix in ['.json','.log','.lean','.py']:
   assert p.stat().st_size<8*1024*1024,p
   copy(p,Path('receipts')/tag/p.name)
 for suffix in ['-input.json','-admission.json']:
  p=H/(tag+suffix)
  if p.is_file():copy(p,p.name)
 if (H/tag).is_dir():
  for p in (H/tag).iterdir():
   if p.is_file() and p.suffix in ['.json','.log']:
    assert p.stat().st_size<8*1024*1024,p
    copy(p,Path('diagnostics')/tag/p.name)
for name in ['sdk-native-window-queue-a-v1','sdk-native-window-queue-b-v1']:
 assert json.loads((H/name/'complete.json').read_text())
 for p in (H/name).iterdir():
  if p.is_file() and p.suffix in ['.json','.log']:copy(p,Path('queues')/name/p.name)
for p in (H/'kit').iterdir():
 if p.is_file() and p.suffix in ['.py','.rs']:copy(p,Path('runner')/p.name)
for rel in ['lakefile.lean','lean-toolchain','S2SdkNativeFrameCoverageV1.lean']:
 copy(H/'lean-native-prefix-frame-v1'/rel,Path('lean')/rel)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',
 accepted_frame=['sdk-native-root1-all-v1','sdk-native-root2-all-v1']+[f'sdk-native-proof-window{i}-all-v1' for i in range(15)],
 accepted_lean='sdk-native-frame-coverage-v2',
 excluded=['sdk-native-root0-all-v1','sdk-native-pair-separated-frame-v1','sdk-native-frame-coverage-v1'],
 qualification='Original SDK, bounded host heap domain, decoder-error prefix, pure read-only std-any overapproximation. Complete enabled noncover properties and two reached covers required per partition. Lean coverage is mathematical composition, with source-certificate and same-execution instantiation still external. Not complete successful stage1, unrestricted runtime transport, S2, S6, S1, TOTAL or soundness closure. Entry-facts separately classified after complete property audit.'),indent=2)+'\n')
pins={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=pins),indent=2)+'\n')
print(O)
