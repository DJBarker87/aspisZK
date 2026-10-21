#!/usr/bin/env python3
"""Collect focused parent-cut text evidence; never export compiled artifacts."""
from pathlib import Path
import hashlib,json,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
O=H/'sdk-parent-cuts-export';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
folders=[f'sdk-heap-{mode}-v{v}' for mode in ['shared','exclusive','length','chain'] for v in [1,2]]
folders += ['sdk-shared-write-frame-v3','sdk-exclusive-write-frame-v3','owned-sdk-snapshots-v1','sdk-paired-context-v1','sdk-stub-preflight-v2']
folders += ['sdk-metadata-prefix-v1','sdk-metadata-prefix-v2','sdk-prefix-context-v1','sdk-prefix-context-v2','sdk-prefix-context-v3','sdk-native-context-v1']
receipts=[f'sdk-heap-{mode}-join-v{v}' for mode in ['shared','exclusive','length','chain'] for v in [1,2]]
receipts += ['sdk-'+mode+'-'+kind+'-v3' for mode in ['shared','exclusive'] for kind in ['write-frame','write-properties']]
receipts += ['owned-sdk-snapshots-v1-charon','owned-sdk-snapshots-v1-aeneas','sdk-paired-context-codegen-v1','sdk-paired-context-check-v1','sdk-private-stub-semantic-preflight-v3','sdk-private-stub-semantic-preflight-v4']
receipts += ['sdk-metadata-prefix-join-v1','sdk-metadata-prefix-join-v2','sdk-paired-context-check-v2','sdk-paired-context-check-v3','sdk-native-context-codegen-v1','sdk-native-context-check-v1','sdk-prefix-context-codegen-v1','sdk-prefix-context-check-v1','sdk-prefix-context-codegen-v2','sdk-prefix-context-check-v2','sdk-prefix-context-codegen-v3','sdk-prefix-context-check-v3']
pins=[]
for name in folders:
 p=H/name
 for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json','charon-input.json','aeneas-input.json','voluntary-stop.json']:
  if (p/rel).is_file():copy(p/rel,Path('sources')/name/rel)
 for f in (p/'generated').rglob('*.lean'):copy(f,Path('sources')/name/(str(f.relative_to(p))+'.txt'))
 for f in p.glob('*.llbc'):pins.append(dict(source=name,path=str(f),sha256=sha(f),has_errors=json.loads(f.read_text())['has_errors']))
for name in receipts:
 for p in (H/'receipts'/name).glob('*'):
  if p.suffix in ['.log','.json']:copy(p,Path('receipts')/name/p.name)
 for suffix in ['-input.json','-admission.json']:
  if (H/(name+suffix)).is_file():copy(H/(name+suffix),name+suffix)
for mode in ['shared','exclusive']:
 for suffix in ['-input.json','-admission.json']:
  p=H/('sdk-'+mode+'-properties-v3'+suffix)
  if p.is_file():copy(p,p.name)
for tag in ['sdk-paired-context-check-v1','sdk-paired-context-check-v2','sdk-paired-context-check-v3','sdk-native-context-check-v1','sdk-prefix-context-check-v1','sdk-prefix-context-check-v2','sdk-prefix-context-check-v3']:
 for p in (H/tag).glob('*.json'):copy(p,Path('diagnostics')/tag/p.name)
 for p in (H/tag).glob('*.log'):
  if p.stat().st_size<1024*1024:copy(p,Path('diagnostics')/tag/p.name)
for p in (H/'target/kani/x86_64-unknown-linux-gnu/debug/.fingerprint').glob('*/*.json'):
 if any(k in p.parent.name for k in ['sdk-heap-','sdk-shared-write-frame','owned-sdk-snapshots','sdk-paired-context','sdk-prefix-context','sdk-native-context','sdk-metadata-prefix','sdk-stub-preflight']):copy(p,Path('compiler-flags')/p.parent.name/p.name)
for p in (H/'kit').glob('*.py'):
 if any(k in p.name for k in ['heap-join','snapshot','paired-context','parent-cuts','write-frame','write-frame-properties','run-modular','metadata-prefix']):copy(p,Path('runner')/p.name)
(O/'llbc-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',qualification='One-operation and lifecycle-cut SDK checks plus pure snapshot fission/extraction. Parent codegen is not proof; timed-out paired context excluded. No complete shipped stage1 or global soundness closure.'),indent=2)+'\n')
print(O)
