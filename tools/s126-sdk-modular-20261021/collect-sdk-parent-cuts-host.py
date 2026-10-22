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
folders += ['sdk-native-context-v2','sdk-native-context-v3','sdk-paired-context-v2','sdk-call-context-v1']
folders += ['sdk-finish-v1','sdk-finish-v2','sdk-finish-contract-v1','sdk-finish-contract-v2','sdk-finish-step-v1','sdk-finish-step-v2','sdk-finish-step-v3']
receipts=[f'sdk-heap-{mode}-join-v{v}' for mode in ['shared','exclusive','length','chain'] for v in [1,2]]
receipts += ['sdk-'+mode+'-'+kind+'-v3' for mode in ['shared','exclusive'] for kind in ['write-frame','write-properties']]
receipts += ['owned-sdk-snapshots-v1-charon','owned-sdk-snapshots-v1-aeneas','sdk-paired-context-codegen-v1','sdk-paired-context-check-v1','sdk-private-stub-semantic-preflight-v3','sdk-private-stub-semantic-preflight-v4']
receipts += ['sdk-metadata-prefix-join-v1','sdk-metadata-prefix-join-v2','sdk-paired-context-check-v2','sdk-paired-context-check-v3','sdk-native-context-codegen-v1','sdk-native-context-check-v1','sdk-prefix-context-codegen-v1','sdk-prefix-context-check-v1','sdk-prefix-context-codegen-v2','sdk-prefix-context-check-v2','sdk-prefix-context-codegen-v3','sdk-prefix-context-check-v3']
receipts += ['sdk-native-context-codegen-v2','sdk-native-context-check-v2','sdk-native-context-codegen-v3','sdk-native-context-check-v3','sdk-paired-context-codegen-v2','sdk-call-prefix-codegen-v1','sdk-call-prefix-check-v1']
receipts += ['sdk-finish-join-v1','sdk-finish-join-v2','sdk-finish-contract-join-v1','sdk-finish-contract-join-v2','sdk-finish-step-join-v1','sdk-finish-step-join-v2','sdk-finish-step-join-v3','sdk-finish-step-properties-v3']
folders += ['owned-sdk-copy-v1','sdk-finish-fixed-frame-v1','sdk-finish-fixed-frame-v2','sdk-finish-fixed-frame-v3','sdk-std-copy-frame-v1','sdk-paired-context-v3','sdk-paired-context-v4','sdk-native-context-v4']
receipts += ['owned-sdk-copy-v1-charon','owned-sdk-copy-v1-aeneas','sdk-finish-fixed-frame-join-v1','sdk-finish-fixed-frame-join-v2','sdk-finish-fixed-frame-join-v3','sdk-finish-fixed-frame-properties-v3','sdk-std-copy-frame-join-v1','sdk-std-copy-frame-properties-v1','sdk-std-copy-bridge-join-v1','sdk-std-copy-bridge-pipeline-v1','sdk-paired-context-codegen-v3','sdk-paired-context-codegen-v4','sdk-paired-context-check-v4','sdk-native-context-codegen-v4','sdk-native-context-check-v4','sdk-native-context-loops-v4']
folders += ['sdk-finish-fixed-frame-v4','sdk-finish-verified-v1','sdk-finish-contract-join-v1']
receipts += ['sdk-finish-fixed-frame-join-v4','sdk-finish-fixed-frame-properties-v4','sdk-finish-verified-join-v1','sdk-finish-contract-state-join-v1','sdk-native-context-check-v5','sdk-native-context-check-v6','sdk-native-context-properties-v4']
folders += ['sdk-finish-fixed-frame-v5','sdk-finish-contract-join-v2']
receipts += ['sdk-finish-fixed-frame-join-v5','sdk-finish-fixed-frame-properties-v5','sdk-finish-contract-state-join-v2']
folders += ['sdk-finish-contract-join-v3','sdk-prefix-context-v4']
receipts += ['sdk-finish-contract-state-join-v3','sdk-finish-contract-state-join-v4','sdk-native-context-check-v7','sdk-native-context-check-v8','sdk-prefix-context-check-v4','sdk-prefix-context-check-v5','sdk-call-prefix-check-v2','sdk-prefix-context-codegen-v4','z3-tool-v1','sdk-std-copy-smt-preflight-v1']
folders += ['sdk-call-context-v2','sdk-paired-context-v5']
receipts += ['sdk-call-prefix-codegen-v3','sdk-call-prefix-check-v3','sdk-paired-context-codegen-v5','sdk-std-copy-smt-preflight-v2','sdk-prefix-context-check-v6','sdk-prefix-context-flat-v1','sdk-prefix-smt-exception-v1']
folders += ['sdk-paired-context-v6','sdk-native-context-v5']
receipts += ['sdk-paired-context-check-v5','sdk-paired-context-check-v6','sdk-paired-context-codegen-v6','sdk-native-context-codegen-v5']
pins=[]
for name in folders:
 p=H/name
 for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json','charon-input.json','aeneas-input.json','voluntary-stop.json','statement-fields.json']:
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
for tag in ['sdk-paired-context-check-v1','sdk-paired-context-check-v2','sdk-paired-context-check-v3','sdk-native-context-check-v1','sdk-prefix-context-check-v1','sdk-prefix-context-check-v2','sdk-prefix-context-check-v3','sdk-native-context-check-v2','sdk-native-context-check-v3','sdk-call-prefix-check-v1','sdk-paired-context-check-v4','sdk-native-context-check-v4','sdk-native-context-check-v5','sdk-native-context-check-v6','sdk-native-context-check-v7','sdk-native-context-check-v8','sdk-prefix-context-check-v4','sdk-prefix-context-check-v5','sdk-call-prefix-check-v2','sdk-std-copy-smt-preflight-v1','sdk-std-copy-smt-preflight-v2','sdk-prefix-context-check-v6','sdk-prefix-context-flat-v1','sdk-prefix-smt-exception-v1','sdk-call-prefix-check-v3','sdk-paired-context-check-v5','sdk-paired-context-check-v6']:
 for p in (H/tag).glob('*.json'):copy(p,Path('diagnostics')/tag/p.name)
 for p in (H/tag).glob('*.log'):
  if p.stat().st_size<1024*1024:copy(p,Path('diagnostics')/tag/p.name)
  else:
   out=O/'diagnostics'/tag;out.mkdir(exist_ok=True,parents=True)
   (out/(p.stem+'-pin.json')).write_text(json.dumps(dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p),qualification='Large raw trace retained on host; complete trace-free property projection exported, no binary or large trace distributed.'),indent=2)+'\n')
for p in (H/'target/kani/x86_64-unknown-linux-gnu/debug/.fingerprint').glob('*/*.json'):
 if any(k in p.parent.name for k in ['sdk-heap-','sdk-shared-write-frame','owned-sdk-snapshots','sdk-paired-context','sdk-prefix-context','sdk-native-context','sdk-metadata-prefix','sdk-call-context','sdk-finish','sdk-std-copy','sdk-stub-preflight']):copy(p,Path('compiler-flags')/p.parent.name/p.name)
for p in (H/'kit').glob('*.py'):
 if any(k in p.name for k in ['heap-join','snapshot','paired-context','parent-cuts','write-frame','write-frame-properties','run-modular','metadata-prefix','statement-fields','reservation','finish-join','finish-contract','finish-step','finish-fixed-frame','std-copy','owned-sdk-copy','context-properties','finish-verified','finish-contract-join','smt-preflight','prepared-sdk','trace-cbmc-exception']):copy(p,Path('runner')/p.name)
p=H/'kit/trace-cbmc-exception.cpp'
if p.is_file():copy(p,Path('runner')/p.name)
for rel in ['z3-tool-v1/tool-pins.json','source-freeze-revalidation-20261022.json']:
 p=H/rel
 if p.is_file():copy(p,Path('tool-and-freeze-pins')/p.name)
(O/'llbc-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',qualification='One-operation and lifecycle-cut SDK checks plus pure snapshot fission/extraction. Parent codegen is not proof; timed-out paired context excluded. No complete shipped stage1 or global soundness closure.'),indent=2)+'\n')
print(O)
