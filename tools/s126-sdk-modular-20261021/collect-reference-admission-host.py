#!/usr/bin/env python3
"""Source-only export of the conditional complete reference admission check."""
from pathlib import Path
import hashlib,json,shutil,tomllib,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
version=sys.argv[1] if len(sys.argv)>1 else 'v1'
assert version in ['v1','v2']
P=H/'sdk-reference-admission-v1';O=H/('sdk-reference-admission-export'+('-v2' if version=='v2' else ''));assert not O.exists();O.mkdir()
tag='sdk-reference-admission-check-'+version;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json']:copy(P/rel,Path('source')/rel)
for p in (H/'receipts'/tag).iterdir():
 if p.is_file() and p.suffix in ['.json','.log']:copy(p,Path('receipt')/p.name)
for suffix in ['-input.json','-admission.json']:copy(H/(tag+suffix),tag+suffix)
if version=='v2':
 copy(H/(tag+'-dependency-postcheck.json'),tag+'-dependency-postcheck.json')
 inp=json.loads((H/(tag+'-input.json')).read_text())
 check=json.loads((H/(tag+'-dependency-postcheck.json')).read_text())
 assert check['exit_status']==0 and all(check['unchanged'].values())
metadata=[]
for p in (H/'target/kani').rglob('aspis_s126_sdk_reference_admission*.kani-metadata.json'):
 for row in json.loads(p.read_text()).get('proof_harnesses',[]):
  if row['crate_name']=='aspis_s126_sdk_reference_admission' and row['pretty_name']=='proofs::reference_admission':metadata.append((p,row))
assert len(metadata)==1,metadata
p,row=metadata[0];copy(p,'harness-metadata.json')
raw=Path(row['goto_file']);names=Path(str(raw).replace('.symtab.out','.pretty_name_map.json'))
copy(names,'pretty-names.json')
dependency_pins={}
for name,value in tomllib.loads((P/'Cargo.toml').read_text())['dependencies'].items():
 if not isinstance(value,dict) or 'path' not in value:continue
 root=Path(value['path']);files={}
 for p in root.rglob('*'):
  if not p.is_file() or 'target' in p.relative_to(root).parts or p.suffix not in ['.rs','.toml','.lock']:continue
  files[str(p.relative_to(root))]=sha(p);copy(p,Path('dependencies')/name/p.relative_to(root))
 dependency_pins[name]=dict(path=str(root),files=files)
 if version=='v2':assert files==inp['local_dependency_source_pins'][name]['files']
receipt=json.loads((O/'receipt/receipt.json').read_text());assert receipt['exit_status']==0 and receipt['swaps']==0
log=(O/'receipt/stdout.log').read_text();assert '0 of 1722 failed' in log and '2 of 2 cover properties satisfied' in log
copy(H/'kit/run-modular-host.py','runner/run-modular-host.py')
copy(H/'kit/reservation.py','runner/reservation.py');copy(H/'kit/capped.py','runner/capped.py')
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(P/'src/lib.rs'),cargo_lock_sha256=sha(P/'Cargo.lock'),raw_goto_sha256=sha(raw),metadata_sha256=sha(O/'harness-metadata.json'),dependency_source_pins=dependency_pins,qualification=__doc__,result='All1722 noncover checks pass; both covers reached. Native-derived entry scalar facts and same scan=false boundary construct the full borrowed reference decoder-error prefix on the original buffers. All data/counter/lamport/Rc inputs remain symbolic within the recorded domain; pointer and scalar restoration checks pass. This is conditional reference admission, not actual native successful stage1 refinement, runtime embedding, ordered child/oracle composition or S2 closure. '+('Local-path dependency inventories pinned before codegen/solver and confirmed unchanged after it; exported snapshots equal those pins. Registry/tool/freeze correspondence remains as recorded, no new release freeze.' if version=='v2' else 'Local-path dependency sources recorded after the check; prior source/freeze transport and absence of concurrent dependency mutation remain explicit.')),indent=2)+'\n')
pins={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=pins),indent=2)+'\n')
print(O)
