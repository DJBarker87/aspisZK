#!/usr/bin/env python3
"""Inspect checked original-SDK/real-guard-reference equivalence and frame.
Preserve text/pins only; no compiled payload is exported.
"""
from pathlib import Path
import hashlib,json,subprocess,sys,shutil,tomllib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
mode=sys.argv[1];version=sys.argv[2] if len(sys.argv)>2 else 'v1'
assert mode in ['length','shared','exclusive']
crate=H/('sdk-live-model-'+mode+'-'+version)
proof='sdk-live-model-'+mode+'-join-'+version;tag='sdk-live-model-'+mode+'-properties-'+version
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cut=json.loads((crate/'source-cut.json').read_text())
assert cut['source_sha256']==sha(crate/'src/lib.rs') and cut['model_sha256']==sha(crate/'src/sdk_live_models.rs')
rp=H/'receipts'/proof/'receipt.json';r=json.loads(rp.read_text());assert r['exit_status']==0 and r['swaps']==0
pin=H/(proof+'-input.json');data=json.loads(pin.read_text())
assert data['source_sha256']==sha(crate/'src/lib.rs') and data['patched_source_pins']=={}
assert data['crate_source_pins']['src/sdk_live_models.rs']==cut['model_sha256']
packages=tomllib.loads((crate/'Cargo.lock').read_text())['package']
sdk=next(p for p in packages if p['name']=='solana-account-info')
assert sdk['version']=='2.3.0' and sdk['checksum']=='c8f5152a288ef1912300fc6efa6c2d1f9bb55d9398eb6c72326360b8063987da'
old={(p['name'],p['version']):p for p in tomllib.loads((H/'sdk-native-context-v9/Cargo.lock').read_text())['package']}
for p in packages:
 if p['name']=='aspis-s126-sdk-live-model-join':continue
 assert old[(p['name'],p['version'])].get('checksum')==p.get('checksum')
selected=[]
for metadata in (H/'target/kani').rglob('aspis_s126_sdk_live_model_join*.kani-metadata.json'):
 for row in json.loads(metadata.read_text()).get('proof_harnesses',[]):
  if row['pretty_name']=='proofs::actual_sdk_live_contract' and row['attributes']['kind']=={'ProofForContract':{'target_fn':'compare_live'}}:selected.append((metadata,row))
assert len(selected)==1,selected
metadata,row=selected[0]
assert row['attributes']['stubs']==[] and row['attributes']['verified_stubs']==[]
program=Path(str(row['goto_file']).replace('.symtab.out','.out'))
snapshot=H/(tag+'-snapshot');snapshot.mkdir(exist_ok=False)
shutil.copyfile(program,snapshot/'checked.out');shutil.copyfile(metadata,snapshot/'harness-metadata.json')
tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc');out=H/'receipts'/tag
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',proof_receipt_sha256=sha(rp),proof_input_sha256=sha(pin),source_sha256=sha(crate/'src/lib.rs'),model_sha256=cut['model_sha256'],program_sha256=sha(snapshot/'checked.out'),metadata_sha256=sha(metadata),harness_metadata=row,tool_sha256=sha(tool),runner_sha256=sha(Path(__file__)),registry_sdk=sdk,qualification=__doc__),indent=2)+'\n')
status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(out),'Inspect already checked exact real SDK/live-reference frame; no solver replay','--',str(tool),'--show-properties','--json-ui',str(snapshot/'checked.out')])
assert status==0,status
props=[p for item in json.loads((out/'stdout.log').read_text()) for p in item.get('properties',[])]
selected=[p for p in props if p.get('class') in ['assigns','postcondition'] or any(s in str(p) for s in ['observed','after_actual','old('])]
assert any(p.get('class')=='assigns' and 'compare_live' in str(p) for p in selected)
assert any('after_actual' in str(p) for p in selected)
(out/'property-audit.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',proof_receipt_sha256=sha(rp),source_sha256=sha(crate/'src/lib.rs'),model_sha256=cut['model_sha256'],program_sha256=sha(snapshot/'checked.out'),total_properties=len(props),selected_properties=selected,qualification=__doc__+' Positive proof is the pinned all-properties receipt, not this metadata inventory.'),indent=2)+'\n')
print(json.dumps(dict(mode=mode,properties=len(props),selected_properties=len(selected))))
